#!/usr/bin/env python3
"""
Local Collin CAD parcel index.

Loads the most recent parcel_export_YYYYMMDD.csv from the CCAD-1 repo
(daily-refreshed) into an in-memory name -> parcel index.  Used as the
primary path for clerk-record -> property resolution, replacing the
slower and statewide-noisy Socrata calls.

Public API:
    load_index(force=False)        — build/refresh the index (idempotent)
    lookup_parcel_local(name)      — same return shape as fetch.lookup_parcel
    log_lookup_stats()             — optional: print summary of hits/misses

Returned dict on a hit:
    prop_address, prop_city, prop_state, prop_zip,
    mail_address, mail_city, mail_state, mail_zip,
    year_built, sqft, market_value, deed_year, long_term_owner (bool),
    account
"""

from __future__ import annotations

import atexit
import csv
import io
import logging
import re
from datetime import datetime, timedelta
from typing import Optional

import requests

log = logging.getLogger("parcel_index")

CCAD_REPO_RAW       = "https://raw.githubusercontent.com/16171290/CCAD-1/main/data"
INDEX_LOOKBACK_DAYS = 14
MIN_VALID_CSV_BYTES = 5_000           # placeholder files are ~266 bytes

# CAD First Name field is messy: 'Curtid P Jeanna M &', 'John C Jr', etc.
# These tokens are stripped before key generation so the same key matches
# clerk records that may or may not include them.
SUFFIXES = {
    "JR", "SR", "II", "III", "IV", "V",
    "LE", "ETUX", "ETAL", "ET", "UX", "AL",
    "TR", "TRUSTEE", "TRUST",
    "MD", "DDS", "ESQ", "PHD",
}

# Particles that commonly start compound surnames in Texas records.
# Used at lookup time to try multi-token last-name splits before falling
# back to the default single-token assumption.
#
# Intentionally excludes 'LE' and 'DA' — those are common standalone
# Vietnamese / Portuguese surnames in Texas and including them would cause
# more false positives than the rare LeBlanc / DaSilva style names we'd
# catch.
COMPOUND_LAST_PARTICLES = {
    "DE", "DEL", "DELA", "DELOS", "LA", "LAS", "LOS",
    "VAN", "VANDER", "VANDEN", "VON",
    "ST", "SAINT", "MAC", "MC",
}

# Primary index: 'LAST FIRST' / 'LAST FIRST MIDDLE' style multi-char keys
_index: dict[str, list[dict]] = {}

# Secondary index: 'LAST F' (single-letter first-initial) keys for last-resort
# fallback lookups.  Only consulted when the primary index returns nothing
# AND only accepted when the initial key resolves to exactly one record.
_initial_index: dict[str, list[dict]] = {}

# Address-keyed index for reverse lookups (foreclosure scraper feeds in
# property addresses; we resolve to the owner + CAD details). Keys are
# produced by _normalize_address() so equivalent street-suffix and
# directional spellings collide cleanly.
_address_index: dict[str, list[dict]] = {}

# Street suffix and directional standardization for address-key generation.
# Both clerk-side and CCAD addresses get hashed through the same normalizer
# so spelling variants ('DRIVE' vs 'DR', 'NORTH' vs 'N') hit the same bucket.
_STREET_SUFFIX_MAP = {
    "STREET":   "ST",
    "AVENUE":   "AVE",
    "DRIVE":    "DR",
    "ROAD":     "RD",
    "LANE":     "LN",
    "BOULEVARD":"BLVD",
    "CIRCLE":   "CIR",
    "COURT":    "CT",
    "PLACE":    "PL",
    "TRAIL":    "TRL",
    "PARKWAY":  "PKWY",
    "HIGHWAY":  "HWY",
    "TERRACE":  "TER",
    "SQUARE":   "SQ",
    "CROSSING": "XING",
    "LANDING":  "LNDG",
    "JUNCTION": "JCT",
    "HARBOR":   "HBR",
    "GARDEN":   "GDN",
    "GARDENS":  "GDNS",
    "VIEW":     "VW",
}
_DIRECTIONAL_MAP = {
    "NORTH":     "N",  "SOUTH":     "S",  "EAST":      "E",  "WEST":      "W",
    "NORTHEAST": "NE", "NORTHWEST": "NW", "SOUTHEAST": "SE", "SOUTHWEST": "SW",
}
_SUFFIX_PAT      = re.compile(r"\b(" + "|".join(_STREET_SUFFIX_MAP) + r")\b")
_DIRECTIONAL_PAT = re.compile(r"\b(" + "|".join(_DIRECTIONAL_MAP)   + r")\b")

_loaded_from:   Optional[str]         = None

# Diagnostic counters — reset on each load_index() call.  Reported by
# log_lookup_stats() at end of run for visibility into match quality.
_lookup_stats = {
    "total":         0,
    "hits_primary":  0,
    "hits_initial":  0,
    "misses":        0,
    "miss_examples": [],   # first ~30 miss names for log inspection
}


# ---------------------------------------------------------------------------
#  NORMALIZATION
# ---------------------------------------------------------------------------

def _normalize(s: str) -> str:
    """Uppercase, strip punctuation/symbols, collapse whitespace."""
    if not s:
        return ""
    s = s.upper()
    s = re.sub(r"[&,.]",  " ", s)
    s = re.sub(r"[^A-Z0-9\s\-]", " ", s)
    s = re.sub(r"\s+",    " ", s).strip()
    return s

def _strip_suffixes(tokens: list[str]) -> list[str]:
    return [t for t in tokens if t not in SUFFIXES]


def _normalize_address(addr: str) -> str:
    """Standardize a street address so equivalent spellings hash to the same
    bucket. Used both at index-build time (over CCAD addresses) and at
    lookup time (over addresses fed in by foreclosure scraper).

    Handles:
      - Case folding ('10022 Plainsman Ln' -> '10022 PLAINSMAN LN')
      - Street-type expansion ('DRIVE' -> 'DR', 'STREET' -> 'ST', etc.)
      - Directional expansion ('NORTH' -> 'N', 'SOUTHWEST' -> 'SW', etc.)
      - Punctuation cleanup (commas, periods, hash marks)
      - Whitespace collapse
    """
    if not addr:
        return ""
    s = addr.upper().strip()
    s = re.sub(r"[.,#]", " ", s)
    s = _DIRECTIONAL_PAT.sub(lambda m: _DIRECTIONAL_MAP[m.group(1)], s)
    s = _SUFFIX_PAT.sub(lambda m: _STREET_SUFFIX_MAP[m.group(1)], s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


# ---------------------------------------------------------------------------
#  KEY GENERATION
# ---------------------------------------------------------------------------

def _keys_for_row(first: str, last: str) -> set[str]:
    """
    Produce every reasonable 'LAST FIRST...' lookup key for a CAD row.

    Handles:
      - Single owner: 'Angela Rocha'        -> {'ROCHA ANGELA'}
      - With MI:      'Elizabeth N Kioni'   -> {'KIONI ELIZABETH', 'KIONI ELIZABETH N'}
      - Joint owners: 'Curtid P Jeanna M & / Taipale'
                      -> {'TAIPALE CURTID', 'TAIPALE CURTID P',
                          'TAIPALE JEANNA', 'TAIPALE JEANNA M', ...}
      - Hyphenated last: 'Smith-Jones'      -> indexes under both halves
      - Initials-only first: 'R L Smith'    -> {'SMITH R', 'SMITH L', 'SMITH R L'}
      - Suffixes (Jr/Sr/II/Le/etc) stripped before key generation
    """
    last_n  = _normalize(last)
    first_n = _normalize(first)
    if not last_n or not first_n:
        return set()

    # Index under the full hyphenated last name AND each half separately.
    last_alts = {last_n}
    for part in last_n.split("-"):
        part = part.strip()
        if part and len(part) >= 2:
            last_alts.add(part)

    f_tokens = _strip_suffixes(first_n.split())
    if not f_tokens:
        return set()

    keys: set[str] = set()
    multi = [t for t in f_tokens if len(t) >= 2]

    for ln in last_alts:
        # Every multi-character first-name token (catches each owner in joint records)
        for t in multi:
            keys.add(f"{ln} {t}")
        # Adjacent token pairs (handles 'first + middle initial' style)
        for i in range(len(f_tokens) - 1):
            keys.add(f"{ln} {f_tokens[i]} {f_tokens[i+1]}")
        # First two multi-char tokens together (skips initials between)
        if len(multi) >= 2:
            keys.add(f"{ln} {multi[0]} {multi[1]}")
        # NEW: initials-only first names ('R L Smith') previously generated
        # zero keys.  Index each token directly so they remain findable.
        if not multi:
            for t in f_tokens:
                if t:
                    keys.add(f"{ln} {t}")

    return keys


def _initial_keys_for_row(first: str, last: str) -> set[str]:
    """
    Generate 'LAST F' (single-letter first-initial) keys for the fallback
    initial-index.  These are deliberately ambiguous — they're only consulted
    at lookup time when the primary index missed AND the initial key resolves
    to exactly one record (uniqueness check protects against false positives).
    """
    last_n  = _normalize(last)
    first_n = _normalize(first)
    if not last_n or not first_n:
        return set()

    last_alts = {last_n}
    for part in last_n.split("-"):
        part = part.strip()
        if part and len(part) >= 2:
            last_alts.add(part)

    f_tokens = _strip_suffixes(first_n.split())
    if not f_tokens:
        return set()

    keys: set[str] = set()
    for ln in last_alts:
        for t in f_tokens:
            if t:
                keys.add(f"{ln} {t[0]}")
    return keys


# ---------------------------------------------------------------------------
#  COMPOUND-SURNAME SPLIT (lookup time)
# ---------------------------------------------------------------------------

def _candidate_last_splits(tokens: list[str]) -> list[tuple[str, list[str]]]:
    """
    Produce plausible (last_name, rest_tokens) splits for a normalized name.

    Most-specific splits first so the more-likely-correct match wins:
      'DE LA CRUZ MARIA'  -> ('DE LA CRUZ', ['MARIA']), ('DE LA', ['CRUZ','MARIA']),
                              ('DE', ['LA','CRUZ','MARIA'])
      'VAN DER BERG JOHN' -> ('VAN DER BERG', ['JOHN']) is NOT generated (only
                              two compound particles deep), but ('VAN DER', ...)
                              and ('VAN', ...) are.
      'MC DONALD JOHN'    -> ('MC DONALD', ['JOHN']), ('MC', ['DONALD','JOHN'])
      'DICKEN ROBERT LEE' -> ('DICKEN', ['ROBERT','LEE'])    (default only)
    """
    splits: list[tuple[str, list[str]]] = []

    # 3-token compound (e.g., DE LA CRUZ): tokens[0] AND tokens[1] are particles
    if (len(tokens) > 3
            and tokens[0] in COMPOUND_LAST_PARTICLES
            and tokens[1] in COMPOUND_LAST_PARTICLES):
        splits.append((" ".join(tokens[:3]), tokens[3:]))

    # 2-token compound (e.g., VAN BERG, MC DONALD, ST PIERRE, DE CRUZ)
    if len(tokens) > 2 and tokens[0] in COMPOUND_LAST_PARTICLES:
        splits.append((" ".join(tokens[:2]), tokens[2:]))

    # Default single-token last name (most common case, always tried)
    splits.append((tokens[0], tokens[1:]))

    return splits


# ---------------------------------------------------------------------------
#  CSV FETCH
# ---------------------------------------------------------------------------

def _fetch_latest_csv() -> tuple[str, str]:
    """
    Find and download the most recent parcel_export_YYYYMMDD.csv from
    CCAD-1.  Tries today, then walks backwards INDEX_LOOKBACK_DAYS days.
    Returns (date_string, csv_text).  Raises RuntimeError on total miss.
    """
    today = datetime.now()
    last_err: Optional[Exception] = None
    for delta in range(INDEX_LOOKBACK_DAYS):
        d  = today - timedelta(days=delta)
        ds = d.strftime("%Y%m%d")
        url = f"{CCAD_REPO_RAW}/parcel_export_{ds}.csv"
        try:
            resp = requests.get(url, timeout=60)
            if resp.status_code == 200 and len(resp.text) >= MIN_VALID_CSV_BYTES:
                log.info("Parcel index source: parcel_export_%s.csv (%.1f MB)",
                         ds, len(resp.text) / 1_000_000)
                return ds, resp.text
        except Exception as exc:
            last_err = exc
            log.debug("parcel_export_%s.csv unavailable: %s", ds, exc)
    raise RuntimeError(
        f"No parcel_export CSV found in the last {INDEX_LOOKBACK_DAYS} days "
        f"(last error: {last_err!r})"
    )


# ---------------------------------------------------------------------------
#  INDEX BUILD
# ---------------------------------------------------------------------------

def load_index(force: bool = False) -> None:
    """Build the in-memory index.  Idempotent unless force=True."""
    global _index, _initial_index, _address_index, _loaded_from
    if _index and not force:
        return
    ds, csv_text = _fetch_latest_csv()
    reader = csv.DictReader(io.StringIO(csv_text))

    new_index:         dict[str, list[dict]] = {}
    new_initial_index: dict[str, list[dict]] = {}
    new_address_index: dict[str, list[dict]] = {}
    n_rows  = 0
    n_keys  = 0
    n_ikeys = 0
    n_addrs = 0
    for row in reader:
        n_rows += 1
        first = row.get("First Name", "")
        last  = row.get("Last Name",  "")
        rec = {
            "prop_address":     (row.get("Property Address") or "").strip(),
            "prop_city":        (row.get("Property City")    or "").strip(),
            "prop_state":       "TX",
            "prop_zip":         (row.get("Property Zip")     or "").strip(),
            "mail_address":     (row.get("Mailing Address")  or "").strip(),
            "mail_city":        (row.get("Mailing City")     or "").strip(),
            "mail_state":       (row.get("Mailing State")    or "TX").strip() or "TX",
            "mail_zip":         (row.get("Mailing Zip")      or "").split("-")[0].strip(),
            "year_built":       (row.get("Year Built")       or "").strip(),
            "sqft":             (row.get("Living Area SqFt") or "").strip(),
            "market_value":     (row.get("Market Value")     or "").strip(),
            "deed_year":        (row.get("Deed Year")        or "").strip(),
            "long_term_owner":  (row.get("Long Term Owner")  or "").strip().upper() == "YES",
            "account":          (row.get("Account Number")   or "").strip(),
            # Owner name fields — included so the address-based lookup can
            # populate `owner` / `homeowner_name` on foreclosure records.
            "owner_first":      first.strip(),
            "owner_last":       last.strip(),
            "owner_name":       (f"{last.strip()} {first.strip()}").strip().upper(),
        }
        for key in _keys_for_row(first, last):
            new_index.setdefault(key, []).append(rec)
            n_keys += 1
        for ikey in _initial_keys_for_row(first, last):
            new_initial_index.setdefault(ikey, []).append(rec)
            n_ikeys += 1
        addr_key = _normalize_address(rec["prop_address"])
        if addr_key:
            new_address_index.setdefault(addr_key, []).append(rec)
            n_addrs += 1

    _index         = new_index
    _initial_index = new_initial_index
    _address_index = new_address_index
    _loaded_from   = ds

    # Reset diagnostic counters for the fresh index
    _lookup_stats["total"]         = 0
    _lookup_stats["hits_primary"]  = 0
    _lookup_stats["hits_initial"]  = 0
    _lookup_stats["misses"]        = 0
    _lookup_stats["miss_examples"] = []

    log.info("Parcel index ready: %d rows -> %d primary keys (%d unique), %d initial keys (%d unique), %d addresses (%d unique)",
             n_rows, n_keys, len(new_index), n_ikeys, len(new_initial_index),
             n_addrs, len(new_address_index))


# ---------------------------------------------------------------------------
#  LOOKUP
# ---------------------------------------------------------------------------

def _rank(rec: dict) -> tuple:
    """
    When one homeowner name matches multiple Collin parcels, pick the
    most-likely primary residence: oldest deed_year first, then oldest
    year_built.  Long-term-owner status is NOT used as a rank criterion
    in collin-intel — every property with an adverse filing is in scope
    regardless of how long the owner has held it.
    """
    return (
        int(rec.get("deed_year")  or 9999),
        int(rec.get("year_built") or 9999),
    )

def lookup_parcel_local(homeowner_name: str) -> dict:
    """
    Resolve a clerk-format homeowner name ('LAST FIRST [MIDDLE]...') against
    the local CAD index.  Returns {} on miss so the caller can fall back to
    other sources (Socrata/ArcGIS).

    Strategy:
      1. Try every plausible last-name segmentation (compound surnames first,
         then default single-token) against the primary multi-char index.
      2. If nothing hits, try the initial-only fallback index — but only
         accept results that resolve to exactly one record (uniqueness check).
      3. On any hit, pick the oldest-deed-year parcel via _rank().

    Caller should pass a name already cleaned by pick_homeowner_name() —
    this function does NOT strip 'DECEASED ESTATE' etc.
    """
    _lookup_stats["total"] += 1

    if not _index:
        try:
            load_index()
        except Exception as exc:
            log.warning("Local parcel index unavailable: %s", exc)
            return {}

    n = _normalize(homeowner_name)
    if not n:
        return {}
    tokens = n.split()
    if len(tokens) < 2:
        return {}

    candidate_splits = _candidate_last_splits(tokens)

    # ---- Pass 1: primary multi-char index ----------------------------------
    all_candidates: list[str] = []
    for last, rest in candidate_splits:
        rest = _strip_suffixes(rest)
        if not rest:
            continue
        rest_multi = [t for t in rest if len(t) > 1]

        all_candidates.append(f"{last} {rest[0]}")
        if len(rest) >= 2:
            all_candidates.append(f"{last} {rest[0]} {rest[1]}")
        if rest_multi:
            all_candidates.append(f"{last} {rest_multi[0]}")
            if len(rest_multi) >= 2:
                all_candidates.append(f"{last} {rest_multi[0]} {rest_multi[1]}")
        # Hyphenated-last fallback: try each half
        if "-" in last:
            for half in last.split("-"):
                half = half.strip()
                if half and len(half) >= 2 and rest:
                    all_candidates.append(f"{half} {rest[0]}")

    seen_accounts: set = set()
    hits: list[dict] = []
    for key in all_candidates:
        for rec in _index.get(key, []):
            if rec["account"] in seen_accounts:
                continue
            seen_accounts.add(rec["account"])
            hits.append(rec)

    if hits:
        _lookup_stats["hits_primary"] += 1
        hits.sort(key=_rank)
        return hits[0]

    # ---- Pass 2: initial-only fallback (uniqueness-gated) ------------------
    # Only accept an initial-key match when it resolves to a single record.
    # This protects against returning 'DICKEN R' -> some random Richard / Ronald
    # Dicken when the clerk record was actually about a Robert.
    for last, rest in candidate_splits:
        rest = _strip_suffixes(rest)
        if not rest:
            continue
        for t in rest:
            if not t:
                continue
            init_key = f"{last} {t[0]}"
            initial_matches = _initial_index.get(init_key, [])
            if len(initial_matches) == 1:
                _lookup_stats["hits_initial"] += 1
                return initial_matches[0]

    # ---- Miss ---------------------------------------------------------------
    _lookup_stats["misses"] += 1
    if len(_lookup_stats["miss_examples"]) < 30:
        _lookup_stats["miss_examples"].append(homeowner_name)
    return {}


def lookup_parcel_by_address(prop_address: str, prop_city: str = "") -> dict:
    """Reverse lookup: find the CCAD record (owner + property details) for
    a given property address. Used by the foreclosure scraper, which has
    full addresses but not owner names.

    Returns the same shape as lookup_parcel_local() plus owner_first /
    owner_last / owner_name on hit, or {} on miss.

    The address is normalized through _normalize_address() before lookup
    so 'DRIVE'/'DR', 'NORTH'/'N', etc. all collide correctly.
    """
    if not prop_address:
        return {}
    if not _index:
        try:
            load_index()
        except Exception as e:
            log.warning("parcel index unavailable for address lookup: %s", e)
            return {}
    if not _address_index:
        return {}

    key = _normalize_address(prop_address)
    if not key:
        return {}
    candidates = _address_index.get(key, [])
    if not candidates:
        return {}

    # When city is provided, prefer the same-city match. Collin CCAD is
    # generally one-city-per-address, so this is mostly a tiebreaker for
    # cases where the same numbered street name exists in two cities.
    if prop_city:
        cu = prop_city.upper().strip()
        for c in candidates:
            if c.get("prop_city", "").upper() == cu:
                return c
    return candidates[0]


def log_lookup_stats() -> None:
    """
    Emit a summary of parcel-lookup match quality.  Call this from the
    caller (fetch.py) AFTER all records have been assembled so the numbers
    reflect a full run.
    """
    s = _lookup_stats
    total = s["total"]
    if not total:
        return
    primary = s["hits_primary"]
    initial = s["hits_initial"]
    miss    = s["misses"]
    log.info(
        "Parcel-lookup stats: %d total | primary-hit %d (%.1f%%) | "
        "initial-fallback-hit %d (%.1f%%) | miss %d (%.1f%%)",
        total,
        primary, primary / total * 100,
        initial, initial / total * 100,
        miss,    miss    / total * 100,
    )
    if s["miss_examples"]:
        log.info("Sample misses (first %d) — paste these to Claude to target the next round of fixes:",
                 len(s["miss_examples"]))
        for name in s["miss_examples"]:
            log.info("  miss: %s", name)


# Print stats automatically on interpreter shutdown so no fetch.py edit is
# needed.  The total>0 gate keeps CLI imports / unit tests quiet.
def _log_stats_at_exit() -> None:
    if _lookup_stats["total"] > 0:
        try:
            log_lookup_stats()
        except Exception:
            pass

atexit.register(_log_stats_at_exit)


# ---------------------------------------------------------------------------
#  ENTRY POINT (CLI test)
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys
    logging.basicConfig(level=logging.INFO,
                        format="%(asctime)s  %(levelname)-8s  %(message)s")
    load_index()
    queries = sys.argv[1:] or [
        "SMITH STEPHANIE LORRAINE",
        "WILSON ROBERT E",
        "TAIPALE CURTID",
        "DE LA CRUZ MARIA",
        "VAN DER BERG JOHN",
        "MC DONALD ROBERT",
    ]
    for q in queries:
        r = lookup_parcel_local(q)
        print(f"{q!r:45} -> {r.get('prop_address','(none)')}, "
              f"{r.get('prop_city','')} | "
              f"yb={r.get('year_built','')} "
              f"long_term={r.get('long_term_owner', False)}")
    log_lookup_stats()
