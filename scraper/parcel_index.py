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

Returned dict on a hit:
    prop_address, prop_city, prop_state, prop_zip,
    mail_address, mail_city, mail_state, mail_zip,
    year_built, sqft, market_value, deed_year, long_term_owner (bool),
    account
"""

from __future__ import annotations

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

_index: dict[str, list[dict]] = {}
_loaded_from: Optional[str]   = None


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

    return keys


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
    global _index, _loaded_from
    if _index and not force:
        return
    ds, csv_text = _fetch_latest_csv()
    reader = csv.DictReader(io.StringIO(csv_text))

    new_index: dict[str, list[dict]] = {}
    n_rows = 0
    n_keys = 0
    for row in reader:
        n_rows += 1
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
        }
        for key in _keys_for_row(row.get("First Name", ""), row.get("Last Name", "")):
            new_index.setdefault(key, []).append(rec)
            n_keys += 1
    _index = new_index
    _loaded_from = ds
    log.info("Parcel index ready: %d rows -> %d index entries (%d unique keys)",
             n_rows, n_keys, len(new_index))


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

    Caller should pass a name already cleaned by pick_homeowner_name() —
    this function does NOT strip 'DECEASED ESTATE' etc.
    """
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

    last = tokens[0]
    rest = _strip_suffixes(tokens[1:])
    if not rest:
        return {}

    # Build the same family of candidate keys we used at index time.
    candidates: list[str] = [f"{last} {rest[0]}"]
    if len(rest) >= 2:
        candidates.append(f"{last} {rest[0]} {rest[1]}")
    rest_multi = [t for t in rest if len(t) > 1]
    if rest_multi:
        candidates.append(f"{last} {rest_multi[0]}")
        if len(rest_multi) >= 2:
            candidates.append(f"{last} {rest_multi[0]} {rest_multi[1]}")
    # Hyphenated-last fallback: try each half
    if "-" in last:
        for half in last.split("-"):
            half = half.strip()
            if half and len(half) >= 2 and rest:
                candidates.append(f"{half} {rest[0]}")

    seen_accounts: set = set()
    hits: list[dict] = []
    for key in candidates:
        for rec in _index.get(key, []):
            if rec["account"] in seen_accounts:
                continue
            seen_accounts.add(rec["account"])
            hits.append(rec)

    if not hits:
        return {}

    hits.sort(key=_rank)
    return hits[0]


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
    ]
    for q in queries:
        r = lookup_parcel_local(q)
        print(f"{q!r:45} -> {r.get('prop_address','(none)')}, "
              f"{r.get('prop_city','')} | "
              f"yb={r.get('year_built','')} "
              f"long_term={r.get('long_term_owner', False)}")
