#!/usr/bin/env python3
"""
Collin County, Texas — Motivated Seller Lead Scraper
Clerk portal : https://collin.tx.publicsearch.us/
Parcel data  : Local CCAD index (primary) + Texas Open Data Socrata + Allen ArcGIS (fallbacks)
Pull all records for current year
"""

from __future__ import annotations

import asyncio
import csv
import json
import logging
import re
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any
from urllib.parse import quote

import requests
from bs4 import BeautifulSoup
from playwright.async_api import async_playwright, Page, BrowserContext

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("collin_scraper")

# Make the scraper/ directory importable so parcel_index.py resolves
# whether this is run as `python fetch.py` from scraper/ or as
# `python scraper/fetch.py` from the repo root.
_SCRAPER_DIR = Path(__file__).resolve().parent
if str(_SCRAPER_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRAPER_DIR))

try:
    from parcel_index import lookup_parcel_local, load_index as _load_local_index
    _LOCAL_INDEX = True
    log.info("Local CCAD parcel index module loaded")
except ImportError as _e:
    log.warning("parcel_index.py not found — local CAD index disabled (%s)", _e)
    _LOCAL_INDEX = False
    def lookup_parcel_local(name: str) -> dict: return {}
    def _load_local_index() -> None: pass


CLERK_BASE     = "https://collin.tx.publicsearch.us"
LOOKBACK_DAYS  = 7
RETRY_ATTEMPTS = 3
RETRY_DELAY    = 5
DEBUG          = True

SOCRATA_OWNER = "https://data.texas.gov/resource/ahis-pci3.json"
SOCRATA_APPR  = "https://data.texas.gov/resource/nne4-8riu.json"

ARCGIS_URL = (
    "https://gismaps.cityofallen.org/arcgis/rest/services/"
    "ReferenceData/Collin_County_Appraisal_District_Parcels/MapServer/1/query"
)

DOC_TYPE_MAP: dict[str, tuple[str, str, list[str]]] = {
    "LP":       ("LP",       "Lis Pendens",             ["Lis pendens", "Pre-foreclosure"]),
    "NOFC":     ("NOFC",     "Notice of Foreclosure",   ["Pre-foreclosure"]),
    "TAXDEED":  ("TAXDEED",  "Tax Deed",                ["Tax lien"]),
    "JUD":      ("JUD",      "Judgment",                ["Judgment lien"]),
    "CCJ":      ("CCJ",      "Certified Judgment",      ["Judgment lien"]),
    "DRJUD":    ("DRJUD",    "Domestic Judgment",       ["Judgment lien"]),
    "LNCORPTX": ("LNCORPTX", "Corp Tax Lien",           ["Tax lien"]),
    "LNIRS":    ("LNIRS",    "IRS Lien",                ["Tax lien"]),
    "LNFED":    ("LNFED",    "Federal Lien",            ["Tax lien"]),
    "LN":       ("LN",       "Lien",                    ["Mechanic lien"]),
    "LNMECH":   ("LNMECH",   "Mechanic Lien",           ["Mechanic lien"]),
    "LNHOA":    ("LNHOA",    "HOA Lien",                ["Mechanic lien"]),
    "MEDLN":    ("MEDLN",    "Medicaid Lien",           ["Judgment lien"]),
    "PRO":      ("PRO",      "Probate Document",        ["Probate / estate"]),
}

ROOT          = Path(__file__).resolve().parent.parent
DASHBOARD_DIR = ROOT / "dashboard"
DATA_DIR      = ROOT / "data"
DEBUG_DIR     = ROOT / "debug"
for _d in [DASHBOARD_DIR, DATA_DIR, DEBUG_DIR]:
    _d.mkdir(parents=True, exist_ok=True)


# ==============================================================================
#  HELPERS
# ==============================================================================

def safe_str(val: Any) -> str:
    return str(val).strip() if val is not None else ""

def parse_amount(raw: str) -> float | None:
    cleaned = re.sub(r"[^\d.]", "", raw)
    try:
        return float(cleaned) if cleaned else None
    except ValueError:
        return None

def name_variants(full_name: str) -> list[str]:
    full_name = full_name.strip().upper()
    variants: list[str] = [full_name]
    parts = full_name.split()
    if len(parts) >= 2:
        flipped = f"{' '.join(parts[1:])} {parts[0]}"
        if flipped not in variants:
            variants.append(flipped)
        comma = f"{parts[0]}, {' '.join(parts[1:])}"
        if comma not in variants:
            variants.append(comma)
    return variants

def _abs_url(href: str) -> str:
    if not href:
        return ""
    return href if href.startswith("http") else f"{CLERK_BASE}{href}"

def _normalise_date(raw: str) -> str:
    if not raw:
        return ""
    if re.match(r"\d{1,2}/\d{1,2}/\d{4}", raw):
        return raw
    m = re.match(r"(\d{4})-(\d{2})-(\d{2})", raw)
    if m:
        return f"{m.group(2)}/{m.group(3)}/{m.group(1)}"
    return raw

def _parse_situsconcat(situs: str) -> tuple[str, str, str, str]:
    situs = situs.strip()
    zip_m = re.search(r"\b(\d{5})(?:-\d{4})?\s*$", situs)
    prop_zip = zip_m.group(1) if zip_m else ""
    remainder = situs[:zip_m.start()].strip(" ,") if zip_m else situs
    st_m = re.search(r",?\s*([A-Z]{2})\s*$", remainder)
    prop_state = st_m.group(1) if st_m else "TX"
    remainder = remainder[:st_m.start()].strip(" ,") if st_m else remainder
    parts = remainder.rsplit(",", 1)
    if len(parts) == 2:
        prop_addr = parts[0].strip()
        prop_city = parts[1].strip()
    else:
        prop_addr = remainder.strip()
        prop_city = ""
    return prop_addr, prop_city, prop_state, prop_zip

def _map_doc_type(raw_type: str) -> tuple[str, str]:
    t = raw_type.upper().strip()
    if t in DOC_TYPE_MAP:
        return t, DOC_TYPE_MAP[t][1]
    # Affidavit of Heirship is a probate-precursor document filed when heirs
    # claim ownership after a death. MUST be checked before the "IRS" rule
    # below, since "HEIRSHIP" contains the substring "IRS" and would otherwise
    # be mislabeled as an IRS Lien.
    if "HEIRSHIP" in t:
        return "PRO", "Affidavit of Heirship"
    # All RELEASE documents (Release of State Tax Lien, Release of Child Support
    # Lien, Release of Lis Pendens, etc.) are debt-paid notices — not motivated-
    # seller signals. MUST be checked before the generic "LIEN" rule below,
    # since phrases like "RELEASE STATE TAX LIEN" would otherwise fall through
    # to the LIEN catch and be miscategorized as LN.
    if "RELEASE" in t:
        return "RELLP", "Release"
    if "LIS PENDENS" in t:
        return "LP", "Lis Pendens"
    if "FORECLOSURE" in t:
        return "NOFC", "Notice of Foreclosure"
    if "TAX DEED" in t:
        return "TAXDEED", "Tax Deed"
    if "IRS" in t or "INTERNAL REVENUE" in t:
        return "LNIRS", "IRS Lien"
    if "FEDERAL TAX" in t or ("FEDERAL" in t and "LIEN" in t):
        return "LNFED", "Federal Lien"
    if "CORP" in t and ("TAX" in t or "LIEN" in t):
        return "LNCORPTX", "Corp Tax Lien"
    if "HOA" in t or "HOMEOWNER" in t or "HOME OWNER" in t:
        return "LNHOA", "HOA Lien"
    if "MECHANIC" in t:
        return "LNMECH", "Mechanic Lien"
    if "MEDICAID" in t:
        return "MEDLN", "Medicaid Lien"
    if "JUDGMENT" in t or "JUDGEMENT" in t:
        if "CERTIFIED" in t:
            return "CCJ", "Certified Judgment"
        if "DOMESTIC" in t:
            return "DRJUD", "Domestic Judgment"
        return "JUD", "Judgment"
    if "PROBATE" in t:
        return "PRO", "Probate Document"
    if "NOTICE OF COMMENCEMENT" in t:
        return "NOC", "Notice of Commencement"
    if "LIEN" in t:
        return "LN", "Lien"
    return t, raw_type

async def screenshot(page: Page, name: str) -> None:
    if not DEBUG:
        return
    try:
        await page.screenshot(path=str(DEBUG_DIR / f"{name}.png"), full_page=True)
        log.info("  screenshot: %s.png", name)
    except Exception as exc:
        log.warning("  screenshot failed: %s", exc)

async def save_html(page: Page, name: str) -> None:
    if not DEBUG:
        return
    try:
        (DEBUG_DIR / f"{name}.html").write_text(
            await page.content(), encoding="utf-8")
        log.info("  html saved: %s.html", name)
    except Exception:
        pass

async def wait_for_table(page: Page, timeout: int = 20_000) -> bool:
    """
    Wait for the results table to fully render after a React state change.
    ROOT CAUSE FIX: previously asyncio.sleep(3) was used which was too short
    for React to finish fetching and rendering data after the year filter click.
    This caused page.content() to capture 'Loading...' HTML with no table.
    """
    try:
        await page.wait_for_selector(
            "table tbody tr",
            timeout=timeout,
            state="attached"
        )
        await asyncio.sleep(0.5)
        return True
    except Exception:
        try:
            await page.wait_for_selector(
                "[class*='no-result'], [class*='empty-state'], [class*='noResults']",
                timeout=3_000,
            )
            return True
        except Exception:
            return False


# ==============================================================================
#  OWNER NORMALIZATION & GRANTOR CLASSIFICATION
#  Decides which party in a clerk record is the actual homeowner.
# ==============================================================================

# Decedent / AKA / DBA noise tokens that pollute clerk owner strings.
_ESTATE_NOISE = re.compile(
    r"\b("
    r"DECEASED\s+ESTATE|ESTATE\s+OF|EST\s+OF|"
    r"DECEASED|DECD|DEC'?D|"
    r"HEIRS\s+(AT\s+LAW\s+)?OF|"
    r"DBA|D/B/A|AKA|A/K/A"
    r")\b",
    re.IGNORECASE,
)

def clean_owner(name: str) -> str:
    """Strip decedent / estate / AKA / DBA noise so the remainder is a real
    parcel-owner name that has a chance of matching CAD data."""
    if not name:
        return ""
    s = _ESTATE_NOISE.sub(" ", name)
    s = re.sub(r"[,;]", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s.upper()


# Patterns that signal a name is NOT a homeowner — it's a plaintiff,
# filer, lender, government entity, HOA, subdivision label, or placeholder.
_NON_HOMEOWNER_RE = re.compile(
    # Government
    r"\bSTATE\s+OF\s+TEXAS\b|\bTEXAS\s+STATE\s+OF\b|"
    r"\bUNITED\s+STATES\s+OF\s+AMERICA\b|\bINTERNAL\s+REVENUE\s+SERVICE\b|"
    r"\bU\.?S\.?\s+TREASURY\b|\bTEXAS\s+COMPTROLLER\b|"
    r"\bTEXAS\s+WORKFORCE\s+COMMISSION\b|\bCOLLIN\s+COUNTY\b|"
    r"\bCITY\s+OF\s+\w+|\bCOUNTY\s+OF\s+\w+|"
    r"\bMUNICIPAL\s+(WATER|UTILITY)\s+DISTRICT\b|\bISD\b|"
    # HOAs / community associations
    r"\b(COMMUNITY\s+)?(ASSOCIATION|ASS?N|ASSOC|HOMEOWNERS)\b|"
    # Development-named corporate entities ("TRAILS AT RIVERSTONE COMMUNITY INC")
    r"\b(COMMUNITY|VILLAGE|RANCH|ESTATES|TRAILS|GARDENS|HEIGHTS|RIDGE|"
    r"PARK|MEADOWS|PRESERVE|CROSSING|LANDING|HARBOR|POINTE?)"
    r"\b[^,]{0,40}\b(INC|LLC|CORP|LTD|CO)\b|"
    # Lenders / servicers / banks
    r"\b(MORTGAGE|SERVICING|BANK|FINANCIAL|CREDIT\s+UNION)\b|"
    # Subdivision / development labels
    r"\b(ADDITION|SUBDIVISION|PHASE)\b|"
    # Placeholders
    r"^\s*PUBLIC\s*$",
    re.IGNORECASE,
)

# Standalone corporate suffix tokens.  Distinct from _NON_HOMEOWNER_RE which
# catches explicit non-homeowner *patterns*; this catches generic business
# entities (LLCs, INCs, LPs) that are almost always filers in lien/judgment
# records, not the actual property owner.
_CORPORATE_SUFFIX_RE = re.compile(
    r"\b(INC|INCORPORATED|LLC|L\.L\.C|CORP|CORPORATION|LTD|LIMITED|"
    r"COMPANY|L\.P|LP|LLP|PLLC)\b",
    re.IGNORECASE,
)

def is_non_homeowner(name: str) -> bool:
    """True when the name is almost certainly a plaintiff / filer / entity /
    placeholder, not an actual property owner."""
    if not name:
        return True
    if len(name.split()) < 2:           # 'PUBLIC', 'INSPIRATION', etc.
        return True
    return bool(_NON_HOMEOWNER_RE.search(name))

def looks_corporate(name: str) -> bool:
    """
    True if `name` carries a generic corporate-suffix token (INC, LLC, CORP,
    LTD, COMPANY, LP, LLP, PLLC).  Distinct from is_non_homeowner: that catches
    specific non-homeowner patterns (banks, HOAs, subdivisions); this catches
    *generic* business entities that aren't called out by those patterns —
    e.g. 'BRIGHTVIEW LANDSCAPE DEVELOPMENT INC', 'TET TITAN ELECTRIC TEXAS LLC',
    'M1 REAL ESTATE PARTNERS LTD'.  These are virtually always filers in
    lien/judgment records, never the homeowner being targeted.
    """
    if not name:
        return False
    return bool(_CORPORATE_SUFFIX_RE.search(name))


# Doc-type categories where the clerk indexes the FILER as grantor and the
# actual property owner as grantee.
GRANTEE_AS_HOMEOWNER_CATS = {
    "LP", "LNHOA", "LNMECH", "LNCORPTX", "LNFED", "LNIRS",
    "JUD", "CCJ", "DRJUD", "MEDLN", "NOFC",
}

def pick_homeowner_name(cat: str, owner: str, grantee: str) -> str:
    """
    Return the cleaned name most likely to match a CAD parcel owner.

    - PRO: decedent's name is in the grantor field (after stripping noise)
    - Lien/judgment cats: grantor is the filer (creditor, contractor,
      plaintiff, taxing authority), grantee is the homeowner.  Prefer
      grantee when grantor looks like a filer — either matching the
      explicit non-homeowner regex OR carrying a generic corporate suffix.
      When BOTH parties look like entities, the record isn't a motivated-
      seller lead — return empty so caller marks it not_actionable.
    - Default: use grantor, fall back to grantee.
    """
    owner_clean   = clean_owner(owner)
    grantee_clean = clean_owner(grantee)

    if cat == "PRO":
        return owner_clean

    if cat in GRANTEE_AS_HOMEOWNER_CATS:
        grantor_is_filer = (
            is_non_homeowner(owner_clean)
            or looks_corporate(owner_clean)
        )
        if grantor_is_filer:
            grantee_is_homeowner = (
                grantee_clean
                and not is_non_homeowner(grantee_clean)
                and not looks_corporate(grantee_clean)
            )
            if grantee_is_homeowner:
                return grantee_clean
            # Both parties are entities / non-homeowner → not actionable
            return ""

    # Default path: grantor if usable, else grantee as last-ditch fallback
    if not is_non_homeowner(owner_clean):
        return owner_clean

    if grantee_clean and not is_non_homeowner(grantee_clean):
        return grantee_clean

    return ""


# ==============================================================================
#  PARCEL LOOKUP
#
#  Resolution order:
#    1) Local CCAD index (parcel_index.py)        — primary
#    2) Socrata `ahis-pci3` / `nne4-8riu`         — fallback
#    3) Allen GIS ArcGIS service                  — fallback
#    4) Socrata fuzzy (substring) match           — last resort
# ==============================================================================

_parcel_cache: dict[str, dict] = {}

def _socrata_lookup(owner_variant: str) -> dict:
    safe_name = owner_variant.replace("'", "''")
    for endpoint in [SOCRATA_OWNER, SOCRATA_APPR]:
        try:
            resp = requests.get(
                endpoint,
                params={"$where": f"ownername = '{safe_name}'", "$limit": 1},
                timeout=10,
                headers={"Accept": "application/json"},
            )
            if resp.status_code != 200:
                continue
            rows = resp.json()
            if not (isinstance(rows, list) and rows):
                continue
            r = rows[0]
            situs      = safe_str(r.get("situsconcat", ""))
            mail_addr  = safe_str(r.get("owneraddrline1", ""))
            mail_city  = safe_str(r.get("owneraddrcity", ""))
            mail_state = safe_str(r.get("owneraddrstate", "")) or "TX"
            mail_zip   = safe_str(r.get("owneraddrzip", ""))
            if "-" in mail_zip:
                mail_zip = mail_zip.split("-")[0]
            prop_addr, prop_city, prop_state, prop_zip = _parse_situsconcat(situs)
            if prop_addr or mail_addr:
                return {
                    "prop_address": prop_addr,
                    "prop_city":    prop_city,
                    "prop_state":   prop_state or "TX",
                    "prop_zip":     prop_zip,
                    "mail_address": mail_addr,
                    "mail_city":    mail_city,
                    "mail_state":   mail_state,
                    "mail_zip":     mail_zip,
                }
        except Exception as exc:
            log.debug("Socrata error %r: %s", owner_variant[:40], exc)
    return {}

def _socrata_fuzzy(owner_variant: str) -> dict:
    parts = owner_variant.strip().split()
    if not parts:
        return {}
    search_word = next((p for p in parts if len(p) > 2), parts[0])
    safe_word = search_word.replace("'", "''")
    for endpoint in [SOCRATA_OWNER, SOCRATA_APPR]:
        try:
            resp = requests.get(
                endpoint,
                params={"$where": f"ownername LIKE '%{safe_word}%'", "$limit": 5},
                timeout=10,
                headers={"Accept": "application/json"},
            )
            if resp.status_code != 200:
                continue
            rows = resp.json()
            if not (isinstance(rows, list) and rows):
                continue
            for r in rows:
                rname = safe_str(r.get("ownername", "")).upper()
                sig_parts = [p for p in parts if len(p) > 2]
                if all(p in rname for p in sig_parts):
                    situs      = safe_str(r.get("situsconcat", ""))
                    mail_addr  = safe_str(r.get("owneraddrline1", ""))
                    mail_city  = safe_str(r.get("owneraddrcity", ""))
                    mail_state = safe_str(r.get("owneraddrstate", "")) or "TX"
                    mail_zip   = safe_str(r.get("owneraddrzip", ""))
                    if "-" in mail_zip:
                        mail_zip = mail_zip.split("-")[0]
                    prop_addr, prop_city, prop_state, prop_zip = _parse_situsconcat(situs)
                    if prop_addr or mail_addr:
                        return {
                            "prop_address": prop_addr,
                            "prop_city":    prop_city,
                            "prop_state":   prop_state or "TX",
                            "prop_zip":     prop_zip,
                            "mail_address": mail_addr,
                            "mail_city":    mail_city,
                            "mail_state":   mail_state,
                            "mail_zip":     mail_zip,
                        }
        except Exception as exc:
            log.debug("Socrata fuzzy error %r: %s", owner_variant[:40], exc)
    return {}

def _arcgis_lookup(owner_variant: str) -> dict:
    safe_name = owner_variant.replace("'", "''")
    try:
        resp = requests.get(
            ARCGIS_URL,
            params={
                "where": f"file_as_name LIKE '{safe_name}'",
                "outFields": (
                    "file_as_name,addr_line1,addr_city,addr_state,addr_zip,"
                    "situs_num,situs_street,situs_city"
                ),
                "returnGeometry": "false",
                "resultRecordCount": 1,
                "f": "json",
            },
            timeout=10,
        )
        if resp.status_code != 200:
            return {}
        data = resp.json()
        if data.get("error"):
            return {}
        features = data.get("features", [])
        if not features:
            return {}
        attrs = features[0].get("attributes", {})
        snum = safe_str(attrs.get("situs_num", ""))
        sstr = safe_str(attrs.get("situs_street", ""))
        return {
            "prop_address": f"{snum} {sstr}".strip(),
            "prop_city":    safe_str(attrs.get("situs_city", "")),
            "prop_state":   "TX",
            "prop_zip":     "",
            "mail_address": safe_str(attrs.get("addr_line1", "")),
            "mail_city":    safe_str(attrs.get("addr_city", "")),
            "mail_state":   safe_str(attrs.get("addr_state", "")) or "TX",
            "mail_zip":     safe_str(attrs.get("addr_zip", "")),
        }
    except Exception as exc:
        log.debug("ArcGIS error %r: %s", owner_variant[:40], exc)
        return {}

def lookup_parcel(owner: str) -> dict:
    """
    Resolve a (cleaned) homeowner name to a parcel record.

    Pipeline: local index -> Socrata exact -> ArcGIS exact -> Socrata fuzzy.
    Caller must have already passed the result of pick_homeowner_name() —
    this function does not re-clean.
    """
    if not owner:
        return {}
    cache_key = owner.strip().upper()
    if cache_key in _parcel_cache:
        return _parcel_cache[cache_key]

    # 1) Primary: local CCAD index. Fast, complete for Collin County,
    #    and returns extra fields (year_built, long_term_owner, sqft, etc.).
    if _LOCAL_INDEX:
        try:
            result = lookup_parcel_local(owner)
            if result.get("prop_address") or result.get("mail_address"):
                _parcel_cache[cache_key] = result
                return result
        except Exception as exc:
            log.warning("Local index lookup failed for %r: %s", owner[:40], exc)

    # 2) Fallback: Socrata exact match (statewide CAD feed)
    result: dict = {}
    for variant in name_variants(owner):
        result = _socrata_lookup(variant)
        if result.get("prop_address") or result.get("mail_address"):
            _parcel_cache[cache_key] = result
            return result

    # 3) Fallback: Allen ArcGIS (Collin parcels published by City of Allen)
    for variant in name_variants(owner):
        result = _arcgis_lookup(variant)
        if result.get("prop_address") or result.get("mail_address"):
            _parcel_cache[cache_key] = result
            return result

    # 4) Last resort: Socrata fuzzy substring match.
    #    Gate at 4 tokens so names like 'PATLOLLA PRAVEEN KUMAR REDDY' qualify.
    if len(owner.split()) <= 4:
        result = _socrata_fuzzy(owner.strip().upper())
        if result.get("prop_address") or result.get("mail_address"):
            _parcel_cache[cache_key] = result
            return result

    _parcel_cache[cache_key] = {}
    return {}


# ==============================================================================
#  CLERK PORTAL — NETWORK INTERCEPTION FOR ONE-CLICK /doc/{id} URLs
#
#  The React app doesn't render <a href="/doc/..."> tags in the DOM — rows
#  navigate via onClick handlers, so HTML scraping can't find the internal
#  document IDs.  Instead, we intercept the JSON API responses the React app
#  makes to fill its results table.  Those responses pair the public doc
#  number (12-14 digits, year-prefixed) with the internal database ID used
#  in /doc/{id} URLs.
# ==============================================================================

# Shared map filled by _on_response() during scraping, consumed by
# _parse_table() to build one-click clerk URLs.
captured_doc_links: dict[str, str] = {}


def _scan_json_for_doc_links(obj: Any, out: dict[str, str]) -> None:
    """
    Walk a JSON tree looking for objects containing both a doc-number-like
    field (12-14 digits matching the clerk instrument-number format) AND a
    shorter internal-ID field.  Adds doc_num -> '/doc/{id}' entries to `out`.
    """
    if isinstance(obj, list):
        for item in obj:
            _scan_json_for_doc_links(item, out)
        return
    if not isinstance(obj, dict):
        return

    doc_num: str | None = None
    doc_id:  str | None = None
    for k, v in obj.items():
        if not isinstance(v, (str, int)):
            continue
        vs = str(v).strip()
        kl = k.lower()
        # Clerk instrument number: 12-14 digits, year-prefixed
        if re.match(r"^\d{12,14}$", vs) and any(p in kl for p in (
            "documentnumber", "instrumentnumber", "docnum", "doc_num",
            "instrument_number", "filingnumber", "filing_number",
        )):
            doc_num = vs
        # Internal database ID: 6-12 digits in a field named like 'id'
        if re.match(r"^\d{6,12}$", vs) and (
            kl == "id" or kl.endswith("_id")
            or kl in ("docid", "documentid", "instrumentid")
        ):
            doc_id = vs

    if doc_num and doc_id:
        out[doc_num] = f"/doc/{doc_id}"

    # Recurse into nested values
    for v in obj.values():
        _scan_json_for_doc_links(v, out)


async def _on_response(response) -> None:
    """
    Network-response listener registered on the browser context.  Captures
    JSON bodies from likely search-API endpoints and harvests doc_num ->
    /doc/{id} mappings into the shared captured_doc_links dict.
    """
    try:
        url = response.url.lower()
        if not any(p in url for p in (
            "/search", "/result", "/documents", "/instrument", "/api"
        )):
            return
        ct = response.headers.get("content-type", "") or ""
        if "json" not in ct.lower():
            return
        try:
            data = await response.json()
        except Exception:
            return
        before = len(captured_doc_links)
        _scan_json_for_doc_links(data, captured_doc_links)
        gained = len(captured_doc_links) - before
        if gained:
            log.debug("Captured %d new doc-link entries from %s (total: %d)",
                      gained, response.url, len(captured_doc_links))
    except Exception:
        # Never let listener errors crash the scrape
        pass


def build_search_url(term: str) -> str:
    return (
        f"{CLERK_BASE}/results"
        f"?searchType=quickSearch&department=RP&searchOcrText=false"
        f"&searchTerm={term}"
    )

def _parse_table(html: str, date_from: datetime, date_to: datetime,
                 doc_links: dict[str, str] | None = None) -> tuple[list[dict], bool]:
    """
    Parse a search-results page into record dicts.

    doc_links: optional dict mapping doc_num -> '/doc/{id}' href (filled by
    network interception in run_clerk_scrape).  When a doc_num is in the
    map, each record's clerk_url is built as a one-click direct link.  Falls
    back to a /doc/ link in the row HTML, then to the two-step search-results
    URL only when neither is available.
    """
    soup = BeautifulSoup(html, "lxml")
    records = []
    all_old = True

    table = soup.find("table")
    if not table:
        return records, False

    headers = [th.get_text(" ", strip=True).lower()
               for th in table.find_all("th")]
    if headers:
        log.info("  Table columns: %s", headers)

    # Log first few dates seen for diagnostics
    sample_dates = []
    for tr in table.find_all("tr")[1:6]:
        cells = [td.get_text(" ", strip=True) for td in tr.find_all("td")]
        if cells and len(cells) > 0:
            row_tmp = dict(zip(headers, cells))
            d = row_tmp.get("recorded date", "")
            if d:
                sample_dates.append(d)
    if sample_dates:
        log.info("  Sample dates on page: %s | looking for %s to %s",
                 sample_dates, date_from.strftime("%m/%d/%Y"), date_to.strftime("%m/%d/%Y"))

    for tr in table.find_all("tr")[1:]:
        cells = [td.get_text(" ", strip=True) for td in tr.find_all("td")]
        if not cells:
            continue
        row = dict(zip(headers, cells))

        def g(*keys) -> str:
            for k in keys:
                v = row.get(k, "")
                if v and v != "N/A":
                    return v.strip()
            return ""

        raw_date = g("recorded date")
        doc_num  = g("doc number")
        owner    = g("grantor")
        grantee  = g("grantee")
        doc_type = g("doc type")
        legal    = g("legal description")

        # Amount: try named columns first, then fall back to scanning every
        # cell for a dollar pattern.  Judgments, IRS / state tax liens, and
        # HOA liens often carry an amount directly in the index.
        amount = g(
            "consideration", "amount", "amt", "amount owed",
            "consideration amount", "judgment amount", "debt amount",
            "total amount", "value", "lien amount",
        )
        if not amount:
            for cell in cells:
                m = re.search(r"\$\s?[\d,]+(?:\.\d{2})?", cell)
                if m and "DOC" not in cell.upper():
                    amount = m.group(0).strip()
                    break

        if not raw_date:
            continue

        try:
            rec_date = datetime.strptime(raw_date, "%m/%d/%Y")
        except ValueError:
            continue

        if rec_date < date_from:
            all_old = True
            continue
        elif rec_date > date_to:
            continue

        all_old = False

        if not owner or owner == "N/A":
            continue

        # Prefer the direct /doc/{id} link from the network-captured map
        # (one click straight to detail).  Fall back to a /doc/ link in the
        # row HTML, then to the search-results URL only if neither is found.
        if doc_links and doc_num and doc_num in doc_links:
            clerk_url = _abs_url(doc_links[doc_num])
        else:
            link = tr.find("a", href=lambda h: h and "/doc/" in h)
            if link:
                clerk_url = _abs_url(link["href"])
            elif doc_num:
                # Two-click search-results fallback
                clerk_url = (
                    f"{CLERK_BASE}/results"
                    f"?department=RP"
                    f"&documentNumberRange=%5B%22{doc_num}%22%5D"
                    f"&searchType=advancedSearch"
                )
            else:
                clerk_url = ""

        cat, cat_label = _map_doc_type(doc_type)

        # Skip unrecognized doc types (DEED, RELEASE, mortgages, etc.).
        # Only keep records whose mapped cat is in our motivated-seller map.
        if cat not in DOC_TYPE_MAP:
            continue

        records.append({
            "doc_num":   doc_num,
            "doc_type":  doc_type,
            "filed":     raw_date,
            "cat":       cat,
            "cat_label": cat_label,
            "owner":     owner,
            "grantee":   grantee,
            "legal":     legal,
            "amount":    amount,
            "clerk_url": clerk_url,
        })

    return records, all_old

async def _click_next(page: Page) -> bool:
    try:
        # Try Playwright locator first
        btn = page.locator("button[aria-label='next page']").first
        if await btn.count() > 0:
            disabled = await btn.get_attribute("disabled")
            aria_disabled = await btn.get_attribute("aria-disabled")
            if disabled is None and aria_disabled != "true":
                await btn.click()
                await page.wait_for_load_state("networkidle", timeout=10_000)
                await wait_for_table(page, timeout=15_000)
                return True
            else:
                log.info("  Next button is disabled — last page reached")
                return False
    except Exception:
        pass
    # Fallback: JS click
    try:
        clicked = await page.evaluate("""
            (() => {
                const btn = document.querySelector("button[aria-label='next page']");
                if (btn && !btn.disabled && btn.getAttribute('aria-disabled') !== 'true') {
                    btn.click();
                    return true;
                }
                return false;
            })()
        """)
        if clicked:
            await page.wait_for_load_state("networkidle", timeout=10_000)
            await wait_for_table(page, timeout=15_000)
            return True
    except Exception:
        pass
    return False

async def _apply_year_filter(page: Page, year: int) -> None:
    """
    Click the year checkbox so the portal shows current-year records first.
    Required even in 7-day mode — without it the portal defaults to oldest
    records (1900s) and the date filter stops pagination immediately.
    """
    try:
        clicked = await page.evaluate(f"""
            (() => {{
                const cb = document.getElementById('recordedYears_{year}');
                if (cb) {{ cb.click(); return true; }}
                return false;
            }})()
        """)
        if clicked:
            log.info("  Year %d filter applied", year)
            table_appeared = await wait_for_table(page, timeout=20_000)
            if not table_appeared:
                log.warning("  Table did not appear after year filter — sleeping 5s")
                await asyncio.sleep(5)

            # Sort by Recorded Date DESCENDING via JavaScript
            # (Playwright click times out because the header is not yet
            # interactive right after the year filter re-render)
            try:
                await asyncio.sleep(2)  # Let React settle after year filter
                sorted_ok = await page.evaluate("""
                    (() => {
                        const ths = document.querySelectorAll('th');
                        for (const th of ths) {
                            if (th.textContent.trim() === 'Recorded Date') {
                                th.click();
                                return true;
                            }
                        }
                        return false;
                    })()
                """)
                if sorted_ok:
                    await wait_for_table(page, timeout=10_000)
                    # Click again for descending order
                    await page.evaluate("""
                        (() => {
                            const ths = document.querySelectorAll('th');
                            for (const th of ths) {
                                if (th.textContent.trim() === 'Recorded Date') {
                                    th.click();
                                }
                            }
                        })()
                    """)
                    await wait_for_table(page, timeout=10_000)
                    log.info("  Sorted by Recorded Date descending via JS")
                else:
                    log.warning("  Recorded Date header not found for sort")
            except Exception as sort_exc:
                log.warning("  Sort error: %s", sort_exc)
        else:
            log.warning("  Year %d checkbox not found in DOM", year)
    except Exception as exc:
        log.warning("  Year filter error: %s", exc)

async def run_clerk_scrape(date_from: datetime, date_to: datetime) -> list[dict]:
    all_records: list[dict] = []
    search_terms = ["JUD", "CCJ", "LNHOA", "PRO",
                    "LN", "LNMECH", "LNIRS", "LNFED",
                    "LP", "NOFC", "TAXDEED"]

    # Reset captured doc-link map for this run
    captured_doc_links.clear()

    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=True,
            args=[
                "--no-sandbox",
                "--disable-dev-shm-usage",
                "--disable-blink-features=AutomationControlled",
                "--disable-infobars",
                "--window-size=1280,900",
            ],
        )
        context = await browser.new_context(
            user_agent=(
                "Mozilla/5.0 (X11; Linux x86_64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/123.0.0.0 Safari/537.36"
            ),
            viewport={"width": 1280, "height": 900},
            extra_http_headers={
                "Accept-Language": "en-US,en;q=0.9",
                "Accept": ("text/html,application/xhtml+xml,"
                           "application/xml;q=0.9,*/*;q=0.8"),
            },
        )
        await context.add_init_script("""
            Object.defineProperty(navigator, 'webdriver', {get: () => undefined});
            Object.defineProperty(navigator, 'plugins', {get: () => [1,2,3,4,5]});
            Object.defineProperty(navigator, 'languages',
                                  {get: () => ['en-US','en']});
            window.chrome = {runtime: {}};
        """)

        # Register the network-response listener so doc_num -> /doc/{id}
        # mappings get harvested from API responses as the React app loads
        # search results and paginates.
        context.on("response", _on_response)

        warmup = await context.new_page()
        try:
            await warmup.goto(CLERK_BASE, timeout=30_000, wait_until="networkidle")
            await asyncio.sleep(3)
            await screenshot(warmup, "homepage")
        except Exception as exc:
            log.warning("Warmup non-fatal: %s", exc)
        finally:
            await warmup.close()

        page: Page | None = None
        for term in search_terms:
            p = await context.new_page()
            try:
                url = build_search_url(term)
                log.info("Trying term %s", term)
                await p.goto(url, timeout=60_000, wait_until="networkidle")
                await asyncio.sleep(4)
                title = await p.title()
                if "Loading" in title:
                    for _ in range(35):
                        await asyncio.sleep(1)
                        title = await p.title()
                        if "Loading" not in title:
                            break
                if "Loading" not in title:
                    log.info("Loaded with term %s | title: %s", term, title)
                    page = p
                    break
                else:
                    await p.close()
            except Exception as exc:
                log.warning("Term %s failed: %s", term, exc)
                await p.close()
            await asyncio.sleep(2)

        if page is None:
            log.error("Could not load any search page")
            await browser.close()
            return all_records

        try:
            await _apply_year_filter(page, date_to.year)
            await screenshot(page, "after_filter")
            await save_html(page, "after_filter")

            page_num = 1
            consecutive_old = 0
            max_pages = 2000

            while page_num <= max_pages:
                table_ready = await wait_for_table(page, timeout=15_000)
                if not table_ready:
                    log.warning("Page %d: table not found after wait", page_num)

                html = await page.content()

                # Belt-and-suspenders: also try JS DOM extraction in case the
                # React app does happen to render <a href="/doc/..."> for some
                # rows.  Merged with the network-captured map.
                try:
                    js_doc_links = await page.evaluate("""
                        () => {
                            const result = {};
                            document.querySelectorAll('a[href*="/doc/"]').forEach(a => {
                                const row = a.closest('tr');
                                if (!row) return;
                                const cells = row.querySelectorAll('td');
                                for (const cell of cells) {
                                    const text = cell.textContent.trim();
                                    if (/^\\d{12,14}$/.test(text)) {
                                        result[text] = a.getAttribute('href');
                                        break;
                                    }
                                }
                            });
                            return result;
                        }
                    """)
                except Exception as exc:
                    log.debug("Doc-link JS extraction failed: %s", exc)
                    js_doc_links = {}

                # Network-captured (primary) merged with JS-extracted (backup)
                combined_links = {**captured_doc_links, **js_doc_links}

                recs, all_old = _parse_table(html, date_from, date_to, combined_links)
                log.info("Page %d: %d records (all_old=%s) | total so far: %d "
                         "| doc-link map: %d entries",
                         page_num, len(recs), all_old, len(all_records),
                         len(combined_links))
                all_records.extend(recs)

                if all_old and page_num > 2:
                    consecutive_old += 1
                    if consecutive_old >= 3:
                        log.info("3 consecutive old pages — stopping at page %d", page_num)
                        break
                else:
                    consecutive_old = 0

                if not await _click_next(page):
                    log.info("No more pages after page %d", page_num)
                    break
                page_num += 1

            log.info("Pagination done: %d records from %d pages",
                     len(all_records), page_num)

        except Exception as exc:
            log.error("Scrape error: %s", exc)
            await screenshot(page, "error_main")
        finally:
            await page.close()

        await browser.close()

    log.info("Raw records collected: %d | doc-link entries captured: %d",
             len(all_records), len(captured_doc_links))
    return all_records


# ==============================================================================
#  SCORING
# ==============================================================================

def compute_flags(rec: dict, today: datetime) -> list[str]:
    flags: list[str] = list(DOC_TYPE_MAP.get(rec.get("cat", ""), ("", "", []))[2])
    try:
        filed_dt = datetime.strptime(rec.get("filed", ""), "%m/%d/%Y")
        if (today - filed_dt).days <= 7:
            flags.append("New this week")
    except ValueError:
        pass
    # Local-index-derived flag. Long-term-owner status is intentionally
    # NOT flagged in collin-intel — every property with an adverse filing
    # is in scope regardless of ownership tenure.
    yb = rec.get("year_built", "")
    try:
        if yb and int(yb) < 2000:
            flags.append("Pre-2000 build")
    except ValueError:
        pass
    if rec.get("not_actionable"):
        flags.append("Not actionable")
    seen: set[str] = set()
    return [f for f in flags if not (f in seen or seen.add(f))]

def compute_score(rec: dict, flags: list[str]) -> int:
    # Non-actionable records (gov filer with no real defendant, placeholder
    # grantee, subdivision name, etc.) get a hard cap so they sink to the
    # bottom of the dashboard.
    if rec.get("not_actionable"):
        return 5

    score = 30
    score += min(len(flags), 4) * 10
    if "Lis pendens" in flags and "Pre-foreclosure" in flags:
        score += 20
    # Thesis-fit bonus (independent of the 4-flag cap)
    if "Pre-2000 build" in flags:
        score += 5
    amount_raw = rec.get("_amount_raw")
    if amount_raw:
        try:
            amt = float(amount_raw)
            score += 15 if amt > 100_000 else (10 if amt > 50_000 else 0)
        except (ValueError, TypeError):
            pass
    if rec.get("prop_address"):
        score += 5
    return min(score, 100)


# ==============================================================================
#  ASSEMBLE + SAVE
# ==============================================================================

def assemble_records(raw_records: list[dict], today: datetime) -> list[dict]:
    # Pre-load the local index so the first lookup doesn't pay the build cost
    # mid-loop (and so any load failure is logged once, up front).
    if _LOCAL_INDEX:
        try:
            _load_local_index()
        except Exception as exc:
            log.warning("Could not preload parcel index: %s", exc)

    assembled: list[dict] = []
    seen: set = set()
    total = len(raw_records)

    for i, raw in enumerate(raw_records, 1):
        try:
            doc_num = safe_str(raw.get("doc_num", ""))
            owner   = safe_str(raw.get("owner", ""))
            grantee = safe_str(raw.get("grantee", ""))
            filed   = safe_str(raw.get("filed", ""))
            cat     = safe_str(raw.get("cat", ""))

            if doc_num:
                dedup_key = ("doc", doc_num)
            else:
                dedup_key = ("combo", owner.upper(), filed, cat)

            if dedup_key in seen:
                continue
            seen.add(dedup_key)

            amount_str = safe_str(raw.get("amount", ""))
            amount_raw = parse_amount(amount_str)

            # Decide which party is the homeowner before doing any I/O.
            homeowner_name = pick_homeowner_name(cat, owner, grantee)
            not_actionable = not homeowner_name

            if i % 100 == 0:
                log.info("  Parcel lookup %d/%d (cache: %d)",
                         i, total, len(_parcel_cache))

            parcel = {} if not_actionable else lookup_parcel(homeowner_name)

            rec: dict = {
                "doc_num":         doc_num,
                "doc_type":        safe_str(raw.get("doc_type", "")),
                "filed":           filed,
                "cat":             cat,
                "cat_label":       safe_str(raw.get("cat_label", "")),
                "owner":           owner,
                "grantee":         grantee,
                "homeowner_name":  homeowner_name,
                "not_actionable":  not_actionable,
                "amount":          amount_str,
                "_amount_raw":     amount_raw,
                "legal":           safe_str(raw.get("legal", "")),
                "prop_address":    parcel.get("prop_address", ""),
                "prop_city":       parcel.get("prop_city", ""),
                "prop_state":      parcel.get("prop_state", "TX"),
                "prop_zip":        parcel.get("prop_zip", ""),
                "mail_address":    parcel.get("mail_address", ""),
                "mail_city":       parcel.get("mail_city", ""),
                "mail_state":      parcel.get("mail_state", "TX"),
                "mail_zip":        parcel.get("mail_zip", ""),
                # Investment-screening signals from the local CAD index
                "year_built":      parcel.get("year_built", ""),
                "sqft":            parcel.get("sqft", ""),
                "market_value":    parcel.get("market_value", ""),
                "deed_year":       parcel.get("deed_year", ""),
                "long_term_owner": parcel.get("long_term_owner", False),
                "clerk_url":       safe_str(raw.get("clerk_url", "")),
            }
            flags = compute_flags(rec, today)
            rec["flags"] = flags
            rec["score"] = compute_score(rec, flags)
            del rec["_amount_raw"]
            assembled.append(rec)
        except Exception as exc:
            log.warning("Skipping bad record: %s", exc)

    assembled.sort(key=lambda r: r["score"], reverse=True)
    with_addr  = sum(1 for r in assembled if r.get("prop_address"))
    actionable = sum(1 for r in assembled if not r.get("not_actionable"))
    long_term  = sum(1 for r in assembled if r.get("long_term_owner"))
    log.info("Assembled %d records (%d actionable, %d with address, %d long-term owners)",
             len(assembled), actionable, with_addr, long_term)
    return assembled


def save_output(records: list[dict], date_from: str, date_to: str) -> None:
    payload = {
        "fetched_at":   datetime.now(timezone.utc).isoformat(),
        "source":       "Collin County Clerk / Collin CAD",
        "date_range":   {"from": date_from, "to": date_to},
        "total":        len(records),
        "actionable":   sum(1 for r in records if not r.get("not_actionable")),
        "with_address": sum(1 for r in records if r.get("prop_address")),
        "long_term":    sum(1 for r in records if r.get("long_term_owner")),
        "records":      records,
    }
    for path in [DASHBOARD_DIR / "records.json", DATA_DIR / "records.json"]:
        path.write_text(json.dumps(payload, indent=2, default=str))
        log.info("Saved -> %s", path)


def export_ghl_csv(records: list[dict]) -> None:
    out_path = DATA_DIR / "ghl_export.csv"
    cols = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Year Built", "SqFt", "Market Value", "Deed Year", "Long-term Owner",
        "Lead Type", "Document Type", "Date Filed", "Document Number",
        "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]
    def split_name(full: str) -> tuple[str, str]:
        parts = full.strip().split()
        if not parts:
            return "", ""
        if len(parts) == 1:
            return parts[0], ""
        return " ".join(parts[:-1]), parts[-1]
    with out_path.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=cols)
        writer.writeheader()
        for r in records:
            # Skip records flagged as not actionable — keeps GHL clean.
            if r.get("not_actionable"):
                continue
            # Use the resolved homeowner_name (falls back to owner if empty).
            name_for_split = r.get("homeowner_name") or r.get("owner", "")
            first, last = split_name(name_for_split)
            writer.writerow({
                "First Name":             first,
                "Last Name":              last,
                "Mailing Address":        r.get("mail_address", ""),
                "Mailing City":           r.get("mail_city", ""),
                "Mailing State":          r.get("mail_state", "TX"),
                "Mailing Zip":            r.get("mail_zip", ""),
                "Property Address":       r.get("prop_address", ""),
                "Property City":          r.get("prop_city", ""),
                "Property State":         r.get("prop_state", "TX"),
                "Property Zip":           r.get("prop_zip", ""),
                "Year Built":             r.get("year_built", ""),
                "SqFt":                   r.get("sqft", ""),
                "Market Value":           r.get("market_value", ""),
                "Deed Year":              r.get("deed_year", ""),
                "Long-term Owner":        "YES" if r.get("long_term_owner") else "",
                "Lead Type":              r.get("cat", ""),
                "Document Type":          r.get("cat_label", ""),
                "Date Filed":             r.get("filed", ""),
                "Document Number":        r.get("doc_num", ""),
                "Amount/Debt Owed":       r.get("amount", ""),
                "Seller Score":           r.get("score", 0),
                "Motivated Seller Flags": "; ".join(r.get("flags", [])),
                "Source":                 "Collin County Clerk",
                "Public Records URL":     r.get("clerk_url", ""),
            })
    log.info("GHL CSV -> %s", out_path)


# ==============================================================================
#  ENTRY POINT
# ==============================================================================

async def main() -> None:
    today     = datetime.now()
    start     = today - timedelta(days=LOOKBACK_DAYS)
    fmt       = "%-m/%-d/%Y" if sys.platform != "win32" else "%#m/%#d/%Y"
    date_from = start.strftime(fmt)
    date_to   = today.strftime(fmt)

    log.info("=" * 60)
    log.info("Collin County Motivated Seller Scraper")
    log.info("Range: %s -> %s", date_from, date_to)
    log.info("=" * 60)

    raw_records = await run_clerk_scrape(start, today)
    log.info("Raw records from clerk: %d", len(raw_records))

    records = assemble_records(raw_records, today)
    save_output(records, date_from, date_to)
    export_ghl_csv(records)

    log.info("Complete. %d records, %d with address.",
             len(records), sum(1 for r in records if r.get("prop_address")))


if __name__ == "__main__":
    asyncio.run(main())
