#!/usr/bin/env python3
"""
Collin County, Texas — Motivated Seller Lead Scraper
Clerk portal : https://collin.tx.publicsearch.us/
Parcel data  : Texas Open Data Socrata ahis-pci3
Runs daily — pulls records filed in the last 7 days.
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

CLERK_BASE     = "https://collin.tx.publicsearch.us"
LOOKBACK_DAYS  = 7   # pull records filed within this many days
RETRY_ATTEMPTS = 3
RETRY_DELAY    = 5
DEBUG          = True

SOCRATA_OWNER = "https://data.texas.gov/resource/ahis-pci3.json"
SOCRATA_APPR  = "https://data.texas.gov/resource/nne4-8riu.json"

ARCGIS_URL = (
    "https://gismaps.cityofallen.org/arcgis/rest/services/"
    "ReferenceData/Collin_County_Appraisal_District_Parcels/MapServer/1/query"
)

# Max concurrent parcel API requests — keeps us from hammering Socrata/ArcGIS
PARCEL_CONCURRENCY = 20

DOC_TYPE_MAP: dict[str, tuple[str, str, list[str]]] = {
    "LP":       ("LP",       "Lis Pendens",             ["Lis pendens", "Pre-foreclosure"]),
    "RELLP":    ("RELLP",    "Release Lis Pendens",     ["Lis pendens"]),
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
    "NOC":      ("NOC",      "Notice of Commencement",  []),
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
    if "LIS PENDENS" in t and "RELEASE" not in t:
        return "LP", "Lis Pendens"
    if "RELEASE" in t and "LIS PENDENS" in t:
        return "RELLP", "Release Lis Pendens"
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


# ==============================================================================
#  PARCEL LOOKUP  (batched Socrata + async concurrent ArcGIS fallback)
# ==============================================================================

_parcel_cache: dict[str, dict] = {}

# Shared session for all parcel HTTP calls (connection pooling)
_session = requests.Session()
_session.headers.update({"Accept": "application/json"})

# How many owner names to pack into a single Socrata IN() query
SOCRATA_BATCH_SIZE = 50


def _row_to_parcel(r: dict) -> dict:
    """Convert a raw Socrata row into a normalised parcel dict."""
    situs      = safe_str(r.get("situsconcat", ""))
    mail_addr  = safe_str(r.get("owneraddrline1", ""))
    mail_city  = safe_str(r.get("owneraddrcity", ""))
    mail_state = safe_str(r.get("owneraddrstate", "")) or "TX"
    mail_zip   = safe_str(r.get("owneraddrzip", ""))
    if "-" in mail_zip:
        mail_zip = mail_zip.split("-")[0]
    prop_addr, prop_city, prop_state, prop_zip = _parse_situsconcat(situs)
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


def _socrata_batch(owner_keys: list[str], endpoint: str) -> dict[str, dict]:
    """
    Fetch up to SOCRATA_BATCH_SIZE owners in one IN() query.
    Returns {upper_owner_name: parcel_dict} for every hit.
    """
    if not owner_keys:
        return {}
    quoted = ", ".join(f"'{n.replace(chr(39), chr(39)*2)}'" for n in owner_keys)
    where  = f"ownername IN ({quoted})"
    try:
        resp = _session.get(
            endpoint,
            params={"$where": where, "$limit": len(owner_keys) * 3},
            timeout=15,
        )
        if resp.status_code != 200:
            return {}
        rows = resp.json()
        if not isinstance(rows, list):
            return {}
        result: dict[str, dict] = {}
        for r in rows:
            key = safe_str(r.get("ownername", "")).upper()
            if key and key not in result:
                parcel = _row_to_parcel(r)
                if parcel["prop_address"] or parcel["mail_address"]:
                    result[key] = parcel
        return result
    except Exception as exc:
        log.debug("Socrata batch error: %s", exc)
        return {}


def socrata_batch_lookup(owners: list[str]) -> dict[str, dict]:
    """
    Look up a list of unique owner name strings against both Socrata
    endpoints using batched IN() queries.  Returns {upper_name: parcel}.
    """
    # Build the full set of (key → canonical_name) pairs we need to look up,
    # skipping anything already cached.
    needed: dict[str, str] = {}  # upper_variant -> original owner key
    for owner in owners:
        cache_key = owner.strip().upper()
        if cache_key in _parcel_cache:
            continue
        for variant in name_variants(owner):
            vkey = variant.strip().upper()
            if vkey not in needed:
                needed[vkey] = cache_key

    if not needed:
        return {}

    variant_list = list(needed.keys())
    found: dict[str, dict] = {}  # upper_variant -> parcel

    for endpoint in [SOCRATA_OWNER, SOCRATA_APPR]:
        # Only query variants we haven't resolved yet
        remaining = [v for v in variant_list if needed[v] not in found.values()
                     and v not in found]
        if not remaining:
            break
        # Chunk into batches
        for i in range(0, len(remaining), SOCRATA_BATCH_SIZE):
            chunk = remaining[i : i + SOCRATA_BATCH_SIZE]
            hits  = _socrata_batch(chunk, endpoint)
            found.update(hits)

    # Populate the cache: map each original owner key to its result
    results: dict[str, dict] = {}
    for variant, cache_key in needed.items():
        if cache_key in _parcel_cache:
            continue
        if variant in found:
            _parcel_cache[cache_key] = found[variant]
            results[cache_key] = found[variant]
        else:
            # Will be filled in by ArcGIS / fuzzy fallback later
            pass

    return results


def _arcgis_lookup(owner_variant: str) -> dict:
    safe_name = owner_variant.replace("'", "''")
    try:
        resp = _session.get(
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

def _socrata_fuzzy(owner_variant: str) -> dict:
    """Single-owner fuzzy LIKE fallback — only used when batch + ArcGIS both miss."""
    parts = owner_variant.strip().split()
    if not parts:
        return {}
    search_word = next((p for p in parts if len(p) > 2), parts[0])
    safe_word = search_word.replace("'", "''")
    for endpoint in [SOCRATA_OWNER, SOCRATA_APPR]:
        try:
            resp = _session.get(
                endpoint,
                params={"$where": f"ownername LIKE '%{safe_word}%'", "$limit": 5},
                timeout=10,
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
                    parcel = _row_to_parcel(r)
                    if parcel["prop_address"] or parcel["mail_address"]:
                        return parcel
        except Exception as exc:
            log.debug("Socrata fuzzy error %r: %s", owner_variant[:40], exc)
    return {}

def _lookup_parcel_sync(owner: str) -> dict:
    """
    Per-record fallback for owners that the batch pass missed.
    Tries ArcGIS then fuzzy Socrata.
    """
    if not owner:
        return {}
    cache_key = owner.strip().upper()
    if cache_key in _parcel_cache:
        return _parcel_cache[cache_key]
    # ArcGIS fallback
    for variant in name_variants(owner):
        result = _arcgis_lookup(variant)
        if result.get("prop_address") or result.get("mail_address"):
            _parcel_cache[cache_key] = result
            return result
    # Fuzzy Socrata last resort
    if len(owner.split()) <= 3:
        result = _socrata_fuzzy(owner.strip().upper())
        _parcel_cache[cache_key] = result
        return result
    _parcel_cache[cache_key] = {}
    return {}

async def lookup_parcel_async(owner: str, sem: asyncio.Semaphore) -> dict:
    """
    Used for the per-record ArcGIS/fuzzy fallback pass only.
    The bulk of lookups are resolved by socrata_batch_lookup() before this runs.
    """
    cache_key = owner.strip().upper()
    if cache_key in _parcel_cache:
        return _parcel_cache[cache_key]
    async with sem:
        loop = asyncio.get_event_loop()
        return await loop.run_in_executor(None, _lookup_parcel_sync, owner)


# ==============================================================================
#  CLERK PORTAL
# ==============================================================================

def build_search_url(term: str) -> str:
    return (
        f"{CLERK_BASE}/results"
        f"?searchType=quickSearch&department=RP&searchOcrText=false"
        f"&searchTerm={term}"
    )

def _parse_table(html: str, cutoff: datetime) -> tuple[list[dict], bool]:
    """
    Parse the results table keeping only records filed on or after cutoff.
    Returns (records, all_old) where all_old=True means every record on
    this page is older than the cutoff — signal to stop paginating.
    The site returns results newest-first, so hitting all_old means we're done.
    """
    soup = BeautifulSoup(html, "lxml")
    records = []
    all_old = True

    table = soup.find("table")
    if not table:
        return records, False

    headers = [th.get_text(" ", strip=True).lower()
               for th in table.find_all("th")]

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

        if not raw_date:
            continue

        rec_date = None
        for fmt in ("%m/%d/%Y", "%-m/%-d/%Y", "%m/%d/%Y", "%#m/%#d/%Y"):
            try:
                rec_date = datetime.strptime(raw_date, fmt)
                break
            except ValueError:
                continue
        if rec_date is None:
            # Try splitting manually to handle any combo of padding
            try:
                parts = raw_date.split("/")
                rec_date = datetime(int(parts[2]), int(parts[0]), int(parts[1]))
            except Exception:
                continue

        if rec_date < cutoff:
            # Older than our lookback window — skip but keep all_old=True
            # so we stop paginating once we've seen 3 consecutive old pages.
            continue

        all_old = False  # at least one record is within the window

        if not owner or owner == "N/A":
            continue

        link = tr.find("a", href=True)
        clerk_url = _abs_url(link["href"]) if link else ""
        cat, cat_label = _map_doc_type(doc_type)

        records.append({
            "doc_num":   doc_num,
            "doc_type":  doc_type,
            "filed":     raw_date,
            "cat":       cat,
            "cat_label": cat_label,
            "owner":     owner,
            "grantee":   grantee,
            "legal":     legal,
            "amount":    "",
            "clerk_url": clerk_url,
        })

    return records, all_old

async def _click_next(page: Page) -> bool:
    try:
        btn = page.locator("button[aria-label='next page']").first
        if await btn.count() > 0:
            disabled = await btn.get_attribute("disabled")
            if disabled is None:
                await btn.click()
                try:
                    await page.wait_for_load_state("networkidle", timeout=10_000)
                except Exception:
                    await asyncio.sleep(3)
                return True
    except Exception:
        pass
    return False

async def _apply_year_filter(page: Page, year: int) -> None:
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
            try:
                await page.wait_for_selector(
                    "table, [class*='no-results'], [class*='empty'], [class*='zero']",
                    timeout=20_000,
                )
            except Exception:
                log.warning("  Timed out waiting for results after year filter; sleeping 8s")
                await asyncio.sleep(8)
        else:
            log.warning("  Year %d checkbox not found", year)
    except Exception as exc:
        log.warning("  Year filter error: %s", exc)

async def run_clerk_scrape(cutoff: datetime) -> list[dict]:
    all_records: list[dict] = []
    search_terms = ["RELLP", "JUD", "CCJ", "LNHOA", "NOC", "PRO",
                    "LN", "LNMECH", "LNIRS", "LNFED",
                    "LP", "NOFC", "TAXDEED"]

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
        loaded_term = None
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
                    loaded_term = term
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
            await _apply_year_filter(page, cutoff.year)
            await screenshot(page, "after_filter")
            await save_html(page, "after_filter")

            page_num = 1
            consecutive_old = 0
            max_pages = 2000

            while page_num <= max_pages:
                try:
                    await page.wait_for_selector("table", timeout=15_000)
                except Exception:
                    log.warning("Page %d: table selector timed out", page_num)

                html = await page.content()
                recs, all_old = _parse_table(html, cutoff)
                log.info("Page %d: %d records (all_old=%s) | total so far: %d",
                         page_num, len(recs), all_old, len(all_records))
                all_records.extend(recs)

                # Site sorts oldest-first within the year filter, so we cannot
                # stop early based on date — just paginate all pages and let
                # _parse_table filter to the cutoff window.
                _ = all_old  # not used for early exit

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

    log.info("Raw records collected: %d", len(all_records))
    return all_records


# ==============================================================================
#  SCORING
# ==============================================================================

def compute_flags(rec: dict, today: datetime) -> list[str]:
    flags: list[str] = list(DOC_TYPE_MAP.get(rec.get("cat", ""), ("", "", []))[2])
    owner_up = rec.get("owner", "").upper()
    if any(kw in owner_up for kw in
           ["LLC", "INC", "CORP", "LTD", "L.L.C",
            "TRUST", "HOLDINGS", "PROPERTIES"]):
        flags.append("LLC / corp owner")
    try:
        filed_dt = datetime.strptime(rec.get("filed", ""), "%m/%d/%Y")
        if (today - filed_dt).days <= 7:
            flags.append("New this week")
    except ValueError:
        pass
    seen: set[str] = set()
    return [f for f in flags if not (f in seen or seen.add(f))]

def compute_score(rec: dict, flags: list[str]) -> int:
    score = 30
    score += min(len(flags), 4) * 10
    if "Lis pendens" in flags and "Pre-foreclosure" in flags:
        score += 20
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
#  ASSEMBLE + SAVE  (parcel lookups now run concurrently)
# ==============================================================================

async def assemble_records_async(raw_records: list[dict], today: datetime) -> list[dict]:
    """
    Deduplicate, then:
      1. Batch-query Socrata with IN() — one request per 50 names instead of
         one request per name.  Resolves the majority of owners in seconds.
      2. Concurrently fall back to ArcGIS + fuzzy Socrata for the misses.
    """
    # --- deduplicate first ---
    deduped: list[dict] = []
    seen: set = set()
    for raw in raw_records:
        doc_num = safe_str(raw.get("doc_num", ""))
        owner   = safe_str(raw.get("owner", ""))
        filed   = safe_str(raw.get("filed", ""))
        cat     = safe_str(raw.get("cat", ""))
        dedup_key = ("doc", doc_num) if doc_num else ("combo", owner.upper(), filed, cat)
        if dedup_key in seen:
            continue
        seen.add(dedup_key)
        deduped.append(raw)

    total = len(deduped)
    log.info("Unique records after dedup: %d (from %d raw)", total, len(raw_records))

    # --- PASS 1: batched Socrata IN() queries (runs in a thread, non-blocking) ---
    unique_owners = list({safe_str(r.get("owner", "")) for r in deduped if r.get("owner")})
    log.info("Pass 1: batched Socrata lookup for %d unique owners "
             "(%d batches of %d)...",
             len(unique_owners),
             -(-len(unique_owners) // SOCRATA_BATCH_SIZE),  # ceil division
             SOCRATA_BATCH_SIZE)

    loop = asyncio.get_event_loop()
    await loop.run_in_executor(None, socrata_batch_lookup, unique_owners)

    batch_hits = sum(1 for o in unique_owners if _parcel_cache.get(o.strip().upper()))
    log.info("Pass 1 done: %d / %d owners resolved via Socrata batch", batch_hits, len(unique_owners))

    # --- PASS 2: concurrent ArcGIS + fuzzy fallback for remaining misses ---
    misses = [o for o in unique_owners if not _parcel_cache.get(o.strip().upper())]
    log.info("Pass 2: concurrent ArcGIS/fuzzy fallback for %d misses "
             "(concurrency=%d)...", len(misses), PARCEL_CONCURRENCY)

    sem = asyncio.Semaphore(PARCEL_CONCURRENCY)
    fallback_done = 0

    async def _fallback(owner: str) -> None:
        nonlocal fallback_done
        await lookup_parcel_async(owner, sem)
        fallback_done += 1
        if fallback_done % 100 == 0:
            log.info("  Fallback %d/%d", fallback_done, len(misses))

    await asyncio.gather(*[_fallback(o) for o in misses])

    final_hits = sum(1 for o in unique_owners
                     if _parcel_cache.get(o.strip().upper(), {}).get("prop_address")
                     or _parcel_cache.get(o.strip().upper(), {}).get("mail_address"))
    log.info("Pass 2 done: %d total owners with address data", final_hits)

    # --- pull results from cache for every record ---
    completed = 0

    async def _get_parcel(raw: dict) -> dict:
        nonlocal completed
        owner = safe_str(raw.get("owner", ""))
        cache_key = owner.strip().upper()
        parcel = _parcel_cache.get(cache_key, {})
        completed += 1
        return parcel

    parcels = await asyncio.gather(*[_get_parcel(raw) for raw in deduped])

    # --- assemble final records ---
    assembled: list[dict] = []
    for raw, parcel in zip(deduped, parcels):
        try:
            amount_str = safe_str(raw.get("amount", ""))
            amount_raw = parse_amount(amount_str)

            rec: dict = {
                "doc_num":      safe_str(raw.get("doc_num", "")),
                "doc_type":     safe_str(raw.get("doc_type", "")),
                "filed":        safe_str(raw.get("filed", "")),
                "cat":          safe_str(raw.get("cat", "")),
                "cat_label":    safe_str(raw.get("cat_label", "")),
                "owner":        safe_str(raw.get("owner", "")),
                "grantee":      safe_str(raw.get("grantee", "")),
                "amount":       amount_str,
                "_amount_raw":  amount_raw,
                "legal":        safe_str(raw.get("legal", "")),
                "prop_address": parcel.get("prop_address", ""),
                "prop_city":    parcel.get("prop_city", ""),
                "prop_state":   parcel.get("prop_state", "TX"),
                "prop_zip":     parcel.get("prop_zip", ""),
                "mail_address": parcel.get("mail_address", ""),
                "mail_city":    parcel.get("mail_city", ""),
                "mail_state":   parcel.get("mail_state", "TX"),
                "mail_zip":     parcel.get("mail_zip", ""),
                "clerk_url":    safe_str(raw.get("clerk_url", "")),
            }
            flags = compute_flags(rec, today)
            rec["flags"] = flags
            rec["score"] = compute_score(rec, flags)
            del rec["_amount_raw"]
            assembled.append(rec)
        except Exception as exc:
            log.warning("Skipping bad record: %s", exc)

    assembled.sort(key=lambda r: r["score"], reverse=True)
    with_addr = sum(1 for r in assembled if r.get("prop_address"))
    log.info("Assembled %d records, %d with address", len(assembled), with_addr)
    return assembled


def save_output(records: list[dict], cutoff: datetime) -> None:
    payload = {
        "fetched_at":   datetime.now(timezone.utc).isoformat(),
        "source":       "Collin County Clerk / Collin CAD",
        "date_range":   {"from": cutoff.strftime("%-m/%-d/%Y"), "to": "present"},
        "total":        len(records),
        "with_address": sum(1 for r in records if r.get("prop_address")),
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
            first, last = split_name(r.get("owner", ""))
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
    today = datetime.now()
    cutoff = today - timedelta(days=LOOKBACK_DAYS)

    log.info("=" * 60)
    log.info("Collin County Motivated Seller Scraper")
    log.info("Pulling records filed on or after: %s", cutoff.strftime("%m/%d/%Y"))
    log.info("=" * 60)

    raw_records = await run_clerk_scrape(cutoff)
    log.info("Raw records from clerk: %d", len(raw_records))

    # Pass 1: batched Socrata IN() queries; Pass 2: concurrent ArcGIS fallback
    records = await assemble_records_async(raw_records, today)
    save_output(records, cutoff)
    export_ghl_csv(records)

    log.info("Complete. %d records, %d with address.",
             len(records), sum(1 for r in records if r.get("prop_address")))


if __name__ == "__main__":
    asyncio.run(main())
