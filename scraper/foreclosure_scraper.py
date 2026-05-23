#!/usr/bin/env python3
"""
Collin County Foreclosure Notices Scraper
Source: https://apps2.collincountytx.gov/ForeclosureNotices

This portal is a separate data source from the clerk's Real Property records.
It contains actual Notice of Trustee Sale filings (real pre-foreclosure leads)
that don't appear in the Real Property doc-type whitelist.

Each list row has: address, city/state/zip, sale date, file date, property type.
Detail pages (/DetailPage/{id}) contain owner name + appraised value + PDF
of the actual notice, but require an extra page load per record.

Returned records use the same schema as clerk records so they merge cleanly
into the dashboard and GHL export.
"""

from __future__ import annotations

import logging
import re
import sys
from datetime import datetime
from typing import Any

from playwright.async_api import (
    BrowserContext,
    Page,
    TimeoutError as PWTimeout,
    async_playwright,
)

log = logging.getLogger("foreclosure_scraper")

FORECLOSURE_URL    = "https://apps2.collincountytx.gov/ForeclosureNotices"
DETAIL_URL_FMT     = "https://apps2.collincountytx.gov/ForeclosureNotices/DetailPage/{id}"
DEFAULT_PROP_TYPE  = "Residential Single Family (A1)"
INIT_WAIT_MS       = 3500
ACTION_WAIT_MS     = 1500
PAGE_NAV_WAIT_MS   = 2000
MAX_PAGES          = 25  # safety bound; portal currently has ~18 pages

# Collin County municipalities + postal cities. Used to split the embedded
# address line ("111 WHEATGRASS LN PRINCETON, TX 75407") into street + city,
# since the portal concatenates them with no delimiter. Longest names first
# at match time so multi-word cities (ROYSE CITY, BLUE RIDGE) win over any
# single-word suffix.
COLLIN_CITIES = {
    "ALLEN", "ANNA", "BLUE RIDGE", "CELINA", "DALLAS", "FAIRVIEW",
    "FARMERSVILLE", "FRISCO", "GARLAND", "JOSEPHINE", "LAVON",
    "LOWRY CROSSING", "LUCAS", "MCKINNEY", "MELISSA", "MURPHY",
    "NEVADA", "NEW HOPE", "PARKER", "PLANO", "PRINCETON", "PROSPER",
    "RICHARDSON", "ROYSE CITY", "SACHSE", "SAINT PAUL", "ST PAUL",
    "VAN ALSTYNE", "WESTON", "WESTMINSTER", "WYLIE", "CARROLLTON",
    "THE COLONY", "LITTLE ELM", "COPEVILLE", "WESTON",
}


def _split_street_city(s: str) -> tuple[str, str]:
    """Split 'STREET CITY' into (street, city) using the Collin city list.

    '111 WHEATGRASS LN PRINCETON' -> ('111 WHEATGRASS LN', 'PRINCETON')
    '2829 EPPING WAY CELINA'      -> ('2829 EPPING WAY',    'CELINA')
    """
    s = s.strip()
    upper = s.upper()
    # Try known cities, longest first so 'ROYSE CITY' beats a stray 'CITY'
    for city in sorted(COLLIN_CITIES, key=len, reverse=True):
        if upper.endswith(" " + city):
            street = s[: len(s) - len(city)].strip()
            return street, city
    # Fallback: assume the final whitespace-delimited token is the city
    parts = s.rsplit(" ", 1)
    if len(parts) == 2:
        return parts[0].strip(), parts[1].strip()
    return s, ""


def _parse_row_text(text: str) -> dict[str, str]:
    """Parse one foreclosure row. Works whether fields are newline-separated
    OR concatenated into a single line (Playwright's table-row text extraction
    drops the line breaks, producing e.g.:

        111 WHEATGRASS LN PRINCETON, TX 75407City: Unincorporated Area\
Sale Date: 07/07/2026File Date: 05/21/2026Property Type:Residential Single Family (A1)

    so we anchor on the field labels rather than on line structure.)
    """
    rec: dict[str, str] = {}
    t = re.sub(r"\s+", " ", text).strip()

    # Labels that bound one field from the next, used as stop-points.
    NEXT = r"(?:\s*(?:City|Sale\s*Date|File\s*Date|Property\s*Type|Status)\s*:|$)"

    m = re.search(rf"Property\s*Type\s*:\s*(.+?){NEXT}", t, re.I)
    if m:
        rec["property_type"] = m.group(1).strip()

    m = re.search(r"Sale\s*Date\s*:\s*(\d{1,2}/\d{1,2}/\d{4})", t, re.I)
    if m:
        rec["sale_date"] = m.group(1)

    m = re.search(r"File\s*Date\s*:\s*(\d{1,2}/\d{1,2}/\d{4})", t, re.I)
    if m:
        rec["file_date"] = m.group(1)

    m = re.search(rf"City\s*:\s*(.+?){NEXT}", t, re.I)
    if m:
        rec["jurisdiction"] = m.group(1).strip()

    # Address = the head of the row, before the first field label, ending in
    # ", TX <zip>". Split off everything from the first label onward.
    head = re.split(r"\s*(?:City|Sale\s*Date|File\s*Date|Property\s*Type)\s*:", t, maxsplit=1)[0].strip()
    am = re.search(r"(.+?),\s*TX\s+(\d{5})", head)
    if am:
        street_city = am.group(1).strip()
        rec["prop_zip"]   = am.group(2)
        rec["prop_state"] = "TX"
        street, city = _split_street_city(street_city)
        rec["prop_address"] = street.upper()
        rec["prop_city"]    = city.upper()

    return rec


async def _set_max_page_size(page: Page) -> None:
    """Try to bump page size to reduce pagination work. Best-effort."""
    for attempt_label in ("200", "100", "50"):
        try:
            sel = page.locator("select").last
            if await sel.count():
                await sel.select_option(label=attempt_label, timeout=3000)
                await page.wait_for_timeout(ACTION_WAIT_MS)
                log.info("  page size set to %s", attempt_label)
                return
        except Exception:
            continue
    log.info("  page size adjust skipped (control not found)")


async def _set_filed_date_filter(page: Page, date_from: datetime, date_to: datetime) -> bool:
    """Fill the 'Filed Date Start' / 'Filed Date End' inputs to narrow results
    to the target window at the source. Best-effort: returns True if both
    fields were filled. The Python-side date filter is the safety net either
    way, so a False here is non-fatal.
    """
    start_str = date_from.strftime("%-m/%-d/%Y") if sys.platform != "win32" else date_from.strftime("%#m/%#d/%Y")
    end_str   = date_to.strftime("%-m/%-d/%Y")   if sys.platform != "win32" else date_to.strftime("%#m/%#d/%Y")

    filled = 0
    for label, value in (("Filed Date Start", start_str), ("Filed Date End", end_str)):
        candidates = [
            page.get_by_label(label, exact=False),
            page.get_by_placeholder(label),
            page.locator(f'input[aria-label*="{label}"]'),
            page.locator(f'xpath=//label[contains(text(), "{label}")]/following::input[1]'),
        ]
        for cand in candidates:
            try:
                if await cand.count() == 0:
                    continue
                inp = cand.first
                await inp.click(timeout=2000)
                await inp.fill("")
                await inp.type(value, delay=40)
                await page.keyboard.press("Tab")
                await page.wait_for_timeout(ACTION_WAIT_MS)
                filled += 1
                log.info("  set %s = %s", label, value)
                break
            except Exception:
                continue

    if filled == 2:
        await page.wait_for_timeout(PAGE_NAV_WAIT_MS)  # let results refresh
        return True
    log.info("  filed-date filter not fully set (%d/2) — will filter in Python", filled)
    return False


async def _click_next_page(page: Page) -> bool:
    """Click the 'next page' button. Return True if click succeeded."""
    candidates = [
        page.get_by_role("button", name=re.compile(r"next", re.I)),
        page.get_by_role("link",   name=re.compile(r"next", re.I)),
        page.locator('button:has-text("Next")'),
        page.locator('a:has-text("Next")'),
        page.locator('button:has-text(">")').last,
        page.locator('a:has-text(">")').last,
    ]
    for cand in candidates:
        try:
            if await cand.count() == 0:
                continue
            first = cand.first
            if not await first.is_enabled(timeout=500):
                continue
            await first.click(timeout=3000)
            await page.wait_for_timeout(PAGE_NAV_WAIT_MS)
            return True
        except Exception:
            continue
    return False


async def _extract_rows_on_page(page: Page) -> list[dict[str, str]]:
    """Pull all visible foreclosure rows from the current page."""
    blocks: list[str] = []

    # Strategy 1: anchor on the address link in each card. Each result has a
    # clickable address that links to /DetailPage/{id}; the surrounding card
    # holds the City/Sale Date/File Date/Property Type fields. We walk up to
    # the card container and grab its full text.
    try:
        links = page.locator('a[href*="DetailPage"], a[href*="Detail"]')
        n = await links.count()
        if n:
            for i in range(n):
                try:
                    card = links.nth(i).locator(
                        'xpath=ancestor::*[self::div or self::li or self::tr][1]'
                    )
                    txt = await card.first.inner_text(timeout=1500)
                    if "Sale Date" in txt and "File Date" in txt:
                        blocks.append(txt)
                except Exception:
                    continue
            if blocks:
                log.info("  matched %d cards via address-link anchor", len(blocks))
    except Exception:
        pass

    # Strategy 2: common container selectors
    if not blocks:
        candidate_selectors = [
            "table tbody tr", ".property-card", ".listing-row",
            ".result-row", "[class*='property']", "[class*='result']",
            "[class*='card']", "li",
        ]
        for sel in candidate_selectors:
            try:
                loc = page.locator(sel)
                if await loc.count() == 0:
                    continue
                texts = await loc.all_text_contents()
                for t in texts:
                    if "Sale Date" in t and "File Date" in t:
                        blocks.append(t)
                if blocks:
                    log.info("  matched %d rows via selector: %s", len(blocks), sel)
                    break
            except Exception:
                continue

    # Strategy 3: split whole body on the address pattern
    if not blocks:
        body_text = await page.locator("body").inner_text()
        chunks = re.split(r"(?=\d+\s+[A-Z].+?,\s*TX\s+\d{5})", body_text)
        for c in chunks:
            if "Sale Date" in c and "File Date" in c:
                blocks.append(c)
        if blocks:
            log.info("  matched %d rows via body-text fallback", len(blocks))

    return [_parse_row_text(b) for b in blocks if b]


async def run_foreclosure_scrape(
    date_from: datetime,
    date_to:   datetime,
    property_type_filter: str = DEFAULT_PROP_TYPE,
) -> list[dict[str, Any]]:
    """Top-level entry point. Manages its own Playwright browser lifecycle so
    it can be called from main() the same way run_clerk_scrape is called."""
    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=True,
            args=[
                "--no-sandbox",
                "--disable-dev-shm-usage",
                "--disable-blink-features=AutomationControlled",
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
        )
        try:
            return await _scrape_with_context(
                context, date_from, date_to, property_type_filter
            )
        finally:
            await context.close()
            await browser.close()


async def _scrape_with_context(
    context: BrowserContext,
    date_from: datetime,
    date_to:   datetime,
    property_type_filter: str = DEFAULT_PROP_TYPE,
) -> list[dict[str, Any]]:
    """Scrape Collin County Foreclosure Notices, return records for the window."""
    log.info(
        "Foreclosure scrape window: %s to %s | property type: %s",
        date_from.strftime("%m/%d/%Y"),
        date_to.strftime("%m/%d/%Y"),
        property_type_filter,
    )

    page = await context.new_page()
    raw_rows: list[dict[str, str]] = []
    seen_addresses: set[str] = set()

    try:
        try:
            await page.goto(FORECLOSURE_URL, wait_until="networkidle", timeout=30_000)
        except PWTimeout:
            log.warning("Network-idle timeout, continuing anyway")
        await page.wait_for_timeout(INIT_WAIT_MS)

        # Narrow to our date window at the source if possible (drops ~460
        # records to ~20). Python-side filter still runs as a safety net.
        await _set_filed_date_filter(page, date_from, date_to)
        await _set_max_page_size(page)

        # Paginate. We don't rely on the UI Filed Date filter because we
        # filter in Python after extraction — simpler and less fragile.
        for page_num in range(1, MAX_PAGES + 1):
            log.info("Foreclosure page %d", page_num)
            rows = await _extract_rows_on_page(page)
            new_rows_on_page = 0
            for r in rows:
                key = (r.get("prop_address", ""), r.get("file_date", ""))
                if key in seen_addresses:
                    continue
                seen_addresses.add(key)
                raw_rows.append(r)
                new_rows_on_page += 1
            log.info("  page %d: %d new rows (%d total)", page_num, new_rows_on_page, len(raw_rows))
            if new_rows_on_page == 0:
                log.info("No new rows on page %d, stopping pagination", page_num)
                break
            advanced = await _click_next_page(page)
            if not advanced:
                log.info("No further pages")
                break

        log.info("Foreclosure scrape: extracted %d unique raw rows", len(raw_rows))
    finally:
        await page.close()

    return _build_records(raw_rows, date_from, date_to, property_type_filter)


def _build_records(
    raw_rows: list[dict[str, str]],
    date_from: datetime,
    date_to:   datetime,
    property_type_filter: str,
) -> list[dict[str, Any]]:
    """Filter raw rows by date + property type, build clerk-schema records."""
    out: list[dict[str, Any]] = []
    skipped_type   = 0
    skipped_date   = 0
    skipped_parse  = 0
    d_from = date_from.date()
    d_to   = date_to.date()

    for r in raw_rows:
        pt = r.get("property_type", "")
        if property_type_filter and pt != property_type_filter:
            skipped_type += 1
            continue
        fd_raw = r.get("file_date", "")
        try:
            fd = datetime.strptime(fd_raw, "%m/%d/%Y").date()
        except (ValueError, TypeError):
            skipped_parse += 1
            continue
        if fd < d_from or fd > d_to:
            skipped_date += 1
            continue

        # Synthetic doc number — not a real clerk doc num, but unique
        synthetic_id = (
            r.get("prop_address", "").replace(" ", "_")
            + "-" + fd_raw.replace("/", "")
        )
        rec: dict[str, Any] = {
            "doc_num":         f"FCL-{synthetic_id}",
            "doc_type":        "NOTICE OF TRUSTEE SALE",
            "filed":           fd_raw,
            "cat":             "NOFC",
            "cat_label":       "Notice of Foreclosure",
            "owner":           "",
            "grantee":         "",
            "homeowner_name":  "",
            "not_actionable":  False,
            "amount":          "",
            "legal":           "",
            "prop_address":    r.get("prop_address", ""),
            "prop_city":       r.get("prop_city", ""),
            "prop_state":      r.get("prop_state", "TX"),
            "prop_zip":        r.get("prop_zip", ""),
            "mail_address":    r.get("prop_address", ""),
            "mail_city":       r.get("prop_city", ""),
            "mail_state":      r.get("prop_state", "TX"),
            "mail_zip":        r.get("prop_zip", ""),
            "year_built":      "",
            "sqft":            "",
            "market_value":    "",
            "deed_year":       "",
            "long_term_owner": False,
            "sale_date":       r.get("sale_date", ""),
            "source":          "Collin County Foreclosure Notices Portal",
            "clerk_url":       FORECLOSURE_URL,
            "flags":           ["Pre-foreclosure", "New this week"],
            "score":           80,
        }
        out.append(rec)

    log.info(
        "Foreclosure filtering: %d kept | %d skipped (wrong type) | %d skipped (out of window) | %d skipped (bad date)",
        len(out), skipped_type, skipped_date, skipped_parse,
    )
    return out
