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


def _parse_row_text(text: str) -> dict[str, str]:
    """Parse one foreclosure row from rendered cell text.

    The portal renders each property as a single table cell with newline-
    or <br>-separated fields, e.g.:

        10022 PLAINSMAN LN  FRISCO, TX 75035
        City: Frisco
        Sale Date: 06/02/2026
        File Date: 05/07/2026
        Property Type: Residential Single Family (A1)
    """
    rec: dict[str, str] = {}
    # Split on any newline-ish or HTML break, then strip
    lines = [seg.strip() for seg in re.split(r"<br\s*/?>|\r\n|\n", text) if seg.strip()]
    if not lines:
        return rec

    # First line should contain street + city + state + zip
    addr_m = re.match(
        r"(.+?)\s{2,}([A-Z][A-Z\s]+?),\s*([A-Z]{2})\s+(\d{5}(?:-\d{4})?)",
        lines[0],
    )
    if addr_m:
        rec["prop_address"] = addr_m.group(1).strip().upper()
        rec["prop_city"]    = addr_m.group(2).strip().upper()
        rec["prop_state"]   = addr_m.group(3).strip()
        rec["prop_zip"]     = addr_m.group(4).strip()[:5]
    else:
        # Fallback: store the raw first line so we have something
        rec["prop_address"] = lines[0].strip().upper()

    # Remaining lines are "Label: Value" pairs
    for line in lines[1:]:
        m = re.match(r"([A-Za-z][A-Za-z\s]*?)\s*:\s*(.+)", line)
        if not m:
            continue
        label = m.group(1).strip().lower()
        value = m.group(2).strip()
        if "sale" in label and "date" in label:
            rec["sale_date"] = value
        elif "file" in label and "date" in label:
            rec["file_date"] = value
        elif "property type" in label:
            rec["property_type"] = value
        elif label == "city" and not rec.get("prop_city"):
            rec["prop_city"] = value.upper()

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
    # The portal renders each property as a row. We try a few strategies
    # because the DOM may vary; the most reliable signal is text containing
    # 'Sale Date' and 'File Date' in the same block.
    candidate_selectors = [
        "table tbody tr",
        ".property-card",
        ".listing-row",
        ".result-row",
        "[class*='property']",
        "[class*='result']",
    ]

    blocks: list[str] = []
    for sel in candidate_selectors:
        try:
            loc = page.locator(sel)
            n = await loc.count()
            if n == 0:
                continue
            texts = await loc.all_text_contents()
            # Keep only blocks that look like a foreclosure row
            for t in texts:
                if "Sale Date" in t and "File Date" in t:
                    blocks.append(t)
            if blocks:
                log.info("  matched %d rows via selector: %s", len(blocks), sel)
                break
        except Exception:
            continue

    if not blocks:
        # Last-resort: split the whole body on the address pattern
        body_text = await page.locator("body").inner_text()
        # Try a per-row split using "File Date:" as a tail marker
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

    for r in raw_rows:
        pt = r.get("property_type", "")
        if property_type_filter and pt != property_type_filter:
            skipped_type += 1
            continue
        fd_raw = r.get("file_date", "")
        try:
            fd = datetime.strptime(fd_raw, "%m/%d/%Y")
        except (ValueError, TypeError):
            skipped_parse += 1
            continue
        if fd < date_from or fd > date_to:
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
