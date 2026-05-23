#!/usr/bin/env python3
"""
Collin County Probate (Affidavit of Heirship) Document Enricher
================================================================

For each PRO-category record, this module signs into the Collin County clerk
portal, downloads the clean (un-watermarked) official PDF of the document,
extracts its text, and parses the actionable details:

    affiant_name      : the heir/filer — the LIVING person you contact
    affiant_address   : their mailing address
    decedent_name     : the deceased (already known, used as cross-check)
    property_address  : where the decedent owned/resided
    owned_property    : True / False / None
    will_status       : note when an unprobated will is mentioned
    legal_description : lot/block legal text

The decedent is deceased and not contactable; the affiant is the lead. This
is what converts a "SCHULTZ LAURENCE — deceased estate" record into a mailable
"Janet L. Schultz, 4505 Sanderosa Lane" lead.

Credentials come from environment variables (set as GitHub Actions secrets):
    CLERK_USERNAME
    CLERK_PASSWORD

If credentials are missing, login fails, or OCR libs aren't installed, the
module degrades gracefully: PRO records keep their decedent-name fallback and
the rest of the run is unaffected.

Dependencies (added to the GitHub Actions workflow):
    apt:  tesseract-ocr  poppler-utils
    pip:  pytesseract  pdf2image  pillow  pdfplumber
"""

from __future__ import annotations

import logging
import os
import re
import tempfile
import urllib.parse
from pathlib import Path
from typing import Any

from playwright.async_api import (
    BrowserContext,
    Page,
    TimeoutError as PWTimeout,
    async_playwright,
)

log = logging.getLogger("probate_enricher")

CLERK_BASE      = "https://collin.tx.publicsearch.us"
NAV_TIMEOUT_MS  = 30_000
ACTION_WAIT_MS  = 1_500
VIEWER_WAIT_MS  = 3_000
MAX_DOCS        = 60          # safety cap on downloads per run
DOWNLOAD_DIR    = Path(tempfile.gettempdir()) / "probate_docs"

# ---- Optional text-extraction dependencies (degrade gracefully) -------------
try:
    import pdfplumber
    _PDFPLUMBER = True
except ImportError:
    _PDFPLUMBER = False

try:
    import pytesseract
    from pdf2image import convert_from_path
    from PIL import Image  # noqa: F401  (used indirectly by pdf2image)
    _OCR = True
except ImportError:
    _OCR = False


# =============================================================================
# Parser  (proven against the real Affidavit of Heirship document)
# =============================================================================

def _clean_name(s: str) -> str:
    s = re.sub(r"\s+", " ", s).strip().rstrip(",")
    # Drop trailing connective words OCR sometimes attaches
    s = re.sub(r"\b(being|hereinafter|and|the)\b.*$", "", s, flags=re.I).strip()
    return s.rstrip(",").strip()


def _clean_addr(s: str) -> str:
    s = re.sub(r"\s+", " ", s).strip().rstrip(".").rstrip(",")
    s = re.sub(r"\s*,\s*", ", ", s)
    return s


def parse_affidavit_of_heirship(text: str) -> dict[str, Any]:
    """Extract heir/decedent/property fields from the standard Texas
    Affidavit of Heirship boilerplate. Uses several anchor patterns per
    field so it tolerates OCR noise and document-to-document variation."""
    result: dict[str, Any] = {
        "affiant_name": "", "affiant_address": "",
        "decedent_name": "", "property_address": "",
        "owned_property": None, "will_status": "",
        "legal_description": "",
    }
    if not text:
        return result
    t = re.sub(r"\s+", " ", text).strip()

    # A personal name = 2-4 consecutive capitalized tokens (allowing middle
    # initials like 'D.'). Requiring consecutive caps prevents the match from
    # reaching back across lowercase connectors ('the surviving spouse of').
    NAME = r"[A-Z][A-Za-z.'\-]+(?:\s+[A-Z][A-Za-z.'\-]+){1,3}"

    # ---- Affiant (heir / filer) --------------------------------------------
    for pat in (
        rf'personally appeared\s+({NAME})\s*\(\s*hereinafter\s+["\u201c]?\s*Affiant',
        rf'personally appeared\s+({NAME})\s*\(',
        rf'My name is\s+({NAME})',
    ):
        m = re.search(pat, t)
        if m:
            result["affiant_name"] = _clean_name(m.group(1))
            break

    # ---- Decedent ----------------------------------------------------------
    for pat in (
        rf'({NAME}),?\s*Deceased\s*\(\s*hereinafter',
        rf'(?:spouse|child|son|daughter|heir|parent|sibling|widow|widower)\s+of\s+({NAME})',
        rf'({NAME}),?\s*Deceased',
    ):
        m = re.search(pat, t)
        if m:
            result["decedent_name"] = _clean_name(m.group(1))
            break

    # ---- Affiant mailing address -------------------------------------------
    m = re.search(r'mailing address is\s+(.+?)\.\s', t, re.I)
    if m:
        result["affiant_address"] = _clean_addr(m.group(1))

    # ---- Property + owned flag ---------------------------------------------
    m = re.search(
        r'Decedent\s+owned\b.{0,80}?(?:located|situated)\s+at\s+(.+?),?\s+and being',
        t, re.I,
    )
    if m:
        result["owned_property"] = True
        result["property_address"] = _clean_addr(m.group(1))
    else:
        m = re.search(
            r'(?:owned|owned and resided in).{0,60}?real property\s+(?:located|situated)\s+at\s+(.+?)[\.,]\s',
            t, re.I,
        )
        if m:
            result["owned_property"] = True
            result["property_address"] = _clean_addr(m.group(1))
        elif re.search(r'did not own (?:any )?real property|owned no real property|no real property', t, re.I):
            result["owned_property"] = False

    # ---- Legal description -------------------------------------------------
    m = re.search(r'particularly described as follows:\s*(.+?)(?:\s+\d+\.\s|\Z)', t, re.I)
    if m:
        result["legal_description"] = re.sub(r"\s+", " ", m.group(1)).strip()

    # ---- Will status -------------------------------------------------------
    if re.search(r'will has not been admitted to probate|no administration.{0,40}opened', t, re.I):
        result["will_status"] = "Unprobated will / no administration opened"
    elif re.search(r'died (?:intestate|without (?:a )?will)', t, re.I):
        result["will_status"] = "Intestate (no will)"
    elif re.search(r'Last Will and Testament', t, re.I):
        result["will_status"] = "Will referenced"

    return result


# =============================================================================
# PDF text extraction:  text-layer first, OCR fallback
# =============================================================================

def _extract_pdf_text(pdf_path: Path) -> str:
    """Return text from a PDF. Tries the embedded text layer first (fast,
    perfect); falls back to rasterize + Tesseract OCR for scanned PDFs."""
    text = ""
    if _PDFPLUMBER:
        try:
            with pdfplumber.open(str(pdf_path)) as pdf:
                for pg in pdf.pages:
                    text += (pg.extract_text() or "") + "\n"
        except Exception as e:
            log.debug("pdfplumber failed on %s: %s", pdf_path.name, e)

    if len(text.strip()) >= 120:
        log.info("    text layer extracted (%d chars)", len(text.strip()))
        return text

    if not _OCR:
        log.warning("    no text layer and OCR libs unavailable")
        return text

    try:
        images = convert_from_path(str(pdf_path), dpi=300)
        ocr_text = ""
        for img in images:
            ocr_text += pytesseract.image_to_string(img) + "\n"
        log.info("    OCR extracted (%d chars from %d page(s))",
                 len(ocr_text.strip()), len(images))
        return ocr_text
    except Exception as e:
        log.warning("    OCR failed on %s: %s", pdf_path.name, e)
        return text


# =============================================================================
# Clerk portal navigation
# =============================================================================

def _results_url(doc_num: str) -> str:
    rng = urllib.parse.quote(f'["{doc_num}"]')
    return (f"{CLERK_BASE}/results?department=RP"
            f"&documentNumberRange={rng}&searchType=advancedSearch")


async def _login(page: Page, username: str, password: str) -> bool:
    """Sign into the clerk portal via the /signin page.

    The login form (confirmed from the live portal) is a same-domain page at
    /signin with an 'Email' placeholder input, a 'Password' placeholder input,
    and a 'Sign In' submit button. No SSO redirect.
    """
    # Use domcontentloaded (not networkidle) — the SPA holds connections open
    # so networkidle never fires and would just time out.
    try:
        await page.goto(f"{CLERK_BASE}/signin?returnPath=%2F",
                        wait_until="domcontentloaded", timeout=NAV_TIMEOUT_MS)
    except PWTimeout:
        log.warning("signin page load timeout, continuing")
    await page.wait_for_timeout(ACTION_WAIT_MS)

    # Wait for the email field to actually render before interacting.
    email_field = None
    for cand in (
        page.get_by_placeholder("Email", exact=True),
        page.get_by_placeholder(re.compile(r"email", re.I)),
        page.locator('input[type="email"]'),
        page.locator('input[type="text"]').first,
    ):
        try:
            await cand.first.wait_for(state="visible", timeout=6000)
            email_field = cand.first
            break
        except Exception:
            continue

    pass_field = None
    for cand in (
        page.get_by_placeholder("Password", exact=True),
        page.get_by_placeholder(re.compile(r"password", re.I)),
        page.locator('input[type="password"]'),
    ):
        try:
            if await cand.count():
                pass_field = cand.first
                break
        except Exception:
            continue

    if email_field is None or pass_field is None:
        log.error("Login form fields not found (email=%s pass=%s) at /signin",
                  email_field is not None, pass_field is not None)
        return False

    try:
        await email_field.fill(username, timeout=4000)
        await pass_field.fill(password, timeout=4000)
    except Exception as e:
        log.error("Failed filling login fields: %s", e)
        return False

    # Click the Sign In submit button
    clicked = False
    for cand in (
        page.get_by_role("button", name=re.compile(r"^\s*sign\s*in\s*$", re.I)),
        page.locator('button:has-text("Sign In")'),
        page.locator('button[type="submit"]'),
    ):
        try:
            if await cand.count():
                await cand.first.click(timeout=4000)
                clicked = True
                break
        except Exception:
            continue
    if not clicked:
        log.error("Sign In button not found")
        return False

    await page.wait_for_timeout(VIEWER_WAIT_MS)

    # Confirm we're signed in: the header switches Sign In -> Sign Out, and we
    # land back on the search app (returnPath=%2F).
    try:
        signout = page.get_by_text(re.compile(r"sign\s*out", re.I))
        if await signout.count():
            log.info("Clerk portal login successful")
            return True
    except Exception:
        pass
    # Fallback check: are the login fields gone?
    try:
        still_login = await page.get_by_placeholder("Password", exact=True).count()
        if still_login == 0:
            log.info("Clerk portal login appears successful (form cleared)")
            return True
    except Exception:
        pass
    log.warning("Login submitted but couldn't confirm signed-in state; proceeding")
    return True


async def _download_document_pdf(page: Page, doc_num: str) -> Path | None:
    """Navigate to a document and download its PDF. Returns the saved path."""
    try:
        await page.goto(_results_url(doc_num), wait_until="networkidle", timeout=NAV_TIMEOUT_MS)
    except PWTimeout:
        log.warning("    results page timeout for %s", doc_num)
    await page.wait_for_timeout(ACTION_WAIT_MS)

    # Click the result row to open the document viewer
    clicked = False
    for cand in (
        page.locator("table tbody tr").first,
        page.locator('[class*="result-row"]').first,
        page.locator('a[href*="doc"]').first,
        page.get_by_text(doc_num).first,
    ):
        try:
            if await cand.count():
                await cand.click(timeout=4000)
                clicked = True
                break
        except Exception:
            continue
    if not clicked:
        log.warning("    couldn't open viewer for %s", doc_num)
        return None
    await page.wait_for_timeout(VIEWER_WAIT_MS)

    # Trigger the download
    DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)
    for cand in (
        page.get_by_role("button", name=re.compile(r"download", re.I)),
        page.get_by_role("link",   name=re.compile(r"download", re.I)),
        page.locator('button:has-text("Download")'),
        page.locator('[aria-label*="download" i], [title*="download" i]'),
    ):
        try:
            if await cand.count() == 0:
                continue
            async with page.expect_download(timeout=15_000) as dl_info:
                await cand.first.click(timeout=4000)
            download = await dl_info.value
            dest = DOWNLOAD_DIR / f"{doc_num}.pdf"
            await download.save_as(str(dest))
            log.info("    downloaded %s (%d bytes)", dest.name, dest.stat().st_size)
            return dest
        except Exception as e:
            log.debug("    download attempt failed: %s", e)
            continue

    log.warning("    no working download control for %s", doc_num)
    return None


# =============================================================================
# Orchestration
# =============================================================================

async def enrich_probate_records(records: list[dict]) -> list[dict]:
    """Enrich PRO-category records in place with affiant/property/will data
    read from the official document PDFs. Returns the same list."""
    pro = [r for r in records if r.get("cat") == "PRO"]
    if not pro:
        return records

    username = os.environ.get("CLERK_USERNAME", "").strip()
    password = os.environ.get("CLERK_PASSWORD", "").strip()
    if not (username and password):
        log.warning("CLERK_USERNAME/CLERK_PASSWORD not set — skipping probate enrichment")
        return records
    if not (_PDFPLUMBER or _OCR):
        log.warning("No PDF text-extraction libs installed — skipping probate enrichment")
        return records

    log.info("Probate enrichment: %d PRO record(s) to process (cap %d)", len(pro), MAX_DOCS)

    async with async_playwright() as pw:
        browser = await pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-dev-shm-usage",
                  "--disable-blink-features=AutomationControlled"],
        )
        context = await browser.new_context(
            accept_downloads=True,
            user_agent=("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                        "(KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36"),
        )
        try:
            page = await context.new_page()
            if not await _login(page, username, password):
                log.error("Login failed — skipping probate enrichment")
                return records

            processed = enriched = 0
            for rec in pro:
                if processed >= MAX_DOCS:
                    log.warning("Hit MAX_DOCS cap (%d); remaining PRO records left as-is", MAX_DOCS)
                    break
                doc_num = rec.get("doc_num", "")
                if not doc_num:
                    continue
                processed += 1
                log.info("  [%d/%d] doc %s", processed, len(pro), doc_num)
                pdf_path = await _download_document_pdf(page, doc_num)
                if not pdf_path:
                    continue
                text = _extract_pdf_text(pdf_path)
                parsed = parse_affidavit_of_heirship(text)
                if _apply_enrichment(rec, parsed):
                    enriched += 1
                try:
                    pdf_path.unlink()
                except Exception:
                    pass

            log.info("Probate enrichment complete: %d/%d documents read & parsed",
                     enriched, processed)
        finally:
            await context.close()
            await browser.close()

    return records


def _apply_enrichment(rec: dict, parsed: dict) -> bool:
    """Write parsed fields onto the record. The affiant becomes the contact
    name; CCAD-derived prop_address is preserved as fallback. Returns True
    if we recovered at least an affiant name."""
    got_affiant = bool(parsed.get("affiant_name"))

    if got_affiant:
        rec["affiant_name"]   = parsed["affiant_name"]
        rec["homeowner_name"] = parsed["affiant_name"]   # the living contact
        rec["owner"]          = parsed["affiant_name"]
    if parsed.get("affiant_address"):
        rec["affiant_address"] = parsed["affiant_address"]
        # Prefer the heir's stated mailing address for outreach
        rec["mail_address_doc"] = parsed["affiant_address"]
    if parsed.get("decedent_name"):
        rec["decedent_name"] = parsed["decedent_name"]
    if parsed.get("property_address"):
        rec["property_address_doc"] = parsed["property_address"]
        # Only override CCAD prop_address if we don't already have one
        if not rec.get("prop_address"):
            rec["prop_address"] = parsed["property_address"]
    if parsed.get("owned_property") is not None:
        rec["owned_property"] = parsed["owned_property"]
    if parsed.get("will_status"):
        rec["will_status"] = parsed["will_status"]
    if parsed.get("legal_description"):
        rec["legal_description"] = parsed["legal_description"]

    # Flags
    flags = rec.setdefault("flags", [])
    if got_affiant and "Heir identified" not in flags:
        flags.append("Heir identified")
    if parsed.get("owned_property") and "Decedent owned property" not in flags:
        flags.append("Decedent owned property")
    if parsed.get("will_status", "").startswith("Unprobated") and "Unprobated estate" not in flags:
        flags.append("Unprobated estate")

    rec["doc_read_ok"] = got_affiant
    return got_affiant
