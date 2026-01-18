# ==========================================
# other_tasks.py  — Clean, Modular, No Login
# Logs & "already sent" flags stored in State sheet (no JSON files)
# ==========================================

import datetime
import datetime as dt
import time
import re
import random
import os
import base64
import traceback
import requests
from bs4 import BeautifulSoup
from datetime import timezone, timedelta

IST = timezone(timedelta(hours=5, minutes=30))
# Selenium globals (injected from main)
driver = None
wait = None


import gspread
from oauth2client.service_account import ServiceAccountCredentials
from gspread.exceptions import WorksheetNotFound
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC

# Recipients reused across different reports
RECIPIENTS = [
    ("Shraddha",  "7406011400"),
    ("Vikas",     "7406611400"),
    ("kumkum",   "8305838835"),
    ("Nayak",     "7828564967"),
    ("Manager",   "9770159033")
]

TODAY = datetime.date.today().strftime("%d-%m-%Y")

# ==========================================
# CONFIG
# ==========================================

CREDENTIALS_PATH = "yesmadamndore-029caf40a32b.json"

# Main "Other Tasks" spreadsheet
SHEET_URL = (
    "https://docs.google.com/spreadsheets/d/"
    "16f-QarUEooXiwymMYAQxqHfulaNExidL47dasKjiP1s/edit#gid=0"
)

DATA_SHEET_NAME = "Sheet1"
SP_LIST_SHEET   = "SP List"
EMP_LIST_SHEET  = "Employee List"

LEAVE_SHEET_URL = (
    "https://docs.google.com/spreadsheets/d/"
    "1IOU9eTV7hjP91i2MDvG_hO0HyPe6whggrHgdaFklt9I/edit"
)

INTERAKT_API_KEY = "hXanaXFAqNGSP8-3HiENI46y0AP4wb26niPGsp6s0cs"
INTERAKT_URL     = "https://api.interakt.ai/v1/public/message/"


# ======================================================
# FRANCHISE PRODUCT ASSIGNED REPORT CONFIG
# ======================================================

FRANCHISE_REPORT_URL = (
    "https://notiononlinesolutions.tech/report/franchise-product-assigned"
)

FRANCHISE_TARGET_SHEET_URL = (
    "https://docs.google.com/spreadsheets/d/"
    "1SRP1m5tjhuNS3DFIwdW55BM1kxCYWgYLhYLK3ytpPzU/edit"
)

FRANCHISE_SHEET_NAME = "Expected_Consumption"


# ==========================================
# GOOGLE SHEET AUTH
# ==========================================

def _open_spreadsheet():
    """
    Open the main Other Tasks spreadsheet (SHEET_URL).
    Used also as home for the 'State' sheet where we store flags.
    """
    scope = [
        "https://spreadsheets.google.com/feeds",
        "https://www.googleapis.com/auth/drive",
        "https://www.googleapis.com/auth/spreadsheets",
    ]
    creds = ServiceAccountCredentials.from_json_keyfile_name(CREDENTIALS_PATH, scope)
    gc = gspread.authorize(creds)
    return gc.open_by_url(SHEET_URL)

# ==========================================
# STATE SHEET HELPERS (Key = Column header, Value in Row 2)
# ==========================================

# Static keys we want to ALWAYS see as columns in the State sheet
STATE_BASE_KEYS = [
    # Existing keys used by BookingOpenedMapView.py (do not touch values)
    "LastSeenOrderIds",
    "LastRolloverDate",
    "DailySummaryLastSentDate",
    "AttendanceLastSentDate",

    # New keys for this file
    "YESTERDAY_LEAVE_DATE",   # once-per-day yesterday leave report
    "FEEDBACK_DATE",          # once-per-day feedback WA report

    "TODAY_LEAVE_SLOTS",      # multi-slot today leave report
    "RIDER_SLOTS",            # multi-slot rider report
    "LEAVE_PROCESS_SLOTS",    # multi-slot leave process reminder
    "WEEKOFF_SLOTS",          # multi-slot weekoff report
]

def _get_state_sheet():
    """
    Returns the 'State' worksheet in the main spreadsheet.
    Creates it if missing.
    Layout:
        Row 1 = headers (keys)
        Row 2 = values
    """
    try:
        ss = _open_spreadsheet()
        try:
            state = ss.worksheet("State")
        except WorksheetNotFound:
            state = ss.add_worksheet("State", rows=10, cols=10)
        return state
    except Exception as e:
        print(f"⚠️ State sheet open error: {e}")
        return None


def _ensure_state_base_columns():
    """
    Make sure all STATE_BASE_KEYS exist as headers in row 1.
    Does NOT overwrite any existing values.
    Only creates missing columns with empty value in row 2.
    """
    state = _get_state_sheet()
    if state is None:
        return

    try:
        headers = state.row_values(1)
        col_count = len(headers)

        # If sheet is brand new (no rows at all), ensure at least 2 rows exist
        # update_cell will create rows as needed anyway.

        for key in STATE_BASE_KEYS:
            if key not in headers:
                col_count += 1
                print(f"🔧 Creating State column: {key} (col {col_count})")
                state.update_cell(1, col_count, key)
                state.update_cell(2, col_count, "")  # default empty
                headers.append(key)

    except Exception as e:
        print(f"_ensure_state_base_columns error: {e}")


def set_selenium_context(_driver, timeout=15):
    global driver, wait
    driver = _driver
    wait = WebDriverWait(driver, timeout)

def state_get_col(col_name, default=None):
    """
    Get a value from 'State' sheet using header in row 1 and value in row 2.
    If the sheet or column does not exist, returns default.
    """
    state = _get_state_sheet()
    if state is None:
        return default

    try:
        headers = state.row_values(1)
        values  = state.row_values(2)

        if col_name in headers:
            idx = headers.index(col_name)  # 0-based
            if idx < len(values):
                val = (values[idx] or "").strip()
                if val != "":
                    return val
        return default
    except Exception as e:
        print(f"state_get_col error for {col_name}: {e}")
        return default


def state_set_col(col_name, value):
    """
    Set a value in 'State' sheet.
    If the column does not exist yet, it will be appended at the end.
    """
    state = _get_state_sheet()
    if state is None:
        return

    try:
        headers = state.row_values(1)
        if col_name in headers:
            col = headers.index(col_name) + 1  # 1-based
        else:
            col = len(headers) + 1
            print(f"🔧 Creating NEW dynamic State column: {col_name} (col {col})")
            state.update_cell(1, col, col_name)

        state.update_cell(2, col, str(value))
    except Exception as e:
        print(f"state_set_col error for {col_name}: {e}")


# ======================================================
# GENERIC HELPERS FOR SLOTS & ONCE-PER-DAY LOGIC
# ======================================================

def _today_str():
    return datetime.date.today().strftime("%Y-%m-%d")


def _load_slots_state(prefix):
    """
    For multi-slot tasks (e.g. leave at 13,16,20):

    Stored in State sheet as:
        key   = f"{prefix}_SLOTS"
        value = "YYYY-MM-DD|13,16"

    Returns: list of sent hours (as strings) for TODAY.
    """
    key = f"{prefix}_SLOTS"
    raw = state_get_col(key, "")
    if not raw:
        return []

    try:
        date_part, hours_part = raw.split("|", 1)
    except ValueError:
        # Old / corrupt format
        return []

    if date_part != _today_str():
        # Different day → treat as nothing sent today
        return []

    return [h for h in hours_part.split(",") if h.strip()]


def _save_slots_state(prefix, hours):
    """
    Save slot hours (list of strings) for TODAY in State.
    """
    key   = f"{prefix}_SLOTS"
    today = _today_str()
    uniq  = sorted(set(hours), key=lambda x: int(x)) if hours else []
    if not uniq:
        state_set_col(key, "")
    else:
        value_str = today + "|" + ",".join(uniq)
        state_set_col(key, value_str)


def _pick_due_hour(scheduled_hours, sent_hours, now_hour):
    """
    Decide which hour slot (if any) is due to send NOW.

    - scheduled_hours: list[int], e.g. [13,16,20]
    - sent_hours: list[str], e.g. ["13","16"]
    - now_hour: int

    Returns:
        int hour that should be sent now, or None.
    """
    sent_set = set(sent_hours)
    for h in sorted(scheduled_hours):
        if h <= now_hour and str(h) not in sent_set:
            return h
    return None


def _has_run_today(prefix):
    """
    For once-per-day tasks.

    key   = f"{prefix}_DATE"
    value = "YYYY-MM-DD"
    """
    key   = f"{prefix}_DATE"
    value = state_get_col(key, "")
    return value == _today_str()


def _mark_run_today(prefix):
    key = f"{prefix}_DATE"
    state_set_col(key, _today_str())


# ======================================================
# Helper — Broadcast message to all recipients
# ======================================================

def _broadcast_leave_message(message):
    recipients = [
        ("Shraddha", "7406011400"),
        ("Vikas",    "7406611400"),
        ("kumkum",  "8305838835"),
        ("Nayak",    "7828564967"),
    ]

    for name, phone in recipients:
        ok = _send_interakt_text(phone, message)
        if ok:
            print(f"✔ Sent to {name} ({phone})")
        else:
            print(f"❌ Failed to send to {name} ({phone})")


# ======================================================
# PLAINTEXT WHATSAPP SENDER (Interakt API)
# ======================================================

def _send_interakt_text(phone, message):
    try:
        digits = re.sub(r"\D", "", phone or "")
        if len(digits) < 10:
            print(f"WA TEXT ERROR: invalid phone {phone}")
            return False
        digits = digits[-10:]

        api_key = INTERAKT_API_KEY
        if not api_key:
            print("❌ INTERAKT_API_KEY missing")
            return False

        auth_header = base64.b64encode(f"{api_key}:".encode()).decode()

        headers = {
            "Authorization": f"Basic {auth_header}",
            "Content-Type": "application/json"
        }

        payload = {
            "countryCode": "+91",
            "phoneNumber": digits,
            "type": "Text",
            "data": {
                "message": message
            }
        }

        resp = requests.post(INTERAKT_URL, json=payload, headers=headers, timeout=20)
        print("WA TEXT SEND:", resp.status_code, resp.text)

        return resp.status_code in (200, 201)

    except Exception as e:
        print("WA TEXT SEND ERROR:", e)
        return False


# ==========================================
# HELPERS
# ==========================================

def _safe_wait(driver, condition, timeout=10):
    try:
        WebDriverWait(driver, timeout).until(condition)
        return True
    except Exception:
        return False


def _str_to_date(date_str):
    return datetime.datetime.strptime(date_str, "%d-%m-%Y").date()


# ======================================================
# TASK 1 — ADD-ON REPORT
# ======================================================

def run_addon_report(driver, spreadsheet,
                     start_date=None, end_date=None):

    if not start_date:
        start_date = TODAY
    if not end_date:
        end_date = TODAY

    print("🔵 Starting Add-on Report...")

    sheet    = spreadsheet.worksheet(DATA_SHEET_NAME)
    sp_sheet = spreadsheet.worksheet(SP_LIST_SHEET)

    sp_rows = sp_sheet.get_all_values()[1:]
    experts = []

    for r in sp_rows:
        if len(r) < 3:
            continue

        emp_id = r[0].strip()
        name   = r[1].strip()
        hub_id = r[2].strip()

        if not emp_id or "(" in name or emp_id.isalpha():
            continue

        experts.append((name, emp_id, hub_id))

    print(f"   → Loaded {len(experts)} SPs")

    date_list = []
    s = _str_to_date(start_date)
    e = _str_to_date(end_date)
    while s <= e:
        date_list.append(s.strftime("%d-%m-%Y"))
        s += datetime.timedelta(days=1)

    existing      = sheet.get_all_values()
    existing_rows = existing[1:] if len(existing) > 1 else []

    def update_or_append(date_str, name, emp_id, addon_value, hub_id):
        for idx, row in enumerate(existing_rows):
            if len(row) >= 3 and row[0] == date_str and row[2] == emp_id:
                sheet.update_cell(idx + 2, 4, addon_value)
                sheet.update_cell(idx + 2, 5, hub_id)
                return
        sheet.append_row([date_str, name, emp_id, addon_value, hub_id])
        existing_rows.append([date_str, name, emp_id, str(addon_value), hub_id])

    for date_str in date_list:
        for name, emp_id, hub_id in experts:
            try:
                url = (
                    "https://notiononlinesolutions.tech/report/sp"
                    f"?id={emp_id}&sdate={date_str}&edate={date_str}"
                )
                driver.get(url)

                _safe_wait(
                    driver,
                    lambda d: d.find_elements(By.CSS_SELECTOR, "tfoot tr th")
                    or d.find_elements(By.XPATH, "//*[contains(text(),'No data')]")
                    or d.find_elements(By.XPATH, "//*[contains(text(),'No records')]")
                )

                soup        = BeautifulSoup(driver.page_source, "html.parser")
                headers     = soup.select("thead tr th")
                header_map  = {h.text.strip(): i for i, h in enumerate(headers)}
                addon_index = header_map.get("Add On")
                addon_value = 0.0

                if addon_index is not None:
                    totals = soup.select("tfoot tr th")
                    if len(totals) > addon_index:
                        raw = totals[addon_index].text.strip()
                        raw = raw.replace(",", "")
                        raw = re.sub(r"[^\d.]", "", raw)
                        addon_value = float(raw) if raw else 0.0

                update_or_append(date_str, name, emp_id, addon_value, hub_id)
                time.sleep(random.uniform(0.25, 0.5))

            except Exception as e:
                print(f"⚠️ Add-on error for {name} ({emp_id}) {date_str}: {e}")

    print("✔ Add-on Report Completed\n")


# ======================================================
# TASK 2 — WEEKOFF SCRAPING
# ======================================================

from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait, Select
from selenium.webdriver.support import expected_conditions as EC

def run_weekoff(driver, spreadsheet):
    print("🔵 Starting Weekoff Scraping...")

    # Reset sheet
    try:
        old = spreadsheet.worksheet("WEEKOFF_SET_CURRENT")
        spreadsheet.del_worksheet(old)
    except Exception:
        pass

    ws = spreadsheet.add_worksheet("WEEKOFF_SET_CURRENT", rows="200", cols="3")
    ws.append_row(["SP NAME", "ID", "WEEKOFF DAY"])

    sp_sheet = spreadsheet.worksheet(SP_LIST_SHEET)
    experts = sp_sheet.get_all_values()[1:]

    rows_to_append = []

    for idx, row in enumerate(experts, start=1):
        if len(row) < 2:
            continue

        emp_id = row[0].strip()
        name   = row[1].strip()

        if not emp_id:
            continue

        weekoff = "Not Set"

        # ⭐ DEBUG PRINT
        url = f"https://notiononlinesolutions.tech/sp/view-and-manage/{emp_id}/settings"
        print(f"🔍 DEBUG → {name} ({emp_id}) → {url}")

        try:
            # Load settings page
            driver.get(url)

            _safe_wait(driver, EC.presence_of_element_located((By.TAG_NAME, "body")))

            # Wait for weekOff dropdown
            try:
                dropdown = WebDriverWait(driver, 10).until(
                    EC.presence_of_element_located((By.ID, "weekOff"))
                )

                # Read weekoff
                select = Select(dropdown)
                weekoff = select.first_selected_option.text.strip()
                print(f"   📅 Weekoff = {weekoff}")

            except Exception as e_inner:
                print(f"⚠️ weekOff not found for {name} ({emp_id}) → {e_inner}")
                weekoff = "Not Available"

        except Exception as e:
            print(f"⚠️ Error loading {name} ({emp_id}) → {e}")
            weekoff = "Error"

        rows_to_append.append([name, emp_id, weekoff])
        time.sleep(random.uniform(0.3, 0.6))

    if rows_to_append:
        ws.append_rows(rows_to_append, value_input_option="RAW")

    print("✔ Weekoff Scraping Completed\n")

# ======================================================
# TASK 3 — PERFORMANCE REPORT
# ======================================================

def run_performance(driver, spreadsheet):
    print("🔵 Starting Performance Report...")

    try:
        old = spreadsheet.worksheet("SP_Performance")
        spreadsheet.del_worksheet(old)
    except Exception:
        pass

    perf = spreadsheet.add_worksheet("SP_Performance", rows="300", cols="8")
    perf.append_row([
        "SP NAME", "ID", "Overall Rating", "Exclusive Percent",
        "Last 50 Job Review Average", "Late Arrival Count",
        "Repeat Unique Customers", "Unique Customers"
    ])

    sp_sheet = spreadsheet.worksheet(SP_LIST_SHEET)
    experts  = sp_sheet.get_all_values()[1:]

    def get_metric(soup, regex):
        label = soup.find("label", string=re.compile(regex, re.I))
        span  = label.find_next_sibling("span") if label else None
        return span.text.strip() if span else "Not Found"

    for row in experts:
        # row[0] = SP NAME
        # row[1] = ID
        name   = row[0].strip()
        emp_id = row[1].strip()

        try:
            url = f"https://notiononlinesolutions.tech/sp/performance/{name}"
            print(f"Fetching: {url}")

            driver.get(url)

            _safe_wait(driver, EC.presence_of_element_located(
                (By.CSS_SELECTOR, "div.star-rating")
            ))

            soup      = BeautifulSoup(driver.page_source, "html.parser")
            overall   = get_metric(soup, "Overall Rating")
            exclusive = get_metric(soup, "Exclusive percent")
            last50    = get_metric(soup, "Last 50 Job Review Average")
            late      = get_metric(soup, "Late Arrival Count")
            repeat    = get_metric(soup, "Repeat Unique Customers")
            unique    = get_metric(soup, "Unique Customers")

            perf.append_row([
                name, emp_id, overall, exclusive, last50, late, repeat, unique
            ])

            time.sleep(random.uniform(0.25, 0.5))

        except Exception as e:
            print(f"⚠️ Performance error for {name} ({emp_id}): {e}")

    print("✔ Performance Report Completed\n")


# ======================================================
# TASK 4 — SEND DAILY ADD-ON REPORT TO TEAM (PLAIN TEXT)
# ======================================================

def run_send_daily_addon_report(driver, spreadsheet):
    print("🔵 Preparing Add-on Report for WhatsApp...")

    try:
        ws = spreadsheet.worksheet("SortedDataDaywise")
    except Exception as e:
        print("⚠️ Cannot open SortedDataDaywise:", e)
        return

    today    = datetime.date.today().strftime("%d-%m-%Y")
    all_rows = ws.get_all_values()

    if len(all_rows) <= 1:
        print("⚠️ No rows in SortedDataDaywise")
        return

    header = all_rows[0]
    data   = all_rows[1:]

    h = {header[i].strip(): i for i in range(len(header))}
    required_cols = ["Date", "Expert", "SP ID", "Add On ₹"]

    if any(col not in h for col in required_cols):
        print("⚠️ Missing columns in SortedDataDaywise")
        return

    c_date = h["Date"]
    c_exp  = h["Expert"]
    c_add  = h["Add On ₹"]

    today_rows = [
        r for r in data
        if len(r) > c_date and r[c_date].strip() == today
    ]

    if not today_rows:
        print("ℹ️ No add-on data for today")
        return

    lines = [f"📊 *Service Add-on Report — {today}*", ""]

    for r in today_rows:
        exp = r[c_exp].strip()

        addon_raw = r[c_add].strip().replace(",", "")
        try:
            addon_val = int(float(addon_raw or 0))
        except Exception:
            addon_val = 0

        lines.append(f"• {exp} — ₹{addon_val}")

    message = "\n".join(lines)

    recipients = [
        ("Shraddha", "7406011400"),
        ("Vikas",    "7406611400"),
        ("Kukum",  "8305838835"),
        ("Nayak",    "7828564967"),
    ]

    for name, phone in recipients:
        ok = _send_interakt_text(phone, message)
        if ok:
            print(f"✔ WhatsApp Add-on Report sent to {name} ({phone})")
        else:
            print(f"❌ Failed to send Add-on Report to {name} ({phone})")

    print()


# ======================================================
# TASK 5 — FETCH YESTERDAY LEAVE REPORT (ONCE PER DAY AFTER 8AM)
# ======================================================

def run_yesterday_leave_report(driver):
    print("🔵 Fetching Yesterday Leave Report...")

    now = datetime.datetime.now()

    # Only after 8 AM; if script was down 8–10, still allow later catch-up
    if now.hour < 8:
        print("⏳ Before 8AM — skipping Yesterday Leave for now")
        return

    if _has_run_today("YESTERDAY_LEAVE"):
        print("⏳ Yesterday Leave already sent today — skipping")
        return

    try:
        scope = [
            "https://spreadsheets.google.com/feeds",
            "https://www.googleapis.com/auth/drive"
        ]
        ServiceAccountCredentials.from_json_keyfile_name(CREDENTIALS_PATH, scope)
        gc          = gspread.service_account(filename=CREDENTIALS_PATH)
        spreadsheet = gc.open_by_url(LEAVE_SHEET_URL)
    except Exception as e:
        print("❌ Error opening Leave Spreadsheet:", e)
        return

    yesterday  = datetime.date.today() - datetime.timedelta(days=1)
    sheet_name = "Leave_Entry_" + yesterday.strftime("%d-%m-%Y")

    print("→ Looking for sheet:", sheet_name)

    try:
        ws = spreadsheet.worksheet(sheet_name)
    except Exception:
        print("⚠️ Leave sheet not found for:", yesterday)
        return

    rows = ws.get_all_values()
    if len(rows) <= 1:
        print("⚠️ Empty leave sheet")
        return

    header = rows[0]
    data   = rows[1:]

    h = {header[i].strip(): i for i in range(len(header))}
    required = ["Date", "Employee Name", "Leave Type", "Remark"]

    if any(col not in h for col in required):
        print("⚠️ Missing required leave columns")
        return

    c_date = h["Date"]
    c_name = h["Employee Name"]
    c_type = h["Leave Type"]
    c_rem  = h["Remark"]

    # Build report text — ONLY LEAVE entries
    lines = [
        f"📄 *Leave Report — {yesterday.strftime('%d-%m-%Y')}*",
        ""
    ]

    leave_found = False

    for r in data:
        try:
            name       = r[c_name].strip()
            leave_type = r[c_type].strip()
            remark     = r[c_rem].strip()

            if leave_type.lower() == "leave":
                leave_found = True
                if remark:
                    lines.append(f"• {name} — Leave ({remark})")
                else:
                    lines.append(f"• {name} — Leave")
        except Exception:
            continue

    if not leave_found:
        lines.append("_No leave today_")

    message = "\n".join(lines)
    print("Message Prepared:\n", message)

    recipients = [
        ("Shraddha", "7406011400"),
        ("Vikas",    "7406611400"),
        ("Kukum",  "8305838835"),
        ("Nayak",    "7828564967"),
    ]

    for name, phone in recipients:
        ok = _send_interakt_text(phone, message)
        if ok:
            print(f"✔ Leave Report sent to {name} ({phone})")
        else:
            print(f"❌ Failed to send Leave Report to {name} ({phone})")

    _mark_run_today("YESTERDAY_LEAVE")
    print("✔ Leave Report Completed\n")


# ======================================================
# TASK 6 — TODAY LEAVE REPORT (1PM, 4PM, 8PM — catch-up)
# ======================================================

def run_today_leave_report(driver):
    print("🔵 Checking Today Leave Report...")

    now = datetime.datetime.now()
    hr  = now.hour

    # SCHEDULED HOURS (1 PM, 4 PM, 8 PM)
    SLOTS = [13, 16, 20]

    # Load what we already sent today from State
    sent_hours = _load_slots_state("TODAY_LEAVE")

    # Decide if any slot is due now (including catch-up)
    due_hour = _pick_due_hour(SLOTS, sent_hours, hr)
    if due_hour is None:
        print("⏳ No pending TODAY LEAVE slot to send right now.")
        return

    print(f"⏰ TODAY LEAVE: sending for slot {due_hour}:00 (current hour = {hr})")

    # OPEN TODAY LEAVE SHEET
    try:
        scope = [
            "https://spreadsheets.google.com/feeds",
            "https://www.googleapis.com/auth/drive"
        ]
        creds = ServiceAccountCredentials.from_json_keyfile_name(CREDENTIALS_PATH, scope)
        gc    = gspread.authorize(creds)
        leave_spreadsheet = gc.open_by_url(LEAVE_SHEET_URL)
    except Exception as e:
        print("❌ Unable to open Leave Sheet:", e)
        sent_hours.append(str(due_hour))
        _save_slots_state("TODAY_LEAVE", sent_hours)
        return

    today      = datetime.date.today()
    sheet_name = "Leave_Entry_" + today.strftime("%d-%m-%Y")

    print("→ Looking for:", sheet_name)

    try:
        ws = leave_spreadsheet.worksheet(sheet_name)
    except Exception:
        print("⚠️ Today sheet not found → manager msg")
        _broadcast_leave_message("Manager leave report bnao")
        sent_hours.append(str(due_hour))
        _save_slots_state("TODAY_LEAVE", sent_hours)
        return

    rows = ws.get_all_values()
    if len(rows) <= 1:
        print("⚠️ Empty leave sheet → manager msg")
        _broadcast_leave_message("Manager leave report bnao")
        sent_hours.append(str(due_hour))
        _save_slots_state("TODAY_LEAVE", sent_hours)
        return

    header = rows[0]
    data   = rows[1:]

    h = {header[i].strip(): i for i in range(len(header))}
    if any(col not in h for col in ["Employee Name", "Leave Type", "Remark"]):
        _broadcast_leave_message("Manager leave report bnao")
        sent_hours.append(str(due_hour))
        _save_slots_state("TODAY_LEAVE", sent_hours)
        return

    c_name = h["Employee Name"]
    c_type = h["Leave Type"]
    c_rem  = h["Remark"]

    lines = [
        f"📄 *Today Leave Report — {today.strftime('%d-%m-%Y')}*",
        ""
    ]

    leave_found = False
    for r in data:
        try:
            name   = r[c_name].strip()
            type_  = r[c_type].strip()
            remark = r[c_rem].strip()
            if type_.lower() == "leave":
                leave_found = True
                if remark:
                    lines.append(f"• {name} — Leave ({remark})")
                else:
                    lines.append(f"• {name} — Leave")
        except Exception:
            continue

    if not leave_found:
        _broadcast_leave_message("Manager leave report bnao")
    else:
        msg = "\n".join(lines)
        _broadcast_leave_message(msg)

    sent_hours.append(str(due_hour))
    _save_slots_state("TODAY_LEAVE", sent_hours)
    print(f"✔ Sent Today Leave Report for slot {due_hour}:00 (current hour = {hr})\n")


# ======================================================
# TASK 7 — YESTERDAY RIDER REPORT (slots with catch-up)
# ======================================================

def run_yesterday_rider_report(driver):
    print("🔵 Checking Yesterday Rider Report...")

    # Safe import for voice
    try:
        from main import speak_message
    except Exception:
        def speak_message(msg):
            return

    now = datetime.datetime.now()
    hr  = now.hour

    # SCHEDULED HOURS — (same as earlier logic)
    SLOTS = [11, 13, 19, 23]

    sent_hours = _load_slots_state("RIDER")
    due_hour   = _pick_due_hour(SLOTS, sent_hours, hr)

    if due_hour is None:
        print("⏳ No pending RIDER slot to send right now.")
        return

    print(f"⏰ RIDER: sending for slot {due_hour}:00 (current hour = {hr})")

    MISS_MSG = "Rider reading abhi tak nh chdai he : Check Nayak, Shubham , Vikhanshu"

    RIDER_SHEET_URL = (
        "https://docs.google.com/spreadsheets/d/"
        "153MFI_LJka22c09qCk0zK9XAEyqwyqNXLLhcfaNGB7A/edit"
    )

    try:
        scope = [
            "https://spreadsheets.google.com/feeds",
            "https://www.googleapis.com/auth/drive"
        ]
        creds = ServiceAccountCredentials.from_json_keyfile_name(CREDENTIALS_PATH, scope)
        gc    = gspread.authorize(creds)
        rider_spreadsheet = gc.open_by_url(RIDER_SHEET_URL)
    except Exception as e:
        print("❌ Unable to open Rider Sheet:", e)
        speak_message(MISS_MSG)
        print("🔊 Voice played for missing rider report")
        _broadcast_leave_message(MISS_MSG)
        sent_hours.append(str(due_hour))
        _save_slots_state("RIDER", sent_hours)
        return

    # Yesterday dd/mm/YYYY
    yesterday     = datetime.date.today() - datetime.timedelta(days=1)
    yesterday_str = yesterday.strftime("%d/%m/%Y")
    print("→ Fetching rows for:", yesterday_str)

    try:
        ws = rider_spreadsheet.worksheet("Daily Rider Summary")
    except Exception as e:
        print("⚠️ Rider sheet not found:", e)
        speak_message(MISS_MSG)
        print("🔊 Voice played for missing rider report")
        _broadcast_leave_message(MISS_MSG)
        sent_hours.append(str(due_hour))
        _save_slots_state("RIDER", sent_hours)
        return

    rows = ws.get_all_values()
    if len(rows) <= 1:
        print("⚠️ Empty rider sheet")
        speak_message(MISS_MSG)
        print("🔊 Voice played for missing rider report")
        _broadcast_leave_message(MISS_MSG)
        sent_hours.append(str(due_hour))
        _save_slots_state("RIDER", sent_hours)
        return

    header = rows[0]
    data   = rows[1:]
    h = {header[i].strip(): i for i in range(len(header))}
    required = [
        "Date", "Rider",
        "IN Time", "IN Odometer (km)", "Break Stop Odometer (km)",
        "OUT Time", "OUT Odometer (km)",
        "Total KM", "Break KM", "Driven KM",
        "Break Time (min)", "Working Time"
    ]

    if any(col not in h for col in required):
        print("⚠️ Missing new rider columns:", required)
        speak_message(MISS_MSG)
        _broadcast_leave_message(MISS_MSG)
        sent_hours.append(str(due_hour))
        _save_slots_state("RIDER", sent_hours)
        return

    c_date   = h["Date"]
    c_rider  = h["Rider"]
    c_in     = h["IN Time"]
    c_inodo  = h["IN Odometer (km)"]
    c_bsodo  = h["Break Stop Odometer (km)"]
    c_out    = h["OUT Time"]
    c_outodo = h["OUT Odometer (km)"]
    c_total  = h["Total KM"]
    c_break  = h["Break KM"]
    c_driven = h["Driven KM"]
    c_btime  = h["Break Time (min)"]
    c_work   = h["Working Time"]

    yesterday_rows = [
        r for r in data
        if len(r) > c_date and r[c_date].strip() == yesterday_str
    ]

    if not yesterday_rows:
        print("⚠️ No rider reading found")
        speak_message(MISS_MSG)
        print("🔊 Voice played for missing rider report")
        _broadcast_leave_message(MISS_MSG)
        sent_hours.append(str(due_hour))
        _save_slots_state("RIDER", sent_hours)
        return

    lines = [f"🚴 *Rider Report — {yesterday_str}*", ""]
    total_driven = 0

    for r in yesterday_rows:
        rider      = r[c_rider].strip()
        in_time    = r[c_in].strip()
        in_odo     = r[c_inodo].strip()
        bs_odo     = r[c_bsodo].strip()
        out_time   = r[c_out].strip()
        out_odo    = r[c_outodo].strip()
        total_km   = r[c_total].strip()
        break_km   = r[c_break].strip()
        driven_km  = r[c_driven].strip()
        break_time = r[c_btime].strip()
        work_time  = r[c_work].strip()

        try:
            total_driven += int(float(driven_km))
        except Exception:
            pass

        lines.append(
            f"• *{rider}*\n"
            f"   🕒 IN: {in_time} | OUT: {out_time}\n"
            f"   📍 IN Odo: {in_odo} km\n"
            f"   📍 Break Stop Odo: {bs_odo} km\n"
            f"   📍 OUT Odo: {out_odo} km\n"
            f"   ➤ Total KM: {total_km}\n"
            f"   ➤ Break KM: {break_km}\n"
            f"   ➤ Driven KM: {driven_km}\n"
            f"   🛑 Break Time: {break_time} min\n"
            f"   🧭 Working Time: {work_time}\n"
        )

    lines.append("━━━━━━━━━━━━━━")
    lines.append(f"🧮 *Total Driven KM:* {total_driven} km")
    lines.append("━━━━━━━━━━━━━━")

    msg = "\n".join(lines)

    for name, phone in RECIPIENTS:
        ok = _send_interakt_text(phone, msg)
        if ok:
            print(f"✔ Rider Report sent to {name} ({phone})")
        else:
            print(f"❌ Failed to send to {name} ({phone})")

    sent_hours.append(str(due_hour))
    _save_slots_state("RIDER", sent_hours)
    print(f"✔ Sent Yesterday Rider Report for slot {due_hour}:00 (current hour = {hr})\n")


# ======================================================
# TASK 8 — LEAVE PROCESS REMINDER TO ALL EMPLOYEES (6PM, 9PM catch-up)
# ======================================================

def run_leave_process_reminder(driver):
    print("🔵 Checking Leave Process Reminder...")

    now = datetime.datetime.now()
    hr  = now.hour

    SLOTS = [18, 21]  # 6 PM, 9 PM

    sent_hours = _load_slots_state("LEAVE_PROCESS")
    due_hour   = _pick_due_hour(SLOTS, sent_hours, hr)

    if due_hour is None:
        print("⏳ No pending Leave Process slot to send right now.")
        return

    print(f"⏰ LEAVE PROCESS: sending for slot {due_hour}:00 (current hour = {hr})")

    message = (
        "अगर आपकी कल की leave सर ने approve कर दी है, तो कृपया ग्रुप में मैसेज डालें, "
        "क्योंकि मैनेजर को अगले दिन दिक्कत आती है।"
    )

    try:
        gc          = gspread.service_account(filename=CREDENTIALS_PATH)
        spreadsheet = gc.open_by_url(LEAVE_SHEET_URL)
        emp_sheet   = spreadsheet.worksheet(EMP_LIST_SHEET)
        rows        = emp_sheet.get_all_values()
        print(f"📄 Loaded employee sheet: {EMP_LIST_SHEET}")
    except Exception as e:
        print(f"❌ Unable to open employee sheet '{EMP_LIST_SHEET}' from LEAVE_SHEET_URL")
        print("Error:", e)
        sent_hours.append(str(due_hour))
        _save_slots_state("LEAVE_PROCESS", sent_hours)
        return

    if len(rows) <= 1:
        print("⚠️ Employee sheet empty — no data to process.")
        sent_hours.append(str(due_hour))
        _save_slots_state("LEAVE_PROCESS", sent_hours)
        return

    header     = rows[0]
    data       = rows[1:]
    header_map = {header[i].strip(): i for i in range(len(header))}

    if "Emp Name" not in header_map or "Phone Number" not in header_map:
        print("⚠️ Required columns missing:", header_map)
        sent_hours.append(str(due_hour))
        _save_slots_state("LEAVE_PROCESS", sent_hours)
        return

    c_name  = header_map["Emp Name"]
    c_phone = header_map["Phone Number"]

    print(f"📨 Sending Leave Process Reminder to {len(data)} employees...")

    for row in data:
        try:
            name  = row[c_name].strip()
            phone = row[c_phone].strip()

            if not phone:
                continue

            ok = _send_interakt_text(phone, message)

            if ok:
                print(f"✔ Sent to {name} ({phone})")
            else:
                print(f"❌ Failed to send to {name} ({phone})")

        except Exception as e:
            print("⚠️ Error processing row:", e)
            continue

    sent_hours.append(str(due_hour))
    _save_slots_state("LEAVE_PROCESS", sent_hours)
    print(f"✔ Leave Process Reminder sent successfully for slot {due_hour}:00\n")


# ======================================================
# HELPER — MAP SP ID → SP NAME FROM SP LIST
# ======================================================

def _map_spid_to_name(spreadsheet):
    """
    Returns {SP_ID: SP_NAME}
    from 'SP List' sheet.
    """
    try:
        ws   = spreadsheet.worksheet("SP List")
        rows = ws.get_all_values()

        if len(rows) <= 1:
            return {}

        header = rows[0]
        h      = {header[i].strip(): i for i in range(len(header))}

        col_id   = h.get("ID") or h.get("SP ID") or h.get("Emp ID")
        col_name = h.get("SP NAME") or h.get("Name") or h.get("SP Name")

        if col_id is None or col_name is None:
            return {}

        mapping = {}
        for r in rows[1:]:
            sid  = r[col_id].strip() if len(r) > col_id else ""
            name = r[col_name].strip() if len(r) > col_name else ""
            if sid and name:
                mapping[sid] = name
        return mapping

    except Exception as e:
        print("⚠️ SP_LIST load error:", e)
        return {}


# ======================================================
# TASK — SEND WEEKOFF REPORT (CLEAN NAME FORMAT, slots with catch-up)
# ======================================================

def run_send_weekoff_report(driver, spreadsheet):
    import datetime as _dt

    print("🔵 Checking Weekoff Report...")

    now = _dt.datetime.now()
    hr  = now.hour

    SLOTS = [12, 14, 17, 21]

    sent_hours = _load_slots_state("WEEKOFF")
    due_hour   = _pick_due_hour(SLOTS, sent_hours, hr)

    if due_hour is None:
        print("⏳ No pending WEEKOFF slot to send right now.")
        return

    print(f"⏰ WEEKOFF: sending for slot {due_hour}:00 (current hour = {hr})")

    try:
        ws = spreadsheet.worksheet("WEEKOFF_SET_CURRENT")
    except Exception as e:
        print("❌ Cannot open WEEKOFF_SET_CURRENT:", e)
        sent_hours.append(str(due_hour))
        _save_slots_state("WEEKOFF", sent_hours)
        return

    rows = ws.get_all_values()
    if len(rows) <= 1:
        print("⚠️ Weekoff sheet empty")
        sent_hours.append(str(due_hour))
        _save_slots_state("WEEKOFF", sent_hours)
        return

    header = rows[0]
    data   = rows[1:]
    h      = {header[i].strip(): i for i in range(len(header))}

    c_id   = h.get("SP NAME", 0)
    c_week = h.get("WEEKOFF DAY", 2)

    sp_map = _map_spid_to_name(spreadsheet)

    ts = now.strftime("%d-%m-%Y %I:%M %p")
    lines = [
        f"📅 *Current Weekoff Set — {ts}*",
        ""
    ]

    for r in data:
        sid  = r[c_id].strip() if len(r) > c_id else ""
        week = r[c_week].strip() if len(r) > c_week else "Not Set"

        if not sid:
            continue

        sp_name = sp_map.get(sid, sid)

        clean = (
            sp_name.replace("SP", "")
                   .replace("(Hub 1.0)", "")
                   .replace("( Hub 1.0)", "")
                   .replace("sp", "")
        ).strip()

        clean = clean.title() or sp_name
        lines.append(f"• *{clean}* — _{week}_")

    if len(lines) == 2:
        lines.append("_No weekoff entries found_")

    msg = "\n".join(lines)

    for name, phone in RECIPIENTS:
        ok = _send_interakt_text(phone, msg)
        if ok:
            print(f"✔ Weekoff Report sent to {name} ({phone})")
        else:
            print(f"❌ Failed to send Weekoff to {name} ({phone})")

    sent_hours.append(str(due_hour))
    _save_slots_state("WEEKOFF", sent_hours)
    print("✔ Weekoff Report Completed\n")


# ======================================================
# TASK — FETCH & SAVE YESTERDAY'S EXPERT FEEDBACK
# ======================================================

def run_yesterday_expert_feedback_report(driver, spreadsheet):
    import datetime as dt_inner
    from gspread.exceptions import WorksheetNotFound as WSNotFound

    print("🔵 Fetching Yesterday Expert Feedback Report...")

    yesterday = dt_inner.date.today() - dt_inner.timedelta(days=1)
    d_str     = yesterday.strftime("%d-%m-%Y")

    url = (
        "https://notiononlinesolutions.tech/order/feedback"
        f"?start={d_str}&end={d_str}&spid=&rating="
    )

    try:
        driver.get(url)
        time.sleep(1.5)

        try:
            WebDriverWait(driver, 8).until(
                EC.presence_of_element_located((By.ID, "datatable"))
            )
        except Exception:
            pass

        table = driver.find_element(By.ID, "datatable")
        soup  = BeautifulSoup(table.get_attribute("outerHTML"), "html.parser")
        rows_html = soup.find_all("tr")[1:]

        if rows_html and "No data available" in rows_html[0].get_text(strip=True):
            print("⚠️ No feedback for yesterday")
            return

        try:
            ws = spreadsheet.worksheet("ExpertFeedback")
        except WSNotFound:
            ws = spreadsheet.add_worksheet("ExpertFeedback", rows=5000, cols=25)
            ws.append_row([
                "Date", "Order ID", "SP Name", "Rating",
                "Hygiene Rating", "Feedback", "Comments",
                "Manager discussion notes with Expert"
            ])

        existing      = ws.get_all_values()
        existing_keys = set()
        for row in existing[1:]:
            if len(row) >= 2 and row[0] and row[1]:
                existing_keys.add((row[0].strip(), row[1].strip()))

        new_rows = []

        for r in rows_html:
            tds = r.find_all("td")
            if len(tds) < 4:
                continue

            order_id = ""
            try:
                first_td = tds[0]
                a        = first_td.find("a")
                if a and a.get_text(strip=True):
                    order_id = a.get_text(strip=True).strip()
                else:
                    order_id = first_td.get_text(strip=True).split()[0]
            except Exception:
                continue

            sp_name  = tds[3].get_text(strip=True) if len(tds) > 3 else ""
            rating   = tds[4].get_text(strip=True) if len(tds) > 4 else ""
            hygiene  = tds[5].get_text(strip=True) if len(tds) > 5 else ""
            feedback = tds[6].get_text(strip=True) if len(tds) > 6 else ""
            comments = tds[7].get_text(strip=True) if len(tds) > 7 else ""

            if not order_id:
                continue

            key = (d_str, order_id)
            if key in existing_keys:
                continue

            new_rows.append([
                d_str, order_id, sp_name,
                rating, hygiene, feedback, comments,
                ""  # Manager notes
            ])

        if new_rows:
            ws.append_rows(new_rows)
            print(f"✅ Saved {len(new_rows)} new entries")
        else:
            print("⚠️ No new entries")

        try:
            ws.sort((1, "des"))
        except Exception:
            pass

        try:
            ws.format("A1:H1", {"textFormat": {"bold": True}})
        except Exception:
            pass

        print("✅ Expert Feedback Fetch Complete")

    except Exception as e:
        print("❌ Feedback Fetch ERROR:", e)


# ======================================================
# TASK — SEND YESTERDAY FEEDBACK REPORT VIA WHATSAPP
# ======================================================

def run_send_yesterday_expert_feedback_whatsapp(driver, spreadsheet):
    import datetime as dt_inner

    print("🔵 Preparing WhatsApp Expert Feedback Report...")

    if _has_run_today("FEEDBACK"):
        print("⏳ Expert Feedback already sent today — skipping")
        return

    try:
        ws = spreadsheet.worksheet("ExpertFeedback")
    except Exception:
        print("❌ Error: ExpertFeedback sheet missing")
        return

    rows = ws.get_all_values()
    if len(rows) <= 1:
        print("⚠️ ExpertFeedback sheet empty")
        return

    header = rows[0]
    data   = rows[1:]
    h      = {header[i].strip(): i for i in range(len(header))}

    required = [
        "Date", "Order ID", "SP Name", "Rating",
        "Hygiene Rating", "Feedback", "Comments",
        "Manager discussion notes with Expert"
    ]
    if any(col not in h for col in required):
        print("⚠️ Missing required columns in ExpertFeedback")
        return

    c_date = h["Date"]
    c_oid  = h["Order ID"]
    c_sp   = h["SP Name"]
    c_rat  = h["Rating"]
    c_hyg  = h["Hygiene Rating"]
    c_fb   = h["Feedback"]
    c_cm   = h["Comments"]
    c_mgr  = h["Manager discussion notes with Expert"]

    yesterday = dt_inner.date.today() - dt_inner.timedelta(days=1)
    y_str     = yesterday.strftime("%d-%m-%Y")

    y_rows = [r for r in data if r[c_date].strip() == y_str]

    if not y_rows:
        print("ℹ️ No feedback for yesterday")
        return

    lines = [f"⭐ *Expert Feedback — {y_str}*", ""]

    for r in y_rows:
        order_id = r[c_oid].strip()
        sp_name  = r[c_sp].strip()
        rat_raw  = r[c_rat].strip() or "-"
        hyg      = r[c_hyg].strip() or "-"
        fb       = r[c_fb].strip()
        cm       = r[c_cm].strip()
        mgr_note = r[c_mgr].strip()

        try:
            rat = int(float(rat_raw))
        except Exception:
            rat = rat_raw

        name_block = f"{order_id} — {sp_name}"

        if isinstance(rat, int) and rat < 4:
            name_txt = f"🟥 *{name_block}*"
        else:
            name_txt = f"*{name_block}*"

        block = f"• {name_txt} — ⭐{rat_raw}, 🧼 {hyg}"

        if fb:
            if isinstance(rat, int) and rat < 4:
                block += f"\n   🟥🔥 *_{fb}_* 🔥🟥"
            else:
                block += f"\n   _{fb}_"

        if cm:
            block += f"\n   💬 {cm}"

        if isinstance(rat, int) and rat < 4:
            if mgr_note:
                block += f"\n   📝 *Manager Notes:* {mgr_note}"
            else:
                block += "\n   📝 _मैनेजर को कारण पर चर्चा करके यह अपडेट करना है कि रेटिंग कम क्यों आई।_"

        lines.append(block)
        lines.append("")

    msg = "\n".join(lines).strip()

    recipients = [
        ("Shraddha", "7406011400"),
        ("Vikas",    "7406611400"),
        ("Kukum",  "8305838835"),
        ("Nayak",    "7828564967"),
        ("Manager",  "9770159033"),
    ]

    success = False
    for name, phone in recipients:
        ok = _send_interakt_text(phone, msg)
        if ok:
            print(f"✔ Feedback Report sent to {name} ({phone})")
            success = True
        else:
            print(f"❌ Failed sending to {name} ({phone})")

    if success:
        _mark_run_today("FEEDBACK")
        print("✅ Expert Feedback WhatsApp Report sent!")


def _js_set_input_value(driver, element, value):
    driver.execute_script("""
        arguments[0].value = arguments[1];
        arguments[0].dispatchEvent(new Event('change', { bubbles: true }));
        arguments[0].dispatchEvent(new Event('input', { bubbles: true }));
    """, element, value)


def _js_click(driver, element):
    driver.execute_script("arguments[0].scrollIntoView({block:'center'});", element)
    driver.execute_script("arguments[0].click();", element)


def _select_all_service_providers(driver):
    """
    Robust SumoSelect ALL selection (JS-based)
    """
    # Open dropdown
    sp_box = WebDriverWait(driver, 15).until(
        EC.presence_of_element_located((By.CSS_SELECTOR, ".sumo_spIds"))
    )
    _js_click(driver, sp_box)

    # Click Select All
    select_all = WebDriverWait(driver, 15).until(
        EC.presence_of_element_located(
            (By.CSS_SELECTOR, ".sumo_spIds .select-all")
        )
    )
    _js_click(driver, select_all)

    # Click OK
    ok_btn = WebDriverWait(driver, 10).until(
        EC.presence_of_element_located(
            (By.CSS_SELECTOR, ".sumo_spIds .btnOk")
        )
    )
    _js_click(driver, ok_btn)


def _close_datepicker_if_open(driver):
    """
    Force close jQuery UI datepicker if it is open
    """
    driver.execute_script("""
        if (window.jQuery && jQuery.datepicker) {
            jQuery.datepicker._hideDatepicker();
        }
        document.body.click();
    """)


def write_franchise_rows_to_sheet(all_rows, sheet_url, sheet_name):
    import traceback

    try:
        scope = [
            "https://spreadsheets.google.com/feeds",
            "https://www.googleapis.com/auth/drive",
            "https://www.googleapis.com/auth/spreadsheets",
        ]
        creds = ServiceAccountCredentials.from_json_keyfile_name(
            CREDENTIALS_PATH, scope
        )
        gc = gspread.authorize(creds)
        ss = gc.open_by_url(sheet_url)

        try:
            ws = ss.worksheet(sheet_name)
        except WorksheetNotFound:
            ws = ss.add_worksheet(sheet_name, rows=5000, cols=30)

        # normalize columns
        max_cols = max(len(r) for r in all_rows)
        safe_rows = [
            r + [""] * (max_cols - len(r))
            for r in all_rows
        ]

        # header-only case
        if len(safe_rows) == 2 and not any(safe_rows[1]):
            print("⚠️ Only header present — writing header only")
            safe_rows = [safe_rows[0]]

        ws.clear()
        ws.append_rows(safe_rows, value_input_option="RAW")

        try:
            ws.freeze(rows=1)
            ws.format("1:1", {"textFormat": {"bold": True}})
            ws.set_basic_filter()
        except Exception:
            pass

    except PermissionError:
        print("❌ Google Sheet permission denied.")
        print("➡️ Share the sheet with the service account email.")
        raise
    except Exception as e:
        print("❌ Google Sheet WRITE FAILED:", repr(e))
        print(traceback.format_exc())
        raise


def _set_date(driver, field_name, value):
    driver.execute_script(
        """
        const el = document.querySelector(`input[name='${arguments[0]}']`);
        if (!el) return;
        el.value = arguments[1];
        el.dispatchEvent(new Event('change', { bubbles: true }));
        el.dispatchEvent(new Event('input', { bubbles: true }));
        """,
        field_name,
        value
    )
    time.sleep(0.3)

from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
import time

def _sumoselect_select_all(driver, timeout=15):
    wait = WebDriverWait(driver, timeout)

    # 1️⃣ Ensure SumoSelect dropdown is opened
    sumo = wait.until(EC.element_to_be_clickable((
        By.CSS_SELECTOR, ".SumoSelect"
    )))
    driver.execute_script("arguments[0].scrollIntoView({block:'center'});", sumo)
    time.sleep(0.2)
    sumo.click()

    # 2️⃣ Wait for "Select All" to be visible inside opened dropdown
    select_all = wait.until(EC.element_to_be_clickable((
        By.CSS_SELECTOR, ".SumoSelect.open p.select-all"
    )))

    # 3️⃣ Click only if not already selected
    driver.execute_script("""
        const el = arguments[0];
        if (!el.classList.contains("selected")) {
            el.scrollIntoView({block:'center'});
            el.click();
        }
    """, select_all)

    time.sleep(0.5)


def _write_franchise_sheet(rows):
    scope = [
        "https://spreadsheets.google.com/feeds",
        "https://www.googleapis.com/auth/drive",
    ]
    creds = ServiceAccountCredentials.from_json_keyfile_name(CREDENTIALS_PATH, scope)
    gc = gspread.authorize(creds)

    ss = gc.open_by_url(FRANCHISE_TARGET_SHEET_URL)

    try:
        ws = ss.worksheet(FRANCHISE_SHEET_NAME)
    except WorksheetNotFound:
        ws = ss.add_worksheet(FRANCHISE_SHEET_NAME, rows=5000, cols=10)

    headers = [
        "Sp Name", "Date", "Order Id",
        "Customer Name", "Product",
        "Product Quantity", "Remark"
    ]

    if ws.row_values(1) != headers:
        ws.clear()
        ws.append_row(headers)

    # 🔐 Load existing Order IDs
    existing_order_ids = _load_existing_order_ids(ws)

    # 🔐 Deduplicate by Order Id
    unique_rows = _dedupe_by_order_id(rows, existing_order_ids)

    if unique_rows:
        ws.append_rows(unique_rows, value_input_option="RAW")
        print(f"➕ New orders inserted: {len(set(r[2] for r in unique_rows))}")
    else:
        print("ℹ️ No new orders to insert")



def _submit_form(driver):
    driver.execute_script("""
        const btn = document.querySelector("button[type='submit']");
        if (!btn) return;
        btn.scrollIntoView({block:'center'});
        btn.click();
    """)
    
def _wait_for_table(driver, timeout=15):
    WebDriverWait(driver, timeout).until(
        lambda d: d.execute_script("""
            if (!window.jQuery) return false;
            if (!jQuery.fn.DataTable) return false;
            const tbl = jQuery('#datatable').DataTable();
            return tbl.settings()[0]._iRecordsTotal >= 0;
        """)
    )
    time.sleep(0.5)

def _set_datatable_max_length(driver):
    driver.execute_script("""
        if (!window.jQuery || !jQuery.fn.DataTable) return;
        const table = jQuery('#datatable').DataTable();
        table.page.len(150).draw(false);
    """)
    time.sleep(0.5)

def _read_all_datatable_rows(driver):
    return driver.execute_script("""
        if (!window.jQuery || !jQuery.fn.DataTable) return [];
        const table = jQuery('#datatable').DataTable();
        return table
            .rows({ search: 'applied' })
            .data()
            .toArray();
    """) or []

def _normalize_franchise_rows(dt_rows):
    clean_rows = []

    for row in dt_rows:
        if not row or len(row) < 7:
            continue

        cleaned = [
            BeautifulSoup(str(cell), "html.parser").get_text(strip=True)
            for cell in row[:7]
        ]

        if "No data available" in cleaned[0]:
            continue

        clean_rows.append(cleaned)

    return clean_rows


def _load_existing_order_ids(ws):
    """
    Returns a set of Order Ids already present in sheet
    """
    rows = ws.get_all_values()
    if len(rows) <= 1:
        return set()

    header = rows[0]
    h = {header[i]: i for i in range(len(header))}

    if "Order Id" not in h:
        return set()

    c_order = h["Order Id"]

    order_ids = set()
    for r in rows[1:]:
        try:
            oid = r[c_order].strip()
            if oid:
                order_ids.add(oid)
        except Exception:
            continue

    return order_ids


def _dedupe_by_order_id(rows, existing_order_ids):
    """
    Drops all rows whose Order Id already exists
    """
    unique = []

    for r in rows:
        try:
            order_id = r[2].strip()  # Order Id column
            if order_id in existing_order_ids:
                continue
            unique.append(r)
        except Exception:
            continue

    return unique


def run_franchise_product_assigned_report(driver):
    print("🔵 Running Franchise Product Assigned Report...")

    yesterday = (datetime.date.today() - datetime.timedelta(days=1)).strftime("%d-%m-%Y")
    driver.get(FRANCHISE_REPORT_URL)

    _set_date(driver, "startat", yesterday)
    _set_date(driver, "endat", yesterday)

    _sumoselect_select_all(driver)
    _submit_form(driver)
    _wait_for_table(driver)

    _set_datatable_max_length(driver)

    dt_rows = _read_all_datatable_rows(driver)
    all_rows = _normalize_franchise_rows(dt_rows)

    print(f"📊 Rows fetched from UI: {len(all_rows)}")

    _write_franchise_sheet(all_rows)

    print("✅ Franchise Product Assigned Report completed safely")





def safe_run_franchise_product_assigned_report(driver):
    try:
        run_franchise_product_assigned_report(driver)
    except Exception as e:
        print("❌ Franchise Product Assigned FAILED:", repr(e))
        print(traceback.format_exc())
    except BaseException as e:
        print("🔥 Franchise Product Assigned FATAL EXIT:", repr(e))
        print(traceback.format_exc())







def format_expert_feedback_sheet(spreadsheet):
    print("🎨 Formatting ExpertFeedback sheet...")

    try:
        ws = spreadsheet.worksheet("ExpertFeedback")
    except Exception:
        print("⚠️ Cannot open ExpertFeedback sheet")
        return

    try:
        ws.freeze(rows=1)
    except Exception:
        pass

    try:
        ws.format("A1:H1", {
            "textFormat": {"bold": True},
            "horizontalAlignment": "CENTER",
            "backgroundColor": {"red": 0.9, "green": 0.9, "blue": 0.9}
        })
    except Exception:
        pass

    try:
        ws.format("F:H", {"wrapStrategy": "WRAP"})
    except Exception:
        pass

    try:
        ws.resize(1)
    except Exception:
        pass

    try:
        ws.set_basic_filter()
    except Exception:
        pass

    try:
        rule = {
            "booleanRule": {
                "condition": {
                    "type": "NUMBER_LESS",
                    "values": [{"userEnteredValue": "4"}]
                },
                "format": {
                    "backgroundColor": {"red": 1, "green": 0.8, "blue": 0.8},
                    "textFormat": {
                        "foregroundColor": {"red": 1, "green": 0, "blue": 0}
                    }
                }
            },
            "range": {
                "sheetId": ws.id,
                "startRowIndex": 1,
                "startColumnIndex": 3,
                "endColumnIndex": 4
            }
        }
        ws.add_conditional_formatting(rule)
    except Exception as e:
        print("⚠️ Conditional formatting failed:", e)

    print("✅ ExpertFeedback sheet formatted!")


# ======================================================
# MASTER RUNNER
# ======================================================

def run_all(driver):
    print("\n==============================")
    print("   RUNNING OTHER TASKS")
    print("==============================\n")

    spreadsheet = _open_spreadsheet()

    # 🔐 Ensure State sheet has all base columns BEFORE running any task
    _ensure_state_base_columns()

    safe_run_franchise_product_assigned_report(driver)
    run_addon_report(driver, spreadsheet)
    run_weekoff(driver, spreadsheet)
    run_performance(driver, spreadsheet)

    run_send_daily_addon_report(driver, spreadsheet)
    run_yesterday_leave_report(driver)
    run_today_leave_report(driver)
    run_yesterday_rider_report(driver)
    run_leave_process_reminder(driver)
    run_send_weekoff_report(driver, spreadsheet)

    print("\n🎉 ALL OTHER TASKS FINISHED CLEANLY")




# ============================================================
# MAIN ENTRY FUNCTION
# ============================================================

def fetch_top_services_last_7_days_and_save_requests(
    auth_cookies,
    spreadsheet,
    hub_id="94"
):
    today = datetime.date.today()
    start_date = today - datetime.timedelta(days=6)

    start_str = start_date.strftime("%d-%m-%Y")
    end_str   = today.strftime("%d-%m-%Y")

    url = (
        "https://www.notiononlinesolutions.tech/report/top-services"
        f"?startDate={start_str}"
        f"&endDate={end_str}"
        f"&hubIds={hub_id}"
        "&_hubIds=1"
    )

    print(f"📊 Top Services (REQUESTS) → {start_str} to {end_str}")

    resp = requests.get(url, cookies=auth_cookies)
    resp.raise_for_status()

    soup = BeautifulSoup(resp.text, "html.parser")
    rows = soup.select("#datatable tbody tr")

    all_rows = []
    seen = set()

    for r in rows:
        cols = [td.get_text(strip=True) for td in r.find_all("td")]
        if len(cols) != 7:
            continue

        try:
            service = cols[3]
            minutes = int(cols[5] or 0)
            price   = int(cols[6] or 0)
            count   = int(cols[4] or 0)
        except Exception:
            continue

        key = (service, price, minutes)
        if key in seen:
            continue
        seen.add(key)

        all_rows.append({
            "category":    cols[0],
            "subcategory": cols[1],
            "heading":     cols[2],
            "service":     service,
            "count":       count,
            "minutes":     minutes,
            "price":       price,
        })

    print(f"✅ Top services collected safely: {len(all_rows)}")

    if all_rows:
                clean_rows = dedupe_top_services(all_rows)
                write_top_services_to_sheet(spreadsheet, clean_rows)

    return all_rows



# ============================================================
# GOOGLE SHEET HELPERS
# ============================================================

def ensure_top_services_sheet():
    SHEET_NAME = "TOP_SERVICES"
    headers = [
        "Category",
        "SubCategory",
        "Heading",
        "Service Name",
        "Number",
        "Minutes",
        "Price",
    ]

    # 🔄 Delete sheet if already present
    try:
        ws_existing = sh.worksheet(SHEET_NAME)
        sh.del_worksheet(ws_existing)
        print("🗑️ Deleted existing sheet → TOP_SERVICES")
    except WorksheetNotFound:
        pass  # Sheet does not exist, nothing to delete

    # 📄 Recreate sheet fresh
    ws = sh.add_worksheet(
        title=SHEET_NAME,
        rows=2000,
        cols=len(headers)
    )

    _with_backoff(ws.update, "A1", [headers])
    ws.freeze(rows=1)
    ws.format("1:1", {"textFormat": {"bold": True}})

    print("📄 Recreated sheet → TOP_SERVICES")

    return ws



def write_top_services_to_sheet(spreadsheet, rows):
    if not rows:
        print("⚠️ No rows to write to TOP_SERVICES")
        return

    try:
        ws = spreadsheet.worksheet("TOP_SERVICES")
    except WorksheetNotFound:
        ws = spreadsheet.add_worksheet("TOP_SERVICES", rows=2000, cols=7)
        ws.append_row([
            "Category",
            "SubCategory",
            "Heading",
            "Service Name",
            "Number",
            "Minutes",
            "Price",
        ])
        ws.freeze(rows=1)

    # Clear old data
    ws.batch_clear(["A2:G"])

    values = [
        [
            r["category"],
            r["subcategory"],
            r["heading"],
            r["service"],
            r["count"],
            r["minutes"],
            r["price"],
        ]
        for r in rows
    ]

    ws.update("A2", values)

    print(f"✅ TOP_SERVICES sheet updated → {len(values)} rows")

def dedupe_top_services(rows):
    """
    Deduplicate TOP_SERVICES rows.
    Key = (service, minutes, price)
    Rule = keep highest Number
    """
    deduped = {}

    for r in rows:
        key = (
            r["service"].strip().lower(),
            int(r["minutes"]),
            int(r["price"]),
        )

        if key not in deduped:
            deduped[key] = r
        else:
            # keep row with higher count
            if r["count"] > deduped[key]["count"]:
                deduped[key] = r

    return list(deduped.values())
