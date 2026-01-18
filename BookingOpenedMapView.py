#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Booking Automation — Final Cleaned & Optimized (Voice ON)

Highlights:
- Stable booking count pulse (original working logic)
- Quota-safe: one sheet-read per worker; batched writes
- Job detail refresh ONLY if Order Status == START JOB
- Pickup ETA + alerts ONLY while START JOB; stop forever after Stop Job At
- Pickup ETA = expected_finish - 40 minutes
- OTP reminders (before/after) retained
- Daily SP summaries (10–11 PM IST)
- Idempotent sends via sheet flags (no in-memory guards)

Python 3.9.x
"""


import other_tasks_map
from other_tasks_map import fetch_top_services_last_7_days_and_save_requests
import time
import random
from googleapiclient.errors import HttpError
import threading
import json
import queue
import os   
import re
import time
import base64
import shutil
import subprocess
import random
from datetime import datetime, date, time as dt_time, timedelta
from webdriver_manager.chrome import ChromeDriverManager
import pytz
import requests
from bs4 import BeautifulSoup

import gspread
from gspread.exceptions import APIError, WorksheetNotFound
from oauth2client.service_account import ServiceAccountCredentials

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC

from dateutil import parser as dtparser


# Recipients reused across different reports
RECIPIENTS = [
    ("Shraddha",  "7406011400"),
    ("Vikas",     "7406611400"),
    ("Manager",   "9770159033"),
    ("Radha", "9302726337")

]

import requests
import json



# ===============================
# CONFIG
# ===============================
IST = pytz.timezone("Asia/Kolkata")
TASK_QUEUE = queue.Queue()
URL_LOGIN = "https://notiononlinesolutions.tech/login"
FRANCHISE_HUB_ID = os.getenv("FRANCHISE_HUB_ID", "94")
TODAY_BOOKINGS_URL = f"https://notiononlinesolutions.tech/order/hub/{FRANCHISE_HUB_ID}/1"
TOMORROW_BOOKINGS_URL = f"https://notiononlinesolutions.tech/order/hub/{FRANCHISE_HUB_ID}/2"
ORDER_DETAIL_URL = "https://notiononlinesolutions.tech/order/{oid}"
TODAY_BOOKING_URL = "https://notiononlinesolutions.tech/dashboard/today"
CUSTOMER_BILL_PAGINATION_XPATH = '//select[@name="datatable_length"]'
BOOKING_COUNT_XPATH = f'//a[@href="/order/hub/{FRANCHISE_HUB_ID}/1?categoryId="]'
DELAY_REPORT_STATE_KEY = "DELAY_REPORT_DATE"

GOOGLE_GEOCODE_API_KEY = "AIzaSyCHcVQui7jGIJbDOusu0Z46NnFDTCUuyvg"

GOOGLE_GEOCODE_DAILY_LIMIT = int(os.getenv("GOOGLE_GEOCODE_DAILY_LIMIT", "200"))
GEOCODE_CACHE = {}
GEOCODE_TODAY_COUNT = 0
GEOCODE_TODAY_DATE = datetime.now().date()

# ------------------------------------
# Distance Matrix persistent cache
# ------------------------------------
DIST_MATRIX_CACHE_FILE = "distance_cache.json"
DIST_MATRIX_CACHE = {}

# 🔥 FIX: Add missing path variable for load/save functions
DISTANCE_CACHE_PATH = DIST_MATRIX_CACHE_FILE

# Also initialize the in-memory dict
DISTANCE_CACHE = {}

MAP_BROWSER = None
MAP_TAB_OPENED = False

USERNAME = os.getenv("NOS_USERNAME", "7406611400")
PASSWORD = os.getenv("NOS_PASSWORD", "Indore@2035")
OTP_ENV  = os.getenv("NOTION_OTP", None)

GOOGLE_SHEET_ID = os.getenv("GOOGLE_SHEET_ID", "1pMvCWaGlP4NQPZfbVPiQVFTJoViozPYPpARQ_VGdLVo")
JSON_KEY_PATH   = os.getenv("GOOGLE_JSON_KEY_PATH", "yesmadamndore-029caf40a32b.json")
CUSTOMER_SHEET_NAME = "Sheet1"

# Loop cadence (quota-safe defaults)
REFRESH_INTERVAL           = int(os.getenv("REFRESH_INTERVAL", "180"))   # main loop sleep
JOB_UPDATE_INTERVAL        = int(os.getenv("JOB_UPDATE_INTERVAL", "600"))  # 10 min
PICKUP_ETA_UPDATE_INTERVAL = int(os.getenv("PICKUP_ETA_UPDATE_INTERVAL", "420"))  # 10 min
ALERT_CHECK_INTERVAL       = int(os.getenv("ALERT_CHECK_INTERVAL", "420"))  # 5 min

# TL Office Coordinates (Google verified)
# Correct Yes Madam TL Hub (Nipania / Bombay Hospital zone)
TL_LATLNG = "22.7569694,75.9018373"   # Correct TL Hub (Bombay Hospital Road)

# AN Office Coordinates (Google verified)
# Correct Annapurna Mandir Road location (NOT the old wrong 75.7308)
AN_LATLNG = "22.689307,75.857139"     # Correct AN Hub



# Interakt (WhatsApp)
INTERAKT_API_KEY          = os.getenv("INTERAKT_API_KEY", "hXanaXFAqNGSP8-3HiENI46y0AP4wb26niPGsp6s0cs")
INTERAKT_URL              = "https://api.interakt.ai/v1/public/message/"
INTERAKT_PLAIN_URL        = "https://api.interakt.ai/v1/messages/"
                
INTERAKT_COUNTRY_CODE     = "+91"
INTERAKT_TEMPLATE         = "booking_confirmation_v4"
INTERAKT_SP_PREBOOK_TMPL  = "sp_one_hour_pre_booking_notification_v1"  # keep as in your code
INTERAKT_SP_FINISH_TMPL   = "sp_finish_eta_alert_v1"                    # Hindi template
INTERAKT_SP_DAILY_TMPL    = "sp_daily_summary_v3"
INTERAKT_SP_OTP_REM_10MIN = "sp_otp_start_reminder_10min"
MANAGER_PHONES = os.getenv("MANAGER_PHONES", "9770159033")
MANAGER_PHONES = [p.strip() for p in MANAGER_PHONES.split(",") if p.strip()]
INTERAKT_CX_STOPJOB_FEEDBACK_TMPL = "payment"


# SP pre-booking windows (seconds)
SP_PREBOOK_1HR_WINDOW   = (50*60, 65*60)
SP_PREBOOK_30MIN_WINDOW = (25*60, 35*60)
SP_PREBOOK_10MIN_WINDOW = (8*60, 12*60)

# Send gaps
SP_SEND_GAP_SECONDS       = int(os.getenv("SP_SEND_GAP_SECONDS", "5"))
CUSTOMER_SEND_GAP_SECONDS = int(os.getenv("CUSTOMER_SEND_GAP_SECONDS", "5"))

# ===============================
# GOOGLE SHEETS AUTH + BACKOFF
# ===============================

DISTANCE_CACHE_PATH = "distance_cache.json"
DISTANCE_CACHE = {}

def _load_distance_cache():
    global DISTANCE_CACHE
    try:
        if os.path.exists(DISTANCE_CACHE_PATH):
            with open(DISTANCE_CACHE_PATH, "r", encoding="utf-8") as f:
                DISTANCE_CACHE = json.load(f)
        else:
            DISTANCE_CACHE = {}
    except Exception:
        DISTANCE_CACHE = {}
        
def _save_distance_cache():
    try:
        with open(DISTANCE_CACHE_PATH, "w", encoding="utf-8") as f:
            json.dump(DISTANCE_CACHE, f, indent=2, ensure_ascii=False)
    except Exception:
        pass



# Call once at startup (module import time)
_load_distance_cache()




def get_last_rollover_date_from_sheet():
    try:
        state = sh.worksheet("State")
    except WorksheetNotFound:
        state = sh.add_worksheet("State", rows=10, cols=5)
        state.update("A1", [["LastSeenOrderIds"]])
        state.update("B1", [["LastRolloverDate"]])
        return None

    try:
        val = state.acell("B2").value
        return val.strip() if val else None
    except:
        return None


def set_last_rollover_date_in_sheet(date_str):
    """
    Stores the last rollover date into the Config sheet.
    Expected cell: B2 (change if needed)
    """
    try:
        ws = sh.worksheet("State")   # Your config sheet
    except Exception:
        raise Exception("Config sheet not found!")

    try:
        ws.update_acell("B2", date_str)
        print(f"📝 Last rollover date updated → {date_str}")
    except Exception as e:
        print(f"⚠️ Failed to update last rollover date: {e}")


# def rollover_day_change():
#     today_str = datetime.now(IST).strftime("%Y-%m-%d")
#     last_roll = get_last_rollover_date_from_sheet()
#     sh = client.open_by_key(GOOGLE_SHEET_ID)


#     # 1️⃣ First-time initialization
#     if not last_roll or not last_roll.strip():
#         print("⏳ First run detected → Initializing rollover date (no rollover today)")
#         set_last_rollover_date_in_sheet(today_str)
#         return

#     # 2️⃣ Date same → Skip
#     if last_roll == today_str:
#         return

#     # 3️⃣ Date changed → Real rollover
#     print(f"🔄 Rollover Triggered — Date changed from {last_roll} → {today_str}")

#     # --- Backup ---
#     booking_date = get_booking_date_from_today_bookings()
#     backup_name = f"Booking-{booking_date}"
#     print(f"📄 Creating backup sheet → {backup_name}")

#     try:
#         duplicate_sheet("TodayBookings", backup_name)
#     except Exception as e:
#         print(f"⚠️ Failed to create backup sheet {backup_name}: {e}")

#     # --- Execute rollover ---
#     print("\n==============================")
#     print("📅 MIDNIGHT ROLLOVER STARTED")
#     print("==============================")

#     #  ⭐ CLEAR PAYMENT MESSAGES SHEET HERE ⭐
#     try:
#         clear_payment_messages_sheet_except_header(sh)
#         print("🧹 Cleared PaymentMessages for new day.")
#     except Exception as e:
#         print(f"⚠️ Failed cleaning PaymentMessages: {e}")

#     # Continue normal rollover
#     rollover_today_bookings()

#     # --- Save new date ---
#     set_last_rollover_date_in_sheet(today_str)

def rollover_day_change():
    today_str = datetime.now(IST).strftime("%Y-%m-%d")
    last_roll = get_last_rollover_date_from_sheet()
    sh = client.open_by_key(GOOGLE_SHEET_ID)

    # ==================================================
    # 1️⃣ First run → initialize only
    # ==================================================
    if not last_roll or not last_roll.strip():
        print("⏳ First run detected → initializing rollover date (no rollover)")
        set_last_rollover_date_in_sheet(today_str)
        return

    # ==================================================
    # 2️⃣ Same day → nothing to do
    # ==================================================
    if last_roll == today_str:
        return

    # ==================================================
    # 3️⃣ Date changed → REAL rollover
    # ==================================================
    print(f"🔄 Rollover triggered → {last_roll} → {today_str}")

    print("\n==============================")
    print("📅 MIDNIGHT ROLLOVER STARTED")
    print("==============================")

    # --------------------------------------------------
    # Backup TodayBookings
    # --------------------------------------------------
    try:
        booking_date = get_booking_date_from_today_bookings()
        backup_name = f"Booking-{booking_date}"
        print(f"📄 Creating backup sheet → {backup_name}")
        duplicate_sheet("TodayBookings", backup_name)
    except Exception as e:
        print(f"⚠️ Backup failed: {e}")

    # --------------------------------------------------
    # Clear PaymentMessages (new day)
    # --------------------------------------------------
    try:
        clear_payment_messages_sheet_except_header(sh)
        print("🧹 Cleared PaymentMessages for new day")
    except Exception as e:
        print(f"⚠️ Failed clearing PaymentMessages: {e}")

    # --------------------------------------------------
    # Execute core rollover logic
    # --------------------------------------------------
    rollover_today_bookings()

    # --------------------------------------------------
    # 🔒 RESTORE WA FLAGS FROM LEDGER (CRITICAL)
    # --------------------------------------------------
    try:
        tomorrow_ws = sh.worksheet("TommorwBookings")
        restore_customer_wa_flags(tomorrow_ws)
    except Exception as e:
        print(f"⚠️ Failed restoring WA flags: {e}")

    # --------------------------------------------------
    # Persist new rollover date
    # --------------------------------------------------
    set_last_rollover_date_in_sheet(today_str)

    print("✅ MIDNIGHT ROLLOVER COMPLETED")



def get_booking_date_from_today_bookings():
    """
    Reads Booking Date from TodayBookings sheet.
    Returns normalized format like → 26-Nov-2025
    """
    ws = sh.worksheet("TodayBookings")
    values = ws.get_all_values()

    header = values[0]
    try:
        col_idx = header.index("Booking Date")
    except ValueError:
        raise Exception("Column 'Booking Date' not found in TodayBookings")

    from datetime import datetime

    for row in values[1:]:
        if len(row) <= col_idx:
            continue

        raw = row[col_idx].strip()
        if not raw:
            continue

        # Support both 26/11/2025 and 26-Nov-2025
        for fmt in ("%d/%m/%Y", "%d-%b-%Y"):
            try:
                dt = datetime.strptime(raw, fmt)
                return dt.strftime("%d-%b-%Y")
            except:
                pass

        raise Exception(f"Invalid Booking Date format: {raw}")

    raise Exception("No Booking Date found")

def duplicate_sheet(source_sheet_name, new_sheet_name):
    """
    Duplicate a sheet inside the same Google Spreadsheet.
    Works reliably for gspread.
    """
    try:
        source_ws = sh.worksheet(source_sheet_name)
    except Exception:
        raise Exception(f"Source sheet '{source_sheet_name}' not found!")

    source_id = source_ws.id

    try:
        sh.duplicate_sheet(
            source_sheet_id=source_id,
            new_sheet_name=new_sheet_name
        )
        print(f"📄 Backup sheet created → {new_sheet_name}")
    except Exception as e:
        raise Exception(f"Failed to duplicate sheet: {e}")


def _with_backoff(fn, *args, **kwargs):
    delay = 1.0
    for _ in range(6):
        try:
            return fn(*args, **kwargs)
        except APIError as e:
            msg = str(e)
            if "429" in msg or "quota" in msg.lower():
                time.sleep(delay + random.random())
                delay *= 2
            else:
                raise
    return fn(*args, **kwargs)

scope = [
    "https://spreadsheets.google.com/feeds",
    "https://www.googleapis.com/auth/drive",
    "https://www.googleapis.com/auth/spreadsheets",
]
creds  = ServiceAccountCredentials.from_json_keyfile_name(JSON_KEY_PATH, scope)
client = gspread.authorize(creds)
sh = client.open_by_key(GOOGLE_SHEET_ID)
# ---------------------------------------------------------
# WEEKOFF SHEET (SEPARATE GOOGLE SHEET)
# ---------------------------------------------------------
WEEKOFF_SHEET_ID = "16f-QarUEooXiwymMYAQxqHfulaNExidL47dasKjiP1s"
sh_weekoff = client.open_by_key(WEEKOFF_SHEET_ID)


# ===============================
# MAC POWER & VOICE
# ===============================
def start_caffeinate():
    try:
        return subprocess.Popen(["caffeinate", "-i"])
    except Exception:
        return None

def stop_caffeinate(proc):
    try:
        if proc:
            proc.terminate()
    except Exception:
        pass

def speak_message(msg: str):
    try:
        v = int(os.popen('osascript -e "output volume of (get volume settings)"').read().strip() or 50)
        os.system('osascript -e "set volume output volume 100"')
        os.system(f'say "{msg}"')
        os.system(f'osascript -e "set volume output volume {v}"')
    except Exception:
        pass

def clean_sp_name(name: str) -> str:
    if not name:
        return ""
    s = str(name)
    s = re.sub(r"\([^)]*\)", " ", s)
    s = re.sub(r"\bS\.?P\.?\b", " ", s, flags=re.I)
    s = re.sub(r"\bsp\b", " ", s, flags=re.I)
    s = re.sub(r"\s+", " ", s).strip()
    return s.title()

def voice_free_time_alert(sp_name_raw: str, expected_finish_dt: datetime):
    sp_name = clean_sp_name(sp_name_raw)
    free_time = expected_finish_dt.strftime("%I:%M %p")
    msg = f"नायक, {sp_name} का काम {free_time} तक खत्म हो जाएगा। Pickup Rider भेजने की तैयारी करो।"
    speak_message(msg)

# ===============================
# SHEET STRUCTURE
# ===============================
TB_HEADERS = [
    "Order Id","Order Status","Service Provider Name","Service Provider Mobile",
    "Customer Name","Customer Mobile","Customer Email",
    "Booking Time","Booking Date",
    "IsWhatsAppLocationMessageSent?","IsSP_PreBooking_1hr_Sent?",
    "Drop Rider","Pickup Rider",
    "Start Journey","Stop Journey","Start Job At","Stop Job At","Total Time",
    "Actual Time Taken","Cx Address"
]

def _col_map(row): return {h.strip(): i for i, h in enumerate(row)}

def _col_letter(idx_1based: int) -> str:
    s, n = "", idx_1based
    while n:
        n, r = divmod(n - 1, 26)
        s = chr(65 + r) + s
    return s

# -----------------------------
# Delayed Report Sheet Helpers
# -----------------------------


# -----------------------------
# Delayed Report Sheet Helpers
# -----------------------------

DELAYED_REPORT_SHEET_NAME = "DelayedReport"
DELAYED_REPORT_SHEET_ID   = "16f-QarUEooXiwymMYAQxqHfulaNExidL47dasKjiP1s"

def ensure_delayed_report_sheet():
    """
    Ensures DelayedReport sheet exists with EXACT structure:

        Date | Order Id | Expert | Booking Time | Booking Date | DelayedMinutes | Manager Comment

    Also normalizes existing rows:
    - Removes leading empty cells (fixes pasted data shifted to the right)
    - Trims/pads each row to exactly 7 columns
    - Removes fully empty rows
    """
    global client

    REQUIRED_HEADER = [
        "Date",
        "Order Id",
        "Expert",
        "Booking Time",
        "Booking Date",
        "DelayedMinutes",
        "Manager Comment",
    ]

    ss = client.open_by_key(DELAYED_REPORT_SHEET_ID)

    # ---------------------------------------------------------
    # 1) CREATE SHEET IF NOT FOUND
    # ---------------------------------------------------------
    try:
        ws = ss.worksheet(DELAYED_REPORT_SHEET_NAME)
    except WorksheetNotFound:
        print("📄 Creating new DelayedReport sheet...")
        ws = ss.add_worksheet(DELAYED_REPORT_SHEET_NAME, rows=2000, cols=len(REQUIRED_HEADER))
        _with_backoff(ws.update, "A1", [REQUIRED_HEADER])
        _beautify_delayed_report(ws)
        print("✅ DelayedReport sheet created fresh")
        return ws

    # ---------------------------------------------------------
    # 2) FIX HEADER
    # ---------------------------------------------------------
    header = _with_backoff(ws.row_values, 1) or []

    # If header is empty or wrong → rewrite it
    if header != REQUIRED_HEADER:
        print("🛠 DelayedReport: fixing header...")
        _with_backoff(ws.update, "A1", [REQUIRED_HEADER])

    # ---------------------------------------------------------
    # 3) NORMALIZE ALL DATA ROWS
    # ---------------------------------------------------------
    all_vals = _with_backoff(ws.get_all_values)

    # all_vals[0] is header, data starts from row 2
    data_rows = all_vals[1:] if len(all_vals) > 1 else []
    cleaned_rows = []

    for raw_row in data_rows:
        # Convert None → "" just in case
        row = [(c or "").strip() for c in raw_row]

        # Skip completely empty rows
        if not any(row):
            continue

        # Remove leading empty cells if there is data later in the row
        # (this fixes rows pasted starting at column D/E/etc.)
        while row and (row[0] == "" or row[0] is None) and any(c.strip() for c in row[1:]):
            row.pop(0)

        # Now row[0] should ideally be Date for valid rows
        # Trim to first 7 cells
        row = row[:7]

        # Pad to exactly 7 cells
        while len(row) < 7:
            row.append("")

        cleaned_rows.append(row)

    # ---------------------------------------------------------
    # 4) WRITE BACK CLEANED DATA
    # ---------------------------------------------------------
    # First, keep header in row 1, clear rest
    # Resize to a known size (will also drop extra columns)
    total_rows = max(2000, len(cleaned_rows) + 1)
    _with_backoff(ws.resize, rows=total_rows, cols=len(REQUIRED_HEADER))

    # Clear all data rows under header
    if total_rows > 1:
        _with_backoff(ws.batch_clear, [f"A2:G{total_rows}"])

    # Write cleaned data (if any)
    if cleaned_rows:
        _with_backoff(ws.update, "A2", cleaned_rows)

    # ---------------------------------------------------------
    # 5) Beautify (bold header, freeze first row, etc.)
    # ---------------------------------------------------------
    _beautify_delayed_report(ws)

    print(f"✅ DelayedReport normalized → {len(cleaned_rows)} data rows, 7 fixed columns")
    return ws


def _beautify_delayed_report(ws):
    """Apply basic beautification."""
    try:
        ws.format("1:1", {"textFormat": {"bold": True}})
        ws.freeze(rows=1)
        ws.resize(rows=2000, cols=7)   # ensure width for Manager Comment
    except Exception as e:
        print("⚠️ Beautify skipped:", e)


def _parse_date_for_sort(date_str):
    """Convert '28-Nov-2025' -> datetime for sorting."""
    try:
        return datetime.strptime(date_str, "%d-%b-%Y")
    except:
        return datetime.min


def ensure_tomorrow_sheet():
    """
    Ensure TommorwBookings sheet exists with EXACT TodayBookings headers.
    WA columns remain blank until tomorrow.
    """
    REQUIRED_COLS = [
        "Order Id","Order Status","Service Provider Name","Service Provider Mobile",
        "Customer Name","Customer Mobile","Customer Email",
        "Booking Time","Booking Date",
        "IsWhatsAppLocationMessageSent?","IsSP_PreBooking_1hr_Sent?",
        "Drop Rider","Pickup ETA","Pickup Rider",
        "Start Journey","Stop Journey","Start Job At","Stop Job At",
        "Total Time","Actual Time Taken",
        "Cx Address","Cx Address Fetched?",
        "IsSP_Start_Job_Reminder_Sent?",
        "OTP Before Sent","OTP After Sent","Stop Job Alert Sent?",
        "Lat&Long","Distance from TL","Distance from AN",
        "IsNearbyCalculatedDone","Nearby Booking 1","Nearby Booking 2","Nearby Booking 3"
    ]

    try:
        ws = sh.worksheet("TommorwBookings")
    except WorksheetNotFound:
        ws = sh.add_worksheet("TommorwBookings", rows=2000, cols=len(REQUIRED_COLS))
        _with_backoff(ws.update, "A1", [REQUIRED_COLS])
        print("sheet: Created TommorwBookings with headers")
        return ws

    header = _with_backoff(ws.row_values, 1)
    if not header:
        _with_backoff(ws.update, "A1", [REQUIRED_COLS])
        return ws

    changed = False
    for col in REQUIRED_COLS:
        if col not in header:
            header.append(col)
            changed = True

    if changed:
        _with_backoff(ws.update, "A1", [header])
        print("sheet: Missing columns added to TommorwBookings")

    return ws




def ensure_today_sheet():
    REQUIRED_COLUMNS = [
        "Order Id","Order Status","Service Provider Name","Service Provider Mobile",
        "Customer Name","Customer Mobile","Customer Email",
        "Booking Time","Booking Date",
        "IsWhatsAppLocationMessageSent?","IsSP_PreBooking_1hr_Sent?",
        "Drop Rider","Pickup ETA","Pickup Rider",
        "Start Journey","Stop Journey","Start Job At","Stop Job At",
        "Total Time","Actual Time Taken",
        "Cx Address","Cx Address Fetched?",
        "IsSP_Start_Job_Reminder_Sent?",
        "OTP Before Sent","OTP After Sent","Stop Job Alert Sent?"
    ]

    try:
        ws = sh.worksheet("TodayBookings")
    except WorksheetNotFound:
        ws = sh.add_worksheet("TodayBookings", rows=2000, cols=60)
        _with_backoff(ws.update, "A1", [REQUIRED_COLUMNS])
        print("sheet: Created TodayBookings with full headers")
        return ws

    # Fetch existing header
    header = _with_backoff(ws.row_values, 1)

    # If header empty → write full required columns
    if not header:
        _with_backoff(ws.update, "A1", [REQUIRED_COLUMNS])
        print("sheet: Header missing, writing full REQUIRED_COLUMNS")
        return ws

    # Build a corrected header preserving REQUIRED_COLUMNS order
    final_header = []
    missing = []

    for col in REQUIRED_COLUMNS:
        if col in header:
            final_header.append(col)
        else:
            final_header.append(col)
            missing.append(col)

    # If sheet has extra non-required columns, append them at the end
    extras = [c for c in header if c not in REQUIRED_COLUMNS]
    final_header.extend(extras)

    # If no change needed, return as-is
    if final_header == header:
        return ws

    # Update header in one batch call
    _with_backoff(ws.update, "A1", [final_header])
    print("sheet: TodayBookings header corrected → added:", missing)

    return ws

    
    
def stop_job_once_stage(ws):
    all_vals = _with_backoff(ws.get_all_values)
    if len(all_vals) <= 1:
        return

    header = all_vals[0]
    h = _col_map(header)

    need = ("Order Id","Stop Job At","Stop Job Alert Sent?","Customer Name","Customer Mobile","Service Provider Name")
    if any(c not in h for c in need):
        print("stop-job-once: required columns missing")
        return

    col_oid   = h["Order Id"]
    col_stop  = h["Stop Job At"]
    col_flag  = h["Stop Job Alert Sent?"]
    col_cname = h["Customer Name"]
    col_cmob  = h["Customer Mobile"]
    col_sp    = h["Service Provider Name"]

    updates = []

    for r_idx, row in enumerate(all_vals[1:], start=2):
        oid   = row[col_oid].strip()
        stop  = row[col_stop].strip()
        flag  = row[col_flag].strip()

        # ✅ Only send when Stop Job At has a timestamp AND not already sent
        if oid and stop and not flag:
            cname = row[col_cname].strip()
            cmob  = row[col_cmob].strip()
            sp    = row[col_sp].strip()

            print(f"stop-job-once: sending feedback → {oid}")

            sent_ok = send_customer_stopjob_feedback(cmob, cname, sp)

            if sent_ok:
                updates.append({
                    "range": f"{_col_letter(col_flag+1)}{r_idx}",
                    "values": [["✅ Sent"]]
                })
                print(f"✅ Feedback sent to {cname} ({cmob})")
            else:
                print(f"⚠️ FAILED → will retry next cycle: {oid}")

    if updates:
        _with_backoff(ws.batch_update, updates)
        print(f"stop-job-once: {len(updates)} marked ✅")


# # ===============================
# # SELENIUM DRIVER
# # ===============================
# chrome_options = Options()
# chrome_options.add_argument("--headless=new")
# chrome_options.add_argument("--no-sandbox")
# chrome_options.add_argument("--disable-gpu")
# chrome_options.add_argument("--window-size=1280,2000")

# service = Service(shutil.which("chromedriver"))
# driver  = webdriver.Chrome(service=service, options=chrome_options)
# # driver.set_page_load_timeout(12)
# wait    = WebDriverWait(driver, 20)

# ===============================
# SELENIUM DRIVER
# ===============================
chrome_options = Options()
chrome_options.add_argument("--headless=new")
chrome_options.add_argument("--no-sandbox")
chrome_options.add_argument("--disable-gpu")
chrome_options.add_argument("--window-size=1280,2000")

driver = webdriver.Chrome(options=chrome_options)
wait    = WebDriverWait(driver, 20)


# ===============================
# LOGIN
# ===============================
def login() -> bool:
    try:
        driver.get(URL_LOGIN)
        WebDriverWait(driver, 20).until(EC.presence_of_element_located((By.ID, "username"))).send_keys(USERNAME)
        driver.find_element(By.ID, "send-otp").click()
        otp_fields = WebDriverWait(driver, 20).until(EC.presence_of_all_elements_located((By.CSS_SELECTOR, ".otp-container input")))
        otp = OTP_ENV or input("Enter OTP: ")
        for i, d in enumerate(otp):
            if i < len(otp_fields): otp_fields[i].send_keys(d)
        driver.find_element(By.ID, "password").send_keys(PASSWORD)
        driver.find_element(By.ID, "sign-with-otp").click()
        WebDriverWait(driver, 20).until(EC.url_contains("dashboard"))
        print("login: ✅")
        return True
    except Exception as e:
        print("login error:", e)
        speak_message("Login failed, script बंद हो गया।")
        return False


# ===============================
# HELPERS: Parsing & Sorting & Colors
# ===============================
def keep_session_alive():
    try:
        cookies = {c['name']: c['value'] for c in driver.get_cookies()}
        # Use a very light page that does not change anything
        requests.get("https://notiononlinesolutions.tech/dashboard", cookies=cookies, timeout=10)
        print("🔄 Session refreshed")
    except Exception as e:
        print("⚠️ Keep-alive error:", e)


def _parse_customer_format_b(lines):
    name = lines[0].strip() if len(lines) > 0 else ""
    mobile, email = "", ""
    for item in lines[1:]:
        s = item.strip()
        if "@" in s:
            email = s
        else:
            digits = re.sub(r"\D", "", s)
            if len(digits) >= 10:
                mobile = digits[-10:]
    return name, mobile, email

def smart_parse_time_date(t_str, d_str):
    t_obj = d_obj = None
    try:
        if t_str: t_obj = dtparser.parse(t_str, fuzzy=True).time()
    except Exception: t_obj = None
    try:
        if d_str: d_obj = dtparser.parse(d_str, fuzzy=True, dayfirst=True).date()
    except Exception: d_obj = None
    if not d_obj: d_obj = datetime.now(IST).date()
    return t_obj, d_obj

def _parse_time_date_strs_for_sheet(t_str, d_str):
    t_obj, d_obj = smart_parse_time_date(t_str, d_str)
    return (t_obj.strftime("%I:%M %p") if t_obj else "",
            d_obj.strftime("%d-%b-%Y") if d_obj else "")

def _apply_time_highlights(ws):
    try:
        all_vals = _with_backoff(ws.get_all_values)
        if len(all_vals) <= 1: return
        header = all_vals[0]; hmap = _col_map(header)
        t_idx, d_idx = hmap.get("Booking Time", 7), hmap.get("Booking Date", 8)
        now = datetime.now(IST)
        light_red  = {"red": 1.0,  "green": 0.85, "blue": 0.85}
        light_blue = {"red": 0.85, "green": 0.92, "blue": 1.0}
        white      = {"red": 1.0,  "green": 1.0,  "blue": 1.0}
        last_col, sheet_id = len(header), ws.id
        reqs = []
        for r_idx, row in enumerate(all_vals[1:], start=2):
            t_str = row[t_idx] if t_idx < len(row) else ""
            d_str = row[d_idx] if d_idx < len(row) else ""
            t_obj, d_obj = smart_parse_time_date(t_str, d_str)
            if t_obj and d_obj:
                booking_dt = IST.localize(datetime.combine(d_obj, t_obj))
                delta = (booking_dt - now).total_seconds()
                color = light_red if 0 <= delta <= 3600 else (light_blue if delta < -3600 else white)
            else:
                color = white
            reqs.append({"repeatCell":{
                "range":{"sheetId":sheet_id,"startRowIndex":r_idx-1,"endRowIndex":r_idx,
                         "startColumnIndex":0,"endColumnIndex":last_col},
                "cell":{"userEnteredFormat":{"backgroundColor":color}},
                "fields":"userEnteredFormat.backgroundColor"
            }})
        for i in range(0, len(reqs), 200):
            _with_backoff(ws.spreadsheet.batch_update, {"requests": reqs[i:i+200]})
        print("sheet: highlights ✅")
    except Exception as e:
        print("sheet: highlight error", e)

def apply_order_status_colors(ws):
    try:
        sheet_id = ws.id
        header   = _with_backoff(ws.row_values, 1)
        hmap     = _col_map(header)
        b_idx    = hmap.get("Order Status", 1)
        green  = {"red":0.80,"green":1.00,"blue":0.80}
        yellow = {"red":1.00,"green":1.00,"blue":0.60}
        orange = {"red":1.00,"green":0.85,"blue":0.70}
        white  = {"red":1.00,"green":1.00,"blue":1.00}
        values = _with_backoff(ws.col_values, b_idx + 1)
        last_col = len(header)
        reqs = []
        for r, status in enumerate(values[1:], start=2):
            s = (status or "").strip().upper()
            if s == "ORDER COMPLEED": s = "ORDER COMPLETED"
            color = green if s == "ORDER COMPLETED" else yellow if s == "START JOB" else orange if s == "START JOURNEY" else white
            reqs.append({"repeatCell":{
                "range":{"sheetId":sheet_id,"startRowIndex":r-1,"endRowIndex":r,
                         "startColumnIndex":b_idx,"endColumnIndex":b_idx+1},
                "cell":{"userEnteredFormat":{"backgroundColor":color}},
                "fields":"userEnteredFormat.backgroundColor"
            }})
        for i in range(0, len(reqs), 200):
            _with_backoff(ws.spreadsheet.batch_update, {"requests": reqs[i:i+200]})
        print("sheet: status colors ✅")
    except Exception as e:
        print("sheet: status color error", e)

def _sort_rows_by_time(ws):
    all_vals = _with_backoff(ws.get_all_values)
    if len(all_vals) <= 2: return
    header, data = all_vals[0], all_vals[1:]
    hmap = _col_map(header)
    t_idx, d_idx = hmap.get("Booking Time", 7), hmap.get("Booking Date", 8)

    def sort_key(row):
        t_str = row[t_idx] if t_idx < len(row) else ""
        d_str = row[d_idx] if d_idx < len(row) else ""
        try: t_obj, d_obj = smart_parse_time_date(t_str, d_str)
        except Exception: t_obj, d_obj = None, None
        return (d_obj or date.max, t_obj or datetime.max.time())

    sorted_rows = sorted([r for r in data if any(r)], key=sort_key)
    last_col, current_rows = len(header), len(all_vals)
    if current_rows > 1:
        _with_backoff(ws.batch_clear, [f"A2:{_col_letter(last_col)}{current_rows}"])
    if sorted_rows:
        _with_backoff(ws.update, "A2", sorted_rows)
    try:
        _with_backoff(ws.freeze, rows=1)
        ws.format(f"A1:{_col_letter(last_col)}1", {"textFormat": {"bold": True}})
        ws.format(f"A:{_col_letter(last_col)}", {"verticalAlignment": "MIDDLE"})
    except Exception:
        pass
    print("sheet: sorted ✅")

def strike_bold_cancelled_rows(ws, latest_ids):
    try:
        all_vals = _with_backoff(ws.get_all_values)
        if not all_vals: return
        header = all_vals[0]
        last_col = len(header)
        sheet_id = ws.id
        reqs = []
        for r_idx, row in enumerate(all_vals[1:], start=2):
            if not row or not row[0].strip(): continue
            oid = row[0].strip()
            tfmt = {"strikethrough": True, "bold": True} if oid not in latest_ids else {"strikethrough": False, "bold": False}
            reqs.append({"repeatCell":{
                "range":{"sheetId":sheet_id,"startRowIndex":r_idx-1,"endRowIndex":r_idx,
                         "startColumnIndex":0,"endColumnIndex":last_col},
                "cell":{"userEnteredFormat":{"textFormat":tfmt}},
                "fields":"userEnteredFormat.textFormat"
            }})
        for i in range(0, len(reqs), 200):
            _with_backoff(ws.spreadsheet.batch_update, {"requests": reqs[i:i+200]})
        print("sheet: cancelled marked ✅")
    except Exception as e:
        print("sheet: cancel mark error", e)
        
def remove_missing_orders(ws, latest_ids_set):
    """
    Remove rows from TodayBookings sheet whose Order Id is NOT in today's datatable.
    """
    all_vals = _with_backoff(ws.get_all_values)
    if len(all_vals) <= 1:
        return

    header = all_vals[0]
    h = _col_map(header)
    if "Order Id" not in h:
        print("remove-missing: 'Order Id' column missing")
        return

    col_oid = h["Order Id"]
    delete_rows = []

    # Identify rows to delete
    for r_idx, row in enumerate(all_vals[1:], start=2):
        oid = row[col_oid].strip() if col_oid < len(row) else ""
        if oid and oid not in latest_ids_set:
            delete_rows.append(r_idx)

    if not delete_rows:
        print("remove-missing: none to delete ✅")
        return

    # Must delete bottom → top to avoid index shift
    delete_rows.sort(reverse=True)
    for r in delete_rows:
        try:
            ws.delete_rows(r)
        except Exception as e:
            print("remove-missing: delete error →", e)

    print(f"remove-missing: deleted {len(delete_rows)} old/cancelled rows ✅")


# ===============================
# INTERAKT HELPERS
# ===============================

def interakt_api_call(payload):
    """
    Core Interakt POST call for sending WhatsApp messages (plain text or template).
    """
    try:
        headers = {
            "Authorization": f"Bearer {INTERAKT_API_KEY}",
            "Content-Type": "application/json"
        }

        response = requests.post(
            INTERAKT_PLAIN_URL,
            headers=headers,
            data=json.dumps(payload)
        )

        print(f"wa: {payload.get('templateId', 'plain')} -> {payload.get('phoneNumber')}: "
              f"{response.status_code} | {response.text}")

        return response.status_code == 200

    except Exception as e:
        print("Interakt API Exception:", e)
        return False


def send_interakt_plain_text(phone, message):
    """
    Sends a free plain-text WhatsApp message via Interakt session API.
    No template required.
    """
    payload = {
        "phoneNumber": phone,
        "type": "text",
        "message": message,
    }
    return interakt_api_call(payload)


def _send_interakt_template(phone, body_values, template_name, language="en"):
    try:
        if not phone:
            print("wa: empty phone"); return False
        digits = re.sub(r"\D", "", str(phone))
        if len(digits) < 10:
            print(f"wa: invalid phone {phone}"); return False
        digits = digits[-10:]

        auth_header = base64.b64encode((INTERAKT_API_KEY + ":").encode()).decode()
        headers = {"Authorization": f"Basic {auth_header}", "Content-Type": "application/json"}
        payload = {
            "countryCode": INTERAKT_COUNTRY_CODE,
            "phoneNumber": digits,
            "type": "Template",
            "template": {"name": template_name, "languageCode": language, "bodyValues": body_values or [], "buttonValues": {}}
        }

        for attempt in range(3):
            try:
                resp = requests.post(INTERAKT_URL, headers=headers, json=payload, timeout=20)
                print(f"wa: {template_name} -> {digits}: {resp.status_code} | {resp.text}")
                if resp.status_code in (200, 201): return True
                if "131049" in str(resp.text):
                    print(f"🚫 wa: {template_name} BLOCKED for {digits} (Meta cooldown 24h)")
                    with open("/tmp/interakt_cooldown.log", "a") as f:
                        ts = datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S")
                        f.write(f"[{ts}] BLOCKED 24h → {digits} ({template_name})\n")
                    return False
                if resp.status_code >= 500 or "quota" in resp.text.lower():
                    time.sleep(2 * (attempt + 1)); continue
                return False
            except Exception as e:
                print("wa: send exception", e); time.sleep(2 * (attempt + 1))
        return False
    except Exception as e:
        print("wa: send error", e); return False

def send_interakt_message(phone, customer_name):
    return _send_interakt_template(phone, [customer_name or ""], INTERAKT_TEMPLATE, "en")
    
def send_customer_stopjob_feedback(phone, customer_name, sp_name):
    # Template expects: {{1}} = Customer Name, {{2}} = SP Name
    return _send_interakt_template(
        phone,
        [customer_name or "", clean_sp_name(sp_name) or ""],
        INTERAKT_CX_STOPJOB_FEEDBACK_TMPL,
        "en"
    )


def send_interakt_sp_prebooking(phone, sp_name):
    return _send_interakt_template(phone, [clean_sp_name(sp_name) or ""], INTERAKT_SP_PREBOOK_TMPL, "en")

def send_interakt_sp_finish_alert_to_manager(sp_name, hhmm):
    # Send to all manager numbers
    ok_any = False
    for phone in MANAGER_PHONES:
        ok = _send_interakt_template(
            phone,
            [clean_sp_name(sp_name) or "", hhmm or ""],
            INTERAKT_SP_FINISH_TMPL,
            "en"
        )
        if ok:
            ok_any = True
            print(f"✅ Manager Alert Sent → {phone}")
        else:
            print(f"⚠️ Manager Alert Failed → {phone}")
        time.sleep(2)  # small gap, avoid WA rate limit
    return ok_any

def send_sp_otp_reminder(phone, sp_name, variant="before"):
    template = INTERAKT_SP_OTP_REM_10MIN
    return _send_interakt_template(phone, [clean_sp_name(sp_name)], template, "en")

def _which_prebooking_window(b_time_str, b_date_str):
    try:
        t_obj, d_obj = smart_parse_time_date(b_time_str, b_date_str)
        if not (t_obj and d_obj): return None
        booking_dt = IST.localize(datetime.combine(d_obj, t_obj))
        delta = (booking_dt - datetime.now(IST)).total_seconds()
        for (lo, hi), label in [(SP_PREBOOK_1HR_WINDOW,"1hr"), (SP_PREBOOK_30MIN_WINDOW,"30min"), (SP_PREBOOK_10MIN_WINDOW,"10min")]:
            if lo <= delta <= hi: return label
        return None
    except Exception:
        return None


# Global in-memory guard to avoid double-send within this process
_BG_SENT_CACHE = set()   # keys: (ws_title, row, col)





def background_worker():
    import time

    # ==================================================
    # NORMALIZERS & GUARDS
    # ==================================================
    def _norm_flag(val):
        return (
            str(val or "")
            .replace("✅", "")
            .replace("✔️", "")
            .replace("\n", "")
            .replace("\r", "")
            .replace("\t", "")
            .replace("\xa0", " ")
            .strip()
            .upper()
        )

    def _should_send_flag(v):
        return _norm_flag(v) in ("", "NOT YET", "FAILED")

    # ==================================================
    # SHEET HELPERS
    # ==================================================
    def _find_row_by_oid(ws, oid):
        try:
            for c in _with_backoff(ws.findall, str(oid)):
                if c.col == 1:
                    return c.row
        except Exception as e:
            print("BG FIND ERROR:", e)
        return None

    def _resolve_row(ws, oid, fallback_row):
        if oid:
            r = _find_row_by_oid(ws, oid)
            if r:
                return r
            if fallback_row:
                print(f"BG NOTICE: OID {oid} not found → fallback row {fallback_row}")
                return int(fallback_row)
            print("BG ERROR: Cannot resolve row (OID missing)")
            return None
        return int(fallback_row) if fallback_row else None

    def _read(ws, row, colA):
        try:
            return _norm_flag(_with_backoff(ws.acell, f"{colA}{row}").value)
        except Exception as e:
            print(f"BG READ ERROR {ws.title}!{colA}{row} → {e}")
            return ""

    def _read_backoff(ws, row, colA, attempts=6):
        delay = 0.5
        for i in range(attempts):
            try:
                return _norm_flag(_with_backoff(ws.acell, f"{colA}{row}").value)
            except Exception as e:
                msg = str(e).lower()
                if "quota" in msg or "429" in msg:
                    print(f"BG BACKOFF READ {i+1}/{attempts} → wait {delay}s")
                    time.sleep(delay)
                    delay = min(delay * 2, 8)
                else:
                    print("BG READ ERROR:", e)
                    return ""
        return ""

    def _safe_update(ws, row, col, value, label):
        for i in range(3):
            try:
                _with_backoff(ws.update_cell, row, col, value)
                print(f"BG: {label} updated → {value} @ row={row}, col={col}")
                return True
            except Exception as e:
                print(f"BG WRITE ERROR {label} ({i+1}/3):", e)
        return False

    def _verify(ws, row, col, expect="SENT"):
        colA = _col_letter(col)
        for i in range(3):
            time.sleep(0.3)
            try:
                v = _norm_flag(_with_backoff(ws.acell, f"{colA}{row}").value)
            except Exception:
                v = ""
            if v == expect:
                print(f"BG VERIFY OK → {expect}")
                return True
            print(f"BG VERIFY MISMATCH ({v}), retry {i+1}")
        return False

    # ==================================================
    # MAIN WORKER LOOP
    # ==================================================
    while True:
        task = None
        try:
            task = TASK_QUEUE.get()
            if task is None:
                break

            ttype = task.get("type")

            # ==================================================
            # CUSTOMER WHATSAPP
            # ==================================================
            if ttype == "customer_whatsapp":
                ws    = task["ws"]
                phone = task["phone"]
                cname = task["cname"]
                col   = int(task["col"])
                oid   = task.get("oid")
                row   = task.get("row")

                live_row = _resolve_row(ws, oid, row)
                if not live_row:
                    continue

                colA = _col_letter(col)
                flag = _read(ws, live_row, colA)

                if not _should_send_flag(flag):
                    print(f"BG WA SKIPPED → flag={flag}")
                    continue

                try:
                    ok = send_interakt_message(phone, cname)
                except Exception as e:
                    print("BG WA ERROR:", e)
                    ok = False

                if ok:
                    _safe_update(ws, live_row, col, "SENT", "WA")
                    _verify(ws, live_row, col)
                    if oid:
                        mark_customer_wa_sent(oid)   # 🔒 persistent ledger
                else:
                    _safe_update(ws, live_row, col, "FAILED", "WA")

            # ==================================================
            # SERVICE PROVIDER PREBOOK
            # ==================================================
            elif ttype == "sp_prebook":
                ws    = task["ws"]
                phone = task["phone"]
                sp    = task["sp"]
                note  = task["note"]
                col   = int(task["col"])
                oid   = task.get("oid")
                row   = task.get("row")

                live_row = _resolve_row(ws, oid, row)
                if not live_row:
                    continue

                colA = _col_letter(col)
                flag = _read(ws, live_row, colA)

                if not _should_send_flag(flag):
                    print(f"BG PREBOOK SKIPPED → flag={flag}")
                    continue

                try:
                    ok = send_interakt_sp_prebooking(phone, sp)
                except Exception as e:
                    print("BG PREBOOK ERROR:", e)
                    ok = False

                if ok:
                    _safe_update(ws, live_row, col, note, "Prebook")
                    _verify(ws, live_row, col, _norm_flag(note))
                else:
                    _safe_update(ws, live_row, col, "FAILED", "Prebook")

            # ==================================================
            # MANAGER DELAY ALERT (BACKOFF READ)
            # ==================================================
            elif ttype == "manager_delay_alert":
                ws    = task["ws"]
                phone = task["phone"]
                msg   = task["message"]
                col   = int(task["col_alert"])
                oid   = task.get("oid")
                row   = task.get("row")

                live_row = _resolve_row(ws, oid, row)
                if not live_row:
                    continue

                colA = _col_letter(col)
                flag = _read_backoff(ws, live_row, colA)

                if not _should_send_flag(flag):
                    print(f"BG DELAY ALERT SKIPPED → flag={flag}")
                    continue

                try:
                    ok = send_interakt_plain_text(phone, msg)
                except Exception as e:
                    print("BG DELAY ALERT ERROR:", e)
                    ok = False

                if ok:
                    _safe_update(ws, live_row, col, "SENT", "DelayAlert")
                    _verify(ws, live_row, col)
                else:
                    _safe_update(ws, live_row, col, "FAILED", "DelayAlert")

            # ==================================================
            # SYSTEM TASKS
            # ==================================================
            elif ttype == "voice":
                speak_message(task["msg"])

            elif ttype == "manager_alert":
                send_interakt_sp_finish_alert_to_manager(
                    task["sp"], task["hhmm"]
                )

            else:
                print("BG UNKNOWN TASK:", ttype)

        except Exception as e:
            print("BG WORKER ERROR:", e)

        finally:
            try:
                TASK_QUEUE.task_done()
            except Exception:
                pass




# ===============================
# BILLING (Sheet1) & PREPAID
# ===============================
wanted_headers = ["Invoice No.", "Date", "Customer Name", "Hub", "Time", "Service Provider", "Total Invoice"]

def ensure_customer_sheet_headers():
    try:
        customer_sheet = client.open_by_key(GOOGLE_SHEET_ID).worksheet(CUSTOMER_SHEET_NAME)
    except WorksheetNotFound:
        customer_sheet = client.open_by_key(GOOGLE_SHEET_ID).add_worksheet(CUSTOMER_SHEET_NAME, rows=100, cols=len(wanted_headers))
    existing = _with_backoff(customer_sheet.get_all_values)
    if not existing or len(existing) == 0:
        _with_backoff(customer_sheet.append_row, wanted_headers)
        print("sheet1: headers added (empty)")
    elif existing[0] != wanted_headers:
        _with_backoff(customer_sheet.insert_row, wanted_headers, 1)
        print("sheet1: headers normalized")

# def fetch_customer_bill():
#     try:
#         customer_sheet = client.open_by_key(GOOGLE_SHEET_ID).worksheet(CUSTOMER_SHEET_NAME)
#     except Exception:
#         ensure_customer_sheet_headers()
#         customer_sheet = client.open_by_key(GOOGLE_SHEET_ID).worksheet(CUSTOMER_SHEET_NAME)

#     today_str = datetime.now(IST).strftime("%d-%m-%Y")
#     url = (f"https://notiononlinesolutions.tech/franchise/customer-bill?"
#           f"startat={today_str}&endat={today_str}&franchise_hub_ids={FRANCHISE_HUB_ID}&_franchise_hub_ids=1")
#     try:
#         driver.get(url); time.sleep(2)
#         try:
#             select_elem = wait.until(EC.presence_of_element_located((By.XPATH, CUSTOMER_BILL_PAGINATION_XPATH)))
#             driver.execute_script("arguments[0].value='150'; arguments[0].dispatchEvent(new Event('change'));", select_elem)
#             wait.until(lambda d: len(d.find_elements(By.CSS_SELECTOR, "#datatable tbody tr")) >= 1)
#         except Exception: pass
#         try:
#             table = driver.find_element(By.XPATH, "//div[@class='dataTables_scroll']//table[@id='datatable']")
#         except Exception:
#             table = driver.find_element(By.ID, "datatable")
#         soup = BeautifulSoup(table.get_attribute("outerHTML"), "html.parser")
#         full_headers = [th.text.strip() for th in soup.find_all("th")]
#         rows_html = soup.find_all("tr")[1:]
#         if rows_html and "No data available in table" in rows_html[0].get_text(strip=True):
#             print("bills: none (no data)"); return 0
#         try:
#             inv_idx = full_headers.index("Invoice No.")
#         except ValueError:
#             print("bills: Invoice No. column missing"); return 0
#         values = _with_backoff(customer_sheet.get_all_values)
#         existing_invoices = set(row[0] for row in values[1:] if row)
#         new_rows = []
#         for row in rows_html:
#             cols = [td.text.strip() for td in row.find_all("td")]
#             if len(cols) <= inv_idx: continue
#             invoice_no = cols[inv_idx]
#             if invoice_no and invoice_no not in existing_invoices:
#                 new_rows.append([cols[full_headers.index(h)] if h in full_headers else "" for h in wanted_headers])
#                 existing_invoices.add(invoice_no)
#         if new_rows:
#             _with_backoff(customer_sheet.append_rows, new_rows)
#             print(f"bills: +{len(new_rows)} ✅"); return len(new_rows)
#         print("bills: none"); return 0
#     except Exception as e:
#         print("bills: error", e); return 0

def fetch_customer_bill():
    """
    Sheet1 = SOURCE OF TRUTH
    - Existing invoices → FULL ROW UPDATE (overwrite)
    - New invoices      → APPEND
    """

    try:
        customer_sheet = client.open_by_key(GOOGLE_SHEET_ID).worksheet(CUSTOMER_SHEET_NAME)
    except Exception:
        ensure_customer_sheet_headers()
        customer_sheet = client.open_by_key(GOOGLE_SHEET_ID).worksheet(CUSTOMER_SHEET_NAME)

    # --------------------------------------------
    # 1️⃣ Load existing Sheet1 (invoice → row map)
    # --------------------------------------------
    sheet_vals = _with_backoff(customer_sheet.get_all_values)
    if not sheet_vals:
        ensure_customer_sheet_headers()
        sheet_vals = _with_backoff(customer_sheet.get_all_values)

    header = sheet_vals[0]
    existing_map = {}   # invoice_no -> row_number (1-based)

    for r_idx, row in enumerate(sheet_vals[1:], start=2):
        if row and row[0]:
            existing_map[row[0]] = r_idx

    # --------------------------------------------
    # 2️⃣ Open Customer Bill page
    # --------------------------------------------
    today_str = datetime.now(IST).strftime("%d-%m-%Y")
    url = (
        f"https://notiononlinesolutions.tech/franchise/customer-bill?"
        f"startat={today_str}&endat={today_str}"
        f"&franchise_hub_ids={FRANCHISE_HUB_ID}&_franchise_hub_ids=1"
    )

    try:
        driver.get(url)
        time.sleep(2)

        try:
            select_elem = wait.until(
                EC.presence_of_element_located((By.XPATH, CUSTOMER_BILL_PAGINATION_XPATH))
            )
            driver.execute_script(
                "arguments[0].value='150'; arguments[0].dispatchEvent(new Event('change'));",
                select_elem
            )
            wait.until(lambda d: len(d.find_elements(By.CSS_SELECTOR, "#datatable tbody tr")) >= 1)
        except Exception:
            pass

        try:
            table = driver.find_element(By.XPATH, "//div[@class='dataTables_scroll']//table[@id='datatable']")
        except Exception:
            table = driver.find_element(By.ID, "datatable")

        soup = BeautifulSoup(table.get_attribute("outerHTML"), "html.parser")
        full_headers = [th.text.strip() for th in soup.find_all("th")]
        rows_html = soup.find_all("tr")[1:]

        if rows_html and "No data available in table" in rows_html[0].get_text(strip=True):
            print("bills: none (no data)")
            return 0

        inv_idx = full_headers.index("Invoice No.")

        # --------------------------------------------
        # 3️⃣ UPSERT logic
        # --------------------------------------------
        updates = []
        inserts = []

        for tr in rows_html:
            cols = [td.text.strip() for td in tr.find_all("td")]
            if len(cols) <= inv_idx:
                continue

            invoice_no = cols[inv_idx]
            if not invoice_no:
                continue

            new_row = [
                cols[full_headers.index("Invoice No.")],
                cols[full_headers.index("Date")],
                cols[full_headers.index("Customer Name")],
                cols[full_headers.index("Hub")],
                cols[full_headers.index("Time")],
                cols[full_headers.index("Service Provider")],
                cols[full_headers.index("Total Invoice")],
            ]

            if invoice_no in existing_map:
                row_no = existing_map[invoice_no]
                updates.append({
                    "range": f"A{row_no}:G{row_no}",
                    "values": [new_row]
                })
            else:
                inserts.append(new_row)

        # --------------------------------------------
        # 4️⃣ Batch write (safe + fast)
        # --------------------------------------------
        if updates:
            _with_backoff(customer_sheet.batch_update, updates)
            print(f"bills: updated {len(updates)} invoices")

        if inserts:
            _with_backoff(customer_sheet.append_rows, inserts)
            print(f"bills: inserted {len(inserts)} new invoices")

        return len(updates) + len(inserts)

    except Exception as e:
        print("bills: error", e)
        return 0


def clear_today_prepaid_sheet():
    try:
        prepaid_sheet = client.open_by_key(GOOGLE_SHEET_ID).worksheet("TodayPrepaid")
        _with_backoff(prepaid_sheet.resize, rows=1)
        print("prepaid: cleared")
    except WorksheetNotFound:
        print("prepaid: will create when needed")

def fetch_prepaid_orders():
    today_str = datetime.now(IST).strftime("%d-%m-%Y")
    prepaid_url = (f"https://notiononlinesolutions.tech/franchise/prepaid-order?"
                   f"start={today_str}&end={today_str}&hubIds={FRANCHISE_HUB_ID}&_hubIds=1&_dateTypes=1")
    try:
        driver.get(prepaid_url)
        wait.until(EC.presence_of_element_located((By.XPATH, "//table[@id='datatable']//tbody/tr"))); time.sleep(1)
        try:
            table = driver.find_element(By.XPATH, "//div[@class='dataTables_scroll']//table[@id='datatable']")
        except Exception:
            table = driver.find_element(By.ID, "datatable")
        soup = BeautifulSoup(table.get_attribute("outerHTML"), "html.parser")
        headers = [th.text.strip() for th in soup.find_all("th")]
        rows = soup.find_all("tr")[1:]
        all_data = [[td.text.strip() for td in r.find_all("td")] for r in rows if r.find_all("td")]
        try:
            prepaid_sheet = client.open_by_key(GOOGLE_SHEET_ID).worksheet("TodayPrepaid")
        except WorksheetNotFound:
            prepaid_sheet = client.open_by_key(GOOGLE_SHEET_ID).add_worksheet("TodayPrepaid", rows="100", cols=str(len(headers)))
            _with_backoff(prepaid_sheet.append_row, headers)
        if all_data:
            _with_backoff(prepaid_sheet.append_rows, all_data)
            print(f"prepaid: +{len(all_data)} ✅")
    except Exception as e:
        ts = datetime.now(IST).strftime("%Y%m%d_%H%M%S")
        try: driver.save_screenshot(f"prepaid_error_{ts}.png")
        except Exception: pass
        print("prepaid: error", e)

# ===============================
# TODAY BOOKINGS SYNC + MESSAGING
# ===============================



import folium
from folium.plugins import HeatMap
from datetime import datetime

TL_LAT, TL_LNG = map(float, TL_LATLNG.split(","))
AN_LAT, AN_LNG = map(float, AN_LATLNG.split(","))

def generate_map_from_sheet(ws):
    """
    FINAL MAP VIEW (Enhanced) — TODAY BOOKINGS
    - TL Hub         = Green marker
    - AN Hub         = Red marker
    - Pin color logic:
        • Status = START JOB
              → Dark Yellow (icon 'orange') + LIVE PULSE animation
        • Status = ORDER COMPLETED / ORDER FEEDBACK DONE
              → Green
        • Other statuses (distance based):
              → Near TL (≤7 km) = Beige
              → Near AN (≤7 km) = Black
              → Normal          = Blue

    Popup:
        - Horizontal layout (left: job; right: address)
        - SP yellow badge (click to highlight all bookings of that SP)
        - Time in red
        - Date shown separately
        - Total Time shown on its own line
        - Status badge with color
        - Color-coded popup border (by status)
        - "Open in Google Maps" button (SP current loc = booking lat/lng)

    Extras:
        - Heatmap
        - Legend
        - Top-right summary box:
              Total / Completed / Running / Assigned
        - Auto-refresh every 30 sec
        - Filters: buttons [All / Running / Completed]
        - SP-click highlight: dims all others, keeps that SP bright
        - Live animation: running markers pulse
    """

    all_rows = ws.get_all_values()
    if len(all_rows) <= 1:
        print("map: no data")
        return

    # -----------------------------------------------------------
    # Header & column indexes
    # -----------------------------------------------------------
    header = all_rows[0]
    h = {name: i for i, name in enumerate(header)}

    required = ["Order Id", "Service Provider Name", "Booking Time",
                "Booking Date", "Cx Address", "Lat&Long"]
    for c in required:
        if c not in h:
            print("map: missing column:", c)
            return

    col_oid        = h["Order Id"]
    col_sp         = h["Service Provider Name"]
    col_bt         = h["Booking Time"]
    col_bd         = h["Booking Date"]
    col_addr       = h["Cx Address"]
    col_latlng     = h["Lat&Long"]
    col_dist_tl    = h.get("Distance from TL")
    col_dist_an    = h.get("Distance from AN")
    col_status     = h.get("Order Status")
    col_total_time = h.get("Total Time")   # NEW

    points = []
    heat = []

    # -----------------------------------------------------------
    # Parse sheet rows → points list
    # points item:
    #   (lat, lng, oid, sp, bt, bd, addr, dist_tl, dist_an, status, total_time)
    # -----------------------------------------------------------
    for row in all_rows[1:]:
        if col_latlng >= len(row):
            continue

        latlng = (row[col_latlng] or "").strip()
        if not latlng or "," not in latlng:
            continue

        try:
            lat, lng = map(float, latlng.split(","))
        except Exception:
            continue

        oid  = row[col_oid]  if col_oid  < len(row) else ""
        sp   = row[col_sp]   if col_sp   < len(row) else ""
        bt   = row[col_bt]   if col_bt   < len(row) else ""
        bd   = row[col_bd]   if col_bd   < len(row) else ""
        addr = row[col_addr] if col_addr < len(row) else ""

        dist_tl = row[col_dist_tl] if (col_dist_tl is not None and col_dist_tl < len(row)) else ""
        dist_an = row[col_dist_an] if (col_dist_an is not None and col_dist_an < len(row)) else ""
        status  = row[col_status]  if (col_status  is not None and col_status  < len(row)) else ""
        total_time = row[col_total_time] if (col_total_time is not None and col_total_time < len(row)) else ""

        points.append((lat, lng, oid, sp, bt, bd, addr, dist_tl, dist_an, status, total_time))
        heat.append([lat, lng])

    if not points:
        print("map: no valid points")
        return

    # -----------------------------------------------------------
    # Base Map centered on TL hub
    # -----------------------------------------------------------
    m = folium.Map(location=[TL_LAT, TL_LNG], zoom_start=12)


    # -----------------------------------------------------------
    # TL & AN HUB markers
    # -----------------------------------------------------------
    folium.Marker(
        [TL_LAT, TL_LNG],
        popup="TL HUB",
        icon=folium.Icon(color="green", icon="home")
    ).add_to(m)

    folium.Marker(
        [AN_LAT, AN_LNG],
        popup="AN HUB",
        icon=folium.Icon(color="red", icon="home")
    ).add_to(m)

    # -----------------------------------------------------------
    # Helpers: icon color + badges + border color
    # -----------------------------------------------------------
    import math

    def hav(lat1, lon1, lat2, lon2):
        R = 6371.0
        d1 = math.radians(lat2 - lat1)
        d2 = math.radians(lon2 - lon1)
        a = (
            math.sin(d1 / 2) ** 2 +
            math.cos(math.radians(lat1)) *
            math.cos(math.radians(lat2)) *
            math.sin(d2 / 2) ** 2
        )
        return 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a)) * R

    def icon_color(lat, lng, status):
        """
        Status-based override:
          - START JOB                           → 'orange' (dark yellow)
          - ORDER COMPLETED / ORDER FEEDBACK DONE → 'green'
        Else distance-based near TL/AN.
        """
        s_up = (status or "").upper()

        # 1) Status overrides
        if "START JOB" in s_up:
            return "orange"  # dark yellow approximation
        if ("ORDER COMPLETED" in s_up) or ("ORDER FEEDBACK DONE" in s_up):
            return "green"

        # 2) Distance-based for others
        d_tl = hav(lat, lng, TL_LAT, TL_LNG)
        d_an = hav(lat, lng, AN_LAT, AN_LNG)

        if d_tl <= 7:
            return "beige"   # Near TL (≤7 km, other statuses)
        if d_an <= 7:
            return "black"   # Near AN (≤7 km, other statuses)
        return "blue"        # Normal

    def status_badge(s):
        s_up = (s or "").upper()
        if "START JOB" in s_up or "PROGRESS" in s_up:
            color = "#FFA000"  # dark yellow
        elif ("ORDER COMPLETED" in s_up) or ("ORDER FEEDBACK DONE" in s_up):
            color = "#4CAF50"  # green
        elif "CANCEL" in s_up or "FAIL" in s_up:
            color = "#F44336"  # red
        else:
            color = "#2196F3"  # blue

        return f"""
            <span style="
                background:{color};
                padding:3px 10px;
                border-radius:6px;
                color:white;
                font-weight:bold;
            ">{s}</span>
        """

    def border_color_for_status(s):
        s_up = (s or "").upper()
        if "START JOB" in s_up or "PROGRESS" in s_up:
            return "#FFA000"  # dark yellow
        if ("ORDER COMPLETED" in s_up) or ("ORDER FEEDBACK DONE" in s_up):
            return "#4CAF50"  # green
        if "CANCEL" in s_up or "FAIL" in s_up:
            return "#F44336"  # red
        return "#9E9E9E"      # grey / default

    # -----------------------------------------------------------
    # Add booking markers + store JS metadata
    # -----------------------------------------------------------
    markers_info = []  # [{js_var, sp_js}, ...]

    for (lat, lng, oid, sp, bt, bd, addr, dist_tl, dist_an, status, total_time) in points:
        border_color = border_color_for_status(status)

        sp_js = (sp or "").replace("\\", "\\\\").replace("'", "\\'")
        # SP current loc = booking location (lat, lng)
        gmaps_url = f"https://www.google.com/maps?q={lat:.6f},{lng:.6f}"

        popup = f"""
        <div style="
            display: flex;
            flex-direction: row;
            gap: 20px;
            padding: 12px;
            font-size: 15px;
            font-family: Arial, sans-serif;
            line-height: 1.4;
            border: 3px solid {border_color};
            border-radius: 10px;
        ">
            <div style="min-width: 210px;">

                <b style="font-size:16px;">Order:</b> {oid}<br>

                <b style="font-size:16px;">SP:</b>
                <span
                    style="
                        background: #ffeb3b;
                        padding: 2px 8px;
                        border-radius: 6px;
                        font-weight:bold;
                        color:#000;
                        cursor:pointer;
                    "
                    onclick="highlightSP('{sp_js}')"
                    title="Click to highlight all bookings of {sp_js}"
                >
                    {sp}
                </span><br>

                <b style="font-size:16px; color:red;">Time:</b>
                <span style="font-weight:bold; color:red;">
                    {bt}
                </span><br>

                <b style="font-size:16px;">Date:</b> {bd}<br>

                <b style="font-size:16px;">Total Time:</b>
                <span style="font-weight:bold;">{total_time}</span><br>

                <b style="font-size:16px;">Status:</b>
                {status_badge(status)}<br>

                <a href="{gmaps_url}" target="_blank"
                   style="
                       display:inline-block;
                       margin-top:10px;
                       padding:6px 10px;
                       background:#1a73e8;
                       color:white;
                       text-decoration:none;
                       border-radius:4px;
                       font-weight:bold;
                       font-size:13px;
                   ">
                    📍 Open in Google Maps
                </a>

            </div>

            <div style="min-width: 260px;">
                <b style="font-size:16px;">Address:</b><br>
                {addr}<br><br>

                <b style="font-size:16px;">Distance:</b><br>
                • From TL: <b>{dist_tl}</b><br>
                • From AN: <b>{dist_an}</b><br>
            </div>
        </div>
        """

        # -----------------------------------------
        # CUSTOM PIN → SP Name + Time + Total Time ABOVE pin
        # -----------------------------------------
        pin_color = icon_color(lat, lng, status)
        
        circle_html = f"""
        <div style="text-align:center; transform: translate(-20px, -75px);">
        
            <!-- SP NAME -->
            <div style="
                background:white;
                border:1px solid #444;
                border-radius:4px;
                padding:1px 6px;
                font-size:11px;
                font-weight:bold;
                display:inline-block;
                margin-bottom:2px;
                white-space:nowrap;
            ">
                {sp}
            </div>
        
            <!-- TIME -->
            <div style="
                background:white;
                border:1px solid #999;
                border-radius:4px;
                padding:1px 6px;
                font-size:10px;
                display:inline-block;
                margin-bottom:2px;
                color:#d32f2f;
                font-weight:bold;
            ">
                {bt}
            </div>
        
            <!-- TOTAL TIME -->
            <div style="
                background:white;
                border:1px solid #999;
                border-radius:4px;
                padding:1px 6px;
                font-size:10px;
                display:inline-block;
                margin-bottom:4px;
                color:#000;
                font-weight:bold;
            ">
                {total_time}
            </div>
        
            <!-- COLORED CIRCLE -->
            <div style="
                width:28px;
                height:28px;
                background:{pin_color};
                border-radius:50%;
                border:3px solid {border_color};
                margin:auto;
                box-shadow:0 0 6px rgba(0,0,0,0.3);
            ">
            </div>
        
        </div>
        """
        
        marker = folium.Marker(
            location=[lat, lng],
            popup=popup,   # popup unchanged
            icon=folium.DivIcon(html=circle_html)
        ).add_to(m)


        markers_info.append({
            "js_var": marker.get_name(),
            "sp_js": sp_js,
        })

    # -----------------------------------------------------------
    # Heatmap Layer
    # -----------------------------------------------------------
    HeatMap(heat, radius=18, blur=15).add_to(m)

    # -----------------------------------------------------------
    # Legend Box
    # -----------------------------------------------------------
    legend_html = """
    <div style="
        position: fixed;
        bottom: 20px;
        left: 20px;
        z-index:9999;
        background:white;
        padding:10px;
        border-radius:8px;
        box-shadow:0 0 10px rgba(0,0,0,0.3);
        font-size:14px;
    ">
        <b>Legend</b><br>
        <span style="color:green;">●</span> TL HUB<br>
        <span style="color:red;">●</span> AN HUB<br>
        <span style="color:orange;">●</span> START JOB (Status)<br>
        <span style="color:green;">●</span> ORDER COMPLETED / FEEDBACK DONE<br>
        <span style="color:beige;">●</span> Near TL (≤7 km, other statuses)<br>
        <span style="color:black;">●</span> Near AN (≤7 km, other statuses)<br>
        <span style="color:blue;">●</span> Normal Booking<br>
    </div>
    """
    m.get_root().html.add_child(folium.Element(legend_html))

    # -----------------------------------------------------------
    # FILTER BUTTONS (Show All / Running / Completed)
    # -----------------------------------------------------------
    filter_buttons = """
    <div style="
        position: fixed;
        top: 20px;
        left: 20px;
        z-index:9999;
        background:white;
        padding:10px;
        border-radius:8px;
        box-shadow:0 0 10px rgba(0,0,0,0.25);
        font-size:14px;
    ">
        <button onclick="showAll()" style="margin:3px; padding:6px 12px;">All</button>

        <button onclick="showRunning()" style="
            margin:3px; padding:6px 12px;
            background:#FFA000; color:white;
            border:none; border-radius:4px;
        ">
            Running
        </button>

        <button onclick="showCompleted()" style="
            margin:3px; padding:6px 12px;
            background:#4CAF50; color:white;
            border:none; border-radius:4px;
        ">
            Completed
        </button>
    </div>
    """
    m.get_root().html.add_child(folium.Element(filter_buttons))

    # -----------------------------------------------------------
    # Summary Box (Top Right) with counts
    # -----------------------------------------------------------
    now = datetime.now().strftime("%I:%M %p")
    today = datetime.now().strftime("%d-%b-%Y")
    total = len(points)

    completed_count = 0
    running_count   = 0
    assigned_count  = 0

    for (_, _, _, _, _, _, _, _, _, status, _) in points:
        s = (status or "").upper()
        if ("ORDER COMPLETED" in s) or ("ORDER FEEDBACK DONE" in s):
            completed_count += 1
        elif "START JOB" in s:
            running_count += 1
        else:
            assigned_count += 1

    summary_html = f"""
    <div style="
        position: fixed;
        top: 20px;
        right: 20px;
        z-index:9999;
        background:white;
        padding:14px;
        border-radius:10px;
        box-shadow:0 0 10px rgba(0,0,0,0.3);
        font-size:15px;
        text-align:right;
        line-height:1.5;
    ">
        <b style="font-size:16px;">Total Bookings: {total}</b><br>

        <span style="color:#4CAF50; font-weight:bold;">
            Completed: {completed_count}
        </span><br>

        <span style="color:#FFA000; font-weight:bold;">
            Running: {running_count}
        </span><br>

        <span style="color:#1A73E8; font-weight:bold;">
            Assigned: {assigned_count}
        </span><br><br>

        Date: {today}<br>
        Time: {now}<br>
        <i>(Auto-refresh every 30 sec)</i>
    </div>
    """
    m.get_root().html.add_child(folium.Element(summary_html))

    # -----------------------------------------------------------
    # JS: SP highlight + marker groups + filters + live animation
    # -----------------------------------------------------------
    js_lines = [
        "<script>",
        "var spGroups = {};",
        "var allMarkers = [];",
        "var runningMarkers = [];",
        "var completedMarkers = [];",
        "var otherMarkers = [];",
    ]

    for (lat, lng, oid, sp, bt, bd, addr, dist_tl, dist_an, status, total_time), mi in zip(points, markers_info):
        js_var = mi["js_var"]
        sp_js  = mi["sp_js"]
        s = (status or "").upper()

        # master list
        js_lines.append(f"allMarkers.push({js_var});")

        # SP grouping
        js_lines.append(f"spGroups['{sp_js}'] = spGroups['{sp_js}'] || [];")
        js_lines.append(f"spGroups['{sp_js}'].push({js_var});")

        # status grouping
        if "START JOB" in s:
            js_lines.append(f"runningMarkers.push({js_var});")
        elif ("ORDER COMPLETED" in s) or ("ORDER FEEDBACK DONE" in s):
            js_lines.append(f"completedMarkers.push({js_var});")
        else:
            js_lines.append(f"otherMarkers.push({js_var});")

    js_lines.append("""
function highlightSP(spName) {
    // Dim all markers
    Object.keys(spGroups).forEach(function(key) {
        spGroups[key].forEach(function(m) {
            if (m.setOpacity) {
                m.setOpacity(0.2);
            }
            if (m._icon) {
                m._icon.style.filter = "grayscale(70%)";
            }
        });
    });

    // Highlight selected SP
    var group = spGroups[spName] || [];
    group.forEach(function(m) {
        if (m.setOpacity && m.setZIndexOffset) {
            m.setOpacity(1.0);
            m.setZIndexOffset(1000);
        }
        if (m._icon) {
            m._icon.style.filter = "none";
        }
    });
}

function hideAllMarkers() {
    allMarkers.forEach(function(m) {
        if (m._icon) m._icon.style.display = "none";
    });
}

function showMarkers(list) {
    list.forEach(function(m) {
        if (m._icon) m._icon.style.display = "block";
    });
}

function showAll() {
    allMarkers.forEach(function(m) {
        if (m._icon) m._icon.style.display = "block";
        if (m.setOpacity) m.setOpacity(1.0);
        if (m._icon) m._icon.style.filter = "none";
    });
}

function showRunning() {
    hideAllMarkers();
    showMarkers(runningMarkers);
}

function showCompleted() {
    hideAllMarkers();
    showMarkers(completedMarkers);
}

function animateRunning() {
    runningMarkers.forEach(function(m) {
        if (m._icon) {
            m._icon.style.transition = "transform 0.6s ease-in-out";
            m._icon.style.transform = "scale(1.35)";
            setTimeout(() => {
                if (m._icon) m._icon.style.transform = "scale(1.0)";
            }, 600);
        }
    });
}
setInterval(animateRunning, 1000);  // pulse every 1 sec
""")

    js_lines.append("</script>")
    m.get_root().html.add_child(folium.Element("\n".join(js_lines)))

    # -----------------------------------------------------------
    # Auto-refresh Script
    # -----------------------------------------------------------
    refresh_js = """
        <script>
            setTimeout(function(){
                location.reload();
            }, 90000);
        </script>
    """
    m.get_root().html.add_child(folium.Element(refresh_js))

    # -----------------------------------------------------------
    # Save Map
    # -----------------------------------------------------------
    save_path = "today_bookings_map.html"
    m.save(save_path)
    print("map: updated →", save_path)


def generate_map_from_tomorrow_sheet(ws):
    """
    Tomorrow Bookings Map — EXACT SAME UI & LOGIC AS TODAY MAP
    (Custom pins, time badge, total time, popup layout, filters,
     highlight SP, heatmap, summary box, live animation, auto-refresh)
    """

    all_rows = ws.get_all_values()
    if len(all_rows) <= 1:
        print("map-tmrw: no data")
        return

    # -----------------------------------------------------------
    # Header map
    # -----------------------------------------------------------
    header = all_rows[0]
    h = {name: i for i, name in enumerate(header)}

    required = ["Order Id", "Service Provider Name", "Booking Time",
                "Booking Date", "Cx Address", "Lat&Long"]

    for c in required:
        if c not in h:
            print("map-tmrw: missing column:", c)
            return

    col_oid        = h["Order Id"]
    col_sp         = h["Service Provider Name"]
    col_bt         = h["Booking Time"]
    col_bd         = h["Booking Date"]
    col_addr       = h["Cx Address"]
    col_latlng     = h["Lat&Long"]
    col_dist_tl    = h.get("Distance from TL")
    col_dist_an    = h.get("Distance from AN")
    col_status     = h.get("Order Status")
    col_total_time = h.get("Total Time")

    points = []
    heat = []

    # -----------------------------------------------------------
    # Parse rows
    # -----------------------------------------------------------
    for row in all_rows[1:]:
        if col_latlng >= len(row): continue

        latlng = (row[col_latlng] or "").strip()
        if not latlng or "," not in latlng: continue
        try:
            lat, lng = map(float, latlng.split(","))
        except:
            continue

        oid  = row[col_oid] if col_oid < len(row) else ""
        sp   = row[col_sp] if col_sp < len(row) else ""
        bt   = row[col_bt] if col_bt < len(row) else ""
        bd   = row[col_bd] if col_bd < len(row) else ""
        addr = row[col_addr] if col_addr < len(row) else ""

        dist_tl = row[col_dist_tl] if col_dist_tl is not None else ""
        dist_an = row[col_dist_an] if col_dist_an is not None else ""
        status  = row[col_status] if col_status is not None else ""
        total_time = row[col_total_time] if col_total_time is not None else ""

        points.append((lat, lng, oid, sp, bt, bd, addr, dist_tl, dist_an, status, total_time))
        heat.append([lat, lng])

    if not points:
        print("map-tmrw: no valid points")
        return

    # -----------------------------------------------------------
    # Base Map
    # -----------------------------------------------------------
    m = folium.Map(location=[TL_LAT, TL_LNG], zoom_start=12)

    # Hub markers
    folium.Marker([TL_LAT, TL_LNG], popup="TL HUB", icon=folium.Icon(color="green", icon="home")).add_to(m)
    folium.Marker([AN_LAT, AN_LNG], popup="AN HUB", icon=folium.Icon(color="red", icon="home")).add_to(m)

    # -----------------------------------------------------------
    # Helpers (same as Today map)
    # -----------------------------------------------------------
    import math

    def hav(lat1, lon1, lat2, lon2):
        R = 6371.0
        d1 = math.radians(lat2 - lat1)
        d2 = math.radians(lon2 - lon1)
        a = (
            math.sin(d1/2)**2 +
            math.cos(math.radians(lat1)) *
            math.cos(math.radians(lat2)) *
            math.sin(d2/2)**2
        )
        return 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a)) * R

    def icon_color(lat, lng, status):
        s = (status or "").upper()
        if "START JOB" in s: return "orange"
        if "ORDER COMPLETED" in s or "ORDER FEEDBACK DONE" in s: return "green"

        d_tl = hav(lat, lng, TL_LAT, TL_LNG)
        d_an = hav(lat, lng, AN_LAT, AN_LNG)

        if d_tl <= 7: return "beige"
        if d_an <= 7: return "black"
        return "blue"

    def status_badge(s):
        s_up = (s or "").upper()
        if "START JOB" in s_up: color = "#FFA000"
        elif "ORDER COMPLETED" in s_up or "FEEDBACK DONE" in s_up: color = "#4CAF50"
        elif "CANCEL" in s_up: color = "#F44336"
        else: color = "#2196F3"
        return f"""
        <span style="background:{color};
                     padding:3px 10px;border-radius:6px;
                     color:white;font-weight:bold;">
            {s}
        </span>
        """

    def border_color(s):
        s_up = (s or "").upper()
        if "START JOB" in s_up: return "#FFA000"
        if "ORDER COMPLETED" in s_up or "FEEDBACK DONE" in s_up: return "#4CAF50"
        if "CANCEL" in s_up: return "#F44336"
        return "#9E9E9E"

    # -----------------------------------------------------------
    # Add Markers (with custom SP/Time/TotalTime pin like Today map)
    # -----------------------------------------------------------
    markers_info = []

    for (lat, lng, oid, sp, bt, bd, addr, dist_tl, dist_an, status, total_time) in points:

        bcolor = border_color(status)
        pin_color = icon_color(lat, lng, status)

        # Escape SP for JS
        sp_js = (sp or "").replace("'", "\\'")

        gmaps = f"https://www.google.com/maps?q={lat},{lng}"

        # Popup — same as Today map
        popup = f"""
        <div style="display:flex;gap:20px;
                    padding:12px;border:3px solid {bcolor};
                    border-radius:10px;font-size:15px;">
            <div style="min-width:210px;">
                <b>Order:</b> {oid}<br>

                <b>SP:</b>
                <span onclick="highlightSP('{sp_js}')"
                      style="background:#ffeb3b;padding:2px 8px;
                             border-radius:6px;font-weight:bold;cursor:pointer;">
                    {sp}
                </span><br>

                <b style="color:red;">Time:</b>
                <span style="font-weight:bold;color:red;">{bt}</span><br>

                <b>Date:</b> {bd}<br>

                <b>Total Time:</b>
                <span style="font-weight:bold;">{total_time}</span><br>

                <b>Status:</b> {status_badge(status)}<br>

                <a href="{gmaps}" target="_blank"
                   style="display:inline-block;margin-top:10px;
                          padding:6px 10px;background:#1a73e8;
                          color:white;border-radius:4px;
                          text-decoration:none;font-weight:bold;">
                    📍 Open in Google Maps
                </a>
            </div>

            <div style="min-width:260px;">
                <b>Address:</b><br>{addr}<br><br>
                <b>Distance:</b><br>
                • From TL: <b>{dist_tl}</b><br>
                • From AN: <b>{dist_an}</b><br>
            </div>
        </div>
        """

        # Custom floating SP+Time+TotalTime pin (same as Today map)
        circle_html = f"""
        <div style="text-align:center; transform: translate(-20px, -75px);">

            <div style="background:white;border:1px solid #444;border-radius:4px;
                        padding:1px 6px;font-size:11px;font-weight:bold;
                        display:inline-block;margin-bottom:2px;white-space:nowrap;">
                {sp}
            </div>

            <div style="background:white;border:1px solid #999;border-radius:4px;
                        padding:1px 6px;font-size:10px;display:inline-block;
                        margin-bottom:2px;color:#d32f2f;font-weight:bold;">
                {bt}
            </div>

            <div style="background:white;border:1px solid #999;border-radius:4px;
                        padding:1px 6px;font-size:10px;display:inline-block;
                        margin-bottom:4px;color:#000;font-weight:bold;">
                {total_time}
            </div>

            <div style="width:28px;height:28px;background:{pin_color};
                        border-radius:50%;border:3px solid {bcolor};
                        margin:auto;box-shadow:0 0 6px rgba(0,0,0,0.3);">
            </div>

        </div>
        """

        marker = folium.Marker(
            location=[lat, lng],
            popup=popup,
            icon=folium.DivIcon(html=circle_html)
        ).add_to(m)

        markers_info.append({
            "js_var": marker.get_name(),
            "sp_js": sp_js
        })

    # -----------------------------------------------------------
    # Heatmap
    # -----------------------------------------------------------
    HeatMap(heat, radius=18, blur=15).add_to(m)

    # -----------------------------------------------------------
    # Legend (same)
    # -----------------------------------------------------------
    legend_html = """
    <div style="position:fixed;bottom:20px;left:20px;z-index:9999;
                background:white;padding:10px;border-radius:8px;
                box-shadow:0 0 10px #0003;font-size:14px;">
        <b>Legend</b><br>
        <span style="color:green;">●</span> TL HUB<br>
        <span style="color:red;">●</span> AN HUB<br>
        <span style="color:orange;">●</span> START JOB<br>
        <span style="color:green;">●</span> Completed<br>
        <span style="color:beige;">●</span> Near TL<br>
        <span style="color:black;">●</span> Near AN<br>
        <span style="color:blue;">●</span> Normal<br>
    </div>
    """
    m.get_root().html.add_child(folium.Element(legend_html))

    # -----------------------------------------------------------
    # Filter Buttons (same)
    # -----------------------------------------------------------
    filter_controls = """
    <div style="position:fixed;top:20px;left:20px;z-index:9999;
                background:white;padding:10px;border-radius:8px;
                box-shadow:0 0 10px #0003;">
        <button onclick="showAll()" style="margin:3px;padding:6px 12px;">All</button>
        <button onclick="showRunning()" style="margin:3px;padding:6px 12px;background:#FFA000;color:white;">Running</button>
        <button onclick="showCompleted()" style="margin:3px;padding:6px 12px;background:#4CAF50;color:white;">Completed</button>
    </div>
    """
    m.get_root().html.add_child(folium.Element(filter_controls))

    # -----------------------------------------------------------
    # Summary Box — same as today map
    # -----------------------------------------------------------
    now = datetime.now().strftime("%I:%M %p")
    today = datetime.now().strftime("%d-%b-%Y")

    total = len(points)
    completed = sum(1 for p in points if ("COMPLETED" in p[9].upper()) or ("FEEDBACK DONE" in p[9].upper()))
    running   = sum(1 for p in points if "START JOB" in p[9].upper())
    assigned  = total - completed - running

    summary_html = f"""
    <div style="position:fixed;top:20px;right:20px;z-index:9999;
                background:white;padding:14px;border-radius:10px;
                box-shadow:0 0 10px #0003;font-size:15px;text-align:right;">
        <b>Total Bookings: {total}</b><br>
        <span style="color:#4CAF50;font-weight:bold;">Completed: {completed}</span><br>
        <span style="color:#FFA000;font-weight:bold;">Running: {running}</span><br>
        <span style="color:#1A73E8;font-weight:bold;">Assigned: {assigned}</span><br><br>
        Date: {today}<br>
        Time: {now}<br>
        <i>(Auto-refresh every 30 sec)</i>
    </div>
    """
    m.get_root().html.add_child(folium.Element(summary_html))

    # -----------------------------------------------------------
    # JS (highlight SP + filters + running pulse)
    # -----------------------------------------------------------
    js_lines = [
        "<script>",
        "var spGroups={};var allMarkers=[];var runningMarkers=[];var completedMarkers=[];var otherMarkers=[];"
    ]

    for (_, _, _, sp, _, _, _, _, _, status, _), info in zip(points, markers_info):
        js_var = info["js_var"]
        sp_js = info["sp_js"]
        s = (status or "").upper()

        js_lines.append(f"allMarkers.push({js_var});")
        js_lines.append(f"spGroups['{sp_js}']=spGroups['{sp_js}']||[]; spGroups['{sp_js}'].push({js_var});")

        if "START JOB" in s:
            js_lines.append(f"runningMarkers.push({js_var});")
        elif "COMPLETED" in s or "FEEDBACK DONE" in s:
            js_lines.append(f"completedMarkers.push({js_var});")
        else:
            js_lines.append(f"otherMarkers.push({js_var});")

    js_lines.append("""
function highlightSP(sp){
    Object.keys(spGroups).forEach(k=>{
        spGroups[k].forEach(m=>{
            if(m.setOpacity)m.setOpacity(0.2);
            if(m._icon)m._icon.style.filter="grayscale(70%)";
        });
    });
    (spGroups[sp]||[]).forEach(m=>{
        if(m.setOpacity)m.setOpacity(1);
        if(m.setZIndexOffset)m.setZIndexOffset(999);
        if(m._icon)m._icon.style.filter="none";
    });
}

function hideAll(){ allMarkers.forEach(m=>{ if(m._icon)m._icon.style.display="none"; }); }
function showList(list){ list.forEach(m=>{ if(m._icon)m._icon.style.display="block"; }); }

function showAll(){
    allMarkers.forEach(m=>{
        if(m._icon)m._icon.style.display="block";
        if(m.setOpacity)m.setOpacity(1);
        if(m._icon)m._icon.style.filter="none";
    });
}

function showRunning(){ hideAll(); showList(runningMarkers); }
function showCompleted(){ hideAll(); showList(completedMarkers); }

function animateRunning(){
    runningMarkers.forEach(m=>{
        if(m._icon){
            m._icon.style.transition="transform .6s ease-in-out";
            m._icon.style.transform="scale(1.35)";
            setTimeout(()=>{ if(m._icon)m._icon.style.transform="scale(1)"; },600);
        }
    });
}
setInterval(animateRunning,1000);
</script>
    """)

    js_lines.append("</script>")
    m.get_root().html.add_child(folium.Element("\n".join(js_lines)))

    # -----------------------------------------------------------
    # Auto-refresh (same as Today)
    # -----------------------------------------------------------
    m.get_root().html.add_child(folium.Element("""
        <script>
            setTimeout(function(){ location.reload(); }, 90000);
        </script>
    """))

    # -----------------------------------------------------------
    # Save map
    # -----------------------------------------------------------
    m.save("tomorrow_bookings_map.html")
    print("map-tmrw: updated → tomorrow_bookings_map.html")

def generate_today_map_async(ws):
    """Async (background) today map builder."""
    def worker():
        try:
            # FIXED: correct function name
            generate_map_from_sheet(ws)  
            print("map-today: async map build done ✅")
        except Exception as e:
            print("map-today async error:", e)

    threading.Thread(target=worker, daemon=True).start()


def generate_tomorrow_map_async(ws):
    """
    Run tomorrow map generation in a background thread.
    Makes sync_tomorrow_bookings() return instantly.
    """
    def worker():
        try:
            generate_map_from_tomorrow_sheet(ws)
            print("map-tmrw: async map build done ✅")
        except Exception as e:
            print("map-tmrw async error:", e)

    t = threading.Thread(target=worker, daemon=True)
    t.start()




def icon_color(lat, lng):
    import math

    def hav(lat1, lon1, lat2, lon2):
        R = 6371
        d1 = math.radians(lat2 - lat1)
        d2 = math.radians(lon2 - lon1)
        a = (
            math.sin(d1/2)**2 +
            math.cos(math.radians(lat1)) *
            math.cos(math.radians(lat2)) *
            math.sin(d2/2)**2
        )
        return 2 * R * math.atan2(math.sqrt(a), math.sqrt(1 - a))

    d_tl = hav(lat, lng, TL_LAT, TL_LNG)
    d_an = hav(lat, lng, AN_LAT, AN_LNG)

    if d_tl <= 7:
        return "orange"   # Near TL
    if d_an <= 7:
        return "black"    # Near AN
    return "blue"         # Normal

def status_badge(s):
    s_up = s.upper()

    if "START" in s_up or "PROGRESS" in s_up:
        color = "#4CAF50"   # Green
    elif "CANCEL" in s_up or "FAIL" in s_up:
        color = "#F44336"   # Red
    else:
        color = "#2196F3"   # Blue

    return f"""
        <span style="
            background:{color};
            padding:3px 10px;
            border-radius:6px;
            color:white;
            font-weight:bold;
        ">{s}</span>
    """

# ----------------------------------------------------
# PLAIN TEXT Interakt Sender (Delay Alerts only)
# ----------------------------------------------------
def send_interakt_plain_text(phone, message):
    try:
        digits = re.sub(r"\D", "", phone or "")
        if len(digits) < 10:
            print(f"WA TEXT ERROR: invalid phone {phone}")
            return False
        digits = digits[-10:]

        api_key = INTERAKT_API_KEY
        auth_header = base64.b64encode(f"{api_key}:".encode()).decode()

        headers = {
            "Authorization": f"Basic {auth_header}",
            "Content-Type": "application/json"
        }

        payload = {
            "countryCode": "+91",
            "phoneNumber": digits,
            "type": "Text",
            "data": {"message": message}
        }

        resp = requests.post(INTERAKT_URL, json=payload, headers=headers, timeout=20)
        print("wa: delay-alert plain ->", phone, ":", resp.status_code, "|", resp.text)

        return resp.status_code in (200, 201)

    except Exception as e:
        print("Interakt plain text error:", e)
        return False


def is_customer_wa_already_sent(oid):
    try:
        ws = sh.worksheet("BookingState")
        rows = ws.get_all_values()
        for r in rows[1:]:
            if r and r[0] == oid and r[1] == "SENT":
                return True
        return False
    except Exception:
        return False


def mark_customer_wa_sent(oid):
    if oid in CUSTOMER_WA_SENT:
        return   # ⛔ prevent duplicate rows

    ws = sh.worksheet("BookingState")
    ws.append_row([str(oid), "SENT"])
    CUSTOMER_WA_SENT.add(oid)


def load_customer_wa_sent_set():
    try:
        ws = sh.worksheet("BookingState")
    except WorksheetNotFound:
        ws = sh.add_worksheet("BookingState", rows=2000, cols=2)
        ws.update("A1:B1", [["Order Id", "Customer WA Sent"]])
        return set()

    rows = ws.get_all_values()[1:]
    return {r[0].strip() for r in rows if len(r) > 1 and r[1].strip().upper() == "SENT"}


# def sync_tomorrow_bookings():
#     """
#     Ultra-optimized TomorrowBookings sync (with async map):
    
#     - Only ONE sheet read (get_all_values) → no quota error
#     - Updates columns A → J from website
#     - Fetches Total Time ONLY once (when blank)
#     - No WhatsApp / No Interakt
#     - No reset of geocode / nearby / address
#     - Async map generation = sync completes instantly
#     """

#     print("sync: TommorwBookings")

#     ws = ensure_tomorrow_sheet()

#     # -------------------------------------------------
#     # Load Tomorrow bookings page
#     # -------------------------------------------------
#     driver.get(TOMORROW_BOOKINGS_URL)
#     try:
#         sel = wait.until(EC.presence_of_element_located(
#             (By.XPATH, "//select[@name='datatable_length']")
#         ))
#         driver.execute_script(
#             "arguments[0].value='500'; arguments[0].dispatchEvent(new Event('change'));",
#             sel
#         )
#         time.sleep(1.2)
#     except:
#         pass

#     trs = driver.find_elements(By.CSS_SELECTOR, "#datatable tbody tr")

#     # -------------------------------------------------
#     # READ SHEET ONCE (single API read)
#     # -------------------------------------------------
#     existing_vals = _with_backoff(ws.get_all_values)
#     if not existing_vals:
#         return

#     header = existing_vals[0]
#     header_map = _col_map(header)
#     sheet_width = len(header)

#     # Map: OrderID → row index
#     existing_map = {}
#     for idx, row in enumerate(existing_vals[1:], start=2):
#         if row and row[0].strip():
#             existing_map[row[0].strip()] = idx

#     # -------------------------------------------------
#     # PARSE WEB TABLE (A..J)
#     # -------------------------------------------------
#     latest = {}

#     for tr in trs:
#         try:
#             tds = tr.find_elements(By.TAG_NAME, "td")
#             if len(tds) < 17:
#                 continue

#             ul_items = tds[1].find_element(By.TAG_NAME, "ul").find_elements(By.TAG_NAME, "li")
#             oid = ul_items[0].find_element(By.TAG_NAME, "a").text.strip()
#             status = ul_items[2].text.strip() if len(ul_items) > 2 else ""

#             sp_lines = (tds[5].text or "").split("\n")
#             sp_name = sp_lines[0].strip()
#             sp_phone = re.sub(r"\D", "", sp_lines[1])[-10:] if len(sp_lines) > 1 else ""

#             cust_lines = [x.strip() for x in (tds[8].text or "").split("\n") if x.strip()]
#             cname, cmobile, cemail = _parse_customer_format_b(cust_lines)

#             dt_lines = [x.strip() for x in tds[14].text.split("\n") if x.strip()]
#             btime = dt_lines[0] if len(dt_lines) > 0 else ""
#             bdate = dt_lines[1] if len(dt_lines) > 1 else ""

#             total_time = tds[16].text.strip() if tds[16].text else ""

#             latest[oid] = [
#                 oid, status, sp_name, sp_phone,
#                 cname, cmobile, cemail,
#                 btime, bdate, total_time
#             ]

#         except Exception as e:
#             print("tmrw parse error:", e)

#     # -------------------------------------------------
#     # APPLY UPDATES + CONDITIONAL PROGRESS UPDATE
#     # -------------------------------------------------
#     updates = []
#     appends = []

#     total_time_col = header_map.get("Total Time")

#     for oid, first10 in latest.items():

#         if oid in existing_map:
#             row_idx = existing_map[oid]

#             # Update A..J every time
#             updates.append({
#                 "range": f"A{row_idx}:J{row_idx}",
#                 "values": [first10]
#             })

#             # Check Total Time only from memory (no sheet read)
#             if total_time_col is not None:
#                 existing_total = existing_vals[row_idx - 1][total_time_col].strip()

#                 if not existing_total:
#                     try:
#                         update_tomorrow_job_progress_details(
#                             oid=oid,
#                             row_index=row_idx,
#                             ws=ws
#                         )
#                     except Exception as e:
#                         print("tmrw progress update error:", oid, e)

#         else:
#             row = first10[:]
#             if len(row) < sheet_width:
#                 row.extend([""] * (sheet_width - len(row)))
#             appends.append(row)

#     # Batch write
#     if updates:
#         _with_backoff(ws.batch_update, updates)
#     if appends:
#         _with_backoff(ws.append_rows, appends)

#     # -------------------------------------------------
#     # Remove missing orders
#     # -------------------------------------------------
#     remove_missing_orders(ws, set(latest.keys()))

#     # -------------------------------------------------
#     # Formatting
#     # -------------------------------------------------
#     _sort_rows_by_time(ws)
#     _apply_time_highlights(ws)
#     apply_order_status_colors(ws)

#     # -------------------------------------------------
#     # ASYNC MAP GENERATION
#     # -------------------------------------------------
#     # try:
#     #     ws = ensure_tomorrow_sheet()
#     #     generate_tomorrow_map_async(ws)
#     # except Exception as e:
#     #     print("tmrw map async error:", e)

#     print("sync: TommorwBookings done ✅")



def sync_tomorrow_bookings():
    """
    TomorrowBookings Sync (v8.3 – FINAL & WA-SAFE)
    ----------------------------------------------
    • Single sheet read (quota-safe)
    • Updates ONLY columns A → I (WA column preserved)
    • Appends new bookings
    • Fetches Total Time once (if blank)
    • No WhatsApp / Interakt
    • No geo / nearby / address reset
    • Guarded auto-delete (SCRAPE trusted only)
    """

    import time, re

    print("sync: TomorrowBookings")

    ws = ensure_tomorrow_sheet()

    # ==================================================
    # LOAD TOMORROW BOOKINGS PAGE
    # ==================================================
    SCRAPE_OK = True
    driver.get(TOMORROW_BOOKINGS_URL)

    try:
        sel = wait.until(
            EC.presence_of_element_located(
                (By.XPATH, "//select[@name='datatable_length']")
            )
        )
        driver.execute_script(
            "arguments[0].value='500'; arguments[0].dispatchEvent(new Event('change'));",
            sel
        )
        time.sleep(1.2)
    except Exception:
        SCRAPE_OK = False
        print("tmrw scrape warn: pagination selector not confirmed")

    trs = driver.find_elements(By.CSS_SELECTOR, "#datatable tbody tr")
    if not trs:
        SCRAPE_OK = False
        print("tmrw scrape warn: no rows found")

    # ==================================================
    # READ SHEET ONCE
    # ==================================================
    existing_vals = _with_backoff(ws.get_all_values)
    if not existing_vals:
        print("tmrw sheet empty – skip")
        return

    header = existing_vals[0]
    hmap = _col_map(header)
    sheet_width = len(header)

    # WA column index (0-based)
    wa_col = hmap.get("IsWhatsAppLocationMessageSent?")

    # OrderId → row index (1-based)
    existing_map = {
        row[0].strip(): idx
        for idx, row in enumerate(existing_vals[1:], start=2)
        if row and row[0].strip()
    }

    # ==================================================
    # PARSE WEBSITE TABLE (A → I + TotalTime temp)
    # ==================================================
    latest = {}

    if SCRAPE_OK:
        for tr in trs:
            try:
                tds = tr.find_elements(By.TAG_NAME, "td")
                if len(tds) < 17:
                    continue

                ul = tds[1].find_elements(By.TAG_NAME, "li")
                if not ul:
                    continue

                oid = ul[0].find_element(By.TAG_NAME, "a").text.strip()
                if not oid:
                    continue

                status = ul[2].text.strip() if len(ul) > 2 else ""

                sp_lines = (tds[5].text or "").split("\n")
                sp_name = sp_lines[0].strip() if sp_lines else ""
                sp_phone = re.sub(r"\D", "", sp_lines[1])[-10:] if len(sp_lines) > 1 else ""

                cust_lines = [
                    x.strip() for x in (tds[8].text or "").split("\n") if x.strip()
                ]
                cname, cmobile, cemail = _parse_customer_format_b(cust_lines)

                dt_lines = [x.strip() for x in tds[14].text.split("\n") if x.strip()]
                btime = dt_lines[0] if len(dt_lines) > 0 else ""
                bdate = dt_lines[1] if len(dt_lines) > 1 else ""

                total_time = tds[16].text.strip() if tds[16].text else ""

                # NOTE: row9 = ONLY A → I (WA column excluded)
                latest[oid] = {
                    "row9": [
                        oid, status, sp_name, sp_phone,
                        cname, cmobile, cemail,
                        btime, bdate
                    ],
                    "total_time": total_time
                }

            except Exception as e:
                print("tmrw parse error:", e)

    # ==================================================
    # APPLY UPDATES & APPENDS (WA-SAFE)
    # ==================================================
    updates = []
    appends = []
    total_time_col = hmap.get("Total Time")

    for oid, data in latest.items():
        row9 = data["row9"]
        scraped_tt = data["total_time"]

        # ------------------------------
        # EXISTING → UPDATE A:I ONLY
        # ------------------------------
        if oid in existing_map:
            r = existing_map[oid]

            updates.append({
                "range": f"A{r}:I{r}",
                "values": [row9]   # ✅ exactly 9 columns
            })

            # Fetch Total Time only once
            if total_time_col is not None:
                try:
                    existing_tt = (
                        existing_vals[r - 1][total_time_col].strip()
                        if total_time_col < len(existing_vals[r - 1])
                        else ""
                    )
                except Exception:
                    existing_tt = ""

                if not existing_tt and scraped_tt:
                    try:
                        update_tomorrow_job_progress_details(
                            oid=oid,
                            row_index=r,
                            ws=ws
                        )
                    except Exception as e:
                        print("tmrw progress update error:", oid, e)

        # ------------------------------
        # NEW → APPEND (full row, WA blank)
        # ------------------------------
        else:
            new_row = row9[:]
            if len(new_row) < sheet_width:
                new_row.extend([""] * (sheet_width - len(new_row)))
            appends.append(new_row)

    if updates:
        _with_backoff(ws.batch_update, updates)

    if appends:
        _with_backoff(ws.append_rows, appends)
        print(f"tmrw added-new: {len(appends)}")

    # ==================================================
    # SAFE AUTO-DELETE (STRICT GUARD)
    # ==================================================
    if SCRAPE_OK and latest:
        try:
            remove_missing_orders(ws, set(latest.keys()))
        except Exception as e:
            print("tmrw remove-missing error:", e)
    else:
        print("tmrw remove-missing skipped (scrape untrusted)")

    # ==================================================
    # FORMATTING
    # ==================================================
    _sort_rows_by_time(ws)
    _apply_time_highlights(ws)
    apply_order_status_colors(ws)

    print("sync: TomorrowBookings done ✅")


def get_auth_cookies_from_driver(driver):
    cookies = {}
    for c in driver.get_cookies():
        cookies[c["name"]] = c["value"]
    return cookies

def send_tomorrow_customer_whatsapp_messages():
    """
    Send WhatsApp location / confirmation message to customers
    from TommorwBookings sheet (same logic as TodayBookings).
    """

    try:
        ws = sh.worksheet("TommorwBookings")
    except WorksheetNotFound:
        print("❌ TommorwBookings sheet not found")
        return

    rows = _with_backoff(ws.get_all_values)
    if len(rows) <= 1:
        return

    header = rows[0]
    h = _col_map(header)

    REQUIRED = [
        "Order Id",
        "Customer Name",
        "Customer Mobile",
        "IsWhatsAppLocationMessageSent?"
    ]

    if any(c not in h for c in REQUIRED):
        print("❌ Missing required columns in TommorwBookings")
        return

    col_oid   = h["Order Id"]
    col_name  = h["Customer Name"]
    col_phone = h["Customer Mobile"]
    col_flag  = h["IsWhatsAppLocationMessageSent?"] + 1  # 1-based for update

    queued = 0

    for r_idx, row in enumerate(rows[1:], start=2):

        oid   = row[col_oid].strip() if col_oid < len(row) else ""
        cname = row[col_name].strip() if col_name < len(row) else ""
        phone = row[col_phone].strip() if col_phone < len(row) else ""
        flag  = row[h["IsWhatsAppLocationMessageSent?"]].strip() if h["IsWhatsAppLocationMessageSent?"] < len(row) else ""

        if not oid or not phone:
            continue

        # normalize flag
        norm_flag = (
            flag.replace("✅", "")
                .replace("✔️", "")
                .strip()
                .upper()
        )

        # send only if NOT sent
        if norm_flag not in ("", "NOT YET", "FAILED"):
            continue

        TASK_QUEUE.put({
            "type": "customer_whatsapp",
            "ws": ws,
            "phone": phone,
            "cname": cname,
            "col": col_flag,
            "oid": oid,
            "row": r_idx
        })

        queued += 1
        time.sleep(CUSTOMER_SEND_GAP_SECONDS)

    if queued:
        print(f"📨 TomorrowBookings → queued {queued} customer WhatsApp messages")


def _is_between_8pm_1130pm_ist():
    now = datetime.now(IST).time()
    start = dt_time(22, 0)     # 08:00 PM
    end   = dt_time(23, 57)    # 11:30 PM
    return start <= now <= end


def run_tomorrow_whatsapp_windowed():
    if not _is_between_8pm_1130pm_ist():
        print("⏳ Tomorrow WA skipped (outside 8PM–11:30PM window)")
        return

    send_tomorrow_customer_whatsapp_messages()
    # after login success
    AUTH_COOKIES = get_auth_cookies_from_driver(driver)
    
    fetch_top_services_last_7_days_and_save_requests(
        AUTH_COOKIES,
        sh_weekoff,
        "94"
    )


def expo_backoff(func, *args, max_retries=7, **kwargs):
    """
    Handles Google Sheets 429 / timeout / rate-limit with exponential backoff.
    Randomized jitter prevents thundering herd.
    """
    delay = 1.0  # start at 1 sec

    for attempt in range(max_retries):
        try:
            return func(*args, **kwargs)

        except HttpError as e:
            status = getattr(e, "status_code", None)

            # Only backoff on 429 or 5xx (timeout / rate-limit)
            if status in (429, 500, 503):
                print(f"⚠️ Google API rate-limit/timeout (attempt {attempt+1}), retrying in {delay:.2f}s…")
                time.sleep(delay + random.uniform(0, 0.5))
                delay *= 2
                continue

            # other errors → not retryable
            raise

        except Exception as e:
            print("⚠️ Non-HTTP error, retrying:", e)
            time.sleep(delay + random.uniform(0, 0.5))
            delay *= 2
            continue

    print("❌ FAILED even after retries.")
    raise RuntimeError("Google API backoff retry exhausted")



def update_tomorrow_bookings_geo_nearby():
    print("tmrw: geo+nearby update")

    ws = ensure_tomorrow_sheet()

    # READ with exponential backoff
    all_rows = expo_backoff(ws.get_all_values)

    if len(all_rows) <= 1:
        print("tmrw: empty sheet")
        return

    header = all_rows[0]
    h = _col_map(header)

    required = [
        "Order Id", "Booking Time", "Booking Date",
        "Cx Address", "Cx Address Fetched?",
        "Lat&Long", "Distance from TL", "Distance from AN",
        "IsNearbyCalculatedDone", "Nearby Booking 1",
        "Nearby Booking 2", "Nearby Booking 3"
    ]
    for c in required:
        if c not in h:
            print("tmrw: missing column:", c)
            return

    col_oid     = h["Order Id"]
    col_btime   = h["Booking Time"]
    col_bdate   = h["Booking Date"]
    col_addr    = h["Cx Address"]
    col_addr_ok = h["Cx Address Fetched?"]
    col_latlong = h["Lat&Long"]
    col_tl      = h["Distance from TL"]
    col_an      = h["Distance from AN"]
    col_done    = h["IsNearbyCalculatedDone"]
    col_n1      = h["Nearby Booking 1"]
    col_n2      = h["Nearby Booking 2"]
    col_n3      = h["Nearby Booking 3"]

    staged = []
    index_rows = []

    # ------------------------------------------------
    # Build static index (NO Google reads inside loop)
    # ------------------------------------------------
    for r_idx, row in enumerate(all_rows[1:], start=2):
        try:
            oid   = row[col_oid].strip()
            latng = row[col_latlong].strip()
            btime = row[col_btime].strip()
            bdate = row[col_bdate].strip()

            if not (oid and latng and btime and bdate):
                continue

            lat, lng = parse_latlng(latng)
            if lat is None:
                continue

            t_obj, d_obj = smart_parse_time_date(btime, bdate)
            if not (t_obj and d_obj):
                continue

            booking_dt = IST.localize(datetime.combine(d_obj, t_obj))

            index_rows.append({
                "oid": oid,
                "lat": lat,
                "lng": lng,
                "dt": booking_dt,
                "btime": btime,
            })

        except:
            pass

    # ------------------------------------------------
    # Process each row
    # ------------------------------------------------
    for r_idx, row in enumerate(all_rows[1:], start=2):
        try:
            oid = row[col_oid].strip()
            if not oid:
                continue

            cx_addr   = row[col_addr].strip()
            addr_done = row[col_addr_ok].strip()
            latlng    = row[col_latlong].strip()
            dist_tl   = row[col_tl].strip()
            dist_an   = row[col_an].strip()
            near_done = row[col_done].strip()

            btime = row[col_btime].strip()
            bdate = row[col_bdate].strip()

            # -------------------------------
            # 1) Fetch Address
            # -------------------------------
            if addr_done != "✅":
                print(f"tmrw: fetching address for {oid}")

                if click_customer_address_in_tomorrow_page(oid):
                    time.sleep(1)
                    soup = BeautifulSoup(driver.page_source, "html.parser")
                    landmark = extract_customer_address(soup)
                    if landmark:
                        cx_addr = landmark
                        staged.append({
                            "range": f"{_col_letter(col_addr+1)}{r_idx}",
                            "values": [[cx_addr]]
                        })

                staged.append({
                    "range": f"{_col_letter(col_addr_ok+1)}{r_idx}",
                    "values": [["✅"]]
                })

            # -------------------------------
            # 2) Geocode
            # -------------------------------
            if cx_addr and not latlng:
                full_addr = cx_addr
                if "indore" not in full_addr.lower():
                    full_addr += ", Indore, Madhya Pradesh"

                latlng = geocode_address_google(full_addr) or geocode_address_free(full_addr)
                if latlng:
                    staged.append({
                        "range": f"{_col_letter(col_latlong+1)}{r_idx}",
                        "values": [[latlng]]
                    })

            # -------------------------------
            # 3) Distance Matrix
            # -------------------------------
            if latlng and (not dist_tl or not dist_an):
                d_tl = get_driving_distance_km(TL_LATLNG, latlng)
                d_an = get_driving_distance_km(AN_LATLNG, latlng)

                staged.append({
                    "range": f"{_col_letter(col_tl+1)}{r_idx}",
                    "values": [[d_tl]]
                })
                staged.append({
                    "range": f"{_col_letter(col_an+1)}{r_idx}",
                    "values": [[d_an]]
                })

            # -------------------------------
            # 4) Nearby Calculation
            # -------------------------------
            if latlng and near_done != "YES":

                my_lat, my_lng = parse_latlng(latlng)
                t_obj, d_obj = smart_parse_time_date(btime, bdate)
                if not (t_obj and d_obj):
                    continue

                my_dt = IST.localize(datetime.combine(d_obj, t_obj))

                nearby = []
                for other in index_rows:
                    if other["oid"] == oid:
                        continue

                    if other["dt"].date() != my_dt.date():
                        continue
                    if other["dt"] <= my_dt:
                        continue

                    d_km = haversine_km(my_lat, my_lng, other["lat"], other["lng"])
                    if d_km <= 7.0:
                        nearby.append((other["oid"], d_km, other["btime"]))

                nearby.sort(key=lambda x: x[1])
                top = nearby[:3]

                if not top:
                    vals = ["Not Found", "Not Found", "Not Found"]
                else:
                    vals = [
                        f"Orderid {oid2} → {dist:.2f} km ({bt})"
                        for (oid2, dist, bt) in top
                    ]
                    while len(vals) < 3:
                        vals.append("")

                staged.append({
                    "range": f"{_col_letter(col_n1+1)}{r_idx}:{_col_letter(col_n3+1)}{r_idx}",
                    "values": [vals]
                })

                staged.append({
                    "range": f"{_col_letter(col_done+1)}{r_idx}",
                    "values": [["YES"]]
                })

        except Exception as e:
            print("tmrw row error:", e)

    # ------------------------------------------------
    # WRITE with exponential backoff
    # ------------------------------------------------
    if staged:
        expo_backoff(ws.batch_update, staged)

    print("tmrw: geo+nearby done ✅")

# ========== PATCH 3 ==========
def close_tomorrow_detail_page():
    """
    Closes tomorrow order detail modal/page safely.
    """
    try:
        # Case 1: Modal close button
        btn = driver.find_element(By.XPATH, "//button[contains(@class,'close') or @data-dismiss='modal']")
        driver.execute_script("arguments[0].click();", btn)
        time.sleep(0.3)
        return True
    except:
        pass

    try:
        # Case 2: Back button (if new page opened)
        driver.back()
        time.sleep(0.3)
        return True
    except:
        pass

    return False


# ========== PATCH 4 ==========
def update_tomorrow_job_progress_details(oid, row_index, ws):
    """
    Reads job progress from ORDER DETAIL PAGE for TomorrowBookings.
    Updates ONLY progress fields (Start/Stop Job, Total Time, ETA, etc.)
    NO WhatsApp, NO Interakt.
    """
    try:
        # 1) Open detail page
        if not open_order_detail_tomorrow_page(oid):
            return

        time.sleep(0.5)

        # 2) Parse detail page
        soup = BeautifulSoup(driver.page_source, "html.parser")
        data = parse_job_progress_from_detail_page(soup)  # <--- PATCH 1

        if not data:
            return

        # 3) Push updates
        header_map = _col_map(ws.row_values(1))
        staged = []

        for col_name, value in data.items():
            if col_name not in header_map:
                continue

            colIndex = header_map[col_name] + 1

            staged.append({
                "range": f"{_col_letter(colIndex)}{row_index}",
                "values": [[value]]
            })

        if staged:
            _with_backoff(ws.batch_update, staged)

    except Exception as e:
        print("tmrw update progress error:", oid, e)

    finally:
        # 4) Always close modal/page
        close_tomorrow_detail_page()



def parse_job_progress_from_detail_page(soup):
    """
    Extract only 'Total Time' from tomorrow order detail page.
    Returns: {"Total Time": "..."} or empty dict if not found.
    """

    result = {}

    # Find all panel bodies
    panels = soup.find_all("div", class_="panel-body")

    for panel in panels:
        rows = panel.find_all("div", class_="row")

        for row in rows:
            cols = row.find_all("div", class_="col-sm-6")
            if len(cols) != 2:
                continue

            label = cols[0].get_text(strip=True)
            if label.lower() == "total time":
                value = cols[1].get_text(strip=True)

                # Clean: “165 (min)” → “165 min”
                value = value.replace("(min)", "").strip()

                result["Total Time"] = value
                return result   # STOP after finding Total Time

    return result


# ========== PATCH 2 ==========
def open_order_detail_tomorrow_page(oid):
    """
    Opens the ORDER DETAIL PAGE for TomorrowBookings.
    Uses multiple XPaths for maximum reliability.
    """
    try:
        # ----- DIRECT MATCH -----
        xpath1 = f"//a[normalize-space(text())='{oid}']"
        try:
            link = wait.until(EC.element_to_be_clickable((By.XPATH, xpath1)))
            driver.execute_script("arguments[0].scrollIntoView(true);", link)
            driver.execute_script("arguments[0].click();", link)
            return True
        except:
            pass

        # ----- INSIDE <ul><li> -----
        xpath2 = f"//td//ul/li/a[normalize-space(text())='{oid}']"
        try:
            link = wait.until(EC.element_to_be_clickable((By.XPATH, xpath2)))
            driver.execute_script("arguments[0].scrollIntoView(true);", link)
            driver.execute_script("arguments[0].click();", link)
            return True
        except:
            pass

        # ----- FALLBACK: ANY CONTAINER -----
        xpath3 = f"//*[normalize-space(text())='{oid}']"
        try:
            link = wait.until(EC.element_to_be_clickable((By.XPATH, xpath3)))
            driver.execute_script("arguments[0].scrollIntoView(true);", link)
            driver.execute_script("arguments[0].click();", link)
            return True
        except:
            pass

        print(f"tmrw: cannot find clickable ID for {oid}")
        return False

    except Exception as e:
        print(f"tmrw: cannot open detail for {oid}", e)
        return False



from datetime import datetime

def _today_sheet_date_str():
    """
    Returns today's date in the same format as 'Booking Date' column,
    e.g. '28-Nov-2025'.
    """
    return datetime.now(IST).strftime("%d-%b-%Y")


def run_delay_report_if_not_sent():
    today = datetime.now(IST).strftime("%d-%b-%Y")
    
    try:
        state_ws = sh.worksheet("State")
        last_sent = state_ws.acell("C2").value  # store last delay report date in C2
    except Exception:
        last_sent = None

    # Already sent today → DO NOTHING
    if last_sent == today:
        print("🌙 Night check: Delay report already sent today, skipping.")
        return

    print("🌙 Night check running: Delay report NOT sent today → sending now…")

    # Call your main delay report function
    try:
        update_delay_report_sheet_hourly()
    except Exception as e:
        print("⚠️ Error sending night delay report:", e)
        return

    # Mark today's date so it never runs again today
    try:
        state_ws.update_acell("C2", today)
        print("🌙 Night delay report marked as sent.")
    except:
        print("⚠️ Failed to update delay report state.")


def run_daily_delay_report():
    """
    Generate & send Daily Delay Booking Report.
    This function is triggered externally (e.g., APScheduler)
    at specific times, so no internal time-window checking
    is required.

    Includes only rows where DelayAlertSent? = SENT.
    Saves into 'DelayedReport' sheet (with Manager Comment column).
    """
    print("🔵 Checking Daily Delay Booking Report…")

    now = datetime.now(IST)
    today_sheet_date = _today_sheet_date_str()  # e.g. "28-Nov-2025"

    # ---------------------------------------------------------
    # Prevent double sending each day
    # ---------------------------------------------------------
    last_sent = state_get_col(DELAY_REPORT_STATE_KEY, "")
    if last_sent == today_sheet_date:
        print("⏳ Daily Delay Report already sent today — skipping.")
        return

    # ---------------------------------------------------------
    # LOAD TODAY BOOKINGS
    # ---------------------------------------------------------
    ws = ensure_today_sheet()
    all_vals = _with_backoff(ws.get_all_values)

    if len(all_vals) <= 1:
        print("📭 TodayBookings is empty — nothing to report.")
        state_set_col(DELAY_REPORT_STATE_KEY, today_sheet_date)
        return

    header = all_vals[0]
    h = _col_map(header)

    required = (
        "Order Id", "Service Provider Name", "Booking Time",
        "Booking Date", "DelayedMinutes", "DelayAlertSent?"
    )
    missing = [c for c in required if c not in h]
    if missing:
        print("❌ Delay report missing columns:", missing)
        return

    c_oid   = h["Order Id"]
    c_sp    = h["Service Provider Name"]
    c_btime = h["Booking Time"]
    c_bdate = h["Booking Date"]
    c_del   = h["DelayedMinutes"]
    c_alert = h["DelayAlertSent?"]

    # ---------------------------------------------------------
    # GATHER DELAYED ROWS
    # ---------------------------------------------------------
    total_bookings_today = 0
    delayed_rows = []

    for row in all_vals[1:]:
        try:
            bdate = row[c_bdate].strip()
            if bdate != today_sheet_date:
                continue

            total_bookings_today += 1

            # include only if Alert Sent
            alert_flag = row[c_alert].strip().upper() if c_alert < len(row) else ""
            if alert_flag != "SENT":
                continue

            dm_raw = row[c_del].strip()
            if not dm_raw:
                continue

            try:
                dm_val = int(float(dm_raw))
            except:
                continue

            if dm_val <= 0:
                continue

            oid = row[c_oid].strip()
            sp  = row[c_sp].strip()
            bt  = row[c_btime].strip()

            delayed_rows.append((dm_val, oid, sp, bt, bdate))

        except Exception as e:
            print("⚠️ Delay row error:", e)
            continue

    if not delayed_rows:
        print("ℹ️ No delayed bookings with ALERT SENT.")
        state_set_col(DELAY_REPORT_STATE_KEY, today_sheet_date)
        return

    # Sort by delay DESC
    delayed_rows.sort(key=lambda x: x[0], reverse=True)

    # ---------------------------------------------------------
    # SAVE INTO GOOGLE SHEET — DelayedReport
    # ---------------------------------------------------------
    try:
        rep_ws = ensure_delayed_report_sheet()
        rep_vals = _with_backoff(rep_ws.get_all_values)

        if not rep_vals:
            rep_ws.append_row(["Date", "Order Id", "Expert", "Booking Time",
                               "Booking Date", "DelayedMinutes", "Manager Comment"])
            rep_vals = rep_ws.get_all_values()

        # existing OIDs (avoid duplicates)
        existing_oids = set(r[1].strip() for r in rep_vals[1:] if len(r) > 1)

        new_rows = []
        for dm, oid, sp, bt, bdate in delayed_rows:
            if oid not in existing_oids:
                new_rows.append([
                    today_sheet_date,
                    oid,
                    sp,
                    bt,
                    bdate,
                    dm,
                    ""   # Manager Comment (blank)
                ])

        if new_rows:
            _with_backoff(rep_ws.append_rows, new_rows)

        # ---- SORT DATA ----
        rep_vals = _with_backoff(rep_ws.get_all_values)
        header = rep_vals[0]
        rows = rep_vals[1:]

        c_bdate = header.index("Booking Date")
        c_delay = header.index("DelayedMinutes")

        sortable = []
        for r in rows:
            try:
                date_sort = _parse_date_for_sort(r[c_bdate])
                delay_sort = int(r[c_delay])
            except:
                date_sort = datetime.min
                delay_sort = 0

            sortable.append((date_sort, delay_sort, r))

        sortable.sort(key=lambda x: (x[0], x[1]), reverse=True)

        # rewrite sorted
        rep_ws.clear()
        rep_ws.append_row(header)
        rep_ws.append_rows([r[2] for r in sortable])

        print("📄 DelayedReport updated & sorted.")

    except Exception as e:
        print("❌ Error updating DelayedReport sheet:", e)

    # ---------------------------------------------------------
    # BUILD WHATSAPP MESSAGE
    # ---------------------------------------------------------
    timestamp = now.strftime("%I:%M %p")

    lines = [
        f"🛑 *Daily Delay Report — {today_sheet_date}*",
        f"_Generated at {timestamp}_",
        "",
        f"*Total Bookings:* {total_bookings_today}",
        f"*Delayed Bookings (Alert Sent):* {len(delayed_rows)}",
        "",
        "*Experts with delayed start (sorted by delay):*",
        ""
    ]

    for dm, oid, sp, bt, _ in delayed_rows:
        lines.append(f"• *{sp}* — {dm} min late")
        lines.append(f"  Order ID: {oid}")
        lines.append(f"  Booking Time: {bt}")
        lines.append("")

    msg = "\n".join(lines).strip()

    # ---------------------------------------------------------
    # SEND TO MANAGERS
    # ---------------------------------------------------------
    MANAGERS = [
        ("Shraddha",  "7406011400"),
        ("Vikas",     "7406611400"),
        ("Kumkum",   "8305838835"),
        ("Manager",   "9770159033")
    ]

    sent_any = False
    for name, phone in MANAGERS:
        ok = send_interakt_plain_text(phone, msg)
        print(f"WA Delay Report → {name} ({phone}) → {ok}")
        if ok:
            sent_any = True

    if sent_any:
        state_set_col(DELAY_REPORT_STATE_KEY, today_sheet_date)
        print("✅ Daily Delay Report successfully sent & marked.")
    else:
        print("❌ Delay Report failed — will retry next run.")




def compute_row_hash(obj):
    """
    Compute a stable hash for a dict using sorted keys.
    Used to detect when an invoice row changed.
    """
    import hashlib
    try:
        blob = json.dumps(obj, sort_keys=True, ensure_ascii=False)
    except Exception:
        blob = str(obj)
    return hashlib.md5(blob.encode("utf-8")).hexdigest()


def detect_changed_invoices(sh):
    """
    Detect which experts have invoices that changed since last run.

    Uses:
    - Today's Payment Collection sheet (🧾 Payment Collection Report - dd/mm/yy)
    - A JSON map stored in State['PaymentMessagesHashMap']:
        { "invoice_id": "row_hash_md5", ... }

    Returns:
        set of expert names whose rows changed.
    """
    ws = _get_today_payment_sheet(sh)
    if ws is None:
        print("⚠️ No Payment Collection sheet for today — skipping PaymentMessages.")
        return set()

    try:
        rows = ws.get_all_records()
    except Exception as e:
        print("⚠️ Error reading payment sheet:", e)
        return set()

    current_map = {}      # invoice_id -> hash
    invoice_expert = {}   # invoice_id -> expert

    for r in rows:
        invoice_id = str(r.get("Invoice No.") or "").strip()
        expert = (r.get("Service Provider") or "").strip()

        if not invoice_id or not expert:
            continue

        # Only hash the fields that matter for messages
        subset = {
            "Invoice No.": invoice_id,
            "Date": r.get("Date"),
            "Time": r.get("Time"),
            "Service Provider": expert,
            "Cash Collected": r.get("Cash Collected"),
            "Cash Collected by Person": r.get("Cash Collected by Person"),
            "Cash Pending": r.get("Cash Pending"),
            "Cash Pending with Person": r.get("Cash Pending with Person"),
            "Lifashi Scanner Online Collected": r.get("Lifashi Scanner Online Collected"),
            "Prepaid/UPI": r.get("Prepaid/UPI"),
            "Remark": r.get("Remark"),
        }

        row_hash = compute_row_hash(subset)
        current_map[invoice_id] = row_hash
        invoice_expert[invoice_id] = expert

    # Load previous hash map from State
    prev_json = state_get_col(PAYMENT_HASH_STATE_KEY, "{}")
    try:
        prev_map = json.loads(prev_json) if prev_json else {}
    except Exception:
        prev_map = {}

    changed_experts = set()

    # Compare current vs previous hashes
    for inv_id, h in current_map.items():
        old_h = prev_map.get(inv_id)
        if old_h != h:
            changed_experts.add(invoice_expert[inv_id])

    # Save new snapshot
    try:
        state_set_col(PAYMENT_HASH_STATE_KEY, json.dumps(current_map))
    except Exception as e:
        print("⚠️ Failed to update payment hash state:", e)

    return changed_experts


def _parse_amount(val):
    """
    Convert numeric-ish cell to float. Blank/invalid -> 0.
    """
    if val is None:
        return 0.0
    if isinstance(val, (int, float)):
        return float(val)
    s = str(val).strip()
    if not s:
        return 0.0
    s = s.replace(",", "")
    try:
        return float(s)
    except Exception:
        return 0.0


def format_payment_fields(r):
    """
    Creates a beautifully formatted payment block for ONE invoice row.
    Returns multi-line WhatsApp-formatted text.
    """

    # Extract values safely
    prepaid          = float(r.get("Prepaid/UPI") or 0)
    scanner          = float(r.get("Lifashi Scanner Online Collected") or 0)
    cash_collected   = float(r.get("Cash Collected") or 0)
    cash_col_by      = str(r.get("Cash Collected by Person") or "").strip()
    cash_pending     = float(r.get("Cash Pending") or 0)
    cash_pending_by  = str(r.get("Cash Pending with Person") or "").strip()

    lines = []

    # PREPAID
    if prepaid > 0:
        lines.append(f"💳 *Prepaid/UPI:* **₹{int(prepaid)}**")

    # SCANNER
    if scanner > 0:
        lines.append(f"📲 *Lifashi Scanner Online Collected:* **₹{int(scanner)}**")

    # CASH COLLECTED
    if cash_collected > 0:
        if cash_col_by:
            lines.append(
                f"💰 *Cash Collected:* **₹{int(cash_collected)}**\n"
                f"   👤 *Collected by:* {cash_col_by}"
            )
        else:
            lines.append(f"💰 *Cash Collected:* **₹{int(cash_collected)}**")

    # CASH PENDING
    if cash_pending > 0:
        if cash_pending_by:
            lines.append(
                f"⛔ *Cash Pending:* **₹{int(cash_pending)}**\n"
                f"   👤 *With Person:* {cash_pending_by}"
            )
        else:
            lines.append(f"⛔ *Cash Pending:* **₹{int(cash_pending)}**")

    # If no fields
    return "\n".join(lines) if lines else ""


def get_expert_mobile_map():
    """
    Build map: Service Provider Name -> Mobile (10-digit) from TodayBookings.
    """
    ws_tb = ensure_today_sheet()
    all_vals = _with_backoff(ws_tb.get_all_values)
    if not all_vals:
        return {}

    header = all_vals[0]
    h = _col_map(header)
    c_name = h.get("Service Provider Name")
    c_mobile = h.get("Service Provider Mobile")

    if c_name is None or c_mobile is None:
        return {}

    mapping = {}
    for row in all_vals[1:]:
        if len(row) <= max(c_name, c_mobile):
            continue
        name = row[c_name].strip()
        mobile_raw = row[c_mobile].strip()
        if not name or not mobile_raw:
            continue

        digits = re.sub(r"\D", "", mobile_raw)
        if len(digits) >= 10:
            mapping[name] = digits[-10:]

    return mapping


def update_payment_messages_sheet(sh, final_messages):
    """
    Write PaymentMessages sheet with columns:
    Expert Name | Mobile | Message
    Only for experts present in `final_messages`.
    """
    try:
        try:
            ws_msg = sh.worksheet("PaymentMessages")
        except WorksheetNotFound:
            ws_msg = sh.add_worksheet("PaymentMessages", rows=200, cols=3)

        expert_mobile = get_expert_mobile_map()

        rows = [["Expert Name", "Mobile", "Message"]]
        for expert in sorted(final_messages.keys()):
            msg = final_messages[expert]
            mobile = expert_mobile.get(expert, "")
            rows.append([expert, mobile, msg])

        ws_msg.clear()
        _with_backoff(ws_msg.update, "A1", rows)
        print(f"✅ PaymentMessages sheet updated for {len(final_messages)} experts.")
    except Exception as e:
        print("❌ Error updating PaymentMessages sheet:", e)


def process_payment_messages_partial(sh, changed_experts):
    """
    Build BEAUTIFIED WhatsApp-style payment messages ONLY for experts in `changed_experts`,
    using today's Payment Collection sheet.
    """

    ws_pay = _get_today_payment_sheet(sh)
    if ws_pay is None:
        return {}

    try:
        rows = ws_pay.get_all_records()
    except Exception as e:
        print("⚠️ Error reading payment sheet:", e)
        return {}

    expert_messages = {}

    for r in rows:
        # Expert
        expert = str(r.get("Service Provider") or "").strip()
        if not expert or expert not in changed_experts:
            continue

        # Invoice No.
        invoice = str(r.get("Invoice No.") or "").strip()
        if not invoice:
            continue

        # Time Slot
        time_slot = str(r.get("Time") or "").strip()

        # Payment fields
        payment_text = format_payment_fields(r)
        if not payment_text:
            continue  # skip 0-value invoices

        # HEADER (create if not exists)
        if expert not in expert_messages:
            expert_messages[expert] = [
                f"✨👩‍💼 *{expert} – Payment Summary* ✨",
                "",
                "📌 *Today’s Completed Jobs:*",
                ""
            ]

        # Count items for numbering
        existing_items = [
            line for line in expert_messages[expert] if "🕒" in line
        ]
        number = len(existing_items) + 1

        # Indent nested payment lines
        indented = payment_text.replace("\n", "\n    ")

        # Append beautified block
        expert_messages[expert].append(
            f"{number}️⃣ *ID:* **{invoice}**\n"
            f"    🕒 **{time_slot}**\n"
            f"    {indented}"
        )

    # FINAL OUTPUT BUILD
    final_messages = {}

    for expert, lines in expert_messages.items():
        msg = "\n".join(lines)
        msg += (
            "\n\n⚠️ **अगर पेमेंट से संबंधित कुछ भी गलती लगे, "
            "तो इसी संदेश का जवाब *Vikas sir* को दें।**"
        )
        final_messages[expert] = msg

    return final_messages



def run_payment_messages_job():
    """
    APScheduler entrypoint:
    - Detect changed invoices by hash (State sheet)
    - Regenerate messages only for affected experts
    - Update PaymentMessages sheet
    """
    print("🟦 PaymentMessages Job Triggered…")

    try:
        changed_experts = detect_changed_invoices(sh)
    except Exception as e:
        print("❌ detect_changed_invoices error:", e)
        return

    if not changed_experts:
        print("⏸ No invoice changes → Skipping PaymentMessages")
        return

    print(f"🆕 Changed experts detected: {', '.join(sorted(changed_experts))}")

    final_messages = process_payment_messages_partial(sh, changed_experts)
    if not final_messages:
        print("ℹ️ No messages built after filter — skipping sheet update.")
        return

    update_payment_messages_sheet(sh, final_messages)



def update_delay_report_sheet_hourly():
    """
    Update DelayedReport sheet every hour with latest delayed bookings.
    No WhatsApp, no daily state check.
    """
    print("🔄 Hourly delayed report sheet update…")

    today_sheet_date = _today_sheet_date_str()
    ws = ensure_today_sheet()
    all_vals = _with_backoff(ws.get_all_values)

    if len(all_vals) <= 1:
        print("📭 TodayBookings empty.")
        return

    header = all_vals[0]
    h = _col_map(header)

    required = ("Order Id","Service Provider Name","Booking Time",
                "Booking Date","DelayedMinutes","DelayAlertSent?")
    missing = [c for c in required if c not in h]
    if missing:
        print("❌ Missing columns:", missing)
        return

    c_oid   = h["Order Id"]
    c_sp    = h["Service Provider Name"]
    c_btime = h["Booking Time"]
    c_bdate = h["Booking Date"]
    c_del   = h["DelayedMinutes"]
    c_alert = h["DelayAlertSent?"]

    # Collect
    delayed_rows = []
    for r in all_vals[1:]:
        try:
            if r[c_bdate].strip() != today_sheet_date:
                continue

            if r[c_alert].strip().upper() != "SENT":
                continue

            dm_raw = r[c_del].strip()
            if not dm_raw:
                continue

            try:
                dm = int(float(dm_raw))
            except:
                continue

            if dm <= 0:
                continue

            delayed_rows.append((
                dm,
                r[c_oid].strip(),
                r[c_sp].strip(),
                r[c_btime].strip(),
                today_sheet_date
            ))

        except Exception as e:
            print("⚠️ Row parse error:", e)

    # Sheet update
    try:
        rep_ws = ensure_delayed_report_sheet()
        rep_vals = _with_backoff(rep_ws.get_all_values)

        if not rep_vals:
            rep_ws.append_row(["Date","Order Id","Expert","Booking Time",
                               "Booking Date","DelayedMinutes","Manager Comment"])
            rep_vals = _with_backoff(rep_ws.get_all_values)

        existing_oids = {r[1].strip() for r in rep_vals[1:] if len(r) > 1}

        new_rows = []
        for dm, oid, sp, bt, bdate in delayed_rows:
            if oid not in existing_oids:
                new_rows.append([bdate, oid, sp, bt, bdate, dm, ""])

        if new_rows:
            _with_backoff(rep_ws.append_rows, new_rows)

        print(f"📄 Hourly update done. Added {len(new_rows)} new delayed rows.")

    except Exception as e:
        print("❌ Error updating hourly:", e)


# Global tracker (put near top of file)
last_payment_msg_sent_date = None


def call_payment_messages_once_nightly():
    """
    Call send_payment_messages_once() only once per day
    between 22:30 and 23:45 IST.
    """
    global last_payment_msg_sent_date

    now = datetime.now(IST)
    today_str = now.strftime("%Y-%m-%d")
    current_time = now.time()

    # Use dt_time (datetime.time), NOT time module
    start_time = dt_time(21, 30)   # 10:30 PM
    end_time   = dt_time(23, 45)   # 11:45 PM

    # Already sent today? do nothing
    if last_payment_msg_sent_date == today_str:
        return

    # Not in allowed window? do nothing
    if not (start_time <= current_time <= end_time):
        return

    # Inside window + not yet sent → send once
    try:
        print("⏳ Sending Payment Summary Messages (night window)…")
        send_payment_messages_once()
        last_payment_msg_sent_date = today_str
        print("✔ Payment Summary Messages sent for today.")
    except Exception as e:
        print("⚠️ Error in call_payment_messages_once_nightly:", e)


# Local guard to avoid duplicate WA queueing inside this sync cycle
_SYNC_WA_CACHE = set()   # keys: (row, phone)




def restore_customer_wa_flags(ws):
    values = ws.get_all_values()
    if len(values) <= 1:
        return

    header = values[0]
    h = {c: i for i, c in enumerate(header)}

    if "Order Id" not in h or "IsWhatsAppLocationMessageSent?" not in h:
        return

    col_oid  = h["Order Id"]
    col_flag = h["IsWhatsAppLocationMessageSent?"]

    updates = []

    for r, row in enumerate(values[1:], start=2):
        oid = row[col_oid].strip() if col_oid < len(row) else ""
        if oid and oid in CUSTOMER_WA_SENT:
            updates.append({
                "range": f"{_col_letter(col_flag+1)}{r}",
                "values": [["SENT"]]
            })

    if updates:
        ws.batch_update(updates)
        print(f"🔄 Restored WA flags for {len(updates)} rows")


def sync_today_bookings():
    """
    TODAY BOOKINGS SYNC (v8.3 – STABLE & IDEMPOTENT)
    ------------------------------------------------
    • Append new bookings
    • Update existing bookings
    • Guarded auto-delete (scrape trusted only)
    • Auto-detect Booking Time & Date
    • Customer WhatsApp queue flushed once
    • Delay calculation preserved
    • Background-worker safe
    """

    import datetime, time, re

    print("sync: TodayBookings")

    # ==================================================
    # Helpers
    # ==================================================
    def _norm(v):
        return (
            str(v or "")
            .replace("✔️", "").replace("✅", "")
            .replace("\xa0", " ")
            .replace("\n", "").replace("\r", "").replace("\t", "")
            .strip().upper()
        )

    def _should_send(v):
        return _norm(v) in ("", "NOT YET", "FAILED")

    def _pad(row, n):
        return row + [""] * (n - len(row)) if len(row) < n else row[:n]

    def _build_existing(values, hmap):
        """
        Build OrderId → metadata map
        """
        out = {}
        for idx, row in enumerate(values[1:], start=2):
            if not row or not str(row[0]).strip():
                continue

            oid = row[0].strip()

            def _get(col):
                return row[col] if col is not None and col < len(row) else ""

            out[oid] = {
                "row": idx,
                "wa": _get(hmap.get("IsWhatsAppLocationMessageSent?")),
            }
        return out

    # ==================================================
    # LOAD + NORMALIZE SHEET
    # ==================================================
    ws = ensure_today_sheet()
    sheet = _with_backoff(ws.get_all_values) or [TB_HEADERS]

    header = sheet[0]
    hmap = _col_map(header)

    # Ensure delay columns exist
    for col in ("DelayedMinutes", "DelayAlertSent?"):
        if col not in header:
            header.append(col)

    _with_backoff(ws.update, "1:1", [header])
    sheet = _with_backoff(ws.get_all_values)

    header = sheet[0]
    hmap = _col_map(header)
    total_cols = len(header)

    existing = _build_existing(sheet, hmap)

    # ==================================================
    # SCRAPE TODAY BOOKINGS
    # ==================================================
    driver.get(TODAY_BOOKINGS_URL)
    SCRAPE_OK = True

    try:
        sel = wait.until(
            EC.presence_of_element_located(
                (By.XPATH, "//select[@name='datatable_length']")
            )
        )
        driver.execute_script(
            "arguments[0].value='500'; arguments[0].dispatchEvent(new Event('change'));",
            sel
        )
        wait.until(lambda d: len(d.find_elements(By.CSS_SELECTOR, "#datatable tbody tr")) > 0)
    except Exception:
        SCRAPE_OK = False
        print("today scrape warn: pagination not confirmed")

    trs = driver.find_elements(By.CSS_SELECTOR, "#datatable tbody tr")
    if not trs:
        SCRAPE_OK = False
        print("today scrape warn: no rows found")

    latest = {}

    for tr in trs:
        try:
            tds = tr.find_elements(By.TAG_NAME, "td")
            if len(tds) < 9:
                continue

            ul = tds[1].find_elements(By.TAG_NAME, "li")
            if not ul:
                continue

            oid = ul[0].find_element(By.TAG_NAME, "a").text.strip()
            if not oid:
                continue

            status = ul[2].text.strip() if len(ul) > 2 else ""

            sp_lines = (tds[5].text or "").split("\n")
            sp_name = sp_lines[0].strip() if sp_lines else ""
            sp_phone = re.sub(r"\D", "", sp_lines[1])[-10:] if len(sp_lines) > 1 else ""

            cust_lines = [
                x.strip() for x in (tds[8].text or "").split("\n") if x.strip()
            ]
            cname, cmobile, cemail = _parse_customer_format_b(cust_lines)

            raw = " ".join(td.text for td in tds if td.text)
            m_time = re.search(r"(\d{1,2}:\d{2}\s*(AM|PM))", raw, re.I)
            m_date = re.search(r"(\d{1,2}-[A-Za-z]{3}-\d{4})", raw)

            btime, bdate = _parse_time_date_strs_for_sheet(
                m_time.group(1).upper() if m_time else "",
                m_date.group(1) if m_date else ""
            )

            latest[oid] = [
                oid, status, sp_name, sp_phone,
                cname, cmobile, cemail,
                btime, bdate
            ]

        except Exception as e:
            print("today scrape row error:", e)

    # ==================================================
    # SAFE AUTO-DELETE (STRICTLY GUARDED)
    # ==================================================
    if SCRAPE_OK and latest:
        missing = [oid for oid in existing if oid not in latest]
        if missing and len(missing) < len(existing):
            for r in sorted([existing[o]["row"] for o in missing], reverse=True):
                _with_backoff(ws.delete_rows, r)
            print(f"remove-missing: deleted {len(missing)} rows")

            sheet = _with_backoff(ws.get_all_values)
            existing = _build_existing(sheet, hmap)
        else:
            print("remove-missing: skipped (unsafe)")
    else:
        print("remove-missing: skipped (scrape untrusted)")

    # ==================================================
    # APPLY UPDATES / APPENDS + BUILD WA QUEUE
    # ==================================================
    updates = []
    appends = []
    wa_tasks = []

    for oid, row9 in latest.items():

        # ----------------------------
        # EXISTING → UPDATE
        # ----------------------------
        if oid in existing:
            r = existing[oid]["row"]
            updates.append({
                "range": f"A{r}:I{r}",
                "values": [row9]
            })

            if row9[5] and _should_send(existing[oid]["wa"]):
                wa_tasks.append((r, row9[5], row9[4], oid))

        # ----------------------------
        # NEW → APPEND
        # ----------------------------
        else:
            new_row = [""] * total_cols
            for i, v in enumerate(row9):
                new_row[i] = v

            if hmap.get("IsWhatsAppLocationMessageSent?") is not None:
                new_row[hmap["IsWhatsAppLocationMessageSent?"]] = "NOT YET"

            appends.append(_pad(new_row, total_cols))

            if row9[5]:
                wa_tasks.append((None, row9[5], row9[4], oid))

    if updates:
        _with_backoff(ws.batch_update, updates)

    if appends:
        _with_backoff(ws.append_rows, appends)
        print(f"added-new: {len(appends)}")

    # ==================================================
    # FLUSH CUSTOMER WHATSAPP QUEUE (IDEMPOTENT)
    # ==================================================
    wa_col = hmap.get("IsWhatsAppLocationMessageSent?", 0) + 1

    for r, phone, cname, oid in wa_tasks:
        TASK_QUEUE.put({
            "type": "customer_whatsapp",
            "ws": ws,
            "row": r,
            "phone": phone,
            "cname": cname,
            "oid": oid,
            "col": wa_col
        })

    print(f"wa queued: {len(wa_tasks)}")

    # ==================================================
    # FORMATTING
    # ==================================================
    _apply_time_highlights(ws)
    apply_order_status_colors(ws)

    print("sync: TodayBookings done ✅")


# ===============================
# JOB DETAIL REFRESH (ONLY WHILE START JOB)
# ===============================
DT_FORMAT_A = "%d-%b-%Y %I:%M %p"

# def _find_detail_value(soup, *labels):
#     labels = [l.strip().lower() for l in labels]
#     for row in soup.select("div.panel-body div.row"):
#         cols = row.find_all("div", recursive=False)
#         if len(cols) >= 2:
#             left = cols[0].get_text(strip=True).lower()
#             right = cols[-1].get_text(strip=True)
#             for lbl in labels:
#                 if lbl in left:
#                     return right
#     return ""


def _calc_actual_time_taken(start_str, stop_str):
    try:
        if start_str and stop_str:
            dt_start = datetime.strptime(start_str, DT_FORMAT_A)
            dt_stop  = datetime.strptime(stop_str,  DT_FORMAT_A)
            diff_minutes = int((dt_stop - dt_start).total_seconds() / 60)
            if diff_minutes >= 0:
                return f"{diff_minutes} min"
    except Exception:
        pass
    return ""


def send_sp_start_job_reminder(phone):
    """
    Sends START JOB Reminder as plain text using send_interakt_plain_text().
    """

    message = (
        "🔔 START JOB Reminder\n\n"
        "कृपया अभी ये 4 बातें ध्यान से फॉलो करें:\n\n"
        "1) अगर क्लाइंट अपने प्रोडक्ट लेकर आई है तो उसका फोटो ग्रुप में भेजें "
        "(न भेजने पर सर आपसे पूछताछ करेंगे)\n\n"
        "2) हमारे कौन-कौन से प्रोडक्ट यूज़ करने हैं और कौन-से पैकेज में नहीं हैं — "
        "यह पहले चेक करें\n\n"
        "3) बुकिंग के बाद कस्टमर सिग्नेचर लेना बहुत ज़रूरी है जिससे यह सुनिश्चित होता है "
        "कि ग्राहक की all belongings सुरक्षित हैं\n\n"
        "4) रेटिंग्स पर फोकस करें — अच्छा काम = अच्छी रेटिंग 🙌"
    )

    return send_interakt_plain_text(phone, message)


def geocode_address_google(address):
    global GEOCODE_TODAY_COUNT, GEOCODE_TODAY_DATE

    if not GOOGLE_GEOCODE_API_KEY:
        return ""

    # Reset daily counter at midnight
    today = datetime.now().date()
    if today != GEOCODE_TODAY_DATE:
        GEOCODE_TODAY_DATE = today
        GEOCODE_TODAY_COUNT = 0

    # Max daily quota check
    if GEOCODE_TODAY_COUNT >= GOOGLE_GEOCODE_DAILY_LIMIT:
        print("GOOGLE-GEOCODE: Daily limit reached → using FREE fallback")
        return ""

    # Cache check
    if address in GEOCODE_CACHE:
        return GEOCODE_CACHE[address]

    try:
        url = "https://maps.googleapis.com/maps/api/geocode/json"
        params = {"address": address, "key": GOOGLE_GEOCODE_API_KEY}

        resp = requests.get(url, params=params, timeout=10).json()

        if resp.get("status") == "OK":
            loc = resp["results"][0]["geometry"]["location"]

            # REMOVE SPACE BETWEEN LAT & LNG
            latlng = f"{loc['lat']},{loc['lng']}"

            GEOCODE_CACHE[address] = latlng
            GEOCODE_TODAY_COUNT += 1

            print("GOOGLE-GEOCODE:", address, "→", latlng)
            return latlng

        print("GOOGLE-GEOCODE FAILURE:", resp.get("status"))
        return ""

    except Exception as e:
        print("GOOGLE-GEOCODE ERROR:", e)
        return ""



def extract_customer_address(soup):
    """
    Extract ONLY the Landmark from the address modal.
    """
    print("DEBUG: extract_customer_address() called")

    try:
        modal = soup.select_one(".cs-address-view-modal-body")
        if not modal:
            print("DEBUG: Modal NOT present in page source")
            return ""

        spans = modal.find_all("span")
        print(f"DEBUG: Found {len(spans)} spans INSIDE MODAL")

        for span in spans:
            key = span.get_text(strip=True).lower()

            if key == "landmark":
                print("DEBUG: Landmark label FOUND")

                lbl = span.find_next("label")
                if lbl:
                    value = lbl.get_text(" ", strip=True)
                    print("DEBUG: Landmark value →", value)

                    if value.lower() != "null" and value.strip():
                        return value.strip()

        print("DEBUG: Landmark NOT found inside modal")
        return ""

    except Exception as e:
        print("extract_customer_address ERROR:", e)
        return ""

def click_customer_address_in_tomorrow_page(oid):
    """
    Visit TomorrowBookings page, expand rows, 
    find Customer Address for given OID, click, and open modal.
    """
    print(f"DEBUG: Searching Customer Address in TomorrowBookings for OID {oid}")

    driver.get(TOMORROW_BOOKINGS_URL)
    time.sleep(1.2)

    # Set table page size to 500
    try:
        select_elem = driver.find_element(By.XPATH, "//select[@name='datatable_length']")
        driver.execute_script(
            "arguments[0].value='500'; arguments[0].dispatchEvent(new Event('change'));",
            select_elem
        )
        time.sleep(1.2)
    except:
        print("DEBUG: Could not set page size=500 on TomorrowBookings")

    # Build xpath (structure same as today)
    xpath = f"//a[text()='{oid}']/ancestor::tr//label[contains(@class,'cs-address-view')]"
    print(f"DEBUG: Tomorrow XPATH → {xpath}")

    try:
        elem = driver.find_element(By.XPATH, xpath)
    except Exception as e:
        print(f"DEBUG: Tomorrow address NOT found for OID {oid}: {e}")
        return False

    # Scroll + click
    try:
        driver.execute_script("arguments[0].scrollIntoView(true);", elem)
        driver.execute_script("arguments[0].click();", elem)
        print("DEBUG: Clicked TomorrowPage customer address")
    except Exception as e:
        print(f"DEBUG: TomorrowPage click fail for OID {oid}: {e}")
        return False

    time.sleep(1.8)
    return True


def click_customer_address_in_today_page(oid):
    """
    Go to TodayBookings page, expand rows, find the Customer Address label 
    for the specific OID, click it, and wait for modal.
    """
    print(f"DEBUG: Searching Customer Address in TodayBookings for OID {oid}")

    # Load today bookings page
    driver.get(TODAY_BOOKINGS_URL)
    time.sleep(1.2)

    # Set page length = 500
    try:
        select_elem = driver.find_element(By.XPATH, "//select[@name='datatable_length']")
        driver.execute_script("arguments[0].value='500'; arguments[0].dispatchEvent(new Event('change'));", select_elem)
        time.sleep(1.3)
    except:
        print("DEBUG: Could not expand to 500 rows")

    # Customer Address label is inside the row that contains the OID link
    xpath = f"//a[text()='{oid}']/ancestor::tr//label[contains(@class,'cs-address-view')]"
    print(f"DEBUG: Using XPATH → {xpath}")

    try:
        elem = driver.find_element(By.XPATH, xpath)
    except Exception as e:
        print(f"DEBUG: Customer Address element NOT found for OID {oid}: {e}")
        return False

    # Scroll + click
    try:
        driver.execute_script("arguments[0].scrollIntoView(true);", elem)
        driver.execute_script("arguments[0].click();", elem)
        print("DEBUG: Clicked Customer Address label")
    except Exception as e:
        print(f"DEBUG: Click failed for OID {oid}: {e}")
        return False

    # Wait for modal to open
    time.sleep(1.8)

    return True

def geocode_address_free(address):
    try:
        url = "https://nominatim.openstreetmap.org/search"
        params = {"q": address, "format": "json", "limit": 1}
        headers = {"User-Agent": "YesMadam-Automation/1.0"}

        time.sleep(1)  # Respect Nominatim rate limits

        resp = requests.get(url, params=params, headers=headers).json()
        if not resp:
            print("FREE-GEOCODE: No result for", address)
            return ""

        # REMOVE SPACE BETWEEN LAT & LNG
        latlng = f"{resp[0]['lat']},{resp[0]['lon']}"

        print("FREE-GEOCODE:", address, "→", latlng)
        return latlng

    except Exception as e:
        print("FREE-GEOCODE ERROR:", e)
        return ""





def _find_detail_value(soup, *labels):
    """
    More robust label finder (works for changed labels also)
    """
    label_variants = [l.strip().lower() for l in labels]

    for row in soup.select("div.panel-body div.row"):
        cols = row.find_all("div", recursive=False)
        if len(cols) < 2:
            continue

        left = cols[0].get_text(" ", strip=True).lower()
        right = cols[1].get_text(" ", strip=True)

        for lbl in label_variants:
            if lbl in left:
                return right

    return ""

# ================================================
# GOOGLE DISTANCE MATRIX API (Driving Distance)
# ================================================

def get_driving_distance_km(origin_latlng, dest_latlng):
    """
    Returns driving distance (fastest route) between origin and destination
    using Google Distance Matrix API + persistent cache.

    origin_latlng = "22.7191,75.8577"
    dest_latlng   = "22.7563,75.9122"

    Returns: "5.23 km"
    """
    global DISTANCE_CACHE

    if not GOOGLE_GEOCODE_API_KEY:
        return ""

    if not origin_latlng or not dest_latlng:
        return ""

    try:
        origin_latlng = origin_latlng.replace(" ", "").strip()
        dest_latlng   = dest_latlng.replace(" ", "").strip()

        cache_key = f"{origin_latlng}|{dest_latlng}"
        if cache_key in DISTANCE_CACHE:
            return DISTANCE_CACHE[cache_key]

        url = "https://maps.googleapis.com/maps/api/distancematrix/json"
        params = {
            "origins": origin_latlng,
            "destinations": dest_latlng,
            "mode": "driving",
            "key": GOOGLE_GEOCODE_API_KEY
        }

        resp = requests.get(url, params=params, timeout=10).json()

        if resp.get("status") != "OK":
            return ""

        element = resp["rows"][0]["elements"][0]
        if element.get("status") != "OK":
            return ""

        meters = element["distance"]["value"]
        km = meters / 1000.0
        dist_str = f"{km:.2f} km"

        DISTANCE_CACHE[cache_key] = dist_str
        _save_distance_cache()

        return dist_str

    except Exception:
        return ""



# -------------------------
# Helper patches for nearby
# -------------------------
import math

def haversine_km(lat1, lon1, lat2, lon2):
    """Return great-circle distance in kilometers between two points."""
    R = 6371.0  # Earth radius km
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    a = math.sin(dphi/2.0)**2 + math.cos(phi1)*math.cos(phi2)*math.sin(dlambda/2.0)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    return R * c

def parse_latlng(latlng_str):
    """Return (lat, lng) floats or (None, None). Accepts 'lat,lng' or 'lat, lng'."""
    if not latlng_str:
        return (None, None)
    try:
        parts = [p.strip() for p in str(latlng_str).split(",")]
        if len(parts) >= 2:
            return (float(parts[0]), float(parts[1]))
    except Exception:
        pass
    return (None, None)

def ensure_nearby_columns(ws, header):
    """
    Ensure 'IsNearbyCalculatedDone' + 'Nearby Booking 1/2/3' exist at end.
    Returns updated header map.
    Uses the header list passed in to avoid extra API calls.
    """
    cols = list(header)
    changed = False
    for cname in ("IsNearbyCalculatedDone", "Nearby Booking 1", "Nearby Booking 2", "Nearby Booking 3"):
        if cname not in cols:
            cols.append(cname)
            changed = True
    if changed:
        _with_backoff(ws.update, "A1", [cols])
        header = _with_backoff(ws.row_values, 1)
    return _col_map(header)

def _format_nearby_entry(oid, km, time_str):
    """
    Format nearby entry like:
      "Orderid 6248030 → 3.10 km (01:00 PM)"
    """
    return f"Orderid {oid} → {km:.2f} km ({time_str})"


# -----------------------------------------
# Rewritten update_job_progress_details()
# -----------------------------------------

def update_job_progress_details():
    """
    Rewritten update_job_progress_details:

    - Start-job reminder (once per row) from IsSP_Start_Job_Reminder_Sent?
    - Scrape timestamps from order detail page (best-effort)
    - Cx Address + Lat&Long + Distance from TL/AN fetched ONLY ONCE,
      controlled by "Cx Address Fetched?"
        * Distances use Google Distance Matrix (fastest driving route)
        * Distances are cached via get_driving_distance_km()
    - Adds Nearby Booking 1..3 (end columns)
    - Nearby is controlled ONLY by "IsNearbyCalculatedDone"
      (NOT by 'Cx Address Fetched?'):
        * Runs when Lat&Long is present AND IsNearbyCalculatedDone != "YES"
        * Only includes same-day FUTURE bookings (booking time greater)
        * Radius filter: 7 km (Haversine)
        * If no nearby found → all three cells = "Not Found"
    - You can recompute nearby for a row by clearing IsNearbyCalculatedDone
      (and optionally Nearby Booking 1/2/3).
    """
    global GEOCODE_TODAY_COUNT, GEOCODE_TODAY_DATE

    print("job: fetch (final rewritten with IsNearbyCalculatedDone & Distance Matrix)")
    ws = ensure_today_sheet()
    all_rows = _with_backoff(ws.get_all_values)
    if len(all_rows) <= 1:
        print("job: empty sheet")
        return

    header = all_rows[0]
    h = _col_map(header)

    # --------------------------------------------------
    # 1) Validate mandatory columns
    # --------------------------------------------------
    required_cols = [
        "Order Id", "Order Status",
        "Service Provider Mobile", "Service Provider Name",
        "Booking Time", "Booking Date",
        "Start Journey", "Stop Journey",
        "Start Job At", "Stop Job At",
        "Total Time", "Actual Time Taken",
        "Cx Address", "Cx Address Fetched?",
        "IsSP_Start_Job_Reminder_Sent?"
    ]
    for c in required_cols:
        if c not in h:
            print("job: missing column:", c)
            return

    # Column indexes (0-based)
    col_oid           = h["Order Id"]
    col_status        = h["Order Status"]
    col_sp_mob        = h["Service Provider Mobile"]
    col_sp_name       = h["Service Provider Name"]
    col_btime         = h["Booking Time"]
    col_bdate         = h["Booking Date"]
    col_start_journey = h["Start Journey"]
    col_stop_journey  = h["Stop Journey"]
    col_start_job     = h["Start Job At"]
    col_stop_job      = h["Stop Job At"]
    col_total_time    = h["Total Time"]
    col_actual_time   = h["Actual Time Taken"]
    col_cx_address    = h["Cx Address"]
    col_cx_flag       = h["Cx Address Fetched?"]
    col_start_alert   = h["IsSP_Start_Job_Reminder_Sent?"]

    # --------------------------------------------------
    # 2) Ensure write columns exist (Lat&Long, Distance from TL/AN)
    # --------------------------------------------------
    def ensure_column_local(colname: str) -> int:
        nonlocal header, h
        if colname not in h:
            new_col_idx_1based = len(header) + 1
            ws.update_cell(1, new_col_idx_1based, colname)
            header = _with_backoff(ws.row_values, 1)
            h = _col_map(header)
        return h[colname]

    col_latlong = ensure_column_local("Lat&Long")
    col_dist_tl = ensure_column_local("Distance from TL")
    col_dist_an = ensure_column_local("Distance from AN")

    # --------------------------------------------------
    # 3) Ensure nearby-related columns exist
    # --------------------------------------------------
    h = ensure_nearby_columns(ws, header)
    col_near_done = h["IsNearbyCalculatedDone"]
    col_near_1    = h["Nearby Booking 1"]
    col_near_2    = h["Nearby Booking 2"]
    col_near_3    = h["Nearby Booking 3"]

    # --------------------------------------------------
    # 4) Reset daily geocode counter at midnight
    # --------------------------------------------------
    today = datetime.now().date()
    if today != GEOCODE_TODAY_DATE:
        GEOCODE_TODAY_DATE = today
        GEOCODE_TODAY_COUNT = 0

    # Helper for safe cell access
    def safe(row, col_idx):
        return row[col_idx].strip() if col_idx < len(row) and row[col_idx] else ""

    # --------------------------------------------------
    # 5) Build index for nearby bookings (rows that ALREADY have Lat&Long)
    # --------------------------------------------------
    index_rows = []
    for r_idx, row in enumerate(all_rows[1:], start=2):
        try:
            oid   = safe(row, col_oid)
            latng = safe(row, col_latlong)
            btime = safe(row, col_btime)
            bdate = safe(row, col_bdate)
            if not (oid and latng and btime and bdate):
                continue

            lat, lng = parse_latlng(latng)
            if lat is None:
                continue

            t_obj, d_obj = smart_parse_time_date(btime, bdate)
            booking_dt = IST.localize(datetime.combine(d_obj, t_obj)) if (t_obj and d_obj) else None

            index_rows.append({
                "oid":        oid,
                "lat":        lat,
                "lng":        lng,
                "row":        r_idx,
                "booking_dt": booking_dt,
                "btime":      btime,
            })
        except Exception:
            continue

    # --------------------------------------------------
    # 6) Main per-row processing loop
    # --------------------------------------------------
    staged_updates = []

    for r_idx, row in enumerate(all_rows[1:], start=2):
        try:
            oid = safe(row, col_oid)
            if not oid:
                continue

            status      = safe(row, col_status).upper()
            sp_mob      = safe(row, col_sp_mob)
            sp_name     = safe(row, col_sp_name)
            cx_addr     = safe(row, col_cx_address)
            cx_done     = safe(row, col_cx_flag)
            latlng      = safe(row, col_latlong)
            dist_tl     = safe(row, col_dist_tl)
            dist_an     = safe(row, col_dist_an)
            nearby_done = safe(row, col_near_done)

            # ----------------------------------------
            # 6.1 Start-job reminder (once per row)
            # ----------------------------------------
            if (
                status == "START JOB"
                and safe(row, col_start_job)
                and not safe(row, col_start_alert)
            ):
                if send_sp_start_job_reminder(sp_mob):
                    staged_updates.append({
                        "range": f"{_col_letter(col_start_alert + 1)}{r_idx}",
                        "values": [["SENT ✅"]]
                    })

            # ----------------------------------------
            # 6.2 Scrape job detail timestamps (best effort)
            # ----------------------------------------
            try:
                driver.get(ORDER_DETAIL_URL.format(oid=oid))
                time.sleep(0.9)

                soup = BeautifulSoup(driver.page_source, "html.parser")

                v_sj     = _find_detail_value(soup, "Start Journey") or safe(row, col_start_journey)
                v_ej     = _find_detail_value(soup, "Stop Journey")  or safe(row, col_stop_journey)
                v_sj2    = _find_detail_value(soup, "Start Job At")  or safe(row, col_start_job)
                v_ej2    = _find_detail_value(soup, "Stop Job At")   or safe(row, col_stop_job)
                v_total  = _find_detail_value(soup, "Total Time")    or safe(row, col_total_time)
                v_actual = _calc_actual_time_taken(v_sj2, v_ej2) if (v_sj2 and v_ej2) else safe(row, col_actual_time)

            except Exception as e:
                print("ERROR scraping:", oid, e)
                v_sj     = safe(row, col_start_journey)
                v_ej     = safe(row, col_stop_journey)
                v_sj2    = safe(row, col_start_job)
                v_ej2    = safe(row, col_stop_job)
                v_total  = safe(row, col_total_time)
                v_actual = safe(row, col_actual_time)

            # ----------------------------------------
            # 6.3 Cx Address + Geocode + Distances
            #     Controlled ONLY by "Cx Address Fetched?"
            # ----------------------------------------
            if cx_done != "✅":
                print(f"DEBUG: Fetching Cx Address & distances → OID {oid}")

                # 6.3.1 Click Customer Address label on TodayBookings page → extract Landmark
                if click_customer_address_in_today_page(oid):
                    time.sleep(0.9)
                    soup2 = BeautifulSoup(driver.page_source, "html.parser")
                    landmark = extract_customer_address(soup2)
                    if landmark:
                        cx_addr = landmark
                        staged_updates.append({
                            "range": f"{_col_letter(col_cx_address + 1)}{r_idx}",
                            "values": [[cx_addr]]
                        })
                    # Try closing modal (best effort)
                    try:
                        driver.find_element(By.CSS_SELECTOR, "button.close").click()
                    except Exception:
                        pass

                # 6.3.2 Geocode ONLY if we have an address & no Lat&Long yet
                if cx_addr and not latlng:
                    addr = cx_addr
                    if "indore" not in addr.lower():
                        addr += ", Indore, Madhya Pradesh"

                    latlng = geocode_address_google(addr) or geocode_address_free(addr)
                    if latlng:
                        staged_updates.append({
                            "range": f"{_col_letter(col_latlong + 1)}{r_idx}",
                            "values": [[latlng]]
                        })

                # 6.3.3 Distances from TL/AN (fastest driving route via Distance Matrix)
                #       FETCH ONLY ONCE (when distance cells empty)
                if latlng and (not dist_tl or not dist_an):
                    # origin = office, destination = customer
                    d_tl = get_driving_distance_km(TL_LATLNG, latlng)
                    d_an = get_driving_distance_km(AN_LATLNG, latlng)

                    staged_updates.append({
                        "range": f"{_col_letter(col_dist_tl + 1)}{r_idx}",
                        "values": [[d_tl]]
                    })
                    staged_updates.append({
                        "range": f"{_col_letter(col_dist_an + 1)}{r_idx}",
                        "values": [[d_an]]
                    })

                # 6.3.4 Mark address block as done so it never repeats
                staged_updates.append({
                    "range": f"{_col_letter(col_cx_flag + 1)}{r_idx}",
                    "values": [["✅"]]
                })

            # # ----------------------------------------
            # # 6.4 Nearby bookings (ONLY via IsNearbyCalculatedDone)
            # # ----------------------------------------
            # if latlng and nearby_done != "YES":
            #     my_lat, my_lng = parse_latlng(latlng)
            #     my_btime = safe(row, col_btime)
            #     my_bdate = safe(row, col_bdate)

            #     my_tobj, my_dobj = smart_parse_time_date(my_btime, my_bdate)
            #     my_booking_dt = IST.localize(datetime.combine(my_dobj, my_tobj)) if (my_tobj and my_dobj) else None

            #     if my_lat is not None and my_booking_dt:
            #         candidates = []

            #         for ir in index_rows:
            #             if ir["oid"] == oid:
            #                 continue
            #             if not ir.get("booking_dt"):
            #                 continue

            #             # same day only
            #             if ir["booking_dt"].date() != my_booking_dt.date():
            #                 continue

            #             # only FUTURE bookings
            #             if ir["booking_dt"] <= my_booking_dt:
            #                 continue

            #             dkm = haversine_km(my_lat, my_lng, ir["lat"], ir["lng"])
            #             if dkm <= 7.0:
            #                 # Use stored booking time (sheet format) → pretty, if possible
            #                 btime_str = ir.get("btime", "")
            #                 try:
            #                     t_obj2, _ = smart_parse_time_date(btime_str, None)
            #                     tstr = t_obj2.strftime("%I:%M %p") if t_obj2 else btime_str
            #                 except Exception:
            #                     tstr = btime_str

            #                 candidates.append((ir["oid"], dkm, tstr))

            #         # Sort by distance and pick top 3
            #         candidates.sort(key=lambda x: x[1])
            #         top = candidates[:3]

            #         if not top:
            #             # No nearby → explicit Not Found
            #             staged_updates.append({
            #                 "range": f"{_col_letter(col_near_1 + 1)}{r_idx}:{_col_letter(col_near_3 + 1)}{r_idx}",
            #                 "values": [["Not Found", "Not Found", "Not Found"]]
            #             })
            #             print(f"nearby: {oid} → Not Found")
            #         else:
            #             formatted = [
            #                 _format_nearby_entry(toid, dist_km, tstr)
            #                 for (toid, dist_km, tstr) in top
            #             ]
            #             # pad to 3 cells
            #             while len(formatted) < 3:
            #                 formatted.append("")
            #             staged_updates.append({
            #                 "range": f"{_col_letter(col_near_1 + 1)}{r_idx}:{_col_letter(col_near_3 + 1)}{r_idx}",
            #                 "values": [formatted]
            #             })
            #             print(f"nearby: {oid} → {len(top)} found")

            #         # Mark nearby as done (won't run again unless you clear it)
            #         staged_updates.append({
            #             "range": f"{_col_letter(col_near_done + 1)}{r_idx}",
            #             "values": [["YES"]]
            #         })

            # ----------------------------------------
            # 6.5 Write timestamps & address block (can refresh every run)
            # ----------------------------------------
            block = [v_sj, v_ej, v_sj2, v_ej2, v_total, v_actual, cx_addr]
            rng = f"{_col_letter(col_start_journey + 1)}{r_idx}:{_col_letter(col_cx_address + 1)}{r_idx}"
            staged_updates.append({
                "range": rng,
                "values": [block]
            })

        except Exception as e:
            print("job-row error:", e)
            continue

    # --------------------------------------------------
    # 7) Apply batch updates
    # --------------------------------------------------
    if staged_updates:
        try:
            _with_backoff(ws.batch_update, staged_updates)
        except Exception as e:
            print("job: batch update error:", e)

    # --------------------------------------------------
    # 8) Hide sensitive columns (best-effort)
    # --------------------------------------------------
    COLUMNS_TO_HIDE = [
        "Service Provider Mobile", "Customer Name", "Customer Email",
        "IsWhatsAppLocationMessageSent?", "IsSP_PreBooking_1hr_Sent?",
        "Start Journey", "Stop Journey", "Start Job At", "Stop Job At",
        "Actual Time Taken", "Cx Address Fetched?", "IsSP_Start_Job_Reminder_Sent?",
        "OTP Before Sent", "OTP After Sent", "Stop Job Alert Sent?", "Lat&Long"
        # NOTE: IsNearbyCalculatedDone is intentionally NOT hidden,
        # so you can see/clear it manually if needed.
    ]
    header = ws.row_values(1)
    for col_name in COLUMNS_TO_HIDE:
        if col_name in header:
            col_index_1based = header.index(col_name) + 1
            try:
                ws.hide_columns(col_index_1based)
            except Exception:
                pass

    print("job: done ✅ (final rewritten with Distance Matrix + IsNearbyCalculatedDone)")

# ===============================
# PICKUP ETA (time-only) + ALERTS — ONLY WHILE START JOB
# ===============================
def _extract_total_minutes(total_time_str: str):
    if not total_time_str: return None
    m = re.search(r"(\d+)", str(total_time_str))
    if not m: return None
    try: return int(m.group(1))
    except Exception: return None

def _compute_pickup_eta_and_finish(start_job_str: str, total_time_str: str):
    try:
        if not (start_job_str and total_time_str): return (None, None)
        total_minutes = _extract_total_minutes(total_time_str)
        if total_minutes is None: return (None, None)
        dt_start = dtparser.parse(start_job_str, fuzzy=True, dayfirst=True)
        if dt_start.tzinfo is None: dt_start = IST.localize(dt_start)
        expected_finish = dt_start + timedelta(minutes=total_minutes)
        pickup_eta      = expected_finish - timedelta(minutes=40)  # original offset
        return (pickup_eta, expected_finish)
    except Exception:
        return (None, None)

def refresh_pickup_eta():
    print("pickup ETA: refresh")
    ws = ensure_today_sheet()

    all_vals = _with_backoff(ws.get_all_values)
    if len(all_vals) <= 1:
        print("pickup ETA: no rows"); return

    h = _col_map(all_vals[0])
    need_cols = ("Order Status","Start Job At","Total Time","Pickup ETA","Service Provider Name","Stop Job At")
    if any(c not in h for c in need_cols):
        print("pickup ETA: required columns missing"); return

    col_status     = h["Order Status"]
    col_start_job  = h["Start Job At"]
    col_total_time = h["Total Time"]
    col_pickup_eta = h["Pickup ETA"]
    col_sp_name    = h["Service Provider Name"]
    col_stop_job   = h["Stop Job At"]

    staged = []
    for r_idx, row in enumerate(all_vals[1:], start=2):
        status = (row[col_status].strip().upper() if col_status < len(row) else "")
        if status != "START JOB": 
            continue

        # If Stop Job At already present → never touch again
        stop_job_val = row[col_stop_job].strip() if col_stop_job < len(row) else ""
        if stop_job_val:
            continue

        start_job   = row[col_start_job]  if col_start_job  < len(row) else ""
        total_time  = row[col_total_time] if col_total_time < len(row) else ""
        sp_name     = row[col_sp_name]    if col_sp_name    < len(row) else ""
        current_eta = row[col_pickup_eta] if col_pickup_eta < len(row) else ""
        if not start_job or not total_time: continue

        pickup_eta_dt, _finish_dt = _compute_pickup_eta_and_finish(start_job, total_time)
        if not pickup_eta_dt: continue

        pickup_eta_str = pickup_eta_dt.strftime("%I:%M %p")
        if pickup_eta_str != current_eta:
            staged.append({"range": f"{_col_letter(col_pickup_eta+1)}{r_idx}", "values": [[pickup_eta_str]]})
            print(f"pickup ETA updated: {clean_sp_name(sp_name)} → {pickup_eta_str}")

    if staged: _with_backoff(ws.batch_update, staged)
    print("pickup ETA: done")

def alert_pickup_eta_repeat():
    print("pickup alert: check")
    ws = ensure_today_sheet()

    all_vals = _with_backoff(ws.get_all_values)
    if len(all_vals) <= 1:
        print("pickup alert: no rows"); return

    h = _col_map(all_vals[0])
    need = ("Order Status","Start Job At","Total Time","Pickup ETA","Pickup Rider","Service Provider Name","Stop Job At")
    if any(c not in h for c in need):
        print("pickup alert: required columns missing"); return

    col_status, col_start_job, col_total_time = h["Order Status"], h["Start Job At"], h["Total Time"]
    col_pickup_eta, col_pickup_rider, col_sp_name = h["Pickup ETA"], h["Pickup Rider"], h["Service Provider Name"]
    col_stop_job = h["Stop Job At"]

    now = datetime.now(IST)
    for r_idx, row in enumerate(all_vals[1:], start=2):
        try:
            status = row[col_status].strip().upper() if col_status < len(row) else ""
            if status != "START JOB":
                continue

            # If Stop Job is filled, never alert again
            stop_job_val = row[col_stop_job].strip() if col_stop_job < len(row) else ""
            if stop_job_val:
                continue

            start_job    = row[col_start_job]    if col_start_job    < len(row) else ""
            total_time   = row[col_total_time]   if col_total_time   < len(row) else ""
            pickup_eta   = row[col_pickup_eta]   if col_pickup_eta   < len(row) else ""
            pickup_rider = row[col_pickup_rider] if col_pickup_rider < len(row) else ""
            sp_name      = row[col_sp_name]      if col_sp_name      < len(row) else ""

            if not start_job or not total_time: continue
            if pickup_rider and pickup_rider.strip() and "?" not in pickup_rider: continue

            pickup_eta_dt, expected_finish_dt = _compute_pickup_eta_and_finish(start_job, total_time)
            if not pickup_eta_dt or not expected_finish_dt: continue

            # keep ETA cell fresh (without extra reads)
            pickup_eta_str = pickup_eta_dt.strftime("%I:%M %p")
            if not pickup_eta:
                _with_backoff(ws.update_cell, r_idx, col_pickup_eta + 1, pickup_eta_str)

            delta_min = (pickup_eta_dt - now).total_seconds() / 60.0
            if 0 < delta_min <= 15:
                print(f"pickup alert: {clean_sp_name(sp_name)} free at {expected_finish_dt.strftime('%I:%M %p')}")

                # Voice alert
                TASK_QUEUE.put({
                    "type": "voice",
                    "msg": f"{sp_name} का काम {expected_finish_dt.strftime('%I:%M %p')} तक खत्म होगा!"
                })

                # WhatsApp to managers (sp_finish_eta_alert_v1)
                finish_hhmm = expected_finish_dt.strftime("%I:%M %p")
                TASK_QUEUE.put({
                    "type": "manager_alert",
                    "sp": sp_name,
                    "hhmm": finish_hhmm
                })

                print("pickup alert: WA manager alert queued")

        except Exception as e:
            print("pickup alert row error:", e)

    print("pickup alert: done ✅")

# ===============================
# OTP REMINDERS (before/after)
# ===============================
def otp_reminders_pass():
    ws = ensure_today_sheet()
    all_vals = _with_backoff(ws.get_all_values)
    if len(all_vals) <= 1: return

    h = _col_map(all_vals[0])
    # Ensure columns exist (they should, via ensure_today_sheet)
    for need in ("OTP Before Sent","OTP After Sent"):
        if need not in h:
            header2 = _with_backoff(ws.row_values, 1)
            header2.append(need)
            _with_backoff(ws.update, "A1", [header2])
            h = _col_map(header2)

    before_col = h["OTP Before Sent"]
    after_col  = h["OTP After Sent"]

    col_sp_name = h.get("Service Provider Name")
    col_sp_mob  = h.get("Service Provider Mobile")
    col_bt      = h.get("Booking Time")
    col_bd      = h.get("Booking Date")
    col_start_job = h.get("Start Job At")

    if None in (col_sp_name, col_sp_mob, col_bt, col_bd, col_start_job):
        print("otp: required columns missing"); return

    updates = []
    now_ist = datetime.now(IST)

    for rowi, row in enumerate(all_vals[1:], start=2):
        def safe(i): return row[i].strip() if (i is not None and i < len(row)) else ""

        sp_name2 = safe(col_sp_name)
        sp_phone2= safe(col_sp_mob)
        btime_str= safe(col_bt)
        bdate_str= safe(col_bd)
        start_job_val = safe(col_start_job)
        before_sent_val= safe(before_col)
        after_sent_val = safe(after_col)

        if not btime_str or not bdate_str or not sp_phone2:
            continue

        t_obj, d_obj = smart_parse_time_date(btime_str, bdate_str)
        if not (t_obj and d_obj):
            continue

        booking_dt = IST.localize(datetime.combine(d_obj, t_obj))
        delta_sec = (booking_dt - now_ist).total_seconds()

        # Before: 10–20 min before booking time
        if 600 <= delta_sec <= 1200 and not before_sent_val:
            print(f"🔔 OTP (Before) → {sp_name2} ({sp_phone2})")
            send_sp_otp_reminder(sp_phone2, sp_name2, "before")
            updates.append({"range": f"{_col_letter(before_col+1)}{rowi}", "values": [["✅ Sent"]]})
            time.sleep(SP_SEND_GAP_SECONDS)

        # After: 5–15 min after booking time if job not started
        elif -900 <= delta_sec <= -300 and not start_job_val and not after_sent_val:
            print(f"🔔 OTP (After) → {sp_name2} ({sp_phone2})")
            send_sp_otp_reminder(sp_phone2, sp_name2, "after")
            updates.append({"range": f"{_col_letter(after_col+1)}{rowi}", "values": [["✅ Sent"]]})
            time.sleep(SP_SEND_GAP_SECONDS)

    if updates:
        _with_backoff(ws.batch_update, updates)
        print(f"✅ OTP updates: {len(updates)}")

# ===============================
# BOOKING COUNT (pulse) — ORIGINAL WORKING LOGIC
# ===============================
last_booking_count = None



def get_last_seen_oids():
    try:
        state = sh.worksheet("State")
    except WorksheetNotFound:
        state = sh.add_worksheet("State", rows=10, cols=5)
        state.update("A1", [["LastSeenOrderIds"]])
        return set()
    
    val = state.acell("A2").value
    if not val:
        return set()
    return set(val.split(","))

def save_last_seen_oids(oids):
    try:
        state = sh.worksheet("State")
    except WorksheetNotFound:
        state = sh.add_worksheet("State", rows=10, cols=5)
        state.update("A1", [["LastSeenOrderIds"]])
    state.update("A2", [",".join(oids)])



def monitor_booking_count():
    global last_booking_count
    try:
        driver.get(TODAY_BOOKING_URL)
        time.sleep(2.0)
        element = wait.until(EC.presence_of_element_located((By.XPATH, BOOKING_COUNT_XPATH)))
        raw = element.text.strip()
        digits = re.sub(r"[^\d]", "", raw)
        current_value = int(digits) if digits else 0
        print(f"count: {current_value}")

        # first run baseline
        if last_booking_count is None:
            last_booking_count = current_value
            return

        # ✅ NEW booking
        if current_value > last_booking_count:
            diff = current_value - last_booking_count
            speak_message(f"{diff} नई बुकिंग आई है। अब कुल {current_value} बुकिंग हैं।")
            print("🔔 NEW BOOKING DETECTED")
            sync_today_bookings()
            last_booking_count = current_value
            return

        # ❌ Booking cancelled
        if current_value < last_booking_count:
            diff = last_booking_count - current_value
            speak_message(f"{diff} बुकिंग कैंसल हुई है। अब {current_value} बुकिंग हैं।")
            print("⚠️ BOOKING CANCELED DETECTED")
            sync_today_bookings()
            last_booking_count = current_value
            return

        # No change
        last_booking_count = current_value

    except Exception as e:
        print("count: error", e)



# ===============================
# DAILY SUMMARY (10–11 PM IST)
# ===============================

def state_get_col(col_name, default=None):
    """
    Get a value from 'State' sheet using header in row 1 and value in row 2.
    If the sheet does not exist yet, it will be created with default headers.
    """
    try:
        state = sh.worksheet("State")
    except WorksheetNotFound:
        state = sh.add_worksheet("State", rows=10, cols=5)
        state.update("A1", [["LastSeenOrderIds"]])
        state.update("B1", [["LastRolloverDate"]])

    try:
        headers = state.row_values(1)
        values = state.row_values(2)
        if col_name in headers:
            idx = headers.index(col_name)  # 0-based
            if idx < len(values):
                val = values[idx].strip()
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
    try:
        state = sh.worksheet("State")
    except WorksheetNotFound:
        state = sh.add_worksheet("State", rows=10, cols=5)
        state.update("A1", [["LastSeenOrderIds"]])
        state.update("B1", [["LastRolloverDate"]])

    try:
        headers = state.row_values(1)
        if col_name in headers:
            col = headers.index(col_name) + 1  # 1-based
        else:
            col = len(headers) + 1
            state.update_cell(1, col, col_name)

        # Ensure row 2 exists and write the value
        state.update_cell(2, col, str(value))
    except Exception as e:
        print(f"state_set_col error for {col_name}: {e}")


PAYMENT_HASH_STATE_KEY = "PaymentMessagesHashMap"


def state_get(sh_unused, key, default=""):
    """
    Backward-compatible wrapper over State sheet config.
    Some older helpers pass a `sh` argument — we ignore it and
    use the global State helpers.
    """
    return state_get_col(key, default)


def state_set(sh_unused, key, value):
    """
    Backward-compatible wrapper over State sheet config.
    Stores values in row 2 under header = `key`.
    """
    state_set_col(key, value)

def _get_today_payment_sheet(sh):
    """
    Return today's Payment Collection sheet, e.g.:
    '🧾 Payment Collection Report - 29/11/25'
    """
    from datetime import datetime

    today_label = datetime.now(IST).strftime("%d/%m/%y")
    sheet_name = f"🧾 Payment Collection Report - {today_label}"

    try:
        return sh.worksheet(sheet_name)
    except WorksheetNotFound:
        print(f"⚠️ Payment sheet not found: {sheet_name}")
        print("⚠️ No Payment Collection sheet for today — skipping PaymentMessages")
        return None


def has_sent_today():
    """
    Check if daily summary has already been sent today.
    Stored in 'State' sheet, column header: DailySummaryLastSentDate
    """
    today = datetime.now(IST).strftime("%Y-%m-%d")
    last = state_get_col("DailySummaryLastSentDate", "")
    return last == today


def mark_sent_today():
    """
    Mark that daily summary has been sent today in the State sheet.
    """
    today = datetime.now(IST).strftime("%Y-%m-%d")
    state_set_col("DailySummaryLastSentDate", today)


def send_daily_summaries():
    ws = ensure_today_sheet()
    all_vals = _with_backoff(ws.get_all_values)
    if len(all_vals) <= 1: return

    h = _col_map(all_vals[0])
    for need in ("Service Provider Name","Service Provider Mobile","Booking Time","Start Journey","Start Job At","Stop Job At","Total Time","Actual Time Taken"):
        if need not in h: 
            print("daily summary: required columns missing"); 
            return

    col_sp, col_phone, col_bt, col_sj, col_sja, col_sja2, col_tt, col_at = \
        h["Service Provider Name"], h["Service Provider Mobile"], h["Booking Time"], h["Start Journey"], h["Start Job At"], h["Stop Job At"], h["Total Time"], h["Actual Time Taken"]

    def fmt_time(v):
        try:
            if not v or v.strip() == "": return ""
            p = dtparser.parse(v); return p.strftime("%I:%M %p")
        except:
            return v

    groups = {}
    for row in all_vals[1:]:
        sp = (row[col_sp].strip() if col_sp < len(row) else "")
        phone = (row[col_phone].strip() if col_phone < len(row) else "")
        if not sp or not phone: continue
        entry = {
            "bt": fmt_time(row[col_bt]) if col_bt < len(row) else "",
            "sj": fmt_time(row[col_sj]) if col_sj < len(row) else "",
            "sja": fmt_time(row[col_sja]) if col_sja < len(row) else "",
            "sja2": fmt_time(row[col_sja2]) if col_sja2 < len(row) else "",
            "tt": (row[col_tt] if col_tt < len(row) else "").replace("(min)", "").strip(),
            "at": (row[col_at] if col_at < len(row) else "").replace("min", "").strip(),
        }
        groups.setdefault((sp, phone), []).append(entry)

    today_str = datetime.now(IST).strftime("%d-%b-%Y")
    for (sp, phone), entries in groups.items():
        lines = []
        for e in entries:
            line = (f"*Booking {e['bt']}* • Start Journey: {e['sj']} • Start Job: {e['sja']} • Stop Job: {e['sja2']} • Total Time: {e['tt']} min • Actual Time: {e['at']} min")
            line = re.sub(r"\s{2,}", " ", line).strip()
            lines.append(line)
        body_value = " ——————————————— ".join(lines)

        phone_digits = re.sub(r"\D", "", phone)
        if len(phone_digits) == 10:
            phone_digits = "91" + phone_digits

        _send_interakt_template(phone_digits, [today_str, clean_sp_name(sp), body_value], INTERAKT_SP_DAILY_TMPL, "en")
    print("daily summary: sent ✅")

#=========================================

# ===============================
# DAILY ATTENDANCE REMINDER USING SP_LIST SHEET (8–9 PM IST, once)
# ===============================
INTERAKT_SP_ATTENDANCE_TMPL = "sp_attendance_reminder_v2"  # your final approved template

def _has_sent_attendance_today():
    """
    Check if daily attendance reminder has already been sent today.
    Stored in 'State' sheet, column header: AttendanceLastSentDate
    """
    today = datetime.now(IST).strftime("%Y-%m-%d")
    last = state_get_col("AttendanceLastSentDate", "")
    return last == today

def _mark_attendance_sent_today():
    """
    Mark that daily attendance reminder has been sent today in the State sheet.
    """
    today = datetime.now(IST).strftime("%Y-%m-%d")
    state_set_col("AttendanceLastSentDate", today)

def _weekday_name(dtobj):
    return dtobj.strftime("%A")

def _is_fri_sat_sun(dtobj):
    return dtobj.weekday() in (4, 5, 6)

def _normalize_phone_for_interakt(phone_raw):
    digits = re.sub(r"\D", "", phone_raw or "")
    if len(digits) == 10:
        digits = "91" + digits
    return digits if digits.startswith("91") and len(digits) == 12 else ""

def _is_between_8pm_and_11_30pm_ist(now_ist=None):
    now_ist = now_ist or datetime.now(IST)
    # 20:00 <= time <= 23:30
    if now_ist.hour < 20:  # before 8PM
        return False
    if now_ist.hour > 23:  # after midnight range
        return False
    if now_ist.hour == 23 and now_ist.minute > 30:  # after 11:30 PM
        return False
    return True



def send_attendance_reminders():
    # Time window guard
    if not _is_between_8pm_and_11_30pm_ist():
        print("attendance reminder: outside allowed time window (8PM–11:30PM); skipping")
        return

    if _has_sent_attendance_today():
        print("attendance reminder: already sent today; skipping")
        return


    # Pull SP roster sheet
    gc = gspread.service_account(filename="yesmadamndore-029caf40a32b.json")
    sh = gc.open_by_key(GOOGLE_SHEET_ID)     # SAME ID your other functions use
    sp_ws = _with_backoff(lambda: sh.worksheet("SP_LIST"))

    sp_vals = _with_backoff(sp_ws.get_all_values)
    if len(sp_vals) <= 1:
        print("attendance reminder: SP_LIST empty")
        _mark_attendance_sent_today()
        return

    h = _col_map(sp_vals[0])
    for c in ("SP Name", "Phone Number"):
        if c not in h:
            print("attendance reminder: SP_LIST missing required columns")
            return

    col_sp = h["SP Name"]
    col_phone = h["Phone Number"]

    roster = []
    for row in sp_vals[1:]:
        sp = row[col_sp].strip() if col_sp < len(row) else ""
        phone = row[col_phone].strip() if col_phone < len(row) else ""
        if sp and phone:
            roster.append((sp, phone))

    if not roster:
        print("attendance reminder: no SPs found")
        _mark_attendance_sent_today()
        return

    # Compose message text variables
    tomorrow = datetime.now(IST) + timedelta(days=1)
    tomorrow_date = tomorrow.strftime("%d-%b-%Y")
    tomorrow_day = _weekday_name(tomorrow)

    if _is_fri_sat_sun(tomorrow):
        policy_note = "Note: Fri–Sun are WEEKOFF days and will not be counted as leave."
    else:
        policy_note = "Note: Leaves are counted on Mon–Thu; Fri–Sun are not counted as leave."

    ai_manager_note = (
        "Note: I am an AI-based manager. I keep note of your leave pattern "
        "— whether leaves are always taken on the same day or on rush days!"
    )

    # Send message to each SP
    sent = 0
    for (sp, phone) in roster:
        msisdn = _normalize_phone_for_interakt(phone)
        if not msisdn:
            continue
        try:
            _send_interakt_template(
                msisdn,
                [tomorrow_date, tomorrow_day, policy_note, ai_manager_note],
                INTERAKT_SP_ATTENDANCE_TMPL,
                "en"
            )
            sent += 1
        except Exception as e:
            print(f"attendance reminder: send error for {sp} ({msisdn}): {e}")

    _mark_attendance_sent_today()
    print(f"attendance reminder: sent ✅ to {sent} SPs")
    


def rollover_today_bookings():
    global LAST_ROLLOVER_DATE

    print("\n==============================")
    print("📅 MIDNIGHT ROLLOVER STARTED")
    print("==============================")

    # ----------------------------------------
    # 1. Open both sheets safely
    # ----------------------------------------
    try:
        ws_today = sh.worksheet("TodayBookings")
    except:
        ws_today = sh.add_worksheet("TodayBookings", rows=2000, cols=40)

    try:
        ws_tmrw = sh.worksheet("TommorwBookings")
    except:
        ws_tmrw = sh.add_worksheet("TommorwBookings", rows=2000, cols=40)

    # ----------------------------------------
    # 2. ALWAYS read header from TommorwBookings first
    # ----------------------------------------
    today_header = ws_tmrw.row_values(1)

    # fallback 1 → read from TodayBookings
    if not today_header:
        today_header = ws_today.row_values(1)

    # fallback 2 → create dummy header (last resort protection)
    if not today_header:
        print("❌ WARNING: Header missing in both sheets — creating fallback header")
        today_header = ["OrderID", "Status", "CustomerName", "CustomerPhone"]

    # ----------------------------------------
    # 3. Load all TomorrowBookings rows
    # ----------------------------------------
    tomorrow_vals = ws_tmrw.get_all_values()

    # ----------------------------------------
    # 4. If no bookings tomorrow, keep only header
    # ----------------------------------------
    if len(tomorrow_vals) <= 1:
        print("⚠️ No tomorrow bookings found – keeping TodayBookings empty")

        ws_today.clear()
        ws_today.update(values=[today_header], range_name="A1")

        ws_tmrw.clear()
        ws_tmrw.update(values=[today_header], range_name="A1")
        return

    # ----------------------------------------
    # 5. Extract tomorrow rows excluding header
    # ----------------------------------------
    new_rows = tomorrow_vals[1:]

    # ----------------------------------------
    # 6. Normalize rows & reset columns
    # ----------------------------------------
    time_cols = [
        "Drop Rider", "Pickup ETA", "Pickup Rider",
        "Start Journey", "Stop Journey", "Start Job At", "Stop Job At",
        "Total Time", "Actual Time Taken",
        "OTP Before Sent", "OTP After Sent", "Stop Job Alert Sent?"
    ]

    for r in new_rows:

        # Ensure row matches header length
        if len(r) < len(today_header):
            r.extend([""] * (len(today_header) - len(r)))

        # Reset WA flags
        for col in ["IsWhatsAppLocationMessageSent?", "IsSP_PreBooking_1hr_Sent?"]:
            if col in today_header:
                r[today_header.index(col)] = ""

        # Reset time/job fields
        for col_name in time_cols:
            if col_name in today_header:
                r[today_header.index(col_name)] = ""

    # ----------------------------------------
    # 7. Rewrite TodayBookings completely
    # ----------------------------------------
    ws_today.clear()

    ws_today.update(values=[today_header], range_name="A1")

    if new_rows:
        ws_today.update(values=new_rows, range_name="A2")

    print("✔️ TodayBookings refreshed with TomorrowBookings")

    # ----------------------------------------
    # 8. Reset TommorwBookings completely (ONLY header)
    # ----------------------------------------
    ws_tmrw.clear()
    ws_tmrw.update(values=[today_header], range_name="A1")

    print("✔️ TommorwBookings reset for new cycle")

    # ----------------------------------------
    # 9. Update in-memory date
    # ----------------------------------------
    LAST_ROLLOVER_DATE = datetime.now(IST).strftime("%Y-%m-%d")
    print("🎉 Rollover completed successfully")


# ===============================
# MAIN LOOP
# ===============================

# -------------------------------
# FIX: use datetime.now(), not datetime.datetime.now()
# -------------------------------
now = datetime.now()
hr = now.hour
mn = now.minute

rollover_day_change()


OTHER_TASKS_STATE_KEY = "other_tasks_map_last_run_date"


def has_run_other_tasks_today():
    """Check State sheet: did other_tasks_map run today?"""
    today = datetime.now(IST).strftime("%Y-%m-%d")
    last_run = state_get_col(OTHER_TASKS_STATE_KEY, "")
    return last_run == today


def mark_other_tasks_run_today():
    """Update State sheet to mark today's run."""
    today = datetime.now(IST).strftime("%Y-%m-%d")
    state_set_col(OTHER_TASKS_STATE_KEY, today)

def send_payment_messages_once():
    """
    Sends Payment Summary messages only once per expert.
    Auto-creates missing 4th column before writing Sent?.
    Sends to:
      - Expert mobile (or default 7406611400)
      - Vikas (7406611400)
      - Mamaji (9826929380) ONLY if message contains "Cash Pending with Person: Mamaji"
    """

    import re
    import gspread
    from oauth2client.service_account import ServiceAccountCredentials

    # ------------------------------
    # Constants
    # ------------------------------
    DEFAULT_MOBILE = "7406611400"
    VIKAS_MOBILE   = "7406611400"
    MAMAJI_MOBILE  = "9826929380"

    # ------------------------------
    # Google Sheet Authentication
    # ------------------------------
    scope = [
        "https://www.googleapis.com/auth/spreadsheets",
        "https://www.googleapis.com/auth/drive"
    ]

    creds  = ServiceAccountCredentials.from_json_keyfile_name(JSON_KEY_PATH, scope)
    client = gspread.authorize(creds)

    sh = client.open_by_key(GOOGLE_SHEET_ID)
    ws = sh.worksheet("PaymentMessages")  # use sheet tab name

    # ------------------------------
    # Ensure minimum 4 columns exist
    # ------------------------------
    current_cols = ws.col_count
    if current_cols < 4:
        ws.add_cols(4 - current_cols)
        print(f"✔ Added {4 - current_cols} missing column(s) to expand to 4 columns.")

    # ------------------------------
    # Ensure Sent? header exists
    # ------------------------------
    header = ws.row_values(1)
    if len(header) < 4 or str(header[3]).strip() != "Sent?":
        ws.update_cell(1, 4, "Sent?")
        print("✔ Added 'Sent?' header in column D.")

    rows = ws.get_all_records()

    # ------------------------------
    # Process rows
    # ------------------------------
    for i, r in enumerate(rows, start=2):

        # Safe string extraction
        expert    = str(r.get("Expert Name") or "").strip()
        mobile    = str(r.get("Mobile") or "").strip()
        message   = str(r.get("Message") or "").strip()
        sent_flag = str(r.get("Sent?") or "").strip().lower()

        # Already sent?
        if sent_flag == "yes":
            print(f"Skipping {expert}: already sent")
            continue

        # No message?
        if not message:
            print(f"Skipping {expert}: empty message")
            continue

        # ------------------------------
        # Clean mobile number
        # ------------------------------
        if not mobile:
            primary = DEFAULT_MOBILE
            print(f"{expert}: missing mobile -> {primary}")
        else:
            digits = re.sub(r"\D", "", mobile)
            primary = digits[-10:] if len(digits) >= 10 else DEFAULT_MOBILE

        # ------------------------------
        # Build recipients list
        # ------------------------------
        recipients = []

        # Expert/default
        if primary not in recipients:
            recipients.append(primary)

        # Vikas
        if VIKAS_MOBILE not in recipients:
            recipients.append(VIKAS_MOBILE)

        # Nayak
        if NAYAK_MOBILE not in recipients:
            recipients.append(NAYAK_MOBILE)

        # Mamaji (only if message contains this keyword)
        if "Cash Pending with Person: Mamaji" in message:
            if MAMAJI_MOBILE not in recipients:
                recipients.append(MAMAJI_MOBILE)

        print(f"{expert}: sending to → {', '.join(recipients)}")

        # ------------------------------
        # Send the message
        # ------------------------------
        any_success = False
        for num in recipients:
            ok = send_interakt_plain_text(num, message)
            if ok:
                any_success = True
                print(f"   ✔ Sent -> {num}")
            else:
                print(f"   ❌ Failed -> {num}")

        # ------------------------------
        # Mark Sent? column
        # ------------------------------
        ws.update_cell(i, 4, "Yes" if any_success else "Failed")



from datetime import datetime, time as dt_time

def run_other_tasks_if_due(driver):
    """
    Runs other_tasks_map once per day between 20:30 and 23:59.
    Uses State sheet — no local files.
    """

    now = datetime.now(IST)
    current_time = now.time()

    # Time window: run between 20:30 → 23:59
    if dt_time(20, 00) <= current_time <= dt_time(23, 59):

        if not has_run_other_tasks_today():
            print("⏳ Running other_tasks_map (Add-on, Weekoff, Performance, WhatsApp Addon Report)…")

            try:
                other_tasks_map.run_all(driver)

                mark_other_tasks_run_today()
                print("✅ other_tasks_map completed successfully")

            except Exception as e:
                print("⚠️ other_tasks_map ERROR:", e)

        else:
            print("ℹ️ other_tasks_map already executed today.")

    else:
        print("⏳ Outside other_tasks_map window (20:30–23:59).")


def clear_payment_messages_sheet_except_header(sh):
    """
    Clears all rows from the 'PaymentMessages' sheet except the header row.
    Keeps row 1 intact and deletes rows 2 onward.
    """

    try:
        ws = sh.worksheet("PaymentMessages")
    except:
        print("⚠️ Sheet 'PaymentMessages' not found.")
        return

    rows = ws.row_count

    # If sheet has more than 1 row, delete rows 2 → last
    if rows > 1:
        ws.delete_rows(2, rows)
        print(f"✔ Cleared {rows-1} rows from PaymentMessages (header preserved).")
    else:
        print("Sheet already clean (only header present).")

def get_requests_session_from_driver(driver):
    session = requests.Session()
    for c in driver.get_cookies():
        session.cookies.set(
            c["name"],
            c["value"],
            domain=c.get("domain"),
            path=c.get("path", "/")
        )
    return session


bg_thread = threading.Thread(target=background_worker, daemon=True)
bg_thread.start()



if __name__ == "__main__":
    caffeinate_proc = start_caffeinate()
    print("System Ready ✅ (caffeinate on)")

   
    # ======================================================
    # 0) START APSCHEDULER (ONLY ONCE)
    # ======================================================
    from apscheduler.schedulers.background import BackgroundScheduler
    scheduler = BackgroundScheduler(timezone="Asia/Kolkata")

    # Delay Report: Every hour at :00 between 9 AM – 8 PM
    scheduler.add_job(
        run_daily_delay_report,
        trigger='cron',
        hour='9-22',
        minute=0,
        id='delay_report'
    )
    
    # Run Daily Delay Report once more between 11 PM – 11:55 PM 
    # ONLY IF today's report is still not sent.
    scheduler.add_job(
        run_delay_report_if_not_sent,
        trigger="cron",
        hour=21,
        minute="0-55/5",
        id="delay_report_night_check",
        replace_existing=True,
        timezone="Asia/Kolkata"
    )


    # Payment Messages: Every hour at :02 between 9 AM – 8 PM
    # scheduler.add_job(
    #     run_payment_messages_job,
    #     trigger='cron',
    #     hour='9-20',
    #     minute=2,
    #     id='payment_messages_hourly'
    # )

    scheduler.start()
    print("APScheduler started 🟢 (Delay Report Scheduler Active)")

    # ======================================================
    # 1) INITIALIZE TIMERS
    # ======================================================
    last_job_update = 0
    last_eta_update = 0
    last_alert_check = 0

    try:
        # ======================================================
        # LOGIN
        # ======================================================
        if not login():
            driver.quit()
            raise SystemExit(1)

        ensure_customer_sheet_headers()

        # ======================================================
        # MAIN LOOP
        # ======================================================
        while True:

            # Auto-exit if session expired
            if "login" in driver.current_url.lower():
                driver.quit()
                raise SystemExit(1)

            # --------------------------------------------------
            # 1) Bills + Prepaid
            # --------------------------------------------------

            # after login is successful
            

            new_bills = fetch_customer_bill()
            if new_bills > 0:
                clear_today_prepaid_sheet()
                fetch_prepaid_orders()

            # --------------------------------------------------
            # 2) Core Sync
            # --------------------------------------------------
            # run_payment_messages_job()
            # other_tasks_map.run_customize_expert_feedback_report(driver, sh_weekoff)


            run_tomorrow_whatsapp_windowed()

            
            sync_today_bookings()

            call_payment_messages_once_nightly()   # ← ADD THIS
            run_other_tasks_if_due(driver)

            try:
                sync_tomorrow_bookings()
            except Exception as e:
                print("tomorrow sync error:", e)

            # --------------------------------------------------
            # 3) Timed Workers
            # --------------------------------------------------
            now_ts = time.time()

            if now_ts - last_job_update >= JOB_UPDATE_INTERVAL:
                print("job: 10m tick")
                update_job_progress_details()
                update_tomorrow_bookings_geo_nearby()
                last_job_update = now_ts

            if now_ts - last_eta_update >= PICKUP_ETA_UPDATE_INTERVAL:
                refresh_pickup_eta()
                last_eta_update = now_ts

            if now_ts - last_alert_check >= ALERT_CHECK_INTERVAL:
                alert_pickup_eta_repeat()
                ws = ensure_today_sheet()
                stop_job_once_stage(ws)
                last_alert_check = now_ts

            # --------------------------------------------------
            # 4) Expert Feedback (12 PM, 5 PM, 7 PM windows)
            # --------------------------------------------------
            hr = datetime.now(IST).hour
            mn = datetime.now(IST).minute

            if hr in (12, 17, 19, 21) and 0 <= mn <= 59:
                try:
                    other_tasks_map.run_yesterday_expert_feedback_report(driver, sh_weekoff)
                    other_tasks_map.format_expert_feedback_sheet(sh_weekoff)
                    other_tasks_map.run_send_yesterday_expert_feedback_whatsapp(driver, sh_weekoff)
                except Exception as e:
                    print("⚠️ Expert Feedback Error:", e)

            # --------------------------------------------------
            # 5) Booking count pulse
            # --------------------------------------------------

            monitor_booking_count()

            # --------------------------------------------------
            # 6) Daily Summary (21:00–23:59)
            # --------------------------------------------------
            now_ist = datetime.now(IST)
            current_time = now_ist.time()

            if dt_time(21, 0) <= current_time <= dt_time(23, 59):
                if not has_sent_today():
                    try:
                        print("⏳ Sending daily summary…")
                        send_daily_summaries()
                        mark_sent_today()
                        print("✅ Daily summary sent!")
                    except Exception as e:
                        print("daily summary trigger error:", e)
                else:
                    print("Daily summary already sent today")

            # --------------------------------------------------
            # 7) Morning Leave Report (8 AM – 10 AM)
            # --------------------------------------------------
            if dt_time(8, 0) <= current_time < dt_time(10, 0):

                if not os.path.exists("/tmp/morning_leave_report_sent.txt"):
                    try:
                        print("⏳ Running Morning Leave Report…")
                        other_tasks_map.run_yesterday_leave_report(driver)
                        other_tasks_map.safe_run_franchise_product_assigned_report(driver)


                        with open("/tmp/morning_leave_report_sent.txt", "w") as f:
                            f.write(datetime.now(IST).strftime("%Y-%m-%d"))

                        print("✅ Morning Leave Report Sent")

                    except Exception as e:
                        print("⚠️ Leave Report Error:", e)
                else:
                    print("Morning Leave Report already sent today")

            # --------------------------------------------------
            # 8) After 10 AM → Reset lock + mid-day tasks
            # --------------------------------------------------
            if current_time >= dt_time(10, 0):

                # Reset lock
                try:
                    if os.path.exists("/tmp/morning_leave_report_sent.txt"):
                        os.remove("/tmp/morning_leave_report_sent.txt")
                        print("Morning Leave Report lock reset")
                except:
                    pass

                # Today Leave Report
                try:
                    other_tasks_map.run_today_leave_report(driver)
                except Exception as e:
                    print("⚠️ Today Leave Report Error:", e)

                # Yesterday Rider Report
                try:
                    other_tasks_map.run_yesterday_rider_report(driver)
                except Exception as e:
                    print("⚠️ Yesterday Rider Report Error:", e)

                # Leave Process Reminder
                try:
                    other_tasks_map.run_leave_process_reminder(driver)
                except Exception as e:
                    print("⚠️ Leave Process Reminder Error:", e)

            # --------------------------------------------------
            # 9) Sleep Cycle
            # --------------------------------------------------
            time.sleep(REFRESH_INTERVAL)

    # ------------------------------------------------------
    # EXIT HANDLING
    # ------------------------------------------------------
    except KeyboardInterrupt:
        print("sys: interrupted by user")

    except Exception as e:
        print("sys: fatal", e)

    finally:
        try: TASK_QUEUE.put(None)
        except: pass

        try: bg_thread.join(timeout=3)
        except: pass

        try: driver.quit()
        except: pass

        try: stop_caffeinate(caffeinate_proc)
        except: pass

        print("sys: exit, sleep restored")