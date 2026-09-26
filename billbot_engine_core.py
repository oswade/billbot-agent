"""BillBot Android comparison core.

The Android app deliberately keeps the calculation engine in Python so the public Energy
CDR parsing and tariff arithmetic can stay close to desktop BillBot.  The module uses only
the Python standard library, Decimal for money, additive SQLite migrations, and local cached
Product Reference Data.

Important CDR semantics implemented here:
* Generic Plans is v1 and Plan Detail prefers v3 with v2/v1 compatibility fallback.
* CDR tariff prices are ex-GST; residential comparison prices add 10% GST exactly once.
* A stepped-rate ``volume`` is the quantity in that block, not a cumulative threshold.
* ``singleRate.period`` is an ISO-8601 duration which controls when stepped blocks reset.
* Complex plans are retained with an honest classification when the available customer data
  cannot support a reliable annual price; they are not silently made to disappear.
"""
from __future__ import annotations

import calendar
import base64
import gzip
import concurrent.futures
import datetime as dt
import hashlib
import http.client
import json
import mimetypes
import os
import re
import socket
import sqlite3
import ssl
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from contextlib import contextmanager
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

APP_VERSION = "1.4.46"
DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
RETAILERS_PATH = os.path.join(DATA_DIR, "retailers.json")
SEASONALITY_PATH = os.path.join(DATA_DIR, "aer_seasonality_2021.json")
USER_AGENT = f"BillBot-Android/{APP_VERSION} (public Energy CDR product reference client)"
CDR_REGISTER_URL = "https://api.cdr.gov.au/cdr-register/v1/energy/data-holders/brands/summary"
AER_GATEWAY_DOMAIN = "cdr.energymadeeasy.gov.au"
GST = Decimal("1.10")
CENTS = Decimal("100")
DAYS_PER_YEAR = Decimal("365")
MONEY_Q = Decimal("0.01")
RATE_Q = Decimal("0.00001")

CDR_OUTER_WORKERS = 12
CDR_DETAIL_WORKERS = 3
# Keep Plan Detail pressure at the proven v1.4.14 ceiling even though lightweight list probes
# now run at higher concurrency.
CDR_DETAIL_GLOBAL_WORKERS = 15
# Listing and Detail work may now overlap, but total live Energy HTTP requests never exceed
# the old proven Detail ceiling. This keeps host pressure no higher than previous releases.
CDR_NETWORK_GLOBAL_LIMIT = 15
CDR_PAGE_WORKERS = 3
CDR_RETAILER_OVERLAP_MINUTES = 15
CDR_INCREMENTAL_OVERLAP_HOURS = 48
CDR_PROGRESS_MIN_WRITE_INTERVAL_SECONDS = 0.20
CDR_PROGRESS_DETAIL_BATCH = 25
NORMALIZER_VERSION = 1
ENERGY_SEED_FORMAT_VERSION = 3
CLOUD_SNAPSHOT_FORMAT_VERSION = 2
CLOUD_MANIFEST_FORMAT_VERSION = 1
ENERGY_SEED_STATE_KEYS = (
    "last_sync", "last_sync_status", "last_sync_report",
    "last_sync_electricity", "last_sync_gas",
    "last_sync_status_electricity", "last_sync_status_gas",
    "last_data_update_electricity", "last_data_update_gas",
    "energy_data_revision", "last_energy_sync_mode",
    "last_energy_successful_sync_at", "last_full_energy_reconciliation_at",
)
CDR_PLAN_LIST_PAGE_SIZE = 1000
CDR_PLAN_LIST_RESCUE_PAGE_SIZE = 250
CDR_RESCUE_REQUEST_TIMEOUT_SECONDS = 45
CDR_RESCUE_REQUEST_ATTEMPTS = 6
CDR_MAX_PLAN_LIST_PAGES = 10000
CDR_REQUEST_TIMEOUT_SECONDS = 25
CDR_REQUEST_ATTEMPTS = 4
CDR_REFRESH_DEADLINE_SECONDS = 15 * 60
CDR_DETAIL_API_VERSIONS = (3, 2, 1)
NBN_MIN_PROMO_MONTHS = 6
SAVINGS_MAX_DISPLAY_RATE_PCT = 10.0
MARKET_REFRESH_DEADLINE_SECONDS = 8 * 60

_HTTP_LOCAL = threading.local()
_CDR_NETWORK_SEMAPHORE = threading.BoundedSemaphore(CDR_NETWORK_GLOBAL_LIMIT)
_CDR_SYNC_LOCK = threading.Lock()

# A postcode cannot always identify a distributor. These legacy hints are used only when the
# national cached CDR plan geography cannot resolve a single unambiguous network.
POSTCODE_DISTRIBUTOR_HINTS = {
    "3168": "United Energy", "3169": "United Energy", "3166": "United Energy",
    "3167": "United Energy", "3170": "United Energy", "3149": "United Energy",
    "3150": "United Energy",
}

# Conservative state inference only. This is used when a bill gives a recognised network but
# omits its state. It never invents a postcode and never overrides an explicit bill state.
DISTRIBUTOR_STATE_HINTS = {
    "UNITED ENERGY": "VIC", "CITIPOWER": "VIC", "POWERCOR": "VIC",
    "AUSNET": "VIC", "JEMENA": "VIC",
    "AUSGRID": "NSW", "ENDEAVOUR ENERGY": "NSW", "ESSENTIAL ENERGY": "NSW",
    "ENERGEX": "QLD", "ERGON ENERGY": "QLD",
    "SA POWER NETWORKS": "SA", "SAPN": "SA",
    "EVOENERGY": "ACT", "TASNETWORKS": "TAS",
}

KNOWN_UNCONDITIONAL_ELIGIBILITY = {
    "NEW_CUSTOMER", "NEW_CUSTOMERS", "ONLINE_ONLY", "ONLINE", "NO_REQUIREMENTS",
    "NONE", "OPEN", "ALL_CUSTOMERS",
}


def _now() -> str:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat()


def _d(value: Any, default: Optional[str] = "0") -> Optional[Decimal]:
    if isinstance(value, dict) and "value" in value:
        value = value.get("value")
    if value in (None, "", "value_or_null"):
        return None if default is None else Decimal(default)
    try:
        text = str(value).replace(",", "").replace("$", "").strip()
        if text.lower().endswith("cr"):
            text = "-" + text[:-2].strip().lstrip("-")
        return Decimal(text)
    except (InvalidOperation, TypeError, ValueError):
        return None if default is None else Decimal(default)


def _money(value: Decimal) -> Decimal:
    return value.quantize(MONEY_Q, rounding=ROUND_HALF_UP)


def _json_money(value: Optional[Decimal]) -> Optional[float]:
    return None if value is None else float(_money(value))


def _json_number(value: Optional[Decimal], places: str = "0.001") -> Optional[float]:
    if value is None:
        return None
    return float(value.quantize(Decimal(places), rounding=ROUND_HALF_UP))


def _field_value(value: Any, default: Any = None) -> Any:
    if isinstance(value, dict) and "value" in value:
        raw = value.get("value")
        return default if raw in (None, "", "value_or_null") else raw
    return default if value is None else value


def _norm(value: Any) -> str:
    return "".join(ch for ch in str(value or "").lower() if ch.isalnum())


def _compact(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value or "")).strip()


@contextmanager
def _connect(db_path: str):
    parent = os.path.dirname(db_path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    con = sqlite3.connect(db_path, timeout=30)
    try:
        con.row_factory = sqlite3.Row
        con.execute("PRAGMA journal_mode=WAL")
        con.execute("PRAGMA busy_timeout=30000")
        yield con
    finally:
        con.close()


def _columns(con: sqlite3.Connection, table: str) -> set[str]:
    try:
        return {str(r[1]) for r in con.execute(f"PRAGMA table_info({table})").fetchall()}
    except Exception:
        return set()


def _add_column(con: sqlite3.Connection, table: str, name: str, ddl: str) -> None:
    if name not in _columns(con, table):
        con.execute(f"ALTER TABLE {table} ADD COLUMN {name} {ddl}")


def _schema(con: sqlite3.Connection) -> None:
    # Keep the v1 table and only add columns. cdr_plans mirrors the desktop naming contract so
    # diagnostics and future shared code can operate without another destructive migration.
    con.executescript(
        """
        CREATE TABLE IF NOT EXISTS energy_plans (
            retailer_key TEXT NOT NULL,
            plan_id TEXT NOT NULL,
            fuel_type TEXT NOT NULL,
            retailer_name TEXT,
            brand TEXT,
            plan_name TEXT,
            last_updated TEXT,
            application_uri TEXT,
            summary_json TEXT NOT NULL,
            detail_json TEXT NOT NULL,
            cached_at TEXT NOT NULL,
            PRIMARY KEY (retailer_key, plan_id)
        );
        CREATE INDEX IF NOT EXISTS idx_energy_fuel ON energy_plans(fuel_type);
        CREATE TABLE IF NOT EXISTS cdr_plans (
            plan_id TEXT PRIMARY KEY,
            provider TEXT,
            name TEXT,
            customer_type TEXT,
            distributors TEXT,
            tariff_type TEXT,
            is_tou INTEGER DEFAULT 0,
            is_flat INTEGER DEFAULT 0,
            has_demand INTEGER DEFAULT 0,
            has_controlled_load INTEGER DEFAULT 0,
            has_solar INTEGER DEFAULT 0,
            daily_supply_cents REAL,
            avg_usage_cents REAL,
            last_updated TEXT,
            raw_usage_rates TEXT,
            website TEXT,
            source TEXT,
            fuel_type TEXT,
            retailer_key TEXT,
            detail_json TEXT,
            summary_json TEXT,
            tariff_periods_json TEXT,
            controlled_load_json TEXT,
            eligibility_json TEXT,
            metering_charges_json TEXT,
            solar_feed_in_json TEXT
        );
        CREATE TABLE IF NOT EXISTS sync_state (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL,
            updated_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS debug_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            created_at TEXT NOT NULL,
            level TEXT NOT NULL,
            message TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS nbn_offers (
            provider TEXT NOT NULL,
            plan TEXT NOT NULL,
            speed_tier TEXT NOT NULL,
            monthly_price REAL NOT NULL,
            promo_monthly_price REAL,
            promo_months INTEGER,
            url TEXT,
            last_updated TEXT,
            imported_at TEXT NOT NULL,
            raw_json TEXT NOT NULL,
            source TEXT DEFAULT 'Local JSON',
            provider_slug TEXT,
            category TEXT,
            technology TEXT,
            license TEXT,
            PRIMARY KEY(provider, plan, speed_tier)
        );
        CREATE TABLE IF NOT EXISTS savings_products (
            holder_key TEXT NOT NULL,
            product_id TEXT NOT NULL,
            provider TEXT,
            product_name TEXT,
            raw_json TEXT NOT NULL,
            cached_at TEXT NOT NULL,
            PRIMARY KEY(holder_key, product_id)
        );
        CREATE INDEX IF NOT EXISTS idx_savings_provider ON savings_products(provider);
        """
    )
    energy_columns_before = _columns(con, "energy_plans")
    for name, ddl in (
        ("source", "TEXT"), ("customer_type", "TEXT"), ("distributors", "TEXT"),
        ("tariff_type", "TEXT"), ("is_tou", "INTEGER DEFAULT 0"),
        ("is_flat", "INTEGER DEFAULT 0"), ("has_demand", "INTEGER DEFAULT 0"),
        ("has_controlled_load", "INTEGER DEFAULT 0"), ("has_solar", "INTEGER DEFAULT 0"),
        ("daily_supply_cents", "REAL"), ("avg_usage_cents", "REAL"),
        ("raw_usage_rates", "TEXT"), ("eligibility_json", "TEXT"),
        ("metering_charges_json", "TEXT"), ("tariff_periods_json", "TEXT"),
        ("controlled_load_json", "TEXT"), ("solar_feed_in_json", "TEXT"),
        ("source_plan_id", "TEXT"), ("summary_revision", "TEXT"),
        ("normalizer_version", "INTEGER DEFAULT 0"), ("is_active", "INTEGER DEFAULT 1"), ("stale_reason", "TEXT"),
        # Metadata-only scan flag. Once populated, routine scans do not need to materialise the
        # large Plan Detail JSON just to prove an unchanged row is reusable.
        ("detail_cached", "INTEGER DEFAULT 0"),
    ):
        _add_column(con, "energy_plans", name, ddl)
    if "detail_cached" not in energy_columns_before:
        # One-time additive migration for existing databases. Future unchanged scans read only
        # compact metadata + Generic summaries instead of transferring ~89 MB of Detail JSON
        # through sqlite3 into Python. Fresh inserts set this flag directly.
        con.execute(
            "UPDATE energy_plans SET detail_cached=CASE WHEN COALESCE(detail_json,'')<>'' THEN 1 ELSE 0 END"
        )

    # Desktop BillBot databases and earlier Android builds can already contain cdr_plans with
    # only the legacy columns. Keep the migration strictly additive so upgrading in-place cannot
    # destroy a working catalogue or historical diagnostics.
    for name, ddl in (
        ("provider", "TEXT"), ("name", "TEXT"), ("customer_type", "TEXT"),
        ("distributors", "TEXT"), ("tariff_type", "TEXT"), ("is_tou", "INTEGER DEFAULT 0"),
        ("is_flat", "INTEGER DEFAULT 0"), ("has_demand", "INTEGER DEFAULT 0"),
        ("has_controlled_load", "INTEGER DEFAULT 0"), ("has_solar", "INTEGER DEFAULT 0"),
        ("daily_supply_cents", "REAL"), ("avg_usage_cents", "REAL"), ("last_updated", "TEXT"),
        ("raw_usage_rates", "TEXT"), ("website", "TEXT"), ("source", "TEXT"),
        ("fuel_type", "TEXT"), ("retailer_key", "TEXT"), ("detail_json", "TEXT"),
        ("summary_json", "TEXT"), ("tariff_periods_json", "TEXT"),
        ("controlled_load_json", "TEXT"), ("eligibility_json", "TEXT"),
        ("metering_charges_json", "TEXT"), ("solar_feed_in_json", "TEXT"),
        ("source_plan_id", "TEXT"), ("summary_revision", "TEXT"),
        ("normalizer_version", "INTEGER DEFAULT 0"), ("is_active", "INTEGER DEFAULT 1"), ("stale_reason", "TEXT"),
    ):
        _add_column(con, "cdr_plans", name, ddl)
    for name, ddl in (
        ("source", "TEXT DEFAULT 'Local JSON'"), ("provider_slug", "TEXT"),
        ("category", "TEXT"), ("technology", "TEXT"), ("license", "TEXT"),
    ):
        _add_column(con, "nbn_offers", name, ddl)
    con.execute("CREATE INDEX IF NOT EXISTS idx_cdr_plans_fuel ON cdr_plans(fuel_type)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_energy_active_fuel ON energy_plans(fuel_type,is_active)")
    con.commit()


def _log(con: sqlite3.Connection, level: str, message: str) -> None:
    con.execute(
        "INSERT INTO debug_logs(created_at, level, message) VALUES(?,?,?)",
        (_now(), level.upper(), str(message)[:4000]),
    )
    con.execute(
        "DELETE FROM debug_logs WHERE id NOT IN (SELECT id FROM debug_logs ORDER BY id DESC LIMIT 1500)"
    )
    con.commit()


def init_app(db_path: str) -> str:
    with _connect(db_path) as con:
        _schema(con)
        _log(con, "INFO", f"BillBot Android {APP_VERSION} initialised")
    return json.dumps({"ok": True, "version": APP_VERSION, "stats": _stats_dict(db_path)})


def _stats_dict(db_path: str) -> Dict[str, Any]:
    with _connect(db_path) as con:
        _schema(con)
        count = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1").fetchone()[0])
        e = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='ELECTRICITY'").fetchone()[0])
        g = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='GAS'").fetchone()[0])
        nbn = int(con.execute("SELECT COUNT(*) FROM nbn_offers").fetchone()[0])
        savings = int(con.execute("SELECT COUNT(*) FROM savings_products").fetchone()[0])
        def state_value(key: str, fallback: str) -> str:
            row = con.execute("SELECT value FROM sync_state WHERE key=?", (key,)).fetchone()
            return row[0] if row else fallback
        try:
            energy_report = json.loads(state_value("last_sync_report", "{}") or "{}")
            if not isinstance(energy_report, dict):
                energy_report = {}
        except Exception:
            energy_report = {}
        coverage_names = energy_report.get("coverage_failure_names") or []
        if not isinstance(coverage_names, list):
            coverage_names = []
        return {
            "energy_plans": count, "electricity_plans": e, "gas_plans": g, "nbn_offers": nbn,
            "energy_coverage_issues": int(energy_report.get("coverage_issues") or 0),
            "energy_coverage_failure_names": ", ".join(str(x) for x in coverage_names[:4]),
            "energy_discovery_warnings": int(energy_report.get("discovery_warnings") or 0),
            "energy_detail_warnings": int(energy_report.get("detail_failures") or 0),
            "savings_products": savings, "last_sync": state_value("last_sync", "Never"),
            "last_sync_status": state_value("last_sync_status", "never"),
            "energy_data_revision": int(state_value("energy_data_revision", "0") or 0),
            "nbn_data_revision": int(state_value("nbn_data_revision", "0") or 0),
            "savings_data_revision": int(state_value("savings_data_revision", "0") or 0),
            "electricity_last_data_update": state_value("last_data_update_electricity", "Unknown" if e else "Never"),
            "gas_last_data_update": state_value("last_data_update_gas", "Unknown" if g else "Never"),
            "electricity_last_sync_status": state_value("last_sync_status_electricity", "legacy" if e else "never"),
            "gas_last_sync_status": state_value("last_sync_status_gas", "legacy" if g else "never"),
            "nbn_last_data_update": state_value("nbn_last_data_update", "Unknown" if nbn else "Never"),
            "nbn_last_sync_status": state_value("nbn_last_sync_status", "legacy" if nbn else "never"),
            "savings_last_data_update": state_value("savings_last_data_update", "Unknown" if savings else "Never"),
            "savings_last_sync_status": state_value("savings_last_sync_status", "legacy" if savings else "never"),
            "cloud_snapshot_id": state_value("cloud_snapshot_id", ""),
            "cloud_generated_at": state_value("cloud_generated_at", ""),
            "cloud_applied_at": state_value("cloud_applied_at", ""),
            "seed_requires_full_sync": int(state_value("seed_requires_full_sync", "0") or 0),
        }

def get_stats(db_path: str) -> str:
    return json.dumps(_stats_dict(db_path))


def get_logs(db_path: str, limit: int = 200) -> str:
    with _connect(db_path) as con:
        _schema(con)
        rows = con.execute(
            "SELECT created_at, level, message FROM debug_logs ORDER BY id DESC LIMIT ?",
            (max(1, min(int(limit), 1000)),),
        ).fetchall()
    return json.dumps({"logs": [dict(r) for r in rows]})


def _distributor_candidates(db_path: str, postcode: str, fuel: str = "ELECTRICITY") -> List[str]:
    """Return every cached distributor explicitly associated with a postcode/fuel.

    Boundary postcodes can legitimately map to more than one electricity or gas
    distributor.  Keep all of those candidates so the UI can ask the customer which
    network serves their property instead of silently dropping the network filter.
    """
    pc = str(postcode or "").strip()
    requested_fuel = str(fuel or "ELECTRICITY").upper()
    if not pc or not db_path:
        hint = POSTCODE_DISTRIBUTOR_HINTS.get(pc, "")
        return [hint] if hint else []

    networks = set()
    try:
        with _connect(db_path) as con:
            _schema(con)
            rows = con.execute(
                "SELECT summary_json, detail_json FROM energy_plans "
                "WHERE UPPER(fuel_type)=? AND COALESCE(is_active,1)=1",
                (requested_fuel,),
            ).fetchall()
        for row in rows:
            try:
                summary = json.loads(row["summary_json"] or "{}")
            except Exception:
                summary = {}
            try:
                detail = json.loads(row["detail_json"] or "{}")
            except Exception:
                detail = {}
            geo = _flatten_geography(detail if detail.get("geography") else summary)
            included_postcodes = geo.get("included_postcodes") or []
            if not included_postcodes or not any(_postcode_token_matches(x, pc) for x in included_postcodes):
                continue
            named = {_compact(x) for x in (geo.get("included_distributors") or []) if _compact(x)}
            if len(named) == 1:
                networks.update(named)
    except Exception:
        pass
    if networks:
        return sorted(networks, key=str.casefold)
    hint = POSTCODE_DISTRIBUTOR_HINTS.get(pc, "")
    return [hint] if hint else []


def distributor_candidates(db_path: str, postcode: str, fuel: str = "ELECTRICITY") -> str:
    candidates = _distributor_candidates(str(db_path or "").strip(), postcode, fuel)
    return json.dumps({
        "postcode": str(postcode or "").strip(),
        "fuel": str(fuel or "ELECTRICITY").upper(),
        "distributors": candidates,
    })


def suggest_distributor(db_path_or_postcode: str, postcode: Optional[str] = None, fuel: str = "ELECTRICITY") -> str:
    """Conservatively infer a single network from cached national market data.

    New callers provide ``db_path, postcode, fuel``. The legacy one-argument form is
    retained for compatibility. A network is returned only when there is exactly one
    candidate. Ambiguous boundary postcodes remain blank here; Android calls
    ``distributor_candidates`` to present those candidates to the customer.
    """
    if postcode is None:
        pc = str(db_path_or_postcode or "").strip()
        return POSTCODE_DISTRIBUTOR_HINTS.get(pc, "")
    candidates = _distributor_candidates(
        str(db_path_or_postcode or "").strip(),
        str(postcode or "").strip(),
        fuel,
    )
    return candidates[0] if len(candidates) == 1 else ""


# ---------------------------------------------------------------------------
# AER seasonal usage profile
# ---------------------------------------------------------------------------

_SEASONALITY_CACHE: Optional[Dict[str, Any]] = None


def _seasonality_data() -> Dict[str, Any]:
    global _SEASONALITY_CACHE
    if _SEASONALITY_CACHE is None:
        try:
            with open(SEASONALITY_PATH, "r", encoding="utf-8") as f:
                _SEASONALITY_CACHE = json.load(f)
        except Exception:
            _SEASONALITY_CACHE = {}
    return _SEASONALITY_CACHE


def _state_from_postcode(postcode: str) -> str:
    try:
        pc = int(str(postcode).strip())
    except Exception:
        return ""
    if 200 <= pc <= 299 or 2600 <= pc <= 2618 or 2900 <= pc <= 2920:
        return "ACT"
    if 1000 <= pc <= 2599 or 2619 <= pc <= 2899 or 2921 <= pc <= 2999:
        return "NSW"
    if 3000 <= pc <= 3999 or 8000 <= pc <= 8999:
        return "VIC"
    if 4000 <= pc <= 4999 or 9000 <= pc <= 9999:
        return "QLD"
    if 5000 <= pc <= 5999:
        return "SA"
    if 6000 <= pc <= 6999:
        return "WA"
    if 7000 <= pc <= 7999:
        return "TAS"
    if 800 <= pc <= 999:
        return "NT"
    return ""


def _profile_for(fuel: str, postcode: str, state: str = "") -> Optional[List[Decimal]]:
    data = _seasonality_data()
    state = str(state or _state_from_postcode(postcode)).upper()
    if fuel.upper() == "GAS":
        raw = (data.get("gas") or {}).get(state)
    else:
        zone = (data.get("postcode_climate_zone") or {}).get(str(postcode).zfill(4))
        zone_data = (data.get("electricity") or {}).get(str(zone), {}) if zone else {}
        raw = zone_data.get(state) or zone_data.get("ALL")
    if not raw or len(raw) != 4:
        return None
    values = [_d(x, None) for x in raw]
    if any(v is None or v <= 0 for v in values):
        return None
    total = sum(values, Decimal("0"))
    return [v / total for v in values]  # type: ignore[arg-type]


def _season_index(day: dt.date) -> int:
    if day.month in (12, 1, 2):
        return 0
    if day.month in (3, 4, 5):
        return 1
    if day.month in (6, 7, 8):
        return 2
    return 3


def _season_days(day: dt.date) -> int:
    idx = _season_index(day)
    if idx == 0:
        start = dt.date(day.year if day.month == 12 else day.year - 1, 12, 1)
        end = dt.date(start.year + 1, 3, 1)
    elif idx == 1:
        start, end = dt.date(day.year, 3, 1), dt.date(day.year, 6, 1)
    elif idx == 2:
        start, end = dt.date(day.year, 6, 1), dt.date(day.year, 9, 1)
    else:
        start, end = dt.date(day.year, 9, 1), dt.date(day.year, 12, 1)
    return (end - start).days


def _parse_date(value: Any) -> Optional[dt.date]:
    value = _field_value(value)
    if not value:
        return None
    text = str(value).strip()
    formats = (
        "%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%d %b %Y", "%d %B %Y",
        "%d %b %y", "%d %B %y",
    )
    for fmt in formats:
        try:
            return dt.datetime.strptime(text[:20].strip(), fmt).date()
        except Exception:
            pass
    # Extract a date embedded in a longer source string.
    patterns = [
        r"\b\d{4}-\d{2}-\d{2}\b",
        r"\b\d{1,2}/\d{1,2}/\d{4}\b",
        r"\b\d{1,2}\s+[A-Za-z]{3,9}\s+\d{2,4}\b",
    ]
    for pattern in patterns:
        m = re.search(pattern, text)
        if m:
            found = _parse_date(m.group(0))
            if found:
                return found
    return None


def _observed_dates(start: Optional[dt.date], end: Optional[dt.date], bill_days: int) -> List[dt.date]:
    if not start or not end or bill_days <= 0:
        return []
    diff = (end - start).days
    if diff < 0:
        return []
    # Most energy periods quote end-start as the number of charge days. If the printed bill_days
    # says otherwise, honour bill_days while never walking beyond one extra inclusive end date.
    if diff == bill_days:
        count = bill_days
    elif diff + 1 == bill_days:
        count = bill_days
    else:
        count = min(max(1, bill_days), diff + 1 if diff >= 0 else bill_days)
    return [start + dt.timedelta(days=i) for i in range(count)]


def annualise_usage(
    usage: Any,
    fuel: str,
    postcode: str,
    state: str = "",
    period_start: Any = None,
    period_end: Any = None,
    bill_days: Any = None,
) -> Dict[str, Any]:
    usage_d = _d(usage, None)
    days_d = _d(bill_days, None)
    if usage_d is None or usage_d <= 0:
        return {"annual_usage": None, "method": "USAGE_MISSING", "observed_days": 0}
    start = _parse_date(period_start)
    end = _parse_date(period_end)
    # Australian retail bills commonly print inclusive start/end dates (for example 5 Jan to
    # 1 Feb = 28 days). Prefer an explicit printed bill_days value; otherwise use the inclusive
    # calendar span rather than silently losing a day.
    inferred_days = ((end - start).days + 1) if start and end and end >= start else 0
    days = int(days_d) if days_d is not None and days_d > 0 else inferred_days
    if days <= 0:
        return {"annual_usage": None, "method": "BILL_DAYS_MISSING", "observed_days": 0}
    if days >= 330:
        annual = usage_d * DAYS_PER_YEAR / Decimal(days)
        return {
            "annual_usage": _json_number(annual, "0.1"), "method": "ACTUAL_NEAR_ANNUAL_DAY_RATE",
            "observed_days": days, "profile_source": "Observed near-annual bill history",
        }
    profile = _profile_for(fuel, postcode, state)
    observed = _observed_dates(start, end, days)
    if profile and observed:
        weight = Decimal("0")
        for day in observed:
            idx = _season_index(day)
            weight += profile[idx] / Decimal(_season_days(day))
        if Decimal("0.01") < weight < Decimal("0.99"):
            annual = usage_d / weight
            method = "AER_RESIDENTIAL_GAS_SEASONAL_PROFILE" if fuel.upper() == "GAS" else "AER_QUARTERLY_SEASONAL_PROFILE"
            return {
                "annual_usage": _json_number(annual, "0.1"), "method": method,
                "observed_days": len(observed), "observed_profile_weight": float(weight),
                "profile": [float(x) for x in profile],
                "profile_source": ("AER / Frontier Economics residential consumption benchmarks; "
                                   "seasonal shape normalised across household sizes"),
            }
    annual = usage_d * DAYS_PER_YEAR / Decimal(days)
    method = "ELAPSED_DAY_RATE_NO_RELIABLE_GAS_PROFILE" if fuel.upper() == "GAS" else "ELAPSED_DAY_RATE_NO_RELIABLE_PROFILE"
    return {
        "annual_usage": _json_number(annual, "0.1"), "method": method,
        "observed_days": days, "profile_source": "Elapsed-day fallback",
    }


def _annual_daily_series(annual_usage: Decimal, profile: Optional[Sequence[Decimal]]) -> List[Tuple[dt.date, Decimal]]:
    year = 2025  # non-leap reference year; annual comparison convention is 365 days.
    if not profile:
        per_day = annual_usage / DAYS_PER_YEAR
        return [(dt.date(year, 1, 1) + dt.timedelta(days=i), per_day) for i in range(365)]
    totals = [Decimal("0")] * 4
    counts = [0] * 4
    for i in range(365):
        day = dt.date(year, 1, 1) + dt.timedelta(days=i)
        counts[_season_index(day)] += 1
    for i in range(4):
        totals[i] = annual_usage * profile[i]
    out = []
    for i in range(365):
        day = dt.date(year, 1, 1) + dt.timedelta(days=i)
        idx = _season_index(day)
        out.append((day, totals[idx] / Decimal(counts[idx])))
    return out


# ---------------------------------------------------------------------------
# CDR discovery and sync
# ---------------------------------------------------------------------------


def _load_retailers() -> List[Dict[str, str]]:
    """Load the last-known-good AER PRD URI catalogue, canonicalised and deduplicated."""
    try:
        with open(RETAILERS_PATH, "r", encoding="utf-8") as f:
            rows = json.load(f)
    except Exception:
        return []
    unique: List[Dict[str, str]] = []
    seen: set[str] = set()
    for row in rows if isinstance(rows, list) else []:
        base = _canonical_base(str(row.get("base_uri") or ""))
        parsed = urllib.parse.urlparse(base)
        key = base.rstrip("/").lower()
        if not base or parsed.scheme.lower() != "https" or not parsed.hostname or key in seen:
            continue
        seen.add(key)
        unique.append({
            "name": str(row.get("name") or row.get("brand") or "Unknown"),
            "base_uri": base, "brand": str(row.get("brand") or ""),
            "source": "Bundled AER rescue",
        })
    return unique



class _HttpStatusError(RuntimeError):
    def __init__(self, status: int, reason: str = "") -> None:
        super().__init__(f"HTTP {status}{': ' + reason if reason else ''}")
        self.status = int(status)


def _check_deadline(deadline: Optional[float]) -> None:
    if deadline is not None and time.monotonic() >= deadline:
        raise TimeoutError("Refresh deadline exceeded")


def _close_http_connection() -> None:
    conn = getattr(_HTTP_LOCAL, "conn", None)
    if conn is not None:
        try:
            conn.close()
        except Exception:
            pass
    _HTTP_LOCAL.conn = None
    _HTTP_LOCAL.conn_key = None


def _persistent_http_json(url: str, headers: Dict[str, str], timeout: float) -> Dict[str, Any]:
    parsed = urllib.parse.urlparse(url)
    if parsed.scheme.lower() != "https" or not parsed.hostname:
        raise ValueError("Only HTTPS public endpoints are supported")
    port = int(parsed.port or 443)
    key = (parsed.hostname.lower(), port)
    conn = getattr(_HTTP_LOCAL, "conn", None)
    if conn is None or getattr(_HTTP_LOCAL, "conn_key", None) != key:
        _close_http_connection()
        conn = http.client.HTTPSConnection(parsed.hostname, port, timeout=timeout, context=ssl.create_default_context())
        _HTTP_LOCAL.conn = conn
        _HTTP_LOCAL.conn_key = key
    else:
        conn.timeout = timeout
    path = urllib.parse.urlunparse(("", "", parsed.path or "/", parsed.params, parsed.query, ""))
    request_headers = {"User-Agent": USER_AGENT, "Connection": "keep-alive", **headers}
    conn.request("GET", path, headers=request_headers)
    response = conn.getresponse()
    raw = response.read(25 * 1024 * 1024 + 1)
    if len(raw) > 25 * 1024 * 1024:
        _close_http_connection()
        raise ValueError("CDR response exceeded the 25 MB safety limit")
    if response.status >= 400:
        status, reason = response.status, response.reason or ""
        if response.status >= 500 or response.status in (408, 429):
            _close_http_connection()
        raise _HttpStatusError(status, reason)
    try:
        data = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _close_http_connection()
        raise ValueError(f"Endpoint returned invalid JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise ValueError("CDR endpoint returned non-object JSON")
    return data


def _request_json(url: str, headers: Dict[str, str], timeout: int = CDR_REQUEST_TIMEOUT_SECONDS,
                  attempts: int = CDR_REQUEST_ATTEMPTS, deadline: Optional[float] = None) -> Dict[str, Any]:
    last: Optional[Exception] = None
    for attempt in range(max(1, int(attempts))):
        _check_deadline(deadline)
        remaining = (deadline - time.monotonic()) if deadline is not None else float(timeout)
        effective_timeout = max(0.5, min(float(timeout), remaining))
        try:
            # Routine listing and Plan Detail now overlap. Gate every live Energy request through
            # one shared semaphore so overlap improves wall-clock time without increasing the
            # maximum simultaneous request pressure beyond the previous 15-request ceiling.
            with _CDR_NETWORK_SEMAPHORE:
                return _persistent_http_json(url, headers, effective_timeout)
        except _HttpStatusError as exc:
            last = exc
            if exc.status not in (408, 429, 500, 502, 503, 504):
                raise
        except (http.client.HTTPException, OSError, socket.timeout, TimeoutError, ValueError) as exc:
            last = exc
            _close_http_connection()
        if attempt + 1 < max(1, int(attempts)):
            _check_deadline(deadline)
            pause = min(5.0, 0.5 * (2 ** attempt))
            if deadline is not None:
                pause = min(pause, max(0.0, deadline - time.monotonic()))
            if pause > 0:
                time.sleep(pause)
    if last:
        raise last
    raise RuntimeError("Request failed")

def _canonical_base(uri: str) -> str:
    uri = str(uri or "").strip().rstrip("/")
    for suffix in ("/cds-au/v1", "/cds-au/v1/energy"):
        if uri.lower().endswith(suffix):
            uri = uri[: -len(suffix)]
            break
    return uri.rstrip("/")


def _retailer_key(base_uri: str) -> str:
    parsed = urllib.parse.urlparse(base_uri)
    path = parsed.path.strip("/").replace("/", "-")
    return _norm((parsed.netloc or "unknown") + "-" + path)[:160]


def _discover_retailers() -> Tuple[List[Dict[str, str]], str]:
    """Discover Energy PRD endpoints using Register ``productBaseUri`` first.

    CDR Register v2 separates Product Reference Data from other public endpoints through
    ``productBaseUri``. BillBot prefers that field, then a known AER mapping for recognised
    brands, and only retains ``publicBaseUri`` as a last-resort discovery probe for an unknown
    holder. The bundled AER list remains a completeness rescue.
    """
    fallback = _load_retailers()
    fallback_by_base = {_canonical_base(r["base_uri"]).lower(): r for r in fallback}
    fallback_by_brand: Dict[str, Dict[str, str]] = {}
    for row in fallback:
        for token in (row.get("brand"), row.get("name")):
            norm = _norm(token)
            if norm and norm not in fallback_by_brand:
                fallback_by_brand[norm] = row

    discovered: Dict[str, Dict[str, str]] = {}
    register_ok = False
    payload: Dict[str, Any] = {}
    register_version = "2"
    try:
        try:
            payload = _request_json(
                CDR_REGISTER_URL,
                {"Accept": "application/json", "x-v": "2", "x-min-v": "2"},
                timeout=25,
            )
        except Exception:
            register_version = "1"
            payload = _request_json(
                CDR_REGISTER_URL,
                {"Accept": "application/json", "x-v": "1", "x-min-v": "1"},
                timeout=25,
            )
        data = payload.get("data") or []
        if isinstance(data, dict):
            data = data.get("brands") or data.get("dataHolders") or []
        for brand in data if isinstance(data, list) else []:
            if not isinstance(brand, dict):
                continue
            name = _compact(brand.get("brandName") or brand.get("name"))
            product_uri = _canonical_base(brand.get("productBaseUri") or brand.get("productBaseURI") or "")
            public_uri = _canonical_base(brand.get("publicBaseUri") or brand.get("publicBaseURI") or "")
            candidate = product_uri or public_uri
            parsed = urllib.parse.urlparse(candidate)
            if not candidate or parsed.scheme.lower() != "https" or not parsed.hostname:
                continue

            known = fallback_by_brand.get(_norm(name))
            if product_uri:
                uri = product_uri
                row = {
                    "name": name or (known or {}).get("name") or "Energy retailer",
                    "base_uri": uri,
                    "brand": (known or {}).get("brand") or _retailer_key(uri),
                    "source": f"Official CDR Register v{register_version} productBaseUri",
                    "coverage_role": "aer_prd" if urllib.parse.urlparse(uri).hostname == AER_GATEWAY_DOMAIN else "register_product",
                }
            elif known is not None:
                uri = _canonical_base(known["base_uri"])
                row = dict(known)
                row.update({
                    "name": name or known.get("name") or "Energy retailer",
                    "base_uri": uri,
                    "source": f"CDR Register v{register_version} + bundled AER PRD mapping",
                    "coverage_role": "aer_prd",
                })
            else:
                # Legacy Register payload with no productBaseUri. Keep the endpoint as a
                # non-authoritative discovery probe only; its failure cannot create a false
                # Energy coverage warning.
                uri = public_uri
                row = {
                    "name": name or "Energy retailer", "base_uri": uri,
                    "brand": _retailer_key(uri),
                    "source": f"Official CDR Register v{register_version} publicBaseUri fallback",
                    "coverage_role": "register_probe",
                }
            discovered[uri.lower()] = row
        register_ok = True
    except Exception:
        register_ok = False

    for base_key, row in fallback_by_base.items():
        if base_key not in discovered:
            rescue = dict(row)
            rescue["source"] = "Bundled AER PRD mapping"
            rescue["coverage_role"] = "aer_prd"
            discovered[base_key] = rescue

    rows = sorted(discovered.values(), key=lambda r: (_norm(r.get("name")), r.get("base_uri", "")))
    source = (f"CDR Register v{register_version} productBaseUri + bundled AER rescue"
              if register_ok else "Bundled AER rescue (Register unavailable)")
    return rows, source

def _energy_source_is_coverage_required(retailer: Dict[str, Any]) -> bool:
    """Whether failure of this endpoint proves an Energy PRD coverage gap.

    The ACCC CDR Register publicBaseUri is useful for discovering newly enrolled brands, but
    for energy it is not necessarily the AER-hosted Product Reference Data route. Register-only
    URIs are therefore probes: their failure is a discovery warning, not proof that a market
    source is unavailable. AER PRD mappings remain coverage-required.
    """
    return str(retailer.get("coverage_role") or "aer_prd").lower() != "register_probe"


def _list_url(base_uri: str) -> str:
    return _canonical_base(base_uri) + "/cds-au/v1/energy/plans"


def _detail_url(base_uri: str, plan_id: str) -> str:
    return _list_url(base_uri) + "/" + urllib.parse.quote(str(plan_id), safe="")



def _safe_next_plan_link(base_uri: str, value: Any) -> Optional[str]:
    text = str(value or "").strip()
    if not text:
        return None
    absolute = urllib.parse.urljoin(_list_url(base_uri) + "?", text)
    target = urllib.parse.urlparse(absolute)
    expected = urllib.parse.urlparse(_list_url(base_uri))
    if target.scheme.lower() != "https" or target.netloc.lower() != expected.netloc.lower():
        raise ValueError("CDR pagination link changed host or scheme")
    if target.path.rstrip("/") != expected.path.rstrip("/"):
        raise ValueError("CDR pagination link changed endpoint path")
    return absolute


def _plan_list_query(updated_since: str = "", page: int = 1, page_size: int = CDR_PLAN_LIST_PAGE_SIZE,
                     fuel_type: str = "ALL", plan_type: str = "ALL") -> str:
    page_size = max(1, min(CDR_PLAN_LIST_PAGE_SIZE, int(page_size or CDR_PLAN_LIST_PAGE_SIZE)))
    fuel_type = str(fuel_type or "ALL").upper()
    plan_type = str(plan_type or "ALL").upper()
    params: Dict[str, Any] = {
        "type": plan_type, "fuelType": fuel_type, "effective": "CURRENT",
        "page": page, "page-size": page_size,
    }
    if str(updated_since or "").strip():
        params["updated-since"] = str(updated_since).strip()
    return urllib.parse.urlencode(params)


def _plan_list_once_sequential(retailer: Dict[str, str], progress: Optional["_ProgressReporter"] = None,
                    deadline: Optional[float] = None, updated_since: str = "",
                    page_size: int = CDR_PLAN_LIST_PAGE_SIZE,
                    request_timeout: int = CDR_REQUEST_TIMEOUT_SECONDS,
                    request_attempts: int = CDR_REQUEST_ATTEMPTS,
                    fuel_type: str = "ALL", plan_type: str = "ALL") -> Dict[str, Any]:
    page_size = max(1, min(CDR_PLAN_LIST_PAGE_SIZE, int(page_size or CDR_PLAN_LIST_PAGE_SIZE)))
    page = 1
    url = _list_url(retailer["base_uri"]) + "?" + _plan_list_query(updated_since, page, page_size, fuel_type, plan_type)
    plans_by_id: Dict[str, Dict[str, Any]] = {}
    seen_urls: set[str] = set()
    seen_signatures: set[Tuple[str, ...]] = set()
    declared_pages: Optional[int] = None
    declared_records: Optional[int] = None
    pages = 0
    complete = True
    errors: List[str] = []
    while url:
        _check_deadline(deadline)
        if url in seen_urls:
            errors.append("pagination loop detected")
            complete = False
            break
        seen_urls.add(url)
        pages += 1
        if pages > CDR_MAX_PLAN_LIST_PAGES:
            errors.append("page safety limit exceeded")
            complete = False
            break
        if progress:
            progress.page(retailer.get("name", "Energy retailer"), pages)
        payload = _request_json(
            url, {"Accept": "application/json", "x-v": "1", "x-min-v": "1"},
            timeout=request_timeout, attempts=request_attempts, deadline=deadline,
        )
        data = payload.get("data") or {}
        page_plans = data.get("plans") if isinstance(data, dict) else []
        if not isinstance(page_plans, list):
            page_plans = []
        page_ids: List[str] = []
        for plan in page_plans:
            if not isinstance(plan, dict):
                continue
            plan_id = str(plan.get("planId") or "").strip()
            if not plan_id:
                errors.append(f"page {pages} contained a plan without planId")
                complete = False
                continue
            page_ids.append(plan_id)
            plans_by_id[plan_id] = plan
        signature = tuple(page_ids)
        if signature and signature in seen_signatures:
            errors.append(f"repeated page content detected at page {pages}")
            complete = False
            break
        if signature:
            seen_signatures.add(signature)
        meta = payload.get("meta") or {}
        try:
            tp = int(meta.get("totalPages")) if meta.get("totalPages") is not None else None
            tr = int(meta.get("totalRecords")) if meta.get("totalRecords") is not None else None
        except (TypeError, ValueError):
            tp = tr = None
            errors.append("invalid pagination metadata")
            complete = False
        if tp is not None:
            if tp < 0 or tp > CDR_MAX_PLAN_LIST_PAGES:
                errors.append("invalid totalPages")
                complete = False
            if declared_pages is None:
                declared_pages = tp
            elif declared_pages != tp:
                errors.append("totalPages changed during pagination")
                complete = False
        if tr is not None:
            if tr < 0:
                errors.append("invalid totalRecords")
                complete = False
            if declared_records is None:
                declared_records = tr
            elif declared_records != tr:
                errors.append("totalRecords changed during pagination")
                complete = False
            if tp is not None and tr >= 0:
                expected_pages = 0 if tr == 0 else (tr + page_size - 1) // page_size
                if tp not in (expected_pages, max(1, expected_pages)):
                    errors.append("pagination metadata is internally inconsistent")
                    complete = False
        next_link = _safe_next_plan_link(retailer["base_uri"], (payload.get("links") or {}).get("next"))
        if next_link:
            url = next_link
        elif declared_pages is not None and pages < declared_pages:
            page = pages + 1
            url = _list_url(retailer["base_uri"]) + "?" + _plan_list_query(updated_since, page, page_size, fuel_type, plan_type)
        else:
            url = None
    expected_response_pages = 1 if declared_pages == 0 and declared_records == 0 else declared_pages
    if expected_response_pages is not None and expected_response_pages != pages:
        complete = False
        errors.append(f"expected {declared_pages} logical pages but received {pages} HTTP page response(s)")
    if declared_records is not None and declared_records != len(plans_by_id):
        complete = False
        errors.append(f"expected {declared_records} unique plans but received {len(plans_by_id)}")
    return {"plans": list(plans_by_id.values()), "plan_ids": set(plans_by_id), "pages": pages,
            "complete": complete, "errors": errors, "updated_since": str(updated_since or ""),
            "page_size": page_size, "declared_records": declared_records,
            "declared_pages": declared_pages, "fuel_type": str(fuel_type or "ALL").upper(),
            "plan_type": str(plan_type or "ALL").upper()}



def _plan_count_probe(retailer: Dict[str, str], deadline: Optional[float] = None,
                      fuel_type: str = "ALL", plan_type: str = "ALL") -> Dict[str, Any]:
    """Fetch one CURRENT row solely to obtain authoritative ``meta.totalRecords`` cheaply."""
    url = _list_url(retailer["base_uri"]) + "?" + _plan_list_query(
        "", 1, 1, fuel_type=fuel_type, plan_type=plan_type
    )
    payload = _request_json(
        url, {"Accept": "application/json", "x-v": "1", "x-min-v": "1"}, deadline=deadline
    )
    meta = payload.get("meta") or {}
    try:
        total = int(meta.get("totalRecords"))
        pages = int(meta.get("totalPages")) if meta.get("totalPages") is not None else None
    except (TypeError, ValueError) as exc:
        raise ValueError("CURRENT count probe returned invalid pagination metadata") from exc
    if total < 0:
        raise ValueError("CURRENT count probe returned negative totalRecords")
    data = payload.get("data") or {}
    plans = data.get("plans") if isinstance(data, dict) else []
    first = plans[0] if isinstance(plans, list) and plans and isinstance(plans[0], dict) else None
    return {
        "total_records": total, "total_pages": pages, "first_plan": first,
        "fuel_type": str(fuel_type or "ALL").upper(),
        "plan_type": str(plan_type or "ALL").upper(),
    }


def _plan_list_once(retailer: Dict[str, str], progress: Optional["_ProgressReporter"] = None,
                    deadline: Optional[float] = None, updated_since: str = "",
                    page_size: int = CDR_PLAN_LIST_PAGE_SIZE,
                    request_timeout: int = CDR_REQUEST_TIMEOUT_SECONDS,
                    request_attempts: int = CDR_REQUEST_ATTEMPTS,
                    fuel_type: str = "ALL", plan_type: str = "ALL") -> Dict[str, Any]:
    """Fetch a Generic Plan catalogue, parallelising pages after page 1 when safe.

    Page 1 establishes ``totalPages``/``totalRecords``. Remaining numbered pages are independent
    CDS requests, so up to ``CDR_PAGE_WORKERS`` are fetched concurrently. Validation remains
    fail-closed: every page must report consistent metadata, unique membership, and the final
    unique-ID count must equal ``totalRecords``. If an endpoint omits usable pagination metadata,
    the legacy link-following implementation is used instead.
    """
    page_size = max(1, min(CDR_PLAN_LIST_PAGE_SIZE, int(page_size or CDR_PLAN_LIST_PAGE_SIZE)))
    headers = {"Accept": "application/json", "x-v": "1", "x-min-v": "1"}

    def fetch_page(page: int) -> Tuple[int, Dict[str, Any]]:
        _check_deadline(deadline)
        url = _list_url(retailer["base_uri"]) + "?" + _plan_list_query(
            updated_since, page, page_size, fuel_type, plan_type
        )
        payload = _request_json(
            url, headers, timeout=request_timeout, attempts=request_attempts, deadline=deadline
        )
        return page, payload

    page1_num, page1 = fetch_page(1)
    meta1 = page1.get("meta") or {}
    try:
        declared_pages = int(meta1.get("totalPages")) if meta1.get("totalPages") is not None else None
        declared_records = int(meta1.get("totalRecords")) if meta1.get("totalRecords") is not None else None
    except (TypeError, ValueError):
        declared_pages = declared_records = None
    if declared_pages is None or declared_records is None:
        return _plan_list_once_sequential(
            retailer, progress, deadline, updated_since, page_size,
            request_timeout, request_attempts, fuel_type, plan_type
        )
    if declared_pages < 0 or declared_pages > CDR_MAX_PLAN_LIST_PAGES or declared_records < 0:
        return {
            "plans": [], "plan_ids": set(), "pages": 1, "complete": False,
            "errors": ["invalid pagination metadata"], "updated_since": str(updated_since or ""),
            "page_size": page_size, "declared_records": declared_records,
            "declared_pages": declared_pages, "fuel_type": str(fuel_type or "ALL").upper(),
            "plan_type": str(plan_type or "ALL").upper(),
        }

    expected_pages = 0 if declared_records == 0 else (declared_records + page_size - 1) // page_size
    errors: List[str] = []
    if declared_pages not in (expected_pages, max(1, expected_pages)):
        errors.append("pagination metadata is internally inconsistent")

    payloads: Dict[int, Dict[str, Any]] = {1: page1}
    logical_pages = max(1, declared_pages) if declared_records == 0 else declared_pages
    if declared_pages > 1:
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(CDR_PAGE_WORKERS, declared_pages - 1)) as pool:
            futures = {pool.submit(fetch_page, page): page for page in range(2, declared_pages + 1)}
            for future in concurrent.futures.as_completed(futures):
                page = futures[future]
                try:
                    num, payload = future.result()
                    payloads[num] = payload
                    if progress:
                        progress.page(retailer.get("name", "Energy retailer"), num)
                except Exception as exc:
                    errors.append(f"page {page} failed: {str(exc)[:260]}")
    if progress:
        progress.page(retailer.get("name", "Energy retailer"), 1)

    plans_by_id: Dict[str, Dict[str, Any]] = {}
    seen_signatures: set[Tuple[str, ...]] = set()
    for page in range(1, declared_pages + 1 if declared_pages > 0 else 2):
        payload = payloads.get(page)
        if payload is None:
            continue
        meta = payload.get("meta") or {}
        try:
            tp = int(meta.get("totalPages")) if meta.get("totalPages") is not None else None
            tr = int(meta.get("totalRecords")) if meta.get("totalRecords") is not None else None
        except (TypeError, ValueError):
            tp = tr = None
        if tp != declared_pages or tr != declared_records:
            errors.append(f"pagination metadata changed at page {page}")
        data = payload.get("data") or {}
        page_plans = data.get("plans") if isinstance(data, dict) else []
        if not isinstance(page_plans, list):
            page_plans = []
        page_ids: List[str] = []
        for plan in page_plans:
            if not isinstance(plan, dict):
                continue
            pid = str(plan.get("planId") or "").strip()
            if not pid:
                errors.append(f"page {page} contained a plan without planId")
                continue
            page_ids.append(pid)
            plans_by_id[pid] = plan
        signature = tuple(page_ids)
        if signature and signature in seen_signatures:
            errors.append(f"repeated page content detected at page {page}")
        if signature:
            seen_signatures.add(signature)

    http_pages = len(payloads)
    if declared_pages > 0 and http_pages != declared_pages:
        errors.append(f"expected {declared_pages} logical pages but received {http_pages} HTTP page response(s)")
    if declared_records != len(plans_by_id):
        errors.append(f"expected {declared_records} unique plans but received {len(plans_by_id)}")
    return {
        "plans": list(plans_by_id.values()), "plan_ids": set(plans_by_id), "pages": http_pages,
        "complete": not errors, "errors": errors, "updated_since": str(updated_since or ""),
        "page_size": page_size, "declared_records": declared_records,
        "declared_pages": declared_pages, "fuel_type": str(fuel_type or "ALL").upper(),
        "plan_type": str(plan_type or "ALL").upper(), "parallel_pages": declared_pages > 1,
    }

def _plan_list_partitioned_recovery(retailer: Dict[str, str], progress: Optional["_ProgressReporter"] = None,
                                    deadline: Optional[float] = None, updated_since: str = "") -> Dict[str, Any]:
    """Recover a catalogue whose ALL-plan pagination is internally unstable.

    The CDS Get Generic Plans filters are mutually exclusive dimensions. Splitting CURRENT data
    by fuel first, and only splitting an unstable fuel further by plan type, avoids page-boundary
    drift while preserving the same authoritative plan universe. This is intentionally generic
    rather than retailer-specific and is only used after the normal and small-page passes fail
    completeness validation.
    """
    merged: Dict[str, Dict[str, Any]] = {}
    total_pages = 0
    diagnostics: List[str] = []
    accepted_declared = 0
    all_declared_known = True

    for fuel in ("ELECTRICITY", "GAS", "DUAL"):
        _check_deadline(deadline)
        try:
            fuel_snapshot = _plan_list_once(
                retailer, progress, deadline, updated_since=updated_since,
                page_size=CDR_PLAN_LIST_PAGE_SIZE,
                request_timeout=CDR_RESCUE_REQUEST_TIMEOUT_SECONDS,
                request_attempts=CDR_RESCUE_REQUEST_ATTEMPTS,
                fuel_type=fuel, plan_type="ALL",
            )
        except Exception as exc:
            return {
                "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages,
                "complete": False, "errors": diagnostics + [f"{fuel} partition failed: {str(exc)[:300]}"],
                "updated_since": str(updated_since or ""), "page_size": CDR_PLAN_LIST_PAGE_SIZE,
                "partitioned_recovery": True, "confirmation": "failed-partitioned-recovery",
            }
        total_pages += int(fuel_snapshot.get("pages") or 0)
        accepted = fuel_snapshot

        if not fuel_snapshot.get("complete"):
            # Further partition this fuel by the complete CDS plan-type enum. We only accept
            # the split if its row count agrees with the fuel-level declared total (when the
            # latter is available), so a future/unknown type cannot be silently dropped.
            type_merged: Dict[str, Dict[str, Any]] = {}
            type_pages = 0
            type_errors: List[str] = []
            type_declared_sum = 0
            type_declared_known = True
            for plan_type in ("MARKET", "STANDING", "REGULATED"):
                try:
                    part = _plan_list_once(
                        retailer, progress, deadline, updated_since=updated_since,
                        page_size=CDR_PLAN_LIST_PAGE_SIZE,
                        request_timeout=CDR_RESCUE_REQUEST_TIMEOUT_SECONDS,
                        request_attempts=CDR_RESCUE_REQUEST_ATTEMPTS,
                        fuel_type=fuel, plan_type=plan_type,
                    )
                except Exception as exc:
                    type_errors.append(f"{fuel}/{plan_type} failed: {str(exc)[:240]}")
                    continue
                type_pages += int(part.get("pages") or 0)
                if not part.get("complete"):
                    type_errors.extend(f"{fuel}/{plan_type}: {e}" for e in (part.get("errors") or [])[:3])
                    continue
                declared = part.get("declared_records")
                if declared is None:
                    type_declared_known = False
                else:
                    type_declared_sum += int(declared)
                for plan in part.get("plans") or []:
                    pid = str(plan.get("planId") or "").strip() if isinstance(plan, dict) else ""
                    if pid:
                        type_merged[pid] = plan

            fuel_declared = fuel_snapshot.get("declared_records")
            if type_errors:
                return {
                    "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages + type_pages,
                    "complete": False, "errors": diagnostics + type_errors,
                    "updated_since": str(updated_since or ""), "page_size": CDR_PLAN_LIST_PAGE_SIZE,
                    "partitioned_recovery": True, "confirmation": "failed-partitioned-recovery",
                }
            if fuel_declared is not None and len(type_merged) != int(fuel_declared):
                return {
                    "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages + type_pages,
                    "complete": False,
                    "errors": diagnostics + [
                        f"{fuel} partition declared {fuel_declared} plans but type shards recovered {len(type_merged)}"
                    ],
                    "updated_since": str(updated_since or ""), "page_size": CDR_PLAN_LIST_PAGE_SIZE,
                    "partitioned_recovery": True, "confirmation": "failed-partitioned-recovery",
                }
            if fuel_declared is not None and type_declared_known and type_declared_sum != int(fuel_declared):
                return {
                    "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages + type_pages,
                    "complete": False,
                    "errors": diagnostics + [
                        f"{fuel} type-shard declared totals {type_declared_sum} != fuel total {fuel_declared}"
                    ],
                    "updated_since": str(updated_since or ""), "page_size": CDR_PLAN_LIST_PAGE_SIZE,
                    "partitioned_recovery": True, "confirmation": "failed-partitioned-recovery",
                }
            accepted = {
                "plans": list(type_merged.values()), "plan_ids": set(type_merged),
                "pages": type_pages, "complete": True, "errors": [],
                "declared_records": fuel_declared if fuel_declared is not None else len(type_merged),
            }
            diagnostics.append(f"{fuel} recovered via plan-type shards")
            total_pages += type_pages

        declared = accepted.get("declared_records")
        if declared is None:
            all_declared_known = False
        else:
            accepted_declared += int(declared)
        for plan in accepted.get("plans") or []:
            pid = str(plan.get("planId") or "").strip() if isinstance(plan, dict) else ""
            if not pid:
                return {
                    "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages,
                    "complete": False, "errors": diagnostics + [f"{fuel} partition returned plan without planId"],
                    "updated_since": str(updated_since or ""), "page_size": CDR_PLAN_LIST_PAGE_SIZE,
                    "partitioned_recovery": True, "confirmation": "failed-partitioned-recovery",
                }
            if pid in merged:
                return {
                    "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages,
                    "complete": False, "errors": diagnostics + [f"planId {pid} appeared in multiple fuel partitions"],
                    "updated_since": str(updated_since or ""), "page_size": CDR_PLAN_LIST_PAGE_SIZE,
                    "partitioned_recovery": True, "confirmation": "failed-partitioned-recovery",
                }
            merged[pid] = plan

    if all_declared_known and accepted_declared != len(merged):
        return {
            "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages,
            "complete": False,
            "errors": diagnostics + [f"partition totals declared {accepted_declared} plans but recovered {len(merged)}"],
            "updated_since": str(updated_since or ""), "page_size": CDR_PLAN_LIST_PAGE_SIZE,
            "partitioned_recovery": True, "confirmation": "failed-partitioned-recovery",
        }
    return {
        "plans": list(merged.values()), "plan_ids": set(merged), "pages": total_pages,
        "complete": True, "errors": diagnostics, "updated_since": str(updated_since or ""),
        "page_size": CDR_PLAN_LIST_PAGE_SIZE,
        "declared_records": accepted_declared if all_declared_known else None,
        "partitioned_recovery": True, "rescue_attempted": True, "rescue_succeeded": True,
        "confirmation": "partitioned-fuel-type-recovery",
    }


def _snapshot_allows_partitioned_recovery(snapshot: Optional[Dict[str, Any]]) -> bool:
    if not snapshot or snapshot.get("complete"):
        return False
    text = " ".join(str(x).lower() for x in (snapshot.get("errors") or []))
    # Only recover catalogue-shape/pagination instability this way. Endpoint/auth/version errors
    # remain genuine source failures and should not fan out into nine redundant requests.
    signals = ("unique plans", "pagination", "repeated page", "totalpages", "totalrecords",
               "logical pages", "changed during", "internally inconsistent")
    return any(token in text for token in signals)


def _membership_keys(plans: Iterable[Dict[str, Any]], fuels: Sequence[str] = ("ELECTRICITY", "GAS")) -> set[str]:
    keys: set[str] = set()
    requested = {str(f).upper() for f in fuels}
    for plan in plans:
        if not isinstance(plan, dict):
            continue
        plan_id = str(plan.get("planId") or "").strip()
        if not plan_id:
            continue
        for fuel in requested:
            if _fuel_matches(plan, fuel):
                keys.add(f"{plan_id}::{fuel}")
    return keys


def _plan_list_snapshot(retailer: Dict[str, str], progress: Optional["_ProgressReporter"] = None,
                        deadline: Optional[float] = None, updated_since: str = "",
                        expected_membership: Optional[set[str]] = None,
                        fuels: Sequence[str] = ("ELECTRICITY", "GAS")) -> Dict[str, Any]:
    # Normal path uses the AER maximum page size for speed. A verified AER source which fails
    # listing receives one targeted recovery pass with smaller responses, a longer per-request
    # timeout and more retries. This is deliberately fail-closed: rescue must itself produce a
    # complete catalogue before the endpoint is considered covered. Register-only probes are not
    # retried here because their failure is not evidence of an Energy PRD coverage gap.
    primary_error = ""
    try:
        first = _plan_list_once(retailer, progress, deadline, updated_since=updated_since)
    except Exception as exc:
        primary_error = str(exc)[:500]
        if not _energy_source_is_coverage_required(retailer):
            raise
        first = None

    rescue_needed = first is None or not bool(first.get("complete"))
    if rescue_needed and _energy_source_is_coverage_required(retailer):
        if progress:
            progress.page(retailer.get("name", "Energy retailer") + " · recovery", 1)
        try:
            rescue = _plan_list_once(
                retailer, progress, deadline, updated_since=updated_since,
                page_size=CDR_PLAN_LIST_RESCUE_PAGE_SIZE,
                request_timeout=CDR_RESCUE_REQUEST_TIMEOUT_SECONDS,
                request_attempts=CDR_RESCUE_REQUEST_ATTEMPTS,
            )
            rescue["rescue_attempted"] = True
            rescue["rescue_page_size"] = CDR_PLAN_LIST_RESCUE_PAGE_SIZE
            if primary_error:
                rescue["primary_error"] = primary_error
            elif first is not None and first.get("errors"):
                rescue["primary_errors"] = list(first.get("errors") or [])[:10]
            if rescue.get("complete"):
                first = rescue
                first["rescue_succeeded"] = True
            elif first is None:
                first = rescue
            else:
                # Preserve both diagnostic sets while remaining incomplete. Never merge partial
                # catalogues into a supposedly verified seed.
                first = dict(rescue)
                first["complete"] = False
                first["errors"] = (
                    ([f"primary: {primary_error}"] if primary_error else
                     [f"primary: {e}" for e in (first.get("primary_errors") or [])])
                    + [f"recovery: {e}" for e in (rescue.get("errors") or [])]
                )
        except Exception as rescue_exc:
            if first is None:
                raise RuntimeError(
                    f"Primary catalogue request failed ({primary_error or 'unknown'}); "
                    f"recovery request also failed ({str(rescue_exc)[:350]})"
                ) from rescue_exc
            first = dict(first)
            first["complete"] = False
            first["rescue_attempted"] = True
            first["rescue_error"] = str(rescue_exc)[:500]
            first["errors"] = list(first.get("errors") or []) + [f"recovery failed: {str(rescue_exc)[:350]}"]

    if first is not None and _energy_source_is_coverage_required(retailer) and _snapshot_allows_partitioned_recovery(first):
        try:
            partitioned = _plan_list_partitioned_recovery(
                retailer, progress, deadline, updated_since=updated_since
            )
            if partitioned.get("complete"):
                # Preserve the original diagnostics for auditability while accepting the
                # independently complete, disjoint recovery snapshot. Every plan which was
                # visible in the unstable ALL response must also be present in the partitioned
                # union; otherwise the recovery itself may have narrowed the market.
                observed_ids = set(first.get("plan_ids") or [])
                recovered_ids = set(partitioned.get("plan_ids") or [])
                if not observed_ids.issubset(recovered_ids):
                    missing_observed = sorted(observed_ids - recovered_ids)[:5]
                    partitioned["complete"] = False
                    partitioned["errors"] = list(partitioned.get("errors") or []) + [
                        f"partitioned recovery omitted {len(observed_ids - recovered_ids)} plan(s) observed in ALL response: {missing_observed}"
                    ]
                else:
                    partitioned["primary_errors"] = list(first.get("errors") or [])[:10]
                    partitioned["all_declared_records"] = first.get("declared_records")
                    partitioned["all_observed_unique"] = len(observed_ids)
                    first = partitioned
            if not partitioned.get("complete"):
                first = dict(first)
                first["partitioned_recovery"] = True
                first["partitioned_errors"] = list(partitioned.get("errors") or [])[:10]
                first["errors"] = list(first.get("errors") or []) + [
                    f"partitioned recovery: {e}" for e in (partitioned.get("errors") or [])[:5]
                ]
        except Exception as partition_exc:
            first = dict(first)
            first["partitioned_recovery"] = True
            first["partitioned_error"] = str(partition_exc)[:500]
            first["errors"] = list(first.get("errors") or []) + [
                f"partitioned recovery failed: {str(partition_exc)[:350]}"
            ]

    if first is None:
        raise RuntimeError(primary_error or "Energy catalogue listing failed")
    if updated_since:
        first["confirmation"] = "partitioned-incremental-recovery" if first.get("partitioned_recovery") else "incremental"
    elif first.get("partitioned_recovery") and first.get("complete"):
        first["confirmation"] = "partitioned-fuel-type-recovery"
    else:
        first["confirmation"] = "recovered-small-pages" if first.get("rescue_succeeded") else "single-pass"
    if updated_since or not first.get("complete") or int(first.get("pages") or 0) <= 1:
        return first

    # A second full catalogue pass is only needed when pass #1 would cause a destructive
    # lifecycle change. Pure additions are safe to accept immediately; unchanged membership
    # is already confirmed by the previous validated cache.
    first_membership = _membership_keys(first.get("plans") or [], fuels)
    if expected_membership is not None:
        expected = set(expected_membership)
        potential_removals = expected - first_membership
        if not potential_removals:
            first["confirmation"] = (
                "partitioned-no-destructive-change" if first.get("partitioned_recovery")
                else "no-destructive-change"
            )
            return first

    # If the ALL-catalogue path was unstable but the disjoint fuel/type recovery was complete,
    # confirm destructive/initial membership with the same stable strategy rather than falling
    # straight back to the known-unstable ALL pagination. This costs extra calls only for the
    # problematic retailer and avoids accepting an off-by-one page boundary snapshot.
    if first.get("partitioned_recovery"):
        second_partitioned = _plan_list_partitioned_recovery(retailer, progress, deadline, updated_since="")
        second_membership = _membership_keys(second_partitioned.get("plans") or [], fuels)
        if second_partitioned.get("complete") and first_membership == second_membership:
            first["confirmation"] = "confirmed-double-partitioned-pass"
            first["second_partition_pages"] = int(second_partitioned.get("pages") or 0)
            return first
        merged = {str(p.get("planId") or ""): p for p in first.get("plans") or [] if str(p.get("planId") or "")}
        for plan in second_partitioned.get("plans") or []:
            pid = str(plan.get("planId") or "")
            if pid:
                merged[pid] = plan
        return {
            "plans": list(merged.values()), "plan_ids": set(merged),
            "pages": max(int(first.get("pages") or 0), int(second_partitioned.get("pages") or 0)),
            "complete": False,
            "errors": list(first.get("errors") or []) + list(second_partitioned.get("errors") or []) +
                      ["partitioned CURRENT catalogue changed between confirmation passes"],
            "updated_since": "", "confirmation": "failed-double-partitioned-pass",
            "partitioned_recovery": True,
        }

    try:
        second = _plan_list_once(retailer, progress, deadline, updated_since="")
        if not second.get("complete") and _energy_source_is_coverage_required(retailer):
            second = _plan_list_once(
                retailer, progress, deadline, updated_since="",
                page_size=CDR_PLAN_LIST_RESCUE_PAGE_SIZE,
                request_timeout=CDR_RESCUE_REQUEST_TIMEOUT_SECONDS,
                request_attempts=CDR_RESCUE_REQUEST_ATTEMPTS,
            )
            second["rescue_attempted"] = True
    except Exception as exc:
        if not _energy_source_is_coverage_required(retailer):
            raise
        second = _plan_list_once(
            retailer, progress, deadline, updated_since="",
            page_size=CDR_PLAN_LIST_RESCUE_PAGE_SIZE,
            request_timeout=CDR_RESCUE_REQUEST_TIMEOUT_SECONDS,
            request_attempts=CDR_RESCUE_REQUEST_ATTEMPTS,
        )
        second["rescue_attempted"] = True
        second["primary_error"] = str(exc)[:500]
    second_membership = _membership_keys(second.get("plans") or [], fuels)
    if not second.get("complete") or first_membership != second_membership:
        merged = {str(p.get("planId") or ""): p for p in first.get("plans") or [] if str(p.get("planId") or "")}
        for plan in second.get("plans") or []:
            pid = str(plan.get("planId") or "")
            if pid:
                merged[pid] = plan
        return {"plans": list(merged.values()), "plan_ids": set(merged),
                "pages": max(int(first.get("pages") or 0), int(second.get("pages") or 0)),
                "complete": False, "errors": list(first.get("errors") or []) + list(second.get("errors") or []) +
                ["CURRENT catalogue changed between confirmation passes"], "updated_since": "",
                "confirmation": "failed-double-pass"}
    second["confirmation"] = "confirmed-double-pass"
    return second


def _list_plans(retailer: Dict[str, str], fuel: str, deadline: Optional[float] = None) -> Iterable[Dict[str, Any]]:
    snapshot = _plan_list_snapshot(retailer, None, deadline)
    for plan in snapshot["plans"]:
        if _fuel_matches(plan, fuel):
            yield plan


def _detail_plan(retailer: Dict[str, str], plan_id: str, deadline: Optional[float] = None) -> Dict[str, Any]:
    errors: List[str] = []
    for version in CDR_DETAIL_API_VERSIONS:
        try:
            payload = _request_json(
                _detail_url(retailer["base_uri"], plan_id),
                {"Accept": "application/json", "x-v": str(version), "x-min-v": "1"},
                deadline=deadline,
            )
            data = payload.get("data") or payload
            if not isinstance(data, dict):
                raise ValueError(f"Plan Detail v{version} returned no plan object")
            return data
        except _HttpStatusError as exc:
            errors.append(f"v{version}=HTTP {exc.status}")
            # Match desktop v80: only version-negotiation failure (406) justifies trying
            # a retired Detail version. 404/resource/network failures are meaningful and
            # must not be multiplied across v3/v2/v1.
            if exc.status == 406 and version != CDR_DETAIL_API_VERSIONS[-1]:
                continue
            raise RuntimeError(f"Unable to fetch plan detail for {plan_id}: " + "; ".join(errors)) from exc
        except Exception as exc:
            errors.append(f"v{version}={exc}")
            raise RuntimeError(f"Unable to fetch plan detail for {plan_id}: " + "; ".join(errors)) from exc
    raise RuntimeError(f"Unable to fetch plan detail for {plan_id}: " + "; ".join(errors))


class _ProgressReporter:
    """Atomic, thread-safe progress file writer used by the Android polling UI.

    Detail events are intentionally throttled: the UI polls every 200 ms, so writing one
    temporary JSON file for every plan only adds flash I/O without making progress smoother.
    Stage transitions, endpoint completion and final status still flush immediately.
    """
    def __init__(self, path: str = "", total_endpoints: int = 0, kind: str = "cdr") -> None:
        self.path = str(path or "")
        self.kind = kind
        self._lock = threading.RLock()
        self._last_write_monotonic = 0.0
        self._pending_detail_events = 0
        self.state: Dict[str, Any] = {
            "kind": kind, "percent": 0, "stage": "Starting", "query": "", "current": "",
            "endpoints_total": max(0, int(total_endpoints)), "endpoints_listed": 0,
            "endpoints_done": 0, "details_total": 0, "details_done": 0, "updated_at": _now(),
        }

    def _recalculate(self) -> None:
        total_ep = max(1, int(self.state.get("endpoints_total") or 0))
        listed = min(total_ep, int(self.state.get("endpoints_listed") or 0))
        done = min(total_ep, int(self.state.get("endpoints_done") or 0))
        details_total = max(0, int(self.state.get("details_total") or 0))
        details_done = min(details_total, int(self.state.get("details_done") or 0))
        list_share = 35.0 * listed / total_ep
        detail_share = (55.0 * details_done / details_total) if details_total else 0.0
        endpoint_share = 9.0 * done / total_ep
        value = min(99, max(int(self.state.get("percent") or 0), int(list_share + detail_share + endpoint_share)))
        self.state["percent"] = value
        self.state["updated_at"] = _now()

    def _write(self, force: bool = False) -> None:
        with self._lock:
            if not self.path:
                return
            now_mono = time.monotonic()
            if not force:
                elapsed = now_mono - self._last_write_monotonic
                if elapsed < CDR_PROGRESS_MIN_WRITE_INTERVAL_SECONDS and self._pending_detail_events < CDR_PROGRESS_DETAIL_BATCH:
                    return
            os.makedirs(os.path.dirname(os.path.abspath(self.path)), exist_ok=True)
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.state, f, separators=(",", ":"))
            os.replace(tmp, self.path)
            self._last_write_monotonic = now_mono
            self._pending_detail_events = 0

    def start(self, stage: str = "Discovering CDR retailers") -> None:
        with self._lock:
            self.state.update({"stage": stage, "query": stage, "current": "", "percent": 1})
            self._write(force=True)

    def page(self, retailer: str, page: int) -> None:
        with self._lock:
            self.state.update({"stage": "Listing CDR plans", "query": f"Listing CDR plans · {retailer}", "current": f"Page {page}"})
            self._write()

    def listed(self, retailer: str, count: int, pages: int = 1) -> None:
        with self._lock:
            self.state["endpoints_listed"] = int(self.state.get("endpoints_listed") or 0) + 1
            self.state["details_total"] = int(self.state.get("details_total") or 0) + max(0, int(count))
            self.state.update({"stage": "Listing CDR plans", "query": f"Listing CDR plans · {retailer}", "current": f"{count} changed/current plan(s) · {pages} page(s)"})
            self._recalculate()
            self._write(force=True)

    def detail_started(self, retailer: str, plan_name: str, plan_id: str) -> None:
        with self._lock:
            shown = str(plan_id)[:18] + ("…" if len(str(plan_id)) > 18 else "")
            self.state.update({"stage": "Fetching plan detail", "query": f"Fetching plan detail · {retailer}", "current": f"{plan_name or 'Plan'} · {shown}"})
            self._write()

    def detail_done(self, retailer: str, plan_name: str = "", plan_id: str = "") -> None:
        with self._lock:
            self.state["details_done"] = int(self.state.get("details_done") or 0) + 1
            self._pending_detail_events += 1
            if retailer:
                shown = str(plan_id)[:18] + ("…" if len(str(plan_id)) > 18 else "")
                self.state.update({"stage": "Fetching plan detail", "query": f"Fetching plan detail · {retailer}", "current": f"{plan_name or 'Plan'}{(' · ' + shown) if shown else ''}"})
            self._recalculate()
            self._write()

    def endpoint_done(self, retailer: str, status: str = "Complete") -> None:
        with self._lock:
            self.state["endpoints_done"] = int(self.state.get("endpoints_done") or 0) + 1
            self.state.update({"stage": "Finalising CDR cache", "query": f"Finalising · {retailer}", "current": status})
            self._recalculate()
            self._write(force=True)

    def finish(self, status: str, message: str) -> None:
        with self._lock:
            self.state.update({"percent": 100, "stage": "Complete" if status != "failed" else "Refresh failed", "query": message, "current": status, "updated_at": _now()})
            self._write(force=True)


def _summary_revision(summary: Dict[str, Any]) -> str:
    last_updated = str(summary.get("lastUpdated") or "").strip()
    if last_updated:
        return "lastUpdated:" + last_updated
    stable = json.dumps(summary, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return "sha256:" + hashlib.sha256(stable.encode("utf-8")).hexdigest()


def _storage_plan_id(source_plan_id: str, fuel: str, summary: Dict[str, Any], detail: Optional[Dict[str, Any]] = None) -> str:
    actual = str((detail or {}).get("fuelType") or summary.get("fuelType") or "").upper()
    return f"{source_plan_id}::{fuel.upper()}" if actual == "DUAL" else source_plan_id


def _parse_iso_time(value: Any) -> Optional[dt.datetime]:
    text = str(value or "").strip()
    if not text:
        return None
    try:
        parsed = dt.datetime.fromisoformat(text.replace("Z", "+00:00"))
        return parsed if parsed.tzinfo else parsed.replace(tzinfo=dt.timezone.utc)
    except ValueError:
        return None


def _detail_fresh_for_summary(summary: Dict[str, Any], detail: Dict[str, Any]) -> bool:
    if not detail:
        return False
    s_time = _parse_iso_time(summary.get("lastUpdated"))
    d_time = _parse_iso_time(detail.get("lastUpdated"))
    if s_time is not None and d_time is not None and d_time < s_time:
        return False
    source_id = str(summary.get("planId") or "").strip()
    detail_id = str(detail.get("planId") or source_id).strip()
    return not source_id or not detail_id or source_id == detail_id


def _cached_detail_can_reuse(row: sqlite3.Row, incoming_summary: Dict[str, Any]) -> bool:
    try:
        cached_summary = json.loads(row["summary_json"] or "{}")
        detail = json.loads(row["detail_json"] or "{}")
    except Exception:
        return False
    stored_revision = str(row["summary_revision"] or "") if "summary_revision" in row.keys() else ""
    if stored_revision:
        same = stored_revision == _summary_revision(incoming_summary)
    else:
        same = cached_summary == incoming_summary
    return same and isinstance(detail, dict) and _detail_fresh_for_summary(incoming_summary, detail)


def _cached_row_has_detail(row: sqlite3.Row) -> bool:
    keys = set(row.keys())
    if "detail_cached" in keys and row["detail_cached"] is not None:
        try:
            return int(row["detail_cached"] or 0) == 1
        except (TypeError, ValueError):
            return False
    # Compatibility path for unit tests / older callers which deliberately SELECT * one row.
    return bool(str(row["detail_json"] or "").strip()) if "detail_json" in keys else False


def _cached_detail_metadata_can_reuse(row: sqlite3.Row, incoming_summary: Dict[str, Any]) -> bool:
    """Cheap reuse check which never parses/materialises cached Plan Detail JSON."""
    keys = set(row.keys())
    stored_revision = str(row["summary_revision"] or "") if "summary_revision" in keys else ""
    return bool(stored_revision and stored_revision == _summary_revision(incoming_summary) and _cached_row_has_detail(row))


def _load_cached_detail(db_path: str, row: sqlite3.Row, incoming_summary: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Lazy-load one cached Detail payload only when re-normalisation actually needs it."""
    keys = set(row.keys())
    if "detail_json" in keys:
        raw = str(row["detail_json"] or "")
    else:
        retailer_key = str(row["retailer_key"] or "") if "retailer_key" in keys else ""
        plan_id = str(row["plan_id"] or "") if "plan_id" in keys else ""
        if not retailer_key or not plan_id:
            return None
        with _connect(db_path) as con:
            fetched = con.execute(
                "SELECT detail_json FROM energy_plans WHERE retailer_key=? AND plan_id=?",
                (retailer_key, plan_id),
            ).fetchone()
        raw = str(fetched[0] or "") if fetched else ""
    if not raw:
        return None
    try:
        detail = json.loads(raw)
    except Exception:
        return None
    return detail if isinstance(detail, dict) and _detail_fresh_for_summary(incoming_summary, detail) else None


def _cached_row_zero_work(row: Optional[sqlite3.Row], incoming_summary: Dict[str, Any]) -> bool:
    """Return True only when a cached normalized row can be retained without JSON/SQL work."""
    if row is None:
        return False
    keys = set(row.keys())
    stored_revision = str(row["summary_revision"] or "") if "summary_revision" in keys else ""
    version = int(row["normalizer_version"] or 0) if "normalizer_version" in keys else 0
    active = int(row["is_active"] if "is_active" in keys and row["is_active"] is not None else 1) == 1
    return bool(stored_revision and stored_revision == _summary_revision(incoming_summary) and
                version == NORMALIZER_VERSION and active and _cached_row_has_detail(row))


def _summary_fuels(summary: Dict[str, Any], requested: Sequence[str] = ("ELECTRICITY", "GAS")) -> List[str]:
    return [str(f).upper() for f in requested if _fuel_matches(summary, str(f).upper())]


def _state_get(con: sqlite3.Connection, key: str, default: str = "") -> str:
    row = con.execute("SELECT value FROM sync_state WHERE key=?", (key,)).fetchone()
    return str(row[0]) if row else default


def _state_set(con: sqlite3.Connection, key: str, value: Any, when: Optional[str] = None) -> None:
    stamp = when or _now()
    con.execute(
        "INSERT INTO sync_state(key,value,updated_at) VALUES(?,?,?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value,updated_at=excluded.updated_at",
        (key, str(value), stamp),
    )


def _state_bump(con: sqlite3.Connection, key: str, when: Optional[str] = None) -> int:
    try:
        current = int(_state_get(con, key, "0") or 0)
    except Exception:
        current = 0
    current += 1
    _state_set(con, key, current, when)
    return current


def _energy_auto_mode(db_path: str, requested_mode: str = "AUTO") -> Tuple[str, str]:
    """Choose Energy sync behaviour without ever scheduling an automatic national FULL verification.

    AUTO is the routine mobile path. It retrieves each retailer's CURRENT Generic catalogue once,
    compares authoritative membership/revisions with the cache, and only fetches Plan Detail for
    new or changed plans. A suspected removal is re-confirmed for that retailer by
    ``_plan_list_snapshot`` before any cached plan is deactivated. This gives daily withdrawal
    detection without periodically re-running a strict whole-market FULL verification.

    FULL is deliberately explicit: only the Settings "Full verification" action and Energy seed
    generation request it. INCREMENTAL remains available as an internal/diagnostic mode but is
    never selected automatically.
    """
    mode = str(requested_mode or "AUTO").upper()
    if mode not in ("AUTO", "ROUTINE", "FULL", "INCREMENTAL"):
        raise ValueError("energy sync mode must be AUTO, ROUTINE, FULL or INCREMENTAL")
    if mode == "FULL":
        return "FULL", ""
    if mode in ("AUTO", "ROUTINE"):
        return "ROUTINE", ""

    # Explicit incremental mode is retained for diagnostics only. It never falls back to FULL.
    with _connect(db_path) as con:
        _schema(con)
        last_success = _state_get(con, "last_energy_successful_sync_at")
    now = dt.datetime.now(dt.timezone.utc)
    success_time = _parse_iso_time(last_success)
    if success_time is None:
        success_time = now - dt.timedelta(hours=CDR_INCREMENTAL_OVERLAP_HOURS)
    since = min(success_time, now) - dt.timedelta(hours=CDR_INCREMENTAL_OVERLAP_HOURS)
    return "INCREMENTAL", since.replace(microsecond=0).isoformat()



def _retailer_watermark_state_key(retailer_key: str) -> str:
    return f"energy_retailer_watermark::{retailer_key}"


def _retailer_empty_state_key(retailer_key: str) -> str:
    return f"energy_retailer_verified_empty::{retailer_key}"


def _retailer_sync_since(raw_watermark: str) -> str:
    parsed = _parse_iso_time(raw_watermark)
    if parsed is None:
        return ""
    now = dt.datetime.now(dt.timezone.utc)
    parsed = min(parsed, now) - dt.timedelta(minutes=CDR_RETAILER_OVERLAP_MINUTES)
    return parsed.replace(microsecond=0).isoformat()


def _summary_generic_fuel(plan: Dict[str, Any]) -> str:
    fuel = str(plan.get("fuelType") or "").upper().strip()
    if fuel in ("ELECTRICITY", "GAS", "DUAL"):
        return fuel
    # Missing/unknown metadata is deliberately treated as ALL so the targeted optimiser
    # cannot silently narrow a retailer's market.
    return "ALL"


def _summary_generic_type(plan: Dict[str, Any]) -> str:
    value = str(plan.get("type") or plan.get("planType") or "").upper().strip()
    return value if value in ("MARKET", "STANDING", "REGULATED") else "ALL"


def _cached_generic_membership(rows: Sequence[sqlite3.Row]) -> Dict[str, Any]:
    """Build unique Generic-plan membership/category sets from normalized cached rows."""
    summaries: Dict[str, Dict[str, Any]] = {}
    for row in rows:
        try:
            active = int(row["is_active"] if "is_active" in row.keys() and row["is_active"] is not None else 1) == 1
        except Exception:
            active = True
        if not active:
            continue
        source = str(row["source_plan_id"] or row["plan_id"] or "") if "source_plan_id" in row.keys() else str(row["plan_id"] or "")
        if not source or source in summaries:
            continue
        try:
            summary = json.loads(row["summary_json"] or "{}")
            if not isinstance(summary, dict):
                summary = {}
        except Exception:
            summary = {}
        summaries[source] = summary
    all_ids = set(summaries)
    by_fuel: Dict[str, set[str]] = {f: set() for f in ("ELECTRICITY", "GAS", "DUAL", "ALL")}
    by_fuel_type: Dict[Tuple[str, str], set[str]] = {}
    unknown = False
    for pid, summary in summaries.items():
        fuel = _summary_generic_fuel(summary)
        typ = _summary_generic_type(summary)
        by_fuel.setdefault(fuel, set()).add(pid)
        by_fuel_type.setdefault((fuel, typ), set()).add(pid)
        if fuel == "ALL" or typ == "ALL":
            unknown = True
    return {"ids": all_ids, "summaries": summaries, "by_fuel": by_fuel,
            "by_fuel_type": by_fuel_type, "unknown_categories": unknown}


def _confirmed_filtered_snapshot(retailer: Dict[str, str], progress: Optional["_ProgressReporter"],
                                 deadline: Optional[float], fuel_type: str, plan_type: str,
                                 expected_ids: set[str]) -> Dict[str, Any]:
    """Fetch one filtered CURRENT partition and double-confirm destructive membership changes."""
    def fetch() -> Dict[str, Any]:
        first = _plan_list_once(retailer, progress, deadline, fuel_type=fuel_type, plan_type=plan_type)
        if not first.get("complete") and _energy_source_is_coverage_required(retailer):
            first = _plan_list_once(
                retailer, progress, deadline, page_size=CDR_PLAN_LIST_RESCUE_PAGE_SIZE,
                request_timeout=CDR_RESCUE_REQUEST_TIMEOUT_SECONDS,
                request_attempts=CDR_RESCUE_REQUEST_ATTEMPTS,
                fuel_type=fuel_type, plan_type=plan_type,
            )
            first["rescue_attempted"] = True
        return first

    first = fetch()
    if not first.get("complete"):
        return first
    current = set(first.get("plan_ids") or [])
    if not (set(expected_ids) - current):
        first["confirmation"] = "targeted-no-destructive-change"
        return first
    second = fetch()
    second_ids = set(second.get("plan_ids") or [])
    if second.get("complete") and current == second_ids:
        second["confirmation"] = "targeted-confirmed-double-pass"
        return second
    merged = {str(p.get("planId") or ""): p for p in first.get("plans") or [] if str(p.get("planId") or "")}
    for p in second.get("plans") or []:
        pid = str(p.get("planId") or "")
        if pid:
            merged[pid] = p
    return {
        "plans": list(merged.values()), "plan_ids": set(merged),
        "pages": max(int(first.get("pages") or 0), int(second.get("pages") or 0)),
        "complete": False,
        "errors": list(first.get("errors") or []) + list(second.get("errors") or []) +
                  ["targeted CURRENT partition changed between confirmation passes"],
        "fuel_type": fuel_type, "plan_type": plan_type,
        "confirmation": "targeted-failed-double-pass",
    }


def _routine_retailer_snapshot(retailer: Dict[str, str], cached_rows: Sequence[sqlite3.Row],
                               watermark: str, progress: Optional["_ProgressReporter"],
                               deadline: Optional[float], verified_empty: bool = False) -> Dict[str, Any]:
    """Fast routine sync: count probe + delta, with surgical membership reconciliation.

    Most retailers need only two small requests: one ``page-size=1`` CURRENT count probe and one
    ``updated-since`` delta. Full membership is fetched only for a retailer/fuel/type partition
    whose count maths proves that a new plan was missed or an old plan vanished.
    """
    cached = _cached_generic_membership(cached_rows)
    cached_ids: set[str] = set(cached["ids"])
    since = _retailer_sync_since(watermark)
    # A previously validated empty catalogue is real market state, not an uninitialised cache.
    # One CURRENT count probe is sufficient to prove it remains empty. If it becomes non-empty,
    # recover that retailer with an authoritative snapshot because there is no old membership to
    # reconstruct from a delta. This prevents empty catalogues being bootstrapped on every scan.
    if not cached_ids and verified_empty:
        count = _plan_count_probe(retailer, deadline, "ALL", "ALL")
        total = int(count["total_records"])
        if total == 0:
            synthetic = {
                "plans": [], "plan_ids": set(), "pages": 1, "complete": True, "errors": [],
                "confirmation": "verified-empty-count-probe", "declared_records": 0,
                "routine_delta": True,
            }
            return {
                "snapshot": synthetic, "summaries": [], "confirmed_removed_source_ids": set(),
                "routine_strategy": "verified-empty-count-probe", "watermark_used": since,
                "count_probe": 0,
            }
        snap = _plan_list_snapshot(retailer, progress, deadline, expected_membership=None,
                                   fuels=("ELECTRICITY", "GAS"))
        return {
            "snapshot": snap, "summaries": list(snap.get("plans") or []),
            "confirmed_removed_source_ids": set(), "routine_strategy": "verified-empty-became-active",
            "watermark_used": since, "count_probe": total,
        }

    # A seed can intentionally omit one retailer. Without cached membership (and without a
    # verified-empty marker), a delta cannot reconstruct old CURRENT plans, so recover this
    # retailer only (never national FULL).
    if not cached_ids:
        snap = _plan_list_snapshot(retailer, progress, deadline, expected_membership=None,
                                   fuels=("ELECTRICITY", "GAS"))
        return {
            "snapshot": snap, "summaries": list(snap.get("plans") or []),
            "confirmed_removed_source_ids": set(), "routine_strategy": "retailer-bootstrap",
            "watermark_used": "", "count_probe": snap.get("declared_records"),
        }

    if not since:
        # No trustworthy retailer/global watermark: reconcile this retailer only.
        snap = _plan_list_snapshot(retailer, progress, deadline, expected_membership=_membership_keys(
            [v for v in cached["summaries"].values() if isinstance(v, dict)], ("ELECTRICITY", "GAS")
        ), fuels=("ELECTRICITY", "GAS"))
        current_ids = set(snap.get("plan_ids") or [])
        return {
            "snapshot": snap, "summaries": list(snap.get("plans") or []),
            "confirmed_removed_source_ids": cached_ids - current_ids if snap.get("complete") else set(),
            "routine_strategy": "retailer-no-watermark", "watermark_used": "",
            "count_probe": snap.get("declared_records"),
        }

    count = _plan_count_probe(retailer, deadline, "ALL", "ALL")
    delta = _plan_list_once(retailer, progress, deadline, updated_since=since)
    if not delta.get("complete"):
        # A malformed delta must never advance the watermark or cause destructive changes.
        raise RuntimeError("Incremental catalogue validation failed: " + "; ".join(delta.get("errors") or [])[:350])
    delta_plans = [p for p in delta.get("plans") or [] if isinstance(p, dict) and str(p.get("planId") or "").strip()]
    delta_ids = {str(p.get("planId") or "").strip() for p in delta_plans}
    new_ids = delta_ids - cached_ids
    total = int(count["total_records"])
    category_changed = False
    for p in delta_plans:
        pid = str(p.get("planId") or "").strip()
        old = cached["summaries"].get(pid)
        if isinstance(old, dict) and (
            _summary_generic_fuel(old) != _summary_generic_fuel(p) or
            _summary_generic_type(old) != _summary_generic_type(p)
        ):
            category_changed = True
            break

    # The set equation is decisive unless an existing ID moved category. Category moves are rare
    # and get a retailer-only authoritative reconciliation to prevent a stale old-fuel row.
    if total == len(cached_ids | new_ids) and not category_changed:
        synthetic = {
            "plans": delta_plans, "plan_ids": delta_ids, "pages": int(delta.get("pages") or 0) + 1,
            "complete": True, "errors": [], "confirmation": "count+delta-no-membership-change",
            "declared_records": total, "routine_delta": True,
        }
        return {
            "snapshot": synthetic, "summaries": delta_plans,
            "confirmed_removed_source_ids": set(), "routine_strategy": "count+delta",
            "watermark_used": since, "count_probe": total,
        }

    # Membership/category changed. Find the smallest authoritative partition which explains it.
    # A category move or unknown cached category deliberately forces a retailer-level
    # reconciliation because source-ID-only removal would otherwise be ambiguous.
    if category_changed or cached.get("unknown_categories"):
        snap = _plan_list_snapshot(retailer, progress, deadline, expected_membership=None,
                                   fuels=("ELECTRICITY", "GAS"))
        current_ids = set(snap.get("plan_ids") or [])
        return {
            "snapshot": snap, "summaries": list(snap.get("plans") or []),
            "confirmed_removed_source_ids": cached_ids - current_ids if snap.get("complete") else set(),
            "routine_strategy": "retailer-unknown-category-reconcile", "watermark_used": since,
            "count_probe": total,
        }

    delta_by_fuel: Dict[str, set[str]] = {f: set() for f in ("ELECTRICITY", "GAS", "DUAL")}
    delta_by_ft: Dict[Tuple[str, str], set[str]] = {}
    for p in delta_plans:
        pid = str(p.get("planId") or "").strip()
        fuel = _summary_generic_fuel(p)
        typ = _summary_generic_type(p)
        if fuel in delta_by_fuel:
            delta_by_fuel[fuel].add(pid)
            delta_by_ft.setdefault((fuel, typ), set()).add(pid)

    fuel_counts = {fuel: int(_plan_count_probe(retailer, deadline, fuel, "ALL")["total_records"])
                   for fuel in ("ELECTRICITY", "GAS", "DUAL")}
    if sum(fuel_counts.values()) != total:
        snap = _plan_list_snapshot(retailer, progress, deadline, expected_membership=None,
                                   fuels=("ELECTRICITY", "GAS"))
        current_ids = set(snap.get("plan_ids") or [])
        return {
            "snapshot": snap, "summaries": list(snap.get("plans") or []),
            "confirmed_removed_source_ids": cached_ids - current_ids if snap.get("complete") else set(),
            "routine_strategy": "retailer-fuel-count-inconsistent", "watermark_used": since,
            "count_probe": total,
        }

    summaries_by_id = {str(p.get("planId") or "").strip(): p for p in delta_plans}
    confirmed_removed: set[str] = set()
    reconciliation_pages = 0
    affected_fuels: List[str] = []
    for fuel in ("ELECTRICITY", "GAS", "DUAL"):
        cached_fuel = set(cached["by_fuel"].get(fuel, set()))
        new_fuel = delta_by_fuel.get(fuel, set()) - cached_ids
        if fuel_counts[fuel] == len(cached_fuel | new_fuel):
            continue
        affected_fuels.append(fuel)

        # Narrow again by plan type when the three type counts are internally complete.
        type_counts = {typ: int(_plan_count_probe(retailer, deadline, fuel, typ)["total_records"])
                       for typ in ("MARKET", "STANDING", "REGULATED")}
        can_split_type = sum(type_counts.values()) == fuel_counts[fuel]
        affected_types: List[str] = []
        if can_split_type:
            for typ in ("MARKET", "STANDING", "REGULATED"):
                cached_part = set(cached["by_fuel_type"].get((fuel, typ), set()))
                new_part = set(delta_by_ft.get((fuel, typ), set())) - cached_ids
                if type_counts[typ] != len(cached_part | new_part):
                    affected_types.append(typ)
        if can_split_type and affected_types:
            partitions = [(fuel, typ, set(cached["by_fuel_type"].get((fuel, typ), set())))
                          for typ in affected_types]
        else:
            partitions = [(fuel, "ALL", cached_fuel)]

        for pfuel, ptype, expected_ids in partitions:
            part = _confirmed_filtered_snapshot(retailer, progress, deadline, pfuel, ptype, expected_ids)
            reconciliation_pages += int(part.get("pages") or 0)
            if not part.get("complete"):
                raise RuntimeError(
                    f"Targeted {pfuel}/{ptype} membership reconciliation failed: " +
                    "; ".join(part.get("errors") or [])[:320]
                )
            current_ids = set(part.get("plan_ids") or [])
            confirmed_removed.update(expected_ids - current_ids)
            for p in part.get("plans") or []:
                if isinstance(p, dict) and str(p.get("planId") or "").strip():
                    summaries_by_id[str(p.get("planId") or "").strip()] = p

    # If partition maths unexpectedly found no affected scope, reconcile this retailer only.
    if not affected_fuels:
        snap = _plan_list_snapshot(retailer, progress, deadline, expected_membership=None,
                                   fuels=("ELECTRICITY", "GAS"))
        current_ids = set(snap.get("plan_ids") or [])
        return {
            "snapshot": snap, "summaries": list(snap.get("plans") or []),
            "confirmed_removed_source_ids": cached_ids - current_ids if snap.get("complete") else set(),
            "routine_strategy": "retailer-count-mismatch-reconcile", "watermark_used": since,
            "count_probe": total,
        }

    synthetic = {
        "plans": list(summaries_by_id.values()), "plan_ids": set(summaries_by_id),
        "pages": int(delta.get("pages") or 0) + 1 + reconciliation_pages,
        "complete": True, "errors": [], "confirmation": "targeted-membership-reconciliation",
        "declared_records": total, "routine_delta": True,
        "affected_fuels": affected_fuels,
    }
    return {
        "snapshot": synthetic, "summaries": list(summaries_by_id.values()),
        "confirmed_removed_source_ids": confirmed_removed,
        "routine_strategy": "targeted-fuel-type", "watermark_used": since,
        "count_probe": total,
    }

def _postcode_token_matches(token: Any, postcode: str) -> bool:
    if isinstance(token, dict):
        start = str(token.get("start") or token.get("from") or token.get("minimum") or "")
        end = str(token.get("end") or token.get("to") or token.get("maximum") or "")
        if start.isdigit() and end.isdigit() and postcode.isdigit():
            return int(start) <= int(postcode) <= int(end)
        token = token.get("postcode") or token.get("value") or ""
    text = str(token or "").strip()
    if text == postcode:
        return True
    if "-" in text:
        a, b = (x.strip() for x in text.split("-", 1))
        if a.isdigit() and b.isdigit() and postcode.isdigit():
            return int(a) <= int(postcode) <= int(b)
    return False


def _flatten_geography(plan: Dict[str, Any]) -> Dict[str, List[Any]]:
    geo = plan.get("geography") or {}
    out: Dict[str, List[Any]] = {
        "included_postcodes": [], "excluded_postcodes": [],
        "included_distributors": [], "excluded_distributors": [],
    }
    if not isinstance(geo, dict):
        return out
    for side in ("included", "excluded"):
        block = geo.get(side) or {}
        blocks = block if isinstance(block, list) else [block]
        for item in blocks:
            if isinstance(item, dict):
                out[f"{side}_postcodes"].extend(item.get("postcodes") or [])
                out[f"{side}_distributors"].extend(item.get("distributors") or [])
    for key, dest in (
        ("includedPostcodes", "included_postcodes"), ("excludedPostcodes", "excluded_postcodes"),
        ("distributors", "included_distributors"),
        ("includedDistributors", "included_distributors"), ("excludedDistributors", "excluded_distributors"),
    ):
        value = geo.get(key)
        if isinstance(value, list):
            out[dest].extend(value)
    return out


def _geography_matches(plan: Dict[str, Any], postcode: str, distributor: str) -> bool:
    geo = _flatten_geography(plan)
    pc = str(postcode or "").strip()
    dist = _norm(distributor)
    if pc and any(_postcode_token_matches(x, pc) for x in geo["excluded_postcodes"]):
        return False
    if dist and any(dist == _norm(x) or dist in _norm(x) or _norm(x) in dist for x in geo["excluded_distributors"]):
        return False
    pc_inclusions = geo["included_postcodes"]
    dist_inclusions = geo["included_distributors"]
    pc_ok = bool(pc and any(_postcode_token_matches(x, pc) for x in pc_inclusions)) if pc_inclusions else None
    dist_ok = bool(dist and any(dist == _norm(x) or dist in _norm(x) or _norm(x) in dist for x in dist_inclusions)) if dist_inclusions else None
    # In CDR geography the inclusion dimensions are alternative ways to identify the covered
    # geography. Do not require both postcode and distributor to be explicitly listed.
    positives = [x for x in (pc_ok, dist_ok) if x is not None]
    return True if not positives else any(positives)


def _customer_type_matches(plan: Dict[str, Any], customer_type: str) -> bool:
    requested = "BUSINESS" if str(customer_type).upper() == "BUSINESS" else "RESIDENTIAL"
    actual = str(plan.get("customerType") or "").upper()
    if not actual:
        return True
    return actual == requested


def _fuel_matches(plan: Dict[str, Any], fuel: str) -> bool:
    actual = str(plan.get("fuelType") or "").upper()
    requested = str(fuel or "").upper()
    return not actual or actual == requested or actual == "DUAL"

def _contract(detail: Dict[str, Any], fuel: str) -> Dict[str, Any]:
    key = "gasContract" if fuel.upper() == "GAS" else "electricityContract"
    contract = detail.get(key) or {}
    return contract if isinstance(contract, dict) else {}


def _as_list(value: Any) -> List[Any]:
    if value is None:
        return []
    return value if isinstance(value, list) else [value]


def _first_supply_cents(contract: Dict[str, Any]) -> Optional[Decimal]:
    for period in _as_list(contract.get("tariffPeriod")):
        if not isinstance(period, dict):
            continue
        # Plan Detail v3 uses dailySupplyCharge for a single daily charge and
        # bandedDailySupplyCharges for stepped day bands. The legacy plural field is
        # still accepted for cached v2-era payloads, but banded charges are not reduced
        # to a misleading single display rate here.
        charge_type = str(period.get("dailySupplyChargeType") or "").upper()
        if charge_type == "BAND" or _as_list(period.get("bandedDailySupplyCharges")):
            continue
        raw = period.get("dailySupplyCharge")
        if raw is None:
            raw = period.get("dailySupplyCharges")
        if isinstance(raw, list):
            raw = raw[0] if len(raw) == 1 else None
        if isinstance(raw, dict):
            raw = raw.get("amount") or raw.get("unitPrice") or raw.get("value")
        amount = _d(raw, None)
        if amount is not None:
            return amount * GST * CENTS
    return None


def _usage_rate_rows(contract: Dict[str, Any]) -> List[Tuple[str, Decimal]]:
    rows: List[Tuple[str, Decimal]] = []
    for period in _as_list(contract.get("tariffPeriod")):
        if not isinstance(period, dict):
            continue
        sr = period.get("singleRate") or {}
        if isinstance(sr, dict):
            rates = _as_list(sr.get("rates"))
            for idx, rate in enumerate(rates):
                if not isinstance(rate, dict):
                    continue
                price = _d(rate.get("unitPrice"), None)
                if price is not None:
                    label = _compact(sr.get("displayName")) or ("Usage" if len(rates) == 1 else f"Usage step {idx + 1}")
                    rows.append((label, price * GST * CENTS))
        for tou in _as_list(period.get("timeOfUseRates")):
            if not isinstance(tou, dict):
                continue
            rates = _as_list(tou.get("rates"))
            for idx, rate in enumerate(rates):
                if not isinstance(rate, dict):
                    continue
                price = _d(rate.get("unitPrice"), None)
                if price is not None:
                    label = _compact(tou.get("displayName") or tou.get("type") or "TOU")
                    if len(rates) > 1:
                        label += f" step {idx + 1}"
                    rows.append((label, price * GST * CENTS))
    return rows



def _normalise_plan(retailer: Dict[str, str], summary: Dict[str, Any], detail: Dict[str, Any], fuel: str) -> Dict[str, Any]:
    contract = _contract(detail, fuel)
    periods = _as_list(contract.get("tariffPeriod"))
    has_tou = any(isinstance(p, dict) and bool(_as_list(p.get("timeOfUseRates"))) for p in periods)
    has_demand = any(isinstance(p, dict) and bool(_as_list(p.get("demandCharges"))) for p in periods)
    controlled = _as_list(contract.get("controlledLoad")); solar = _as_list(contract.get("solarFeedInTariff"))
    rates = _usage_rate_rows(contract)
    avg = (sum((x[1] for x in rates), Decimal("0")) / Decimal(len(rates))) if rates else None
    supply = _first_supply_cents(contract)
    geo = _flatten_geography(detail if detail.get("geography") else summary)
    distributors = sorted({_compact(x) for x in geo["included_distributors"] if _compact(x)})
    source_plan_id = str(detail.get("planId") or summary.get("planId") or "").strip()
    plan_id = _storage_plan_id(source_plan_id, fuel, summary, detail)
    retailer_name = _compact(detail.get("brand") or detail.get("brandName") or summary.get("brand") or retailer.get("name"))
    if isinstance(detail.get("brand"), dict):
        retailer_name = _compact(detail["brand"].get("name") or detail["brand"].get("brandName")) or retailer_name
    app_uri = str(detail.get("applicationUri") or summary.get("applicationUri") or "")
    return {
        "retailer_key": _retailer_key(retailer["base_uri"]), "plan_id": plan_id, "source_plan_id": source_plan_id,
        "summary_revision": _summary_revision(summary), "normalizer_version": NORMALIZER_VERSION, "is_active": 1, "stale_reason": None,
        "fuel_type": fuel.upper(), "retailer_name": retailer_name or retailer.get("name", ""),
        "brand": _compact(summary.get("brand") or retailer.get("brand")),
        "plan_name": _compact(detail.get("displayName") or summary.get("displayName") or "Unnamed plan"),
        "last_updated": str(detail.get("lastUpdated") or summary.get("lastUpdated") or ""),
        "application_uri": app_uri, "source": retailer.get("source", "CDR"),
        "customer_type": str(detail.get("customerType") or summary.get("customerType") or "RESIDENTIAL").upper(),
        "distributors": "; ".join(distributors), "tariff_type": str(contract.get("pricingModel") or "").upper(),
        "is_tou": 1 if has_tou or str(contract.get("pricingModel") or "").upper() == "TIME_OF_USE" else 0,
        "is_flat": 1 if not has_tou and str(contract.get("pricingModel") or "").upper() == "SINGLE_RATE" else 0,
        "has_demand": 1 if has_demand else 0, "has_controlled_load": 1 if controlled else 0, "has_solar": 1 if solar else 0,
        "daily_supply_cents": float(supply) if supply is not None else None, "avg_usage_cents": float(avg) if avg is not None else None,
        "raw_usage_rates": " | ".join(f"{label}: {price:.3f}c/{'MJ' if fuel.upper() == 'GAS' else 'kWh'}" for label, price in rates),
        "summary_json": json.dumps(summary, separators=(",", ":")), "detail_json": json.dumps(detail, separators=(",", ":")),
        "detail_cached": 1,
        "tariff_periods_json": json.dumps(periods, separators=(",", ":")), "controlled_load_json": json.dumps(controlled, separators=(",", ":")),
        "eligibility_json": json.dumps(detail.get("eligibility") or summary.get("eligibility") or [], separators=(",", ":")),
        "metering_charges_json": json.dumps(contract.get("meteringCharges") or [], separators=(",", ":")),
        "solar_feed_in_json": json.dumps(solar, separators=(",", ":")),
    }


def _upsert_plan(con: sqlite3.Connection, record: Dict[str, Any]) -> None:
    fields = [
        "retailer_key", "plan_id", "source_plan_id", "summary_revision", "normalizer_version", "is_active", "stale_reason",
        "fuel_type", "retailer_name", "brand", "plan_name", "last_updated", "application_uri",
        "summary_json", "detail_json", "detail_cached", "cached_at", "source", "customer_type", "distributors",
        "tariff_type", "is_tou", "is_flat", "has_demand", "has_controlled_load", "has_solar",
        "daily_supply_cents", "avg_usage_cents", "raw_usage_rates", "eligibility_json",
        "metering_charges_json", "tariff_periods_json", "controlled_load_json", "solar_feed_in_json",
    ]
    values = [record.get(f) for f in fields]; values[fields.index("cached_at")] = _now()
    updates = ",".join(f"{f}=excluded.{f}" for f in fields if f not in ("retailer_key", "plan_id"))
    con.execute(f"INSERT INTO energy_plans({','.join(fields)}) VALUES({','.join('?' for _ in fields)}) ON CONFLICT(retailer_key,plan_id) DO UPDATE SET {updates}", values)
    cdr_fields = [
        "plan_id", "source_plan_id", "summary_revision", "normalizer_version", "is_active", "stale_reason", "provider", "name",
        "customer_type", "distributors", "tariff_type", "is_tou", "is_flat", "has_demand", "has_controlled_load",
        "has_solar", "daily_supply_cents", "avg_usage_cents", "last_updated", "raw_usage_rates", "website", "source",
        "fuel_type", "retailer_key", "detail_json", "summary_json", "tariff_periods_json", "controlled_load_json",
        "eligibility_json", "metering_charges_json", "solar_feed_in_json",
    ]
    cdr_record = dict(record, provider=record.get("retailer_name"), name=record.get("plan_name"), website=record.get("application_uri"))
    cdr_values = [cdr_record.get(f) for f in cdr_fields]
    cdr_updates = ",".join(f"{f}=excluded.{f}" for f in cdr_fields if f != "plan_id")
    con.execute(f"INSERT INTO cdr_plans({','.join(cdr_fields)}) VALUES({','.join('?' for _ in cdr_fields)}) ON CONFLICT(plan_id) DO UPDATE SET {cdr_updates}", cdr_values)

def _sync_energy_fuels(db_path: str, fuels: Sequence[str], postcode: str = "", distributor: str = "",
                       progress_path: str = "", mode: str = "AUTO") -> str:
    requested_fuels = tuple(dict.fromkeys(str(f).upper() for f in fuels))
    if not requested_fuels or any(f not in ("ELECTRICITY", "GAS") for f in requested_fuels):
        raise ValueError("fuels must contain ELECTRICITY and/or GAS")
    if not _CDR_SYNC_LOCK.acquire(blocking=False):
        return json.dumps({"ok": False, "status": "busy", "message": "A CDR refresh is already running."})

    deadline = time.monotonic() + CDR_REFRESH_DEADLINE_SECONDS
    reporter = _ProgressReporter(progress_path, 0, "cdr")
    try:
        sync_mode, updated_since = _energy_auto_mode(db_path, mode) if set(requested_fuels) == {"ELECTRICITY", "GAS"} else ("FULL", "")
        reporter.start("Discovering CDR retailers")
        retailers, discovery_source = _discover_retailers()
        reporter.state["endpoints_total"] = len(retailers)
        reporter.state["sync_mode"] = sync_mode.lower()
        reporter._write(force=True)
        if not retailers:
            reporter.finish("failed", "No CDR retailer endpoints discovered")
            return json.dumps({"ok": False, "status": "failed", "message": "No CDR retailer endpoints could be discovered."})

        # Load only compact cache metadata + Generic summaries. Plan Detail JSON is intentionally
        # excluded from this scan: unchanged routine runs no longer materialise the ~89 MB Detail
        # cache through sqlite3/Python. A Detail payload is fetched by primary key only when a
        # parser-version change/reactivation genuinely needs re-normalisation.
        cached_by_key: Dict[str, List[sqlite3.Row]] = {}
        expected_membership_by_key: Dict[str, set[str]] = {}
        retailer_watermarks: Dict[str, str] = {}
        verified_empty_by_key: Dict[str, bool] = {}
        scan_started_at = _now()
        with _connect(db_path) as con:
            _schema(con)
            fallback_watermark = (
                _state_get(con, "seed_source_full_attempt_at") or
                _state_get(con, "last_full_energy_reconciliation_at") or
                _state_get(con, "last_energy_successful_sync_at") or
                _state_get(con, "last_sync")
            )
            cache_columns = (
                "retailer_key,plan_id,source_plan_id,summary_revision,normalizer_version,"
                "is_active,stale_reason,fuel_type,summary_json,detail_cached"
            )
            for retailer in retailers:
                key = _retailer_key(retailer["base_uri"])
                placeholders = ",".join("?" for _ in requested_fuels)
                rows = con.execute(
                    f"SELECT {cache_columns} FROM energy_plans "
                    f"WHERE retailer_key=? AND UPPER(fuel_type) IN ({placeholders})",
                    (key, *requested_fuels),
                ).fetchall()
                cached_by_key[key] = rows
                expected: set[str] = set()
                for row in rows:
                    active = int(row["is_active"] if row["is_active"] is not None else 1) == 1
                    if not active:
                        continue
                    source = str(row["source_plan_id"] or row["plan_id"] or "")
                    fuel = str(row["fuel_type"] or "").upper()
                    if source and fuel in requested_fuels:
                        expected.add(f"{source}::{fuel}")
                expected_membership_by_key[key] = expected
                retailer_watermarks[key] = _state_get(con, _retailer_watermark_state_key(key)) or fallback_watermark
                verified_empty_by_key[key] = _state_get(con, _retailer_empty_state_key(key), "0") == "1"

        def list_retailer(retailer: Dict[str, str]) -> Dict[str, Any]:
            name = retailer.get("name") or "Energy retailer"
            key = _retailer_key(retailer["base_uri"])
            expected = expected_membership_by_key.get(key, set())
            try:
                endpoint_mode = sync_mode
                confirmed_removed: set[str] = set()
                strategy = sync_mode.lower()
                if sync_mode == "ROUTINE":
                    routine = _routine_retailer_snapshot(
                        retailer, cached_by_key.get(key, []), retailer_watermarks.get(key, ""),
                        reporter, deadline, verified_empty=verified_empty_by_key.get(key, False),
                    )
                    snapshot = routine["snapshot"]
                    summaries = [
                        p for p in routine.get("summaries") or []
                        if isinstance(p, dict) and str(p.get("planId") or "").strip()
                        and any(_fuel_matches(p, f) for f in requested_fuels)
                    ]
                    confirmed_removed = set(routine.get("confirmed_removed_source_ids") or set())
                    strategy = str(routine.get("routine_strategy") or "routine")
                else:
                    expected_for_confirmation = None if sync_mode == "FULL" else (expected if cached_by_key.get(key) else None)
                    snapshot = _plan_list_snapshot(
                        retailer, reporter, deadline,
                        updated_since=updated_since if sync_mode == "INCREMENTAL" else "",
                        expected_membership=expected_for_confirmation,
                        fuels=requested_fuels,
                    )
                    summaries = [
                        p for p in snapshot.get("plans") or []
                        if isinstance(p, dict) and str(p.get("planId") or "").strip()
                        and any(_fuel_matches(p, f) for f in requested_fuels)
                    ]
                reporter.listed(name, len(summaries), int(snapshot.get("pages") or 0))
                return {
                    "ok": True, "retailer": retailer, "snapshot": snapshot,
                    "summaries": summaries, "endpoint_mode": endpoint_mode,
                    "confirmed_removed_source_ids": confirmed_removed,
                    "routine_strategy": strategy,
                }
            except Exception as exc:
                reporter.endpoint_done(name, "Listing failed · cached data preserved")
                return {"ok": False, "retailer": retailer, "error": str(exc)[:500]}

        def process_summary(item: Tuple[Dict[str, str], Dict[str, Any], List[str], Dict[str, sqlite3.Row]]) -> Dict[str, Any]:
            retailer, summary, needed_fuels, cached_rows = item
            name = retailer.get("name") or "Energy retailer"
            plan_id = str(summary.get("planId") or "").strip()
            plan_name = _compact(summary.get("displayName") or "Plan")
            reusable_detail: Optional[Dict[str, Any]] = None
            cache_reusable: Dict[str, bool] = {}
            network_fetched = False
            try:
                # Re-normalisation is rare. First make a metadata-only revision check, then lazy
                # load at most one matching Detail JSON payload by primary key if it is actually
                # needed. Unchanged current-normalizer rows never touch Detail JSON at all.
                for fuel, row in cached_rows.items():
                    can_reuse = _cached_detail_metadata_can_reuse(row, summary)
                    cache_reusable[fuel] = can_reuse
                    if reusable_detail is None and can_reuse:
                        candidate = _load_cached_detail(db_path, row, summary)
                        if candidate is not None:
                            reusable_detail = candidate
                        else:
                            cache_reusable[fuel] = False
                if reusable_detail is None:
                    reporter.detail_started(name, plan_name, plan_id)
                    reusable_detail = _detail_plan(retailer, plan_id, deadline)
                    network_fetched = True
                if not _detail_fresh_for_summary(summary, reusable_detail):
                    raise ValueError("Plan Detail is older than its CURRENT Generic Plan summary")
                records: List[Dict[str, Any]] = []
                matched = 0
                for fuel in needed_fuels:
                    # Preserve the existing fail-open fuel semantics: a DUAL/missing-fuel summary
                    # can still produce the requested contract even if Detail metadata is sparse.
                    if not _fuel_matches(reusable_detail, fuel) and not _fuel_matches(summary, fuel):
                        continue
                    record = _normalise_plan(retailer, summary, reusable_detail, fuel)
                    records.append(record)
                    if _geography_matches(reusable_detail if reusable_detail.get("geography") else summary, postcode, distributor):
                        matched += 1
                return {"records": records, "error": None, "stale_ids": [], "matched": matched,
                        "network_fetched": network_fetched}
            except Exception as exc:
                stale_ids: List[str] = []
                for fuel in needed_fuels:
                    row = cached_rows.get(fuel)
                    if row is not None and not cache_reusable.get(fuel, False):
                        stale_ids.append(str(row["plan_id"]))
                return {"records": [], "error": f"{plan_id}: {str(exc)[:350]}", "stale_ids": stale_ids,
                        "matched": 0, "network_fetched": network_fetched}
            finally:
                reporter.detail_done(name, plan_name, plan_id)

        # Pipeline list/probe work directly into the persistent Detail pool. Large retailers no
        # longer have to wait for every other retailer to finish listing before their changed
        # plans begin downloading. The shared HTTP semaphore above keeps aggregate live request
        # pressure <= 15, while all existing pagination/membership/detail validations remain intact.
        listed_results: Dict[str, Dict[str, Any]] = {}
        endpoint_work: Dict[str, Dict[str, Any]] = {}
        detail_futures: Dict[concurrent.futures.Future, Tuple[Dict[str, str], Dict[str, Any], List[str], Dict[str, sqlite3.Row]]] = {}
        zero_work_hits = 0
        fetched_summaries = 0

        with concurrent.futures.ThreadPoolExecutor(max_workers=CDR_DETAIL_GLOBAL_WORKERS) as detail_executor, \
             concurrent.futures.ThreadPoolExecutor(max_workers=CDR_OUTER_WORKERS) as list_executor:
            list_future_map = {list_executor.submit(list_retailer, retailer): retailer for retailer in retailers}
            for future in concurrent.futures.as_completed(list_future_map):
                _check_deadline(deadline)
                retailer = list_future_map[future]
                key = _retailer_key(retailer["base_uri"])
                try:
                    listed = future.result()
                except Exception as exc:
                    listed = {"ok": False, "retailer": retailer, "error": str(exc)[:500]}
                listed_results[key] = listed
                if not listed.get("ok"):
                    continue

                summaries = list(listed.get("summaries") or [])
                fetched_summaries += len(summaries)
                cache_by_pair: Dict[Tuple[str, str], sqlite3.Row] = {}
                for row in cached_by_key.get(key, []):
                    source = str(row["source_plan_id"] or row["plan_id"] or "")
                    fuel = str(row["fuel_type"] or "").upper()
                    if source and fuel:
                        cache_by_pair[(source, fuel)] = row
                endpoint_work[key] = {
                    "records": [], "stale_ids": [], "errors": [], "matched": 0,
                    "network_details": 0, "cache_fast_hits": 0,
                }
                for summary in summaries:
                    source_id = str(summary.get("planId") or "").strip()
                    applicable = _summary_fuels(summary, requested_fuels)
                    cached_for_fuel = {f: cache_by_pair.get((source_id, f)) for f in applicable}
                    zero_fuels = [f for f in applicable if _cached_row_zero_work(cached_for_fuel.get(f), summary)]
                    needed = [f for f in applicable if f not in zero_fuels]
                    if not needed:
                        zero_work_hits += 1
                        endpoint_work[key]["cache_fast_hits"] += 1
                        reporter.detail_done(
                            retailer.get("name") or "Energy retailer",
                            _compact(summary.get("displayName") or "Plan"), source_id,
                        )
                        continue
                    item = (retailer, summary, needed, {f: r for f, r in cached_for_fuel.items() if r is not None})
                    detail_futures[detail_executor.submit(process_summary, item)] = item

            # Detail tasks have been running throughout listing. Drain the already-active global
            # queue once every retailer has been enumerated; only the coordinator mutates buckets.
            for future in concurrent.futures.as_completed(list(detail_futures)):
                _check_deadline(deadline)
                item = detail_futures[future]
                retailer = item[0]
                key = _retailer_key(retailer["base_uri"])
                bucket = endpoint_work[key]
                try:
                    result = future.result()
                except Exception as exc:
                    result = {"records": [], "error": f"detail worker failed: {str(exc)[:350]}", "stale_ids": [],
                              "matched": 0, "network_fetched": False}
                bucket["records"].extend(result.get("records") or [])
                bucket["stale_ids"].extend(result.get("stale_ids") or [])
                if result.get("error"):
                    bucket["errors"].append(result["error"])
                bucket["matched"] += int(result.get("matched") or 0)
                if result.get("network_fetched"):
                    bucket["network_details"] += 1

        successes = failures = detail_failures = matched = records_written = records_deactivated = network_details = 0
        coverage_endpoint_failures = coverage_incomplete_catalogues = discovery_warnings = 0
        coverage_failure_names: List[str] = []
        coverage_failure_details: List[Dict[str, str]] = []
        catalogue_complete_all = True
        per_endpoint: List[Dict[str, Any]] = []
        validated_retailer_keys: List[str] = []
        with _connect(db_path) as con:
            _schema(con)
            _log(con, "INFO", f"Starting combined {','.join(requested_fuels)} CDR {sync_mode.lower()} sync across {len(retailers)} unique endpoints ({discovery_source})")
            for retailer in retailers:
                key = _retailer_key(retailer["base_uri"])
                listed = listed_results.get(key) or {"ok": False, "retailer": retailer, "error": "listing result missing"}
                if not listed.get("ok"):
                    failures += 1
                    error = str(listed.get("error") or "Unknown endpoint failure")
                    coverage_required = _energy_source_is_coverage_required(retailer)
                    if coverage_required:
                        coverage_endpoint_failures += 1
                        catalogue_complete_all = False
                        coverage_failure_names.append(str(retailer.get("name") or "Energy retailer"))
                        coverage_failure_details.append({
                            "name": str(retailer.get("name") or "Energy retailer"),
                            "kind": "endpoint", "error": error[:300],
                        })
                        level = "ERROR"
                    else:
                        # Register-only publicBaseUri values are discovery probes, not confirmed
                        # AER Energy PRD routes. Their failure must not create a false
                        # "some sources unavailable" market-coverage alert.
                        discovery_warnings += 1
                        level = "WARN"
                    per_endpoint.append({
                        "name": retailer.get("name"),
                        "status": "failed" if coverage_required else "discovery_warning",
                        "coverage_required": coverage_required, "error": error[:300],
                    })
                    _log(con, level, f"{retailer.get('name')}: CDR endpoint failed; cached rows preserved: {error}")
                    continue

                work = endpoint_work.get(key, {"records": [], "stale_ids": [], "errors": [], "matched": 0, "network_details": 0, "cache_fast_hits": 0})
                records = list(work.get("records") or [])
                errors = list(work.get("errors") or [])
                detail_failures += len(errors)
                matched += int(work.get("matched") or 0)
                network_details += int(work.get("network_details") or 0)
                snapshot = listed.get("snapshot") or {}
                endpoint_mode = str(listed.get("endpoint_mode") or sync_mode)
                endpoint_full = endpoint_mode.startswith("FULL")
                membership_authoritative = endpoint_full
                confirmed_removed_source_ids = set(listed.get("confirmed_removed_source_ids") or set())
                catalogue_complete = bool(snapshot.get("complete"))
                coverage_required = _energy_source_is_coverage_required(retailer)
                if not catalogue_complete:
                    if coverage_required:
                        # An incomplete full snapshot threatens lifecycle reconciliation; an
                        # incomplete incremental response can miss updates. Both are genuine
                        # freshness/coverage issues even though cached rows remain preserved.
                        catalogue_complete_all = False
                        coverage_incomplete_catalogues += 1
                        coverage_failure_names.append(str(retailer.get("name") or "Energy retailer"))
                        snapshot_errors = "; ".join(str(x) for x in (snapshot.get("errors") or [])[:3])
                        if snapshot.get("rescue_error"):
                            snapshot_errors = (snapshot_errors + "; " if snapshot_errors else "") + "recovery: " + str(snapshot.get("rescue_error"))
                        coverage_failure_details.append({
                            "name": str(retailer.get("name") or "Energy retailer"),
                            "kind": "catalogue",
                            "error": (snapshot_errors or "catalogue completeness validation failed")[:300],
                        })
                    else:
                        discovery_warnings += 1
                for error in errors[:20]:
                    _log(con, "WARN", f"{retailer.get('name')}: detail failed: {error}")

                with con:
                    # Only rows which were new, changed, reactivated or produced under an older
                    # normalizer version reach this list. True cache hits perform no SQLite write.
                    for record in records:
                        _upsert_plan(con, record)
                        records_written += 1
                    for storage_id in set(work.get("stale_ids") or []):
                        cur = con.execute(
                            "UPDATE energy_plans SET is_active=0, stale_reason='SUMMARY_CHANGED_DETAIL_FAILED' "
                            "WHERE retailer_key=? AND plan_id=? AND COALESCE(is_active,1)<>0",
                            (key, storage_id),
                        )
                        if cur.rowcount and cur.rowcount > 0:
                            records_deactivated += int(cur.rowcount)
                        con.execute(
                            "UPDATE cdr_plans SET is_active=0, stale_reason='SUMMARY_CHANGED_DETAIL_FAILED' "
                            "WHERE plan_id=? AND COALESCE(is_active,1)<>0",
                            (storage_id,),
                        )

                    # Routine Sync v2 receives only explicitly double-confirmed removals from
                    # targeted retailer/fuel/type membership checks. It never treats the delta
                    # response itself as an authoritative whole-retailer membership snapshot.
                    if endpoint_mode == "ROUTINE" and catalogue_complete and confirmed_removed_source_ids:
                        for old in cached_by_key.get(key, []):
                            source = str(old["source_plan_id"] or old["plan_id"] or "") if "source_plan_id" in old.keys() else str(old["plan_id"] or "")
                            active = int(old["is_active"] if "is_active" in old.keys() and old["is_active"] is not None else 1) == 1
                            if active and source in confirmed_removed_source_ids:
                                cur = con.execute(
                                    "UPDATE energy_plans SET is_active=0, stale_reason='NO_LONGER_CURRENT' "
                                    "WHERE retailer_key=? AND plan_id=? AND COALESCE(is_active,1)<>0",
                                    (key, old["plan_id"]),
                                )
                                if cur.rowcount and cur.rowcount > 0:
                                    records_deactivated += int(cur.rowcount)
                                con.execute(
                                    "UPDATE cdr_plans SET is_active=0, stale_reason='NO_LONGER_CURRENT' "
                                    "WHERE plan_id=? AND COALESCE(is_active,1)<>0",
                                    (old["plan_id"],),
                                )

                    # Explicit FULL snapshots remain authoritative for all lifecycle changes.
                    if membership_authoritative and catalogue_complete:
                        current_by_fuel = {
                            fuel: {str(p.get("planId") or "").strip() for p in snapshot.get("plans") or []
                                   if isinstance(p, dict) and str(p.get("planId") or "").strip() and _fuel_matches(p, fuel)}
                            for fuel in requested_fuels
                        }
                        for old in cached_by_key.get(key, []):
                            fuel = str(old["fuel_type"] or "").upper()
                            if fuel not in requested_fuels:
                                continue
                            source = str(old["source_plan_id"] or old["plan_id"] or "") if "source_plan_id" in old.keys() else str(old["plan_id"] or "")
                            active = int(old["is_active"] if "is_active" in old.keys() and old["is_active"] is not None else 1) == 1
                            if active and source and source not in current_by_fuel.get(fuel, set()):
                                cur = con.execute(
                                    "UPDATE energy_plans SET is_active=0, stale_reason='NO_LONGER_CURRENT' "
                                    "WHERE retailer_key=? AND plan_id=? AND COALESCE(is_active,1)<>0",
                                    (key, old["plan_id"]),
                                )
                                if cur.rowcount and cur.rowcount > 0:
                                    records_deactivated += int(cur.rowcount)
                                con.execute(
                                    "UPDATE cdr_plans SET is_active=0, stale_reason='NO_LONGER_CURRENT' "
                                    "WHERE plan_id=? AND COALESCE(is_active,1)<>0",
                                    (old["plan_id"],),
                                )
                    elif membership_authoritative:
                        reason = "; ".join(str(x) for x in (snapshot.get("errors") or [])[:3])
                        suffix = f": {reason}" if reason else ""
                        _log(con, "WARN", f"{retailer.get('name')}: CURRENT catalogue validation incomplete; absent-plan lifecycle changes skipped{suffix}")

                # Preserve authoritative empty-catalogue state across routine scans and future
                # seed exports. This state changes only after a complete combined-fuel catalogue
                # validation; failed/incomplete endpoints keep their previous marker untouched.
                if catalogue_complete and set(requested_fuels) == {"ELECTRICITY", "GAS"}:
                    declared = snapshot.get("declared_records")
                    try:
                        declared_count = int(declared) if declared is not None else len(set(snapshot.get("plan_ids") or []))
                    except (TypeError, ValueError):
                        declared_count = -1
                    if declared_count == 0:
                        _state_set(con, _retailer_empty_state_key(key), "1", scan_started_at)
                    elif declared_count > 0:
                        con.execute("DELETE FROM sync_state WHERE key=?", (_retailer_empty_state_key(key),))

                # Advance a retailer watermark only when its Generic catalogue/delta and all
                # required Detail work completed cleanly. A failed Detail therefore remains in
                # the next overlapping delta window instead of being skipped forever. Verified
                # empty retailers also receive a watermark, so the state is fully portable.
                if endpoint_mode == "ROUTINE" and catalogue_complete and not errors:
                    _state_set(con, _retailer_watermark_state_key(key), scan_started_at, scan_started_at)

                successes += 1
                if catalogue_complete:
                    validated_retailer_keys.append(key)
                if not catalogue_complete and coverage_required:
                    status_ep = "partial"
                elif errors or not catalogue_complete:
                    status_ep = "warning"
                else:
                    status_ep = "ok"
                per_endpoint.append({"name": retailer.get("name"), "status": status_ep,
                                     "coverage_required": coverage_required, "plans_written": len(records),
                                     "detail_failures": len(errors), "mode": endpoint_mode,
                                     "confirmation": snapshot.get("confirmation", ""),
                                     "rescue_attempted": bool(snapshot.get("rescue_attempted")),
                                     "page_size": int(snapshot.get("page_size") or CDR_PLAN_LIST_PAGE_SIZE)})
                reporter.endpoint_done(retailer.get("name") or "Energy retailer", "Complete" if not errors else f"{len(errors)} detail warning(s)")

            timestamp = _now()
            if records_written > 0 or records_deactivated > 0:
                _state_bump(con, "energy_data_revision", timestamp)
            coverage_issues = coverage_endpoint_failures + coverage_incomplete_catalogues
            if successes == 0:
                status = "failed"
            elif coverage_issues > 0:
                status = "partial"
            elif detail_failures > 0 or discovery_warnings > 0:
                status = "success_with_warnings"
            else:
                status = "success"

            for fuel in requested_fuels:
                fuel_key = fuel.lower()
                _state_set(con, f"last_sync_{fuel_key}", timestamp, timestamp)
                _state_set(con, f"last_sync_status_{fuel_key}", status, timestamp)
                if successes > 0:
                    _state_set(con, f"last_data_update_{fuel_key}", timestamp, timestamp)
            _state_set(con, "last_sync", timestamp, timestamp)
            _state_set(con, "last_sync_status", status, timestamp)
            _state_set(con, "last_energy_sync_mode", sync_mode.lower(), timestamp)
            _state_set(con, "last_sync_report", json.dumps({
                "fuels": list(requested_fuels), "mode": sync_mode.lower(), "updated_since": updated_since,
                "endpoints": len(retailers), "successes": successes, "failures": failures,
                "coverage_endpoint_failures": coverage_endpoint_failures,
                "coverage_incomplete_catalogues": coverage_incomplete_catalogues,
                "coverage_issues": coverage_issues, "coverage_failure_names": sorted(set(coverage_failure_names)),
                "coverage_failure_details": coverage_failure_details[:20],
                "discovery_warnings": discovery_warnings, "detail_failures": detail_failures,
                "summaries_received": fetched_summaries, "zero_work_cache_hits": zero_work_hits,
                "network_detail_fetches": network_details, "records_written": records_written,
                "records_deactivated": records_deactivated,
                "matched_location_checked": matched,
                "validated_retailer_keys": sorted(set(validated_retailer_keys)),
            }), timestamp)

            # Record the last completely clean combined run. Routine sync does not depend on
            # this watermark for membership: it always checks each retailer's CURRENT Generic
            # catalogue, but the timestamp remains useful for explicit incremental diagnostics.
            if set(requested_fuels) == {"ELECTRICITY", "GAS"} and coverage_issues == 0 and detail_failures == 0:
                _state_set(con, "last_energy_successful_sync_at", timestamp, timestamp)
            if (set(requested_fuels) == {"ELECTRICITY", "GAS"} and sync_mode == "FULL" and
                    coverage_issues == 0 and catalogue_complete_all):
                _state_set(con, "last_full_energy_reconciliation_at", timestamp, timestamp)
            con.commit()
            _log(con, "INFO", f"Combined energy sync {status}/{sync_mode.lower()}: {successes}/{len(retailers)} endpoints, "
                               f"{coverage_issues} verified AER coverage issue(s), {discovery_warnings} discovery warning(s), "
                               f"{fetched_summaries} summaries, {zero_work_hits} zero-work hits, "
                               f"{network_details} Detail HTTP fetches, {records_written} rows written, {detail_failures} detail failures")

        message = (f"Energy CDR {sync_mode.lower()} refresh {status}: {successes}/{len(retailers)} endpoints; "
                   f"{coverage_issues} verified AER coverage issue(s); {discovery_warnings} discovery warning(s); "
                   f"{fetched_summaries} summaries; {zero_work_hits} unchanged cache hits; "
                   f"{network_details} Plan Detail download(s); {detail_failures} detail failure(s).")
        reporter.finish(status, message)
        return json.dumps({
            "ok": successes > 0, "status": status, "mode": sync_mode.lower(), "updated_since": updated_since,
            "message": message, "endpoints": len(retailers), "successful_endpoints": successes,
            "failed_endpoints": failures, "coverage_issues": coverage_issues,
            "coverage_endpoint_failures": coverage_endpoint_failures,
            "coverage_incomplete_catalogues": coverage_incomplete_catalogues,
            "coverage_failure_names": sorted(set(coverage_failure_names)),
            "coverage_failure_details": coverage_failure_details[:20],
            "discovery_warnings": discovery_warnings, "detail_failures": detail_failures,
            "fetched_summaries": fetched_summaries, "zero_work_cache_hits": zero_work_hits,
            "network_detail_fetches": network_details, "records_written": records_written,
            "matched_location": matched, "discovery_source": discovery_source,
        })
    except TimeoutError as exc:
        reporter.finish("failed", "CDR refresh deadline reached; last-good cache preserved")
        return json.dumps({"ok": False, "status": "failed", "message": str(exc)})
    finally:
        _close_http_connection()
        _CDR_SYNC_LOCK.release()



def _energy_seed_source_status(db_path: str) -> Dict[str, Any]:
    """Validate that the live DB can be exported as a safe Energy seed.

    A FULL combined scan is required, but verified AER catalogue coverage issues are export
    warnings rather than hard failures. Any retailer whose catalogue did not validate is simply
    excluded from the seed and recorded in metadata. Structural/database problems, missing fuels,
    Plan Detail failures, or non-current normalizer rows remain hard failures.

    Warning seeds deliberately clear their old incremental/full-success watermarks when created.
    Routine sync no longer interprets that as a request for a national FULL verification: it checks
    CURRENT membership for every source and rebuilds any omitted retailer directly.
    """
    with _connect(db_path) as con:
        _schema(con)
        integrity = str(con.execute("PRAGMA integrity_check").fetchone()[0] or "").lower()
        if integrity != "ok":
            return {"ok": False, "message": f"Live database integrity check failed: {integrity}"}

        def state(key: str, default: str = "") -> str:
            return _state_get(con, key, default)

        try:
            report = json.loads(state("last_sync_report", "{}") or "{}")
            if not isinstance(report, dict):
                report = {}
        except Exception:
            report = {}

        reasons: List[str] = []
        warnings: List[str] = []
        if str(report.get("mode") or "").lower() != "full":
            reasons.append("the latest Energy scan was not a FULL reconciliation attempt")
        fuels = {str(x).upper() for x in (report.get("fuels") or [])}
        if not {"ELECTRICITY", "GAS"}.issubset(fuels):
            reasons.append("the latest Energy scan did not cover both electricity and gas")

        coverage_issues = int(report.get("coverage_issues") or 0)
        detail_failures = int(report.get("detail_failures") or 0)
        coverage_failure_names = sorted({str(x).strip() for x in (report.get("coverage_failure_names") or []) if str(x).strip()})
        coverage_failure_details = [x for x in (report.get("coverage_failure_details") or []) if isinstance(x, dict)]
        if coverage_issues:
            names = ", ".join(coverage_failure_names[:6])
            warnings.append(f"{coverage_issues} verified AER source issue(s){f' ({names})' if names else ''}")
        if detail_failures:
            reasons.append(f"{detail_failures} Plan Detail failure(s) remain")

        last_sync = state("last_sync")
        last_full = state("last_full_energy_reconciliation_at")
        last_status = state("last_sync_status", "unknown")
        if not last_sync:
            reasons.append("the latest FULL scan has no sync timestamp")
        if coverage_issues == 0:
            if not last_full:
                reasons.append("no successful full reconciliation timestamp is present")
            elif last_sync != last_full:
                reasons.append("the latest sync timestamp does not match the verified FULL reconciliation")
            if last_status not in ("success", "success_with_warnings"):
                reasons.append(f"latest Energy status is {last_status}")
        else:
            # A partial status is expected when one or more verified AER catalogues could not be
            # validated. The seed may still be exported from every catalogue which *was* validated.
            if last_status not in ("partial", "success_with_warnings", "success"):
                reasons.append(f"latest Energy status is {last_status}")

        validated_keys = sorted({str(x) for x in (report.get("validated_retailer_keys") or []) if str(x).strip()})
        if not validated_keys:
            reasons.append("the full scan did not record any validated retailer catalogues")

        placeholders = ",".join("?" for _ in validated_keys) or "''"
        where = f"COALESCE(is_active,1)=1 AND retailer_key IN ({placeholders})"
        params: Tuple[Any, ...] = tuple(validated_keys)
        active_count = int(con.execute(f"SELECT COUNT(*) FROM energy_plans WHERE {where}", params).fetchone()[0]) if validated_keys else 0
        electricity = int(con.execute(f"SELECT COUNT(*) FROM energy_plans WHERE {where} AND UPPER(fuel_type)='ELECTRICITY'", params).fetchone()[0]) if validated_keys else 0
        gas = int(con.execute(f"SELECT COUNT(*) FROM energy_plans WHERE {where} AND UPPER(fuel_type)='GAS'", params).fetchone()[0]) if validated_keys else 0
        invalid_rows = int(con.execute(
            f"SELECT COUNT(*) FROM energy_plans WHERE {where} AND ("
            "COALESCE(summary_json,'')='' OR COALESCE(detail_json,'')='' OR COALESCE(normalizer_version,0)<>?)",
            (*params, NORMALIZER_VERSION),
        ).fetchone()[0]) if validated_keys else 0
        if active_count <= 0 or electricity <= 0 or gas <= 0:
            reasons.append("the validated portion of the baseline does not contain both electricity and gas plans")
        if invalid_rows:
            reasons.append(f"{invalid_rows} active plan row(s) are not fully normalised/cached")

        message = "; ".join(reasons) if reasons else (
            "Energy baseline is exportable with warning: " + "; ".join(warnings)
            if warnings else "Verified Energy baseline is ready"
        )
        return {
            "ok": not reasons,
            "status": "warning" if (not reasons and warnings) else ("verified" if not reasons else "failed"),
            "message": message,
            "warnings": warnings,
            "plan_count": active_count,
            "electricity_plans": electricity,
            "gas_plans": gas,
            "coverage_issues": coverage_issues,
            "coverage_failure_names": coverage_failure_names,
            "coverage_failure_details": coverage_failure_details[:20],
            "detail_failures": detail_failures,
            "discovery_warnings": int(report.get("discovery_warnings") or 0),
            "validated_retailer_keys": validated_keys,
            "last_sync_at": last_sync,
            "last_full_energy_reconciliation_at": last_full,
            "requires_live_recovery": coverage_issues > 0,
            "energy_data_revision": int(state("energy_data_revision", "0") or 0),
        }

def _energy_seed_progress(path: str, stage: str, detail: str = "") -> None:
    """Best-effort seed-build progress. Export correctness never depends on this file."""
    if not path:
        return
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as handle:
            json.dump({
                "kind": "seed", "percent": 100, "stage": str(stage or "Building Energy seed"),
                "query": str(stage or "Building Energy seed"), "current": str(detail or ""),
                "updated_at": _now(),
            }, handle, separators=(",", ":"))
        os.replace(tmp, path)
    except Exception:
        pass


def export_energy_seed(db_path: str, output_gzip_path: str, progress_path: str = "") -> str:
    """Serialize a verified Energy seed without racing a CDR refresh.

    The seed is deliberately built as a fresh SQLite file in DELETE-journal mode. This avoids
    copying the live WAL database, avoids VACUUM's temporary second full-size database, and keeps
    the compatibility cdr_plans mirror lightweight instead of duplicating the large Generic/Detail
    JSON already stored in energy_plans.
    """
    if not _CDR_SYNC_LOCK.acquire(blocking=False):
        return json.dumps({"ok": False, "status": "busy", "message": "Energy CDR refresh is running; retry seed export when it finishes."})
    try:
        return _export_energy_seed_unlocked(db_path, output_gzip_path, progress_path)
    finally:
        _CDR_SYNC_LOCK.release()


def _export_energy_seed_unlocked(db_path: str, output_gzip_path: str, progress_path: str = "") -> str:
    """Export a sanitized, gzip-compressed, verified Energy baseline SQLite database."""
    stage = "checking the verified Energy baseline"
    _energy_seed_progress(progress_path, "Checking verified baseline", "Confirming FULL CDR coverage and cached Plan Detail")
    verification = _energy_seed_source_status(db_path)
    if not verification.get("ok"):
        return json.dumps({"ok": False, "status": "not_verified", **verification})

    output_gzip_path = os.path.abspath(str(output_gzip_path))
    parent = os.path.dirname(output_gzip_path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    raw_path = output_gzip_path + ".tmp.db"
    for candidate in (raw_path, raw_path + "-journal", raw_path + "-wal", raw_path + "-shm", output_gzip_path):
        try:
            os.remove(candidate)
        except FileNotFoundError:
            pass

    validated_keys = list(verification["validated_retailer_keys"])
    generated_at = _now()
    try:
        stage = "creating the sanitized temporary database"
        _energy_seed_progress(progress_path, "Creating sanitized database", "Copying only verified active Energy data")

        # A fresh seed has no deleted/free pages, so VACUUM would provide almost no size benefit
        # while temporarily requiring roughly another full database worth of storage on Android.
        seed = sqlite3.connect(raw_path, timeout=30)
        try:
            seed.row_factory = sqlite3.Row
            seed.execute("PRAGMA journal_mode=DELETE")
            seed.execute("PRAGMA synchronous=NORMAL")
            seed.execute("PRAGMA busy_timeout=30000")
            _schema(seed)
            seed.execute("PRAGMA journal_mode=DELETE")

            with _connect(db_path) as src:
                _schema(src)
                energy_cols = [r[1] for r in src.execute("PRAGMA table_info(energy_plans)").fetchall()]
                energy_col_sql = ",".join(f'"{c}"' for c in energy_cols)
                placeholders = ",".join("?" for _ in validated_keys)
                select = src.execute(
                    f"SELECT {energy_col_sql} FROM energy_plans WHERE COALESCE(is_active,1)=1 "
                    f"AND retailer_key IN ({placeholders})",
                    tuple(validated_keys),
                )
                insert_sql = (
                    f"INSERT INTO energy_plans({energy_col_sql}) VALUES("
                    + ",".join("?" for _ in energy_cols) + ")"
                )
                copied = 0
                while True:
                    rows = select.fetchmany(100)
                    if not rows:
                        break
                    seed.executemany(insert_sql, [tuple(row[c] for c in energy_cols) for row in rows])
                    copied += len(rows)
                    if copied % 1000 < len(rows):
                        seed.commit()
                        _energy_seed_progress(progress_path, "Copying verified plans", f"{copied:,} of {verification['plan_count']:,} plans")
                seed.commit()

                # Keep cdr_plans structurally useful without duplicating the very large raw
                # Generic/Detail JSON. All comparison and FastSync cache reads use energy_plans.
                seed.execute(
                    """
                    INSERT OR REPLACE INTO cdr_plans(
                        plan_id,provider,name,customer_type,distributors,tariff_type,is_tou,is_flat,
                        has_demand,has_controlled_load,has_solar,daily_supply_cents,avg_usage_cents,
                        last_updated,raw_usage_rates,website,source,fuel_type,retailer_key,
                        detail_json,summary_json,tariff_periods_json,controlled_load_json,eligibility_json,
                        metering_charges_json,solar_feed_in_json,source_plan_id,summary_revision,
                        normalizer_version,is_active,stale_reason
                    )
                    SELECT
                        plan_id,retailer_name,plan_name,customer_type,distributors,tariff_type,is_tou,is_flat,
                        has_demand,has_controlled_load,has_solar,daily_supply_cents,avg_usage_cents,
                        last_updated,raw_usage_rates,application_uri,source,fuel_type,retailer_key,
                        NULL,NULL,tariff_periods_json,controlled_load_json,eligibility_json,
                        metering_charges_json,solar_feed_in_json,source_plan_id,summary_revision,
                        normalizer_version,is_active,stale_reason
                    FROM energy_plans
                    """
                )

                allowed = set(ENERGY_SEED_STATE_KEYS)
                static_rows = src.execute(
                    f"SELECT key,value,updated_at FROM sync_state WHERE key IN ({','.join('?' for _ in allowed)})",
                    tuple(sorted(allowed)),
                ).fetchall()
                dynamic_rows = src.execute(
                    "SELECT key,value,updated_at FROM sync_state "
                    "WHERE key LIKE 'energy_retailer_watermark::%' OR key LIKE 'energy_retailer_verified_empty::%'"
                ).fetchall()
                validated_set = set(validated_keys)
                portable_dynamic = []
                for r in dynamic_rows:
                    key_text = str(r["key"] or "")
                    suffix = key_text.split("::", 1)[1] if "::" in key_text else ""
                    if suffix in validated_set:
                        portable_dynamic.append((r["key"], r["value"], r["updated_at"]))
                seed.executemany(
                    "INSERT OR REPLACE INTO sync_state(key,value,updated_at) VALUES(?,?,?)",
                    [(r["key"], r["value"], r["updated_at"]) for r in static_rows] + portable_dynamic,
                )

            if verification.get("requires_live_recovery"):
                # The missing retailer(s) are intentionally absent from the seed. Clear legacy
                # success/full watermarks so the warning remains explicit. AUTO routine sync still
                # checks CURRENT membership for every retailer and will populate omitted sources
                # directly; it never schedules a national FULL verification automatically.
                seed.execute("DELETE FROM sync_state WHERE key IN ('last_energy_successful_sync_at','last_full_energy_reconciliation_at')")

            seed_meta = {
                "seed_verified": "1",
                "seed_format_version": str(ENERGY_SEED_FORMAT_VERSION),
                "seed_app_version": APP_VERSION,
                "seed_normalizer_version": str(NORMALIZER_VERSION),
                "seed_generated_at": generated_at,
                "seed_energy_plan_count": str(verification["plan_count"]),
                "seed_electricity_plan_count": str(verification["electricity_plans"]),
                "seed_gas_plan_count": str(verification["gas_plans"]),
                "seed_source_last_full_reconciliation_at": str(verification.get("last_full_energy_reconciliation_at") or ""),
                "seed_source_full_attempt_at": str(verification.get("last_sync_at") or ""),
                "seed_coverage_issues": str(int(verification.get("coverage_issues") or 0)),
                "seed_coverage_failure_names": json.dumps(verification.get("coverage_failure_names") or [], separators=(",", ":")),
                "seed_requires_full_sync": "1" if verification.get("requires_live_recovery") else "0",
            }
            seed.executemany(
                "INSERT OR REPLACE INTO sync_state(key,value,updated_at) VALUES(?,?,?)",
                [(k, v, generated_at) for k, v in seed_meta.items()],
            )
            seed.commit()

            stage = "validating the sanitized database"
            _energy_seed_progress(progress_path, "Validating seed", "Running SQLite integrity and content checks")
            integrity = str(seed.execute("PRAGMA integrity_check").fetchone()[0] or "").lower()
            if integrity != "ok":
                raise RuntimeError(f"seed integrity check failed: {integrity}")
            actual = int(seed.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1").fetchone()[0])
            e = int(seed.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='ELECTRICITY'").fetchone()[0])
            g = int(seed.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='GAS'").fetchone()[0])
            if (actual, e, g) != (verification["plan_count"], verification["electricity_plans"], verification["gas_plans"]):
                raise RuntimeError("seed row-count verification failed")
            # cdr_plans historically keys only on plan_id (not retailer_key), so two retailers
            # may legitimately collapse to one compatibility row. energy_plans is authoritative.
            if int(seed.execute("SELECT COUNT(*) FROM cdr_plans WHERE detail_json IS NOT NULL OR summary_json IS NOT NULL").fetchone()[0]) != 0:
                raise RuntimeError("compact cdr_plans mirror unexpectedly duplicates raw Plan Detail JSON")
            for table in ("debug_logs", "nbn_offers", "savings_products"):
                if int(seed.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0]) != 0:
                    raise RuntimeError(f"seed sanitisation failed: {table} is not empty")
        finally:
            seed.close()

        stage = "compressing the verified database"
        raw_bytes = os.path.getsize(raw_path)
        _energy_seed_progress(progress_path, "Compressing seed", f"Sanitized database size {raw_bytes / (1024.0 * 1024.0):.1f} MB")
        sha = hashlib.sha256()
        with open(raw_path, "rb") as source, gzip.open(output_gzip_path, "wb", compresslevel=6) as target:
            while True:
                chunk = source.read(1024 * 1024)
                if not chunk:
                    break
                target.write(chunk)
        with open(output_gzip_path, "rb") as exported:
            for chunk in iter(lambda: exported.read(1024 * 1024), b""):
                sha.update(chunk)
        compressed_bytes = os.path.getsize(output_gzip_path)
        _energy_seed_progress(progress_path, "Seed ready", f"{verification['plan_count']:,} plans · {compressed_bytes / (1024.0 * 1024.0):.1f} MB compressed")
        warning_count = int(verification.get("coverage_issues") or 0)
        warning_names = list(verification.get("coverage_failure_names") or [])
        warning_suffix = ""
        if warning_count:
            label = ", ".join(warning_names[:6])
            warning_suffix = f" Warning: {warning_count} AER source(s) were unavailable{f' ({label})' if label else ''}; they were omitted and routine live membership recovery will retry them."
        return json.dumps({
            "ok": True,
            "status": "warning" if warning_count else "verified",
            "message": f"Energy seed exported with {verification['plan_count']} active plans.{warning_suffix}",
            "file": output_gzip_path,
            "raw_bytes": raw_bytes,
            "compressed_bytes": compressed_bytes,
            "sha256": sha.hexdigest(),
            "seed_format_version": ENERGY_SEED_FORMAT_VERSION,
            "normalizer_version": NORMALIZER_VERSION,
            "generated_at": generated_at,
            "plan_count": verification["plan_count"],
            "electricity_plans": verification["electricity_plans"],
            "gas_plans": verification["gas_plans"],
            "coverage_issues": warning_count,
            "coverage_failure_names": warning_names,
            "requires_live_recovery": bool(verification.get("requires_live_recovery")),
            "discovery_warnings": verification["discovery_warnings"],
        })
    except Exception as exc:
        try:
            os.remove(output_gzip_path)
        except FileNotFoundError:
            pass
        text = str(exc) or exc.__class__.__name__
        if "disk" in text.lower() and "full" in text.lower():
            text += ". Free some internal app storage and retry; seed export needs temporary SQLite workspace."
        return json.dumps({"ok": False, "status": "failed", "stage": stage, "message": f"Energy seed export failed while {stage}: {text}"})
    finally:
        for candidate in (raw_path, raw_path + "-journal", raw_path + "-wal", raw_path + "-shm"):
            try:
                os.remove(candidate)
            except FileNotFoundError:
                pass


def _cloud_semantic_fingerprint(con: sqlite3.Connection) -> str:
    """Fingerprint market content while deliberately ignoring refresh/check timestamps.

    This runs on the central updater, not on normal Android startup. Reading Detail JSON here is
    intentional: it makes the cloud snapshot id sensitive to a Detail-only change even if a
    retailer publishes an imperfect Generic lastUpdated value.
    """
    sha = hashlib.sha256()
    # A client cache key must also roll when the portable snapshot/normalizer contract changes,
    # even if the underlying market happens to be byte-for-byte unchanged.
    sha.update(f"snapshot_format={CLOUD_SNAPSHOT_FORMAT_VERSION};normalizer={NORMALIZER_VERSION}\n".encode("ascii"))
    for row in con.execute(
        "SELECT retailer_key,plan_id,fuel_type,COALESCE(summary_revision,''),COALESCE(summary_json,''),COALESCE(detail_json,'') "
        "FROM energy_plans WHERE COALESCE(is_active,1)=1 ORDER BY retailer_key,plan_id,fuel_type"
    ):
        for value in row:
            sha.update(str(value or "").encode("utf-8"))
            sha.update(b"\x1f")
        sha.update(b"\n")
    sha.update(_savings_market_fingerprint(con).encode("ascii"))
    return sha.hexdigest()


def _copy_sqlite_table(src: sqlite3.Connection, dst: sqlite3.Connection, table: str,
                       where: str = "", params: Sequence[Any] = ()) -> int:
    src_cols = [str(r[1]) for r in src.execute(f"PRAGMA table_info({table})").fetchall()]
    dst_cols = {str(r[1]) for r in dst.execute(f"PRAGMA table_info({table})").fetchall()}
    cols = [c for c in src_cols if c in dst_cols]
    if not cols:
        return 0
    col_sql = ",".join('"' + c.replace('"', '""') + '"' for c in cols)
    sql = f"SELECT {col_sql} FROM {table}" + (f" WHERE {where}" if where else "")
    cur = src.execute(sql, tuple(params))
    insert = f"INSERT OR REPLACE INTO {table}({col_sql}) VALUES({','.join('?' for _ in cols)})"
    total = 0
    while True:
        rows = cur.fetchmany(200)
        if not rows:
            break
        dst.executemany(insert, [tuple(row[i] for i in range(len(cols))) for row in rows])
        total += len(rows)
    return total


def _cloud_snapshot_validate_db(con: sqlite3.Connection) -> Dict[str, Any]:
    integrity = str(con.execute("PRAGMA integrity_check").fetchone()[0] or "").lower()
    if integrity != "ok":
        raise ValueError(f"SQLite integrity_check failed: {integrity}")
    for table in ("energy_plans", "cdr_plans", "sync_state", "nbn_offers", "savings_products"):
        if not con.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table,)).fetchone():
            raise ValueError(f"snapshot is missing required table {table}")
    energy = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1").fetchone()[0])
    electricity = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='ELECTRICITY'").fetchone()[0])
    gas = int(con.execute("SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND UPPER(fuel_type)='GAS'").fetchone()[0])
    incomplete = int(con.execute(
        "SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND "
        "(COALESCE(summary_json,'')='' OR COALESCE(detail_json,'')='' OR COALESCE(detail_cached,0)<>1)"
    ).fetchone()[0])
    newer = int(con.execute(
        "SELECT COUNT(*) FROM energy_plans WHERE COALESCE(is_active,1)=1 AND COALESCE(normalizer_version,0)>?",
        (NORMALIZER_VERSION,),
    ).fetchone()[0])
    savings = int(con.execute("SELECT COUNT(*) FROM savings_products").fetchone()[0])
    if energy <= 0 or electricity <= 0 or gas <= 0:
        raise ValueError("snapshot does not contain a usable electricity and gas baseline")
    if savings <= 0:
        raise ValueError("snapshot does not contain a usable Banking savings baseline")
    if incomplete:
        raise ValueError(f"snapshot contains {incomplete} incomplete active Energy rows")
    if newer:
        raise ValueError(f"snapshot contains {newer} Energy rows from a newer normalizer")
    return {
        "energy_plans": energy,
        "electricity_plans": electricity,
        "gas_plans": gas,
        "savings_products": savings,
    }


def export_cloud_snapshot(db_path: str, output_gzip_path: str, manifest_path: str = "",
                          public_base_url: str = "") -> str:
    """Build the mobile/cloud market database used by the zero-crawl Android fast path.

    This snapshot intentionally contains only Energy and Banking market data. NBN remains an
    on-device refresh because its source is small. The snapshot preserves all active Energy
    Generic + Detail data needed by the comparison engine, while keeping the compatibility
    cdr_plans mirror compact so raw Energy JSON is stored once.
    """
    if not _CDR_SYNC_LOCK.acquire(blocking=False):
        return json.dumps({"ok": False, "status": "busy", "message": "Energy CDR refresh is running; retry cloud export when it finishes."})
    output_gzip_path = os.path.abspath(str(output_gzip_path))
    raw_path = output_gzip_path + ".tmp.db"
    generated_at = _now()
    try:
        os.makedirs(os.path.dirname(output_gzip_path) or ".", exist_ok=True)
        for candidate in (raw_path, raw_path + "-journal", raw_path + "-wal", raw_path + "-shm", output_gzip_path):
            try:
                os.remove(candidate)
            except FileNotFoundError:
                pass

        with _connect(db_path) as src:
            _schema(src)
            counts = _cloud_snapshot_validate_db(src)
            snapshot_id = _cloud_semantic_fingerprint(src)
            refresh_report = {}
            try:
                refresh_report = json.loads(_state_get(src, "last_sync_report", "{}") or "{}")
                if not isinstance(refresh_report, dict):
                    refresh_report = {}
            except Exception:
                refresh_report = {}

            out = sqlite3.connect(raw_path, timeout=30)
            try:
                out.row_factory = sqlite3.Row
                out.execute("PRAGMA journal_mode=DELETE")
                out.execute("PRAGMA synchronous=NORMAL")
                _schema(out)
                out.execute("PRAGMA journal_mode=DELETE")

                _copy_sqlite_table(src, out, "energy_plans", "COALESCE(is_active,1)=1")
                # Avoid duplicating the large raw Generic/Detail JSON in cdr_plans.
                out.execute("DELETE FROM cdr_plans")
                out.execute(
                    """
                    INSERT OR REPLACE INTO cdr_plans(
                        plan_id,provider,name,customer_type,distributors,tariff_type,is_tou,is_flat,
                        has_demand,has_controlled_load,has_solar,daily_supply_cents,avg_usage_cents,
                        last_updated,raw_usage_rates,website,source,fuel_type,retailer_key,
                        detail_json,summary_json,tariff_periods_json,controlled_load_json,eligibility_json,
                        metering_charges_json,solar_feed_in_json,source_plan_id,summary_revision,
                        normalizer_version,is_active,stale_reason
                    )
                    SELECT
                        plan_id,retailer_name,plan_name,customer_type,distributors,tariff_type,is_tou,is_flat,
                        has_demand,has_controlled_load,has_solar,daily_supply_cents,avg_usage_cents,
                        last_updated,raw_usage_rates,application_uri,source,fuel_type,retailer_key,
                        NULL,NULL,tariff_periods_json,controlled_load_json,eligibility_json,
                        metering_charges_json,solar_feed_in_json,source_plan_id,summary_revision,
                        normalizer_version,is_active,stale_reason
                    FROM energy_plans
                    """
                )
                # NBN is deliberately excluded from the cloud snapshot and refreshed on-device.
                out.execute("DELETE FROM nbn_offers")
                _copy_sqlite_table(src, out, "savings_products")

                # Portable market metadata only. Local client/app metadata is never exported.
                state_rows = src.execute(
                    "SELECT key,value,updated_at FROM sync_state WHERE "
                    "key NOT LIKE 'cloud_client_%' AND key NOT LIKE 'seed_%' AND key NOT LIKE 'nbn_%' "
                    "AND key NOT IN ('cloud_applied_at','cloud_last_checked_at')"
                ).fetchall()
                out.executemany(
                    "INSERT OR REPLACE INTO sync_state(key,value,updated_at) VALUES(?,?,?)",
                    [(r["key"], r["value"], r["updated_at"]) for r in state_rows],
                )
                cloud_meta = {
                    "cloud_snapshot_format_version": str(CLOUD_SNAPSHOT_FORMAT_VERSION),
                    "cloud_snapshot_id": snapshot_id,
                    "cloud_generated_at": generated_at,
                    "cloud_app_version": APP_VERSION,
                    "cloud_normalizer_version": str(NORMALIZER_VERSION),
                }
                out.executemany(
                    "INSERT OR REPLACE INTO sync_state(key,value,updated_at) VALUES(?,?,?)",
                    [(k, v, generated_at) for k, v in cloud_meta.items()],
                )
                out.commit()
                verified_counts = _cloud_snapshot_validate_db(out)
                if verified_counts != counts:
                    raise RuntimeError(f"cloud snapshot row-count verification failed: {verified_counts} != {counts}")
            finally:
                out.close()

        raw_bytes = os.path.getsize(raw_path)
        # Use mtime=0 so identical raw database bytes produce deterministic compressed bytes.
        with open(raw_path, "rb") as source, open(output_gzip_path, "wb") as raw_out:
            with gzip.GzipFile(fileobj=raw_out, mode="wb", compresslevel=6, mtime=0) as target:
                for chunk in iter(lambda: source.read(1024 * 1024), b""):
                    target.write(chunk)
        compressed_bytes = os.path.getsize(output_gzip_path)
        compressed_sha = hashlib.sha256()
        with open(output_gzip_path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                compressed_sha.update(chunk)
        db_sha = hashlib.sha256()
        with open(raw_path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                db_sha.update(chunk)

        base = str(public_base_url or "").strip().rstrip("/")
        # The publisher exposes one current database via a stable latest-release URL. Integrity is
        # pinned by SHA-256 in the manifest, and Android rejects any object/manifest mismatch.
        file_sha256 = compressed_sha.hexdigest()
        download_name = "latest.db.gz"
        manifest = {
            "manifest_format_version": CLOUD_MANIFEST_FORMAT_VERSION,
            "snapshot_format_version": CLOUD_SNAPSHOT_FORMAT_VERSION,
            "snapshot_id": snapshot_id,
            "generated_at": generated_at,
            "app_version": APP_VERSION,
            "normalizer_version": NORMALIZER_VERSION,
            "download_url": f"{base}/{download_name}" if base else download_name,
            "compressed_bytes": compressed_bytes,
            "uncompressed_bytes": raw_bytes,
            "sha256": file_sha256,
            "database_sha256": db_sha.hexdigest(),
            "counts": counts,
            "energy_status": str(refresh_report.get("status") or _state_get_from_path(db_path, "last_sync_status", "unknown")),
            "coverage_issues": int(refresh_report.get("coverage_issues") or 0),
            "detail_failures": int(refresh_report.get("detail_failures") or 0),
        }
        if manifest_path:
            manifest_abs = os.path.abspath(str(manifest_path))
            os.makedirs(os.path.dirname(manifest_abs) or ".", exist_ok=True)
            tmp = manifest_abs + ".tmp"
            with open(tmp, "w", encoding="utf-8") as handle:
                json.dump(manifest, handle, indent=2, sort_keys=True)
                handle.write("\n")
            os.replace(tmp, manifest_abs)
        return json.dumps({"ok": True, "status": "ready", "file": output_gzip_path, "manifest": manifest}, separators=(",", ":"))
    except Exception as exc:
        try:
            os.remove(output_gzip_path)
        except FileNotFoundError:
            pass
        return json.dumps({"ok": False, "status": "failed", "message": f"Cloud snapshot export failed: {exc}"})
    finally:
        _CDR_SYNC_LOCK.release()
        for candidate in (raw_path, raw_path + "-journal", raw_path + "-wal", raw_path + "-shm"):
            try:
                os.remove(candidate)
            except FileNotFoundError:
                pass


def _state_get_from_path(db_path: str, key: str, fallback: str = "") -> str:
    with _connect(db_path) as con:
        _schema(con)
        return _state_get(con, key, fallback)


def apply_cloud_snapshot(db_path: str, snapshot_db_path: str, manifest_json: str) -> str:
    """Validate and atomically apply a downloaded cloud snapshot to the live Android DB.

    Automatic cloud updates never fall back to live Energy/Banking CDR crawling. A newer manual
    local FULL Energy verification wins over an older cloud build. NBN is wholly device-owned and
    is never changed by a cloud snapshot.
    """
    if not _CDR_SYNC_LOCK.acquire(blocking=False):
        return json.dumps({"ok": False, "status": "busy", "message": "A manual Energy verification is running; cloud update deferred."})
    try:
        manifest = json.loads(manifest_json or "{}")
        if not isinstance(manifest, dict):
            raise ValueError("invalid cloud manifest")
        if int(manifest.get("manifest_format_version") or 0) != CLOUD_MANIFEST_FORMAT_VERSION:
            raise ValueError("unsupported cloud manifest format")
        if int(manifest.get("snapshot_format_version") or 0) != CLOUD_SNAPSHOT_FORMAT_VERSION:
            raise ValueError("unsupported cloud snapshot format")
        if int(manifest.get("normalizer_version") or 0) > NORMALIZER_VERSION:
            raise ValueError("cloud snapshot requires a newer BillBot normalizer")
        snapshot_id = str(manifest.get("snapshot_id") or "").strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", snapshot_id):
            raise ValueError("cloud snapshot id is invalid")
        generated_at = str(manifest.get("generated_at") or "").strip()
        generated_dt = dt.datetime.fromisoformat(generated_at.replace("Z", "+00:00"))
        if generated_dt.tzinfo is None:
            generated_dt = generated_dt.replace(tzinfo=dt.timezone.utc)
        if generated_dt > dt.datetime.now(dt.timezone.utc) + dt.timedelta(hours=24):
            raise ValueError("cloud snapshot is future dated")

        src = sqlite3.connect(os.path.abspath(snapshot_db_path), timeout=30)
        src.row_factory = sqlite3.Row
        try:
            counts = _cloud_snapshot_validate_db(src)
            state = {str(r[0]): str(r[1]) for r in src.execute("SELECT key,value FROM sync_state")}
            if state.get("cloud_snapshot_id", "").lower() != snapshot_id:
                raise ValueError("cloud snapshot id does not match its SQLite metadata")
            if state.get("cloud_generated_at", "") != generated_at:
                raise ValueError("cloud manifest timestamp does not match its SQLite metadata")
            if int(state.get("cloud_snapshot_format_version", "0") or 0) != CLOUD_SNAPSHOT_FORMAT_VERSION:
                raise ValueError("cloud SQLite snapshot format is unsupported")
            if int(state.get("cloud_normalizer_version", "0") or 0) != int(manifest.get("normalizer_version") or 0):
                raise ValueError("cloud manifest normalizer does not match its SQLite metadata")
            declared = manifest.get("counts") if isinstance(manifest.get("counts"), dict) else {}
            for key, actual in counts.items():
                if key in declared and int(declared.get(key) or 0) != actual:
                    raise ValueError(f"cloud manifest count mismatch for {key}")

            with _connect(db_path) as dst:
                _schema(dst)
                already = _state_get(dst, "cloud_snapshot_id", "").lower()
                if already == snapshot_id:
                    return json.dumps({"ok": True, "status": "unchanged", "updated": False, "snapshot_id": snapshot_id, "message": "Cloud market database is already current."})

                # Never roll a device back if a stale CDN/object-store manifest is observed.
                current_cloud_generated = _state_get(dst, "cloud_generated_at", "")
                if current_cloud_generated:
                    try:
                        current_cloud_dt = dt.datetime.fromisoformat(current_cloud_generated.replace("Z", "+00:00"))
                        if current_cloud_dt.tzinfo is None:
                            current_cloud_dt = current_cloud_dt.replace(tzinfo=dt.timezone.utc)
                        if current_cloud_dt > generated_dt:
                            return json.dumps({"ok": True, "status": "stale_cloud", "updated": False, "snapshot_id": already, "message": "Ignored an older cloud market snapshot; current local cloud data is newer."})
                    except Exception:
                        pass

                # If the user explicitly ran a local FULL verification after this cloud build,
                # never silently replace it with older Energy data. The next daily cloud build can
                # supersede it naturally.
                local_mode = _state_get(dst, "last_energy_sync_mode", "").lower()
                local_last = _state_get(dst, "last_sync", "")
                if local_mode == "full" and local_last:
                    try:
                        local_dt = dt.datetime.fromisoformat(local_last.replace("Z", "+00:00"))
                        if local_dt.tzinfo is None:
                            local_dt = local_dt.replace(tzinfo=dt.timezone.utc)
                        if local_dt > generated_dt:
                            return json.dumps({"ok": True, "status": "local_newer", "updated": False, "snapshot_id": already, "message": "Local Full verification is newer than the cloud snapshot; local Energy data preserved."})
                    except Exception:
                        pass

                old_energy_rev = int(_state_get(dst, "energy_data_revision", "0") or 0)
                old_savings_rev = int(_state_get(dst, "savings_data_revision", "0") or 0)

                dst.execute("BEGIN IMMEDIATE")
                dst.execute("DELETE FROM energy_plans")
                dst.execute("DELETE FROM cdr_plans")
                _copy_sqlite_table(src, dst, "energy_plans")
                _copy_sqlite_table(src, dst, "cdr_plans")

                # NBN is deliberately device-owned. Do not delete, copy or revise any NBN rows.
                dst.execute("DELETE FROM savings_products")
                _copy_sqlite_table(src, dst, "savings_products")

                # Replace portable market state, but keep client-local revision counters and
                # cloud application/check metadata. Revisions are incremented locally so ranking
                # caches invalidate even if server-side counters started from a different seed.
                portable = src.execute(
                    "SELECT key,value,updated_at FROM sync_state WHERE "
                    "key NOT IN ('energy_data_revision','nbn_data_revision','savings_data_revision',"
                    "'cloud_applied_at','cloud_last_checked_at') "
                    "AND key NOT LIKE 'cloud_client_%' AND key NOT LIKE 'nbn_%'"
                ).fetchall()
                # Remove cloud-owned Energy/Banking metadata as a set while preserving all local
                # NBN state/revisions and client-local cloud check metadata.
                dst.execute(
                    "DELETE FROM sync_state WHERE key NOT IN "
                    "('energy_data_revision','nbn_data_revision','savings_data_revision','cloud_last_checked_at') "
                    "AND key NOT LIKE 'cloud_client_%' AND key NOT LIKE 'nbn_%'"
                )
                dst.executemany(
                    "INSERT OR REPLACE INTO sync_state(key,value,updated_at) VALUES(?,?,?)",
                    [(r["key"], r["value"], r["updated_at"]) for r in portable],
                )
                applied_at = _now()
                for key, value in (
                    ("energy_data_revision", str(old_energy_rev + 1)),
                    ("savings_data_revision", str(old_savings_rev + 1)),
                    ("cloud_snapshot_id", snapshot_id),
                    ("cloud_generated_at", generated_at),
                    ("cloud_applied_at", applied_at),
                ):
                    _state_set(dst, key, value, applied_at)
                dst.commit()
                _log(dst, "INFO", f"Applied cloud market snapshot {snapshot_id[:12]} with {counts['energy_plans']} Energy and {counts['savings_products']} Banking rows; NBN preserved on-device")

            return json.dumps({
                "ok": True, "status": "updated", "updated": True, "snapshot_id": snapshot_id,
                "generated_at": generated_at, "counts": counts,
                "message": f"Cloud market database updated: {counts['electricity_plans']} electricity, {counts['gas_plans']} gas and {counts['savings_products']} Banking products. NBN remains on-device.",
            }, separators=(",", ":"))
        finally:
            src.close()
    except Exception as exc:
        return json.dumps({"ok": False, "status": "failed", "updated": False, "message": f"Cloud snapshot rejected: {exc}"})
    finally:
        _CDR_SYNC_LOCK.release()

def sync_energy_all(db_path: str, postcode: str = "", distributor: str = "", progress_path: str = "",
                    mode: str = "AUTO") -> str:
    """Refresh electricity and gas from one shared Generic Plan scan."""
    return _sync_energy_fuels(db_path, ("ELECTRICITY", "GAS"), postcode, distributor, progress_path, mode)


def sync_energy(db_path: str, fuel: str, postcode: str = "", distributor: str = "", progress_path: str = "") -> str:
    """Backward-compatible single-fuel entry point used by tests/older callers."""
    fuel = str(fuel).upper()
    if fuel not in ("ELECTRICITY", "GAS"):
        raise ValueError("fuel must be ELECTRICITY or GAS")
    return _sync_energy_fuels(db_path, (fuel,), postcode, distributor, progress_path, "FULL")

def _period_bounds(period: Dict[str, Any]) -> Tuple[Optional[Tuple[int, int]], Optional[Tuple[int, int]]]:
    def mmdd(value: Any) -> Optional[Tuple[int, int]]:
        text = str(value or "").strip()
        if not text:
            return None
        m = re.search(r"(?<!\d)(\d{1,2})-(\d{1,2})(?!\d)", text)
        if not m:
            return None
        a, b = int(m.group(1)), int(m.group(2))
        # Standard says mm-dd. Be tolerant of accidental dd-mm only when the first token cannot be a month.
        month, day = (b, a) if a > 12 and b <= 12 else (a, b)
        if 1 <= month <= 12 and 1 <= day <= 31:
            return month, day
        return None
    return mmdd(period.get("startDate")), mmdd(period.get("endDate"))


def _period_applies(period: Dict[str, Any], day: dt.date) -> bool:
    start, end = _period_bounds(period)
    if not start and not end:
        return True
    if not start or not end:
        return False
    md = (day.month, day.day)
    if start <= end:
        return start <= md <= end
    return md >= start or md <= end


def _tariff_period_map(periods: Sequence[Dict[str, Any]]) -> Tuple[Optional[List[int]], Optional[str]]:
    if not periods:
        return None, "NO_TARIFF_PERIOD"
    mapping: List[int] = []
    for i in range(365):
        day = dt.date(2025, 1, 1) + dt.timedelta(days=i)
        hits = [idx for idx, p in enumerate(periods) if _period_applies(p, day)]
        if len(hits) != 1:
            return None, "TARIFF_PERIOD_OVERLAP" if len(hits) > 1 else "TARIFF_PERIOD_GAP"
        mapping.append(hits[0])
    return mapping, None


def _parse_iso_duration(value: Any) -> Optional[Tuple[str, int]]:
    text = str(value or "").upper().strip()
    if not text:
        return None
    aliases = {
        "DAY": ("D", 1), "DAILY": ("D", 1), "WEEK": ("W", 1), "WEEKLY": ("W", 1),
        "MONTH": ("M", 1), "MONTHLY": ("M", 1), "QUARTER": ("M", 3), "QUARTERLY": ("M", 3),
        "YEAR": ("Y", 1), "YEARLY": ("Y", 1), "ANNUAL": ("Y", 1), "ANNUALLY": ("Y", 1),
    }
    if text in aliases:
        return aliases[text]
    m = re.fullmatch(r"P(\d+)([DWMY])", text)
    if not m:
        return None
    n = int(m.group(1))
    return (m.group(2), n) if n > 0 else None


def _group_daily_series(series: Sequence[Tuple[dt.date, Decimal]], period: Tuple[str, int]) -> List[Decimal]:
    unit, n = period
    if unit == "D":
        return [sum((x[1] for x in series[i:i+n]), Decimal("0")) for i in range(0, len(series), n)]
    if unit == "W":
        step = 7 * n
        return [sum((x[1] for x in series[i:i+step]), Decimal("0")) for i in range(0, len(series), step)]
    if unit == "M":
        groups: Dict[Tuple[int, int], Decimal] = {}
        for day, usage in series:
            block = (day.year, (day.month - 1) // n)
            groups[block] = groups.get(block, Decimal("0")) + usage
        return list(groups.values())
    if unit == "Y":
        if n != 1:
            return [sum((x[1] for x in series), Decimal("0"))]
        return [sum((x[1] for x in series), Decimal("0"))]
    return []


def _rate_price(rate: Dict[str, Any]) -> Optional[Decimal]:
    return _d(rate.get("unitPrice") if isinstance(rate, dict) else None, None)


def _price_block_usage(usage: Decimal, rates: Sequence[Dict[str, Any]]) -> Optional[Decimal]:
    if usage < 0 or not rates:
        return None
    remaining = usage
    total = Decimal("0")
    for idx, rate in enumerate(rates):
        if not isinstance(rate, dict):
            return None
        price = _rate_price(rate)
        if price is None or price < 0:
            return None
        volume = _d(rate.get("volume"), None)
        if volume is None or volume <= 0:
            qty = remaining
        else:
            qty = min(remaining, volume)
        total += qty * price
        remaining -= qty
        if remaining <= Decimal("0.0000001"):
            return total
    # If every published block had a finite volume but usage exceeds them, the payload is not
    # complete enough to extrapolate a price safely.
    return None if remaining > Decimal("0.0000001") else total


def _price_stepped_series(
    series: Sequence[Tuple[dt.date, Decimal]], rates_raw: Any, period_value: Any,
) -> Tuple[Optional[Decimal], Optional[str]]:
    rates = [r for r in _as_list(rates_raw) if isinstance(r, dict)]
    if not rates:
        return None, "MISSING_USAGE_RATE"
    if len(rates) == 1 and (_d(rates[0].get("volume"), None) in (None, Decimal("0"))):
        price = _rate_price(rates[0])
        return (sum((x[1] for x in series), Decimal("0")) * price, None) if price is not None else (None, "MISSING_USAGE_RATE")
    parsed = _parse_iso_duration(period_value)
    if parsed is None:
        return None, "BLOCK_PERIOD_REQUIRED"
    groups = _group_daily_series(series, parsed)
    if not groups:
        return None, "BLOCK_PERIOD_UNSUPPORTED"
    total = Decimal("0")
    for usage in groups:
        cost = _price_block_usage(usage, rates)
        if cost is None:
            return None, "BLOCK_RATE_INCOMPLETE"
        total += cost
    return total, None


def _supply_for_period(period: Dict[str, Any], days: int) -> Tuple[Optional[Decimal], Optional[str]]:
    # Current Plan Detail v3 has explicit SINGLE/BAND supply semantics. Banded supply
    # rates use volume as the number of DAYS in that block, so the same stepped-block
    # calculator can price the number of days mapped to this tariff period.
    charge_type = str(period.get("dailySupplyChargeType") or "").upper()
    banded = [x for x in _as_list(period.get("bandedDailySupplyCharges")) if isinstance(x, dict)]
    if charge_type == "BAND" or banded:
        if not banded:
            return None, "BANDED_SUPPLY_RATE_REQUIRED"
        cost = _price_block_usage(Decimal(days), banded)
        return (cost, None) if cost is not None else (None, "BANDED_SUPPLY_RATE_INCOMPLETE")

    raw = period.get("dailySupplyCharge")
    if raw is None:
        raw = period.get("dailySupplyCharges")  # legacy v2 cache compatibility
    if raw is None:
        return Decimal("0"), None
    if isinstance(raw, list):
        if len(raw) != 1:
            return None, "INVALID_SUPPLY_CHARGE"
        raw = raw[0]
    if isinstance(raw, dict):
        raw = raw.get("amount") or raw.get("unitPrice") or raw.get("value")
    amount = _d(raw, None)
    if amount is None or amount < 0:
        return None, "INVALID_SUPPLY_CHARGE"
    return amount * Decimal(days), None


def _normalise_tou_shares(raw: Any) -> Dict[str, Decimal]:
    if isinstance(raw, str):
        try:
            raw = json.loads(raw) if raw.strip() else {}
        except Exception:
            raw = {}
    if not isinstance(raw, dict):
        return {}
    out: Dict[str, Decimal] = {}
    for key, value in raw.items():
        d = _d(value, None)
        if d is None or d < 0:
            continue
        out[_norm(key)] = d
    total = sum(out.values(), Decimal("0"))
    if total <= 0:
        return {}
    # Accept either fractions or percentages, then normalise to exactly 1.
    return {k: v / total for k, v in out.items()}


def _tou_band_share(band: Dict[str, Any], shares: Dict[str, Decimal]) -> Optional[Decimal]:
    candidates = [band.get("type"), band.get("displayName"), band.get("description")]
    for value in candidates:
        n = _norm(value)
        if n in shares:
            return shares[n]
        for key, share in shares.items():
            if key and n and (key in n or n in key):
                return share
    aliases = {
        "peak": ["peak"], "offpeak": ["offpeak", "offpeakusage"], "shoulder": ["shoulder"],
    }
    n = _norm(band.get("type") or band.get("displayName"))
    for canonical, names in aliases.items():
        if canonical in n:
            for name in names:
                if name in shares:
                    return shares[name]
    return None


def _indicative_tou_band_shares(bands: Sequence[Dict[str, Any]]) -> List[Decimal]:
    """Return a plan-compatible residential TOU estimate for the published bands.

    The UI only knows that the customer wants a TOU comparison, not their interval-meter
    profile. Retailers publish different band structures (commonly peak/off-peak or
    peak/shoulder/off-peak), so one fixed three-band split can incorrectly make otherwise
    priceable plans look incomplete. Keep the estimate deliberately simple and normalised
    to the bands which actually exist on each plan.
    """
    if not bands:
        return []

    kinds: List[str] = []
    for band in bands:
        n = _norm(band.get("type") or band.get("displayName") or band.get("description"))
        if "offpeak" in n:
            kinds.append("offpeak")
        elif "shoulder" in n:
            kinds.append("shoulder")
        elif "peak" in n:
            kinds.append("peak")
        else:
            kinds.append("other")

    # Unknown/custom retailer bands cannot be mapped honestly to the standard residential
    # labels. Equal weighting is preferable to excluding the plan entirely, and the result
    # remains explicitly MODELLED_TOU rather than VERIFIED.
    if "other" in kinds:
        equal = Decimal("1") / Decimal(len(bands))
        return [equal for _ in bands]

    present = set(kinds)
    if present == {"peak", "shoulder", "offpeak"}:
        base = {"peak": Decimal("0.30"), "shoulder": Decimal("0.30"), "offpeak": Decimal("0.40")}
    elif present == {"peak", "offpeak"}:
        base = {"peak": Decimal("0.35"), "offpeak": Decimal("0.65")}
    elif present == {"shoulder", "offpeak"}:
        base = {"shoulder": Decimal("0.40"), "offpeak": Decimal("0.60")}
    elif present == {"peak", "shoulder"}:
        base = {"peak": Decimal("0.55"), "shoulder": Decimal("0.45")}
    else:
        equal = Decimal("1") / Decimal(len(bands))
        return [equal for _ in bands]

    counts = {kind: kinds.count(kind) for kind in present}
    weights = [base[kind] / Decimal(counts[kind]) for kind in kinds]
    total = sum(weights, Decimal("0"))
    return [w / total for w in weights] if total > 0 else weights


def _contract_is_tou(detail: Dict[str, Any], summary: Dict[str, Any], fuel: str) -> bool:
    """Use current Plan Detail as the source of truth for tariff type.

    `energy_plans.is_tou` is a denormalised search aid and can lag older snapshots. The
    comparison path already has fresh detail JSON, so filtering on the actual contract avoids
    a stale flag accidentally producing an empty TOU catalogue.
    """
    contract = _contract(detail, fuel)
    if not contract:
        return False
    if str(contract.get("pricingModel") or "").upper() == "TIME_OF_USE":
        return True
    return any(
        isinstance(period, dict) and bool(_as_list(period.get("timeOfUseRates")))
        for period in _as_list(contract.get("tariffPeriod"))
    )


def _price_tou_period(
    period_series: Sequence[Tuple[dt.date, Decimal]], bands_raw: Any, shares: Dict[str, Decimal],
    indicative: bool = False,
) -> Tuple[Optional[Decimal], Optional[str], List[str]]:
    bands = [b for b in _as_list(bands_raw) if isinstance(b, dict)]
    if not bands:
        return None, "MISSING_TOU_RATES", []
    mapped: List[Tuple[Dict[str, Any], Decimal]] = []
    warnings: List[str] = []
    if indicative:
        estimated = _indicative_tou_band_shares(bands)
        mapped = list(zip(bands, estimated))
        warnings.append("TOU annual cost uses an indicative residential usage split because interval-meter usage was not supplied.")
    else:
        if not shares:
            return None, "TOU_PROFILE_REQUIRED", []
        for band in bands:
            share = _tou_band_share(band, shares)
            if share is None:
                return None, "TOU_BAND_MAPPING_REQUIRED", []
            mapped.append((band, share))
    mapped_total = sum((x[1] for x in mapped), Decimal("0"))
    if abs(mapped_total - Decimal("1")) > Decimal("0.02"):
        return None, "TOU_SHARES_INCOMPLETE", []
    period_usage = sum((x[1] for x in period_series), Decimal("0"))
    total = Decimal("0")
    for band, share in mapped:
        rates = [r for r in _as_list(band.get("rates")) if isinstance(r, dict)]
        if not rates:
            return None, "MISSING_TOU_RATE", []
        band_usage = period_usage * share / mapped_total
        if len(rates) == 1 and (_d(rates[0].get("volume"), None) in (None, Decimal("0"))):
            price = _rate_price(rates[0])
            if price is None:
                return None, "MISSING_TOU_RATE", []
            total += band_usage * price
        else:
            # Current Plan Detail v3 permits an ISO-8601 period on stepped TOU bands. If it is
            # absent, the block reset cannot be inferred safely.
            reset = band.get("period")
            if not reset:
                return None, "TOU_BLOCK_PERIOD_REQUIRED", []
            scaled = [(day, usage * share / mapped_total) for day, usage in period_series]
            cost, issue = _price_stepped_series(scaled, rates, reset)
            if cost is None:
                return None, issue or "TOU_BLOCK_RATE_UNSUPPORTED", []
            total += cost
    return total, None, warnings


def _eligibility_status(detail: Dict[str, Any], summary: Dict[str, Any]) -> Tuple[str, List[str]]:
    eligibility = detail.get("eligibility")
    if eligibility in (None, [], {}):
        eligibility = summary.get("eligibility")
    items = [x for x in _as_list(eligibility) if x not in (None, "")]
    if not items:
        return "VERIFIED", []
    warnings: List[str] = []
    unknown = False
    for item in items:
        if isinstance(item, str):
            etype = item
            info = item
        elif isinstance(item, dict):
            etype = str(item.get("type") or item.get("category") or item.get("eligibilityType") or "")
            info = _compact(item.get("information") or item.get("description") or item.get("displayName") or etype)
        else:
            unknown = True
            continue
        norm = re.sub(r"[^A-Z0-9]+", "_", etype.upper()).strip("_")
        if "EXISTING" in norm and "CUSTOMER" in norm:
            return "INELIGIBLE", [info or "Existing-customer-only eligibility"]
        if norm not in KNOWN_UNCONDITIONAL_ELIGIBILITY:
            unknown = True
            warnings.append(info or etype or "Eligibility condition requires checking")
    return ("CHECK_REQUIRED", warnings) if unknown else ("VERIFIED", warnings)


def _has_metering_charge(contract: Dict[str, Any]) -> bool:
    charges = [x for x in _as_list(contract.get("meteringCharges")) if x not in (None, {}, "")]
    return bool(charges)


def _price_controlled_load(
    contract: Dict[str, Any], annual_cl: Decimal, profile: Optional[Sequence[Decimal]],
    cl_tou_shares: Dict[str, Decimal],
) -> Tuple[Optional[Decimal], Optional[str], List[str]]:
    if annual_cl <= 0:
        return Decimal("0"), None, ["Published controlled-load tariff is unused because controlled-load usage is 0 kWh/year."] if _as_list(contract.get("controlledLoad")) else []
    options = [x for x in _as_list(contract.get("controlledLoad")) if isinstance(x, dict)]
    if not options:
        return None, "CONTROLLED_LOAD_PLAN_REQUIRED", []
    if len(options) > 1:
        return None, "CONTROLLED_LOAD_TARIFF_REQUIRED", []
    option = options[0]
    series = _annual_daily_series(annual_cl, profile)
    rate_type = str(option.get("rateBlockUType") or "").lower()
    supply_raw = option.get("dailySupplyCharge")
    if rate_type == "singleRate".lower() or option.get("singleRate"):
        sr = option.get("singleRate") or {}
        if not isinstance(sr, dict):
            return None, "CONTROLLED_LOAD_RATE_REQUIRED", []
        # In Plan Detail v3 controlled-load daily supply may be nested in singleRate.
        # Accept the legacy outer placement as well, but never count both.
        if supply_raw is None:
            supply_raw = sr.get("dailySupplyCharge")
        supply = _d(supply_raw, "0") or Decimal("0")
        supply_cost = supply * DAYS_PER_YEAR
        rates = _as_list(sr.get("rates"))
        if len(rates) > 1 and not sr.get("period"):
            return None, "CONTROLLED_LOAD_BLOCK_PERIOD_REQUIRED", []
        usage_cost, issue = _price_stepped_series(series, rates, sr.get("period") or "P1Y")
        return ((supply_cost + usage_cost) if usage_cost is not None else None, issue, [])
    if rate_type == "timeofuserates" or option.get("timeOfUseRates"):
        tou_bands = [band for band in _as_list(option.get("timeOfUseRates")) if isinstance(band, dict)]
        if supply_raw is None:
            nested_supply = {
                value for value in (_d(band.get("dailySupplyCharge"), None) for band in tou_bands)
                if value is not None
            }
            # A repeated identical nested charge is one controlled-load access charge, not one
            # charge per TOU band. Different values are ambiguous without tariff-specific rules.
            if len(nested_supply) > 1:
                return None, "CONTROLLED_LOAD_SUPPLY_AMBIGUOUS", []
            if nested_supply:
                supply_raw = next(iter(nested_supply))
        supply = _d(supply_raw, "0") or Decimal("0")
        supply_cost = supply * DAYS_PER_YEAR
        usage_cost, issue, warnings = _price_tou_period(series, tou_bands, cl_tou_shares)
        return ((supply_cost + usage_cost) if usage_cost is not None else None, issue, warnings)
    return None, "CONTROLLED_LOAD_RATE_REQUIRED", []


def _price_demand(contract: Dict[str, Any], max_demand_kw: Optional[Decimal]) -> Tuple[Optional[Decimal], Optional[str]]:
    charges: List[Dict[str, Any]] = []
    for period in _as_list(contract.get("tariffPeriod")):
        if isinstance(period, dict):
            charges.extend(x for x in _as_list(period.get("demandCharges")) if isinstance(x, dict))
    if not charges:
        return Decimal("0"), None
    if max_demand_kw is None or max_demand_kw <= 0:
        return None, "DEMAND_DATA_REQUIRED"
    total = Decimal("0")
    for charge in charges:
        amount = _d(charge.get("amount"), None)
        if amount is None:
            return None, "DEMAND_RATE_REQUIRED"
        unit = str(charge.get("measureUnit") or "KW").upper()
        if unit not in ("KW", "KVA"):
            return None, "DEMAND_MEASURE_UNSUPPORTED"
        cp = str(charge.get("chargePeriod") or "").upper()
        duration = _parse_iso_duration(cp)
        if duration is None:
            duration = {"DAY": ("D", 1), "MONTH": ("M", 1), "YEAR": ("Y", 1)}.get(cp)
        if duration == ("D", 1):
            multiplier = DAYS_PER_YEAR
        elif duration == ("M", 1):
            multiplier = Decimal("12")
        elif duration == ("Y", 1):
            multiplier = Decimal("1")
        else:
            return None, "DEMAND_CHARGE_PERIOD_UNSUPPORTED"
        total += max_demand_kw * amount * multiplier
    return total, None


def _price_contract(detail: Dict[str, Any], summary: Dict[str, Any], request: Dict[str, Any]) -> Dict[str, Any]:
    fuel = str(request.get("fuel") or summary.get("fuelType") or detail.get("fuelType") or "ELECTRICITY").upper()
    contract = _contract(detail, fuel)
    if not contract:
        return {"priceable": False, "classification": "CONTRACT_MISSING", "reason": "No matching energy contract in Plan Detail v3."}
    annual_usage = _d(request.get("annual_usage"), None)
    if annual_usage is None or annual_usage <= 0:
        return {"priceable": False, "classification": "USAGE_REQUIRED", "reason": "Annual usage is required."}
    annual_cl = _d(request.get("annual_controlled_load_usage"), "0") or Decimal("0")
    solar_export = _d(request.get("annual_solar_export"), "0") or Decimal("0")
    max_demand = _d(request.get("max_demand_kw"), None)
    postcode = str(request.get("postcode") or "")
    state = str(request.get("state") or _state_from_postcode(postcode))
    profile = _profile_for(fuel, postcode, state)
    series = _annual_daily_series(annual_usage, profile)
    tou_shares = _normalise_tou_shares(request.get("tou_shares"))
    cl_tou_shares = _normalise_tou_shares(request.get("controlled_load_tou_shares"))

    eligibility, eligibility_warnings = _eligibility_status(detail, summary)
    if eligibility == "INELIGIBLE":
        return {"priceable": False, "classification": "INELIGIBLE", "reason": "; ".join(eligibility_warnings)}

    pricing_model = str(contract.get("pricingModel") or "").upper()
    if pricing_model in ("FLEXIBLE", "QUOTA"):
        return {"priceable": False, "classification": "COMPLEX_PRICING_MODEL", "reason": f"{pricing_model} pricing requires contract-specific inputs."}

    periods = [p for p in _as_list(contract.get("tariffPeriod")) if isinstance(p, dict)]
    mapping, map_issue = _tariff_period_map(periods)
    if mapping is None:
        return {"priceable": False, "classification": map_issue or "TARIFF_PERIOD_REQUIRED", "reason": "Tariff periods do not map unambiguously across a full year."}

    is_tou = pricing_model == "TIME_OF_USE" or any(bool(_as_list(p.get("timeOfUseRates"))) for p in periods)
    controlled_load_is_tou = annual_cl > 0 and any(
        isinstance(option, dict)
        and (str(option.get("rateBlockUType") or "").lower() == "timeofuserates" or bool(_as_list(option.get("timeOfUseRates"))))
        for option in _as_list(contract.get("controlledLoad"))
    )
    ex_gst_total = Decimal("0")
    warnings = list(eligibility_warnings)
    for idx, period in enumerate(periods):
        period_series = [item for day_index, item in enumerate(series) if mapping[day_index] == idx]
        days = len(period_series)
        if not period_series:
            continue
        supply_cost, supply_issue = _supply_for_period(period, days)
        if supply_cost is None:
            return {"priceable": False, "classification": supply_issue or "SUPPLY_RATE_REQUIRED", "reason": "Supply charge could not be priced reliably."}
        ex_gst_total += supply_cost
        block_type = str(period.get("rateBlockUType") or "").lower()
        if is_tou or block_type == "timeofuserates" or _as_list(period.get("timeOfUseRates")):
            usage_cost, issue, tou_warnings = _price_tou_period(
                period_series,
                period.get("timeOfUseRates"),
                tou_shares,
                indicative=str(request.get("tou_profile_source") or "").upper() == "PROFILE_ESTIMATE",
            )
            warnings.extend(tou_warnings)
            if usage_cost is None:
                return {"priceable": False, "classification": issue or "TOU_PROFILE_REQUIRED", "reason": "Time-of-use plan needs a compatible usage split before it can be ranked."}
            ex_gst_total += usage_cost
        else:
            sr = period.get("singleRate") or {}
            if not isinstance(sr, dict):
                return {"priceable": False, "classification": "SINGLE_RATE_REQUIRED", "reason": "Single-rate tariff block was missing."}
            cost, issue = _price_stepped_series(period_series, sr.get("rates"), sr.get("period") or ("P1Y" if len(_as_list(sr.get("rates"))) <= 1 else None))
            if cost is None:
                return {"priceable": False, "classification": issue or "USAGE_RATE_REQUIRED", "reason": "Usage rate could not be priced reliably."}
            ex_gst_total += cost

    cl_cost, cl_issue, cl_warnings = _price_controlled_load(contract, annual_cl, profile, cl_tou_shares)
    warnings.extend(cl_warnings)
    if cl_cost is None:
        return {"priceable": False, "classification": cl_issue or "CONTROLLED_LOAD_DATA_REQUIRED", "reason": "Controlled-load tariff needs additional customer data."}
    ex_gst_total += cl_cost

    demand_cost, demand_issue = _price_demand(contract, max_demand)
    if demand_cost is None:
        return {"priceable": False, "classification": demand_issue or "DEMAND_DATA_REQUIRED", "reason": "Demand tariff needs demand data or unsupported demand semantics."}
    ex_gst_total += demand_cost

    if _has_metering_charge(contract):
        return {"priceable": False, "classification": "METERING_CHARGE_CHECK_REQUIRED", "reason": "Published separate metering charges need confirmation before ranking."}

    if solar_export > 0 and _as_list(contract.get("solarFeedInTariff")):
        # Residential solar credits have GST/timing nuances; without an export profile and a
        # verified tariff match, do not make the headline cost look more precise than it is.
        return {"priceable": False, "classification": "SOLAR_EXPORT_PROFILE_REQUIRED", "reason": "Solar export is present; feed-in credits require a compatible export profile."}

    annual_cost = ex_gst_total * GST
    if eligibility == "CHECK_REQUIRED":
        classification = "ELIGIBILITY_CHECK_REQUIRED"
        confidence = "MEDIUM"
    elif demand_cost > 0:
        classification = "MODELLED_DEMAND"
        confidence = "MEDIUM"
    elif is_tou or controlled_load_is_tou:
        classification = "MODELLED_TOU"
        confidence = "MEDIUM"
    else:
        classification = "VERIFIED"
        confidence = "HIGH"
    return {
        "priceable": True, "classification": classification, "confidence": confidence,
        "annual_cost": annual_cost, "pricing_mode": "TIME_OF_USE" if (is_tou or controlled_load_is_tou) else "SINGLE_RATE",
        "warnings": warnings, "has_controlled_load": bool(_as_list(contract.get("controlledLoad"))),
        "has_demand": demand_cost > 0, "has_solar": bool(_as_list(contract.get("solarFeedInTariff"))),
    }


def _plan_from_row(row: sqlite3.Row) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    try:
        summary = json.loads(row["summary_json"] or "{}")
    except Exception:
        summary = {}
    try:
        detail = json.loads(row["detail_json"] or "{}")
    except Exception:
        detail = {}
    return summary if isinstance(summary, dict) else {}, detail if isinstance(detail, dict) else {}


def _display_money_amount(value: Any) -> str:
    amount = _d(value, None)
    if amount is None:
        return ""
    return f"${float(amount):,.2f}"


def _plan_fee_lines(detail: Dict[str, Any], fuel: str) -> List[str]:
    contract = _contract(detail, fuel)
    lines: List[str] = []
    seen = set()

    def add(text: str) -> None:
        clean = _compact(text)
        key = clean.casefold()
        if clean and key not in seen:
            seen.add(key); lines.append(clean)

    for fee in _as_list(detail.get("fees")) + _as_list(contract.get("fees")):
        if not isinstance(fee, dict):
            continue
        fee_type = str(fee.get("type") or "Fee").replace("_", " ").title()
        term = str(fee.get("term") or "").replace("_", " ").title()
        amount = _display_money_amount(fee.get("amount"))
        rate = _compact(fee.get("rate"))
        value = amount or (f"{rate}%" if rate and not rate.endswith("%") else rate)
        suffix = " · ".join(x for x in (value, term, _compact(fee.get("description"))) if x)
        add(f"{fee_type}: {suffix}" if suffix else fee_type)

    for charge in _as_list(detail.get("meteringCharges")) + _as_list(contract.get("meteringCharges")):
        if not isinstance(charge, dict):
            continue
        name = _compact(charge.get("displayName") or "Metering charge")
        minimum = _display_money_amount(charge.get("minimumValue"))
        maximum = _display_money_amount(charge.get("maximumValue"))
        amount = f"{minimum}–{maximum}" if minimum and maximum and minimum != maximum else (minimum or maximum)
        period = _compact(charge.get("period"))
        description = _compact(charge.get("description"))
        add(" · ".join(x for x in (name, amount, period, description) if x))

    additional = _compact(contract.get("additionalFeeInformation"))
    if additional:
        add(additional)
    return lines[:12]


def _controlled_load_rate_lines(detail: Dict[str, Any], fuel: str) -> List[str]:
    contract = _contract(detail, fuel)
    lines: List[str] = []
    for controlled in _as_list(contract.get("controlledLoad")):
        if not isinstance(controlled, dict):
            continue
        name = _compact(controlled.get("displayName") or "Controlled load")
        single = controlled.get("singleRate") or {}
        if isinstance(single, dict):
            for rate in _as_list(single.get("rates")):
                if isinstance(rate, dict):
                    price = _d(rate.get("unitPrice"), None)
                    if price is not None:
                        lines.append(f"{name}: {float(price * GST * CENTS):.3f}c/{str(rate.get('measureUnit') or 'kWh').lower()}")
        for tou in _as_list(controlled.get("timeOfUseRates")):
            if not isinstance(tou, dict):
                continue
            label = _compact(tou.get("displayName") or tou.get("type") or name)
            for rate in _as_list(tou.get("rates")):
                if isinstance(rate, dict):
                    price = _d(rate.get("unitPrice"), None)
                    if price is not None:
                        lines.append(f"{label}: {float(price * GST * CENTS):.3f}c/{str(rate.get('measureUnit') or 'kWh').lower()}")
    return list(dict.fromkeys(lines))[:12]


def _solar_rate_lines(detail: Dict[str, Any], fuel: str) -> List[str]:
    """Return published solar feed-in rates from current and legacy CDR shapes.

    Energy plan unit prices are published ex-GST. Unlike customer charges, feed-in
    credits should not be blindly grossed up by 10% because GST treatment depends on
    the customer's circumstances. The UI therefore displays the published rate.
    """
    contract = _contract(detail, fuel)
    lines: List[str] = []

    def add_rates(container: Any, default_label: str) -> None:
        for block in _as_list(container):
            if not isinstance(block, dict):
                continue
            raw_label = block.get("displayName") or block.get("type") or default_label
            block_label = _compact(str(raw_label).replace("_", " ").title() if block.get("displayName") is None and block.get("type") else raw_label)
            # Current CDR plan schemas wrap prices inside a `rates` array. Keep a
            # direct-rate fallback for older/test payloads seen in the wild.
            rates = _as_list(block.get("rates")) if block.get("rates") is not None else [block]
            for rate in rates:
                if not isinstance(rate, dict):
                    continue
                amount = _d(rate.get("unitPrice") or rate.get("amount") or rate.get("rate"), None)
                if amount is None:
                    continue
                unit = str(rate.get("measureUnit") or "KWH").upper()
                unit_label = "kWh" if unit == "KWH" else unit.lower()
                rate_label = _compact(rate.get("displayName") or block_label or default_label)
                lines.append(f"{rate_label}: {float(amount * CENTS):.3f}c/{unit_label} published")

    for item in _as_list(contract.get("solarFeedInTariff")):
        if not isinstance(item, dict):
            continue
        name = _compact(item.get("displayName") or "Solar feed-in")
        add_rates(item.get("singleTariff"), name)
        add_rates(item.get("timeVaryingTariffs"), name)
    return list(dict.fromkeys(lines))[:12]


def _plan_output(row: sqlite3.Row, detail: Dict[str, Any], priced: Dict[str, Any], current_cost: Optional[Decimal]) -> Dict[str, Any]:
    annual = priced.get("annual_cost")
    annual_d = annual if isinstance(annual, Decimal) else _d(annual, None)
    savings = (current_cost - annual_d) if current_cost is not None and annual_d is not None else None
    warnings = priced.get("warnings") or []
    notes = "; ".join(_compact(x) for x in warnings if _compact(x))
    return {
        "plan_id": str(row["source_plan_id"] or row["plan_id"]), "source_plan_id": str(row["source_plan_id"] or row["plan_id"]),
        "plan_name": str(row["plan_name"] or detail.get("displayName") or "Unnamed plan"),
        "retailer": str(row["retailer_name"] or "Energy retailer"),
        "website": str(row["application_uri"] or ""), "application_uri": str(row["application_uri"] or ""),
        "annual_cost": _json_money(annual_d), "savings": _json_money(savings),
        "avg_usage": row["avg_usage_cents"], "daily_supply": row["daily_supply_cents"],
        "raw_rates": str(row["raw_usage_rates"] or ""),
        "fee_lines": _plan_fee_lines(detail, str(row["fuel_type"] or "")),
        "controlled_load_rates": _controlled_load_rate_lines(detail, str(row["fuel_type"] or "")),
        "solar_rates": _solar_rate_lines(detail, str(row["fuel_type"] or "")),
        "has_solar": bool(row["has_solar"] or 0), "has_controlled_load": bool(row["has_controlled_load"] or 0),
        "pricing_mode": priced.get("pricing_mode") or str(row["tariff_type"] or ""),
        "classification": priced.get("classification") or "UNKNOWN",
        "confidence": priced.get("confidence") or "LOW", "notes": notes,
        "source": str(row["source"] or "CDR"), "last_updated": str(row["last_updated"] or ""),
    }


def _unpriced_output(row: sqlite3.Row, priced: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "plan_id": str(row["source_plan_id"] or row["plan_id"]), "plan_name": str(row["plan_name"] or "Unnamed plan"),
        "retailer": str(row["retailer_name"] or "Energy retailer"),
        "classification": priced.get("classification") or "UNPRICED",
        "reason": priced.get("reason") or "Additional information is required.",
        "application_uri": str(row["application_uri"] or ""), "source": str(row["source"] or "CDR"),
    }


def _dedupe_ranked(plans: List[Dict[str, Any]], merge_controlled_load_variants: bool) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    groups: Dict[Tuple[Any, ...], Dict[str, Any]] = {}
    for plan in sorted(plans, key=lambda x: (x.get("annual_cost") is None, x.get("annual_cost") or 10**12, _norm(x.get("retailer")), _norm(x.get("plan_name")))):
        if merge_controlled_load_variants:
            key = (_norm(plan.get("retailer")), _norm(plan.get("plan_name")), round(float(plan.get("annual_cost") or 0), 2))
        else:
            key = (str(plan.get("plan_id")),)
        if key not in groups:
            copy = dict(plan)
            copy["_merged_plan_ids"] = [plan.get("plan_id")]
            groups[key] = copy
            out.append(copy)
        else:
            groups[key]["_merged_plan_ids"].append(plan.get("plan_id"))
            if plan.get("has_controlled_load"):
                groups[key]["notes"] = _compact((groups[key].get("notes") or "") + " Also published with an unused controlled-load variant.")
    return out


def _market_refresh(con: sqlite3.Connection) -> Dict[str, Any]:
    last = con.execute("SELECT value FROM sync_state WHERE key='last_sync'").fetchone()
    status = con.execute("SELECT value FROM sync_state WHERE key='last_sync_status'").fetchone()
    report = con.execute("SELECT value FROM sync_state WHERE key='last_sync_report'").fetchone()
    try:
        parsed = json.loads(report[0]) if report else {}
    except Exception:
        parsed = {}
    return {"last_sync": last[0] if last else None, "status": status[0] if status else "never", **parsed}


def compare_energy_v2(db_path: str, request_json: str) -> str:
    try:
        request = json.loads(request_json) if isinstance(request_json, str) else dict(request_json)
    except Exception as exc:
        raise ValueError(f"Invalid comparison request JSON: {exc}")
    fuel = str(request.get("fuel") or "ELECTRICITY").upper()
    if fuel not in ("ELECTRICITY", "GAS"):
        raise ValueError("fuel must be ELECTRICITY or GAS")
    request["fuel"] = fuel
    postcode = str(request.get("postcode") or "").strip()
    distributor = str(request.get("distributor") or "").strip()
    customer_type = "BUSINESS" if str(request.get("customer_type") or "").upper() == "BUSINESS" else "RESIDENTIAL"
    current_cost = _d(request.get("current_annual_cost"), None)
    annual_usage = _d(request.get("annual_usage"), None)
    if annual_usage is None or annual_usage <= 0:
        return json.dumps({"ok": False, "error": "Annual usage is missing or zero."})

    with _connect(db_path) as con:
        _schema(con)
        rows = con.execute("SELECT * FROM energy_plans WHERE UPPER(fuel_type)=? AND COALESCE(is_active,1)=1", (fuel,)).fetchall()
        market_refresh = _market_refresh(con)
    verified: List[Dict[str, Any]] = []
    modelled: List[Dict[str, Any]] = []
    eligibility_check: List[Dict[str, Any]] = []
    needs_input: List[Dict[str, Any]] = []
    excluded = 0
    candidate_count = 0
    classification_counts: Dict[str, int] = {}
    current_plan_id = str(request.get("current_plan_id") or "").strip()
    tariff_preference = str(request.get("tariff_preference") or "").upper() if fuel == "ELECTRICITY" else ""
    if tariff_preference not in ("SINGLE_RATE", "TIME_OF_USE"):
        tariff_preference = ""
    for row in rows:
        summary, detail = _plan_from_row(row)
        source_plan_id = str(row["source_plan_id"] or row["plan_id"] or "")
        if not _detail_fresh_for_summary(summary, detail):
            candidate_count += 1
            priced = {"priceable": False, "classification": "STALE_PLAN_DETAIL", "reason": "Cached Plan Detail is older than the CURRENT plan summary."}
            classification_counts["STALE_PLAN_DETAIL"] = classification_counts.get("STALE_PLAN_DETAIL", 0) + 1
            needs_input.append(_unpriced_output(row, priced))
            continue
        geo_source = detail if detail.get("geography") else summary
        if not _fuel_matches(summary or detail, fuel) or not _customer_type_matches(detail or summary, customer_type):
            excluded += 1
            continue
        if not _geography_matches(geo_source, postcode, distributor):
            excluded += 1
            continue
        if tariff_preference:
            detail_is_tou = _contract_is_tou(detail, summary, fuel)
            if tariff_preference == "TIME_OF_USE" and not detail_is_tou:
                excluded += 1
                continue
            if tariff_preference == "SINGLE_RATE" and detail_is_tou:
                excluded += 1
                continue
        candidate_count += 1
        priced = _price_contract(detail, summary, request)
        classification = str(priced.get("classification") or "UNKNOWN")
        classification_counts[classification] = classification_counts.get(classification, 0) + 1
        if not priced.get("priceable"):
            needs_input.append(_unpriced_output(row, priced))
            continue
        output = _plan_output(row, detail, priced, current_cost)
        if classification == "VERIFIED":
            verified.append(output)
        elif classification == "ELIGIBILITY_CHECK_REQUIRED":
            eligibility_check.append(output)
        else:
            modelled.append(output)
    merge_cl = (_d(request.get("annual_controlled_load_usage"), "0") or Decimal("0")) <= 0
    verified = _dedupe_ranked(verified, merge_cl)
    modelled = _dedupe_ranked(modelled, merge_cl)
    eligibility_check = _dedupe_ranked(eligibility_check, merge_cl)
    verified.sort(key=lambda x: x.get("annual_cost") or 10**12)
    modelled.sort(key=lambda x: x.get("annual_cost") or 10**12)
    eligibility_check.sort(key=lambda x: x.get("annual_cost") or 10**12)

    current_has_cl = (_d(request.get("annual_controlled_load_usage"), "0") or Decimal("0")) > 0
    current_has_solar = (_d(request.get("annual_solar_export"), "0") or Decimal("0")) > 0
    def _not_current_plan(plan):
        return not current_plan_id or str(plan.get("plan_id") or "").strip() != current_plan_id
    recommended_verified = [p for p in verified if _not_current_plan(p)]
    recommended_modelled = [p for p in modelled if _not_current_plan(p)]
    recommended_eligibility = [p for p in eligibility_check if _not_current_plan(p)]
    selected_ui = recommended_verified[:3] + recommended_modelled[:3]
    # Compact catalogue used by the Profile plan picker. Keep the comparison cards rich,
    # but expose enough matched plans here to search by retailer + plan without loading
    # the whole raw CDR payload into Compose.
    lookup_rows = []
    lookup_seen = set()
    for plan in verified + modelled + eligibility_check:
        key = str(plan.get("plan_id") or "").strip() or (
            _norm(plan.get("retailer")), _norm(plan.get("plan_name"))
        )
        if key in lookup_seen:
            continue
        lookup_seen.add(key)
        lookup_rows.append({
            "retailer": plan.get("retailer") or "",
            "plan_name": plan.get("plan_name") or "",
            "annual_cost": plan.get("annual_cost"),
            "plan_id": plan.get("plan_id") or "",
        })
    lookup_rows.sort(key=lambda x: (_norm(x.get("retailer")), _norm(x.get("plan_name")), x.get("annual_cost") or 10**12))
    current_tariffs = str(request.get("current_raw_rates") or "")
    payload = {
        "ok": True, "fuel": fuel, "usage": float(annual_usage),
        "annual_usage_kwh": float(annual_usage) if fuel == "ELECTRICITY" else None,
        "annual_usage_mj": float(annual_usage) if fuel == "GAS" else None,
        "annual_controlled_load_kwh": float(_d(request.get("annual_controlled_load_usage"), "0") or 0) if fuel == "ELECTRICITY" else 0,
        "customer_name": request.get("customer_name") or "Valued Customer",
        "customer_type": customer_type, "distributor": distributor,
        "tariff_preference": tariff_preference or None,
        "customer_has_solar": current_has_solar, "solar_filter_mode": "PRICE_WHEN_SUPPORTED",
        "customer_has_controlled_load": current_has_cl,
        "current_annual_baseline": _json_money(current_cost),
        "current_provider": request.get("current_provider") or "Current Provider",
        "current_plan_name": request.get("current_plan_name") or "",
        "current_daily_supply": request.get("current_daily_supply"),
        "current_avg_usage": request.get("current_avg_usage"),
        "current_raw_rates": current_tariffs, "current_tariffs": current_tariffs,
        "verified_plans": recommended_verified[:25], "single_rate_plans": recommended_verified[:25],
        "modelled_plans": recommended_modelled[:25], "eligibility_check_plans": recommended_eligibility[:25],
        "plan_lookup": lookup_rows[:300],
        "unpriceable_plans": needs_input[:100], "plans": selected_ui,
        "candidate_count": candidate_count, "excluded_candidate_count": excluded + len(needs_input),
        "classification_counts": classification_counts, "market_refresh": market_refresh,
        "seasonality": request.get("seasonality") or {},
        "message": (
            f"Compared {candidate_count} eligible cached {fuel.lower()} plans: "
            f"{len(verified)} verified, {len(modelled)} modelled, {len(eligibility_check)} eligibility-check, "
            f"{len(needs_input)} needing additional data."
        ),
    }
    return json.dumps(payload, separators=(",", ":"))


def compare_energy(
    db_path: str, fuel: str, postcode: str, distributor: str, usage: float,
    current_annual_cost: float = 0.0, tou_shares_json: str = "",
) -> str:
    # Backward-compatible v1 bridge. New code should call compare_energy_v2.
    req = {
        "fuel": fuel, "postcode": postcode, "distributor": distributor,
        "annual_usage": usage, "current_annual_cost": current_annual_cost if current_annual_cost and current_annual_cost > 0 else None,
        "tou_shares": tou_shares_json,
    }
    return compare_energy_v2(db_path, json.dumps(req))


# ---------------------------------------------------------------------------
# Banking CDR savings accounts + NBN Tracker public market data
# ---------------------------------------------------------------------------


def _market_module():
    import billbot_market
    return billbot_market


def _set_sync_state(con: sqlite3.Connection, key: str, value: str, when: Optional[str] = None) -> None:
    stamp = when or _now()
    con.execute("INSERT INTO sync_state(key,value,updated_at) VALUES(?,?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value,updated_at=excluded.updated_at", (key, str(value), stamp))


def _savings_market_fingerprint(con: sqlite3.Connection) -> str:
    h = hashlib.sha256()
    rows = con.execute(
        "SELECT holder_key,product_id,provider,product_name,raw_json FROM savings_products ORDER BY holder_key,product_id"
    ).fetchall()
    for row in rows:
        h.update("\x1f".join(str(row[k] or "") for k in row.keys()).encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()


def _nbn_market_fingerprint(con: sqlite3.Connection) -> str:
    h = hashlib.sha256()
    rows = con.execute(
        "SELECT provider,plan,speed_tier,monthly_price,promo_monthly_price,promo_months,url,source,provider_slug,category,technology,license,raw_json "
        "FROM nbn_offers ORDER BY provider,plan,speed_tier,source"
    ).fetchall()
    for row in rows:
        # compare_nbn uses raw description/notes only for the residential/business guard.
        # Include those ranking-relevant fields, but deliberately exclude cache/import timestamps
        # so an identical daily refresh does not invalidate a cached comparison.
        try:
            raw = json.loads(row["raw_json"] or "{}")
            description = str(raw.get("description") or "") if isinstance(raw, dict) else ""
            notes = str(raw.get("notes") or "") if isinstance(raw, dict) else ""
        except Exception:
            description = notes = ""
        stable = [str(row[k] if row[k] is not None else "") for k in row.keys() if k != "raw_json"]
        stable.extend((description, notes))
        h.update("\x1f".join(stable).encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()


def refresh_savings(db_path: str, progress_path: str = "") -> str:
    market = _market_module()
    reporter = _ProgressReporter(progress_path, 0, "savings")
    reporter.start("Discovering Banking CDR products")
    try:
        holders = market.discover_banking_public_endpoints()
    except Exception as exc:
        reporter.finish("failed", "Banking CDR discovery failed; cached products preserved")
        with _connect(db_path) as con:
            _schema(con); _set_sync_state(con, "savings_last_sync_status", "failed"); con.commit()
        return json.dumps({"ok": False, "status": "failed", "message": f"Banking CDR discovery failed: {exc}. Existing cache was preserved."})
    reporter.state["endpoints_total"] = len(holders); reporter._write()
    list_results: Dict[str, Tuple[Dict[str, str], Optional[List[Dict[str, Any]]], Optional[str]]] = {}
    def list_holder(holder: Dict[str, str]):
        try:
            products = market.list_savings_products(holder)
            return holder, products, None
        except Exception as exc:
            return holder, None, str(exc)[:400]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        futures = [ex.submit(list_holder, h) for h in holders]
        for fut in concurrent.futures.as_completed(futures):
            holder, products, error = fut.result(); key = _retailer_key(holder.get("base_uri", "")); list_results[key] = (holder, products, error)
            reporter.listed(holder.get("brand") or "Bank", len(products or []), 1)
    detail_jobs: List[Tuple[str, Dict[str, str], Dict[str, Any]]] = []
    for key,(holder,products,error) in list_results.items():
        if products is not None:
            detail_jobs.extend((key,holder,p) for p in products)
    reporter.state["details_total"] = len(detail_jobs); reporter._write()
    successful: Dict[str, List[Dict[str, Any]]] = {}; detail_failed_holders: set[str] = set(); detail_failures = 0
    def detail_one(job):
        key,holder,product=job; pid=str(product.get("productId") or ""); name=_compact(product.get("name") or pid)
        reporter.detail_started(holder.get("brand") or "Bank", name, pid)
        try:
            detail=market.get_savings_product_detail(product)
            if not detail: raise ValueError("empty product detail")
            return key,detail,None
        except Exception as exc:
            return key,None,str(exc)[:350]
        finally:
            reporter.detail_done(holder.get("brand") or "Bank", name, pid)
    with concurrent.futures.ThreadPoolExecutor(max_workers=10) as ex:
        futures=[ex.submit(detail_one,j) for j in detail_jobs]
        for fut in concurrent.futures.as_completed(futures):
            key,detail,error=fut.result()
            if detail: successful.setdefault(key,[]).append(detail)
            if error:
                detail_failed_holders.add(key)
                detail_failures += 1
    inserted=0; list_failures=sum(1 for _,p,e in list_results.values() if p is None)
    with _connect(db_path) as con:
        _schema(con)
        before_fingerprint = _savings_market_fingerprint(con)
        for key,(holder,products,error) in list_results.items():
            if products is None:
                _log(con,"WARN",f"{holder.get('brand')}: Banking CDR list failed; cached savings rows preserved: {error}")
                continue
            live_ids={str(p.get("productId") or "") for p in products if str(p.get("productId") or "")}
            for detail in successful.get(key,[]):
                pid=str(detail.get("productId") or ""); provider=str(detail.get("brandName") or holder.get("brand") or ""); name=str(detail.get("name") or "")
                if not pid: continue
                con.execute("INSERT INTO savings_products(holder_key,product_id,provider,product_name,raw_json,cached_at) VALUES(?,?,?,?,?,?) ON CONFLICT(holder_key,product_id) DO UPDATE SET provider=excluded.provider,product_name=excluded.product_name,raw_json=excluded.raw_json,cached_at=excluded.cached_at", (key,pid,provider,name,json.dumps(detail,separators=(",",":")),_now())); inserted+=1
            # A fully successful detail pass is needed before removing disappeared rows.
            if key not in detail_failed_holders:
                if live_ids:
                    marks=','.join('?' for _ in live_ids); con.execute(f"DELETE FROM savings_products WHERE holder_key=? AND product_id NOT IN ({marks})", [key,*sorted(live_ids)])
                else:
                    con.execute("DELETE FROM savings_products WHERE holder_key=?",(key,))
        after_fingerprint = _savings_market_fingerprint(con)
        market_changed = before_fingerprint != after_fingerprint
        status = (
            "failed" if not inserted else
            "partial" if list_failures > 0 or detail_failures > 0 else
            "success"
        )
        stamp=_now(); _set_sync_state(con,"savings_last_sync_status",status,stamp)
        if inserted: _set_sync_state(con,"savings_last_data_update",stamp,stamp)
        if market_changed: _state_bump(con,"savings_data_revision",stamp)
        con.commit(); _log(con,"INFO",f"Savings refresh {status}: {inserted} product details cached")
    message=(f"Banking CDR savings refresh {status}: {inserted} current product details cached from {len(holders)} data-holder endpoints; "
             f"{list_failures} list failure(s), {detail_failures} detail failure(s).")
    reporter.finish(status,message)
    return json.dumps({
        "ok": inserted > 0 and list_failures == 0 and detail_failures == 0,
        "complete": list_failures == 0 and detail_failures == 0,
        "status": status, "products": inserted, "holders": len(holders),
        "list_failures": list_failures, "detail_failures": detail_failures,
        "detail_failed_holders": len(detail_failed_holders), "message": message,
    })


def compare_savings(db_path: str) -> str:
    """Rank consumer savings accounts by published rates without assuming a user balance.

    BillBot intentionally does not calculate annual interest or silently choose a balance tier.
    Tier/applicability conditions are surfaced as text. Rates above 10% are excluded from the
    displayed ranking because they are almost certainly malformed/non-retail CDR values.
    """
    market = _market_module()
    with _connect(db_path) as con:
        _schema(con)
        rows = con.execute("SELECT raw_json FROM savings_products").fetchall()

    analysed: List[Dict[str, Any]] = []
    for row in rows:
        try:
            detail = json.loads(row["raw_json"] or "{}")
        except Exception:
            continue
        item = market.analyse_savings_product(detail)
        if item:
            analysed.append(item)

    def sane_rate(value: Any) -> bool:
        rate = _d(value, None)
        return rate is not None and Decimal("0") <= rate <= Decimal(str(SAVINGS_MAX_DISPLAY_RATE_PCT))

    ongoing_candidates = [x for x in analysed if sane_rate(x.get("ongoing_rate_pct"))]
    intro_candidates = [x for x in analysed if x.get("has_intro") and sane_rate(x.get("offer_rate_pct"))]

    def prefer_zero_fee(items: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        zero_fee = [x for x in items if float(x.get("periodic_fee") or 0) <= 0]
        return zero_fee or items

    ongoing_pool = prefer_zero_fee(ongoing_candidates)
    intro_pool = prefer_zero_fee(intro_candidates)
    ongoing = sorted(
        ongoing_pool,
        key=lambda x: (-float(x.get("ongoing_rate_pct") or 0), float(x.get("periodic_fee") or 0), _norm(x.get("brand")), _norm(x.get("name"))),
    )
    intro = sorted(
        intro_pool,
        key=lambda x: (-float(x.get("offer_rate_pct") or 0), float(x.get("periodic_fee") or 0), _norm(x.get("brand")), _norm(x.get("name"))),
    )
    visible_ids = {str(x.get("product_id") or "") for x in ongoing_candidates + intro_candidates}
    visible_count = len({x for x in visible_ids if x})
    over_cap = sum(
        1 for x in analysed
        if (x.get("ongoing_rate_pct") is not None and not sane_rate(x.get("ongoing_rate_pct")))
        or (x.get("offer_rate_pct") is not None and not sane_rate(x.get("offer_rate_pct")))
    )
    return json.dumps(
        {
            "ok": True,
            "product_count": visible_count,
            "ongoing": ongoing[:12],
            "introductory": intro[:12],
            "excluded_over_10_percent": over_cap,
            "message": (
                f"Ranked {visible_count} eligible savings accounts by advertised rate. "
                f"Rates above {SAVINGS_MAX_DISPLAY_RATE_PCT:g}% are excluded and balance-tier conditions are shown rather than assumed."
            ),
        },
        separators=(",", ":"),
    )


def import_nbn_offers(db_path: str, path: str) -> str:
    with open(path,"r",encoding="utf-8-sig") as f: payload=json.load(f)
    offers=payload.get("offers") if isinstance(payload,dict) else payload
    if not isinstance(offers,list): raise ValueError("NBN JSON must be an array or an object containing an 'offers' array")
    inserted=0
    with _connect(db_path) as con:
        _schema(con)
        before_fingerprint = _nbn_market_fingerprint(con)
        for raw in offers:
            if not isinstance(raw,dict): continue
            provider=_compact(raw.get("provider")); plan=_compact(raw.get("plan") or raw.get("plan_name")); tier=_compact(raw.get("speed_tier") or raw.get("tier")).upper(); monthly=_d(raw.get("monthly_price"),None)
            if not provider or not plan or not tier or monthly is None or monthly<=0: continue
            promo=_d(raw.get("promo_monthly_price"),None); promo_months=max(0,min(12,int(_d(raw.get("promo_months"),"0") or 0)))
            con.execute("""INSERT INTO nbn_offers(provider,plan,speed_tier,monthly_price,promo_monthly_price,promo_months,url,last_updated,imported_at,raw_json,source,category,technology,license)
            VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(provider,plan,speed_tier) DO UPDATE SET monthly_price=excluded.monthly_price,promo_monthly_price=excluded.promo_monthly_price,promo_months=excluded.promo_months,url=excluded.url,last_updated=excluded.last_updated,imported_at=excluded.imported_at,raw_json=excluded.raw_json,source=excluded.source,category=excluded.category,technology=excluded.technology,license=excluded.license""",
            (provider,plan,tier,float(monthly),float(promo) if promo is not None else None,promo_months,str(raw.get("url") or ""),str(raw.get("last_updated") or ""),_now(),json.dumps(raw,separators=(",",":")),"Local JSON fallback",str(raw.get("category") or "residential"),str(raw.get("technology") or "nbn"),"User supplied")); inserted+=1
        after_fingerprint = _nbn_market_fingerprint(con)
        if before_fingerprint != after_fingerprint:
            _state_bump(con,"nbn_data_revision")
        con.commit(); _log(con,"INFO",f"Imported {inserted} NBN offers from local JSON fallback")
    return json.dumps({"ok":True,"inserted":inserted,"message":f"Imported/updated {inserted} NBN fallback offers."})


def refresh_nbn(db_path: str, progress_path: str = "") -> str:
    market=_market_module(); reporter=_ProgressReporter(progress_path,1,"nbn"); reporter.start("Downloading NBN Tracker public data")
    try:
        providers,plans=market.fetch_nbntracker_data(); reporter.state.update({"stage":"Parsing NBN Tracker","query":"Filtering residential NBN plans","current":f"{len(plans)} published plans","percent":65}); reporter._write()
        live=[]
        for plan in plans:
            if not market.is_consumer_nbn_plan(plan) or str(plan.get("technology") or "nbn").lower()!="nbn" or str(plan.get("speed_tier") or "").upper() not in market.NBN_VALID_SPEED_TIERS: continue
            provider=providers.get(str(plan.get("provider_slug") or ""),{}); provider_name=str(provider.get("name") or plan.get("provider_slug") or "")
            if not provider_name: continue
            item=dict(plan); item["provider_name"]=provider_name; item["url"]=str(plan.get("cis_url") or provider.get("website_url") or ""); live.append(item)
        with _connect(db_path) as con:
            _schema(con); before_fingerprint = _nbn_market_fingerprint(con); live_keys=[]
            for item in live:
                provider=item["provider_name"]; name=str(item.get("name") or ""); tier=str(item.get("speed_tier") or "").upper(); monthly=_d(item.get("monthly_price"),None)
                if not name or not tier or monthly is None: continue
                live_keys.append((provider,name,tier)); promo=_d(item.get("promo_price"),None); months=max(0,min(12,int(item.get("promo_months") or 0)))
                con.execute("""INSERT INTO nbn_offers(provider,plan,speed_tier,monthly_price,promo_monthly_price,promo_months,url,last_updated,imported_at,raw_json,source,provider_slug,category,technology,license)
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(provider,plan,speed_tier) DO UPDATE SET monthly_price=excluded.monthly_price,promo_monthly_price=excluded.promo_monthly_price,promo_months=excluded.promo_months,url=excluded.url,last_updated=excluded.last_updated,imported_at=excluded.imported_at,raw_json=excluded.raw_json,source=excluded.source,provider_slug=excluded.provider_slug,category=excluded.category,technology=excluded.technology,license=excluded.license""",
                (provider,name,tier,float(monthly),float(promo) if promo is not None else None,months,item.get("url") or "",_now(),_now(),json.dumps(item,separators=(",",":")),"NBN Tracker",item.get("provider_slug") or "",item.get("category") or "residential",item.get("technology") or "nbn",market.NBN_LICENSE))
            # Source-scoped replacement keeps an optional user-imported fallback untouched.
            if live_keys:
                existing=con.execute("SELECT provider,plan,speed_tier FROM nbn_offers WHERE source='NBN Tracker'").fetchall(); live_set=set(live_keys)
                for row in existing:
                    key=(row["provider"],row["plan"],row["speed_tier"])
                    if key not in live_set: con.execute("DELETE FROM nbn_offers WHERE source='NBN Tracker' AND provider=? AND plan=? AND speed_tier=?",key)
            after_fingerprint = _nbn_market_fingerprint(con)
            stamp=_now(); _set_sync_state(con,"nbn_last_sync_status","success",stamp); _set_sync_state(con,"nbn_last_data_update",stamp,stamp)
            if before_fingerprint != after_fingerprint: _state_bump(con,"nbn_data_revision",stamp)
            con.commit(); _log(con,"INFO",f"NBN Tracker refresh success: {len(live)} consumer plans")
        message=f"NBN Tracker refresh complete: {len(live)} residential NBN plans cached."; reporter.finish("success",message)
        return json.dumps({"ok":True,"status":"success","plans":len(live),"message":message,"source":"NBN Tracker","license":market.NBN_LICENSE})
    except Exception as exc:
        with _connect(db_path) as con:
            _schema(con); _set_sync_state(con,"nbn_last_sync_status","failed"); con.commit(); _log(con,"WARN",f"NBN Tracker refresh failed; cache preserved: {exc}")
        reporter.finish("failed","NBN Tracker refresh failed; last-good cache preserved")
        return json.dumps({"ok":False,"status":"failed","message":f"NBN Tracker refresh failed: {exc}. Existing cache was preserved."})


def compare_nbn(db_path: str, speed_tier: str, current_monthly_cost: float = 0.0) -> str:
    market=_market_module(); tier=str(speed_tier).strip().upper(); current=_d(current_monthly_cost,None)
    with _connect(db_path) as con:
        _schema(con); rows=con.execute("SELECT * FROM nbn_offers WHERE UPPER(speed_tier)=?",(tier,)).fetchall()
    out=[]
    for r in rows:
        raw={}
        try: raw=json.loads(r["raw_json"] or "{}")
        except Exception: pass
        if str(r["source"] or "")=="NBN Tracker" and not market.is_consumer_nbn_plan(raw): continue
        months=max(0,min(12,int(r["promo_months"] or 0))); monthly=_d(r["monthly_price"],"0") or Decimal("0"); promo=_d(r["promo_monthly_price"],None) or monthly
        annual=Decimal(months)*promo+Decimal(12-months)*monthly
        ongoing_annual=Decimal("12")*monthly
        savings=current*Decimal("12")-annual if current is not None and current>0 else None
        ongoing_savings=current*Decimal("12")-ongoing_annual if current is not None and current>0 else None
        qualifies=months>=NBN_MIN_PROMO_MONTHS and promo<monthly
        has_intro=months>0 and promo<monthly
        out.append({"provider":r["provider"],"plan":r["plan"],"speed_tier":r["speed_tier"],"monthly_price":_json_money(monthly),"promo_monthly_price":_json_money(promo) if months else None,"promo_months":months,"annual_cost":_json_money(annual),"ongoing_annual_cost":_json_money(ongoing_annual),"savings":_json_money(savings),"ongoing_savings":_json_money(ongoing_savings),"url":r["url"] or "","source":r["source"] or "Local JSON","promo_qualifies_headline":qualifies,"has_intro":has_intro,"promo_text":f"${promo:.2f}/mo for {months} months, then ${monthly:.2f}/mo" if has_intro else ""})
    # NBN comparison columns are intentionally ranked by the monthly price shown to the user.
    # Annualised figures are still calculated for compatibility/savings metadata, but never drive order.
    out.sort(key=lambda x:(x["monthly_price"] or 10**12,x["provider"],x["plan"]))
    ongoing_offers=sorted(out,key=lambda x:(x["monthly_price"] or 10**12,x["provider"],x["plan"]))
    introductory_offers=sorted([x for x in out if x["has_intro"]],key=lambda x:(x["promo_monthly_price"] or 10**12,x["monthly_price"] or 10**12,x["provider"],x["plan"]))
    # Preserve the existing six-month headline rule for the leader while also exposing
    # all genuine introductory offers in the right-hand comparison column.
    ongoing=min(out,key=lambda x:(x["monthly_price"] or 10**12,x["annual_cost"] or 10**12),default=None)
    headline_promos=[x for x in out if x["promo_qualifies_headline"]]
    offer=min(headline_promos,key=lambda x:(x["promo_monthly_price"] or 10**12,x["annual_cost"] or 10**12,x["monthly_price"] or 10**12),default=None) or ongoing
    return json.dumps({"ok":True,"offers":out[:20],"ongoing_offers":ongoing_offers[:20],"introductory_offers":introductory_offers[:20],"ongoing_leader":ongoing,"offer_leader":offer,"minimum_headline_promo_months":NBN_MIN_PROMO_MONTHS,"message":f"Ranked {len(out)} {tier} consumer offers by monthly price. Ongoing and introductory views are separated; headline promos require at least {NBN_MIN_PROMO_MONTHS} months."},separators=(",",":"))


# ---------------------------------------------------------------------------
# Gemini bill extraction + deterministic BillBot normalisation
# ---------------------------------------------------------------------------


BILL_INLINE_PDF_MAX_BYTES = 20 * 1024 * 1024


def _bill_progress(path: str, percent: int, stage: str, detail: str = "") -> None:
    """Best-effort progress for the Android bill-analysis UI.

    The file is intentionally advisory only: failures to write progress must never break bill
    extraction. Atomic replacement prevents the Compose-side watcher reading partial JSON.
    """
    if not path:
        return
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as handle:
            json.dump({
                "percent": max(0, min(100, int(percent))),
                "stage": str(stage or "Analysing bill"),
                "detail": str(detail or ""),
                "updated_at": _now(),
            }, handle, separators=(",", ":"))
        os.replace(tmp, path)
    except Exception:
        pass


def _gemini_http_json(req: urllib.request.Request, timeout: int, operation: str) -> Dict[str, Any]:
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
            return json.loads(raw) if raw.strip() else {}
    except urllib.error.HTTPError as exc:
        try:
            body = exc.read().decode("utf-8", errors="replace")
        except Exception:
            body = ""
        detail = body[:1600].strip()
        if detail:
            try:
                parsed = json.loads(detail)
                detail = _compact(((parsed.get("error") or {}).get("message")) or detail)
            except Exception:
                pass
        raise RuntimeError(f"Gemini {operation} failed (HTTP {exc.code}){': ' + detail if detail else ''}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"Gemini {operation} network error: {exc.reason}") from exc
    except (TimeoutError, socket.timeout) as exc:
        raise RuntimeError(f"Gemini {operation} timed out. The request can be retried safely.") from exc



def _json_schema_to_openapi(value: Any) -> Any:
    """Convert BillBot's small JSON-Schema subset to the older Gemini OpenAPI Schema shape.

    Gemini's legacy responseSchema field does not accept JSON-Schema type arrays. This
    compatibility converter maps a nullable two-type union to OpenAPI ``nullable: true``
    and recursively preserves the object/array/enum structure used by bill extraction.
    """
    if isinstance(value, list):
        return [_json_schema_to_openapi(item) for item in value]
    if not isinstance(value, dict):
        return value
    out: Dict[str, Any] = {}
    for key, item in value.items():
        if key == "type" and isinstance(item, list):
            non_null = [entry for entry in item if str(entry).lower() != "null"]
            if len(non_null) == 1 and len(non_null) != len(item):
                out["type"] = non_null[0]
                out["nullable"] = True
            else:
                out["type"] = item[0] if item else "string"
            continue
        out[key] = _json_schema_to_openapi(item)
    return out

def _gemini_upload(path: str, api_key: str) -> Tuple[str, str]:
    size = os.path.getsize(path); mime = mimetypes.guess_type(path)[0] or "application/pdf"; name = os.path.basename(path)
    url = "https://generativelanguage.googleapis.com/upload/v1beta/files"
    metadata = json.dumps({"file": {"display_name": name}}).encode("utf-8")
    req = urllib.request.Request(url, data=metadata, method="POST", headers={
        "Content-Type": "application/json", "x-goog-api-key": api_key,
        "X-Goog-Upload-Protocol": "resumable", "X-Goog-Upload-Command": "start",
        "X-Goog-Upload-Header-Content-Length": str(size), "X-Goog-Upload-Header-Content-Type": mime, "User-Agent": USER_AGENT,
    })
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            upload_url = resp.headers.get("X-Goog-Upload-URL")
    except urllib.error.HTTPError as exc:
        try: body = exc.read().decode("utf-8", errors="replace")
        except Exception: body = ""
        try: detail = _compact(((json.loads(body).get("error") or {}).get("message")) or body)
        except Exception: detail = _compact(body)
        raise RuntimeError(f"Gemini file upload start failed (HTTP {exc.code}){': ' + detail[:1200] if detail else ''}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"Gemini file upload network error: {exc.reason}") from exc
    if not upload_url:
        raise RuntimeError("Gemini did not return an upload URL")
    with open(path, "rb") as f:
        data = f.read()
    req2 = urllib.request.Request(upload_url, data=data, method="POST", headers={
        "Content-Length": str(size), "X-Goog-Upload-Offset": "0", "X-Goog-Upload-Command": "upload, finalize",
        "Content-Type": mime, "User-Agent": USER_AGENT,
    })
    obj = _gemini_http_json(req2, 90, "file upload")
    file_obj = obj.get("file") or obj
    return str(file_obj.get("uri") or ""), str(file_obj.get("name") or "")


def _gemini_wait_active(file_name: str, api_key: str, timeout_seconds: int = 180, progress_path: str = "") -> Dict[str, Any]:
    """Wait until an uploaded Gemini File is ready for inference.

    Google can return uploaded PDFs in PROCESSING state. Calling generateContent before the
    file becomes ACTIVE produces an HTTP 400 even with a valid API key, so poll the Files API
    rather than treating that transient state as an authentication/upload failure.
    """
    if not file_name:
        raise RuntimeError("Gemini file upload returned no file name")
    deadline = time.monotonic() + max(5, int(timeout_seconds))
    started = time.monotonic()
    url = "https://generativelanguage.googleapis.com/v1beta/" + file_name.lstrip("/")
    while True:
        req = urllib.request.Request(url, method="GET", headers={"User-Agent": USER_AGENT, "x-goog-api-key": api_key})
        obj = _gemini_http_json(req, 30, "file processing check")
        state = str(obj.get("state") or "").upper()
        if state == "ACTIVE":
            _bill_progress(progress_path, 42, "Bill uploaded", "Gemini finished preparing the PDF")
            return obj
        if state == "FAILED":
            error = obj.get("error") or {}
            message = _compact(error.get("message") if isinstance(error, dict) else error)
            raise RuntimeError(f"Gemini file processing failed{': ' + message if message else ''}")
        if time.monotonic() >= deadline:
            raise RuntimeError(f"Gemini file processing timed out while state was {state or 'unknown'}")
        elapsed = max(0.0, time.monotonic() - started)
        fraction = min(1.0, elapsed / max(1.0, float(timeout_seconds)))
        _bill_progress(progress_path, 30 + int(10 * fraction), "Preparing uploaded PDF", f"Gemini file state: {state or 'PROCESSING'}")
        time.sleep(2)


def _gemini_delete(file_name: str, api_key: str) -> None:
    if not file_name:
        return
    url = "https://generativelanguage.googleapis.com/v1beta/" + file_name.lstrip("/")
    req = urllib.request.Request(url, method="DELETE", headers={"User-Agent": USER_AGENT, "x-goog-api-key": api_key})
    try:
        urllib.request.urlopen(req, timeout=15).close()
    except Exception:
        pass


def _prov(value: Any, confidence: str = "MEDIUM", source_text: Any = None, page: Any = None) -> Dict[str, Any]:
    return {"value": value, "page": page, "source_text": source_text, "parser_confidence": confidence}


def _rate_dollars_per_unit(rate: Any, unit: str) -> Optional[Decimal]:
    d = _d(rate, None)
    if d is None:
        return None
    u = str(unit or "").upper().replace(" ", "")
    if "C/" in u or u.startswith("C") or "CENT" in u:
        return d / CENTS
    # Gemini is instructed to preserve printed units. Values below 1 with missing units are most
    # commonly $/kWh or $/day; values above 1 are usually cents. This fallback is explicit.
    if not u and abs(d) > 1:
        return d / CENTS
    return d


def _normalise_charge_lines(raw_lines: Any) -> Tuple[List[Dict[str, Any]], Dict[str, List[Dict[str, Any]]]]:
    canonical: List[Dict[str, Any]] = []
    buckets = {"usage_lines": [], "supply_charge_lines": [], "controlled_load_lines": [], "demand_lines": [], "electricity_discount_credit_lines": []}
    for idx, line in enumerate(_as_list(raw_lines)):
        if not isinstance(line, dict):
            continue
        category = str(line.get("category") or "OTHER").upper()
        desc = _compact(line.get("description") or category)
        qty = _d(line.get("quantity"), None)
        rate = _d(line.get("unit_rate"), None)
        total = _d(line.get("line_total_inc_gst"), None)
        obj = {
            "category": _prov(category, "MEDIUM", desc), "description": _prov(desc, "MEDIUM", desc),
            "tariff_label": _prov(line.get("tariff_label"), "MEDIUM"), "time_band": _prov(line.get("time_band"), "MEDIUM"),
            "period_start": _prov(line.get("period_start"), "MEDIUM"), "period_end": _prov(line.get("period_end"), "MEDIUM"),
            "quantity": _prov(float(qty) if qty is not None else None, "MEDIUM"), "unit": _prov(line.get("unit"), "MEDIUM"),
            "unit_rate": _prov(float(rate) if rate is not None else None, "MEDIUM"), "rate_unit": _prov(line.get("rate_unit"), "MEDIUM"),
            "line_total_inc_gst": _prov(float(total) if total is not None else None, "MEDIUM"),
            "gst_included": _prov(True, "MEDIUM", "Bill charge amount as printed"), "is_credit": _prov(bool(line.get("is_credit")), "MEDIUM"),
            "line_index": idx,
        }
        canonical.append(obj)
        # More specific categories must win over generic words such as SUPPLY. For example
        # CONTROLLED_LOAD_SUPPLY belongs to the controlled-load register, not main supply.
        if "CONTROLLED" in category:
            bucket = "controlled_load_lines"
        elif "DEMAND" in category:
            bucket = "demand_lines"
        elif any(x in category for x in ("CREDIT", "DISCOUNT", "SOLAR", "FEED")) or bool(line.get("is_credit")):
            bucket = "electricity_discount_credit_lines"
        elif "SUPPLY" in category or "DAILY" in category or "SERVICE" in category:
            bucket = "supply_charge_lines"
        else:
            bucket = "usage_lines"
        buckets[bucket].append(obj)
    return canonical, buckets


def _sum_usage(lines: Sequence[Dict[str, Any]], units: Sequence[str]) -> Decimal:
    total = Decimal("0")
    for line in lines:
        unit = str(_field_value(line.get("unit"), "")).upper()
        qty = _d(_field_value(line.get("quantity")), None)
        if qty is not None and any(u in unit for u in units):
            total += qty
    return total


def _tou_shares_from_lines(lines: Sequence[Dict[str, Any]]) -> Dict[str, float]:
    totals: Dict[str, Decimal] = {}
    for line in lines:
        band = _norm(_field_value(line.get("time_band"), "") or _field_value(line.get("tariff_label"), "") or _field_value(line.get("description"), ""))
        qty = _d(_field_value(line.get("quantity")), None)
        unit = str(_field_value(line.get("unit"), "")).upper()
        if not band or qty is None or qty <= 0 or "KWH" not in unit:
            continue
        canonical = "offpeak" if "offpeak" in band else ("shoulder" if "shoulder" in band else ("peak" if "peak" in band else band))
        totals[canonical] = totals.get(canonical, Decimal("0")) + qty
    total = sum(totals.values(), Decimal("0"))
    if total <= 0 or len(totals) < 2:
        return {}
    return {k: float(v / total) for k, v in totals.items()}


def _current_rates_from_lines(buckets: Dict[str, List[Dict[str, Any]]], fuel: str,
                              annual_general: Optional[Decimal], annual_cl: Optional[Decimal],
                              bill_days: int = 0) -> Dict[str, Any]:
    days = Decimal(max(0, int(bill_days or 0)))
    usage_cost = Decimal("0"); usage_qty = Decimal("0"); raw_parts: List[str] = []
    fixed_period_cost = Decimal("0"); fixed_rate_fallback = Decimal("0")
    def signed_total(line: Dict[str, Any]) -> Optional[Decimal]:
        total = _d(_field_value(line.get("line_total_inc_gst")), None)
        if total is None: return None
        if bool(_field_value(line.get("is_credit"), False)) and total > 0: return -abs(total)
        return total
    # Main daily/service supply.
    for line in buckets["supply_charge_lines"]:
        total=signed_total(line)
        if total is not None: fixed_period_cost += total
        else:
            rate=_rate_dollars_per_unit(_field_value(line.get("unit_rate")),str(_field_value(line.get("rate_unit"),"")))
            if rate is not None: fixed_rate_fallback += rate
    for line in buckets["usage_lines"]:
        qty=_d(_field_value(line.get("quantity")),None); total=signed_total(line)
        unit=str(_field_value(line.get("unit"),"")).upper(); rate_unit=str(_field_value(line.get("rate_unit"),"")).upper()
        rate=_rate_dollars_per_unit(_field_value(line.get("unit_rate")),rate_unit); desc=_compact(_field_value(line.get("description"),"Usage"))
        if rate is not None: raw_parts.append(f"{desc}: {(rate*CENTS):.3f}c/{'MJ' if fuel == 'GAS' else 'kWh'}")
        energy_unit=("MJ" in unit) if fuel=="GAS" else ("KWH" in unit)
        if qty is not None and qty>0 and total is not None and energy_unit:
            usage_qty+=qty; usage_cost+=total
    effective=(usage_cost/usage_qty) if usage_qty>0 else None
    cl_qty=Decimal("0"); cl_cost=Decimal("0")
    for line in buckets["controlled_load_lines"]:
        qty=_d(_field_value(line.get("quantity")),None); total=signed_total(line); unit=str(_field_value(line.get("unit"),"")).upper(); rate_unit=str(_field_value(line.get("rate_unit"),"")).upper(); desc=_compact(_field_value(line.get("description"),"Controlled load"))
        is_energy="KWH" in unit or "KWH" in rate_unit
        is_daily="DAY" in unit or "DAY" in rate_unit or "SUPPLY" in str(_field_value(line.get("category"),"")).upper()
        if is_energy and qty is not None and qty>0 and total is not None:
            cl_qty+=qty; cl_cost+=total
            rate=_rate_dollars_per_unit(_field_value(line.get("unit_rate")),rate_unit)
            if rate is not None: raw_parts.append(f"{desc}: {(rate*CENTS):.3f}c/kWh")
        elif is_daily:
            if total is not None: fixed_period_cost += total
            else:
                rate=_rate_dollars_per_unit(_field_value(line.get("unit_rate")),rate_unit)
                if rate is not None: fixed_rate_fallback += rate
    # Demand and recurring bill credits/discounts affect the current-plan baseline too. With no
    # full demand history the most auditable baseline is their observed bill-period amount annualised.
    other_period_cost=Decimal("0")
    for key in ("demand_lines","electricity_discount_credit_lines"):
        for line in buckets[key]:
            total=signed_total(line)
            if total is not None: other_period_cost += total
    current_annual=None
    if annual_general is not None and annual_general>0 and effective is not None:
        current_annual=annual_general*effective
        if days>0: current_annual += (fixed_period_cost+other_period_cost)*DAYS_PER_YEAR/days
        else: current_annual += fixed_rate_fallback*DAYS_PER_YEAR
        if annual_cl is not None and annual_cl>0 and cl_qty>0: current_annual += annual_cl*cl_cost/cl_qty
    if days>0:
        daily_supply=(fixed_period_cost/days) if fixed_period_cost else (fixed_rate_fallback if fixed_rate_fallback else None)
    else: daily_supply=fixed_rate_fallback if fixed_rate_fallback else None
    return {"current_daily_supply":_json_number((daily_supply*CENTS) if daily_supply is not None else None,"0.001"),
            "current_avg_usage":_json_number((effective*CENTS) if effective is not None else None,"0.001"),
            "current_raw_rates":" | ".join(dict.fromkeys(raw_parts)),"annual_cost":current_annual,
            "annualised_other_charges":_json_money(other_period_cost*DAYS_PER_YEAR/days) if days>0 else None}

def _validate_extraction(ex: Dict[str, Any], buckets: Dict[str, List[Dict[str, Any]]], target: Optional[Decimal]) -> Dict[str, Any]:
    issues: List[Dict[str, Any]] = []
    def add(code: str, severity: str, message: str) -> None:
        issues.append({"code": code, "severity": severity, "message": message})
    fuel = str(_field_value(ex.get("fuel_type"), "UNKNOWN")).upper()
    if not _field_value(ex.get("distributor_name")):
        add("MISSING_DISTRIBUTOR", "HIGH", "Distributor/network is required for plan matching.")
    start = _parse_date(ex.get("billing_period_start")); end = _parse_date(ex.get("billing_period_end"))
    if not start or not end:
        add("MISSING_PERIOD", "HIGH", "Billing period dates were not extracted.")
    days = int(_d(_field_value(ex.get("bill_days")), "0") or 0)
    if days <= 0:
        add("INVALID_BILL_DAYS", "HIGH", "Bill days are missing or invalid.")
    usage = _d(_field_value(ex.get("total_usage_mj" if fuel == "GAS" else "total_usage_kwh")), "0") or Decimal("0")
    if usage <= 0:
        add("MISSING_USAGE", "HIGH", "Imported energy usage is missing or zero.")
    line_totals: List[Decimal] = []
    for bucket in buckets.values():
        for line in bucket:
            total = _d(_field_value(line.get("line_total_inc_gst")), None)
            if total is not None:
                is_credit = bool(_field_value(line.get("is_credit"), False))
                line_totals.append(-abs(total) if is_credit and total > 0 else total)
    reconciliation = None
    if target is not None and target != 0 and line_totals:
        reconstructed = sum(line_totals, Decimal("0")); delta = reconstructed - target
        tolerance = max(abs(target) * Decimal("0.005"), Decimal("0.05"))
        reconciliation = {
            "target": _json_money(target), "reconstructed": _json_money(reconstructed), "delta": _json_money(delta),
            "tolerance": _json_money(tolerance), "pass": abs(delta) <= tolerance,
            "method": "SIGNED_SUM_OF_CANONICAL_CHARGE_LINES",
        }
        if abs(delta) > tolerance:
            add("CHARGE_RECONCILIATION_FAILURE", "HIGH", "Printed current charges do not reconcile to extracted charge lines.")
    elif target is not None and target != 0 and not line_totals:
        add("NO_CHARGE_LINES", "HIGH", "No complete current charge-line totals were extracted, so the bill cannot be reconciled safely.")
    elif target is None and line_totals:
        add("MISSING_CURRENT_CHARGES", "HIGH", "The current energy-charge total was not extracted, so charge lines cannot be independently reconciled.")
    elif target is None and not line_totals:
        add("NO_CHARGE_LINES", "HIGH", "Current bill charges and complete charge lines were not extracted, so the bill cannot be reconciled safely.")
    high_blockers = {
        "MISSING_DISTRIBUTOR", "MISSING_PERIOD", "INVALID_BILL_DAYS", "MISSING_USAGE",
        "CHARGE_RECONCILIATION_FAILURE", "NO_CHARGE_LINES", "MISSING_CURRENT_CHARGES",
    }
    comparison_eligible = not any(x["code"] in high_blockers for x in issues)
    score = max(0, 100 - sum(25 if x["severity"] == "HIGH" else 8 for x in issues))
    return {
        "reconciliation": reconciliation,
        "validation": {"status": "PASS" if not issues else ("REVIEW_REQUIRED" if comparison_eligible else "FAIL"),
                       "quality_score": score, "comparison_eligible": comparison_eligible, "issues": issues, "repair_attempted": True},
    }


def _normalise_gemini_bill(raw: Dict[str, Any]) -> Dict[str, Any]:
    fuel = str(raw.get("fuel_type") or "UNKNOWN").upper()
    confidence = str(raw.get("confidence") or "MEDIUM").upper()
    raw_charge_lines = raw.get("charge_lines") if isinstance(raw.get("charge_lines"), list) else []
    canonical_lines, buckets = _normalise_charge_lines(raw_charge_lines)

    # Prefer the bill-level period, then repair missing dates deterministically from the charge
    # rows. This mirrors desktop BillBot's rule that period dates are not merely guessed for
    # annualisation. We retain the bill-level value when it exists and only fill genuine gaps.
    start = _parse_date(raw.get("billing_period_start"))
    end = _parse_date(raw.get("billing_period_end"))
    line_starts = [_parse_date(line.get("period_start")) for line in raw_charge_lines if isinstance(line, dict)]
    line_ends = [_parse_date(line.get("period_end")) for line in raw_charge_lines if isinstance(line, dict)]
    line_starts = [value for value in line_starts if value is not None]
    line_ends = [value for value in line_ends if value is not None]
    if start is None and line_starts:
        start = min(line_starts)
    if end is None and line_ends:
        end = max(line_ends)

    printed_days = int(_d(raw.get("bill_days"), "0") or 0)
    date_days = ((end - start).days + 1) if start and end and end >= start else 0
    days = printed_days or date_days
    # If the printed days and dates disagree materially, preserve the printed value but flag it
    # below. A one-day inclusive/exclusive convention difference is accepted.
    total_usage = _d(raw.get("total_usage_mj" if fuel == "GAS" else "total_usage_kwh"), None)
    general = _d(raw.get("general_usage_kwh"), None) if fuel == "ELECTRICITY" else total_usage
    cl = _d(raw.get("controlled_load_kwh"), "0") or Decimal("0")
    if fuel == "ELECTRICITY":
        line_general = _sum_usage(buckets["usage_lines"], ("KWH",))
        line_cl = _sum_usage(buckets["controlled_load_lines"], ("KWH",))
        if general is None or general <= 0:
            general = line_general if line_general > 0 else ((total_usage - cl) if total_usage is not None and total_usage > cl else total_usage)
        if cl <= 0 and line_cl > 0:
            cl = line_cl
        if total_usage is None or total_usage <= 0:
            total_usage = (general or Decimal("0")) + cl
    elif fuel == "GAS" and (total_usage is None or total_usage <= 0):
        total_usage = _sum_usage(buckets["usage_lines"], ("MJ",))
        general = total_usage

    service_address = str(raw.get("service_address") or "").strip()
    postcode = str(raw.get("service_postcode") or "").strip()
    if not postcode and service_address:
        matches = re.findall(r"(?<!\d)(\d{4})(?!\d)", service_address)
        if matches:
            postcode = matches[-1]

    state = str(raw.get("service_state") or "").strip().upper()
    if not state and service_address:
        state_match = re.search(r"\b(NSW|VIC|QLD|SA|WA|TAS|ACT|NT)\b", service_address.upper())
        if state_match:
            state = state_match.group(1)
    if not state and postcode:
        state = _state_from_postcode(postcode)
    if not state:
        distributor_key = re.sub(r"[^A-Z0-9]+", " ", str(raw.get("distributor_name") or "").upper()).strip()
        for network, network_state in DISTRIBUTOR_STATE_HINTS.items():
            if network in distributor_key:
                state = network_state
                break

    annual_general_info = annualise_usage(general, fuel, postcode, state, start, end, days)
    annual_general = _d(annual_general_info.get("annual_usage"), None)
    annual_cl = None
    if fuel == "ELECTRICITY" and cl > 0:
        # Until a controlled-load-specific AER shape is bundled, avoid claiming the general-load
        # profile is a CL profile. This matches BillBot's rule that registers stay separate.
        annual_cl = cl * DAYS_PER_YEAR / Decimal(days) if days > 0 else None
    solar = _d(raw.get("solar_export_kwh"), "0") or Decimal("0")
    solar_annual = solar * DAYS_PER_YEAR / Decimal(days) if solar > 0 and days > 0 else Decimal("0")
    current_rates = _current_rates_from_lines(buckets, fuel, annual_general, annual_cl, days)
    target_key = "total_new_gas_charges_inc_gst" if fuel == "GAS" else "total_new_electricity_charges_inc_gst"
    target = _d(raw.get(target_key), None)
    if target is None:
        target = _d(raw.get("current_bill_amount"), None)
    validation_pack: Dict[str, Any]

    ex: Dict[str, Any] = {
        "customer_name": _prov(raw.get("customer_name"), confidence),
        "customer_type": _prov(raw.get("customer_type"), confidence),
        "retailer_name": _prov(raw.get("retailer_name"), confidence),
        "distributor_name": _prov(raw.get("distributor_name"), confidence),
        "fuel_type": _prov(fuel, confidence),
        "billing_period_start": _prov(
            start.isoformat() if start else None, confidence,
            raw.get("billing_period_start") or ("earliest charge-line period_start" if line_starts else None),
        ),
        "billing_period_end": _prov(
            end.isoformat() if end else None, confidence,
            raw.get("billing_period_end") or ("latest charge-line period_end" if line_ends else None),
        ),
        "bill_days": _prov(days if days > 0 else None, confidence, raw.get("bill_days") or ("inclusive extracted period span" if date_days else None)),
        "service_address": _prov(raw.get("service_address"), confidence),
        "service_suburb": _prov(raw.get("service_suburb"), confidence),
        "service_state": _prov(state or None, confidence, raw.get("service_state") or (service_address if state and service_address else raw.get("distributor_name"))),
        "service_postcode": _prov(postcode or None, confidence, raw.get("service_postcode") or (service_address if postcode and service_address else None)),
        "nmi": _prov(raw.get("nmi"), confidence), "current_plan_name": _prov(raw.get("current_plan_name"), confidence),
        "current_plan_id": _prov(raw.get("current_plan_id"), confidence),
        "tariff_code": _prov(raw.get("tariff_code"), confidence), "meter_number": _prov(raw.get("meter_number"), confidence),
        "total_usage_kwh": _prov(float(total_usage) if fuel == "ELECTRICITY" and total_usage is not None else None, confidence),
        "general_usage_kwh": _prov(float(general) if fuel == "ELECTRICITY" and general is not None else None, confidence),
        "controlled_load_kwh": _prov(float(cl) if fuel == "ELECTRICITY" else 0.0, confidence),
        "solar_export_kwh": _prov(float(solar) if fuel == "ELECTRICITY" else 0.0, confidence),
        "total_usage_mj": _prov(float(total_usage) if fuel == "GAS" and total_usage is not None else None, confidence),
        "max_demand_kw": _prov(raw.get("max_demand_kw"), confidence),
        "solar_detected": _prov(bool(solar > 0), confidence), "controlled_load_detected": _prov(bool(cl > 0), confidence),
        "demand_detected": _prov(_d(raw.get("max_demand_kw"), "0") > 0, confidence),
        "usage_lines": buckets["usage_lines"], "supply_charge_lines": buckets["supply_charge_lines"],
        "controlled_load_lines": buckets["controlled_load_lines"], "demand_lines": buckets["demand_lines"],
        "electricity_discount_credit_lines": buckets["electricity_discount_credit_lines"], "charge_lines": canonical_lines,
        target_key: _prov(float(target) if target is not None else None, confidence),
        "amount_due": _prov(raw.get("amount_due"), confidence),
        "extraction_schema_version": 5, "llm_provider": "gemini", "llm_model": raw.get("_model"),
    }
    validation_pack = _validate_extraction(ex, buckets, target)
    if validation_pack["reconciliation"]:
        ex["reconciliation"] = validation_pack["reconciliation"]
    else:
        ex["reconciliation"] = {"target": _json_money(target) if target is not None else 0.0, "reconstructed": None, "delta": None, "tolerance": None, "pass": None, "method": "INSUFFICIENT_LINE_TOTALS"}
    ex["extraction_validation"] = validation_pack["validation"]
    if start and end and printed_days and date_days and abs(printed_days - date_days) > 1:
        ex["extraction_validation"]["issues"].append({"code": "DATE_DURATION_MISMATCH", "severity": "MEDIUM", "message": "Printed bill days do not match extracted period dates."})
        ex["extraction_validation"]["status"] = "REVIEW_REQUIRED" if ex["extraction_validation"]["comparison_eligible"] else "FAIL"
    ex["extraction_metadata"] = {
        "schema_version": 5, "provider": "gemini", "model": raw.get("_model"), "extracted_at": _now(),
        "structured_output_requested": True, "deterministic_repairs": ["dates", "bill_days", "usage_components", "annualisation", "reconciliation"],
    }

    annual_cost = current_rates.get("annual_cost")
    if annual_cost is None and target is not None and days > 0:
        annual_cost = target * DAYS_PER_YEAR / Decimal(days)
    return {
        "fuel_type": fuel, "customer_name": raw.get("customer_name"), "postcode": postcode,
        "state": state, "distributor": raw.get("distributor_name") or "", "retailer": raw.get("retailer_name") or "",
        "plan_name": raw.get("current_plan_name") or "", "current_plan_id": raw.get("current_plan_id") or "", "billing_period_start": start.isoformat() if start else None,
        "billing_period_end": end.isoformat() if end else None, "days": days or None,
        "usage_kwh": float(total_usage) if fuel == "ELECTRICITY" and total_usage is not None else None,
        "usage_mj": float(total_usage) if fuel == "GAS" and total_usage is not None else None,
        "annual_usage_kwh": _json_number(annual_general, "0.1") if fuel == "ELECTRICITY" else None,
        "annual_usage_mj": _json_number(annual_general, "0.1") if fuel == "GAS" else None,
        "annual_controlled_load_kwh": _json_number(annual_cl, "0.1") if annual_cl is not None else 0.0,
        "annual_solar_export_kwh": _json_number(solar_annual, "0.1") if fuel == "ELECTRICITY" else 0.0,
        "max_demand_kw": raw.get("max_demand_kw"), "annual_cost_estimate": _json_money(annual_cost),
        "current_daily_supply": current_rates.get("current_daily_supply"), "current_avg_usage": current_rates.get("current_avg_usage"),
        "current_raw_rates": current_rates.get("current_raw_rates") or "", "seasonality": annual_general_info,
        "tou_shares": _tou_shares_from_lines(buckets["usage_lines"]),
        "current_tariff_type": "TIME_OF_USE" if _tou_shares_from_lines(buckets["usage_lines"]) else "SINGLE_RATE",
        "confidence": confidence, "comparison_eligible": bool(ex["extraction_validation"]["comparison_eligible"]),
        "validation_status": ex["extraction_validation"]["status"], "extraction": ex,
    }


def extract_bill(path: str, api_key: str, model: str = "gemini-3.6-flash", progress_path: str = "") -> str:
    if not api_key.strip():
        raise ValueError("Gemini API key is required")
    if not os.path.isfile(path):
        raise FileNotFoundError(path)
    file_uri = file_name = ""
    try:
        size = os.path.getsize(path)
        mime = mimetypes.guess_type(path)[0] or "application/pdf"
        _bill_progress(progress_path, 3, "Reading bill", f"Preparing {max(1, size // 1024)} KB PDF")

        nullable_string = {"type": ["string", "null"]}
        nullable_number = {"type": ["number", "null"]}
        nullable_bool = {"type": ["boolean", "null"]}
        line_schema = {
            "type": "object", "properties": {
                "category": {"type": ["string", "null"]}, "description": nullable_string,
                "tariff_label": nullable_string, "time_band": nullable_string,
                "period_start": nullable_string, "period_end": nullable_string,
                "quantity": nullable_number, "unit": nullable_string, "unit_rate": nullable_number,
                "rate_unit": nullable_string, "line_total_inc_gst": nullable_number, "is_credit": nullable_bool,
            },
        }
        schema = {
            "type": "object", "properties": {
                "fuel_type": {"type": "string", "enum": ["ELECTRICITY", "GAS", "UNKNOWN"]},
                "customer_name": nullable_string, "customer_type": nullable_string,
                "retailer_name": nullable_string, "distributor_name": nullable_string,
                "billing_period_start": nullable_string, "billing_period_end": nullable_string, "bill_days": nullable_number,
                "service_address": nullable_string, "service_suburb": nullable_string, "service_state": nullable_string,
                "service_postcode": nullable_string, "nmi": nullable_string, "current_plan_name": nullable_string, "current_plan_id": nullable_string,
                "tariff_code": nullable_string, "meter_number": nullable_string,
                "total_usage_kwh": nullable_number, "general_usage_kwh": nullable_number, "controlled_load_kwh": nullable_number,
                "solar_export_kwh": nullable_number, "total_usage_mj": nullable_number, "max_demand_kw": nullable_number,
                "total_new_electricity_charges_inc_gst": nullable_number, "total_new_gas_charges_inc_gst": nullable_number,
                "current_bill_amount": nullable_number, "amount_due": nullable_number,
                "charge_lines": {"type": "array", "items": line_schema},
                "confidence": {"type": "string", "enum": ["HIGH", "MEDIUM", "LOW"]},
            }, "required": ["fuel_type", "confidence", "charge_lines"],
        }
        prompt = """
You are extracting an Australian retail electricity or gas bill for BillBot. Return only the requested JSON.
Be conservative: use null when a printed value cannot be supported. Never infer a distributor from postcode or NMI. Extract current_plan_id when an offer/plan ID is explicitly printed.
Dates should be YYYY-MM-DD when possible. Keep general electricity usage separate from controlled-load usage and solar export.
For charge_lines include CURRENT energy charge rows only (usage, supply, controlled load, demand, discounts/credits/solar), not payments,
opening balances, previous bills or account ledger transactions. line_total_inc_gst must be the signed printed line amount; credits should have
is_credit=true. unit_rate must preserve the printed magnitude and rate_unit must say $/kWh, c/kWh, $/day, c/day, $/MJ, c/MJ, $/kW/day etc.
Do not annualise anything and do not add GST. total_new_*_charges_inc_gst should be the current energy charges for the bill period, not amount due
when the account has prior balances or credits. The output will be deterministically reconciled and annualised by BillBot.
""".strip()

        # A bill is a one-shot document, so inline PDF input is both simpler and faster than the
        # Files API for ordinary bills: there is no resumable-upload handshake and no PROCESSING
        # state to poll. Keep a conservative Android-memory ceiling and retain the Files API for
        # unusually large PDFs. Google currently allows inline PDFs up to 50 MB; BillBot uses a
        # lower 20 MB cutoff to avoid excessive base64/JSON memory use on phones.
        if size <= BILL_INLINE_PDF_MAX_BYTES:
            _bill_progress(progress_path, 12, "Preparing PDF", "Encoding the bill securely for a one-time Gemini request")
            with open(path, "rb") as handle:
                encoded = base64.b64encode(handle.read()).decode("ascii")
            media_part: Dict[str, Any] = {"inline_data": {"mime_type": mime, "data": encoded}}
            _bill_progress(progress_path, 22, "Sending bill to Gemini", "PDF attached inline — no file-processing wait")
        else:
            _bill_progress(progress_path, 10, "Uploading bill", "Large PDF — starting Gemini Files upload")
            file_uri, file_name = _gemini_upload(path, api_key.strip())
            if not file_uri:
                raise RuntimeError("Gemini file upload returned no URI")
            _bill_progress(progress_path, 28, "Upload complete", "Waiting for Gemini to prepare the large PDF")
            _gemini_wait_active(file_name, api_key.strip(), progress_path=progress_path)
            media_part = {"file_data": {"mime_type": mime, "file_uri": file_uri}}

        contents = [{"parts": [{"text": prompt}, media_part]}]
        model_id = urllib.parse.quote(model.strip(), safe="-._")
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{model_id}:generateContent"
        headers = {"Content-Type": "application/json", "User-Agent": USER_AGENT, "x-goog-api-key": api_key.strip()}

        payloads = [
            {"contents": contents, "generationConfig": {
                "responseMimeType": "application/json", "responseJsonSchema": schema,
            }},
            {"contents": contents, "generationConfig": {
                "responseMimeType": "application/json", "responseSchema": _json_schema_to_openapi(schema),
            }},
            {"contents": contents, "generationConfig": {
                "responseFormat": {"text": {"mimeType": "application/json", "schema": schema}},
            }},
        ]
        request_shape_errors: List[str] = []
        response: Optional[Dict[str, Any]] = None
        for index, body in enumerate(payloads):
            _bill_progress(
                progress_path,
                48 if index == 0 else 52 + (index * 4),
                "Reading your bill",
                "Gemini is extracting usage, dates, rates and charges — this can take around a minute",
            )
            req = urllib.request.Request(url, data=json.dumps(body).encode("utf-8"), method="POST", headers=headers)
            try:
                response = _gemini_http_json(req, 120, "bill extraction")
                break
            except RuntimeError as exc:
                if "HTTP 400" not in str(exc):
                    raise
                request_shape_errors.append(str(exc))
                if index == len(payloads) - 1:
                    concise = " | ".join(request_shape_errors[-3:])
                    raise RuntimeError("Gemini rejected all supported structured-output request formats. " + concise) from exc
        if response is None:
            raise RuntimeError("Gemini bill extraction returned no response")

        _bill_progress(progress_path, 82, "Checking extraction", "Validating Gemini's structured response")
        candidates = response.get("candidates") or []
        if not candidates:
            feedback = response.get("promptFeedback") or {}
            raise RuntimeError(f"Gemini returned no candidate. {feedback}")
        parts = ((candidates[0].get("content") or {}).get("parts") or [])
        text = next((p.get("text") for p in parts if isinstance(p, dict) and p.get("text")), "{}")
        raw = json.loads(text)
        if not isinstance(raw, dict):
            raise RuntimeError("Gemini bill result was not a JSON object")
        raw["_model"] = model.strip()
        _bill_progress(progress_path, 90, "Validating bill", "Reconciling charge lines and annualising usage locally")
        result = _normalise_gemini_bill(raw)
        _bill_progress(progress_path, 100, "Bill ready", "BillBot validation complete")
        return json.dumps(result, separators=(",", ":"))
    finally:
        _gemini_delete(file_name, api_key.strip())

