"""Privacy-minimised diagnostics and output reasonableness checks for BillBot.

The diagnostic log deliberately excludes raw bill text, customer names, email addresses,
service addresses, account/NMI identifiers and attachment contents.  It records only the
pipeline stage, exception/anomaly code, non-identifying numeric summaries, market snapshot
metadata and a random run id.
"""
from __future__ import annotations

import datetime as dt
import json
import math
import os
import threading
import traceback
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional

_DEFAULT_LOG_DIR = os.environ.get("BILLBOT_LOG_DIR", "") or str(Path.cwd() / "logs")
_LOCK = threading.Lock()


def _utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def _finite_number(value: Any) -> Optional[float]:
    try:
        out = float(value)
    except (TypeError, ValueError):
        return None
    return out if math.isfinite(out) else None


def _safe_details(details: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    """Keep only diagnostic-safe scalar/list/dict values and cap long strings."""
    if not isinstance(details, dict):
        return {}
    blocked = {
        "customer_name", "email", "customer_email", "address", "service_address",
        "nmi", "account", "account_number", "raw_email", "bill_text", "pdf_text",
        "attachment_text", "source_text",
    }

    def clean(value: Any, depth: int = 0) -> Any:
        if depth > 3:
            return "<truncated>"
        if value is None or isinstance(value, (bool, int, float)):
            return value
        if isinstance(value, str):
            return value[:300]
        if isinstance(value, (list, tuple)):
            return [clean(x, depth + 1) for x in list(value)[:20]]
        if isinstance(value, dict):
            return {
                str(k): clean(v, depth + 1)
                for k, v in list(value.items())[:30]
                if str(k).lower() not in blocked
            }
        return str(value)[:300]

    return {str(k): clean(v) for k, v in details.items() if str(k).lower() not in blocked}


def log_path(log_dir: Optional[str] = None) -> Path:
    root = Path(log_dir or os.environ.get("BILLBOT_LOG_DIR") or _DEFAULT_LOG_DIR)
    root.mkdir(parents=True, exist_ok=True)
    return root / "billbot-error-log.jsonl"


def append_log(entry: Dict[str, Any], log_dir: Optional[str] = None) -> None:
    path = log_path(log_dir)
    line = json.dumps(entry, separators=(",", ":"), ensure_ascii=False)
    with _LOCK:
        with path.open("a", encoding="utf-8") as handle:
            handle.write(line + "\n")


def read_log(*, run_id: str = "", limit: int = 100, log_dir: Optional[str] = None) -> List[Dict[str, Any]]:
    path = log_path(log_dir)
    if not path.exists():
        return []
    limit = max(1, min(int(limit), 500))
    rows: List[Dict[str, Any]] = []
    with path.open("r", encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                item = json.loads(line)
            except Exception:
                continue
            if run_id and str(item.get("run_id") or "") != run_id:
                continue
            rows.append(item)
    return rows[-limit:]


@dataclass
class DiagnosticRecorder:
    run_id: str = field(default_factory=lambda: uuid.uuid4().hex)
    entries: List[Dict[str, Any]] = field(default_factory=list)
    log_dir: Optional[str] = None

    def record(
        self,
        level: str,
        code: str,
        stage: str,
        message: str,
        details: Optional[Dict[str, Any]] = None,
        *,
        write: bool = True,
    ) -> Dict[str, Any]:
        entry = {
            "timestamp": _utc_now(),
            "run_id": self.run_id,
            "level": str(level).upper(),
            "code": str(code),
            "stage": str(stage),
            "message": str(message)[:1000],
            "details": _safe_details(details),
        }
        self.entries.append(entry)
        if write and entry["level"] in {"WARNING", "ERROR"}:
            append_log(entry, self.log_dir)
        return entry

    def warning(self, code: str, stage: str, message: str, details: Optional[Dict[str, Any]] = None) -> None:
        self.record("WARNING", code, stage, message, details)

    def error(self, code: str, stage: str, message: str, details: Optional[Dict[str, Any]] = None) -> None:
        self.record("ERROR", code, stage, message, details)

    def exception(self, code: str, stage: str, exc: BaseException, details: Optional[Dict[str, Any]] = None) -> None:
        safe = dict(details or {})
        safe.update({
            "exception_type": type(exc).__name__,
            "traceback_tail": traceback.format_exc(limit=8)[-4000:],
        })
        self.error(code, stage, str(exc) or type(exc).__name__, safe)

    @property
    def warnings(self) -> List[Dict[str, Any]]:
        return [x for x in self.entries if x.get("level") == "WARNING"]

    @property
    def errors(self) -> List[Dict[str, Any]]:
        return [x for x in self.entries if x.get("level") == "ERROR"]

    def summary(self) -> Dict[str, Any]:
        status = "FAIL" if self.errors else "WARN" if self.warnings else "PASS"
        return {
            "run_id": self.run_id,
            "status": status,
            "warning_count": len(self.warnings),
            "error_count": len(self.errors),
            "log_file": str(log_path(self.log_dir)),
            "issues": [
                {k: x.get(k) for k in ("level", "code", "stage", "message", "details")}
                for x in self.entries
                if x.get("level") in {"WARNING", "ERROR"}
            ],
        }


class BillBotComparisonError(ValueError):
    def __init__(self, message: str, run_id: str = ""):
        super().__init__(message)
        self.run_id = run_id


def _warn_if(rec: DiagnosticRecorder, condition: bool, code: str, stage: str, message: str, details: Dict[str, Any]) -> None:
    if condition:
        rec.warning(code, stage, message, details)


def sense_check_result(result: Dict[str, Any], recorder: DiagnosticRecorder) -> Dict[str, Any]:
    """Deterministic final sanity checks. Suspicious values are logged, never silently hidden."""
    bill = result.get("bill") or {}
    season = result.get("seasonality") or {}
    current = result.get("current") or {}
    plans = result.get("top_plans") or []
    market = result.get("market") or {}

    usage = _finite_number(bill.get("general_usage_kwh"))
    days = _finite_number(bill.get("bill_days"))
    annual = _finite_number(season.get("adjusted_annual_usage"))
    raw_annual = _finite_number(season.get("raw_annual_usage"))
    factor = _finite_number(season.get("seasonal_adjustment_factor"))
    current_cost = _finite_number(current.get("annual_comparable_cost"))

    _warn_if(recorder, usage is None or usage <= 0, "NON_POSITIVE_USAGE", "sense_check", "General electricity usage is missing or non-positive.", {"usage_kwh": usage})
    _warn_if(recorder, days is None or days < 1 or days > 370, "UNUSUAL_BILL_DAYS", "sense_check", "Billing-period day count is outside the expected range.", {"bill_days": days})
    _warn_if(recorder, annual is None or annual <= 0, "NON_POSITIVE_ANNUAL_USAGE", "sense_check", "Annualised usage is missing or non-positive.", {"annual_usage_kwh": annual})
    _warn_if(recorder, annual is not None and (annual < 250 or annual > 60000), "UNUSUAL_ANNUAL_USAGE", "sense_check", "Annual electricity usage is unusually low or high for a residential comparison; verify extraction and premises type.", {"annual_usage_kwh": annual})
    _warn_if(recorder, factor is None or factor < 0.60 or factor > 1.80, "UNUSUAL_SEASONAL_FACTOR", "sense_check", "Seasonal adjustment factor is unusually large; verify dates, postcode and usage extraction.", {"seasonal_factor": factor, "raw_annual_kwh": raw_annual, "adjusted_annual_kwh": annual})
    _warn_if(recorder, current_cost is not None and (current_cost < 100 or current_cost > 20000), "UNUSUAL_CURRENT_COST", "sense_check", "Current comparable annual cost looks unusual; verify rates and units.", {"current_annual_cost": current_cost})

    costs: List[float] = []
    for index, plan in enumerate(plans, start=1):
        cost = _finite_number(plan.get("annual_cost"))
        saving = _finite_number(plan.get("savings"))
        if cost is None or cost <= 0:
            recorder.warning("INVALID_PLAN_COST", "sense_check", "A ranked plan has a missing or non-positive annual cost.", {"rank": index, "annual_cost": cost, "plan_id": plan.get("plan_id")})
            continue
        costs.append(cost)
        if cost < 100 or cost > 20000:
            recorder.warning("UNUSUAL_PLAN_COST", "sense_check", "A ranked plan annual cost is outside a broad residential plausibility range.", {"rank": index, "annual_cost": cost, "plan_id": plan.get("plan_id")})
        if current_cost is not None and saving is not None:
            expected = current_cost - cost
            if abs(expected - saving) > max(1.0, abs(expected) * 0.005):
                recorder.warning("SAVINGS_ARITHMETIC_MISMATCH", "sense_check", "Reported savings do not reconcile with current annual cost minus candidate annual cost.", {"rank": index, "annual_cost": cost, "reported_savings": saving, "expected_savings": expected, "plan_id": plan.get("plan_id")})

    if costs and costs != sorted(costs):
        recorder.error("TOP_PLANS_NOT_SORTED", "sense_check", "Top plans are not sorted by ascending annual cost.", {"costs": costs[:20]})
    if len(plans) == 0:
        recorder.warning("NO_RANKED_PLANS", "sense_check", "No priceable plans were returned after filtering.", {"candidate_count": market.get("candidate_count")})
    candidate_count = market.get("candidate_count")
    try:
        if candidate_count is not None and int(candidate_count) < len(plans):
            recorder.error("CANDIDATE_COUNT_MISMATCH", "sense_check", "Ranked plan count exceeds reported candidate count.", {"candidate_count": candidate_count, "ranked_count": len(plans)})
    except Exception:
        recorder.warning("INVALID_CANDIDATE_COUNT", "sense_check", "Market candidate count was not a valid integer.", {"candidate_count": candidate_count})

    status = "FAIL" if recorder.errors else "WARN" if recorder.warnings else "PASS"
    return {
        "status": status,
        "summary": (
            "Deterministic sense check found blocking errors; do not present rankings as reliable."
            if status == "FAIL" else
            "Deterministic sense check found warnings; present them and verify suspicious inputs/results."
            if status == "WARN" else
            "Deterministic sense check passed."
        ),
        "llm_final_review_required": True,
        "llm_checklist": [
            "Confirm the extracted billing dates, usage kWh, postcode/distributor and tariff units are internally plausible.",
            "Confirm annual usage is plausible relative to the observed bill period and seasonal factor.",
            "Confirm plan costs are positive, sorted lowest-to-highest, and savings equal current comparable annual cost minus plan annual cost.",
            "Check that no result is being described as more certain than its BillBot confidence/classification supports.",
            "If anything looks inconsistent, implausible or contradictory, tell the user and inspect the BillBot diagnostic log for this run_id rather than silently correcting BillBot's output.",
        ],
    }
