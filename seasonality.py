"""Climate-normal seasonal annualisation for Australian residential energy usage.

This module deliberately does *not* claim to weather-normalise a customer's usage.
It uses the AER / Frontier Economics residential benchmark seasonal shape bundled with
BillBot.  The source benchmark is converted to seasonal shares by postcode climate zone
and state and then applied day-by-day to the exact observed billing period.

The calculation is deterministic and transparent:

    estimated annual usage = observed usage / expected annual share in observed dates

When more than one non-overlapping bill is supplied, the observations are pooled:

    estimated annual usage = sum(observed usage) / sum(expected annual shares)

That makes multiple bills progressively more informative without annualising each bill
separately and averaging the resulting estimates.
"""
from __future__ import annotations

import datetime as dt
import json
import os
from dataclasses import dataclass, asdict
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

DATA_PATH = os.path.join(os.path.dirname(__file__), "aer_seasonality_2021.json")
D365 = Decimal("365")
Q3 = Decimal("0.001")
Q2 = Decimal("0.01")

DISTRIBUTOR_STATE = {
    "JEMENA": "VIC", "CITIPOWER": "VIC", "CITYPOWER": "VIC", "POWERCOR": "VIC",
    "UNITED ENERGY": "VIC", "UNITEDENERGY": "VIC", "AUSNET": "VIC",
    "AUSGRID": "NSW", "ENDEAVOUR ENERGY": "NSW", "ESSENTIAL ENERGY": "NSW",
    "SA POWER NETWORKS": "SA", "SAPN": "SA",
    "ENERGEX": "QLD", "ERGON": "QLD", "ERGON ENERGY": "QLD",
    "TASNETWORKS": "TAS", "AURORA": "TAS",
    "EVOENERGY": "ACT", "ACTEWAGL": "ACT",
    "WESTERN POWER": "WA", "SYNERGY": "WA",
    "POWER AND WATER": "NT", "POWERWATER": "NT",
}

_STATE_RANGES = (
    # Match the postcode/state rules used by BillBot Android v1.4.46.
    ("ACT", 200, 299), ("ACT", 2600, 2618), ("ACT", 2900, 2920),
    ("NSW", 1000, 2599), ("NSW", 2619, 2899), ("NSW", 2921, 2999),
    ("VIC", 3000, 3999), ("VIC", 8000, 8999),
    ("QLD", 4000, 4999), ("QLD", 9000, 9999),
    ("SA", 5000, 5999), ("WA", 6000, 6999),
    ("TAS", 7000, 7999), ("NT", 800, 999),
)


@dataclass(frozen=True)
class UsageObservation:
    start: dt.date
    end: dt.date
    usage: Decimal
    label: str = "bill"

    @property
    def days(self) -> int:
        return (self.end - self.start).days + 1


@dataclass
class SeasonalityResult:
    adjusted_annual_usage: Decimal
    raw_annual_usage: Decimal
    seasonal_adjustment_factor: Decimal
    expected_profile_share: Optional[Decimal]
    observed_days: int
    observation_count: int
    profile_state: str
    climate_zone: Optional[str]
    location_basis: str
    confidence: str
    method: str
    source: str
    warnings: List[str]

    def to_dict(self) -> Dict[str, Any]:
        data = asdict(self)
        for key in (
            "adjusted_annual_usage", "raw_annual_usage", "seasonal_adjustment_factor",
            "expected_profile_share",
        ):
            value = data.get(key)
            if isinstance(value, Decimal):
                data[key] = float(value.quantize(Q3, rounding=ROUND_HALF_UP))
        return data


def _d(value: Any, default: Optional[Decimal] = None) -> Optional[Decimal]:
    try:
        if value in (None, ""):
            return default
        return Decimal(str(value))
    except (InvalidOperation, TypeError, ValueError):
        return default


def parse_date(value: Any) -> Optional[dt.date]:
    if isinstance(value, dt.datetime):
        return value.date()
    if isinstance(value, dt.date):
        return value
    text = str(value or "").strip()
    if not text:
        return None
    formats = (
        "%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%d %b %Y", "%d %B %Y",
        "%Y/%m/%d", "%d.%m.%Y",
    )
    for fmt in formats:
        try:
            return dt.datetime.strptime(text, fmt).date()
        except ValueError:
            pass
    return None


def state_from_postcode(postcode: Any) -> str:
    text = "".join(ch for ch in str(postcode or "") if ch.isdigit())
    if len(text) != 4:
        return ""
    pc = int(text)
    for state, lo, hi in _STATE_RANGES:
        if lo <= pc <= hi:
            return state
    return ""


def state_from_distributor(distributor: Any) -> str:
    value = " ".join(str(distributor or "").upper().replace("-", " ").split())
    for marker, state in DISTRIBUTOR_STATE.items():
        if marker in value:
            return state
    return ""


def _load_profiles(path: str = DATA_PATH) -> Dict[str, Any]:
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def _normalise_profile(raw: Any) -> Optional[List[Decimal]]:
    if not isinstance(raw, list) or len(raw) != 4:
        return None
    vals = [_d(x) for x in raw]
    if any(x is None or x <= 0 for x in vals):
        return None
    total = sum(vals, Decimal("0"))
    if total <= 0:
        return None
    return [x / total for x in vals]  # type: ignore[operator]


def _profile_for(
    postcode: str = "", state: str = "", distributor: str = "", fuel: str = "ELECTRICITY",
    path: str = DATA_PATH,
) -> Tuple[Optional[List[Decimal]], str, Optional[str], str]:
    payload = _load_profiles(path)
    explicit_state = str(state or "").upper().strip()
    pc_state = state_from_postcode(postcode)
    inferred_state = state_from_distributor(distributor)
    resolved_state = explicit_state or pc_state or inferred_state
    basis = "confirmed_state" if explicit_state else "postcode" if pc_state else "distributor_inferred" if inferred_state else "unknown"

    fuel = str(fuel or "ELECTRICITY").upper()
    climate_zone = None
    raw = None
    if fuel == "GAS":
        raw = (payload.get("gas") or {}).get(resolved_state)
    else:
        climate_zone = (payload.get("postcode_climate_zone") or {}).get(str(postcode).zfill(4)) if postcode else None
        if climate_zone is not None:
            zone_data = (payload.get("electricity") or {}).get(str(climate_zone), {})
            raw = zone_data.get(resolved_state) or zone_data.get("ALL")
        if raw is None and resolved_state:
            # Conservative fallback: average every climate-zone profile available for the state.
            candidates = []
            for zone_data in (payload.get("electricity") or {}).values():
                if not isinstance(zone_data, dict):
                    continue
                candidate = _normalise_profile(zone_data.get(resolved_state))
                if candidate:
                    candidates.append(candidate)
            if candidates:
                raw = [sum(row[i] for row in candidates) / Decimal(len(candidates)) for i in range(4)]
                basis = basis + "+state_average"

    return _normalise_profile(raw), resolved_state, str(climate_zone) if climate_zone is not None else None, basis


def _season_index(day: dt.date) -> int:
    month = day.month
    if month in (12, 1, 2):
        return 0  # summer
    if month in (3, 4, 5):
        return 1  # autumn
    if month in (6, 7, 8):
        return 2  # winter
    return 3      # spring


def _season_days(day: dt.date) -> int:
    """Return days in the actual Australian season containing ``day``.

    This mirrors Android v1.4.46 and correctly handles summers which cross a leap-year
    boundary (for example December 2027 to February 2028).
    """
    idx = _season_index(day)
    if idx == 0:
        season_start = dt.date(day.year if day.month == 12 else day.year - 1, 12, 1)
        season_end = dt.date(season_start.year + 1, 3, 1)
    elif idx == 1:
        season_start, season_end = dt.date(day.year, 3, 1), dt.date(day.year, 6, 1)
    elif idx == 2:
        season_start, season_end = dt.date(day.year, 6, 1), dt.date(day.year, 9, 1)
    else:
        season_start, season_end = dt.date(day.year, 9, 1), dt.date(day.year, 12, 1)
    return (season_end - season_start).days


def expected_share(start: dt.date, end: dt.date, profile: Sequence[Decimal]) -> Decimal:
    """Return the fraction of a climate-normal annual profile represented by inclusive dates."""
    if end < start:
        raise ValueError("end must not be before start")
    total = Decimal("0")
    day = start
    while day <= end:
        season = _season_index(day)
        total += profile[season] / Decimal(_season_days(day))
        day += dt.timedelta(days=1)
    return total


def _dedupe_observations(observations: Iterable[UsageObservation]) -> Tuple[List[UsageObservation], List[str]]:
    """Keep a deterministic non-overlapping set without silently preferring a larger duplicate.

    Exact-period duplicates keep the first observation supplied (the caller supplies the latest
    bill first). Conflicting usage for the same dates is explicitly warned. Partial overlaps then
    prefer the longer observation because it contributes more independent seasonal coverage.
    """
    warnings: List[str] = []
    by_period: Dict[Tuple[dt.date, dt.date], UsageObservation] = {}
    for obs in observations:
        key = (obs.start, obs.end)
        existing = by_period.get(key)
        if existing is None:
            by_period[key] = obs
            continue
        if existing.usage > 0:
            delta = abs(obs.usage - existing.usage) / existing.usage
            if delta > Decimal("0.01"):
                warnings.append(
                    f"Conflicting usage for duplicate period {obs.start.isoformat()}–{obs.end.isoformat()}; "
                    f"kept the first observation ({existing.label})."
                )
        else:
            warnings.append(f"Ignored duplicate observation {obs.start.isoformat()}–{obs.end.isoformat()}.")

    ranked = sorted(by_period.values(), key=lambda x: (x.days, x.end), reverse=True)
    accepted: List[UsageObservation] = []
    for obs in ranked:
        overlaps = any(not (obs.end < other.start or obs.start > other.end) for other in accepted)
        if overlaps:
            warnings.append(f"Ignored overlapping observation {obs.start.isoformat()}–{obs.end.isoformat()} ({obs.label}).")
            continue
        accepted.append(obs)
    accepted.sort(key=lambda x: x.start)
    return accepted, warnings


def estimate_from_observations(
    observations: Iterable[Dict[str, Any] | UsageObservation], *, postcode: str = "", state: str = "",
    distributor: str = "", fuel: str = "ELECTRICITY", profiles_path: str = DATA_PATH,
) -> SeasonalityResult:
    parsed: List[UsageObservation] = []
    warnings: List[str] = []
    for item in observations:
        if isinstance(item, UsageObservation):
            obs = item
        else:
            start = parse_date(item.get("start") or item.get("billing_period_start"))
            end = parse_date(item.get("end") or item.get("billing_period_end"))
            usage = _d(item.get("usage") if "usage" in item else item.get("kwh"))
            if not start or not end or usage is None or usage <= 0 or end < start:
                warnings.append("Ignored an observation with invalid dates or usage.")
                continue
            label = str(item.get("label") or "bill")
            stated_days = _d(item.get("bill_days") if item.get("bill_days") is not None else item.get("days"))
            if stated_days is not None and stated_days > 0 and stated_days == stated_days.to_integral_value():
                day_count = int(stated_days)
                calendar_days = (end - start).days + 1
                # Mirror Android's bill-day convention: if a provider prints an exclusive period
                # end (end-start == bill_days), use exactly bill_days from the start date. Never
                # extend beyond the source end date when bill_days conflicts with the date span.
                if day_count <= calendar_days:
                    effective_end = start + dt.timedelta(days=day_count - 1)
                    if day_count != calendar_days:
                        warnings.append(
                            f"{label} dates span {calendar_days} inclusive days but the bill states {day_count}; "
                            f"used the stated {day_count} days from the period start."
                        )
                    end = effective_end
                elif day_count > calendar_days:
                    warnings.append(
                        f"{label} states {day_count} days but its dates span only {calendar_days}; "
                        "used the source date span rather than extending beyond the bill."
                    )
            obs = UsageObservation(start, end, usage, label)
        if obs.usage > 0 and obs.end >= obs.start:
            parsed.append(obs)

    parsed, overlap_warnings = _dedupe_observations(parsed)
    warnings.extend(overlap_warnings)
    if not parsed:
        raise ValueError("At least one valid dated usage observation is required.")

    total_usage = sum((o.usage for o in parsed), Decimal("0"))
    total_days = sum(o.days for o in parsed)
    raw_annual = (total_usage / Decimal(total_days)) * D365
    profile, resolved_state, climate_zone, location_basis = _profile_for(
        postcode=postcode, state=state, distributor=distributor, fuel=fuel, path=profiles_path,
    )

    source = "AER / Frontier Economics residential energy consumption benchmarks (Dec 2020; postcode climate mapping Jun 2021)"
    if profile:
        share = sum((expected_share(o.start, o.end, profile) for o in parsed), Decimal("0"))
        if share <= 0:
            adjusted = raw_annual
            factor = Decimal("1")
            method = "elapsed_day_fallback"
            confidence = "LOW"
            warnings.append("Seasonal profile produced a non-positive observed share; used elapsed-day annualisation.")
        else:
            adjusted = total_usage / share
            factor = adjusted / raw_annual if raw_annual > 0 else Decimal("1")
            method = "aer_climate_normal_exact_date"
            # Near-annual coverage naturally produces a factor close to 1; still run the profile
            # so multi-bill observations spread across more than one year cannot bypass seasonality.
            if location_basis.startswith("postcode") and total_days >= 56:
                confidence = "HIGH"
            elif resolved_state and total_days >= 28:
                confidence = "MEDIUM"
            else:
                confidence = "LOW"
    else:
        share = None
        adjusted = raw_annual
        factor = Decimal("1")
        method = "elapsed_day_fallback"
        confidence = "LOW"
        warnings.append("No matching AER seasonal profile was available; used elapsed-day annualisation.")

    # Clamp only patently implausible *adjustment factors* caused by malformed inputs/profile lookup.
    # Normal AER factors remain untouched; this is a safety rail, not a modelling assumption.
    if factor < Decimal("0.45") or factor > Decimal("2.20"):
        warnings.append(f"Seasonal factor {factor:.3f} was outside the safety range; used raw annualisation instead.")
        adjusted, factor, share, method, confidence = raw_annual, Decimal("1"), None, "elapsed_day_safety_fallback", "LOW"

    return SeasonalityResult(
        adjusted_annual_usage=adjusted,
        raw_annual_usage=raw_annual,
        seasonal_adjustment_factor=factor,
        expected_profile_share=share,
        observed_days=total_days,
        observation_count=len(parsed),
        profile_state=resolved_state or "UNKNOWN",
        climate_zone=climate_zone,
        location_basis=location_basis,
        confidence=confidence,
        method=method,
        source=source,
        warnings=warnings,
    )


def estimate_annual_usage(
    usage_kwh: Any, billing_period_start: Any, billing_period_end: Any, *, postcode: str = "",
    state: str = "", distributor: str = "", fuel: str = "ELECTRICITY",
) -> SeasonalityResult:
    return estimate_from_observations(
        [{"start": billing_period_start, "end": billing_period_end, "usage": usage_kwh}],
        postcode=postcode, state=state, distributor=distributor, fuel=fuel,
    )
