"""Validation and deterministic normalisation of host-LLM bill extraction."""
from __future__ import annotations

import json
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from typing import Any, Dict, Iterable, List, Optional, Tuple

from seasonality import estimate_from_observations, parse_date, state_from_distributor, state_from_postcode

MONEY_Q = Decimal("0.01")


def _d(value: Any, default: Decimal = Decimal("0")) -> Decimal:
    try:
        if value in (None, ""):
            return default
        return Decimal(str(value))
    except (InvalidOperation, TypeError, ValueError):
        return default


def _lines(payload: Dict[str, Any], key: str) -> List[Dict[str, Any]]:
    value = payload.get(key) or []
    return [dict(x) for x in value if isinstance(x, dict)] if isinstance(value, list) else []


def _line_usage(lines: Iterable[Dict[str, Any]]) -> Decimal:
    return sum((_d(x.get("kwh")) for x in lines), Decimal("0"))


def _line_total(lines: Iterable[Dict[str, Any]], rate_field: str = "unit_rate_cents") -> Decimal:
    total = Decimal("0")
    for line in lines:
        line_total = _d(line.get("line_total_dollars"), Decimal("-1"))
        if line_total >= 0:
            total += line_total
            continue
        qty = _d(line.get("kwh"))
        rate = _d(line.get(rate_field))
        if qty > 0 and rate >= 0:
            total += qty * rate / Decimal("100")
    return total


def _effective_cents(lines: List[Dict[str, Any]]) -> Optional[Decimal]:
    qty = _line_usage(lines)
    total = _line_total(lines)
    if qty > 0 and total >= 0:
        return (total / qty) * Decimal("100")
    rates = [_d(x.get("unit_rate_cents"), Decimal("-1")) for x in lines]
    rates = [x for x in rates if x >= 0]
    if len(rates) == 1:
        return rates[0]
    return None


def _supply_daily_cents(lines: List[Dict[str, Any]], bill_days: int) -> Optional[Decimal]:
    """Return a day-weighted effective supply rate across every supported supply row.

    Some bills expose line totals for one tariff period and only a published c/day rate for
    another. Treating those groups separately and returning only the line-total subset biases
    the annual baseline. Convert each usable row to c/day first, then weight all rows by days.
    """
    weighted_cents = Decimal("0")
    weighted_days = Decimal("0")
    fallback_rates: List[Decimal] = []
    for line in lines:
        days = _d(line.get("days"))
        rate = _d(line.get("unit_rate_cents_per_day"), Decimal("-1"))
        total = _d(line.get("line_total_dollars"), Decimal("-1"))
        effective: Optional[Decimal] = None
        if days > 0 and total >= 0:
            effective = (total / days) * Decimal("100")
        elif days > 0 and rate >= 0:
            effective = rate
        elif rate >= 0:
            fallback_rates.append(rate)
        if effective is not None and days > 0:
            weighted_cents += effective * days
            weighted_days += days
    if weighted_days > 0:
        return weighted_cents / weighted_days
    if len(fallback_rates) == 1:
        return fallback_rates[0]
    if fallback_rates:
        return sum(fallback_rates, Decimal("0")) / Decimal(len(fallback_rates))
    return None


def _extract_tou_shares(lines: List[Dict[str, Any]]) -> Dict[str, float]:
    buckets: Dict[str, Decimal] = {}
    for line in lines:
        label = str(line.get("tou_band") or line.get("description") or "").lower()
        band = None
        for marker in ("peak", "shoulder", "offpeak", "off peak", "overnight"):
            if marker in label:
                band = "offpeak" if marker in ("off peak", "overnight") else marker
                break
        if band:
            buckets[band] = buckets.get(band, Decimal("0")) + _d(line.get("kwh"))
    total = sum(buckets.values(), Decimal("0"))
    if total <= 0:
        return {}
    return {k: float(v / total) for k, v in buckets.items()}


def normalise_bill(payload: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(payload, dict):
        raise ValueError("Bill extraction must be a JSON object.")
    fuel = str(payload.get("fuel_type") or "ELECTRICITY").upper()
    if fuel != "ELECTRICITY":
        raise ValueError("This connector release currently ranks electricity plans only.")

    start = parse_date(payload.get("billing_period_start"))
    end = parse_date(payload.get("billing_period_end"))
    if not start or not end or end < start:
        raise ValueError("Valid billing_period_start and billing_period_end are required.")
    computed_days = (end - start).days + 1
    stated_days = int(_d(payload.get("bill_days"), Decimal(computed_days)))
    warnings: List[str] = []
    if stated_days > 0 and abs(stated_days - computed_days) <= 1:
        # A one-day difference commonly means the provider's displayed end date is exclusive.
        # Honour the bill's explicit charge-day count, matching Android's annualisation semantics.
        bill_days = stated_days
    else:
        bill_days = computed_days
        if stated_days > 0 and stated_days != computed_days:
            warnings.append(
                f"Bill states {stated_days} days but dates span {computed_days} inclusive days; "
                "the source date span was used because the mismatch was larger than one day."
            )

    usage_lines = _lines(payload, "usage_lines")
    controlled = _lines(payload, "controlled_load_lines")
    supply = _lines(payload, "supply_charge_lines")
    solar = _lines(payload, "solar_export_lines")
    demand = _lines(payload, "demand_lines")
    general_kwh = _line_usage(usage_lines)
    if general_kwh <= 0:
        general_kwh = _d(payload.get("general_usage_kwh") or payload.get("usage_kwh"))
    if general_kwh <= 0:
        raise ValueError("No positive general electricity usage was extracted from the bill.")

    postcode = "".join(ch for ch in str(payload.get("service_postcode") or "") if ch.isdigit())
    if len(postcode) != 4:
        postcode = ""
    distributor = str(payload.get("distributor_name") or "").strip()
    explicit_state = str(payload.get("service_state") or "").upper().strip()
    postcode_state = state_from_postcode(postcode)
    distributor_state = state_from_distributor(distributor)
    # A valid service postcode is the strongest location signal for the AER climate mapping.
    # Never silently let a conflicting extracted state override it.
    if postcode_state:
        state = postcode_state
        if explicit_state and explicit_state != postcode_state:
            warnings.append(
                f"Extracted state {explicit_state} conflicts with service postcode {postcode}; "
                f"used postcode-derived {postcode_state} for seasonality and market geography."
            )
        if distributor_state and distributor_state != postcode_state:
            warnings.append(
                f"Distributor {distributor} appears inconsistent with postcode {postcode}; "
                "confirm the service address/distributor if plan results look incomplete."
            )
    else:
        state = explicit_state or distributor_state

    observations = [{
        "start": start.isoformat(), "end": end.isoformat(), "usage": general_kwh,
        "bill_days": bill_days, "label": "latest bill",
    }]
    for item in payload.get("historical_usage_observations") or []:
        if not isinstance(item, dict):
            continue
        observations.append({
            "start": item.get("billing_period_start") or item.get("start"),
            "end": item.get("billing_period_end") or item.get("end"),
            "usage": item.get("general_usage_kwh") if item.get("general_usage_kwh") is not None else item.get("usage_kwh"),
            "bill_days": item.get("bill_days") or item.get("days"),
            "label": item.get("label") or "previous bill",
        })
    seasonality = estimate_from_observations(
        observations, postcode=postcode, state=state, distributor=distributor, fuel="ELECTRICITY",
    )

    cl_kwh = _line_usage(controlled)
    annual_cl = cl_kwh / Decimal(bill_days) * Decimal("365") if cl_kwh > 0 else Decimal("0")
    solar_kwh = _line_usage(solar)
    annual_solar = solar_kwh / Decimal(bill_days) * Decimal("365") if solar_kwh > 0 else Decimal("0")

    usage_rate = _effective_cents(usage_lines)
    cl_rate = _effective_cents(controlled)
    solar_rate = _effective_cents(solar)
    supply_rate = _supply_daily_cents(supply, bill_days)

    current_comparable = Decimal("0")
    if supply_rate is not None:
        current_comparable += supply_rate / Decimal("100") * Decimal("365")
    if usage_rate is not None:
        current_comparable += usage_rate / Decimal("100") * seasonality.adjusted_annual_usage
    else:
        annualised_observed_usage_cost = _line_total(usage_lines) / Decimal(bill_days) * Decimal("365")
        current_comparable += annualised_observed_usage_cost
        warnings.append("Current general-usage baseline used annualised observed usage charges because an effective c/kWh rate was unavailable.")
    if cl_kwh > 0:
        if cl_rate is not None:
            current_comparable += cl_rate / Decimal("100") * annual_cl
        else:
            current_comparable += _line_total(controlled) / Decimal(bill_days) * Decimal("365")
            warnings.append("Controlled-load usage was straight-line annualised; no separate seasonal profile was assumed.")
    if solar_kwh > 0 and solar_rate is not None:
        current_comparable -= solar_rate / Decimal("100") * annual_solar
        warnings.append("Solar export was straight-line annualised; no seasonal export model was assumed.")
    if demand:
        current_comparable += _line_total(demand) / Decimal(bill_days) * Decimal("365")
        warnings.append("Current demand charges were straight-line annualised; candidate demand plans remain conservatively classified by BillBot.")

    bill_total = _d(payload.get("bill_total_dollars"), Decimal("0"))
    tou_shares = _extract_tou_shares(usage_lines)
    if len(tou_shares) > 1:
        warnings.append(
            "Current TOU baseline assumes the observed bill-period peak/shoulder/off-peak mix is "
            "representative of the year; candidate TOU results should be read with their model confidence."
        )

    return {
        "fuel": "ELECTRICITY",
        "postcode": postcode,
        "state": state,
        "distributor": distributor,
        "customer_type": str(payload.get("customer_type") or "RESIDENTIAL").upper(),
        "customer_name": str(payload.get("customer_name") or ""),
        "current_provider": str(payload.get("retailer_name") or "Current retailer"),
        "current_plan_name": str(payload.get("current_plan_name") or ""),
        "current_plan_id": str(payload.get("current_plan_id") or ""),
        "annual_usage": float(seasonality.adjusted_annual_usage),
        "annual_controlled_load_usage": float(annual_cl),
        "annual_solar_export": float(annual_solar),
        "current_annual_cost": float(current_comparable.quantize(MONEY_Q, rounding=ROUND_HALF_UP)) if current_comparable > 0 else None,
        "current_daily_supply": float(supply_rate) if supply_rate is not None else None,
        "current_avg_usage": float(usage_rate) if usage_rate is not None else None,
        "current_raw_rates": _rates_text(usage_lines, supply, controlled, solar),
        "tou_shares": tou_shares or None,
        "tou_profile_source": "OBSERVED_BILL" if tou_shares else "PROFILE_ESTIMATE",
        "seasonality": seasonality.to_dict(),
        "bill": {
            "billing_period_start": start.isoformat(),
            "billing_period_end": end.isoformat(),
            "bill_days": bill_days,
            "general_usage_kwh": float(general_kwh),
            "controlled_load_kwh": float(cl_kwh),
            "solar_export_kwh": float(solar_kwh),
            "bill_total_dollars": float(bill_total) if bill_total else None,
        },
        "warnings": warnings + seasonality.warnings,
    }


def _rates_text(usage: List[Dict[str, Any]], supply: List[Dict[str, Any]], controlled: List[Dict[str, Any]], solar: List[Dict[str, Any]]) -> str:
    out: List[str] = []
    for line in supply:
        r = _d(line.get("unit_rate_cents_per_day"), Decimal("-1"))
        if r >= 0:
            out.append(f"Supply {r:.3f}c/day")
    for group, suffix in ((usage, "c/kWh"), (controlled, "c/kWh"), (solar, "c/kWh export")):
        for line in group:
            r = _d(line.get("unit_rate_cents"), Decimal("-1"))
            if r >= 0:
                label = str(line.get("description") or line.get("tou_band") or "Usage")
                out.append(f"{label} {r:.3f}{suffix}")
    return " · ".join(dict.fromkeys(out))


def schema_example() -> Dict[str, Any]:
    return {
        "fuel_type": "ELECTRICITY",
        "customer_type": "RESIDENTIAL",
        "customer_name": None,
        "retailer_name": None,
        "current_plan_name": None,
        "current_plan_id": None,
        "distributor_name": None,
        "service_postcode": None,
        "service_state": None,
        "billing_period_start": "YYYY-MM-DD",
        "billing_period_end": "YYYY-MM-DD",
        "bill_days": None,
        "bill_total_dollars": None,
        "usage_lines": [{"description": "Peak", "tou_band": "peak", "kwh": 0, "unit_rate_cents": 0, "line_total_dollars": 0}],
        "supply_charge_lines": [{"description": "Supply", "days": 0, "unit_rate_cents_per_day": 0, "line_total_dollars": 0}],
        "controlled_load_lines": [],
        "solar_export_lines": [],
        "demand_lines": [],
        "historical_usage_observations": [
            {"billing_period_start": "YYYY-MM-DD", "billing_period_end": "YYYY-MM-DD", "general_usage_kwh": 0, "label": "previous bill"}
        ],
        "source": {"email_subject": None, "email_date": None, "attachment_name": None},
    }
