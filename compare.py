"""End-to-end BillBot bill comparison orchestration."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional
import re

from bill import normalise_bill
from market import DEFAULT_MANIFEST_URL, get_market_database
import billbot_core
from diagnostics import BillBotComparisonError, DiagnosticRecorder, sense_check_result
from render import render_html, render_markdown


def _norm_name(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", " ", str(value or "").lower()).strip()


def _rank_top(
    payload: Dict[str, Any], top_n: int, *, current_provider: str = "", current_plan_name: str = ""
) -> List[Dict[str, Any]]:
    candidates: List[Dict[str, Any]] = []
    for group, reliability in (
        (payload.get("verified_plans") or [], 0),
        (payload.get("modelled_plans") or [], 1),
    ):
        for plan in group:
            if plan.get("annual_cost") is None:
                continue
            if current_provider and current_plan_name:
                if (
                    _norm_name(plan.get("retailer")) == _norm_name(current_provider)
                    and _norm_name(plan.get("plan_name")) == _norm_name(current_plan_name)
                ):
                    continue
            item = dict(plan)
            item["_reliability_order"] = reliability
            candidates.append(item)
    candidates.sort(key=lambda p: (float(p.get("annual_cost") or 1e30), p["_reliability_order"], str(p.get("retailer") or ""), str(p.get("plan_name") or "")))
    out = []
    for i, plan in enumerate(candidates[: max(1, min(int(top_n), 50))], start=1):
        plan.pop("_reliability_order", None)
        plan["rank"] = i
        out.append(plan)
    return out


def compare_bill(
    bill: Dict[str, Any], *, top_n: int = 10, manifest_url: str = DEFAULT_MANIFEST_URL,
    cache_dir: Optional[str] = None, render: bool = True, log_dir: Optional[str] = None,
) -> Dict[str, Any]:
    recorder = DiagnosticRecorder(log_dir=log_dir)
    request: Dict[str, Any] = {}
    manifest: Dict[str, Any] = {}
    try:
        try:
            request = normalise_bill(bill)
        except Exception as exc:
            recorder.exception("BILL_NORMALISATION_FAILED", "normalise_bill", exc)
            raise

        for warning in request.get("warnings") or []:
            recorder.warning("INPUT_OR_CALCULATION_WARNING", "normalise_bill", str(warning), {
                "bill_days": (request.get("bill") or {}).get("bill_days"),
                "general_usage_kwh": (request.get("bill") or {}).get("general_usage_kwh"),
                "annual_usage_kwh": request.get("annual_usage"),
            })

        try:
            db_path, manifest = get_market_database(manifest_url=manifest_url, cache_dir=cache_dir)
        except Exception as exc:
            recorder.exception("MARKET_DOWNLOAD_OR_VALIDATION_FAILED", "market_database", exc, {"manifest_url": manifest_url})
            raise

        if not request.get("distributor") and request.get("postcode"):
            try:
                suggested = billbot_core.suggest_distributor(db_path, str(request["postcode"]), "ELECTRICITY")
            except Exception as exc:
                recorder.exception("DISTRIBUTOR_SUGGESTION_FAILED", "distributor_resolution", exc, {"postcode": request.get("postcode")})
                suggested = ""
            if suggested:
                request["distributor"] = suggested
            else:
                try:
                    candidates = json.loads(billbot_core.distributor_candidates(db_path, str(request["postcode"]), "ELECTRICITY")).get("distributors") or []
                except Exception as exc:
                    recorder.exception("DISTRIBUTOR_CANDIDATES_FAILED", "distributor_resolution", exc, {"postcode": request.get("postcode")})
                    candidates = []
                if len(candidates) > 1:
                    raise ValueError("This postcode maps to more than one electricity distributor. Confirm the distributor shown on the bill before comparing: " + ", ".join(candidates))
        if not request.get("postcode") and not request.get("distributor"):
            raise ValueError("A service postcode or electricity distributor is required to filter plans to the customer's market.")

        core_request = {k: v for k, v in request.items() if k not in ("bill", "warnings", "seasonality")}
        try:
            raw = billbot_core.compare_energy_v2(db_path, json.dumps(core_request, separators=(",", ":")))
            compared = json.loads(raw)
        except Exception as exc:
            recorder.exception("ANDROID_CORE_COMPARISON_FAILED", "billbot_core.compare_energy_v2", exc, {
                "annual_usage_kwh": request.get("annual_usage"),
                "has_postcode": bool(request.get("postcode")),
                "has_distributor": bool(request.get("distributor")),
                "snapshot_id": manifest.get("snapshot_id"),
            })
            raise
        if not compared.get("ok"):
            message = compared.get("error") or "BillBot comparison failed."
            recorder.error("ANDROID_CORE_RETURNED_ERROR", "billbot_core.compare_energy_v2", str(message), {
                "snapshot_id": manifest.get("snapshot_id"),
                "candidate_count": compared.get("candidate_count"),
            })
            raise ValueError(message)

        try:
            top = _rank_top(
                compared, top_n,
                current_provider=str(request.get("current_provider") or ""),
                current_plan_name=str(request.get("current_plan_name") or ""),
            )
        except Exception as exc:
            recorder.exception("RANKING_FAILED", "rank_top", exc, {"top_n": top_n})
            raise

        result = {
            "ok": True,
            "run_id": recorder.run_id,
            "bill": request["bill"],
            "current": {
                "retailer": request.get("current_provider"),
                "plan_name": request.get("current_plan_name"),
                "annual_comparable_cost": request.get("current_annual_cost"),
                "daily_supply_cents": request.get("current_daily_supply"),
                "effective_usage_cents": request.get("current_avg_usage"),
                "raw_rates": request.get("current_raw_rates"),
            },
            "seasonality": request.get("seasonality"),
            "top_plans": top,
            "market": {
                "snapshot_id": manifest.get("snapshot_id"),
                "generated_at": manifest.get("generated_at"),
                "counts": manifest.get("counts"),
                "status": compared.get("market_refresh"),
                "candidate_count": compared.get("candidate_count"),
                "classification_counts": compared.get("classification_counts"),
                "publisher": manifest.get("publisher"),
                "publisher_version": manifest.get("publisher_version"),
                "download_url": manifest.get("download_url"),
            },
            "warnings": request.get("warnings") or [],
            "unpriceable_count": len(compared.get("unpriceable_plans") or []),
            "provenance": {
                "provider": "BillBot",
                "engine_version": "1.2.0",
                "market_data": "BillBot Market Updater Android snapshot (the same latest.db.gz consumed by BillBot Android v1.4.46)",
                "seasonality_source": (request.get("seasonality") or {}).get("source"),
                "support": "https://square.link/u/1cl90zLr",
            },
        }
        result["sense_check"] = sense_check_result(result, recorder)
        result["diagnostics"] = recorder.summary()
        if result["sense_check"]["status"] == "FAIL":
            result["ok"] = False

        if render:
            try:
                result["markdown"] = render_markdown(result)
                result["html"] = render_html(result)
            except Exception as exc:
                recorder.exception("RENDER_FAILED", "render", exc, {"ranked_count": len(top)})
                result["diagnostics"] = recorder.summary()
                raise
        return result
    except BillBotComparisonError:
        raise
    except Exception as exc:
        if not recorder.errors or recorder.errors[-1].get("message") != str(exc):
            recorder.exception("COMPARISON_PIPELINE_FAILED", "compare_bill", exc, {
                "snapshot_id": manifest.get("snapshot_id") if isinstance(manifest, dict) else None,
                "has_postcode": bool(request.get("postcode")) if isinstance(request, dict) else False,
                "has_distributor": bool(request.get("distributor")) if isinstance(request, dict) else False,
            })
        raise BillBotComparisonError(f"{exc} [BillBot run_id={recorder.run_id}]", recorder.run_id) from exc


def compare_bill_file(path: str, **kwargs: Any) -> Dict[str, Any]:
    bill = json.loads(Path(path).read_text(encoding="utf-8"))
    return compare_bill(bill, **kwargs)
