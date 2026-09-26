"""BillBot chat-friendly markdown and self-contained app-like HTML output."""
from __future__ import annotations

import html
from typing import Any, Dict


def _money(value: Any) -> str:
    try: return f"${float(value):,.0f}"
    except Exception: return "—"


def _esc(value: Any) -> str:
    return html.escape(str(value or ""))


def render_markdown(result: Dict[str, Any]) -> str:
    current = result.get("current") or {}
    season = result.get("seasonality") or {}
    sense = result.get("sense_check") or {}
    diagnostics = result.get("diagnostics") or {}
    lines = [
        "## BillBot electricity comparison",
        f"**Estimated annual usage:** {float(season.get('adjusted_annual_usage') or 0):,.0f} kWh · {season.get('confidence','').title()} confidence",
        f"**Current comparable annual cost:** {_money(current.get('annual_comparable_cost'))}",
        "",
        "| # | Plan | Est. annual cost | Est. saving | Confidence |",
        "|---:|---|---:|---:|---|",
    ]
    for p in result.get("top_plans") or []:
        saving = p.get("savings")
        saving_text = _money(saving) if saving is not None else "—"
        lines.append(f"| {p.get('rank')} | **{p.get('retailer')} — {p.get('plan_name')}** | {_money(p.get('annual_cost'))} | {saving_text} | {p.get('confidence') or p.get('classification')} |")
    lines += [
        "",
        f"Climate-normal seasonal adjustment: **{float(season.get('seasonal_adjustment_factor') or 1):.3f}×** using exact bill dates; this is not observed-weather normalization.",
        f"**Sense check:** {sense.get('status', 'UNKNOWN')} — {sense.get('summary', 'No sense-check summary available.')}",
        f"**Diagnostic run:** `{result.get('run_id') or diagnostics.get('run_id') or 'n/a'}` · warnings {diagnostics.get('warning_count', 0)} · errors {diagnostics.get('error_count', 0)}",
        "BillBot is free and independent; voluntary support never affects rankings.",
    ]
    return "\n".join(lines)


def render_html(result: Dict[str, Any]) -> str:
    current = result.get("current") or {}
    season = result.get("seasonality") or {}
    market = result.get("market") or {}
    plans = result.get("top_plans") or []
    bill_info = result.get("bill") or {}
    best = plans[0] if plans else {}
    sense = result.get("sense_check") or {}
    diagnostics = result.get("diagnostics") or {}
    sense_status = str(sense.get("status") or "UNKNOWN").upper()
    sense_class = "sense-pass" if sense_status == "PASS" else "sense-warn" if sense_status == "WARN" else "sense-fail"
    cards = []
    for p in plans:
        saving = p.get("savings")
        positive = saving is not None and float(saving) > 0
        badge = p.get("confidence") or p.get("classification") or "Estimate"
        url = p.get("application_uri") or p.get("website") or ""
        cta = f'<a class="cta" href="{_esc(url)}" target="_blank" rel="noopener">View plan</a>' if url else ''
        note = _esc(p.get("notes") or "")
        cards.append(f'''<article class="plan-card">
          <div class="rank">{p.get("rank")}</div>
          <div class="plan-main">
            <div class="eyebrow">{_esc(p.get("retailer"))} <span class="badge">{_esc(badge)}</span></div>
            <h3>{_esc(p.get("plan_name"))}</h3>
            <div class="money-row"><strong>{_money(p.get("annual_cost"))}</strong><span>/ year</span></div>
            <div class="saving {'good' if positive else ''}">{('Save ' + _money(saving) + ' / year') if saving is not None else 'Current-cost comparison unavailable'}</div>
            {f'<p class="note">{note}</p>' if note else ''}
          </div>
          <div class="plan-actions">{cta}</div>
        </article>''')
    warnings = "".join(f"<li>{_esc(x)}</li>" for x in result.get("warnings") or [])
    raw = season.get("raw_annual_usage") or 0
    adjusted = season.get("adjusted_annual_usage") or 0
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>BillBot comparison</title><style>
:root{{--bg:#07110e;--surface:#0d1b17;--card:#10241d;--line:#244438;--text:#f3fbf7;--muted:#9fbbb0;--mint:#7df1c4;--green:#20c886;--chip:#18362c;--shadow:0 18px 50px rgba(0,0,0,.28)}}
*{{box-sizing:border-box}}body{{margin:0;background:radial-gradient(circle at top right,#153c30 0,#07110e 36%,#050b09 100%);color:var(--text);font:15px/1.45 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}}a{{color:inherit}}.app{{max-width:760px;margin:auto;padding:22px 16px 60px}}header{{display:flex;justify-content:space-between;align-items:center;margin-bottom:18px}}.brand{{font-weight:850;font-size:25px;letter-spacing:-.7px}}.brand i{{font-style:normal;color:var(--mint)}}.open{{font-size:12px;color:var(--muted);border:1px solid var(--line);padding:7px 10px;border-radius:999px}}.hero{{background:linear-gradient(145deg,#0e261e,#0b1915);border:1px solid #285344;border-radius:24px;padding:22px;box-shadow:var(--shadow)}}.hero .kicker{{color:var(--mint);font-size:12px;font-weight:800;text-transform:uppercase;letter-spacing:.8px}}h1{{font-size:28px;line-height:1.08;margin:8px 0 16px;letter-spacing:-.8px}}.hero-grid{{display:grid;grid-template-columns:1fr 1fr;gap:10px}}.stat{{background:#091510;border:1px solid #1c3d32;border-radius:16px;padding:13px}}.stat label{{display:block;color:var(--muted);font-size:11px;margin-bottom:4px}}.stat strong{{font-size:21px}}.best{{margin-top:12px;background:linear-gradient(120deg,#174f3c,#123126);border-radius:16px;padding:14px}}.best small{{color:#bcefdc}}.best strong{{display:block;font-size:20px;margin-top:2px}}.section-title{{margin:24px 2px 10px;display:flex;justify-content:space-between;align-items:end}}.section-title h2{{font-size:18px;margin:0}}.section-title span{{font-size:12px;color:var(--muted)}}.plan-card{{position:relative;display:grid;grid-template-columns:38px 1fr auto;gap:12px;align-items:center;background:rgba(16,36,29,.92);border:1px solid var(--line);border-radius:18px;padding:14px;margin:9px 0;box-shadow:0 8px 20px rgba(0,0,0,.12)}}.rank{{width:32px;height:32px;border-radius:11px;background:var(--chip);display:grid;place-items:center;color:var(--mint);font-weight:850}}.eyebrow{{font-size:12px;color:#b8d2c8;font-weight:700}}.badge{{display:inline-block;margin-left:6px;padding:2px 6px;border-radius:999px;background:#1b3b30;color:#b5ebd5;font-size:9px;text-transform:uppercase}}h3{{font-size:15px;margin:3px 0 7px}}.money-row{{display:flex;gap:5px;align-items:baseline}}.money-row strong{{font-size:20px}}.money-row span{{font-size:11px;color:var(--muted)}}.saving{{font-size:12px;color:#b8c6c0}}.saving.good{{color:var(--mint);font-weight:800}}.note{{font-size:10px;color:var(--muted);margin:6px 0 0;max-width:470px}}.cta{{display:inline-block;text-decoration:none;border:1px solid #4d9b7d;border-radius:11px;padding:8px 10px;color:#d9fff0;font-size:11px;font-weight:750;white-space:nowrap}}.detail{{background:#0a1713;border:1px solid #1c352d;border-radius:18px;padding:16px;margin-top:22px}}.detail h2{{font-size:15px;margin:0 0 10px}}.detail-grid{{display:grid;grid-template-columns:1fr 1fr;gap:8px}}.detail p{{margin:0;background:#0d201a;border-radius:12px;padding:10px;color:var(--muted);font-size:11px}}.detail b{{display:block;color:var(--text);font-size:12px;margin-top:2px}}.warnings{{font-size:11px;color:#d6caaa}}.sense{{margin-top:12px;border-radius:14px;padding:12px;font-size:11px}}.sense-pass{{background:#102d24;color:#c7f7e4;border:1px solid #286c55}}.sense-warn{{background:#302713;color:#f5deb0;border:1px solid #725b24}}.sense-fail{{background:#351819;color:#ffd0d0;border:1px solid #7e3438}}footer{{text-align:center;color:var(--muted);font-size:11px;margin-top:22px}}.support{{display:inline-block;margin-top:8px;padding:9px 12px;border-radius:12px;background:#163c30;color:#dffff2;text-decoration:none;font-weight:750}}
@media(max-width:580px){{.app{{padding:14px 10px 44px}}.hero{{padding:17px}}h1{{font-size:24px}}.plan-card{{grid-template-columns:34px 1fr}}.plan-actions{{grid-column:2}}.detail-grid{{grid-template-columns:1fr}}}}
</style></head><body><main class="app"><header><div class="brand">Bill<i>Bot</i></div><div class="open">Free · independent · open</div></header>
<section class="hero"><div class="kicker">Your electricity comparison</div><h1>Market checked against your actual bill</h1><div class="hero-grid"><div class="stat"><label>Estimated annual usage</label><strong>{float(adjusted):,.0f} kWh</strong></div><div class="stat"><label>Current comparable cost</label><strong>{_money(current.get('annual_comparable_cost'))}</strong></div></div>
<div class="best"><small>Best priced result</small><strong>{_esc(best.get('retailer'))} · {_money(best.get('annual_cost'))}/yr</strong><small>{('Estimated saving ' + _money(best.get('savings')) + '/yr') if best else 'No priceable result'}</small></div></section>
<div class="section-title"><h2>Top {len(plans)} plans</h2><span>Ranked by estimated annual cost</span></div>{''.join(cards)}
<section class="detail"><h2>How BillBot calculated this</h2><div class="detail-grid"><p>Observed usage<b>{float(bill_info.get('general_usage_kwh') or 0):,.0f} kWh · {bill_info.get('bill_days')} days</b></p><p>Seasonal estimate<b>{float(raw):,.0f} → {float(adjusted):,.0f} kWh/yr · {float(season.get('seasonal_adjustment_factor') or 1):.3f}×</b></p><p>Location basis<b>{_esc(season.get('location_basis'))} · climate zone {_esc(season.get('climate_zone') or 'n/a')}</b></p><p>Market snapshot<b>{_esc(market.get('generated_at') or 'latest available')} · {_esc(market.get('publisher') or 'BillBot')}</b></p></div>
<p style="margin-top:10px">Seasonality is a climate-normal AER benchmark adjustment using exact bill dates. It is <b style="display:inline">not observed-weather normalization</b>.</p>{f'<ul class="warnings">{warnings}</ul>' if warnings else ''}<div class="sense {sense_class}"><b>Final deterministic sense check: {_esc(sense_status)}</b><br>{_esc(sense.get('summary') or 'No sense-check summary available.')}<br>Run ID: <code>{_esc(result.get('run_id') or diagnostics.get('run_id') or 'n/a')}</code> · warnings {diagnostics.get('warning_count',0)} · errors {diagnostics.get('error_count',0)}</div></section>
<footer>BillBot receives no retailer commissions. Donations never affect rankings.<br><a class="support" href="https://square.link/u/1cl90zLr">Support BillBot</a></footer></main></body></html>'''
