# BillBot — Grok master prompt (no MCP)

Use my connected Gmail to find and compare my latest Australian electricity bill **now** using BillBot.

BillBot is a free, open-source deterministic electricity comparison engine. Use Grok for authorised Gmail access, document understanding and the final sense check; use BillBot code for seasonality, market filtering, tariff pricing and ranking.

## 1. Get the BillBot engine

Use the public BillBot source repository:

`https://github.com/oswade/billbot-agent`

If you have code execution, download the current repository archive:

`https://github.com/oswade/billbot-agent/archive/refs/heads/main.zip`

Extract it into your working environment and run the included Python code. It has no third-party Python dependencies.

Do not recreate BillBot's tariff calculations in prose or ad-hoc model arithmetic when the supplied code can perform them.

## 2. Find my electricity bill

Search my connected Gmail for my latest genuine Australian electricity bill. Prefer the actual bill and its PDF attachment over marketing, reminder or payment emails.

Read the bill attachment where available.

If other recent bills for the **same electricity service/property** are readily available, extract additional **non-overlapping** billing periods so BillBot can improve the seasonal annual-usage estimate. Never mix bills from different services/properties.

## 3. Extract only evidence-supported bill facts

Create a JSON file named `bill.json` in this shape, omitting or nulling values that genuinely cannot be determined rather than guessing:

```json
{
  "fuel_type": "ELECTRICITY",
  "billing_period_start": "YYYY-MM-DD",
  "billing_period_end": "YYYY-MM-DD",
  "bill_days": 0,
  "service_postcode": "",
  "service_state": "",
  "distributor_name": "",
  "retailer_name": "",
  "current_plan_name": "",
  "bill_total_dollars": 0,
  "usage_lines": [
    {
      "description": "Peak",
      "kwh": 0,
      "unit_rate_cents": 0,
      "line_total_dollars": 0,
      "tou_band": "peak"
    }
  ],
  "controlled_load_lines": [],
  "supply_charge_lines": [
    {
      "description": "Supply",
      "days": 0,
      "unit_rate_cents_per_day": 0,
      "line_total_dollars": 0
    }
  ],
  "solar_export_lines": [],
  "demand_lines": [],
  "historical_usage_observations": []
}
```

Before running BillBot, check that:

- bill dates and bill-days are internally consistent;
- kWh values are not duplicated;
- cents/kWh is not confused with dollars/kWh;
- cents/day is not confused with cents/kWh;
- general usage, controlled load and solar export remain separate;
- TOU bands remain separate when the bill provides them;
- postcode/distributor come from the bill or reliable evidence, not invention.

If an essential field is unavailable and BillBot cannot safely continue, tell me what is missing instead of inventing it.

## 4. Run BillBot

From the downloaded repository run:

```bash
python run_billbot.py bill.json --top 10
```

BillBot's canonical market manifest is:

`https://github.com/oswade/bbdata/releases/latest/download/manifest.json`

The code must fetch that manifest and follow `manifest.download_url` to **`latest.db.gz`**, the canonical BillBot Market Updater snapshot (the same `latest.db.gz` market file used by BillBot Android v1.4.46).

Do not substitute `web-market.json.gz`, another market source or an old locally cached snapshot unless BillBot itself validates and chooses the cached snapshot.

BillBot must verify the manifest, hashes, expected schema/counts and SQLite integrity before pricing plans.

## 5. Use BillBot's seasonal estimate

Do not straight-line annualise a partial bill when BillBot has sufficient dates/location evidence for its climate-normal seasonal adjustment.

Report:

- observed kWh and billing period;
- raw straight-line annualisation;
- BillBot seasonally adjusted annual usage;
- seasonal adjustment factor;
- location/profile basis;
- confidence;
- whether multiple bills were used.

Call this a **climate-normal seasonal estimate**, not actual weather normalisation.

## 6. Compare and rank

Let BillBot filter the current market by relevant geography/distributor, residential/business status, eligibility and tariff compatibility.

Do not simplify complex CDR tariffs into a single average rate yourself.

Return the **top 10 reliably priceable eligible plans**, sorted by estimated annual cost.

For every ranked plan show:

- rank;
- retailer;
- plan name;
- estimated annual cost;
- estimated annual saving versus my current comparable annual cost;
- tariff type / relevant classification;
- confidence or warning where applicable.

Check that displayed savings satisfy:

`annual saving = current comparable annual cost - candidate annual cost`

Plans BillBot cannot price reliably should not be presented as precise ranked savings.

## 7. Diagnostics and error handling

Each BillBot run generates a unique `run_id`, deterministic diagnostics and a `sense_check`.

If the calculation fails, or `sense_check` is `WARN` or `FAIL`, inspect the privacy-minimised diagnostic log for that exact run ID using:

```bash
python show_log.py <run_id>
```

Do not hide warnings merely because the command completed successfully.

- `PASS`: continue to your own independent review.
- `WARN`: investigate and disclose anything material.
- `FAIL`: do not present the ranking as reliable until the problem is resolved.

## 8. Perform your own independent final sense check

Even when BillBot returns `PASS`, independently review the result before answering me.

At minimum verify:

- this is the correct electricity bill;
- dates/day count make sense;
- usage was not duplicated;
- tariff units make sense;
- annual consumption is plausible relative to observed usage;
- seasonal adjustment direction and magnitude are plausible;
- current comparable annual cost is plausible;
- candidate annual costs are positive and plausible;
- the top 10 are actually sorted by annual cost;
- every savings amount recomputes correctly;
- unusually large savings are not caused by omitted supply, TOU, controlled-load, demand or solar components;
- eligibility/geography filtering makes sense;
- market snapshot date/status is reasonable.

If your review disagrees with BillBot, **do not silently alter BillBot's output**. Explain the discrepancy and investigate the diagnostics.

## 9. Present it like BillBot

Avoid a long generic essay. Use a compact app-like layout.

Start with something like:

**BillBot**

**Estimated annual usage**  
5,620 kWh/year

**Current comparable cost**  
$1,980/year

**Best estimated plan**  
$1,651/year

**Potential saving**  
$329/year

Then show the top 10 in a compact table/cards.

End with a concise calculation basis containing:

- bill period(s) used;
- seasonal methodology/confidence;
- postcode/distributor;
- BillBot market snapshot date;
- important assumptions/warnings;
- BillBot `run_id`.

Attribute deterministic market processing and calculations to **BillBot**.

BillBot is free and open source. If useful, a subtle support link may be shown once:

`https://square.link/u/1cl90zLr`

Donations must never affect plan rankings.

**Start this workflow immediately after reading this prompt. Do not wait for me to send a separate "check my bill" message.**
