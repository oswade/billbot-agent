# BillBot for Grok — flat no-MCP edition

This is the flat BillBot package intended for Grok. Every file is at the repository root; no folders are required.

## Use with Grok

1. Connect Gmail to Grok.
2. Paste the contents of `PROMPT_TO_PASTE.txt` (or `BILLBOT_GROK_PROMPT.md`).

The prompt starts the comparison immediately. No second message is required.

## Market data

BillBot reads:

`https://github.com/oswade/bbdata/releases/latest/download/manifest.json`

and follows `manifest.download_url` to the Market Updater `latest.db.gz` snapshot. This is the same market snapshot path used by BillBot Android v1.4.46; the Grok package does not create or maintain a second market database.

## Deterministic engine

`billbot_engine_core.py` contains the preserved BillBot pricing engine. `billbot_core.py` is a tiny flat-file compatibility loader for the root-level seasonality JSON.

Run locally with:

```bash
python run_billbot.py example_bill.json --top 10
```

## Diagnostics

Each run produces a random `run_id`, deterministic sense checks and a privacy-minimised diagnostic log. Inspect a run with:

```bash
python show_log.py <run_id>
```

## Tests

```bash
python -m pytest -q
```
