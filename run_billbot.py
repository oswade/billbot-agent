#!/usr/bin/env python3
"""BillBot no-MCP runner for Grok/other code-execution environments."""
from __future__ import annotations
import argparse, json
from pathlib import Path
from compare import compare_bill_file


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bill_json")
    ap.add_argument("--top", type=int, default=10)
    ap.add_argument("--manifest", default=None)
    ap.add_argument("--out", default="billbot-result.json")
    ap.add_argument("--html", default="billbot-result.html")
    ap.add_argument("--log-dir", default="billbot-logs")
    args = ap.parse_args()
    kwargs = {"top_n": args.top, "log_dir": args.log_dir}
    if args.manifest:
        kwargs["manifest_url"] = args.manifest
    result = compare_bill_file(args.bill_json, **kwargs)
    Path(args.html).write_text(result.get("html", ""), encoding="utf-8")
    compact = {k:v for k,v in result.items() if k != "html"}
    Path(args.out).write_text(json.dumps(compact, indent=2), encoding="utf-8")
    print(result.get("markdown") or json.dumps(compact, indent=2))
    print(f"\nrun_id={result.get('run_id')}")
    print(f"diagnostics={result.get('diagnostics',{}).get('log_file')}")

if __name__ == "__main__":
    main()
