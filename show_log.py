#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from diagnostics import read_log

ap=argparse.ArgumentParser(description="Read privacy-minimised BillBot diagnostics for one run.")
ap.add_argument("run_id")
ap.add_argument("--log-dir", default="billbot-logs")
args=ap.parse_args()
rows=read_log(run_id=args.run_id, log_dir=args.log_dir)
print(json.dumps(rows, indent=2))
