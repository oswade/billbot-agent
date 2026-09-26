from __future__ import annotations
import argparse, json
from pathlib import Path
from compare import compare_bill_file


def main():
    p=argparse.ArgumentParser(description="Compare an extracted electricity bill with BillBot's latest public CDR market snapshot.")
    p.add_argument("bill_json")
    p.add_argument("--top", type=int, default=10)
    p.add_argument("--html", default="billbot-comparison.html")
    p.add_argument("--json", dest="json_out", default="billbot-comparison.json")
    p.add_argument("--manifest", default=None)
    p.add_argument("--log-dir", default=None)
    args=p.parse_args()
    kwargs={"top_n":args.top, "log_dir": args.log_dir}
    if args.manifest: kwargs["manifest_url"]=args.manifest
    result=compare_bill_file(args.bill_json, **kwargs)
    Path(args.html).write_text(result["html"],encoding="utf-8")
    compact={k:v for k,v in result.items() if k != "html"}
    Path(args.json_out).write_text(json.dumps(compact, indent=2), encoding="utf-8")
    print(result["markdown"])
    print(f"\nHTML report: {args.html}")
    print(f"JSON report: {args.json_out}")
    print(f"Diagnostic log: {result.get('diagnostics',{}).get('log_file','n/a')}")

if __name__=="__main__": main()
