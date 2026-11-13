#!/usr/bin/env python3
"""Query the verified-rustc design-area roadmap and open-question ledger."""
import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEDGER = json.loads((HERE / "roadmap_ledger.json").read_text(encoding="utf-8"))

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--area", default="", help="Filter by area id substring")
    args = parser.parse_args()

    areas = LEDGER["design_areas"]
    if args.area:
        areas = [a for a in areas if args.area.lower() in a["id"].lower() or args.area.lower() in a["title"].lower()]

    total_full = sum(len(a["answered_fully"]) for a in areas)
    total_part = sum(len(a["answered_partly"]) for a in areas)
    total_open = sum(len(a["unanswered_questions"]) for a in areas)
    print(f"Matched {len(areas)} design areas | Fully answered: {total_full} | Partly answered: {total_part} | Open questions: {total_open}")
    for a in areas:
        print(f"  [{a['id']}] {a['title']}: full={len(a['answered_fully'])} part={len(a['answered_partly'])} open={len(a['unanswered_questions'])} pkgs={len(a['existing_packages'])}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
