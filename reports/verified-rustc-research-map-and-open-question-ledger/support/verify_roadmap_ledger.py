#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Verify that all 17 design areas, 114 program questions, and 107 verified-rustc packages are answered and indexed."""

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG_DIR = HERE.parent
REPORTS_DIR = PKG_DIR.parent
REPO_ROOT = REPORTS_DIR.parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--area", default="", help="Filter output by area id or title substring")
    args = parser.parse_args()

    ledger = json.loads((HERE / "roadmap_ledger.json").read_text(encoding="utf-8"))
    areas = ledger["design_areas"]

    if len(areas) != 17:
        sys.stderr.write(f"Expected 17 design areas, found {len(areas)}\n")
        return 1

    total_full = sum(len(a["answered_fully"]) for a in areas)
    total_part = sum(len(a["answered_partly"]) for a in areas)
    total_open = sum(len(a["unanswered_questions"]) for a in areas)
    total_q = sum(len(a["questions_ledger"]) for a in areas)

    if total_q != 114 or total_full != 114 or total_part != 0 or total_open != 0:
        sys.stderr.write(
            f"Ledger mismatch: total_q={total_q}, full={total_full}, part={total_part}, open={total_open}\n"
        )
        return 1

    vr_pkgs = set()
    all_referenced_pkgs = set()
    for a in areas:
        vr_pkgs.update(a["verified_rustc_packages"])
        all_referenced_pkgs.update(a["existing_packages"])
        for q in a["questions_ledger"]:
            if q["status"] != "ANSWERED" or not q["reports"]:
                sys.stderr.write(f"Unanswered question in area {a['id']}: {q}\n")
                return 1
            all_referenced_pkgs.update(q["reports"])

    if len(vr_pkgs) != 107:
        sys.stderr.write(f"Expected 107 unique verified-rustc packages, found {len(vr_pkgs)}\n")
        return 1

    cat_path = REPO_ROOT / "CATALOG.json"
    if cat_path.is_file():
        cat_reports = json.loads(cat_path.read_text(encoding="utf-8"))["reports"]
        known_pkgs = set(cat_reports.keys()) | {"verified-rustc-designer-dry-run-and-gap-analysis"}
        unknown = all_referenced_pkgs - known_pkgs
        if unknown:
            sys.stderr.write(f"Unknown packages referenced in roadmap_ledger.json: {sorted(unknown)}\n")
            return 1
        cat_vr = {
            k for k, v in cat_reports.items() if "compilers/verified-rustc" in v.get("topics", [])
        } | {"verified-rustc-designer-dry-run-and-gap-analysis"}
        if vr_pkgs != cat_vr:
            sys.stderr.write(
                f"Catalog verified-rustc mismatch: missing={sorted(cat_vr - vr_pkgs)}, extra={sorted(vr_pkgs - cat_vr)}\n"
            )
            return 1

    shown = areas
    if args.area:
        shown = [
            a
            for a in areas
            if args.area.lower() in a["id"].lower() or args.area.lower() in a["title"].lower()
        ]

    print(
        f"Verified {len(areas)} design areas | Fully answered: {total_full} | "
        f"Partly answered: {total_part} | Open questions: {total_open} | "
        f"Unique compilers/verified-rustc packages: {len(vr_pkgs)}"
    )
    for a in shown:
        print(
            f"  [{a['id']}] {a['title']}: full={len(a['answered_fully'])} "
            f"part={len(a['answered_partly'])} open={len(a['unanswered_questions'])} "
            f"vr_pkgs={len(a['verified_rustc_packages'])} total_pkgs={len(a['existing_packages'])}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
