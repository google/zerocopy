#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Verify designer dry-run decision coverage and gap closure across all 13 domains and 27 goals."""

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG_DIR = HERE.parent
REPORTS_DIR = PKG_DIR.parent
REPO_ROOT = REPORTS_DIR.parent


def load_catalog_packages() -> tuple[set[str], set[str]]:
    cat_path = REPO_ROOT / "CATALOG.json"
    if cat_path.is_file():
        reports = json.loads(cat_path.read_text(encoding="utf-8"))["reports"]
        all_pkgs = set(reports.keys()) | {PKG_DIR.name}
        vr_pkgs = {
            k for k, v in reports.items() if "compilers/verified-rustc" in v.get("topics", [])
        } | {PKG_DIR.name}
        return all_pkgs, vr_pkgs
    return set(), set()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--domain",
        default="",
        help="Optional domain ID filter (e.g., D1, D6, D13)",
    )
    args = parser.parse_args()

    matrix_path = HERE / "decision_coverage_matrix.json"
    matrix = json.loads(matrix_path.read_text(encoding="utf-8"))

    domains = matrix["decision_domains"]
    goals = matrix["goals_coverage"]
    tensions = matrix["design_tensions_resolved"]

    if len(domains) != 13:
        sys.stderr.write(f"Expected 13 decision domains, found {len(domains)}\n")
        return 1
    if len(goals) != 27:
        sys.stderr.write(f"Expected 27 research goals, found {len(goals)}\n")
        return 1

    covered_goals = set()
    mapped_pkgs = set()
    unrecorded_facts = 0
    new_seeds = 0

    for d in domains:
        covered_goals.update(d["goals_addressed"])
        mapped_pkgs.update(d["supplying_reports"])
        unrecorded_facts += len(d["missing_or_contradictory_facts"])
        new_seeds += len(d["new_seeds_required"])
        if d["gap_classification"] != "REASONING_ONLY":
            sys.stderr.write(
                f"Domain {d['domain_id']} has unresolved gap classification: {d['gap_classification']}\n"
            )
            return 1
        if not d["quantitative_facts"] or not d["supplying_reports"]:
            sys.stderr.write(f"Domain {d['domain_id']} is missing facts or reports\n")
            return 1

    if covered_goals != set(range(1, 28)):
        missing_g = set(range(1, 28)) - covered_goals
        sys.stderr.write(f"Missing research goals: {sorted(missing_g)}\n")
        return 1

    if unrecorded_facts != 0 or new_seeds != 0:
        sys.stderr.write(
            f"Expected 0 unrecorded facts and 0 new seeds, got {unrecorded_facts} and {new_seeds}\n"
        )
        return 1

    all_cat_pkgs, vr_pkgs = load_catalog_packages()
    if all_cat_pkgs:
        unknown_pkgs = mapped_pkgs - all_cat_pkgs
        if unknown_pkgs:
            sys.stderr.write(f"Unknown packages referenced in matrix: {sorted(unknown_pkgs)}\n")
            return 1
        unmapped_vr = vr_pkgs - mapped_pkgs
        if unmapped_vr:
            sys.stderr.write(f"Unmapped compilers/verified-rustc packages: {sorted(unmapped_vr)}\n")
            return 1

    shown_domains = domains
    if args.domain:
        shown_domains = [
            d for d in domains if args.domain.lower() in d["domain_id"].lower()
        ]

    print(
        f"Verified {len(domains)} architectural decision domains, {len(goals)} research goals, "
        f"and {len(tensions)} cross-cutting design tensions across {len(mapped_pkgs)} mapped packages "
        f"(unrecorded_external_facts={unrecorded_facts}, new_seeds_required={new_seeds})."
    )
    for d in shown_domains:
        print(
            f"  [{d['domain_id']}] {d['title']} | goals={d['goals_addressed']} "
            f"| reports={len(d['supplying_reports'])} | facts={len(d['quantitative_facts'])} "
            f"| gap={d['gap_classification']}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
