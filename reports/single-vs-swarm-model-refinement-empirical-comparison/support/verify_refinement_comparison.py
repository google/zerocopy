#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible verification and audit script for the single-agent vs. swarm
conceptual model refinement empirical comparison report package.

Validates:
1. REPORT.json schema, lexicographically sorted kebab-case topics, subjects, and
   ISO 8601 observed_at date.
2. REPORT.md top-level section ordering, Basis role declarations, 80-column
   prose wrapping, and absence of ephemeral scratch or conversation paths.
3. support/refinement_defects_and_metrics.json structural and quantitative
   invariants across the 5 macro-architectural simplifications (M-1..M-5),
   the 12 micro-semantic/soundness/audit defects (D-01..D-12), the holdout
   reclassification and exposure accounting (D1..D10, H1..H10, R1..R4), and
   the multi-pass regression transition matrix.
4. Optional live git blob verification (--anneal-repo or ANNEAL_REPO) checking
   exact line counts, byte sizes, SHA-256 digests, and source patterns at
   commits 572f1e80580daa4b052ce5646bb675484d9bb957 and
   d79b0c070cf4115b523fe6ee62c1e72504de2254.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


REQUIRED_SECTIONS = [
    "## Summary",
    "## Applicability",
    "## Findings",
    "## Boundaries",
    "## Evidence",
    "## Revalidation",
]

ALLOWED_BASIS_ROLES = {
    "normative",
    "documentation",
    "source",
    "execution",
    "derived",
}

ALLOWED_SUBJECT_KINDS = {
    "repository",
    "specification",
    "toolchain",
    "library",
    "platform",
    "concept",
}

KEBAB_RE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*(/[a-z0-9]+(-[a-z0-9]+)*)*$")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", file=sys.stderr)
    sys.exit(1)


def verify_report_json(pkg_dir: Path) -> dict:
    report_json_path = pkg_dir / "REPORT.json"
    if not report_json_path.is_file():
        fail(f"Missing {report_json_path}")
    data = json.loads(report_json_path.read_text(encoding="utf-8"))

    for key in ("topics", "subjects", "observed_at"):
        if key not in data:
            fail(f"REPORT.json missing required key: {key}")

    topics = data["topics"]
    if not isinstance(topics, list) or not topics:
        fail("REPORT.json topics must be a non-empty list")
    for t in topics:
        if not isinstance(t, str) or not KEBAB_RE.match(t):
            fail(f"Invalid topic format in REPORT.json: {t!r}")
    if topics != sorted(set(topics)):
        fail("REPORT.json topics must be sorted lexicographically without duplicates")

    subjects = data["subjects"]
    if not isinstance(subjects, list) or not subjects:
        fail("REPORT.json subjects must be a non-empty list")
    revisions_seen = set()
    for s in subjects:
        if not s.get("name"):
            fail("Subject in REPORT.json missing 'name'")
        ident = s.get("identity")
        if not isinstance(ident, dict) or not ident:
            fail("Subject in REPORT.json missing non-empty 'identity' dict")
        if ident.get("kind") not in ALLOWED_SUBJECT_KINDS:
            fail(f"Invalid subject kind in REPORT.json: {ident.get('kind')!r}")
        if "revision" in ident:
            revisions_seen.add(ident["revision"])

    for req_rev in (
        "d79b0c070cf4115b523fe6ee62c1e72504de2254",
        "f2bc17e9be87b777d63c785b31f3370ff058d69b",
    ):
        if req_rev not in revisions_seen:
            fail(f"REPORT.json subjects missing required Anneal revision {req_rev}")

    if not DATE_RE.match(str(data["observed_at"])):
        fail(f"Invalid observed_at date in REPORT.json: {data['observed_at']!r}")

    return data


def verify_report_md(pkg_dir: Path) -> None:
    report_md_path = pkg_dir / "REPORT.md"
    if not report_md_path.is_file():
        fail(f"Missing {report_md_path}")
    text = report_md_path.read_text(encoding="utf-8")
    lines = text.splitlines()

    if not lines or not lines[0].startswith("# "):
        fail("REPORT.md must start with a level-1 '# Title' heading")

    for forbidden in ("/scratch/", "conversation:" + "//", "/usr/local/" + "google/"):
        if forbidden in text:
            fail(f"REPORT.md contains forbidden ephemeral path or link: {forbidden!r}")

    top_sections = [line.strip() for line in lines if line.startswith("## ")]
    if top_sections != REQUIRED_SECTIONS:
        fail(
            f"REPORT.md top-level sections {top_sections} do not match "
            f"required order {REQUIRED_SECTIONS}"
        )

    # Verify every '### Finding' heading is followed by a valid 'Basis:' line.
    finding_indices = [
        i for i, line in enumerate(lines) if line.startswith("### Finding ")
    ]
    if len(finding_indices) < 4:
        fail(f"Expected at least 4 findings in REPORT.md, found {len(finding_indices)}")

    for idx in finding_indices:
        # Look for Basis: within the next 3 lines.
        window = lines[idx + 1 : idx + 4]
        basis_lines = [w for w in window if w.startswith("Basis:")]
        if not basis_lines:
            fail(f"Finding at line {idx + 1} ({lines[idx]}) missing 'Basis:' line")
        roles_raw = basis_lines[0].split("Basis:", 1)[1].strip()
        roles = [r.strip() for r in roles_raw.split(",") if r.strip()]
        if not roles or any(r not in ALLOWED_BASIS_ROLES for r in roles):
            fail(
                f"Invalid Basis roles at line {idx + 1}: {roles!r} "
                f"(allowed: {sorted(ALLOWED_BASIS_ROLES)})"
            )

    # Check 80-column prose wrapping outside code blocks and Markdown tables.
    in_code_block = False
    for lineno, line in enumerate(lines, start=1):
        if line.strip().startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue
        if line.lstrip().startswith("|"):
            continue
        if line.startswith("#"):
            continue
        if len(line) > 80:
            fail(
                f"REPORT.md line {lineno} exceeds 80 columns "
                f"({len(line)} cols): {line!r}"
            )


def verify_dataset(pkg_dir: Path) -> dict:
    dataset_path = pkg_dir / "support" / "refinement_defects_and_metrics.json"
    if not dataset_path.is_file():
        fail(f"Missing {dataset_path}")
    data = json.loads(dataset_path.read_text(encoding="utf-8"))

    # Verify baseline repository metrics.
    revs = data["baseline_repository_metrics"]["revisions"]
    rev_572 = revs["572f1e80580daa4b052ce5646bb675484d9bb957"]
    rev_d79 = revs["d79b0c070cf4115b523fe6ee62c1e72504de2254"]
    if len(rev_572) != 16:
        fail(f"Expected 16 tracked files at 572f1e80, found {len(rev_572)}")
    if len(rev_d79) != 3:
        fail(f"Expected 3 tracked files at d79b0c07, found {len(rev_d79)}")

    agg = data["baseline_repository_metrics"]["aggregates_572f1e80"]
    trusted_lean = sum(
        v["lines"] for k, v in rev_572.items() if k.startswith("trusted/lean/")
    )
    trusted_capture = sum(
        v["lines"]
        for k, v in rev_572.items()
        if k.startswith("trusted/rustc-capture/")
    )
    trusted_audit = rev_572["trusted/audit/TrustedBoundary.lean"]["lines"]
    trusted_cargo = rev_572["trusted/cargo-anneal/src/lib.rs"]["lines"]
    theory_lines = sum(
        v["lines"] for k, v in rev_572.items() if k.startswith("theory/")
    )
    if (
        trusted_lean != agg["trusted_lean_lines"]
        or trusted_capture != agg["trusted_rustc_capture_lines"]
        or trusted_audit != agg["trusted_audit_lines"]
        or trusted_cargo != agg["trusted_cargo_anneal_lines"]
        or (trusted_lean + trusted_capture + trusted_audit + trusted_cargo)
        != agg["total_trusted_lines"]
        or theory_lines != agg["theory_anneal_lines"]
    ):
        fail("Aggregate line counts in dataset do not match per-file line sums")

    # Verify the 5 macro-architectural simplifications.
    macros = data["macro_architectural_simplifications"]
    if [m["id"] for m in macros] != ["M-1", "M-2", "M-3", "M-4", "M-5"]:
        fail("Expected macro simplifications M-1 through M-5 in exact order")

    # Verify the 12 micro-semantic, soundness, completeness, and audit defects.
    defects = data["defect_discovery_matrix"]
    expected_ids = [f"D-{i:02d}" for i in range(1, 13)]
    if [d["id"] for d in defects] != expected_ids:
        fail(f"Expected defect IDs {expected_ids}, found {[d['id'] for d in defects]}")

    for d in defects:
        if d["swarm_lifecycle"]["candidate_003_state"] != "resolved":
            fail(f"Defect {d['id']} not marked resolved in Candidate 003")
        if d["single_agent_m3_prime_status"] not in {
            "missed",
            "introduced",
            "unaddressed-prerequisite",
        }:
            fail(f"Unexpected single-agent status on {d['id']}")

    # Verify holdout stitcher accounting.
    stitcher = data["mechanism_attribution"]["holdout_stitcher_and_exposure_accounting"]
    if len(stitcher["discovery_set"]) != 10:
        fail("Expected 10 discovery set items (D1..D10)")
    if len(stitcher["blind_holdout_set"]) != 10:
        fail("Expected 10 blind holdout items (H1..H10)")
    if len(stitcher["reserve_holdout_set"]) != 4:
        fail("Expected 4 reserve holdout items (R1..R4)")
    if (
        stitcher["pass_0_reclassification_audit"]["reclassified_to_discovery_count"]
        != 6
    ):
        fail("Expected 6 initial holdouts reclassified to discovery during Pass 0")

    p1 = stitcher["pass_evaluations"]["pass_1"]
    p2 = stitcher["pass_evaluations"]["pass_2"]
    p3 = stitcher["pass_evaluations"]["pass_3"]
    if (
        p1["holdouts_passed"] + p1["holdouts_partial"] + p1["holdouts_failed"] != 10
        or p2["holdouts_passed"] + p2["holdouts_partial"] + p2["holdouts_failed"] != 10
        or p3["holdouts_passed"] != 10
        or p3["reserve_holdouts_passed"] != 4
    ):
        fail("Holdout Stitcher pass evaluation counts do not sum to 10 (and 4 reserve)")

    # Verify multi-pass regression transition matrix.
    matrix = data["mechanism_attribution"]["multi_pass_regression_transition_matrix"]
    if (
        matrix["pass_0_baseline_and_single_agent_m3_prime"]["count_active"] != 10
        or matrix["pass_1_candidate_001"]["count_active"] != 9
        or matrix["pass_1_candidate_001"]["count_newly_introduced"] != 7
        or matrix["pass_2_candidate_002"]["count_active"] != 6
        or matrix["pass_2_candidate_002"]["count_newly_introduced"] != 3
        or matrix["pass_3_candidate_003"]["count_active"] != 0
    ):
        fail("Multi-pass regression transition matrix counts inconsistent")

    return data


def verify_live_anneal_repo(repo_path: Path, dataset: dict) -> None:
    revs = dataset["baseline_repository_metrics"]["revisions"]
    for commit, files in revs.items():
        for rel_path, expected in files.items():
            try:
                blob = subprocess.check_output(
                    ["git", "-C", str(repo_path), "show", f"{commit}:{rel_path}"],
                    stderr=subprocess.STDOUT,
                )
            except subprocess.CalledProcessError as exc:
                fail(f"git show {commit}:{rel_path} failed: {exc.output.decode()}")

            actual_lines = blob.count(b"\n")
            actual_bytes = len(blob)
            actual_sha256 = hashlib.sha256(blob).hexdigest()
            if (
                actual_lines != expected["lines"]
                or actual_bytes != expected["bytes"]
                or actual_sha256 != expected["sha256"]
            ):
                fail(
                    f"Mismatch for {commit}:{rel_path}: "
                    f"expected {expected}, got lines={actual_lines}, "
                    f"bytes={actual_bytes}, sha256={actual_sha256}"
                )

    # Verify concrete source patterns cited in Findings 1 and 2 at 572f1e80.
    c_572 = "572f1e80580daa4b052ce5646bb675484d9bb957"
    extract_rs = subprocess.check_output(
        ["git", "-C", str(repo_path), "show", f"{c_572}:trusted/rustc-capture/src/extract.rs"]
    ).decode("utf-8")
    if "Ok(ir::Rvalue::Field0(local_index(l)))" not in extract_rs:
        fail("Expected Field0 partial-move pattern in extract.rs")

    mir_sem = subprocess.check_output(
        ["git", "-C", str(repo_path), "show", f"{c_572}:trusted/lean/Trusted/MirSemantics.lean"]
    ).decode("utf-8")
    for snippet in (
        "opaque TargetSem",
        "def AdmissibleAdtInv",
        "inner.valid adts defaultAdtInv s 0 payload",
        "| [] => .terminated (.normal ⟨retVal, s⟩)",
    ):
        if snippet not in mir_sem:
            fail(f"Expected snippet {snippet!r} in Trusted/MirSemantics.lean")

    boundary = subprocess.check_output(
        ["git", "-C", str(repo_path), "show", f"{c_572}:trusted/audit/TrustedBoundary.lean"]
    ).decode("utf-8")
    for snippet in (
        "Excludes `unsafe`, `partial`, `meta`, `nonrec`, `openScoped`, `derivingClass`",
        "def allowedCommandSyntaxKinds : List Name :=",
        "def allowedNotationSyntaxKinds : List Name :=",
        "`«term_∈_»",
    ):
        if snippet not in boundary:
            fail(f"Expected syntax-audit snippet {snippet!r} in TrustedBoundary.lean")
    for forbidden_notation in ("`«term-_»", "`«term_^_»", "`«term_∉_»"):
        if forbidden_notation in boundary:
            fail(
                f"Expected {forbidden_notation!r} to be excluded from "
                "allowedNotationSyntaxKinds in TrustedBoundary.lean"
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--anneal-repo",
        type=Path,
        default=os.environ.get("ANNEAL_REPO"),
        help="Optional path to a joshlf/anneal git checkout for live blob verification.",
    )
    args = parser.parse_args()

    pkg_dir = Path(__file__).resolve().parent.parent
    verify_report_json(pkg_dir)
    verify_report_md(pkg_dir)
    dataset = verify_dataset(pkg_dir)

    live_status = "skipped (standalone mode)"
    if args.anneal_repo and Path(args.anneal_repo).is_dir():
        verify_live_anneal_repo(Path(args.anneal_repo), dataset)
        live_status = f"verified 19 git blobs and source patterns in {args.anneal_repo}"

    print("[OK] REPORT.json schema, topics, subjects, and observed_at validated.")
    print("[OK] REPORT.md section order, Basis labels, 80-col wrapping, and path hygiene validated.")
    print(
        "[OK] support/refinement_defects_and_metrics.json validated "
        "(5/5 macro-simplifications, 12/12 micro-defects, 24 discovery/holdout/reserve cases)."
    )
    print(f"[OK] Live repository verification: {live_status}.")


if __name__ == "__main__":
    main()
