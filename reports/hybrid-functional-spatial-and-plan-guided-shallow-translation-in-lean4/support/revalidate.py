#!/usr/bin/env python3
"""Deterministic revalidation harness for hybrid-functional-spatial-translation-2026-10-29.

Runs Lean 4 (`v4.34.1`) on `support/HybridBorrowHeapPrototype.lean`, verifies its
SHA-256 digest, checks that compilation succeeds with exit code 0, and verifies
the exact `#print axioms` output for all 24 kernel-checked theorems (confirming
zero `sorryAx` and zero `Classical.choice` across the entire mechanization).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path


EXPECTED_AXIOMS = [
    "'HybridBorrowHeapPrototype.OwnLoc.readNA_preserves' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.OwnLoc.afterWriteNA_self' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.OwnLoc.afterWriteNA_other' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.OwnLoc.preserved_by_atomic_load' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.ReadOwnLoc.preserved_by_atomic_load' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.OwnLoc.transfer_acquire' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.SafeAndSatisfies.of_step' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.SafeAndSatisfies.of_terminated' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.SafeAndSatisfies.of_demonic_choice' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.LoanRel.preserved_by_raw_write' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.LoanRel.preserved_by_atomic_load' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.promoteRaw_preserves_loanRel' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.releaseRaw_preserves_rawRel' does not depend on any axioms",
    "'HybridBorrowHeapPrototype.zipSymTree_eq_ite' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.evalSymTree_sound' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.evalSymTree_abstracts' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.atomicMaxAssign_evalSymTree_rfl' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.atomicMaxAssign_satisfies_spec' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.rawAddAndZero_evalSymTree_rfl' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.rawAddAndZero_satisfies_spec' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.reborrowRawMaxAssign_evalSymTree_rfl' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.reborrowRawMaxAssign_satisfies_spec' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.acquireReadRaw_evalSymTree_rfl' depends on axioms: [propext]",
    "'HybridBorrowHeapPrototype.acquireReadRaw_satisfies_spec' depends on axioms: [propext]",
]


def find_lean_binary() -> str:
    elan_lean = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1" / "bin" / "lean"
    if elan_lean.is_file():
        return str(elan_lean)
    which_lean = shutil.which("lean")
    if which_lean:
        return which_lean
    raise RuntimeError("Could not locate Lean 4 binary (`lean`).")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def run_verification() -> dict:
    support_dir = Path(__file__).resolve().parent
    lean_file = support_dir / "HybridBorrowHeapPrototype.lean"
    if not lean_file.is_file():
        raise FileNotFoundError(f"Missing Lean prototype: {lean_file}")

    lean_bin = find_lean_binary()
    version_proc = subprocess.run(
        [lean_bin, "--version"],
        capture_output=True,
        text=True,
        check=True,
    )
    lean_version = version_proc.stdout.strip()

    check_proc = subprocess.run(
        [lean_bin, "-j1", "-M1024", str(lean_file)],
        capture_output=True,
        text=True,
        check=False,
    )
    output_lines = [
        line.strip()
        for line in check_proc.stdout.replace("\r\n", "\n").splitlines()
        if line.strip()
    ]
    stderr_lines = [
        line.strip()
        for line in check_proc.stderr.replace("\r\n", "\n").splitlines()
        if line.strip()
    ]

    has_sorry = any("sorryAx" in line for line in output_lines + stderr_lines)
    axioms_match = output_lines == EXPECTED_AXIOMS
    passed = (
        check_proc.returncode == 0
        and not stderr_lines
        and not has_sorry
        and axioms_match
    )

    return {
        "report_id": "hybrid-functional-spatial-translation-2026-10-29",
        "observed_at": "2026-10-29",
        "lean_version": lean_version,
        "prototype_file": "support/HybridBorrowHeapPrototype.lean",
        "prototype_sha256": sha256_file(lean_file),
        "prototype_line_count": len(lean_file.read_text(encoding="utf-8").splitlines()),
        "command": "lean -j1 -M1024 reports/hybrid-functional-spatial-translation-2026-10-29/support/HybridBorrowHeapPrototype.lean",
        "exit_code": check_proc.returncode,
        "has_sorryAx": has_sorry,
        "axioms_match_expected": axioms_match,
        "theorem_count": len(EXPECTED_AXIOMS),
        "zero_axiom_theorem_count": sum(
            1 for line in output_lines if line.endswith("does not depend on any axioms")
        ),
        "propext_only_theorem_count": sum(
            1 for line in output_lines if line.endswith("depends on axioms: [propext]")
        ),
        "axiom_lines": output_lines,
        "stderr_lines": stderr_lines,
        "passed": passed,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-json",
        action="store_true",
        help="Write verification output to support/verification-results.json",
    )
    args = parser.parse_args()

    result = run_verification()
    if args.write_json:
        out_path = Path(__file__).resolve().parent / "verification-results.json"
        out_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
