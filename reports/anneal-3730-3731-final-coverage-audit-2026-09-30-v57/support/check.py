#!/usr/bin/env python3
"""Offline v57 checker: inherited ledger, I062 direct, I025 context."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V56 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v56" / "support"
PACKAGE = "anneal-3731-i062-utf32-only-unicode-lsp-2026-09-30"
DIRECT = {"I062"}
CONTEXT = {"I025"}
FIELDS = (
    "v57_status", "v57_gate_categories", "v57_specific_remaining_delta",
    "v57_scope_assessment", "v57_review_package", "v57_new_evidence_packages",
    "v57_evidence_files", "v57_next_prerequisite", "v57_evidence_relation",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    validation = json.loads((HERE / "validation-v57.json").read_text())
    assert validation["reference_tip_at_start"] == "a5ecd5bde3d2b33457b5a13b4b435d79515f4012"
    assert validation["source_reference_package"] == V56.parent.name
    assert validation["issue_snapshot_relation"] == "fresh public REST fetch; issue fields unchanged from v56"
    assert (validation["row_count"], validation["investigation_count"],
            validation["suggestion_count"], validation["suggestion_destination_links"]) == (333, 159, 174, 345)
    assert validation["status_counts"] == {
        "investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
        "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4},
    }
    assert set(validation["changed_residual_ids"]) == set(validation["direct_evidence_ids"]) == DIRECT
    assert set(validation["bounded_context_ids"]) == CONTEXT
    assert validation["changed_status_ids"] == validation["changed_gate_ids"] == validation["changed_prerequisite_ids"] == []
    for name, expected in validation["input_sha256"].items():
        path = V56 / name[4:] if name.startswith("v56/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name
    live=json.loads((HERE / "live-issue-snapshot-v57.json").read_text())
    earlier=json.loads((V56 / "live-issue-snapshot-v56.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"

    previous = json.loads((V56 / "row-challenge-v56.json").read_text())
    current = json.loads((HERE / "row-challenge-v57.json").read_text())
    assert len(previous) == len(current) == 333
    assert [row["id"] for row in previous] == [row["id"] for row in current]
    by_id = {row["id"]: row for row in current}
    for old, row in zip(previous, current):
        item = row["id"]
        assert all(row[key] == value for key, value in old.items()), item
        assert row["v57_status"] == row["v56_status"]
        assert row["v57_gate_categories"] == row["v56_gate_categories"]
        assert row["v57_next_prerequisite"] == row["v56_next_prerequisite"]
        assert row["v57_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v57_evidence_files"]), item
        if item in DIRECT:
            assert row["v57_status"] == "partial" and row["v57_gate_categories"] == ["product"]
            assert row["v57_specific_remaining_delta"] != row["v56_specific_remaining_delta"]
            assert row["v57_new_evidence_packages"] == [PACKAGE]
            assert row["v57_evidence_files"]
            assert row["v57_evidence_relation"] == "direct bounded I062 UTF-32-only Lean LSP evidence"
            assert row["v57_review_package"] == HERE.parent.name
        elif item in CONTEXT:
            assert row["v57_specific_remaining_delta"] == row["v56_specific_remaining_delta"]
            assert row["v57_new_evidence_packages"] == [PACKAGE]
            assert row["v57_evidence_relation"] == "bounded I025 coordinate-context evidence"
            assert row["v57_review_package"] == HERE.parent.name
        else:
            assert row["v57_specific_remaining_delta"] == row["v56_specific_remaining_delta"]
            assert row["v57_new_evidence_packages"] == row["v57_evidence_files"] == []
            assert row["v57_review_package"] == row["v56_review_package"]
            assert row["v57_evidence_relation"] == "no direct v57 evidence"
    assert {row["id"] for row in current if row["v57_specific_remaining_delta"] != row["v56_specific_remaining_delta"]} == DIRECT
    residual = by_id["I062"]["v57_specific_remaining_delta"]
    assert "A direct Lean 4.30.0-rc2 UTF-32-only offer" in residual
    assert "UTF-16 columns 16-27 rather than scalar 15-26" in residual
    assert "complete post-edit buffer was not returned" in residual
    assert "does not prove selected UTF-32 or a protocol violation" in residual
    assert all(by_id[item]["v57_specific_remaining_delta"] ==
               by_id[item]["v56_specific_remaining_delta"] for item in CONTEXT)

    for new_name, old_name, key, count in (
        ("investigation-final-v57.csv", "investigation-final-v56.csv", "id", 159),
        ("3730-crosswalk-final-v57.csv", "3730-crosswalk-final-v56.csv", "3730_id", 174),
    ):
        new, old = rows(HERE / new_name), rows(V56 / old_name)
        assert len(new) == len(old) == count
        assert [row[key] for row in new] == [row[key] for row in old]
        for a, b in zip(new, old):
            assert all(a[field] == value for field, value in b.items()), a[key]
            source = by_id[a[key]]
            for field in FIELDS:
                value = source[field]
                assert a[field] == (";".join(value) if isinstance(value, list) else value)
            assert a["status"] == a["v57_status"]

    inventory = rows(HERE / "source-package-inventory-v57.csv")
    assert len(inventory) == validation["inventory_files"]
    assert set(validation["source_packages"]) == {V56.parent.name, PACKAGE}
    expected_paths = []
    for package in validation["source_packages"]:
        for path in sorted((REPORTS / package).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                expected_paths.append(path.relative_to(ROOT).as_posix())
    assert [row["path"] for row in inventory] == expected_paths
    assert all(sha(ROOT / row["path"]) == row["sha256"] for row in inventory)

    metadata = json.loads((HERE.parent / "REPORT.json").read_text())
    assert metadata["observed_at"] == "2026-09-30"
    snapshot = next(s for s in metadata["subjects"] if "snapshot_sha256" in s["identity"])
    assert snapshot["identity"]["snapshot_sha256"] == sha(HERE / "live-issue-snapshot-v57.json")
    source_result = next(s for s in metadata["subjects"] if "results_sha256" in s["identity"])
    assert source_result["identity"]["results_sha256"] == sha(REPORTS / PACKAGE / "results.json")
    proc = subprocess.run([sys.executable, "-B", "check.py"], cwd=REPORTS / PACKAGE,
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 0 and '"utf32_only"' in proc.stdout, (proc.stdout, proc.stderr)
    print("PASS: v57 inherited ledger, I062 direct, I025 context, sources and metadata")


if __name__ == "__main__":
    main()
