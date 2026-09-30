#!/usr/bin/env python3
"""Offline v51 checker: inherited ledger, I062 direct, B03/I025 context."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V50 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v50" / "support"
PACKAGE = "anneal-3731-i062-utf8-only-unicode-lsp-2026-09-30"
DIRECT = {"I062"}
CONTEXT = {"B03", "I025"}
FIELDS = (
    "v51_status", "v51_gate_categories", "v51_specific_remaining_delta",
    "v51_scope_assessment", "v51_review_package", "v51_new_evidence_packages",
    "v51_evidence_files", "v51_next_prerequisite", "v51_evidence_relation",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    validation = json.loads((HERE / "validation-v51.json").read_text())
    assert validation["reference_tip_at_start"] == "ebfeac694e945da0b52e09c6a185d857f982f4f3"
    assert validation["source_reference_package"] == V50.parent.name
    assert validation["issue_snapshot_relation"] == "exact inherited v50 snapshot; no fresh fetch"
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
        path = V50 / name[4:] if name.startswith("v50/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name
    assert json.loads((HERE / "live-issue-snapshot-v51.json").read_text()) == json.loads(
        (V50 / "live-issue-snapshot-v50.json").read_text())

    previous = json.loads((V50 / "row-challenge-v50.json").read_text())
    current = json.loads((HERE / "row-challenge-v51.json").read_text())
    assert len(previous) == len(current) == 333
    assert [row["id"] for row in previous] == [row["id"] for row in current]
    by_id = {row["id"]: row for row in current}
    for old, row in zip(previous, current):
        item = row["id"]
        assert all(row[key] == value for key, value in old.items()), item
        assert row["v51_status"] == row["v50_status"]
        assert row["v51_gate_categories"] == row["v50_gate_categories"]
        assert row["v51_next_prerequisite"] == row["v50_next_prerequisite"]
        assert row["v51_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v51_evidence_files"]), item
        if item in DIRECT:
            assert row["v51_status"] == "partial" and row["v51_gate_categories"] == ["product"]
            assert row["v51_specific_remaining_delta"] != row["v50_specific_remaining_delta"]
            assert row["v51_new_evidence_packages"] == [PACKAGE]
            assert row["v51_evidence_files"]
            assert row["v51_evidence_relation"] == "direct bounded Unicode Lean LSP encoding evidence"
            assert row["v51_review_package"] == HERE.parent.name
        elif item in CONTEXT:
            assert row["v51_specific_remaining_delta"] == row["v50_specific_remaining_delta"]
            assert row["v51_new_evidence_packages"] == [PACKAGE]
            assert row["v51_evidence_relation"] == "bounded Unicode Lean LSP encoding context"
            assert row["v51_review_package"] == HERE.parent.name
        else:
            assert row["v51_specific_remaining_delta"] == row["v50_specific_remaining_delta"]
            assert row["v51_new_evidence_packages"] == row["v51_evidence_files"] == []
            assert row["v51_review_package"] == row["v50_review_package"]
            assert row["v51_evidence_relation"] == "no direct v51 evidence"
    assert {row["id"] for row in current if row["v51_specific_remaining_delta"] != row["v50_specific_remaining_delta"]} == DIRECT
    residual = by_id["I062"]["v51_specific_remaining_delta"]
    assert "UTF-16 columns 16-27" in residual
    assert "UTF-8 byte columns 19-30" in residual
    assert "protocol violation" in residual
    assert all(by_id[item]["v51_specific_remaining_delta"] ==
               by_id[item]["v50_specific_remaining_delta"] for item in CONTEXT)

    for new_name, old_name, key, count in (
        ("investigation-final-v51.csv", "investigation-final-v50.csv", "id", 159),
        ("3730-crosswalk-final-v51.csv", "3730-crosswalk-final-v50.csv", "3730_id", 174),
    ):
        new, old = rows(HERE / new_name), rows(V50 / old_name)
        assert len(new) == len(old) == count
        assert [row[key] for row in new] == [row[key] for row in old]
        for a, b in zip(new, old):
            assert all(a[field] == value for field, value in b.items()), a[key]
            source = by_id[a[key]]
            for field in FIELDS:
                value = source[field]
                assert a[field] == (";".join(value) if isinstance(value, list) else value)
            assert a["status"] == a["v51_status"]

    inventory = rows(HERE / "source-package-inventory-v51.csv")
    assert len(inventory) == validation["inventory_files"]
    assert set(validation["source_packages"]) == {V50.parent.name, PACKAGE}
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
    assert snapshot["identity"]["snapshot_sha256"] == sha(HERE / "live-issue-snapshot-v51.json")
    source_result = next(s for s in metadata["subjects"] if "results_sha256" in s["identity"])
    assert source_result["identity"]["results_sha256"] == sha(REPORTS / PACKAGE / "results.json")
    proc = subprocess.run([sys.executable, "-B", "check.py"], cwd=REPORTS / PACKAGE,
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 0 and "batch_exits" in proc.stdout, (proc.stdout, proc.stderr)
    print("PASS: v51 inherited ledger, I062 direct, B03/I025 context, sources and metadata")


if __name__ == "__main__":
    main()
