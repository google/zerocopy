#!/usr/bin/env python3
"""Offline v65 checker: inherited ledger, I092 direct and F07 context."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V64 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v64" / "support"
PACKAGE = "anneal-3731-i092-preseeded-valid-server-goal-2026-09-30"
DIRECT = {"I092"}
CONTEXT = {"F07"}
FIELDS = (
    "v65_status", "v65_gate_categories", "v65_specific_remaining_delta",
    "v65_scope_assessment", "v65_review_package", "v65_new_evidence_packages",
    "v65_evidence_files", "v65_next_prerequisite", "v65_evidence_relation",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    validation = json.loads((HERE / "validation-v65.json").read_text())
    assert validation["reference_tip_at_start"] == "e2692485db6b8417bf415c83223cfc5a99e73e4f"
    assert validation["source_reference_package"] == V64.parent.name
    assert validation["issue_snapshot_relation"] == "fresh public REST fetch; issue fields unchanged from v64"
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
        path = V64 / name[4:] if name.startswith("v64/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name
    live=json.loads((HERE / "live-issue-snapshot-v65.json").read_text())
    earlier=json.loads((V64 / "live-issue-snapshot-v64.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"

    previous = json.loads((V64 / "row-challenge-v64.json").read_text())
    current = json.loads((HERE / "row-challenge-v65.json").read_text())
    assert len(previous) == len(current) == 333
    assert [row["id"] for row in previous] == [row["id"] for row in current]
    by_id = {row["id"]: row for row in current}
    for old, row in zip(previous, current):
        item = row["id"]
        assert all(row[key] == value for key, value in old.items()), item
        assert row["v65_status"] == row["v64_status"]
        assert row["v65_gate_categories"] == row["v64_gate_categories"]
        assert row["v65_next_prerequisite"] == row["v64_next_prerequisite"]
        assert row["v65_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v65_evidence_files"]), item
        if item in DIRECT:
            assert row["v65_status"] == "partial" and row["v65_gate_categories"] == ["product"]
            assert row["v65_specific_remaining_delta"] != row["v64_specific_remaining_delta"]
            assert row["v65_new_evidence_packages"] == [PACKAGE]
            assert row["v65_evidence_files"]
            assert row["v65_evidence_relation"] == "direct bounded I092 preseeded valid-server goal evidence"
            assert row["v65_review_package"] == HERE.parent.name
        elif item in CONTEXT:
            assert row["v65_specific_remaining_delta"] == row["v64_specific_remaining_delta"]
            assert row["v65_new_evidence_packages"] == [PACKAGE]
            assert row["v65_evidence_relation"] == "bounded context evidence"
            assert row["v65_review_package"] == HERE.parent.name
        else:
            assert row["v65_specific_remaining_delta"] == row["v64_specific_remaining_delta"]
            assert row["v65_new_evidence_packages"] == row["v65_evidence_files"] == []
            assert row["v65_review_package"] == row["v64_review_package"]
            assert row["v65_evidence_relation"] == "no direct v65 evidence"
    assert {row["id"] for row in current if row["v65_specific_remaining_delta"] != row["v64_specific_remaining_delta"]} == DIRECT
    residual = by_id["I092"]["v65_specific_remaining_delta"]
    assert "live goal depValue = 7" in residual
    assert "29.8279% reclaimable RAM" in residual
    assert "no-dependency server did not run" in residual
    assert by_id["F07"]["v65_specific_remaining_delta"] == by_id["F07"]["v64_specific_remaining_delta"]

    for new_name, old_name, key, count in (
        ("investigation-final-v65.csv", "investigation-final-v64.csv", "id", 159),
        ("3730-crosswalk-final-v65.csv", "3730-crosswalk-final-v64.csv", "3730_id", 174),
    ):
        new, old = rows(HERE / new_name), rows(V64 / old_name)
        assert len(new) == len(old) == count
        assert [row[key] for row in new] == [row[key] for row in old]
        for a, b in zip(new, old):
            assert all(a[field] == value for field, value in b.items()), a[key]
            source = by_id[a[key]]
            for field in FIELDS:
                value = source[field]
                assert a[field] == (";".join(value) if isinstance(value, list) else value)
            assert a["status"] == a["v65_status"]

    inventory = rows(HERE / "source-package-inventory-v65.csv")
    assert len(inventory) == validation["inventory_files"]
    assert set(validation["source_packages"]) == {V64.parent.name, PACKAGE}
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
    assert snapshot["identity"]["snapshot_sha256"] == sha(HERE / "live-issue-snapshot-v65.json")
    source_result = next(s for s in metadata["subjects"] if "results_sha256" in s["identity"])
    assert source_result["identity"]["results_sha256"] == sha(REPORTS / PACKAGE / "results.json")
    proc = subprocess.run([sys.executable, "-B", "check.py"], cwd=REPORTS / PACKAGE,
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 0 and "PASS: preseeded valid server goal" in proc.stdout, (proc.stdout, proc.stderr)
    print("PASS: v65 inherited ledger, I092 direct, F07 context, sources and metadata")


if __name__ == "__main__":
    main()
