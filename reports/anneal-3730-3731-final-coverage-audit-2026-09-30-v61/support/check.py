#!/usr/bin/env python3
"""Offline v61 checker: inherited ledger, I090 direct and F05 context."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V60 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v60" / "support"
PACKAGE = "anneal-3731-i090-lake-version-only-identity-2026-09-30"
DIRECT = {"I090"}
CONTEXT = {"F05"}
FIELDS = (
    "v61_status", "v61_gate_categories", "v61_specific_remaining_delta",
    "v61_scope_assessment", "v61_review_package", "v61_new_evidence_packages",
    "v61_evidence_files", "v61_next_prerequisite", "v61_evidence_relation",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    validation = json.loads((HERE / "validation-v61.json").read_text())
    assert validation["reference_tip_at_start"] == "97677918e2120591c57486a353ee1b75e2f0bd6f"
    assert validation["source_reference_package"] == V60.parent.name
    assert validation["issue_snapshot_relation"] == "fresh public REST fetch; issue fields unchanged from v60"
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
        path = V60 / name[4:] if name.startswith("v60/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name
    live=json.loads((HERE / "live-issue-snapshot-v61.json").read_text())
    earlier=json.loads((V60 / "live-issue-snapshot-v60.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"

    previous = json.loads((V60 / "row-challenge-v60.json").read_text())
    current = json.loads((HERE / "row-challenge-v61.json").read_text())
    assert len(previous) == len(current) == 333
    assert [row["id"] for row in previous] == [row["id"] for row in current]
    by_id = {row["id"]: row for row in current}
    for old, row in zip(previous, current):
        item = row["id"]
        assert all(row[key] == value for key, value in old.items()), item
        assert row["v61_status"] == row["v60_status"]
        assert row["v61_gate_categories"] == row["v60_gate_categories"]
        assert row["v61_next_prerequisite"] == row["v60_next_prerequisite"]
        assert row["v61_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v61_evidence_files"]), item
        if item in DIRECT:
            assert row["v61_status"] == "partial" and row["v61_gate_categories"] == ["product"]
            assert row["v61_specific_remaining_delta"] != row["v60_specific_remaining_delta"]
            assert row["v61_new_evidence_packages"] == [PACKAGE]
            assert row["v61_evidence_files"]
            assert row["v61_evidence_relation"] == "direct bounded I090 Lake package-version identity evidence"
            assert row["v61_review_package"] == HERE.parent.name
        elif item in CONTEXT:
            assert row["v61_specific_remaining_delta"] == row["v60_specific_remaining_delta"]
            assert row["v61_new_evidence_packages"] == [PACKAGE]
            assert row["v61_evidence_relation"] == "bounded context evidence"
            assert row["v61_review_package"] == HERE.parent.name
        else:
            assert row["v61_specific_remaining_delta"] == row["v60_specific_remaining_delta"]
            assert row["v61_new_evidence_packages"] == row["v61_evidence_files"] == []
            assert row["v61_review_package"] == row["v60_review_package"]
            assert row["v61_evidence_relation"] == "no direct v61 evidence"
    assert {row["id"] for row in current if row["v61_specific_remaining_delta"] != row["v60_specific_remaining_delta"]} == DIRECT
    residual = by_id["I090"]["v61_specific_remaining_delta"]
    assert "producer package version 1.0.0→2.0.0→1.0.0" in residual
    assert "Dep.olean and consumer Generated.olean bytes" in residual
    assert "real archive still need Anneal producer/consumer" in residual
    assert by_id["F05"]["v61_specific_remaining_delta"] == by_id["F05"]["v60_specific_remaining_delta"]

    for new_name, old_name, key, count in (
        ("investigation-final-v61.csv", "investigation-final-v60.csv", "id", 159),
        ("3730-crosswalk-final-v61.csv", "3730-crosswalk-final-v60.csv", "3730_id", 174),
    ):
        new, old = rows(HERE / new_name), rows(V60 / old_name)
        assert len(new) == len(old) == count
        assert [row[key] for row in new] == [row[key] for row in old]
        for a, b in zip(new, old):
            assert all(a[field] == value for field, value in b.items()), a[key]
            source = by_id[a[key]]
            for field in FIELDS:
                value = source[field]
                assert a[field] == (";".join(value) if isinstance(value, list) else value)
            assert a["status"] == a["v61_status"]

    inventory = rows(HERE / "source-package-inventory-v61.csv")
    assert len(inventory) == validation["inventory_files"]
    assert set(validation["source_packages"]) == {V60.parent.name, PACKAGE}
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
    assert snapshot["identity"]["snapshot_sha256"] == sha(HERE / "live-issue-snapshot-v61.json")
    source_result = next(s for s in metadata["subjects"] if "results_sha256" in s["identity"])
    assert source_result["identity"]["results_sha256"] == sha(REPORTS / PACKAGE / "results.json")
    proc = subprocess.run([sys.executable, "-B", "check.py"], cwd=REPORTS / PACKAGE,
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 0 and "PASS: 5 cells" in proc.stdout, (proc.stdout, proc.stderr)
    print("PASS: v61 inherited ledger, I090 direct, F05 context, sources and metadata")


if __name__ == "__main__":
    main()
