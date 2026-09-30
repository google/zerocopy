#!/usr/bin/env python3
"""Offline v47 checker: inherited ledger, source package and two direct rows."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V46 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v46" / "support"
PACKAGE = "anneal-3731-i076-sequential-shared-destination-2026-09-30"
DIRECT = {"I020", "I076"}
CONTEXT = {"D07"}
FIELDS = (
    "v47_status", "v47_gate_categories", "v47_specific_remaining_delta",
    "v47_scope_assessment", "v47_review_package", "v47_new_evidence_packages",
    "v47_evidence_files", "v47_next_prerequisite", "v47_evidence_relation",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    validation = json.loads((HERE / "validation-v47.json").read_text())
    assert validation["reference_tip_at_start"] == "24eb9c0b5896c54d24884755f68dfe5b8b077d20"
    assert validation["source_reference_package"] == V46.parent.name
    assert validation["issue_snapshot_relation"] == "exact inherited v46 snapshot; no fresh fetch"
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
        path = V46 / name[4:] if name.startswith("v46/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name
    assert json.loads((HERE / "live-issue-snapshot-v47.json").read_text()) == json.loads(
        (V46 / "live-issue-snapshot-v46.json").read_text())

    previous = json.loads((V46 / "row-challenge-v46.json").read_text())
    current = json.loads((HERE / "row-challenge-v47.json").read_text())
    assert len(previous) == len(current) == 333
    assert [row["id"] for row in previous] == [row["id"] for row in current]
    by_id = {row["id"]: row for row in current}
    for old, row in zip(previous, current):
        item = row["id"]
        assert all(row[key] == value for key, value in old.items()), item
        assert row["v47_status"] == row["v46_status"]
        assert row["v47_gate_categories"] == row["v46_gate_categories"]
        assert row["v47_next_prerequisite"] == row["v46_next_prerequisite"]
        assert row["v47_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v47_evidence_files"]), item
        if item in DIRECT:
            assert row["v47_status"] == "partial" and row["v47_gate_categories"] == ["product"]
            assert row["v47_specific_remaining_delta"] != row["v46_specific_remaining_delta"]
            assert row["v47_new_evidence_packages"] == [PACKAGE]
            assert row["v47_evidence_files"]
            assert row["v47_evidence_relation"] == "direct bounded sequential Charon destination evidence"
            assert row["v47_review_package"] == HERE.parent.name
        elif item in CONTEXT:
            assert row["v47_specific_remaining_delta"] == row["v46_specific_remaining_delta"]
            assert row["v47_new_evidence_packages"] == [PACKAGE]
            assert row["v47_evidence_relation"] == "bounded sequential Charon destination context"
            assert row["v47_review_package"] == HERE.parent.name
        else:
            assert row["v47_specific_remaining_delta"] == row["v46_specific_remaining_delta"]
            assert row["v47_new_evidence_packages"] == row["v47_evidence_files"] == []
            assert row["v47_review_package"] == row["v46_review_package"]
            assert row["v47_evidence_relation"] == "no direct v47 evidence"
    assert {row["id"] for row in current if row["v47_specific_remaining_delta"] != row["v46_specific_remaining_delta"]} == DIRECT
    assert "sequential Charon probe" in by_id["I020"]["v47_specific_remaining_delta"]
    assert "serial Charon cell" in by_id["I076"]["v47_specific_remaining_delta"]

    for new_name, old_name, key, count in (
        ("investigation-final-v47.csv", "investigation-final-v46.csv", "id", 159),
        ("3730-crosswalk-final-v47.csv", "3730-crosswalk-final-v46.csv", "3730_id", 174),
    ):
        new, old = rows(HERE / new_name), rows(V46 / old_name)
        assert len(new) == len(old) == count
        assert [row[key] for row in new] == [row[key] for row in old]
        for a, b in zip(new, old):
            assert all(a[field] == value for field, value in b.items()), a[key]
            source = by_id[a[key]]
            for field in FIELDS:
                value = source[field]
                assert a[field] == (";".join(value) if isinstance(value, list) else value)
            assert a["status"] == a["v47_status"]

    inventory = rows(HERE / "source-package-inventory-v47.csv")
    assert len(inventory) == validation["inventory_files"]
    assert set(validation["source_packages"]) == {V46.parent.name, PACKAGE}
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
    assert snapshot["identity"]["snapshot_sha256"] == sha(HERE / "live-issue-snapshot-v47.json")
    source_result = next(s for s in metadata["subjects"] if "results_sha256" in s["identity"])
    assert source_result["identity"]["results_sha256"] == sha(REPORTS / PACKAGE / "support/results.json")
    proc = subprocess.run([sys.executable, "-B", "support/check.py"], cwd=REPORTS / PACKAGE,
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 0 and "PASS:" in proc.stdout, (proc.stdout, proc.stderr)
    print("PASS: v47 inherited ledger, two direct residuals, D07 context, sources and metadata")


if __name__ == "__main__":
    main()
