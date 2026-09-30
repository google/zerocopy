#!/usr/bin/env python3
"""Offline v54 checker: inherited ledger, I079 direct, I031 context."""

import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V53 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v53" / "support"
PACKAGE = "anneal-3731-i079-symlink-module-identity-2026-09-30"
DIRECT = {"I079"}
CONTEXT = {"I031"}
FIELDS = (
    "v54_status", "v54_gate_categories", "v54_specific_remaining_delta",
    "v54_scope_assessment", "v54_review_package", "v54_new_evidence_packages",
    "v54_evidence_files", "v54_next_prerequisite", "v54_evidence_relation",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    validation = json.loads((HERE / "validation-v54.json").read_text())
    assert validation["reference_tip_at_start"] == "6b0acaee13124bc17bef31c764693836a93ff25a"
    assert validation["source_reference_package"] == V53.parent.name
    assert validation["issue_snapshot_relation"] == "fresh public REST fetch; issue fields unchanged from v53"
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
        path = V53 / name[4:] if name.startswith("v53/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name
    live=json.loads((HERE / "live-issue-snapshot-v54.json").read_text())
    earlier=json.loads((V53 / "live-issue-snapshot-v53.json").read_text())
    assert live["issues"] == earlier["issues"]
    assert live["fetched_at_utc"] != earlier["fetched_at_utc"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"

    previous = json.loads((V53 / "row-challenge-v53.json").read_text())
    current = json.loads((HERE / "row-challenge-v54.json").read_text())
    assert len(previous) == len(current) == 333
    assert [row["id"] for row in previous] == [row["id"] for row in current]
    by_id = {row["id"]: row for row in current}
    for old, row in zip(previous, current):
        item = row["id"]
        assert all(row[key] == value for key, value in old.items()), item
        assert row["v54_status"] == row["v53_status"]
        assert row["v54_gate_categories"] == row["v53_gate_categories"]
        assert row["v54_next_prerequisite"] == row["v53_next_prerequisite"]
        assert row["v54_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v54_evidence_files"]), item
        if item in DIRECT:
            assert row["v54_status"] == "partial" and row["v54_gate_categories"] == ["product"]
            assert row["v54_specific_remaining_delta"] != row["v53_specific_remaining_delta"]
            assert row["v54_new_evidence_packages"] == [PACKAGE]
            assert row["v54_evidence_files"]
            assert row["v54_evidence_relation"] == "direct bounded I079 LLBC lexical-alias file-identity evidence"
            assert row["v54_review_package"] == HERE.parent.name
        elif item in CONTEXT:
            assert row["v54_specific_remaining_delta"] == row["v53_specific_remaining_delta"]
            assert row["v54_new_evidence_packages"] == [PACKAGE]
            assert row["v54_evidence_relation"] == "bounded I031 Charon lexical-source context"
            assert row["v54_review_package"] == HERE.parent.name
        else:
            assert row["v54_specific_remaining_delta"] == row["v53_specific_remaining_delta"]
            assert row["v54_new_evidence_packages"] == row["v54_evidence_files"] == []
            assert row["v54_review_package"] == row["v53_review_package"]
            assert row["v54_evidence_relation"] == "no direct v54 evidence"
    assert {row["id"] for row in current if row["v54_specific_remaining_delta"] != row["v53_specific_remaining_delta"]} == DIRECT
    residual = by_id["I079"]["v54_specific_remaining_delta"]
    assert "A matched APFS same-inode symlink-alias versus distinct-inode physical-copy" in residual
    assert "six positional short_names leaves across three" in residual
    assert "does not establish cross-filesystem identity" in residual
    assert all(by_id[item]["v54_specific_remaining_delta"] ==
               by_id[item]["v53_specific_remaining_delta"] for item in CONTEXT)

    for new_name, old_name, key, count in (
        ("investigation-final-v54.csv", "investigation-final-v53.csv", "id", 159),
        ("3730-crosswalk-final-v54.csv", "3730-crosswalk-final-v53.csv", "3730_id", 174),
    ):
        new, old = rows(HERE / new_name), rows(V53 / old_name)
        assert len(new) == len(old) == count
        assert [row[key] for row in new] == [row[key] for row in old]
        for a, b in zip(new, old):
            assert all(a[field] == value for field, value in b.items()), a[key]
            source = by_id[a[key]]
            for field in FIELDS:
                value = source[field]
                assert a[field] == (";".join(value) if isinstance(value, list) else value)
            assert a["status"] == a["v54_status"]

    inventory = rows(HERE / "source-package-inventory-v54.csv")
    assert len(inventory) == validation["inventory_files"]
    assert set(validation["source_packages"]) == {V53.parent.name, PACKAGE}
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
    assert snapshot["identity"]["snapshot_sha256"] == sha(HERE / "live-issue-snapshot-v54.json")
    source_result = next(s for s in metadata["subjects"] if "results_sha256" in s["identity"])
    assert source_result["identity"]["results_sha256"] == sha(REPORTS / PACKAGE / "results.json")
    proc = subprocess.run([sys.executable, "-B", "check.py"], cwd=REPORTS / PACKAGE,
                          capture_output=True, text=True, timeout=10)
    assert proc.returncode == 0 and '"status": "pass"' in proc.stdout, (proc.stdout, proc.stderr)
    print("PASS: v54 inherited ledger, I079 direct, I031 context, sources and metadata")


if __name__ == "__main__":
    main()
