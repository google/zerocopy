#!/usr/bin/env python3
"""Read-only offline validation of the v26 333-row coverage revision."""

import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V25 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v25" / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
CHANGED = {"D03", "D07", "E07", "I020", "I076", "I080", "I113", "I125", "I148", "J01", "J02", "L02"}
EXPECTED_PACKAGES = {
    "I020": ["anneal-v2-cargo-root-selection-multipackage-2026-09-29", "anneal-v2-feature-subject-slug-collision-2026-09-29"],
    "I076": ["anneal-v2-feature-subject-slug-collision-2026-09-29"],
    "I080": ["anneal-3731-i080-incremental-target-layout-matrix-2026-09-29"],
    "I148": ["charon-zerocopy-library-repeat-order-nightly-2026-05-31"],
    "I113": ["anneal-3731-full-chain-transient-workspace-accounting-2026-09-29"],
    "I125": ["anneal-3731-i125-plugin-cwd-path-alias-v4-30-0-rc2"],
    "D03": ["anneal-3731-i080-incremental-target-layout-matrix-2026-09-29"],
    "D07": ["anneal-v2-feature-subject-slug-collision-2026-09-29"],
    "E07": ["charon-zerocopy-library-repeat-order-nightly-2026-05-31"],
    "J01": ["anneal-3731-full-chain-transient-workspace-accounting-2026-09-29"],
    "J02": ["anneal-3731-full-chain-transient-workspace-accounting-2026-09-29"],
    "L02": ["anneal-3731-full-chain-transient-workspace-accounting-2026-09-29"],
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def csv_rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    manifest = json.loads((HERE / "validation-v26.json").read_text())
    assert manifest["source_reference_package"] == V25.parent.name
    assert manifest["source_anneal_revision"] == "bd0956be95c5f798f0c0484921b9b9d1fc6e9988"
    assert (manifest["row_count"], manifest["investigation_count"], manifest["suggestion_count"], manifest["suggestion_destination_links"]) == (333, 159, 174, 345)
    assert manifest["changed_status_ids"] == []
    assert set(manifest["changed_residual_ids"]) == set(manifest["changed_prerequisite_ids"]) == set(manifest["new_evidence_ids"]) == CHANGED
    assert manifest["status_counts"] == {
        "investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
        "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4},
    }
    for name, expected in manifest["input_sha256"].items():
        path = V25 / name[4:] if name.startswith("v25/") else V22 / name[4:] if name.startswith("v22/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in manifest["generated_sha256"].items():
        assert sha(HERE / name) == expected, name

    prior = json.loads((V25 / "row-challenge-v25.json").read_text())
    current = json.loads((HERE / "row-challenge-v26.json").read_text())
    assert len(prior) == len(current) == 333
    assert len({row["id"] for row in current}) == 333
    for before, row in zip(prior, current):
        assert all(row[key] == value for key, value in before.items()), before["id"]
        assert row["v26_status"] == row["v25_status"]
        assert row["v26_gate_categories"] == row["v25_gate_categories"]
        assert row["v26_specific_remaining_delta"] and row["v26_next_prerequisite"]
        assert all((ROOT / path).is_file() for path in row["v26_evidence_files"]), row["id"]
        if row["id"] in CHANGED:
            assert row["v26_status"] == "partial"
            assert row["v26_new_evidence_packages"] == EXPECTED_PACKAGES[row["id"]]
            assert row["v26_review_package"] == HERE.parent.name
            assert row["v26_evidence_files"]
        else:
            assert row["v26_specific_remaining_delta"] == row["v25_specific_remaining_delta"]
            assert row["v26_next_prerequisite"] == row["v25_next_prerequisite"]
            assert row["v26_new_evidence_packages"] == []
            assert row["v26_evidence_files"] == []
    by_id = {row["id"]: row for row in current}
    assert {row["id"] for row in current if row["v26_specific_remaining_delta"] != row["v25_specific_remaining_delta"]} == CHANGED
    assert {row["id"] for row in current if row["v26_next_prerequisite"] != row["v25_next_prerequisite"]} == CHANGED
    assert "not an observed overwrite" in by_id["I076"]["v26_specific_remaining_delta"]
    assert "no edits or cancellations" in by_id["I080"]["v26_specific_remaining_delta"]
    assert "lower bound" in by_id["J02"]["v26_specific_remaining_delta"]
    assert "zero observed net change" in by_id["L02"]["v26_specific_remaining_delta"]
    assert "not loaded-binary attestation" in by_id["I125"]["v26_specific_remaining_delta"]
    assert "has_errors: true" in by_id["I148"]["v26_specific_remaining_delta"]
    assert "has_errors: true" in by_id["E07"]["v26_specific_remaining_delta"]
    assert by_id["D03"]["v26_new_evidence_packages"] == EXPECTED_PACKAGES["D03"]
    assert by_id["D07"]["v26_new_evidence_packages"] == EXPECTED_PACKAGES["D07"]
    for excluded in ("D05", "D06", "E06", "F20"):
        assert by_id[excluded]["v26_specific_remaining_delta"] == by_id[excluded]["v25_specific_remaining_delta"]
        assert by_id[excluded]["v26_next_prerequisite"] == by_id[excluded]["v25_next_prerequisite"]
        assert by_id[excluded]["v26_new_evidence_packages"] == []

    for filename, key, count in (("investigation-final-v26.csv", "id", 159), ("3730-crosswalk-final-v26.csv", "3730_id", 174)):
        old = csv_rows(V25 / filename.replace("-v26", "-v25"))
        rows = csv_rows(HERE / filename)
        assert len(old) == len(rows) == count
        assert [row[key] for row in rows] == [row[key] for row in old]
        for before, row in zip(old, rows):
            assert all(row[field] == value for field, value in before.items()), row[key]
            choice = by_id[row[key]]
            assert row["status"] == row["v26_status"] == choice["v26_status"]
            for field in ("v26_status", "v26_gate_categories", "v26_specific_remaining_delta", "v26_post_v25_scope_assessment", "v26_review_package", "v26_new_evidence_packages", "v26_evidence_files", "v26_next_prerequisite", "v26_evidence_relation"):
                value = choice[field]
                assert row[field] == (";".join(value) if isinstance(value, list) else value), (row[key], field)

    live = json.loads((HERE / "live-issue-snapshot-v26.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    v25_live = json.loads((V25 / "live-issue-hashes.json").read_text())["issues"]
    for number, state, comment_id in ((3730, "closed", 5884380373), (3731, "open", 5884299718)):
        key = str(number)
        item = live["issues"][key]
        assert item["number"] == number and item["state"] == state
        assert item["body"] == frozen[key]["body"]
        assert item["body_sha256"] == hashlib.sha256(item["body"].encode()).hexdigest() == v25_live[key]["body_sha256"]
        assert len(item["comments"]) == 1 and item["comments"][0]["id"] == comment_id
        comment = item["comments"][0]
        assert comment["body"] == frozen[key]["comments"][0]["body"]
        assert comment["body_sha256"] == hashlib.sha256(comment["body"].encode()).hexdigest() == v25_live[key]["comments"][0]["body_sha256"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (live["issues"]["3731"]["body"], live["issues"]["3731"]["comments"][0]["body"])
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", live["issues"]["3731"]["comments"][0]["body"])}
    assert len(titles) == 159 and len(cross) == 174
    investigation = csv_rows(HERE / "investigation-final-v26.csv")
    suggestions = csv_rows(HERE / "3730-crosswalk-final-v26.csv")
    assert all(row["title"] == titles[row["id"]] for row in investigation)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and set(row["3731_destinations"].split(";")) == cross[row["3730_id"]][1] for row in suggestions)
    assert sum(len(destinations) for _, destinations in cross.values()) == 345

    inventory = csv_rows(HERE / "source-package-inventory-v26.csv")
    assert len(inventory) == manifest["inventory_files"] == 133
    assert len({row["path"] for row in inventory}) == len(inventory)
    for row in inventory:
        assert sha(ROOT / row["path"]) == row["sha256"], row["path"]
    for package in manifest["source_packages"]:
        path = REPORTS / package
        assert (path / "REPORT.md").is_file() and (path / "REPORT.json").is_file()
        result = subprocess.run([sys.executable, "-B", str(path / "support/check.py")], cwd=ROOT, capture_output=True, text=True, timeout=90)
        assert result.returncode == 0, (package, result.stdout, result.stderr)
    print("PASS: v26 333 rows, 345 exact links, 12 bounded updates, six source checkers and 133 source files")


if __name__ == "__main__":
    main()
