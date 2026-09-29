#!/usr/bin/env python3
"""Read-only offline checker for v28's 333 inherited rows and four sources."""
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
V27 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v27" / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
CHANGED = {"I012", "I038", "I041", "I089", "I092", "I099", "C09", "C11", "F07", "F08", "F19", "I04"}
CONTEXT = {"B15", "C01", "I042", "I045", "I039", "I091", "I131", "I132", "I134", "F02", "F04", "F13", "F20", "I02"}
PACKAGES = {
    "I012": ["lean-lsp-open-buffer-path-disappearance-v4-30-0-rc2"],
    "I038": ["lean-unsaved-cross-module-import-v4-30-0-rc2", "lean-lake-unsaved-cross-module-import-v4-30-0-rc2"],
    "C11": ["lean-unsaved-cross-module-import-v4-30-0-rc2", "lean-lake-unsaved-cross-module-import-v4-30-0-rc2"],
    "I041": ["lean-lsp-cross-version-goal-completion-v4-30-0-rc2"],
    "C09": ["lean-lsp-cross-version-goal-completion-v4-30-0-rc2"],
    **{key: ["anneal-3731-lake-fresh-cache-consumer-matrix-2026-09-29"] for key in ("I089", "I092", "I099", "F07", "F08", "F19", "I04")},
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))

def main():
    validation = json.loads((HERE / "validation-v28.json").read_text())
    assert validation["reference_tip_at_start"] == "1b67b6b87b3266f1f798cd825de9988e297b5822"
    assert validation["source_reference_package"] == V27.parent.name
    assert validation["source_anneal_revision"] == "bd0956be95c5f798f0c0484921b9b9d1fc6e9988"
    assert (validation["row_count"], validation["investigation_count"], validation["suggestion_count"], validation["suggestion_destination_links"]) == (333, 159, 174, 345)
    assert validation["changed_status_ids"] == validation["changed_gate_ids"] == []
    assert set(validation["changed_residual_ids"]) == set(validation["changed_prerequisite_ids"]) == set(validation["direct_evidence_ids"]) == CHANGED
    assert set(validation["bounded_context_ids"]) == CONTEXT
    assert validation["status_counts"] == {
        "investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
        "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4},
    }
    for name, expected in validation["input_sha256"].items():
        path = V27 / name[4:] if name.startswith("v27/") else V22 / name[4:] if name.startswith("v22/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name

    prior = json.loads((V27 / "row-challenge-v27.json").read_text())
    current = json.loads((HERE / "row-challenge-v28.json").read_text())
    assert len(prior) == len(current) == 333
    assert len({row["id"] for row in current}) == 333
    by_id = {row["id"]: row for row in current}
    for before, row in zip(prior, current):
        item = row["id"]
        assert all(row[key] == value for key, value in before.items()), item
        assert row["v28_status"] == row["v27_status"]
        assert row["v28_gate_categories"] == row["v27_gate_categories"]
        assert row["v28_specific_remaining_delta"] and row["v28_next_prerequisite"] and row["v28_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v28_evidence_files"]), item
        if item in CHANGED:
            assert row["v28_status"] == "partial"
            assert row["v28_review_package"] == HERE.parent.name
            assert row["v28_new_evidence_packages"] == PACKAGES[item]
            assert row["v28_evidence_files"]
            assert row["v28_specific_remaining_delta"] != row["v27_specific_remaining_delta"]
            assert row["v28_next_prerequisite"] != row["v27_next_prerequisite"]
            assert row["v28_evidence_relation"] == "direct bounded component evidence"
        else:
            assert row["v28_specific_remaining_delta"] == row["v27_specific_remaining_delta"]
            assert row["v28_next_prerequisite"] == row["v27_next_prerequisite"]
            assert row["v28_review_package"] == row["v27_review_package"]
            assert row["v28_new_evidence_packages"] == row["v28_evidence_files"] == []
            assert "v27 residual and prerequisite remain" in row["v28_scope_assessment"]
            assert row["v28_evidence_relation"] == ("bounded context only" if item in CONTEXT else "no direct v28 evidence")
    assert {row["id"] for row in current if row["v28_specific_remaining_delta"] != row["v27_specific_remaining_delta"]} == CHANGED
    assert {row["id"] for row in current if row["v28_next_prerequisite"] != row["v27_next_prerequisite"]} == CHANGED
    assert "direct lean --server and lake serve" in by_id["I038"]["v28_specific_remaining_delta"]
    assert "harness itself writes B before didSave" in by_id["I012"]["v28_specific_remaining_delta"]
    assert "version 2 tactic execution" in by_id["I041"]["v28_specific_remaining_delta"]
    assert "actual content-identified Anneal omnibus archive" in by_id["I089"]["v28_specific_remaining_delta"]
    assert "syscall traces" in by_id["I092"]["v28_specific_remaining_delta"]
    assert "actual same-platform Anneal archive" in by_id["I099"]["v28_specific_remaining_delta"]
    assert by_id["F02"]["v28_specific_remaining_delta"] == by_id["F02"]["v27_specific_remaining_delta"]
    assert by_id["I02"]["v28_specific_remaining_delta"] == by_id["I02"]["v27_specific_remaining_delta"]

    for filename, key, count in (("investigation-final-v28.csv", "id", 159), ("3730-crosswalk-final-v28.csv", "3730_id", 174)):
        before = rows(V27 / filename.replace("-v28", "-v27"))
        now = rows(HERE / filename)
        assert len(before) == len(now) == count
        assert [row[key] for row in before] == [row[key] for row in now]
        for old, row in zip(before, now):
            assert all(row[field] == value for field, value in old.items()), row[key]
            choice = by_id[row[key]]
            assert row["status"] == row["v28_status"] == choice["v28_status"]
            for field in ("v28_status", "v28_gate_categories", "v28_specific_remaining_delta", "v28_scope_assessment", "v28_review_package", "v28_new_evidence_packages", "v28_evidence_files", "v28_next_prerequisite", "v28_evidence_relation"):
                value = choice[field]
                assert row[field] == (";".join(value) if isinstance(value, list) else value), (row[key], field)

    live = json.loads((HERE / "live-issue-snapshot-v28.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    prior_live = json.loads((V27 / "live-issue-snapshot-v27.json").read_text())["issues"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["fetched_at_utc"].startswith("2026-09-29T")
    for number, state, comment_id in ((3730, "closed", 5884380373), (3731, "open", 5884299718)):
        key = str(number)
        item = live["issues"][key]
        assert item["number"] == number and item["state"] == state
        assert item["updated_at"] == prior_live[key]["updated_at"]
        assert item["body"] == frozen[key]["body"] == prior_live[key]["body"]
        assert item["body_sha256"] == hashlib.sha256(item["body"].encode()).hexdigest() == prior_live[key]["body_sha256"]
        assert len(item["comments"]) == 1 and item["comments"][0]["id"] == comment_id
        comment = item["comments"][0]
        assert comment["updated_at"] == prior_live[key]["comments"][0]["updated_at"]
        assert comment["body"] == frozen[key]["comments"][0]["body"] == prior_live[key]["comments"][0]["body"]
        assert comment["body_sha256"] == hashlib.sha256(comment["body"].encode()).hexdigest() == prior_live[key]["comments"][0]["body_sha256"]
    issue_body = live["issues"]["3731"]["body"]
    issue_comment = live["issues"]["3731"]["comments"][0]["body"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (issue_body, issue_comment)
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", issue_comment)}
    investigation = rows(HERE / "investigation-final-v28.csv")
    suggestions = rows(HERE / "3730-crosswalk-final-v28.csv")
    assert len(titles) == 159 and len(cross) == 174
    assert all(row["title"] == titles[row["id"]] for row in investigation)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and set(row["3731_destinations"].split(";")) == cross[row["3730_id"]][1] for row in suggestions)
    assert sum(len(destinations) for _, destinations in cross.values()) == 345

    inventory = rows(HERE / "source-package-inventory-v28.csv")
    assert len(inventory) == validation["inventory_files"]
    assert len({row["path"] for row in inventory}) == len(inventory)
    expected_paths = {
        path.relative_to(ROOT).as_posix()
        for package in validation["source_packages"]
        for path in (REPORTS / package).rglob("*")
        if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc"
    }
    assert {row["path"] for row in inventory} == expected_paths
    for row in inventory:
        assert sha(ROOT / row["path"]) == row["sha256"], row["path"]
    for package in validation["source_packages"]:
        path = REPORTS / package
        assert (path / "REPORT.md").is_file() and (path / "REPORT.json").is_file()
        result = subprocess.run([sys.executable, "-B", str(path / "support/check.py")], cwd=ROOT, capture_output=True, text=True, timeout=120)
        assert result.returncode == 0, (package, result.stdout, result.stderr)
    print(f"PASS: v28 333 rows, 345 links, 12 direct partial deltas, {len(CONTEXT)} bounded-context exclusions, {len(inventory)} source files and six source checkers")

if __name__ == "__main__":
    main()
