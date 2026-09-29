#!/usr/bin/env python3
"""Read-only offline checker for the v27 333-row ledger and source evidence."""

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
V26 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v26" / "support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"
CHANGED = {"C02", "E06", "E07", "F12", "I025", "I043", "I079", "I148", "I151"}
EVIDENCE_ONLY = {"I046"}
PACKAGES = {
    "I025": ["anneal-3731-compiler-backed-coordinate-bridge-2026-09-29"],
    "I043": ["anneal-3731-rich-goal-unsaved-recovery-v4-30-0-rc2"],
    "I046": ["anneal-3731-rich-goal-unsaved-recovery-v4-30-0-rc2"],
    "C02": ["anneal-3731-rich-goal-unsaved-recovery-v4-30-0-rc2"],
    "I079": ["anneal-3731-charon-relocation-comment-provenance-2026-09-29"],
    "I148": ["anneal-3731-charon-relocation-comment-provenance-2026-09-29"],
    "E06": ["anneal-3731-charon-relocation-comment-provenance-2026-09-29"],
    "E07": ["anneal-3731-charon-relocation-comment-provenance-2026-09-29"],
    "I151": ["anneal-3731-i151-matched-lake-writer-isolation-2026-09-29"],
    "F12": ["anneal-3731-i151-matched-lake-writer-isolation-2026-09-29"],
}
CONTEXT = {"B02", "B03", "K01", "I009", "I074", "I044", "I108", "I080", "I113", "J01", "J02", "A02", "A08", "D05", "D07", "D06"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def main():
    validation = json.loads((HERE / "validation-v27.json").read_text())
    assert validation["reference_tip_at_start"] == "087760fd8bccaa8852390f189d8daf01f0958b19"
    assert validation["source_reference_package"] == V26.parent.name
    assert validation["source_anneal_revision"] == "bd0956be95c5f798f0c0484921b9b9d1fc6e9988"
    assert (validation["row_count"], validation["investigation_count"], validation["suggestion_count"], validation["suggestion_destination_links"]) == (333, 159, 174, 345)
    assert validation["changed_status_ids"] == validation["changed_gate_ids"] == []
    assert set(validation["changed_residual_ids"]) == set(validation["changed_prerequisite_ids"]) == CHANGED
    assert set(validation["direct_evidence_ids"]) == CHANGED | EVIDENCE_ONLY
    assert set(validation["evidence_only_ids"]) == EVIDENCE_ONLY
    assert set(validation["bounded_context_ids"]) == CONTEXT
    assert validation["status_counts"] == {
        "investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
        "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4},
    }
    for name, expected in validation["input_sha256"].items():
        path = V26 / name[4:] if name.startswith("v26/") else V22 / name[4:] if name.startswith("v22/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name

    prior = json.loads((V26 / "row-challenge-v26.json").read_text())
    current = json.loads((HERE / "row-challenge-v27.json").read_text())
    assert len(prior) == len(current) == 333
    assert len({row["id"] for row in current}) == 333
    by_id = {row["id"]: row for row in current}
    for before, row in zip(prior, current):
        assert all(row[key] == value for key, value in before.items()), before["id"]
        assert row["v27_status"] == row["v26_status"]
        assert row["v27_gate_categories"] == row["v26_gate_categories"]
        assert row["v27_specific_remaining_delta"] and row["v27_next_prerequisite"] and row["v27_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v27_evidence_files"]), row["id"]
        if row["id"] in CHANGED:
            assert row["v27_status"] == "partial"
            assert row["v27_review_package"] == HERE.parent.name
            assert row["v27_new_evidence_packages"] == PACKAGES[row["id"]]
            assert row["v27_evidence_files"]
            assert row["v27_specific_remaining_delta"] != row["v26_specific_remaining_delta"]
            assert row["v27_next_prerequisite"] != row["v26_next_prerequisite"]
        elif row["id"] in EVIDENCE_ONLY:
            assert row["v27_status"] == row["v26_status"] == "complete"
            assert row["v27_review_package"] == HERE.parent.name
            assert row["v27_new_evidence_packages"] == PACKAGES[row["id"]]
            assert row["v27_evidence_files"]
            assert row["v27_specific_remaining_delta"] == row["v26_specific_remaining_delta"]
            assert row["v27_next_prerequisite"] == row["v26_next_prerequisite"]
        else:
            assert row["v27_specific_remaining_delta"] == row["v26_specific_remaining_delta"]
            assert row["v27_next_prerequisite"] == row["v26_next_prerequisite"]
            assert row["v27_new_evidence_packages"] == row["v27_evidence_files"] == []
            assert "v26 residual and prerequisite remain" in row["v27_scope_assessment"]
            if row["id"] in CONTEXT:
                assert row["v27_evidence_relation"] == "bounded context only"
            else:
                assert row["v27_evidence_relation"] == "no direct v27 evidence"
    assert {row["id"] for row in current if row["v27_specific_remaining_delta"] != row["v26_specific_remaining_delta"]} == CHANGED
    assert {row["id"] for row in current if row["v27_next_prerequisite"] != row["v26_next_prerequisite"]} == CHANGED
    assert "24 cursor/version pairs" in by_id["I043"]["v27_specific_remaining_delta"]
    assert "28 valid scalar boundaries" in by_id["I025"]["v27_specific_remaining_delta"]
    assert "hand-authored exact-copy harness" in by_id["I025"]["v27_specific_remaining_delta"]
    assert "not test rich reference" in by_id["I043"]["v27_specific_remaining_delta"]
    assert "one safe function" in by_id["I079"]["v27_specific_remaining_delta"]
    assert "error-bearing" in by_id["I148"]["v27_specific_remaining_delta"]
    assert "before artifact output" in by_id["I151"]["v27_specific_remaining_delta"]
    assert by_id["D05"]["v27_specific_remaining_delta"] == by_id["D05"]["v26_specific_remaining_delta"]
    assert by_id["I108"]["v27_specific_remaining_delta"] == by_id["I108"]["v26_specific_remaining_delta"]

    for filename, key, count in (("investigation-final-v27.csv", "id", 159), ("3730-crosswalk-final-v27.csv", "3730_id", 174)):
        before = rows(V26 / filename.replace("-v27", "-v26"))
        now = rows(HERE / filename)
        assert len(before) == len(now) == count
        assert [row[key] for row in before] == [row[key] for row in now]
        for old, row in zip(before, now):
            assert all(row[field] == value for field, value in old.items()), row[key]
            choice = by_id[row[key]]
            assert row["status"] == row["v27_status"] == choice["v27_status"]
            for field in ("v27_status", "v27_gate_categories", "v27_specific_remaining_delta", "v27_scope_assessment", "v27_review_package", "v27_new_evidence_packages", "v27_evidence_files", "v27_next_prerequisite", "v27_evidence_relation"):
                value = choice[field]
                assert row[field] == (";".join(value) if isinstance(value, list) else value), (row[key], field)

    live = json.loads((HERE / "live-issue-snapshot-v27.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    prior_live = json.loads((V26 / "live-issue-snapshot-v26.json").read_text())["issues"]
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    assert live["fetched_at_utc"] == "2026-09-29T22:10:04.154540+00:00"
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
    assert len(titles) == 159 and len(cross) == 174
    investigation = rows(HERE / "investigation-final-v27.csv")
    suggestions = rows(HERE / "3730-crosswalk-final-v27.csv")
    assert all(row["title"] == titles[row["id"]] for row in investigation)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and set(row["3731_destinations"].split(";")) == cross[row["3730_id"]][1] for row in suggestions)
    assert sum(len(destinations) for _, destinations in cross.values()) == 345

    inventory = rows(HERE / "source-package-inventory-v27.csv")
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
        result = subprocess.run([sys.executable, "-B", str(path / "support/check.py")], cwd=ROOT, capture_output=True, text=True, timeout=90)
        assert result.returncode == 0, (package, result.stdout, result.stderr)
    print(f"PASS: v27 333 rows, 345 links, nine direct deltas, one corroborated complete row, {len(CONTEXT)} bounded-context exclusions, {len(inventory)} source files and five source checkers")


if __name__ == "__main__":
    main()
