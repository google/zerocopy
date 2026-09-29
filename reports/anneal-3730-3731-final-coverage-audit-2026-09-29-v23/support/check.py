#!/usr/bin/env python3
"""Offline integrity and row-level validation for the v23 central ledger."""
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
reports = here.parents[1]
root = reports.parent
v22 = reports / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))

generated = ("row-challenge-v23.json", "investigation-final-v23.csv", "3730-crosswalk-final-v23.csv", "review-package-inventory-v23.csv", "validation-v23.json")
before = {name: sha(here / name) for name in generated}
for _ in range(2):
    result = subprocess.run([sys.executable, str(here / "build_audit.py")], cwd=root,
                            capture_output=True, text=True, timeout=60, check=True)
    assert {name: sha(here / name) for name in generated} == before, result.stdout

validation = json.loads((here / "validation-v23.json").read_text())
assert validation["baseline_reference_head"] == "75fa78c1b623ab8db9d9acb4f31ec7958bfb9110"
assert validation["changed_status_ids"] == ["C03"]
assert validation["row_count"] == 333 and validation["suggestion_destination_links"] == 345
for name, expected in validation["input_sha256"].items():
    path = v22 / name[4:] if name.startswith("v22/") else reports / name
    assert sha(path) == expected, name
for name, expected in validation["generated_sha256"].items():
    assert sha(here / name) == expected, name

old = json.loads((v22 / "row-challenge-v22.json").read_text())
new = json.loads((here / "row-challenge-v23.json").read_text())
assert len(old) == len(new) == 333
assert len({row["id"] for row in new}) == 333
for previous, current in zip(old, new):
    assert all(current[key] == value for key, value in previous.items()), previous["id"]
    assert current["v23_specific_remaining_delta"] and current["v23_next_prerequisite"]
    assert current["v23_review_package"]
    assert all((root / path).is_file() for path in current["v23_evidence_files"]), current["id"]
by_id = {row["id"]: row for row in new}
assert {row["id"] for row in new if row["v23_status"] != row["v22_status"]} == {"C03"}
assert by_id["C03"]["v23_status"] == "partial"
assert by_id["I049"]["v23_status"] == "complete"
assert by_id["I129"]["v23_gate_categories"] == ["human", "product"]
assert "controlled interpretation evaluation" in by_id["I129"]["v23_next_prerequisite"]
assert all("OCaml/Dune/opam" not in by_id[item]["v23_next_prerequisite"] for item in
           ("I065", "I071", "I077", "I089", "I094", "I101", "I103", "D01", "F02", "F14", "I04"))
assert "same-nanosecond-mtime" in by_id["I147"]["v23_specific_remaining_delta"]
assert "two conflicting Lake processes" in by_id["I151"]["v23_specific_remaining_delta"]
assert "two-writer" in by_id["F12"]["v23_specific_remaining_delta"]
assert "reverse-kill" in by_id["F12"]["v23_specific_remaining_delta"]
assert "already explicit in v22" in by_id["F12"]["v23_post_v22_scope_assessment"]
assert by_id["F15"]["v23_new_evidence_packages"] == ["anneal-3730-f15-final-versus-moved-lake-2026-09-29"]
assert "Dep.trace" in by_id["F15"]["v23_specific_remaining_delta"]
assert "anneal-3731-embedded-proof-generated-model-vertical-v4-30-0-rc2" in by_id["I01"]["v23_new_evidence_packages"]
assert all("human" not in by_id[item]["v23_gate_categories"] for item in ("F19", "I01", "I03"))
assert set(by_id["I08"]["v23_gate_categories"]) == {"human", "product"}
for item in ("J01", "J02", "J03", "J04", "J05", "J06", "J07", "J08", "J09", "J10", "J12", "J14"):
    assert "product" in by_id[item]["v23_gate_categories"]
    assert "prepared Anneal workload" in by_id[item]["v23_next_prerequisite"]
assert set(validation["challenged_suggestion_ids"]) == {
    "C03", "D01", "F02", "F12", "F14", "F15", "F19", "I01", "I03", "I04", "I08",
    "J01", "J02", "J03", "J04", "J05", "J06", "J07", "J08", "J09", "J10", "J12", "J14"
}

investigations = rows(here / "investigation-final-v23.csv")
suggestions = rows(here / "3730-crosswalk-final-v23.csv")
assert len(investigations) == 159 and len(suggestions) == 174
for name, key, source in (
    ("investigation-final-v23.csv", "id", "investigation-final-v22.csv"),
    ("3730-crosswalk-final-v23.csv", "3730_id", "3730-crosswalk-final-v22.csv"),
):
    for current, prior in zip(rows(here / name), rows(v22 / source)):
        assert current[key] == prior[key]
        assert all(current[field] == value for field, value in prior.items() if field != "status"), current[key]
        assert current["status"] == current["v23_status"] == by_id[current[key]]["v23_status"]
assert validation["status_counts"] == {
    "investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
    "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4},
}

issue = json.loads((v22 / "issue-scope-snapshot.json").read_text())
titles = {
    item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
    for source in (issue["3731"]["body"], issue["3731"]["comments"][0]["body"])
    for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)
}
cross = {
    item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
    for item, title, destinations in re.findall(
        r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|",
        issue["3731"]["comments"][0]["body"],
    )
}
assert len(titles) == 159 and len(cross) == 174
assert {row["id"] for row in investigations} == set(titles)
assert {row["3730_id"] for row in suggestions} == set(cross)
assert all(row["title"] == titles[row["id"]] for row in investigations)
assert all(row["suggestion"] == cross[row["3730_id"]][0] and
           set(re.findall(r"I\d{3}", row["3731_destinations"])) == cross[row["3730_id"]][1]
           for row in suggestions)
assert sum(len(destinations) for _, destinations in cross.values()) == 345

inventory = rows(here / "review-package-inventory-v23.csv")
assert len(inventory) == 8 and {row["package"] for row in inventory} == set(validation["new_packages"])
for row in inventory:
    directory = reports / row["package"]
    assert sha(directory / "REPORT.md") == row["report_sha256"]
    assert sha(directory / "REPORT.json") == row["metadata_sha256"]
    checker = directory / "support/check.py"
    assert (sha(checker) if checker.is_file() else "") == row["checker_sha256"]

for name in (
    "anneal-3730-3731-final-coverage-audit-2026-09-29-v22",
    "anneal-3730-3731-v22-independent-rereview-2026-09-29",
    "anneal-3730-174-row-crosswalk-reaudit-2026-09-29",
    "anneal-3730-c03-proof-resend-refresh-2026-09-29",
    "anneal-3730-f15-final-versus-moved-lake-2026-09-29",
    "anneal-3730-five-original-packages-rereview-2026-09-29",
    "anneal-3731-i001-i053-residual-reaudit-2026-09-29",
    "anneal-3731-i054-i106-independent-rereview-2026-09-29",
    "anneal-3731-i080-shared-cargo-target-two-process-2026-09-29",
    "anneal-3731-i107-i159-independent-rereview-2026-09-29",
):
    result = subprocess.run([sys.executable, str(reports / name / "support/check.py")],
                            cwd=root, capture_output=True, text=True, timeout=60, check=True)
    assert result.stdout.strip(), name
print("PASS: deterministic v23 333-row ledger, exact 345 links, C03 partial, 23 challenge outcomes, ten evidence checkers")
