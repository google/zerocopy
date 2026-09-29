#!/usr/bin/env python3
"""Read-only offline integrity and exact-scope check for v24."""
import csv
import hashlib
import json
import re
import runpy
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V23 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v23/support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def main():
    validation = json.loads((HERE / "validation-v24.json").read_text())
    assert validation["baseline_reference_head"] == "9d2426519c7eaaf58b13b109a2f4c16d84c51616"
    assert validation["row_count"] == 333 and validation["investigation_count"] == 159
    assert validation["suggestion_count"] == 174 and validation["suggestion_destination_links"] == 345
    assert validation["changed_status_ids"] == []
    assert validation["changed_residual_ids"] == sorted({"I005", "I076", "I126", "I127", "I145",
                                                        "A01", "A02", "A08", "C01", "D07", "F05",
                                                        "G01", "G02", "G09", "G12", "L01", "O03"})
    assert validation["changed_prerequisite_ids"] == sorted({"I005", "I076", "I126", "I127", "I145", "D07", "G09"})
    assert validation["new_bounded_experiment_ids"] == ["I005", "I076", "I126"]
    assert validation["status_counts"] == {
        "investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
        "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4},
    }
    for name, expected in validation["input_sha256"].items():
        path = V23 / name[4:] if name.startswith("v23/") else V22 / name[4:] if name.startswith("v22/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in validation["generated_sha256"].items():
        assert sha(HERE / name) == expected, name

    old = json.loads((V23 / "row-challenge-v23.json").read_text())
    new = json.loads((HERE / "row-challenge-v24.json").read_text())
    assert len(old) == len(new) == 333
    assert len({x["id"] for x in new}) == 333
    for previous, current in zip(old, new):
        assert all(current[key] == value for key, value in previous.items()), previous["id"]
        assert current["v24_status"] == current["v23_status"]
        assert current["v24_gate_categories"] == current["v23_gate_categories"]
        assert current["v24_specific_remaining_delta"] and current["v24_next_prerequisite"]
        assert all((ROOT / path).is_file() for path in current["v24_evidence_files"]), current["id"]
        assert current["v24_new_distinct_cached_only_experiment_executed"] == (current["id"] in {"I005", "I076", "I126"})
    by_id = {x["id"]: x for x in new}
    assert {x["id"] for x in new if x["v24_specific_remaining_delta"] != x["v23_specific_remaining_delta"]} == set(validation["changed_residual_ids"])
    assert {x["id"] for x in new if x["v24_next_prerequisite"] != x["v23_next_prerequisite"]} == set(validation["changed_prerequisite_ids"])
    assert by_id["I046"]["v24_status"] == by_id["I049"]["v24_status"] == "complete"
    assert all(by_id[item]["v24_status"] == "partial" for item in ("I005", "I076", "I126", "I127", "I145", "D07", "G09"))
    assert "12 schedules" in by_id["I005"]["v24_specific_remaining_delta"]
    assert "11 versus 29" in by_id["I076"]["v24_specific_remaining_delta"]
    assert "targeted macOS sandbox denial" in by_id["I126"]["v24_specific_remaining_delta"]
    assert "absolute owned marker path" in by_id["I127"]["v24_specific_remaining_delta"]
    assert "sibling-Cargo" in by_id["I145"]["v24_specific_remaining_delta"]

    for filename, key, number in (("investigation-final-v24.csv", "id", 159),
                                  ("3730-crosswalk-final-v24.csv", "3730_id", 174)):
        current = rows(HERE / filename)
        previous = rows(V23 / filename.replace("-v24", "-v23"))
        assert len(current) == len(previous) == number
        for row, before in zip(current, previous):
            assert row[key] == before[key]
            assert all(row[field] == value for field, value in before.items() if field != "status"), row[key]
            assert row["status"] == row["v24_status"] == by_id[row[key]]["v24_status"]
            assert row["v24_gate_categories"] == ";".join(by_id[row[key]]["v24_gate_categories"])
            assert row["v24_evidence_files"] == ";".join(by_id[row[key]]["v24_evidence_files"])
    investigations = rows(HERE / "investigation-final-v24.csv")
    suggestions = rows(HERE / "3730-crosswalk-final-v24.csv")

    live = json.loads((HERE / "live-issue-hashes.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    original = json.loads((REPORTS / "anneal-3730-3731-coverage-audit-2026-09-29/support/source-snapshot/manifest.json").read_text())["files"]
    for number, state, comment_id in ((3730, "closed", 5884380373), (3731, "open", 5884299718)):
        item = live["issues"][str(number)]
        assert item["number"] == number and item["state"] == state
        assert item["body_sha256"] == original[f"issue{number}.txt"]["sha256"]
        assert len(item["comments"]) == 1 and item["comments"][0]["id"] == comment_id
        assert item["comments"][0]["body_sha256"] == original[f"comment{number}.txt"]["sha256"]
        assert hashlib.sha256(frozen[str(number)]["body"].encode()).hexdigest() == item["body_sha256"]
        assert hashlib.sha256(frozen[str(number)]["comments"][0]["body"].encode()).hexdigest() == item["comments"][0]["body_sha256"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (frozen["3731"]["body"], frozen["3731"]["comments"][0]["body"])
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", frozen["3731"]["comments"][0]["body"])}
    assert len(titles) == 159 and len(cross) == 174
    assert {x["id"] for x in investigations} == set(titles)
    assert {x["3730_id"] for x in suggestions} == set(cross)
    assert all(x["title"] == titles[x["id"]] for x in investigations)
    assert all(x["suggestion"] == cross[x["3730_id"]][0] and
               set(re.findall(r"I\d{3}", x["3731_destinations"])) == cross[x["3730_id"]][1]
               for x in suggestions)
    assert sum(len(value[1]) for value in cross.values()) == 345
    directly_linked = {x["3730_id"] for x in suggestions if set(x["3731_destinations"].split(";")) & {"I005", "I076", "I126", "I127", "I145"}}
    assert directly_linked == set(validation["linked_suggestion_ids"])

    inventory = rows(HERE / "source-package-inventory-v24.csv")
    assert len(inventory) == validation["inventory_files"] == 41
    assert len({x["path"] for x in inventory}) == len(inventory)
    for record in inventory:
        assert sha(ROOT / record["path"]) == record["sha256"], record["path"]
    names = validation["source_packages"]
    assert names == ["anneal-3731-i001-i053-postpublication-residual-review-2026-09-29",
                     "anneal-3731-i054-i106-postpublication-residual-audit-2026-09-29",
                     "anneal-3731-i107-i159-postpublication-residual-audit-2026-09-29"]
    reference = runpy.run_path(str(ROOT / "tools/reference.py"))
    for name in names:
        report, problems = reference["_load_report"](REPORTS / name)
        assert report is not None and not problems, name
        result = subprocess.run([sys.executable, "-B", str(REPORTS / name / "support/check.py")],
                                cwd=ROOT, capture_output=True, text=True, timeout=60)
        assert result.returncode == 0 and result.stdout.strip().startswith("PASS"), (name, result.stdout, result.stderr)
    report, problems = reference["_load_report"](HERE.parent)
    assert report is not None and not problems
    print("PASS: v24 333 rows, 345 exact links, 17 residual updates, unchanged statuses, 41 inventoried files, and three audit loaders/checkers")


if __name__ == "__main__":
    main()
