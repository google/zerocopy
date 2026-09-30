#!/usr/bin/env python3
"""Offline v46 audit checker: inherited rows, refreshed issue scope and sources."""
import csv
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
ROOT = REPORTS.parent
V45 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-30-v45" / "support"
PLUGIN = "anneal-3731-i125-i154-native-plugin-mapped-workers-2026-09-30"
DIRECT = {"I125", "I154"}
CONTEXT = {"J08", "J12"}
FIELDS = ("v46_status", "v46_gate_categories", "v46_specific_remaining_delta",
          "v46_scope_assessment", "v46_review_package", "v46_new_evidence_packages",
          "v46_evidence_files", "v46_next_prerequisite", "v46_evidence_relation")

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def rows(path):
    with path.open(newline="") as stream: return list(csv.DictReader(stream))

def main():
    v = json.loads((HERE / "validation-v46.json").read_text())
    assert v["reference_tip_at_start"] == "22c27b3d8ba12ab9708cb7cd8f13eb29217ec71a"
    assert v["source_reference_package"] == V45.parent.name
    assert (v["row_count"], v["investigation_count"], v["suggestion_count"],
            v["suggestion_destination_links"]) == (333, 159, 174, 345)
    assert v["status_counts"] == {"investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
                                  "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4}}
    assert set(v["changed_residual_ids"]) == set(v["direct_evidence_ids"]) == DIRECT
    assert set(v["bounded_context_ids"]) == CONTEXT
    assert v["changed_status_ids"] == v["changed_gate_ids"] == v["changed_prerequisite_ids"] == []
    for name, expected in v["input_sha256"].items():
        path = V45 / name[4:] if name.startswith("v45/") else HERE / name
        assert sha(path) == expected, name
    for name, expected in v["generated_sha256"].items(): assert sha(HERE / name) == expected, name

    before = json.loads((V45 / "row-challenge-v45.json").read_text())
    current = json.loads((HERE / "row-challenge-v46.json").read_text())
    assert len(before) == len(current) == 333
    assert [r["id"] for r in before] == [r["id"] for r in current]
    by_id = {r["id"]: r for r in current}
    for old, row in zip(before, current):
        item = row["id"]
        assert all(row[k] == value for k, value in old.items()), item
        assert row["v46_status"] == row["v45_status"]
        assert row["v46_gate_categories"] == row["v45_gate_categories"]
        assert row["v46_next_prerequisite"] == row["v45_next_prerequisite"]
        assert row["v46_specific_remaining_delta"] and row["v46_scope_assessment"]
        assert all((ROOT / path).is_file() for path in row["v46_evidence_files"]), item
        if item in DIRECT:
            assert row["v46_status"] == "partial" and row["v46_gate_categories"] == ["product"]
            assert row["v46_specific_remaining_delta"] != row["v45_specific_remaining_delta"]
            assert len(row["v46_new_evidence_packages"]) == 1 and row["v46_evidence_files"]
            assert row["v46_evidence_relation"] == "direct bounded native-plugin mapping evidence"
        elif item in CONTEXT:
            assert row["v46_specific_remaining_delta"] == row["v45_specific_remaining_delta"]
            assert row["v46_new_evidence_packages"] == [PLUGIN]
            assert row["v46_evidence_relation"] == "bounded mapped-worker context"
        else:
            assert row["v46_specific_remaining_delta"] == row["v45_specific_remaining_delta"]
            assert row["v46_new_evidence_packages"] == row["v46_evidence_files"] == []
            assert row["v46_review_package"] == row["v45_review_package"]
            assert row["v46_evidence_relation"] == "no direct v46 evidence"
    assert {r["id"] for r in current if r["v46_specific_remaining_delta"] != r["v45_specific_remaining_delta"]} == DIRECT
    assert "1.5 GiB summed-RSS guard" in by_id["I125"]["v46_specific_remaining_delta"]
    assert "in-one-watchdog v1→v2→v1 mapped transition" in by_id["I154"]["v46_specific_remaining_delta"]
    assert "same-run v2 marker was not retained" in by_id["I154"]["v46_specific_remaining_delta"]
    for item in DIRECT | CONTEXT:
        assert by_id[item]["v46_review_package"] == HERE.parent.name

    for new, old_name, key, count in (("investigation-final-v46.csv", "investigation-final-v45.csv", "id", 159),
                                       ("3730-crosswalk-final-v46.csv", "3730-crosswalk-final-v45.csv", "3730_id", 174)):
        a, b = rows(V45 / old_name), rows(HERE / new)
        assert len(a) == len(b) == count and [x[key] for x in a] == [x[key] for x in b]
        for old, row in zip(a, b):
            assert all(row[field] == value for field, value in old.items()), row[key]
            item = by_id[row[key]]
            assert row["status"] == row["v46_status"] == item["v46_status"]
            for field in FIELDS:
                value = item[field]
                assert row[field] == (";".join(value) if isinstance(value, list) else value), (row[key], field)

    live = json.loads((HERE / "live-issue-snapshot-v46.json").read_text())
    old_live = json.loads((V45 / "live-issue-snapshot-v45.json").read_text())
    assert live["source"] == "public GitHub REST issue and comments endpoints"
    for number, state in ((3730, "closed"), (3731, "open")):
        x, p = live["issues"][str(number)], old_live["issues"][str(number)]
        assert x["number"] == number and x["state"] == state == p["state"]
        assert x["body"] == p["body"] and x["body_sha256"] == sha_text(x["body"]) == p["body_sha256"]
        assert len(x["comments"]) == len(p["comments"]) == 1
        y, z = x["comments"][0], p["comments"][0]
        assert y["id"] == z["id"] and y["body"] == z["body"]
        assert y["body_sha256"] == sha_text(y["body"]) == z["body_sha256"]
    body, comment = live["issues"]["3731"]["body"], live["issues"]["3731"]["comments"][0]["body"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip() for source in (body, comment)
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", comment)}
    investigations = rows(HERE / "investigation-final-v46.csv")
    suggestions = rows(HERE / "3730-crosswalk-final-v46.csv")
    assert len(titles) == 159 and len(cross) == 174
    assert all(r["title"] == titles[r["id"]] for r in investigations)
    assert all(r["suggestion"] == cross[r["3730_id"]][0] and
               set(r["3731_destinations"].split(";")) == cross[r["3730_id"]][1] for r in suggestions)
    assert sum(len(x[1]) for x in cross.values()) == 345
    assert {r["3730_id"] for r in suggestions if "I154" in r["3731_destinations"].split(";")} == CONTEXT

    inventory = rows(HERE / "source-package-inventory-v46.csv")
    assert len(inventory) == v["inventory_files"] and len({r["path"] for r in inventory}) == len(inventory)
    expected = {path.relative_to(ROOT).as_posix() for package in v["source_packages"]
                for path in (REPORTS / package).rglob("*") if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc"}
    assert {r["path"] for r in inventory} == expected
    for row in inventory: assert sha(ROOT / row["path"]) == row["sha256"], row["path"]
    assert v["source_packages"] == [V45.parent.name, PLUGIN]
    for package in v["source_packages"]:
        path = REPORTS / package
        checker = path / ("support/check.py" if (path / "support/check.py").exists() else "check.py")
        result = subprocess.run([sys.executable, "-B", str(checker)], cwd=path,
                                capture_output=True, text=True, timeout=120)
        assert result.returncode == 0, (package, result.stdout, result.stderr)

    spec = importlib.util.spec_from_file_location("reference", ROOT / "tools/reference.py")
    reference = importlib.util.module_from_spec(spec); sys.modules[spec.name] = reference; spec.loader.exec_module(reference)
    for package in (*v["source_packages"], HERE.parent.name):
        report, problems = reference._load_report(REPORTS / package)
        assert report is not None and not problems, (package, problems)
    metadata = json.loads((HERE.parent / "REPORT.json").read_text())
    prior, issues, *sources = (x["identity"] for x in metadata["subjects"])
    assert prior["reference_revision"] == v["reference_tip_at_start"]
    assert prior["row_challenge_sha256"] == sha(V45 / "row-challenge-v45.json")
    for number in (3730, 3731):
        x = live["issues"][str(number)]
        assert issues[f"issue_{number}_body_sha256"] == x["body_sha256"]
        assert issues[f"comment_{number}_sha256"] == x["comments"][0]["body_sha256"]
    for package, subject in zip(v["source_packages"][1:], sources):
        assert subject["source_report_sha256"] == sha(REPORTS / package / "REPORT.md")
    print(f"PASS: v46 333 rows, 345 links, two direct deltas, two mapped contexts, {len(inventory)} source files and two source checkers")

def sha_text(text): return hashlib.sha256(text.encode()).hexdigest()

if __name__ == "__main__": main()
