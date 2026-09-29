#!/usr/bin/env python3
"""Read-only offline checker for the v25 333-row coverage ledger."""
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
V24 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v24/support"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"
AUDIT = REPORTS / "anneal-3730-174-suggestion-postpublication-native-trust-audit-2026-09-29"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def main():
    validation = json.loads((HERE / "validation-v25.json").read_text())
    assert validation["baseline_reference_head"] == "9d2426519c7eaaf58b13b109a2f4c16d84c51616"
    assert (validation["row_count"], validation["investigation_count"], validation["suggestion_count"], validation["suggestion_destination_links"]) == (333, 159, 174, 345)
    assert validation["changed_status_ids"] == []
    assert validation["changed_residual_ids"] == ["G09", "I126", "I127"]
    assert validation["changed_prerequisite_ids"] == []
    assert validation["new_bounded_experiment_ids"] == ["I126"]
    assert validation["cross_slice_observation_ids"] == ["I127"]
    assert validation["direct_suggestion_evidence_ids"] == ["G09"]
    assert validation["status_counts"] == {
        "investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3},
        "suggestions": {"complete": 3, "partial": 162, "not-run": 5, "conditional": 4},
    }
    for key, expected in validation["input_sha256"].items():
        path = V24 / key[4:] if key.startswith("v24/") else V22 / key[4:] if key.startswith("v22/") else HERE / key if key == "live-issue-hashes.json" else REPORTS / key
        assert sha(path) == expected, key
    for key, expected in validation["generated_sha256"].items():
        assert sha(HERE / key) == expected, key

    old = json.loads((V24 / "row-challenge-v24.json").read_text())
    new = json.loads((HERE / "row-challenge-v25.json").read_text())
    assert len(old) == len(new) == 333
    assert len({row["id"] for row in new}) == 333
    for before, current in zip(old, new):
        assert all(current[key] == value for key, value in before.items()), before["id"]
        assert current["v25_status"] == current["v24_status"]
        assert current["v25_gate_categories"] == current["v24_gate_categories"]
        assert current["v25_specific_remaining_delta"] and current["v25_next_prerequisite"]
        assert current["v25_cached_only_decision"]
        assert all((ROOT / path).is_file() for path in current["v25_evidence_files"]), current["id"]
    by_id = {row["id"]: row for row in new}
    assert {row["id"] for row in new if row["v25_specific_remaining_delta"] != row["v24_specific_remaining_delta"]} == {"G09", "I126", "I127"}
    assert not any(row["v25_next_prerequisite"] != row["v24_next_prerequisite"] for row in new)
    assert {row["id"] for row in new if row["v25_new_evidence_packages"]} == {"G09", "I126", "I127"}
    assert all(by_id[item]["v25_status"] == "partial" for item in ("G09", "I126", "I127"))
    assert "native Lean plugin initializer" in by_id["I126"]["v25_specific_remaining_delta"]
    assert "absolute owned scratch path" in by_id["I127"]["v25_specific_remaining_delta"]
    assert "native-plugin initializer" in by_id["G09"]["v25_specific_remaining_delta"]
    for item in ("I005", "I076", "I145"):
        assert by_id[item]["v25_specific_remaining_delta"] == by_id[item]["v24_specific_remaining_delta"]
        assert by_id[item]["v25_evidence_files"] == []
        assert by_id[item]["v24_evidence_files"]

    audits = {row["id"]: row for row in rows(AUDIT / "support/row-decisions.csv")}
    assert len(audits) == 174
    for filename, key, count in (("investigation-final-v25.csv", "id", 159),
                                 ("3730-crosswalk-final-v25.csv", "3730_id", 174)):
        current = rows(HERE / filename)
        previous = rows(V24 / filename.replace("-v25", "-v24"))
        assert len(current) == len(previous) == count
        for row, before in zip(current, previous):
            assert row[key] == before[key]
            assert all(row[field] == value for field, value in before.items() if field != "status"), row[key]
            assert row["status"] == row["v25_status"] == by_id[row[key]]["v25_status"]
            assert row["v25_evidence_files"] == ";".join(by_id[row[key]]["v25_evidence_files"])
            if key == "3730_id":
                decision = audits[row[key]]
                assert row["v25_original_request_sha256"] == decision["requested_text_sha256"]
                assert row["v25_entire_requested_scope_supported"] == decision["entire_requested_scope_supported"]
                assert row["v25_cached_only_decision"] == decision["cached_only_decision"]
                assert row["v25_new_evidence_relation"] == decision["new_evidence_relation"]
                assert row["v25_cited_packages"] == decision["cited_packages"]
                assert row["v25_specific_remaining_delta"] == decision["remaining_gate"]
                assert row["v25_next_prerequisite"] == decision["next_prerequisite"]
    investigations = rows(HERE / "investigation-final-v25.csv")
    suggestions = rows(HERE / "3730-crosswalk-final-v25.csv")
    assert {row["3730_id"] for row in suggestions if row["v25_entire_requested_scope_supported"] == "true"} == {"C04", "C13", "N11"}

    live = json.loads((HERE / "live-issue-hashes.json").read_text())
    frozen = json.loads((V22 / "issue-scope-snapshot.json").read_text())
    original = json.loads((REPORTS / "anneal-3730-3731-coverage-audit-2026-09-29/support/source-snapshot/manifest.json").read_text())["files"]
    for n, state, comment_id in ((3730, "closed", 5884380373), (3731, "open", 5884299718)):
        item = live["issues"][str(n)]
        assert item["number"] == n and item["state"] == state
        assert item["body_sha256"] == original[f"issue{n}.txt"]["sha256"]
        assert hashlib.sha256(frozen[str(n)]["body"].encode()).hexdigest() == item["body_sha256"]
        assert len(item["comments"]) == 1 and item["comments"][0]["id"] == comment_id
        assert item["comments"][0]["body_sha256"] == original[f"comment{n}.txt"]["sha256"]
    titles = {item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
              for source in (frozen["3731"]["body"], frozen["3731"]["comments"][0]["body"])
              for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)}
    cross = {item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
             for item, title, destinations in re.findall(r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", frozen["3731"]["comments"][0]["body"])}
    assert len(titles) == 159 and len(cross) == 174
    assert all(row["title"] == titles[row["id"]] for row in investigations)
    assert all(row["suggestion"] == cross[row["3730_id"]][0] and
               set(row["3731_destinations"].split(";")) == cross[row["3730_id"]][1]
               for row in suggestions)
    assert sum(len(value[1]) for value in cross.values()) == 345

    inventory = rows(HERE / "source-package-inventory-v25.csv")
    assert len(inventory) == validation["inventory_files"] == 72
    assert len({row["path"] for row in inventory}) == len(inventory)
    for row in inventory:
        assert sha(ROOT / row["path"]) == row["sha256"], row["path"]
    names = validation["source_packages"]
    assert len(names) == 5 and names[-1] == AUDIT.name
    reference = runpy.run_path(str(ROOT / "tools/reference.py"))
    for name in names:
        report, problems = reference["_load_report"](REPORTS / name)
        assert report is not None and not problems, name
    for name in (names[0], names[-1]):
        result = subprocess.run([sys.executable, "-B", str(REPORTS / name / "support/check.py")],
                                cwd=ROOT, capture_output=True, text=True, timeout=90)
        assert result.returncode == 0 and result.stdout.strip().startswith("PASS"), (name, result.stdout, result.stderr)
    report, problems = reference["_load_report"](HERE.parent)
    assert report is not None and not problems
    print("PASS: v25 333 rows, 345 exact links, 174 per-suggestion decisions, native I126/G09 evidence, unchanged statuses, 72 source files and audit checkers")


if __name__ == "__main__":
    main()
