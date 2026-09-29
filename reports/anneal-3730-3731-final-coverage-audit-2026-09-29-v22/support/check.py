#!/usr/bin/env python3
"""Validate the deterministic v22 source-surface coverage audit."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
V21 = ROOT / "reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v21/support"
SOURCE = "anneal-v2-current-source-surface-main-bd0956b-2026-09-29"
FILES = ("row-challenge-v22.json", "investigation-final-v22.csv", "3730-crosswalk-final-v22.csv", "new-package-review-v22.csv", "new-file-inventory-v22.csv", "unrun-conditional-inputs-v22.csv", "validation-v22.json")
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
read_csv = lambda path: list(csv.DictReader(Path(path).open(newline="")))
before = {name: sha(HERE / name) for name in FILES}
for _ in range(2):
    result = subprocess.run([sys.executable, str(HERE / "build_audit.py")], cwd=ROOT, capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert {name: sha(HERE / name) for name in FILES} == before, "nondeterministic rebuild"

record = json.loads((HERE / "validation-v22.json").read_text())
assert record["reference_commit"] == "a5b4d034aa65aa44d85afc943c3caec26a5229ba"
assert record["source_revision"] == "bd0956be95c5f798f0c0484921b9b9d1fc6e9988"
assert record["row_challenge_count"] == 333 and record["source_mapped_rows"] == 62
assert record["issue_3730_heading_count"] == 174 and record["issue_3731_id_count"] == 159
assert record["new_complete_ids"] == [] and record["unrun_conditional_count"] == 13
assert record["status_counts"] == {"investigations": {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3}, "suggestions": {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}}
for name, digest in record["input_sha256"].items():
    assert sha(HERE / name) == digest
for name, digest in record["prior_sha256"].items():
    assert sha(V21 / name) == digest
for name, digest in record["generated_sha256"].items():
    assert sha(HERE / name) == digest

judgments = json.loads((HERE / "row-challenge-v22.json").read_text())
prior = json.loads((V21 / "row-challenge-v21.json").read_text())
assert len(judgments) == len(prior) == 333
for current, old in zip(judgments, prior):
    assert current["id"] == old["id"] and current["title"] == old["title"]
    assert all(current[key] == value for key, value in old.items()), current["id"]
    assert current["v22_status"] == old["v21_status"]
    assert current["v22_gate_categories"] == old["v21_gate_categories"]
    assert current["v22_next_prerequisite"] == old["v21_next_prerequisite"]
    assert current["v22_new_distinct_cached_only_experiment_available"] is False
assert sum(bool(x["v22_new_evidence_packages"]) for x in judgments) == 62
assert {x["id"] for x in judgments if x["v22_specific_remaining_delta"] != x["v21_specific_remaining_delta"]} == set(record["residual_corrections"])
by_id = {x["id"]: x for x in judgments}
assert all(by_id[id_]["v22_new_evidence_packages"] == [SOURCE] for id_ in ("I05", "I06", "I07", "I08"))
assert all(not by_id[id_]["v22_new_evidence_packages"] for id_ in ("I005", "I006", "I007", "I008"))
assert by_id["I072"]["v22_status"] == "not-run"
assert by_id["F04"]["v22_status"] == "not-run"
assert by_id["I137"]["v22_status"] == by_id["I138"]["v22_status"] == "complete"
for id_ in ("I020", "I075", "I076", "I078", "I089", "I096", "I157", "L07", "L08"):
    assert by_id[id_]["v22_specific_remaining_delta"] != by_id[id_]["v21_specific_remaining_delta"]

for filename, count, key in (("investigation-final-v22.csv", 159, "id"), ("3730-crosswalk-final-v22.csv", 174, "3730_id")):
    old = read_csv(V21 / filename.replace("v22", "v21"))
    rows = read_csv(HERE / filename)
    assert len(rows) == len(old) == count == len({row[key] for row in rows})
    for current, prior_row in zip(rows, old):
        assert all(current[field] == value for field, value in prior_row.items()), current[key]
        assert current["status"] == current["v21_status"] == current["v22_status"]
        assert current["v22_specific_remaining_delta"] and current["v22_next_prerequisite"]
        assert current["v22_new_distinct_cached_only_experiment_available"] == "False"
assert len(read_csv(HERE / "unrun-conditional-inputs-v22.csv")) == 13
inventory = read_csv(HERE / "new-file-inventory-v22.csv")
assert len(inventory) == 2 and {x["relative_path"] for x in inventory} == {"REPORT.md", "REPORT.json"}
for entry in inventory:
    path = ROOT / "reports" / entry["package"] / entry["relative_path"]
    assert path.stat().st_size == int(entry["bytes"]) and sha(path) == entry["sha256"]
print("PASS: deterministic v22 333-row audit; 62 source-mapped rows, unchanged status counts and 13 gates; source report bytes verified")
