#!/usr/bin/env python3
"""Validate v18 row decisions, deterministic build and new prototype evidence."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
NAMES = ("investigation-final-v18.csv", "3730-crosswalk-final-v18.csv", "new-package-review-v18.csv", "new-file-inventory-v18.csv", "unrun-conditional-inputs-v18.csv", "validation-v18.json")
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
before = {name: sha(HERE / name) for name in NAMES}
for _ in range(2):
    result = subprocess.run([sys.executable, str(HERE / "build_audit.py")], cwd=ROOT, capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert {name: sha(HERE / name) for name in NAMES} == before, "non-deterministic rebuild"
validation = json.loads((HERE / "validation-v18.json").read_text())
assert validation["reference_commit"] == "b1787210c0143a705f6bbbf2da3b2fba30cc5718"
assert validation["row_challenge_count"] == 333
assert validation["issue_3730_heading_count"] == 174 and validation["issue_3731_id_count"] == 159
assert validation["new_complete_ids"] == ["I137", "I138"]
assert validation["status_counts"]["investigations"] == {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3}
assert validation["status_counts"]["suggestions"] == {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}
assert validation["unrun_conditional_count"] == 13
for filename, count, key in (("investigation-final-v18.csv", 159, "id"), ("3730-crosswalk-final-v18.csv", 174, "3730_id")):
    with (HERE / filename).open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == count == len({row[key] for row in rows})
    assert all(row["v18_specific_remaining_delta"] and row["v18_next_prerequisite"] and row["v18_post_v17_scope_assessment"] for row in rows)
    assert all(row["v18_new_distinct_cached_only_experiment_available"] == "False" for row in rows)
with (HERE / "investigation-final-v18.csv").open(newline="") as stream:
    by_id = {row["id"]: row for row in csv.DictReader(stream)}
assert all(by_id[item]["status"] == "complete" for item in ("I137", "I138"))
assert all(by_id[item]["v17_status"] == "partial" for item in ("I137", "I138"))
with (HERE / "unrun-conditional-inputs-v18.csv").open(newline="") as stream:
    gates = list(csv.DictReader(stream))
assert len(gates) == 13 and all(row["exact_blocker_or_input"] for row in gates)
package = validation["new_packages"][0]
script = ROOT / "reports" / package / "support" / "check.py"
result = subprocess.run([sys.executable, str(script)], cwd=ROOT, capture_output=True, text=True, timeout=90)
assert result.returncode == 0, (package, result.stdout, result.stderr)
print("PASS: deterministic v18 159/174 row audit; I137/I138 narrow completion; new package checker")
