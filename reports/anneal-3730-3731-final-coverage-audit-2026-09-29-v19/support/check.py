#!/usr/bin/env python3
"""Validate v19 row decisions, deterministic build and new prototype evidence."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
NAMES = ("investigation-final-v19.csv", "3730-crosswalk-final-v19.csv", "new-package-review-v19.csv", "new-file-inventory-v19.csv", "unrun-conditional-inputs-v19.csv", "validation-v19.json")
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
before = {name: sha(HERE / name) for name in NAMES}
for _ in range(2):
    result = subprocess.run([sys.executable, str(HERE / "build_audit.py")], cwd=ROOT, capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert {name: sha(HERE / name) for name in NAMES} == before, "non-deterministic rebuild"
validation = json.loads((HERE / "validation-v19.json").read_text())
assert validation["reference_commit"] == "5f4c846fa5dddc19b649305d86d612bf142ce606"
assert validation["row_challenge_count"] == 333
assert validation["issue_3730_heading_count"] == 174 and validation["issue_3731_id_count"] == 159
assert validation["new_complete_ids"] == []
assert validation["status_counts"]["investigations"] == {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3}
assert validation["status_counts"]["suggestions"] == {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}
assert validation["unrun_conditional_count"] == 13
for filename, count, key in (("investigation-final-v19.csv", 159, "id"), ("3730-crosswalk-final-v19.csv", 174, "3730_id")):
    with (HERE / filename).open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == count == len({row[key] for row in rows})
    assert all(row["v19_specific_remaining_delta"] and row["v19_next_prerequisite"] and row["v19_post_v18_scope_assessment"] for row in rows)
    assert all(row["v19_new_distinct_cached_only_experiment_available"] == "False" for row in rows)
with (HERE / "investigation-final-v19.csv").open(newline="") as stream:
    by_id = {row["id"]: row for row in csv.DictReader(stream)}
assert all(by_id[item]["status"] == "partial" for item in ("I051",))
assert all(by_id[item]["v18_status"] == "partial" for item in ("I051",))
assert by_id["I051"]["v19_new_evidence_packages"] == "anneal-3731-real-generation-publication-v4-30-0-rc2"
with (HERE / "3730-crosswalk-final-v19.csv").open(newline="") as stream:
    suggestions = {row["3730_id"]: row for row in csv.DictReader(stream)}
assert all(suggestions[item]["status"] == "partial" and suggestions[item]["v19_new_evidence_packages"] == "anneal-3731-real-generation-publication-v4-30-0-rc2" for item in ("A03", "E04"))
with (HERE / "unrun-conditional-inputs-v19.csv").open(newline="") as stream:
    gates = list(csv.DictReader(stream))
assert len(gates) == 13 and all(row["exact_blocker_or_input"] for row in gates)
package = validation["new_packages"][0]
script = ROOT / "reports" / package / "support" / "check.py"
result = subprocess.run([sys.executable, str(script)], cwd=ROOT, capture_output=True, text=True, timeout=90)
assert result.returncode == 0, (package, result.stdout, result.stderr)
print("PASS: deterministic v19 159/174 row audit; I051/A03/E04 partial with new real-artifact evidence; new package checker")
