#!/usr/bin/env python3
"""Validate v21 row decisions, deterministic build and new prototype evidence."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
NAMES = ("investigation-final-v21.csv", "3730-crosswalk-final-v21.csv", "new-package-review-v21.csv", "new-file-inventory-v21.csv", "unrun-conditional-inputs-v21.csv", "validation-v21.json")
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
before = {name: sha(HERE / name) for name in NAMES}
for _ in range(2):
    result = subprocess.run([sys.executable, str(HERE / "build_audit.py")], cwd=ROOT, capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert {name: sha(HERE / name) for name in NAMES} == before, "non-deterministic rebuild"
validation = json.loads((HERE / "validation-v21.json").read_text())
assert validation["reference_commit"] == "c89f1410d4f1cfbd9b654ea5268b38f5c81e115e"
assert validation["row_challenge_count"] == 333
assert validation["issue_3730_heading_count"] == 174 and validation["issue_3731_id_count"] == 159
assert validation["new_complete_ids"] == []
assert validation["status_counts"]["investigations"] == {"complete": 4, "partial": 151, "not-run": 1, "conditional": 3}
assert validation["status_counts"]["suggestions"] == {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}
assert validation["unrun_conditional_count"] == 13
for filename, count, key in (("investigation-final-v21.csv", 159, "id"), ("3730-crosswalk-final-v21.csv", 174, "3730_id")):
    with (HERE / filename).open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == count == len({row[key] for row in rows})
    assert all(row["v21_specific_remaining_delta"] and row["v21_next_prerequisite"] and row["v21_post_v20_scope_assessment"] for row in rows)
    assert all(row["v21_new_distinct_cached_only_experiment_available"] == "False" for row in rows)
with (HERE / "investigation-final-v21.csv").open(newline="") as stream:
    by_id = {row["id"]: row for row in csv.DictReader(stream)}
assert by_id["I121"]["status"] == by_id["I121"]["v20_status"] == "partial"
assert by_id["I121"]["v21_new_evidence_packages"] == "anneal-3731-reader-owned-generation-lease-v4-30-0-rc2"
assert "Actual Anneal-owned lease acquisition" in by_id["I121"]["v21_specific_remaining_delta"]
assert by_id["I122"]["status"] == "partial"
assert by_id["I122"]["v21_new_evidence_packages"] == "anneal-3731-reader-owned-generation-lease-v4-30-0-rc2"
assert "does not reconstruct Anneal" in by_id["I122"]["v21_post_v20_scope_assessment"]
with (HERE / "3730-crosswalk-final-v21.csv").open(newline="") as stream:
    suggestions = {row["3730_id"]: row for row in csv.DictReader(stream)}
assert suggestions["J11"]["status"] == suggestions["J11"]["v20_status"] == "partial"
assert suggestions["J11"]["v21_new_evidence_packages"] == "anneal-3731-reader-owned-generation-lease-v4-30-0-rc2"
assert "Anneal-owned reader leases" in suggestions["J11"]["v21_specific_remaining_delta"]
with (HERE / "unrun-conditional-inputs-v21.csv").open(newline="") as stream:
    gates = list(csv.DictReader(stream))
assert len(gates) == 13 and all(row["exact_blocker_or_input"] for row in gates)
package = validation["new_packages"][0]
script = ROOT / "reports" / package / "support" / "check.py"
result = subprocess.run([sys.executable, str(script)], cwd=ROOT, capture_output=True, text=True, timeout=90)
assert result.returncode == 0, (package, result.stdout, result.stderr)
print("PASS: deterministic v21 159/174 row audit; I121/J11 partial with new reader-owned lease evidence; new package checker")
