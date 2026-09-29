#!/usr/bin/env python3
"""Validate retained v17 row judgments, package evidence and deterministic build."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
NAMES = ("investigation-final-v17.csv", "3730-crosswalk-final-v17.csv", "post-v16-package-review.csv", "post-v16-file-inventory.csv", "validation-v17.json")
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
before = {name: sha(HERE / name) for name in NAMES}
for _ in range(2):
    result = subprocess.run([sys.executable, str(HERE / "build_audit.py")], cwd=ROOT, capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert {name: sha(HERE / name) for name in NAMES} == before, "non-deterministic rebuild"
validation = json.loads((HERE / "validation-v17.json").read_text())
assert validation["reference_commit"] == "2c45d74f7176d15a417f9a78a60afaf66eb2fdf2"
assert validation["row_challenge_count"] == 333
assert validation["issue_3730_heading_count"] == 174
assert validation["issue_3731_id_count"] == 159
assert validation["new_distinct_cached_only_experiment_count"] == 0
assert validation["status_counts"]["investigation"] == {"complete": 2, "partial": 153, "not-run": 1, "conditional": 3}
assert validation["status_counts"]["suggestion"] == {"complete": 4, "partial": 161, "not-run": 5, "conditional": 4}
for filename, count, key in (("investigation-final-v17.csv", 159, "id"), ("3730-crosswalk-final-v17.csv", 174, "3730_id")):
    with (HERE / filename).open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == count == len({row[key] for row in rows})
    assert all(row["v17_specific_remaining_delta"] and row["v17_next_prerequisite"] and row["v17_post_v16_scope_assessment"] for row in rows)
    assert all(row["v17_new_distinct_cached_only_experiment_available"] == "False" for row in rows)
for package in validation["post_v16_packages"]:
    script = ROOT / "reports" / package / "support" / "check.py"
    result = subprocess.run([sys.executable, str(script)], cwd=ROOT, capture_output=True, text=True, timeout=90)
    assert result.returncode == 0, (package, result.stdout, result.stderr)
print("PASS: deterministic v17 159/174 row audit; two post-v16 package checkers")
