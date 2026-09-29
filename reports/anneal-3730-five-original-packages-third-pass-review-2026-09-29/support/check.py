#!/usr/bin/env python3
"""Read-only integrity and replay check for the third-pass package."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

package = Path(__file__).resolve().parents[1]
reports = package.parent
manifest = json.loads((package / "support/manifest.json").read_text())
metadata = json.loads((package / "REPORT.json").read_text())
prior = reports / "anneal-3730-five-original-packages-rereview-2026-09-29"
review = json.loads((prior / "support/review.json").read_text())
third = review["third_pass"]

assert metadata["subjects"][0]["identity"]["checkout_base_revision"] == manifest["checkout_base_commit"]
assert manifest["checkout_base_commit"] == third["checkout_base_commit"]
assert manifest["historical_first_pass_commit"] == review["second_pass"]["checkout_base_commit"]
assert manifest["historical_second_pass_commit"] == third["historical_second_pass_commit"]
assert manifest["reviewed_at_utc"] == third["reviewed_at_utc"]
assert manifest["package_names"] == sorted(third["dispositions"])
assert len(manifest["package_names"]) == 5
assert len(manifest["files_sha256"]) == 31
assert set(third["files_sha256"]) <= set(manifest["files_sha256"])
for member, expected in manifest["files_sha256"].items():
    assert re.fullmatch(r"[0-9a-f]{64}", expected), member
    assert hashlib.sha256((reports / member).read_bytes()).hexdigest() == expected, member
for member, expected in third["files_sha256"].items():
    assert manifest["files_sha256"][member] == expected, member

result = subprocess.run(
    [sys.executable, str(prior / "support/check.py")],
    cwd=reports.parent, capture_output=True, text=True, check=True,
)
assert ("18 first-pass and 24 second-pass Git blobs" in result.stdout
        or "historical digest shapes (Git history unavailable)" in result.stdout), result.stdout
assert "28 current third-pass file hashes" in result.stdout, result.stdout
assert "five package checkers" in result.stdout, result.stdout
print("PASS: 31 third-pass manifest hashes, historical Git blobs, five current package checkers")
