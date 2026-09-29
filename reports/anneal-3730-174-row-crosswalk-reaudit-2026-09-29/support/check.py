#!/usr/bin/env python3
"""Read-only validation of the retained 174-row crosswalk re-audit."""
import csv
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parent
reports = root.parents[1]
v22 = reports / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"
meta = json.loads((root.parent / "REPORT.json").read_text())
data = json.loads((root / "audit.json").read_text())
checks = json.loads((root / "checker-runs.json").read_text())
csv_file = v22 / "3730-crosswalk-final-v22.csv"
issues_file = v22 / "issue-scope-snapshot.json"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert digest(csv_file) == data["source_csv_sha256"] == meta["subjects"][0]["identity"]["crosswalk_sha256"]
assert digest(issues_file) == data["issue_snapshot_sha256"] == meta["subjects"][0]["identity"]["issue_snapshot_sha256"]
assert digest(root / "audit.json") == meta["subjects"][1]["identity"]["audit_sha256"]
assert digest(root / "checker-runs.json") == data["checker_runs_sha256"] == meta["subjects"][1]["identity"]["checker_runs_sha256"]
source = json.loads(issues_file.read_text())["3730"]["body"]
challenge = {x["id"] for x in json.loads((v22 / "row-challenge-v22.json").read_text())}
original = list(csv.DictReader(csv_file.open()))
rows = data["rows"]
assert len(original) == len(rows) == data["row_count"] == 174
assert len({r["id"] for r in rows}) == 174
assert [r["3730_id"] for r in original] == [r["id"] for r in rows]
assert data["destination_link_count"] == sum(len(r["destinations"]) for r in rows) == 345
assert all(re.search(r"(?m)^### " + r["id"] + r"\. ", source) for r in rows)
assert all(dest in challenge for row in rows for dest in row["destinations"])
packages = {p for row in rows for p in row["cited_packages"]}
evidence = {f for row in rows for f in row["cited_evidence_files"]}
assert len(packages) == data["unique_cited_packages"] == 106
assert len(evidence) == data["unique_cited_files"] == 364
assert all((reports / p).is_dir() for p in packages)
assert all(((reports.parent if f.startswith("reports/") else reports) / f).is_file() for f in evidence)
assert len(checks) == 64 and sum(c["exit"] == 0 for c in checks) == 63
assert sum(c["exit"] != 0 for c in checks) == 1
failed = next(c for c in checks if c["exit"] != 0)
assert failed["package"] == "anneal-3730-five-original-packages-rereview-2026-09-29"
assert "AssertionError" in failed["stderr_tail"]
assert sum(r["audit_finding"] != "no_further_discrepancy_found" for r in rows) == 23
assert next(r for r in rows if r["id"] == "C03")["recommended_status"] == "partial"
assert next(r for r in rows if r["id"] == "F15")["recommended_status"] == "partial"
markdown = (root.parent / "REPORT.md").read_text()
assert all(markdown.count("| " + r["id"] + " |") == 1 for r in rows)
print("PASS: 174 rows, 345 destinations, 106 packages, 364 files, 63/64 prior checker passes, 23 challenged rows")
