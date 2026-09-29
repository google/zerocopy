#!/usr/bin/env python3
"""Recheck frozen v22 scope, mappings, selected evidence, and later C03 gap."""
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
reports = here.parents[1]
root = reports.parent
review = json.loads((here / "review.json").read_text())
v22 = reports / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support"

def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))

for member, expected in review["files_sha256"].items():
    assert hashlib.sha256((reports / member).read_bytes()).hexdigest() == expected, member

issue = json.loads((v22 / "issue-scope-snapshot.json").read_text())
body = issue["3731"]["body"]
comment = issue["3731"]["comments"][0]["body"]
titles = {
    item: re.sub(r"\s*\[[^]]+\]\.?$", "", title).strip()
    for source in (body, comment)
    for item, title in re.findall(r"(?m)^\*\*(I\d{3})\s+[—.]\s+([^\n]*?)\*\*", source)
}
suggestions = {
    item: (title.strip(), set(re.findall(r"I\d{3}", destinations)))
    for item, title, destinations in re.findall(
        r"(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|", comment
    )
}
investigations = rows(v22 / "investigation-final-v22.csv")
crosswalk = rows(v22 / "3730-crosswalk-final-v22.csv")
challenge = json.loads((v22 / "row-challenge-v22.json").read_text())
assert len(titles) == len(investigations) == 159
assert len(suggestions) == len(crosswalk) == 174
assert len(challenge) == 333 == len({row["id"] for row in challenge})
assert {row["id"] for row in investigations} == set(titles)
assert {row["3730_id"] for row in crosswalk} == set(suggestions)
for row in investigations:
    assert row["title"] == titles[row["id"]], row["id"]
for row in crosswalk:
    title, destinations = suggestions[row["3730_id"]]
    assert row["suggestion"] == title, row["3730_id"]
    assert set(re.findall(r"I\d{3}", row["3731_destinations"])) == destinations, row["3730_id"]
assert sum(len(destinations) for _, destinations in suggestions.values()) == 345
assert {row["id"] for row in challenge if row["v22_status"] == "complete"} == {
    "I046", "I049", "I137", "I138", "C03", "C04", "C13", "N11"
}
assert sum(row["v22_status"] in ("not-run", "conditional") for row in challenge) == 13
assert sum(bool(row["v22_new_evidence_packages"]) for row in challenge) == 62
packages = {
    name
    for source in (investigations, crosswalk)
    for row in source
    for field, value in row.items()
    if field.endswith("packages")
    for name in value.split(";") if name
}
assert len(packages) == 175
assert all((reports / name / "REPORT.md").is_file() and
           (reports / name / "REPORT.json").is_file() for name in packages)

c03 = re.search(r"(?ms)^### C03\..*?(?=^### [A-O]\d{2}\.|\Z)", issue["3730"]["body"]).group()
assert all(term in c03 for term in (
    "resend proof document", "restart file worker", "restart entire server",
    "new workspace/server generation", "fresh batch Lean"
))
for target in (
    v22 / "check.py",
    reports / "anneal-3731-embedded-proof-generated-model-vertical-v4-30-0-rc2/support/check.py",
    reports / "anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2/support/summarize.py",
    reports / "anneal-3730-c03-proof-resend-refresh-2026-09-29/support/check.py",
):
    result = subprocess.run([sys.executable, str(target)], cwd=root,
                            capture_output=True, text=True, check=True)
    assert result.stdout.strip(), target
print("PASS: 333 issue rows, 345 exact crosswalk links, 175 cited packages, four decisive checks, C03 gap")
