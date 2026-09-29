#!/usr/bin/env python3
"""Check retained 53-row decision and evidence records without rerunning probes."""
import csv
import hashlib
import json
import re
import runpy
from pathlib import Path

support = Path(__file__).resolve().parent
package = support.parent
reports = package.parent
markdown = (package / "REPORT.md").read_text()
ids = re.findall(r"^\| (I\d{3}) \| ([AP]) \|", markdown, re.M)
assert ids == [(f"I{i:03d}", "A" if i in (46, 49) else "P") for i in range(1, 54)]
v22 = reports / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22"
with (v22 / "support/investigation-final-v22.csv").open() as stream:
    source = list(csv.DictReader(stream))[:53]
assert [r["id"] for r in source] == [row[0] for row in ids]
assert [(r["id"], r["v22_status"]) for r in source if r["v22_status"] == "complete"] == [
    ("I046", "complete"), ("I049", "complete")
]
index = json.loads((support / "package-evidence-index.json").read_text())
assert len(index) == len({r["package"] for r in index}) == 68
assert all(r["report_md"] and r["report_json"] for r in index)
assert sum(r["checker_exit"] == 0 for r in index) == 24
assert sum(r["checker_exit"] == 1 for r in index) == 1
bad = [r for r in index if r["checker_exit"] == 1]
assert bad[0]["package"] == "anneal-3730-five-original-packages-rereview-2026-09-29"
runs = json.loads((support / "checker-runs.json").read_text())
assert len(runs) == 25
assert {r["package"]: r["exit"] for r in runs} == {
    r["package"]: r["checker_exit"] for r in index if r["checker_present"]
}
stale = json.loads((support / "stale-hashes.json").read_text())["mismatches"]
assert len(stale) == 8
assert len({r["path"] for r in stale}) == 8
assert all(re.fullmatch(r"[0-9a-f]{64}", r[key]) for r in stale for key in ("historical_sha256", "current_sha256"))
assert all(r["historical_sha256"] != r["current_sha256"] for r in stale)
metadata = json.loads((package / "REPORT.json").read_text())
probe_hash = hashlib.sha256((support / "aba_double_collect.py").read_bytes()).hexdigest()
assert metadata["subjects"][1]["identity"]["probe_sha256"] == probe_hash
runpy.run_path(str(support / "check_aba_double_collect.py"), run_name="__main__")
print("PASS: 53 row decisions, 68 cited packages, 24 checker passes, one checker failure, eight stale hashes")
