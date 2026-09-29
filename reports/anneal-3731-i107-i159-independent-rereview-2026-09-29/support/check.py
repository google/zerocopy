#!/usr/bin/env python3
"""Read-only validation of the dated review and its two direct Lean controls."""
import csv
import hashlib
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
V22 = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29-v22" / "support"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))

validation = json.loads((HERE / "validation.json").read_text())
assert validation["baseline_reference_head"] == "75fa78c1b623ab8db9d9acb4f31ec7958bfb9110"
for field, path in (
    ("v22_ledger_sha256", V22 / "investigation-final-v22.csv"),
    ("v22_row_challenge_sha256", V22 / "row-challenge-v22.json"),
    ("v22_issue_snapshot_sha256", V22 / "issue-scope-snapshot.json"),
):
    assert sha(path) == validation[field], field
for name, expected in validation["generated_sha256"].items():
    assert sha(HERE / name) == expected, name
for name, expected in validation["i147_probe_files_sha256"].items():
    assert sha(HERE / name) == expected, name

review = rows(HERE / "row-review.csv")
source = rows(V22 / "investigation-final-v22.csv")[106:159]
assert len(review) == len(source) == 53
assert [r["id"] for r in review] == [f"I{i:03}" for i in range(107, 160)]
assert Counter(r["review_status"] for r in review) == {"partial": 49, "complete": 2, "conditional": 2}
for item, prior in zip(review, source):
    assert item["id"] == prior["id"]
    assert item["title"] == prior["title"]
    assert item["exact_requested_scope"] == prior["requested_scope"]
    assert item["review_status"] == prior["v22_status"]
    assert item["v22_status_changed"] == "false"
    assert item["review_remaining_delta"]
assert [r["id"] for r in review if r["review_status"] == "complete"] == ["I137", "I138"]
assert [r["id"] for r in review if r["review_status"] == "conditional"] == ["I141", "I143"]
by_id = {r["id"]: r for r in review}
assert "build scripts and proc macros" in by_id["I126"]["review_remaining_delta"]
assert "same-nanosecond-mtime" in by_id["I147"]["review_remaining_delta"]
assert "two conflicting Lake processes" in by_id["I151"]["review_remaining_delta"]

packages = rows(HERE / "cited-package-inventory.csv")
evidence = rows(HERE / "cited-evidence-inventory.csv")
assert len(packages) == validation["counts"]["packages"] == 123
assert sum(bool(r["checker_sha256"]) for r in packages) == validation["counts"]["package_checkers"] == 44
assert len(evidence) == validation["counts"]["evidence_files"] == 232
for row in packages:
    directory = REPORTS / row["package"]
    assert sha(directory / "REPORT.md") == row["report_md_sha256"]
    assert sha(directory / "REPORT.json") == row["report_json_sha256"]
    checker = directory / "support/check.py"
    assert (sha(checker) if checker.is_file() else "") == row["checker_sha256"]
for row in evidence:
    pointer = row["pointer"]
    path = ROOT / pointer if pointer.startswith("reports/") else REPORTS / pointer
    assert sha(path) == row["sha256"], pointer

def samples(events):
    return {e["phase"]: e for e in events if e["kind"] == "sample"}

def goal(sample):
    return sample["goals"]["rfl-end"].get("result", {}).get("goals")

mtime = HERE / "i147-same-mtime"
events = json.loads((mtime / "transcript.json").read_text())
assert not any(e["kind"] == "fatal" for e in events)
fixture = next(e for e in events if e["kind"] == "fixture")
change = next(e for e in events if e["kind"] == "olean_only_change")
assert fixture["artifact"]["sha256"] == sha(mtime / "baseline-Dep.olean")
assert change["artifact"]["sha256"] == sha(mtime / "value9-Dep.olean")
assert fixture["artifact"]["sha256"] != change["artifact"]["sha256"]
assert fixture["artifact"]["mtime_ns"] == change["artifact"]["mtime_ns"] == change["original_mtime_ns"]
assert fixture["artifact"]["hash_sidecar"] == change["artifact"]["hash_sidecar"]
assert fixture["source_sha256"] == change["source_sha256"]
ss = samples(events)
assert goal(ss["baseline"]) == goal(ss["old-open"]) == goal(ss["old-after-new"]) == []
assert goal(ss["new-open"]) == goal(ss["reopened"]) == goal(ss["fresh-server"]) == ["⊢ selected = 7"]
assert all(e["artifact"]["sha256"] == change["artifact"]["sha256"] for e in ss.values() if e["phase"] != "baseline")
setup = [e for e in events if e["kind"] in ("setup_file", "setup_file_rehash")]
assert len(setup) == 3
assert all(e["rc"] == 0 and e["after"]["sha256"] == change["artifact"]["sha256"] for e in setup)
batch = json.loads((mtime / "fresh-batch.json").read_text())
assert batch["exit"] == 1 and batch["artifact_sha256"] == change["artifact"]["sha256"]
assert batch["source_sha256"] == sha(mtime / "Check.lean")
assert "Tactic `rfl` failed" in batch["stdout"] and '"data":"9"' in batch["stdout"]

comment = HERE / "i147-comment-equivalence"
events = json.loads((comment / "transcript.json").read_text())
assert not any(e["kind"] == "fatal" for e in events)
fixture = next(e for e in events if e["kind"] == "fixture")
change = next(e for e in events if e["kind"] == "source_only_change")
assert fixture["source_sha256"] != change["source_sha256"]
assert fixture["artifact"]["sha256"] == sha(comment / "baseline-Dep.olean")
assert sha(comment / "baseline-Dep.olean") == sha(comment / "comment-Dep.olean")
ss = samples(events)
assert list(ss) == ["baseline", "old-open", "new-open", "old-after-new", "reopened"]
assert all(goal(e) == [] for e in ss.values())
assert all(e["artifact"]["sha256"] == fixture["artifact"]["sha256"] for e in ss.values())
assert any(e["kind"] == "server" and "Built Dep" in str(e["message"])
           for e in events), "new file must cause the recorded rebuild"
batch = json.loads((comment / "fresh-batch.json").read_text())
assert batch["exit"] == 0 and batch["artifact_sha256"] == fixture["artifact"]["sha256"]
assert batch["source_sha256"] == sha(comment / "Check.lean")
assert '"data":"7"' in batch["stdout"]

print("PASS: 53 reviewed rows, 123 cited packages, 232 evidence files, and both I147 controls")
