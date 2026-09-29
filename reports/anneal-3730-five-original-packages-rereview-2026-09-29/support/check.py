#!/usr/bin/env python3
"""Read-only verification of retained five-package review decisions."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

package = Path(__file__).resolve().parents[1]
reports = package.parent
review = json.loads((package / "support/review.json").read_text())
assert len(review["dispositions"]) == 5
assert len(review["files_sha256"]) == 18
second = review["second_pass"]
third = review["third_pass"]
assert len(second["dispositions"]) == 5
assert set(review["dispositions"]) == set(second["dispositions"])
assert set(second["dispositions"]) == set(third["dispositions"])
assert len(second["files_sha256"]) == 24
assert len(third["files_sha256"]) == 28
assert second["checkout_base_commit"] == "df4f6d6c84f936489c01edfa5ff19b2ee005f4d0"
assert third["historical_second_pass_commit"] == "c89f1410d4f1cfbd9b654ea5268b38f5c81e115e"
assert third["checkout_base_commit"] == "75fa78c1b623ab8db9d9acb4f31ec7958bfb9110"
assert set(review["files_sha256"]) <= set(second["files_sha256"])
assert set(second["files_sha256"]) <= set(third["files_sha256"])
for phase in (review, second, third):
    assert all(re.fullmatch(r"[0-9a-f]{64}", value) for value in phase["files_sha256"].values())
sha = lambda blob: hashlib.sha256(blob).hexdigest()
try:
    git_root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], cwd=reports.parent,
        capture_output=True, text=True,
    )
except FileNotFoundError:
    git_root = None
repo_history_available = (
    git_root is not None and git_root.returncode == 0
    and Path(git_root.stdout.strip()).resolve() == reports.parent.resolve()
)
if repo_history_available:
    for name, phase, commit in (
        ("first pass", review, second["checkout_base_commit"]),
        ("second pass", second, third["historical_second_pass_commit"]),
    ):
        for member, expected in phase["files_sha256"].items():
            original = subprocess.run(
                ["git", "show", f"{commit}:reports/{member}"],
                cwd=reports.parent, capture_output=True, check=True,
            ).stdout
            assert sha(original) == expected, (name, member)
for member, expected in third["files_sha256"].items():
    assert sha((reports / member).read_bytes()) == expected, ("third pass", member)
model = json.loads((reports / "anneal-interactive-model-probes-2026-09-29/support/model-probes.json").read_text())
cases = model["identity_ablation"]["cases"]
assert len(cases) == len({tuple(c["changed_fields"]) for c in cases}) == 10
assert any(c["changed_fields"] == ["llbc"] for c in cases)
assert [case["name"] for case in model["projection_coordinates"]["patch_cases"][-3:]] == [
    "stale host digest", "stale projection digest", "stale document version",
]
assert model["generation_schedule_model"]["safe_stale_publishes"] == 0
checker = (reports / "lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/support/check.py").read_text()
assert 'for name, document_version in (("NewOpen.lean", 1), ("OldOpen.lean", 2)):' in checker
assert '"Tactic `rfl` failed" in item.get("message", "")' in checker
lean_report = reports / "lean-import-refresh-cross-version-v4-29-to-v4-30-rc2"
fixture_identity = json.loads((lean_report / "REPORT.json").read_text())["subjects"][2]["identity"]
assert "revision" not in fixture_identity
lean_text = (lean_report / "REPORT.md").read_text()
assert "support/v429/transcript.json" in lean_text and "support/v430/transcript.json" in lean_text
simultaneous = json.loads((reports / "lean-same-server-dependency-generation-v4-30-0-rc2/support/simultaneous-transcript.json").read_text())
assert simultaneous["old_worker_goal_after_new_worker"]["result"]["rendered"] == "no goals"
assert simultaneous["new_worker_goal_same_server"]["result"]["goals"] == ["⊢ sharedValue = 3"]
latest = json.loads((reports / "aeneas-concurrent-generation-determinism-nightly-2026-06-03/support/simultaneous-transcript.json").read_text())
for name, count in (("independent", 4), ("shared", 3)):
    runs = latest["groups"][name]["runs"]
    assert len(runs) == count
    assert all(run["observed_alive"] and run["returncode"] == 0 for run in runs)
independent_hashes = {
    tuple(sorted((path, item["sha256"]) for path, item in run["inventory"].items()))
    for run in latest["groups"]["independent"]["runs"]
}
assert len(independent_hashes) == 1
assert tuple(sorted((path, item["sha256"]) for path, item in latest["groups"]["shared"]["final_inventory"].items())) in independent_hashes
gap = json.loads((reports / "anneal-interactive-model-probes-2026-09-29/support/supersession-gap.json").read_text())
assert (gap["valid_orders"], gap["delayed_stage_token_stale_publishes"], gap["request_time_token_stale_publishes"]) == (10, 2, 0)
same_server = reports / "lean-same-server-dependency-generation-v4-30-0-rc2"
direct_fixture = json.loads((same_server / "REPORT.json").read_text())["subjects"][1]["identity"]
assert direct_fixture["probe_sha256"] == sha((same_server / "support/probe.py").read_bytes())
for name in third["dispositions"]:
    subprocess.run([sys.executable, str(reports / name / "support/check.py")],
                   cwd=reports.parent, check=True, capture_output=True, text=True)
history_check = "18 first-pass and 24 second-pass Git blobs" if repo_history_available else "historical digest shapes (Git history unavailable)"
print(f"PASS: {history_check}, 28 current third-pass file hashes, five dispositions, five package checkers, and corrected controls")
