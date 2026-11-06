#!/usr/bin/env python3
"""Read-only, offline check of the retained evidence and deterministic replay."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
expected = (ROOT / "expected.json").read_bytes()
actual = subprocess.check_output([sys.executable, "-B", str(ROOT / "replay.py")])
if actual != expected:
    raise SystemExit("FAIL: replay output differs from expected.json")
records = json.loads(actual)
if len(records["runs"]) != 3:
    raise SystemExit("FAIL: expected three retained runs")
verdicts = {
    "recorded_arrival": (["current_live", "stale_snapshot"], ["⊢ False"]),
    "explicit_historical": (["current_live", "historical_only"], ["⊢ False"]),
    "old_reply_first_after_edit": (["stale_snapshot", "current_live"], ["⊢ False"]),
    "old_reply_before_edit": (["current_live", "current_live"], ["⊢ False"]),
    "restart_reuses_id_and_snapshot": (["expired_incarnation"], []),
    "same_version_changed_source": (["stale_snapshot"], []),
    "same_snapshot_changed_position": (["stale_snapshot"], []),
    "same_snapshot_changed_uri": (["stale_snapshot"], []),
}
for run_number, run in enumerate(records["runs"], 1):
    if run["run"] != run_number or set(run["cases"]) != set(verdicts):
        raise SystemExit("FAIL: missing or mislabeled run/case")
    for name, (decisions, final_latest) in verdicts.items():
        case = run["cases"][name]
        if ([reply["decision"] for reply in case["replies"]], case["final_latest"]) != (decisions, final_latest):
            raise SystemExit(f"FAIL: {name} in run {run_number}")
    if run["cases"]["recorded_arrival"]["replies"] != run["cases"]["explicit_historical"]["replies"][:1] + [
        {"request": 20, "goal": "⊢ True", "decision": "stale_snapshot"}
    ]:
        raise SystemExit("FAIL: old reply attribution")
print("PASS: 3 retained traces, 8 cases each; exact snapshot, history, and incarnation decisions")
