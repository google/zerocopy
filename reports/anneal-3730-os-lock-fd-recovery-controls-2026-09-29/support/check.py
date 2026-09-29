#!/usr/bin/env python3
"""Validate the retained bounded OS controls without rerunning them."""
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
data = json.loads((here / "results.json").read_text())
assert data["platform"] == "darwin"
cycle = data["lock_order_cycle"]
assert cycle["both_first_locks_held"] and cycle["both_second_locks_attempted"]
assert cycle["both_blocked_before_kill"]
assert cycle["victim_exit"] == -9
assert cycle["survivor_exit"] == 0 and cycle["survivor_acquired_after_victim_kill"]
ordered = data["consistent_order"]
assert ordered["second_waited_for_first"]
assert ordered["first_acquired_both"] and ordered["second_acquired_both"]
assert ordered["exits"] == [0, 0]
fd = data["fd_exhaustion"]
assert fd["soft_nofile"] == 32 and fd["opened_extra_descriptors"] >= 20
assert fd["stage_failed_emfile"]
assert fd["pointer_after_failure"] == "A" and fd["pointer_after_retry"] == "B"
assert fd["last_good_sha256"] == hashlib.sha256(b"last-good-A\n").hexdigest()
assert fd["retry_artifact_sha256"] == hashlib.sha256(b"candidate-B\n").hexdigest()
print("I108/I109 retained OS controls passed")
