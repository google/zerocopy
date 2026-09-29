#!/usr/bin/env python3
"""Finite counterexample for advancing a generation token only after staging."""
import itertools
import json
import sys
from pathlib import Path

output = Path(__file__).with_name("supersession-gap.json")
events = ("stageA", "requestB", "stageB", "publishA", "publishB")
valid_orders = []
stale_gap_orders = []
delayed_guard_stale_publishes = 0
request_guard_stale_publishes = 0
delayed_guard_accepts = 0
request_guard_accepts = 0

for order in itertools.permutations(events):
    # Both outputs must be staged before publication; B must be requested before
    # it stages. These constraints leave all other interleavings unrestricted.
    if not (order.index("stageA") < order.index("publishA")
            and order.index("requestB") < order.index("stageB") < order.index("publishB")):
        continue
    valid_orders.append(order)
    desired = "A"
    delayed_token = "A"
    request_token = "A"
    for event in order:
        if event == "requestB":
            desired = "B"
            request_token = "B"
        elif event == "stageB":
            delayed_token = "B"
        elif event.startswith("publish"):
            generation = event[-1]
            if generation == delayed_token:
                delayed_guard_accepts += 1
                if generation != desired:
                    delayed_guard_stale_publishes += 1
                    stale_gap_orders.append(order)
            if generation == request_token:
                request_guard_accepts += 1
                if generation != desired:
                    request_guard_stale_publishes += 1

assert len(valid_orders) == 10
assert delayed_guard_stale_publishes == 2
assert request_guard_stale_publishes == 0
assert delayed_guard_accepts > request_guard_accepts >= 10
assert len(set(stale_gap_orders)) == 2

result = {
    "events": list(events),
    "valid_orders": len(valid_orders),
    "constraints": ["stageA before publishA", "requestB before stageB before publishB"],
    "delayed_stage_token_stale_publishes": delayed_guard_stale_publishes,
    "request_time_token_stale_publishes": request_guard_stale_publishes,
    "delayed_stage_token_accepted_publications": delayed_guard_accepts,
    "request_time_token_accepted_publications": request_guard_accepts,
    "stale_gap_orders": [list(order) for order in stale_gap_orders],
    "interpretation": "A token advanced only at stageB admits A publication after requestB and before stageB; advancing the desired token at requestB rejects it.",
}

if sys.argv[1:] == ["--check"]:
    assert json.loads(output.read_text()) == result
    print("PASS: retained supersession-gap result matches a fresh run")
elif not sys.argv[1:]:
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
else:
    raise SystemExit("usage: supersession_gap_probe.py [--check]")
