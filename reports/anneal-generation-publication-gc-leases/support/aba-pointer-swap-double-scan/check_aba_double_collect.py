#!/usr/bin/env python3
"""Check retained raw pointer-ABA result without rerunning the OS probe."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
r = json.loads((root / "aba-double-collect-results.json").read_text())
events = r["events"]
assert [(e["operation"], e.get("generation", e.get("name"))) for e in events] == [
    ("select", "A"), ("read", "x"),
    ("select", "B"), ("read", "y"),
    ("select", "A"), ("read", "x"),
    ("select", "B"), ("read", "y"),
    ("select", "A"),
]
assert [e["selected_before_open"] for e in events if e["operation"] == "read"] == ["A", "B", "A", "B"]
for item in r["first_collect"] + r["second_collect"]:
    assert item["sha256"] == hashlib.sha256(item["value"].encode()).hexdigest()
assert r["first_collect"] == r["second_collect"]
assert r["unfenced_equal_collects_accept"] is True
mixed = [item["value"] for item in r["first_collect"]]
assert mixed == [r["complete_generations"]["A"][0], r["complete_generations"]["B"][1]]
assert mixed not in r["complete_generations"].values()
assert r["mixed_collect_equal_to_complete_generation"] is False
assert r["pinned_values"] == r["complete_generations"][r["pinned_generation"]]
print("PASS: retained ABA schedule, identical mixed collects, and pinned-generation control")
