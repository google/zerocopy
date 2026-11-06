#!/usr/bin/env python3
"""Check retained I010 results without rerunning the filesystem probe."""
import json
from pathlib import Path

result = json.loads((Path(__file__).resolve().parent / "results.json").read_text())
trials = result["trials"]
assert set(trials) == {"re-resolved", "pinned", "mutable-generation"}
assert trials["pinned"]["matches_a"] is True
assert trials["pinned"]["matches_b"] is False
assert trials["pinned"]["manifest_digest"] == trials["pinned"]["a_manifest_digest"]
for name in ("re-resolved", "mutable-generation"):
    assert trials[name]["matches_a"] is False
    assert trials[name]["matches_b"] is False
    assert trials[name]["manifest_digest"] != trials[name]["a_manifest_digest"]
    assert trials[name]["manifest_digest"] != trials[name]["b_manifest_digest"]
    live = trials[name]["live_after"]
    assert live["renamed_source_present"] and live["old_source_absent"]
    assert live["symlink_target"] == "targets/beta"
assert "src/200.dat" in trials["re-resolved"]["missing_names"]
assert trials["re-resolved"]["key_entries"]["link"]["target"] == "targets/beta"
assert trials["re-resolved"]["key_entries"]["generated/010.bin"] != trials["pinned"]["key_entries"]["generated/010.bin"]
assert not trials["mutable-generation"]["missing_names"]
assert trials["mutable-generation"]["key_entries"]["src/220.dat"] != trials["pinned"]["key_entries"]["src/220.dat"]
print("I010 retained result checks passed")
