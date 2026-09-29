#!/usr/bin/env python3
"""Validate the retained Aeneas concurrency transcript and generated files."""
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TRANSCRIPT = json.loads((ROOT / "concurrency-transcript.json").read_text())
EXPECTED_BINARY = "f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03"
EXPECTED_INPUT = "b98023ca3d222796ed4f08e9331e8ffa750c8971daeb786fea37a888b8c8d098"
EXPECTED_FILES = {"Funs.lean", "Probe.lean", "Types.lean"}
FLAGS = ["-backend", "lean", "-no-progress-bar", "-sequential", "-split-files", "-gen-lib-entry"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(path):
    return {
        file.relative_to(path).as_posix(): {"sha256": sha(file), "bytes": file.stat().st_size}
        for file in sorted(path.rglob("*")) if file.is_file()
    }


assert TRANSCRIPT["aeneas_sha256"] == EXPECTED_BINARY
assert TRANSCRIPT["input_sha256"] == EXPECTED_INPUT
assert TRANSCRIPT["input_bytes"] == (ROOT / "fixture/probe.llbc").stat().st_size
assert sha(ROOT / "fixture/probe.llbc") == EXPECTED_INPUT
if os.environ.get("AENEAS_BIN"):
    assert sha(Path(os.environ["AENEAS_BIN"]).resolve()) == EXPECTED_BINARY
assert TRANSCRIPT["cwd"] == "parent of reference-publish checkout (resolved from report fixture)"

independent = TRANSCRIPT["processes"]["independent_destination"]
shared = TRANSCRIPT["processes"]["same_writable_destination"]
assert len(independent) == 4 and len(shared) == 3
all_runs = independent + shared
assert len({r["pid"] for r in independent}) == 4
assert len({r["pid"] for r in shared}) == 3
for run in all_runs:
    assert run["argv_flags"] == FLAGS
    assert run["returncode"] == 0 and run["stderr"] == ""
    assert run["spawned_alive"] is True
    assert run["started_ns"] <= run["spawned_ns"] < run["ended_ns"]
    assert set(run["inventory"]) == EXPECTED_FILES
    assert all(v["bytes"] > 0 for v in run["inventory"].values())
    assert "Generated:" in run["stdout"]
assert max(r["spawned_ns"] for r in independent) < min(r["ended_ns"] for r in independent)
assert max(r["spawned_ns"] for r in shared) < min(r["ended_ns"] for r in shared)

oracle = independent[0]["inventory"]
assert all(r["inventory"] == oracle for r in all_runs)
for run in independent:
    assert inventory(ROOT / "parallel-independent" / run["destination"]) == oracle
assert inventory(ROOT / "parallel-shared-dest") == oracle
summary = TRANSCRIPT["summary"]
assert all(summary[key] is True for key in (
    "independent_all_exit_0", "independent_outputs_identical", "shared_all_exit_0",
    "shared_process_inventories_identical", "shared_outputs_complete",
    "shared_final_matches_independent", "independent_runs_overlapped", "shared_runs_overlapped",
))
assert summary["independent_inventory"] == summary["shared_final_inventory"] == oracle
print("PASS: 7 pinned Aeneas processes, overlapping post-spawn intervals, matching retained outputs")
