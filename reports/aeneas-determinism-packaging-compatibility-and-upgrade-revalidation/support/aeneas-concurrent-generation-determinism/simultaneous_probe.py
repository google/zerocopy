#!/usr/bin/env python3
"""Observe all same-input Aeneas children live after the final spawn."""
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import tempfile
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
FIXTURE = ROOT / "fixture/probe.llbc"
AENEAS = Path(os.environ["AENEAS_BIN"]).resolve()
FLAGS = ["-backend", "lean", "-no-progress-bar", "-sequential", "-split-files", "-gen-lib-entry"]
EXPECTED_BINARY = "f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03"
EXPECTED_INPUT = "b98023ca3d222796ed4f08e9331e8ffa750c8971daeb786fea37a888b8c8d098"
EXPECTED_FILES = {"Funs.lean", "Probe.lean", "Types.lean"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(directory):
    return {
        path.relative_to(directory).as_posix(): {"sha256": sha(path), "bytes": path.stat().st_size}
        for path in sorted(directory.rglob("*")) if path.is_file()
    }


def run_group(scratch, name, count):
    group = scratch / name
    group.mkdir()
    destinations = ([group / f"worker-{i}" for i in range(count)]
                    if name == "independent" else [group] * count)
    children = []
    records = []
    try:
        for index, destination in enumerate(destinations):
            child = subprocess.Popen(
                [str(AENEAS), *FLAGS, "-dest", str(destination), str(FIXTURE)],
                cwd=scratch,
                env=dict(os.environ, LC_ALL="C", TZ="UTC"),
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            )
            children.append(child)
            records.append({
                "label": f"{name}-{index}", "pid": child.pid,
                "destination": destination.relative_to(scratch).as_posix(),
                "spawned_ns": time.monotonic_ns(),
            })
        # All children have been spawned. A later live observation also proves
        # that child was alive at the first observation, before it could exit.
        for child, record in zip(children, records):
            record["observed_alive"] = child.poll() is None
            record["observed_ns"] = time.monotonic_ns()
        for child, record in zip(children, records):
            stdout, stderr = child.communicate(timeout=30)
            record["collected_ns"] = time.monotonic_ns()
            record["returncode"] = child.returncode
            record["stdout"] = stdout.replace(str(scratch), "$SCRATCH").replace(str(ROOT), "$REPORT_SUPPORT")
            record["stderr"] = stderr.replace(str(scratch), "$SCRATCH").replace(str(ROOT), "$REPORT_SUPPORT")
            if name == "independent":
                record["inventory"] = inventory(scratch / record["destination"])
    finally:
        for child in children:
            if child.poll() is None:
                child.kill()
                child.communicate()
    return {"runs": records, "final_inventory": inventory(group) if name == "shared" else None}


assert sha(AENEAS) == EXPECTED_BINARY
assert sha(FIXTURE) == EXPECTED_INPUT
with tempfile.TemporaryDirectory(prefix="aeneas-live-", dir=os.environ.get("AENEAS_SCRATCH_DIR")) as tmp:
    scratch = Path(tmp)
    result = {
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "host": {"system": platform.system(), "machine": platform.machine()},
        "binary_sha256": sha(AENEAS), "input_sha256": sha(FIXTURE),
        "input_bytes": FIXTURE.stat().st_size,
        "flags": FLAGS, "cwd": "$SCRATCH",
        "groups": {
            "independent": run_group(scratch, "independent", 4),
            "shared": run_group(scratch, "shared", 3),
        },
    }
oracle = result["groups"]["independent"]["runs"][0]["inventory"]
for name, group in result["groups"].items():
    runs = group["runs"]
    assert all(r["observed_alive"] for r in runs)
    assert max(r["spawned_ns"] for r in runs) < min(r["observed_ns"] for r in runs)
    assert all(r["returncode"] == 0 and r["stderr"] == "" for r in runs)
    if name == "independent":
        assert all(r["inventory"] == oracle for r in runs)
    else:
        assert group["final_inventory"] == oracle
assert set(oracle) == EXPECTED_FILES and all(v["bytes"] > 0 for v in oracle.values())
(ROOT / "simultaneous-transcript.json").write_text(json.dumps(result, indent=2) + "\n")
print("PASS: all 4 independent and all 3 shared-destination children observed live after final spawn")
