#!/usr/bin/env python3
"""Bounded Aeneas CLI process-isolation and destination-ownership comparator."""

import hashlib
import json
import os
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixture"
ARTIFACTS = HERE / "artifacts"
OUT = HERE / "raw-results.json"
AENEAS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/bin/aeneas")
BASE_FLAGS = ["-backend", "lean", "-no-progress-bar", "-sequential", "-split-files", "-gen-lib-entry"]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inventory(root):
    return {str(p.relative_to(root)): {"sha256": sha(p), "bytes": p.stat().st_size}
            for p in sorted(root.rglob("*")) if p.is_file()}


def call(label, llbc, destination, flags=BASE_FLAGS):
    destination.mkdir(parents=True, exist_ok=True)
    command = [str(AENEAS), *flags, "-dest", str(destination), str(FIXTURE / llbc)]
    start = time.monotonic_ns()
    result = subprocess.run(command, cwd=HERE, capture_output=True, text=True, timeout=30)
    end = time.monotonic_ns()
    return {"label": label, "input": llbc, "input_sha256": sha(FIXTURE / llbc),
            "flags": flags, "command": command, "start_ns": start, "end_ns": end,
            "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr,
            "inventory": inventory(destination)}


def concurrent_group(label, inputs, root):
    processes = []
    for index, llbc in enumerate(inputs):
        destination = root / f"worker-{index}"
        destination.mkdir(parents=True)
        command = [str(AENEAS), *BASE_FLAGS, "-dest", str(destination), str(FIXTURE / llbc)]
        start = time.monotonic_ns()
        process = subprocess.Popen(command, cwd=HERE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        processes.append((index, llbc, destination, command, start, process))
    def collect(job):
        index, llbc, destination, command, start, process = job
        stdout, stderr = process.communicate(timeout=30)
        end = time.monotonic_ns()
        return {"label": f"{label}-worker-{index}", "input": llbc,
                "input_sha256": sha(FIXTURE / llbc), "flags": BASE_FLAGS,
                "command": command, "start_ns": start, "end_ns": end,
                "exit_code": process.returncode, "stdout": stdout, "stderr": stderr,
                "inventory": inventory(destination)}
    with ThreadPoolExecutor(max_workers=len(processes)) as pool:
        records = list(pool.map(collect, processes))
    overlap_pairs = [[a["label"], b["label"]] for i, a in enumerate(records)
                     for b in records[i+1:] if max(a["start_ns"], b["start_ns"]) < min(a["end_ns"], b["end_ns"])]
    return {"jobs": len(inputs), "records": records, "overlap_pairs": overlap_pairs}


def different_input_shared(root):
    root.mkdir(parents=True)
    jobs = []
    for label, llbc in (("A", "A.llbc"), ("B", "B.llbc")):
        command = [str(AENEAS), *BASE_FLAGS, "-dest", str(root), str(FIXTURE / llbc)]
        start = time.monotonic_ns()
        process = subprocess.Popen(command, cwd=HERE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        jobs.append((label, llbc, command, start, process))
    def collect(job):
        label, llbc, command, start, process = job
        stdout, stderr = process.communicate(timeout=30)
        return {"label": label, "input": llbc, "command": command,
                "start_ns": start, "end_ns": time.monotonic_ns(),
                "exit_code": process.returncode, "stdout": stdout, "stderr": stderr}
    with ThreadPoolExecutor(max_workers=len(jobs)) as pool:
        records = list(pool.map(collect, jobs))
    return {"records": records, "final_inventory": inventory(root)}


def timeout_control(root):
    root.mkdir(parents=True)
    command = [str(AENEAS), *BASE_FLAGS, "-dest", str(root), str(FIXTURE / "A.llbc")]
    start = time.monotonic_ns()
    process = subprocess.Popen(command, cwd=HERE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=0.000001)
    except subprocess.TimeoutExpired:
        timed_out = True
        process.kill()
        stdout, stderr = process.communicate(timeout=10)
    return {"command": command, "timed_out": timed_out, "exit_code": process.returncode,
            "stdout": stdout, "stderr": stderr, "elapsed_ns": time.monotonic_ns() - start,
            "inventory_after": inventory(root)}


def main():
    if ARTIFACTS.exists():
        shutil.rmtree(ARTIFACTS)
    ARTIFACTS.mkdir()
    oracle_a = call("oracle-A", "A.llbc", ARTIFACTS / "oracle-A")
    oracle_b = call("oracle-B", "B.llbc", ARTIFACTS / "oracle-B")
    assert oracle_a["exit_code"] == oracle_b["exit_code"] == 0
    oracles = {"A.llbc": oracle_a["inventory"], "B.llbc": oracle_b["inventory"]}

    groups = []
    for count, inputs in ((1, ["A.llbc"]), (2, ["A.llbc", "B.llbc"]),
                          (4, ["A.llbc", "B.llbc", "A.llbc", "B.llbc"])):
        group = concurrent_group(f"isolated-{count}", inputs, ARTIFACTS / f"isolated-{count}")
        assert all(r["exit_code"] == 0 and r["inventory"] == oracles[r["input"]] for r in group["records"])
        groups.append(group)

    namespace = call("namespace-option", "A.llbc", ARTIFACTS / "namespace-option",
                     [*BASE_FLAGS, "-namespace", "Alternate"])
    assert namespace["exit_code"] == 0 and namespace["inventory"] != oracle_a["inventory"]

    shared = different_input_shared(ARTIFACTS / "different-input-shared")
    assert all(r["exit_code"] == 0 for r in shared["records"])

    stale_dir = ARTIFACTS / "flag-change-shared"
    split = call("split-first", "A.llbc", stale_dir)
    unsplit = call("unsplit-second", "A.llbc", stale_dir,
                   ["-backend", "lean", "-no-progress-bar", "-sequential"])
    # A clean unsplit output provides the expected current-owned file set.
    unsplit_oracle = call("unsplit-clean-oracle", "A.llbc", ARTIFACTS / "unsplit-oracle",
                          ["-backend", "lean", "-no-progress-bar", "-sequential"])
    stale_files = sorted(set(unsplit["inventory"]) - set(unsplit_oracle["inventory"]))
    assert split["exit_code"] == unsplit["exit_code"] == unsplit_oracle["exit_code"] == 0

    failed_dir = ARTIFACTS / "failed-shared"
    previous = call("successful-before-error", "A.llbc", failed_dir)
    unsupported = call("unsupported-after-success", "unsupported.llbc", failed_dir)
    assert previous["exit_code"] == 0 and unsupported["exit_code"] != 0

    timeout = timeout_control(ARTIFACTS / "killed-timeout")
    assert timeout["timed_out"] and timeout["exit_code"] != 0

    result = {"environment": {"python": sys.version, "platform": platform.platform(),
                              "aeneas_sha256": sha(AENEAS), "script_sha256": sha(__file__),
                              "fixture_hashes": {p.name: sha(p) for p in FIXTURE.iterdir() if p.is_file()},
                              "aeneas_version": subprocess.run([str(AENEAS), "-version"],
                                  capture_output=True, text=True).stdout.strip()},
              "baseline_flags": BASE_FLAGS, "oracles": [oracle_a, oracle_b],
              "isolated_groups": groups, "namespace_option": namespace,
              "different_input_shared": shared,
              "flag_change_shared": {"split_first": split, "unsplit_second": unsplit,
                                     "unsplit_clean_oracle": unsplit_oracle,
                                     "stale_files_after_unsplit": stale_files},
              "failed_shared": {"previous": previous, "unsupported": unsupported,
                                "contains_sorry": "sorry" in (failed_dir / "Funs.lean").read_text()},
              "timeout_control": timeout}
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"isolated_jobs": [g["jobs"] for g in groups],
                      "isolated_matches_oracle": True,
                      "shared_final_funs": shared["final_inventory"].get("Funs.lean", {}).get("sha256"),
                      "stale_files_after_flag_change": stale_files,
                      "unsupported_exit": unsupported["exit_code"],
                      "timeout_killed": timeout["timed_out"]}, sort_keys=True))


if __name__ == "__main__":
    main()
