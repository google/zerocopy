#!/usr/bin/env python3
import json
import os
import re
import subprocess
import time
from pathlib import Path

SCRATCH = Path("<scratch>/mvp-investigations/task3")
MVP_ROOT = Path("<workspace>/anneal/.agent-worktrees/joshlf-mvp")
TOOLCHAIN_ROOT = Path("<host-home>/.cache/anneal/toolchain/e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a")
LEAN_BIN = TOOLCHAIN_ROOT / "lean/bin/lean"

def parse_time_v(stderr: str) -> dict:
    user_m = re.search(r"User time \(seconds\):\s*([0-9.]+)", stderr)
    sys_m = re.search(r"System time \(seconds\):\s*([0-9.]+)", stderr)
    rss_m = re.search(r"Maximum resident set size \(kbytes\):\s*([0-9]+)", stderr)
    return {
        "user_s": float(user_m.group(1)) if user_m else 0.0,
        "sys_s": float(sys_m.group(1)) if sys_m else 0.0,
        "max_rss_kb": int(rss_m.group(1)) if rss_m else 0,
    }

def main():
    work = SCRATCH / "profile_stage"
    ps_text = (MVP_ROOT / "trusted/cargo-anneal/tests/fixtures/starnix/proof/ProductionSteps.lean").read_text()

    # Count states per path in ProductionSteps.lean
    paths = ["le8", "le16", "le32", "le64", "be8", "be16", "be32", "be64"]
    path_counts = {}
    for p in paths:
        states = re.findall(rf"private def {p}_state(\d+)\b", ps_text)
        suffixes = re.findall(rf"private theorem {p}_suffix(\d+)\b", ps_text)
        path_counts[p] = {
            "states": len(states),
            "max_state_idx": max(int(x) for x in states),
            "suffixes": len(suffixes),
        }
    print("Path counts in ProductionSteps.lean:", json.dumps(path_counts, indent=2))

    # Build a setup.json that imports InitialCache (same imports as ProductionSteps)
    ps_setup = json.loads((work / "ProductionSteps.setup.json").read_text())
    clean_env = {
        "HOME": os.environ.get("HOME", "/root"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
        "PATH": f"{os.path.expanduser('~/.local/bin')}:/usr/bin:/bin",
    }

    # Test 1: Whole-execution reduction via `run_initial_success` (`run sourceBody fuel (initial ...) = some ... := by rfl`)
    # for each of the 8 paths individually!
    whole_exec_specs = [
        ("le64", 9, "[0, 3, value]", "value"),
        ("le8", 12, "[0, 0, value]", "(value &&& 255)"),
        ("le16", 12, "[0, 1, value]", "(value &&& 65535)"),
        ("le32", 12, "[0, 2, value]", "(value &&& 4294967295)"),
        ("be8", 12, "[1, 0, value]", "(value &&& 255)"),
        ("be16", 33, "[1, 1, value]", "(swap16 value)"),
        ("be32", 57, "[1, 2, value]", "(swap32 value)"),
        ("be64", 99, "[1, 3, value]", "(swap64 value)"),
    ]

    whole_results = []
    for name, fuel, args_str, res_str in whole_exec_specs:
        src = f"""prelude
import InitialCache

namespace BenchWhole

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

theorem {name}_whole (value : Word) :
    Safe sourceBody {args_str} ∧
      Returns sourceBody {args_str} {res_str} :=
  run_initial_success (body := sourceBody) (fuel := {fuel})
    (args := {args_str}) (value := {res_str}) rfl

end BenchWhole
"""
        lean_file = work / f"BenchWhole_{name}.lean"
        olean_file = work / f"BenchWhole_{name}.olean"
        setup_file = work / f"BenchWhole_{name}.setup.json"
        s_obj = dict(ps_setup)
        s_obj["name"] = f"BenchWhole_{name}"
        setup_file.write_text(json.dumps(s_obj))
        lean_file.write_text(src)

        cmd = [
            "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
            "/usr/bin/time", "-v",
            str(LEAN_BIN), "-j1", "-M2048", "-t0",
            "-DElab.async=false", "-Ddebug.skipKernelTC=false",
            "--setup", str(setup_file),
            "-o", str(olean_file),
            str(lean_file),
        ]
        t0 = time.perf_counter()
        try:
            proc = subprocess.run(cmd, cwd=work, env=clean_env, capture_output=True, text=True, timeout=45)
            wall_ms = (time.perf_counter() - t0) * 1000.0
            stats = parse_time_v(proc.stderr)
            row = {
                "path": name,
                "fuel": fuel,
                "returncode": proc.returncode,
                "wall_ms": wall_ms,
                "user_s": stats["user_s"],
                "max_rss_kb": stats["max_rss_kb"],
                "olean_bytes": olean_file.stat().st_size if olean_file.exists() else 0,
                "stdout": proc.stdout.strip()[:400],
            }
        except subprocess.TimeoutExpired:
            row = {
                "path": name,
                "fuel": fuel,
                "returncode": -1,
                "wall_ms": 45000.0,
                "timeout": True,
            }
        whole_results.append(row)
        print(f"Whole-exec from initial {name:6s} (fuel={fuel:2d}): rc={row['returncode']} wall={row['wall_ms']:.1f} ms rss={row.get('max_rss_kb',0)/1024:.1f} MiB | err={row.get('stdout','')[:120]}")

    # Test 2: What if we normalize `initial sourceBody args = state0 value` FIRST by `rfl`,
    # and then run `run_success (body := sourceBody) (fuel := fuel) (start := state0 value) (value := res) rfl`?
    state0_results = []
    for name, fuel, args_str, res_str in whole_exec_specs:
        # Extract <name>_state0 from ProductionSteps.lean
        m0 = re.search(rf"(private def {name}_state0 \(value : Word\) : State :=\n(?:  .*\n)+)", ps_text)
        state0_def = m0.group(1)
        src = f"""prelude
import InitialCache

namespace BenchState0

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

{state0_def}
theorem {name}_from_state0 (value : Word) :
    Safe sourceBody {args_str} ∧
      Returns sourceBody {args_str} {res_str} := by
  have start : initial sourceBody {args_str} = {name}_state0 value := by rfl
  have exec : Executes sourceBody ({name}_state0 value) {res_str} :=
    run_executes (body := sourceBody) (fuel := {fuel})
      (start := {name}_state0 value) (value := {res_str}) rfl
  have exec0 : Executes sourceBody (initial sourceBody {args_str}) {res_str} := by
    rw [start]
    exact exec
  exact ⟨executes_safe exec0, executes_returns exec0⟩

end BenchState0
"""
        lean_file = work / f"BenchState0_{name}.lean"
        olean_file = work / f"BenchState0_{name}.olean"
        setup_file = work / f"BenchState0_{name}.setup.json"
        s_obj = dict(ps_setup)
        s_obj["name"] = f"BenchState0_{name}"
        setup_file.write_text(json.dumps(s_obj))
        lean_file.write_text(src)

        cmd = [
            "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
            "/usr/bin/time", "-v",
            str(LEAN_BIN), "-j1", "-M2048", "-t0",
            "-DElab.async=false", "-Ddebug.skipKernelTC=false",
            "--setup", str(setup_file),
            "-o", str(olean_file),
            str(lean_file),
        ]
        t0 = time.perf_counter()
        try:
            proc = subprocess.run(cmd, cwd=work, env=clean_env, capture_output=True, text=True, timeout=45)
            wall_ms = (time.perf_counter() - t0) * 1000.0
            stats = parse_time_v(proc.stderr)
            row = {
                "path": name,
                "fuel": fuel,
                "returncode": proc.returncode,
                "wall_ms": wall_ms,
                "user_s": stats["user_s"],
                "max_rss_kb": stats["max_rss_kb"],
                "olean_bytes": olean_file.stat().st_size if olean_file.exists() else 0,
                "stdout": proc.stdout.strip()[:400],
            }
        except subprocess.TimeoutExpired:
            row = {
                "path": name,
                "fuel": fuel,
                "returncode": -1,
                "wall_ms": 45000.0,
                "timeout": True,
            }
        state0_results.append(row)
        print(f"Whole-exec from state0  {name:6s} (fuel={fuel:2d}): rc={row['returncode']} wall={row['wall_ms']:.1f} ms rss={row.get('max_rss_kb',0)/1024:.1f} MiB | err={row.get('stdout','')[:120]}")

    out = {
        "path_counts": path_counts,
        "per_path_whole_exec_from_initial": whole_results,
        "per_path_whole_exec_from_state0": state0_results,
    }
    (SCRATCH / "whole_exec_vs_witness_bench.json").write_text(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
