#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible runner for Lean 4 Stage 3 verification scaling benchmarks.

Executes `ReflectionVsSymExecBench.lean` via `anneal-lean-run --mode file
--concurrency 2` across `leanprover/lean4:v4.28.0-rc1` (`3b0f2862196c6a8...`),
`leanprover/lean4:v4.28.0` (`7e01a1bf5c70fc6...`), and
`leanprover/lean4:v4.34.1` (`5045d0056413266...`), plus boundary probes for
`K = 8, 10` (Architecture A exponential blowup) and `N = 200` (`ClosureLocals`
default `maxRecDepth` exhaustion), saving structured measurements to
`lean_scaling_results.json`.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from typing import Any

TOOLCHAINS = [
    "leanprover/lean4:v4.28.0-rc1",
    "leanprover/lean4:v4.28.0",
    "leanprover/lean4:v4.34.1",
]

METRIC_RE = re.compile(
    r"^METRIC AnnealBench\.([A-Za-z0-9_]+): dag_objs=(\d+) tree_nodes=(\d+)$"
)
PROFILE_LINE_RE = re.compile(
    r"^\s*(tactic execution|elaboration|type checking|attribute application|"
    r"process pre-definitions|share common exprs|instantiate metavars|simp)"
    r"(?: of [^\n]+)? took ([0-9.]+)(ms|s)$"
)
CUMULATIVE_LINE_RE = re.compile(r"^\t([a-z ()\-]+) ([0-9.]+)(ms|s)$")


def to_ms(val_str: str, unit: str) -> float:
    val = float(val_str)
    return val * 1000.0 if unit == "s" else val


def get_lean_version(toolchain: str) -> dict[str, str]:
    proc = subprocess.run(
        [
            "anneal-lean-run",
            "--mode",
            "file",
            "--concurrency",
            "2",
            "--",
            "elan",
            "run",
            toolchain,
            "lean",
            "--version",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    line = proc.stdout.strip().splitlines()[0]
    m_commit = re.search(r"commit ([0-9a-f]{40})", line)
    return {
        "toolchain": toolchain,
        "version_line": line,
        "commit": m_commit.group(1) if m_commit else "",
    }


def parse_bench_output(combined_output: str) -> dict[str, Any]:
    lines = combined_output.splitlines()
    theorems: dict[str, dict[str, Any]] = {}
    cumulative: dict[str, float] = {}

    # Skip preamble definitions before the first benchmark theorem (`archA_diamond1`).
    # We locate the `typeclass inference of MonadLiftT` / `doMatch` block from
    # `printProofMetrics` definition so the first theorem window starts cleanly.
    start_idx = 0
    for idx, line in enumerate(lines):
        if "doMatch" in line or "compilation (LCNF mono)" in line:
            start_idx = idx + 1
        if "METRIC AnnealBench." in line:
            break

    window_lines: list[str] = []
    in_cumulative = False

    for line in lines[start_idx:]:
        if line.strip() == "cumulative profiling times:":
            in_cumulative = True
            continue
        if in_cumulative:
            m_cum = CUMULATIVE_LINE_RE.match(line)
            if m_cum:
                cumulative[m_cum.group(1)] = round(
                    to_ms(m_cum.group(2), m_cum.group(3)), 3
                )
            continue

        m_metric = METRIC_RE.match(line.strip())
        if m_metric:
            thm_name = m_metric.group(1)
            dag_objs = int(m_metric.group(2))
            tree_nodes = int(m_metric.group(3))

            tactic_ms = 0.0
            elab_ms = 0.0
            typecheck_ms = 0.0
            attr_ms = 0.0
            predef_ms = 0.0
            share_ms = 0.0

            for wline in window_lines:
                if "MonadEvalT" in wline or "_eval._boxed" in wline:
                    continue
                m_prof = PROFILE_LINE_RE.match(wline)
                if m_prof:
                    cat = m_prof.group(1)
                    ms = to_ms(m_prof.group(2), m_prof.group(3))
                    if cat == "tactic execution":
                        tactic_ms += ms
                    elif cat == "elaboration":
                        elab_ms += ms
                    elif cat == "type checking":
                        typecheck_ms += ms
                    elif cat == "attribute application":
                        attr_ms += ms
                    elif cat == "process pre-definitions":
                        predef_ms += ms
                    elif cat == "share common exprs":
                        share_ms += ms

            total_ms = tactic_ms + elab_ms + typecheck_ms + predef_ms
            theorems[thm_name] = {
                "dag_objs": dag_objs,
                "tree_nodes": tree_nodes,
                "tactic_execution_ms": round(tactic_ms, 2),
                "elaboration_ms": round(elab_ms, 2),
                "type_checking_ms": round(typecheck_ms, 2),
                "attribute_application_ms": round(attr_ms, 2),
                "process_pre_definitions_ms": round(predef_ms, 2),
                "share_common_exprs_ms": round(share_ms, 2),
                "total_check_ms": round(total_ms, 2),
            }
            window_lines = []
        else:
            window_lines.append(line)

    return {
        "theorems": theorems,
        "cumulative_ms": cumulative,
    }


def run_boundary_probes(toolchain: str, bench_path: Path) -> dict[str, Any]:
    src = bench_path.read_text(encoding="utf-8")
    core_prefix = src.split("-- Architecture A instances")[0]

    probes: dict[str, Any] = {}

    with tempfile.TemporaryDirectory(prefix="anneal_lean_probe_") as tmpdir:
        tmp_dir = Path(tmpdir)

        # Probe 1: Architecture A at K = 8 (with raised heartbeats)
        k8_file = tmp_dir / "ArchAK8.lean"
        k8_file.write_text(
            core_prefix
            + "\nset_option maxHeartbeats 10000000\n"
            + "set_option maxRecDepth 200000\n"
            + "theorem archA_diamond8 : BodySafe diamondCfg8 defaultInitLocals := by intro oracle; step_arch_a\n"
            + "#eval printProofMetrics ``archA_diamond8\n"
            + "end AnnealBench\n",
            encoding="utf-8",
        )
        t0 = time.monotonic()
        p_k8 = subprocess.run(
            [
                "anneal-lean-run",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--",
                "elan",
                "run",
                toolchain,
                "lean",
                "-Dprofiler=true",
                "-Dprofiler.threshold=1",
                str(k8_file),
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        k8_wall_ms = (time.monotonic() - t0) * 1000.0
        k8_parsed = parse_bench_output(p_k8.stdout + "\n" + p_k8.stderr)
        k8_info = k8_parsed["theorems"]["archA_diamond8"]
        k8_info["wall_clock_ms"] = round(k8_wall_ms, 2)
        probes["archA_diamond8"] = k8_info

        # Probe 2: Architecture A at K = 8 and K = 10 under default maxHeartbeats (200,000)
        k10_default_file = tmp_dir / "ArchAK10Default.lean"
        k10_default_file.write_text(
            core_prefix
            + "\nset_option maxHeartbeats 200000\n"
            + "theorem archA_diamond8_default : BodySafe diamondCfg8 defaultInitLocals := by intro oracle; step_arch_a\n"
            + "theorem archA_diamond10_default : BodySafe diamondCfg10 defaultInitLocals := by intro oracle; step_arch_a\n"
            + "end AnnealBench\n",
            encoding="utf-8",
        )
        p_k10 = subprocess.run(
            [
                "anneal-lean-run",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--",
                "elan",
                "run",
                toolchain,
                "lean",
                str(k10_default_file),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        k10_out = p_k10.stdout + "\n" + p_k10.stderr
        probes["archA_default_heartbeats_k8_k10"] = {
            "exit_code": p_k10.returncode,
            "exceeded_max_heartbeats": (
                "deterministic timeout" in k10_out or "heartbeats" in k10_out
            ),
            "diagnostic_excerpt": re.sub(
                r"^/tmp/[^/]+/",
                "",
                next(
                    (
                        ln
                        for ln in k10_out.splitlines()
                        if "timeout" in ln or "heartbeats" in ln or "error:" in ln
                    ),
                    "",
                ),
            ),
        }

        # Probe 3: ClosureLocals at N = 200 under default maxRecDepth (512)
        closure_default_file = tmp_dir / "ClosureDefaultRecDepth.lean"
        closure_default_file.write_text(
            core_prefix
            + "\nset_option maxRecDepth 512\n"
            + "theorem env_closure_200_default : checkClosureEnv 200 = true := rfl\n"
            + "end AnnealBench\n",
            encoding="utf-8",
        )
        p_clos = subprocess.run(
            [
                "anneal-lean-run",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--",
                "elan",
                "run",
                toolchain,
                "lean",
                str(closure_default_file),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        clos_out = p_clos.stdout + "\n" + p_clos.stderr
        probes["env_closure_200_default_maxRecDepth"] = {
            "exit_code": p_clos.returncode,
            "exceeded_max_rec_depth": "maximum recursion depth has been reached"
            in clos_out,
            "diagnostic_excerpt": re.sub(
                r"^/tmp/[^/]+/",
                "",
                next(
                    (
                        ln
                        for ln in clos_out.splitlines()
                        if "maximum recursion depth" in ln
                    ),
                    "",
                ),
            ),
        }

    return probes


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    bench_path = support_dir / "ReflectionVsSymExecBench.lean"
    out_path = support_dir / "lean_scaling_results.json"

    results: dict[str, Any] = {
        "benchmark_file": bench_path.name,
        "toolchains": {},
    }

    for tc in TOOLCHAINS:
        meta = get_lean_version(tc)
        t0 = time.monotonic()
        proc = subprocess.run(
            [
                "anneal-lean-run",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--",
                "elan",
                "run",
                tc,
                "lean",
                "-Dprofiler=true",
                "-Dprofiler.threshold=1",
                str(bench_path),
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        wall_ms = (time.monotonic() - t0) * 1000.0
        parsed = parse_bench_output(proc.stdout + "\n" + proc.stderr)
        probes = run_boundary_probes(tc, bench_path)
        parsed["theorems"]["archA_diamond8"] = probes["archA_diamond8"]

        # Verify key scaling invariants
        thms = parsed["theorems"]
        assert thms["archA_diamond6"]["tree_nodes"] > 300000
        assert thms["archA_diamond8"]["tree_nodes"] > 1500000
        assert thms["archB_diamond10"]["tree_nodes"] < 50000
        assert thms["archC_diamond10"]["dag_objs"] == 30
        assert thms["archC_chain128"]["dag_objs"] == 30
        assert (
            thms["env_closure_200"]["type_checking_ms"]
            > 3.0 * thms["env_list_200"]["type_checking_ms"]
        )
        assert probes["archA_default_heartbeats_k8_k10"]["exceeded_max_heartbeats"]
        assert probes["env_closure_200_default_maxRecDepth"]["exceeded_max_rec_depth"]

        results["toolchains"][tc] = {
            "metadata": meta,
            "suite_wall_clock_ms": round(wall_ms, 2),
            "theorems": thms,
            "cumulative_ms": parsed["cumulative_ms"],
            "boundary_probes": probes,
        }

    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} across {len(TOOLCHAINS)} Lean 4 toolchains.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
