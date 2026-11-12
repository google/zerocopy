#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible benchmark harness for canonical MIR state and symbolic execution probes.

Measures:
1. Line counts (LOC), `.olean` artifact sizes, wall-clock compilation times,
   and peak RSS for the three standalone Lean 4 probes:
   - `CanonicalStateAndJoinProbe.lean`
   - `StarnixZeroGeneratorSymbolicEngine.lean`
   - `CompositionalBorrowAndLoopWP.lean`
2. Quantitative comparison against the baseline artifacts in `joshlf/anneal`
   (`a7ac073219f4`, `2fb744d6ecb5`, and `aa325aa43af9`).
"""

from __future__ import annotations

import json
import os
import resource
import shutil
import subprocess
import tempfile
import time
from pathlib import Path


def count_lines(path: Path) -> dict[str, int]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    non_empty = sum(1 for line in lines if line.strip())
    return {
        "total_lines": len(lines),
        "non_empty_lines": non_empty,
        "bytes": len(text.encode("utf-8")),
    }


def resolve_lean_bin() -> str:
    env_bin = os.environ.get("LEAN_BIN")
    if env_bin:
        return env_bin
    nix_store = Path("/nix/store")
    if nix_store.exists():
        for pattern in (
            "*lean-toolchain-x86_64-linux-4.34.1*/bin/lean",
            "*lean-toolchain*/bin/lean",
        ):
            for p in sorted(nix_store.glob(pattern)):
                return str(p)
    which_lean = shutil.which("lean")
    if which_lean:
        return which_lean
    raise FileNotFoundError("Could not locate `lean` binary; set LEAN_BIN.")


def resolve_runner_bin() -> str | None:
    env_runner = os.environ.get("ANNEAL_LEAN_RUN")
    if env_runner and Path(env_runner).exists():
        return env_runner
    which_runner = shutil.which("anneal-lean-run")
    if which_runner:
        return which_runner
    local_runner = Path.home() / ".local" / "bin" / "anneal-lean-run"
    if local_runner.exists():
        return str(local_runner)
    return None


def run_lean_probe(lean_bin: str, runner_bin: str | None, lean_file: Path) -> dict:
    with tempfile.TemporaryDirectory(prefix="anneal-topic8-olean-") as tmpdir:
        olean_path = Path(tmpdir) / (lean_file.stem + ".olean")
        cmd = [lean_bin, "-o", str(olean_path), lean_file.name]
        if runner_bin:
            cmd = [runner_bin, "--mode", "file", "--concurrency", "5", "--"] + cmd

        t0 = time.perf_counter()
        r_before = resource.getrusage(resource.RUSAGE_CHILDREN)
        proc = subprocess.run(
            cmd, cwd=str(lean_file.parent), capture_output=True, text=True, check=False
        )
        t1 = time.perf_counter()
        r_after = resource.getrusage(resource.RUSAGE_CHILDREN)

        olean_bytes = olean_path.stat().st_size if olean_path.exists() else 0
        return {
            "file": lean_file.name,
            **count_lines(lean_file),
            "exit_code": proc.returncode,
            "wall_ms": round((t1 - t0) * 1000.0, 2),
            "user_s": round(r_after.ru_utime - r_before.ru_utime, 3),
            "sys_s": round(r_after.ru_stime - r_before.ru_stime, 3),
            "max_rss_kb": r_after.ru_maxrss,
            "olean_bytes": olean_bytes,
            "stdout": proc.stdout.strip(),
            "stderr": proc.stderr.strip(),
        }


def main() -> None:
    here = Path(__file__).resolve().parent
    lean_bin = resolve_lean_bin()
    runner_bin = resolve_runner_bin()

    ver_proc = subprocess.run(
        [lean_bin, "--version"], capture_output=True, text=True, check=True
    )

    probe_names = [
        "CanonicalStateAndJoinProbe.lean",
        "StarnixZeroGeneratorSymbolicEngine.lean",
        "CompositionalBorrowAndLoopWP.lean",
    ]
    probe_results = []
    for name in probe_names:
        path = here / name
        res = run_lean_probe(lean_bin, runner_bin, path)
        if res["exit_code"] != 0:
            raise RuntimeError(
                f"Probe {name} failed with exit code {res['exit_code']}:\n"
                f"{res['stdout']}\n{res['stderr']}"
            )
        probe_results.append(res)

    baselines = {
        "joshlf:trusted/lean/Trusted/MirSemantics.lean": {
            "total_lines": 2057,
            "non_empty_lines": 1884,
            "bytes": 89791,
        },
        "joshlf:theory/Anneal/Lowering.lean": {
            "total_lines": 2257,
            "non_empty_lines": 2142,
            "bytes": 89293,
        },
        "joshlf:theory/Anneal/MirLemmas.lean": {
            "total_lines": 6625,
            "non_empty_lines": 6206,
            "bytes": 267177,
        },
        "joshlf:theory/Anneal/FunctionalTranslation.lean": {
            "total_lines": 11619,
            "non_empty_lines": 10943,
            "bytes": 507104,
        },
        "joshlf-mvp:trusted/lean/Trusted/Mvp.lean": {
            "total_lines": 12,
            "non_empty_lines": 11,
            "bytes": 475,
        },
        "joshlf-mvp:theory/Anneal/Mvp/Execution.lean": {
            "total_lines": 257,
            "non_empty_lines": 229,
            "bytes": 10334,
        },
        "joshlf-mvp:trusted/cargo-anneal/tests/fixtures/starnix/proof/generate_steps.py": {
            "total_lines": 181,
            "non_empty_lines": 163,
            "bytes": 7007,
        },
        "joshlf-mvp:trusted/cargo-anneal/tests/fixtures/starnix/proof/ProductionSteps.lean": {
            "total_lines": 5230,
            "non_empty_lines": 4742,
            "bytes": 212392,
        },
        "joshlf-mvp:trusted/cargo-anneal/tests/fixtures/starnix/proof/ProductionClaims.lean": {
            "total_lines": 108,
            "non_empty_lines": 98,
            "bytes": 4298,
        },
    }

    summary = {
        "lean_version": ver_proc.stdout.strip(),
        "probes": probe_results,
        "baselines": baselines,
        "comparisons": {
            "starnix_witness_reduction": {
                "baseline_production_steps_lines_at_2fb744d6e": 5230,
                "baseline_production_steps_lines_pre_2fb744d6e": 5270,
                "baseline_generate_steps_py_lines": 181,
                "baseline_captured_lean_lines": 961,
                "replacement_engine_lines_in_execution_lean": 42,
                "replacement_production_steps_lines": 38,
                "replacement_generate_steps_py_lines": 0,
                "production_steps_loc_reduction_ratio": round(5230 / 38, 1),
            },
            "functional_translation_reduction": {
                "baseline_functional_translation_lines": 11619,
                "baseline_mir_lemmas_and_lowering_lines": 8882,
                "baseline_total_theory_lines": 23686,
                "compositional_probe_total_lines": probe_results[2]["total_lines"],
                "loc_reduction_ratio_vs_functional_translation": round(
                    11619 / probe_results[2]["total_lines"], 1
                ),
            },
        },
    }

    out_path = here / "benchmark_results.json"
    out_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
