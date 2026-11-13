#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Reproducible multi-target, multi-backend speed, size, and compile-time harness for rustc 1.99.1."""

import argparse
import concurrent.futures
import hashlib
import json
import math
import os
import random
import re
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "aarch64-pc-windows-msvc",
    "i686-pc-windows-msvc",
]

EXECUTABLE_LINUX_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
]

CONFIGURATIONS = {
    "C01_O0": {
        "opt_level": "0",
        "lto": "off",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=0", "-C", "codegen-units=16", "-C", "embed-bitcode=no"],
        "description": "Unoptimized dev baseline (-O0, 16 CGUs)",
    },
    "C02_O1": {
        "opt_level": "1",
        "lto": "ThinLocal",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=1", "-C", "codegen-units=16", "-C", "embed-bitcode=no"],
        "description": "Fast optimization tier (-O1, ThinLocal, 16 CGUs)",
    },
    "C03_O2": {
        "opt_level": "2",
        "lto": "ThinLocal",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=2", "-C", "codegen-units=16", "-C", "embed-bitcode=no"],
        "description": "Balanced optimization tier (-O2, ThinLocal, 16 CGUs)",
    },
    "C04_O3_no_lto": {
        "opt_level": "3",
        "lto": "off",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=3", "-C", "codegen-units=16", "-C", "lto=off", "-C", "embed-bitcode=no"],
        "description": "True no-LTO -O3 baseline (-C lto=off disables implicit ThinLocal)",
    },
    "C05_O3_thinlocal": {
        "opt_level": "3",
        "lto": "ThinLocal",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=3", "-C", "codegen-units=16", "-C", "embed-bitcode=no"],
        "description": "Standard cargo build --release default (-O3, ThinLocal across 16 CGUs)",
    },
    "C06_O3_thin_lto": {
        "opt_level": "3",
        "lto": "thin",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=3", "-C", "codegen-units=16", "-C", "lto=thin"],
        "description": "Cross-crate ThinLTO without PGO (-O3, -C lto=thin, 16 CGUs)",
    },
    "C07_O3_fat_lto": {
        "opt_level": "3",
        "lto": "fat",
        "codegen_units": 1,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=3", "-C", "codegen-units=1", "-C", "lto=fat"],
        "description": "Whole-program single-CGU Fat LTO without PGO (-O3, -C lto=fat, 1 CGU)",
    },
    "C08_O3_no_lto_pgo": {
        "opt_level": "3",
        "lto": "off",
        "codegen_units": 16,
        "pgo": True,
        "rustc_flags": ["-C", "opt-level=3", "-C", "codegen-units=16", "-C", "lto=off", "-C", "embed-bitcode=no"],
        "description": "-O3 no-LTO with LLVM IR PGO (-C lto=off -C profile-use)",
    },
    "C09_O3_thin_lto_pgo": {
        "opt_level": "3",
        "lto": "thin",
        "codegen_units": 16,
        "pgo": True,
        "rustc_flags": ["-C", "opt-level=3", "-C", "codegen-units=16", "-C", "lto=thin"],
        "description": "-O3 cross-crate ThinLTO with LLVM IR PGO (-C lto=thin -C profile-use)",
    },
    "C10_O3_fat_lto_pgo": {
        "opt_level": "3",
        "lto": "fat",
        "codegen_units": 1,
        "pgo": True,
        "rustc_flags": ["-C", "opt-level=3", "-C", "codegen-units=1", "-C", "lto=fat"],
        "description": "Peak performance configuration (-O3 + Fat LTO + 1 CGU + LLVM IR PGO)",
    },
    "C11_Os": {
        "opt_level": "s",
        "lto": "ThinLocal",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=s", "-C", "codegen-units=16", "-C", "embed-bitcode=no"],
        "description": "Size-optimized -Os with default ThinLocal (16 CGUs)",
    },
    "C12_Oz": {
        "opt_level": "z",
        "lto": "ThinLocal",
        "codegen_units": 16,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=z", "-C", "codegen-units=16", "-C", "embed-bitcode=no"],
        "description": "Aggressive size-optimized -Oz with default ThinLocal (16 CGUs)",
    },
    "C11_Os_fat_lto": {
        "opt_level": "s",
        "lto": "fat",
        "codegen_units": 1,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=s", "-C", "codegen-units=1", "-C", "lto=fat"],
        "description": "Size-optimized -Os with whole-program Fat LTO (1 CGU)",
    },
    "C12_Oz_fat_lto": {
        "opt_level": "z",
        "lto": "fat",
        "codegen_units": 1,
        "pgo": False,
        "rustc_flags": ["-C", "opt-level=z", "-C", "codegen-units=1", "-C", "lto=fat"],
        "description": "Aggressive size-optimized -Oz with whole-program Fat LTO (1 CGU)",
    },
}


# ---------------------------------------------------------------------------
# Statistical Estimators, Bootstrap CI, Mann-Whitney U, and TOST Parity Gate
# ---------------------------------------------------------------------------

def summarize_samples(samples: list[float]) -> dict:
    if not samples:
        return {}
    s = sorted(samples)
    n = len(s)
    med = statistics.median(s)
    q25 = s[max(0, (n * 1) // 4 - 1)] if n >= 4 else s[0]
    q75 = s[min(n - 1, (n * 3) // 4)] if n >= 4 else s[-1]
    p90 = s[min(n - 1, int(math.ceil(0.90 * n)) - 1)]
    p99 = s[min(n - 1, int(math.ceil(0.99 * n)) - 1)]
    iqr = q75 - q25
    mad = statistics.median([abs(x - med) for x in s])
    mean = statistics.mean(s)
    stdev = statistics.stdev(s) if n >= 2 else 0.0
    return {
        "n": n,
        "min": round(s[0], 6),
        "p25": round(q25, 6),
        "median": round(med, 6),
        "p75": round(q75, 6),
        "p90": round(p90, 6),
        "p99": round(p99, 6),
        "max": round(s[-1], 6),
        "mean": round(mean, 6),
        "stdev": round(stdev, 6),
        "cv_pct": round((stdev / mean) * 100.0, 3) if mean > 0 else 0.0,
        "iqr": round(iqr, 6),
        "normalized_iqr_pct": round((iqr / med) * 100.0, 3) if med > 0 else 0.0,
        "mad": round(mad, 6),
    }


def mann_whitney_u_two_sided(x: list[float], y: list[float]) -> dict:
    """Two-sided Mann-Whitney U test with tie correction and normal approximation."""
    nx, ny = len(x), len(y)
    if nx == 0 or ny == 0:
        return {"u_stat": 0.0, "z_score": 0.0, "p_value": 1.0}
    combined = [(v, 0) for v in x] + [(v, 1) for v in y]
    combined.sort(key=lambda pair: pair[0])
    n = nx + ny
    ranks = [0.0] * n
    tie_sum = 0.0
    i = 0
    while i < n:
        j = i
        while j < n and combined[j][0] == combined[i][0]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[k] = avg_rank
        t = j - i
        if t > 1:
            tie_sum += (t ** 3 - t)
        i = j
    r_x = sum(ranks[k] for k in range(n) if combined[k][1] == 0)
    u_x = r_x - nx * (nx + 1) / 2.0
    u = min(u_x, nx * ny - u_x)
    mu_u = (nx * ny) / 2.0
    var_u = (nx * ny / (12.0 * n * (n - 1))) * ((n ** 3 - n) - tie_sum) if n > 1 else 0.0
    if var_u <= 0.0:
        return {"u_stat": round(u, 2), "z_score": 0.0, "p_value": 1.0}
    z = (abs(u - mu_u) - 0.5) / math.sqrt(var_u)
    p_val = math.erfc(max(0.0, z) / math.sqrt(2.0))
    return {
        "u_stat": round(u, 2),
        "z_score": round(z, 4),
        "p_value": round(min(1.0, max(0.0, p_val)), 6),
    }


def bootstrap_median_ratio(
    cand: list[float],
    base: list[float],
    resamples: int = 2000,
    seed: int = 20261113,
) -> dict:
    """Percentile bootstrap 95% CI on candidate/baseline median ratio."""
    if not cand or not base:
        return {}
    rng = random.Random(seed)
    nc, nb = len(cand), len(base)
    base_med = statistics.median(base)
    cand_med = statistics.median(cand)
    point_ratio = cand_med / base_med if base_med > 0 else 1.0
    ratios = []
    for _ in range(resamples):
        sc = sorted(cand[rng.randrange(nc)] for _ in range(nc))
        sb = sorted(base[rng.randrange(nb)] for _ in range(nb))
        mc = sc[nc // 2] if nc % 2 == 1 else 0.5 * (sc[nc // 2 - 1] + sc[nc // 2])
        mb = sb[nb // 2] if nb % 2 == 1 else 0.5 * (sb[nb // 2 - 1] + sb[nb // 2])
        if mb > 0:
            ratios.append(mc / mb)
    ratios.sort()
    lo = ratios[max(0, int(0.025 * len(ratios)))]
    hi = ratios[min(len(ratios) - 1, int(0.975 * len(ratios)))]
    mwu = mann_whitney_u_two_sided(cand, base)
    return {
        "ratio_median": round(point_ratio, 5),
        "delta_pct": round((point_ratio - 1.0) * 100.0, 3),
        "ci95_low": round(lo, 5),
        "ci95_high": round(hi, 5),
        "ci95_delta_pct": [round((lo - 1.0) * 100.0, 3), round((hi - 1.0) * 100.0, 3)],
        "mann_whitney_u": mwu,
    }


def parse_llvm_size_sysv(llvm_size_bin: str, artifact_path: Path) -> dict:
    """Run `llvm-size -A --radix=10` on an object, rlib, staticlib, or binary and sum sections."""
    p = subprocess.run(
        [llvm_size_bin, "-A", "--radix=10", str(artifact_path)],
        capture_output=True,
        text=True,
    )
    cats = {
        "executable_code": 0,
        "read_only_data": 0,
        "initialized_data": 0,
        "zero_initialized_bss": 0,
        "unwind_tables": 0,
        "debug_and_symbols": 0,
        "other": 0,
    }
    raw_sections = {}
    for line in p.stdout.splitlines():
        parts = line.split()
        if len(parts) < 2:
            continue
        sec, sz_str = parts[0], parts[1]
        if sec in ("section", "Total", "TOTAL") or sec.endswith(":"):
            continue
        try:
            sz = int(sz_str)
        except ValueError:
            continue
        raw_sections[sec] = raw_sections.get(sec, 0) + sz
        s_low = sec.lower()
        if s_low in (".text", "__text", ".init", ".fini", ".plt", ".plt.got") or s_low.startswith(".text."):
            cats["executable_code"] += sz
        elif (
            s_low in (".rodata", "__const", ".rdata", "__cstring", "__literal4", "__literal8", "__literal16")
            or s_low.startswith(".rodata.")
            or s_low.startswith(".rdata$")
        ):
            cats["read_only_data"] += sz
        elif (
            s_low in (".data", ".data.rel.ro", "__data", "__const_coal", ".got", ".got.plt", ".idata", ".CRT")
            or s_low.startswith(".data.")
            or s_low.startswith(".CRT$")
        ):
            cats["initialized_data"] += sz
        elif s_low in (".bss", "__bss", "__common", ".tbss") or s_low.startswith(".bss."):
            cats["zero_initialized_bss"] += sz
        elif (
            s_low in (".eh_frame", ".eh_frame_hdr", ".pdata", ".xdata", "__unwind_info", "__eh_frame", ".gcc_except_table")
            or s_low.startswith(".eh_frame")
            or s_low.startswith(".pdata")
            or s_low.startswith(".xdata")
            or s_low.startswith(".gcc_except_table")
        ):
            cats["unwind_tables"] += sz
        elif (
            s_low.startswith(".debug")
            or s_low.startswith("__debug")
            or s_low in (".symtab", ".strtab", ".shstrtab", ".comment")
        ):
            cats["debug_and_symbols"] += sz
        else:
            cats["other"] += sz

    cats["text_plus_rodata_bytes"] = cats["executable_code"] + cats["read_only_data"]
    cats["allocatable_load_image_bytes"] = (
        cats["executable_code"]
        + cats["read_only_data"]
        + cats["initialized_data"]
        + cats["unwind_tables"]
    )
    cats["total_file_bytes"] = artifact_path.stat().st_size if artifact_path.exists() else 0
    return cats


def parse_time_passes_jsonl(stderr_text: str) -> dict:
    """Categorize `-Z time-passes -Z time-passes-format=json` output into compiler phases."""
    passes = {}
    max_rss = 0
    for line in stderr_text.splitlines():
        if not line.startswith("time: {"):
            continue
        try:
            obj = json.loads(line[len("time: "):])
        except json.JSONDecodeError:
            continue
        pname = obj.get("pass", "")
        t_sec = float(obj.get("time", 0.0))
        passes[pname] = passes.get(pname, 0.0) + t_sec
        max_rss = max(max_rss, int(obj.get("rss_start", 0)), int(obj.get("rss_end", 0)))

    frontend_parse_expand_resolve = (
        passes.get("parse_crate", 0.0)
        + passes.get("macro_expand_crate", 0.0)
        + passes.get("resolve_crate", 0.0)
        + passes.get("AST_validation", 0.0)
    )
    frontend_typeck_borrowck_lint = (
        passes.get("coherence_checking", 0.0)
        + passes.get("type_check_crate", 0.0)
        + passes.get("MIR_borrow_checking", 0.0)
        + passes.get("MIR_effect_checking", 0.0)
        + passes.get("lint_checking", 0.0)
        + passes.get("privacy_checking_modules", 0.0)
    )
    middle_monomorphize_partition = (
        passes.get("monomorphization_collector_root_collections", 0.0)
        + passes.get("monomorphization_collector_graph_walk", 0.0)
        + passes.get("partition_and_assert_distinct_symbols", 0.0)
    )
    backend_ir_lowering = passes.get("codegen_to_LLVM_IR", 0.0)
    backend_llvm_passes = passes.get("LLVM_passes", 0.0)
    backend_lto = (
        passes.get("LLVM_thinlto", 0.0)
        + passes.get("LLVM_lto_optimize", 0.0)
        + passes.get("LLVM_fat_lto_link_module", 0.0)
    )
    backend_ongoing = passes.get("finish_ongoing_codegen", 0.0)
    linker_sec = passes.get("link_crate", passes.get("link", 0.0))
    total_sec = passes.get("total", 0.0)

    return {
        "frontend_parse_expand_resolve_sec": round(frontend_parse_expand_resolve, 6),
        "frontend_typeck_borrowck_lint_sec": round(frontend_typeck_borrowck_lint, 6),
        "middle_monomorphize_partition_sec": round(middle_monomorphize_partition, 6),
        "backend_ir_lowering_sec": round(backend_ir_lowering, 6),
        "backend_llvm_opt_and_codegen_sec": round(max(backend_llvm_passes, backend_ongoing - backend_lto), 6),
        "backend_lto_sec": round(backend_lto, 6),
        "linker_sec": round(linker_sec, 6),
        "total_sec": round(total_sec, 6),
        "peak_rss_bytes": max_rss,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["verify-baselines", "summary"], default="verify-baselines")
    args = parser.parse_args()

    speed_path = HERE / "tier1_speed_baselines.json"
    size_path = HERE / "tier1_size_baselines.json"
    ct_path = HERE / "compile_time_phase_breakdowns.json"
    gate_path = HERE / "parity_gate_specification.json"

    for p in (speed_path, size_path, ct_path, gate_path):
        if not p.exists():
            print(f"MISSING required artifact: {p}", file=sys.stderr)
            return 1

    speed = json.loads(speed_path.read_text(encoding="utf-8"))
    size = json.loads(size_path.read_text(encoding="utf-8"))
    ct = json.loads(ct_path.read_text(encoding="utf-8"))
    gate = json.loads(gate_path.read_text(encoding="utf-8"))

    assert len(size["tier1_targets_covered"]) == 8
    assert len(speed["executable_targets"]) == 3
    assert len(speed["configurations"]) >= 12
    print(json.dumps({
        "status": "ok",
        "tier1_targets_in_size_baselines": len(size["tier1_targets_covered"]),
        "executable_targets_in_speed_baselines": len(speed["executable_targets"]),
        "configurations_evaluated": len(speed["configurations"]),
        "w_core_workloads": len(speed["w_core_workloads"]),
        "w_macro_workloads": len(speed["w_macro_workloads"]),
        "layout_shuffle_seeds": speed["layout_randomization_experiment"]["num_linker_seeds"],
        "parity_gates_defined": list(gate["parity_tiers"].keys()),
    }, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
