#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical differential ablation of rustc_mir_transform vs. LLVM opt -O2.

Compares four configurations across five representative Rust patterns:
  - C0: rustc -Zmir-opt-level=0 (unoptimized LLVM IR emitted from PostCleanup MIR)
  - C1: rustc -Zmir-opt-level=0 + standalone LLVM `opt -passes='default<O2>'`
  - C2: rustc -Zmir-opt-level=0 -Zmir-enable-passes=+DestinationPropagation,+CopyProp,+ScalarReplacementOfAggregates,+Inline + standalone LLVM `opt -passes='default<O2>'`
  - C3: rustc -Zmir-opt-level=2 + standalone LLVM `opt -passes='default<O2>'`

We pass `-Copt-level=2 -Cno-prepopulate-passes -Cpanic=abort` to `rustc` so that:
  1. Functions do not carry the `optnone` attribute (allowing `opt -O2` to run),
  2. `rustc` itself does not run LLVM optimization passes during emission
     (`-Cno-prepopulate-passes`), isolating `rustc_mir_transform` in C0 and
     delegating LLVM IR optimization exclusively to `/usr/bin/opt`.
"""

import json
import os
import re
import subprocess
from pathlib import Path

SCRATCH_DIR = Path(__file__).resolve().parent
RUSTC = "/home/user/.cargo/bin/rustc"
OPT = "/usr/bin/opt"
SRC = SCRATCH_DIR / "bench_patterns.rs"

FUNCTIONS = [
    "pattern1_large_aggregate_builder",
    "pattern2_option_adapter_chain",
    "pattern3_enum_state_machine",
    "pattern4_scalar_cse_loop",
    "pattern5_drop_elaboration",
]

CONFIGS = {
    "C0": {
        "desc": "rustc -Zmir-opt-level=0 (no LLVM opt)",
        "rustc_flags": ["-Zmir-opt-level=0"],
        "run_opt": False,
    },
    "C2_raw": {
        "desc": "rustc -Zmir-opt-level=0 + {DestProp,CopyProp,MirSROA,Inline} (no LLVM opt)",
        "rustc_flags": [
            "-Zmir-opt-level=0",
            "-Zmir-enable-passes=+DestinationPropagation,+CopyProp,+ScalarReplacementOfAggregates,+Inline",
        ],
        "run_opt": False,
    },
    "C3_raw": {
        "desc": "rustc -Zmir-opt-level=2 (no LLVM opt)",
        "rustc_flags": ["-Zmir-opt-level=2"],
        "run_opt": False,
    },
    "C1": {
        "desc": "rustc -Zmir-opt-level=0 + opt -O2",
        "rustc_flags": ["-Zmir-opt-level=0"],
        "run_opt": True,
    },
    "C2": {
        "desc": "rustc -Zmir-opt-level=0 + {DestProp,CopyProp,MirSROA,Inline} + opt -O2",
        "rustc_flags": [
            "-Zmir-opt-level=0",
            "-Zmir-enable-passes=+DestinationPropagation,+CopyProp,+ScalarReplacementOfAggregates,+Inline",
        ],
        "run_opt": True,
    },
    "C3": {
        "desc": "rustc -Zmir-opt-level=2 + opt -O2",
        "rustc_flags": ["-Zmir-opt-level=2"],
        "run_opt": True,
    },
}


def parse_llvm_ir(ir_text: str):
    """Extract per-function and module-wide metrics from textual LLVM IR."""
    funcs = {}
    current_fn = None
    body_lines = []

    define_re = re.compile(r"^define\b.*@([A-Za-z0-9_$]+)\s*\(")
    for line in ir_text.splitlines():
        if current_fn is None:
            m = define_re.match(line)
            if m:
                current_fn = m.group(1)
                body_lines = []
        else:
            if line.startswith("}"):
                funcs[current_fn] = analyze_fn_body(body_lines)
                current_fn = None
            else:
                body_lines.append(line)

    return funcs


def analyze_fn_body(lines):
    inst_count = 0
    alloca_count = 0
    memcpy_count = 0
    bb_count = 0
    load_count = 0
    store_count = 0

    for raw in lines:
        s = raw.strip()
        if not s or s.startswith(";"):
            continue
        # Basic block label
        if re.match(r"^[A-Za-z0-9_$.-]+:\s*(;.*)?$", s):
            bb_count += 1
            continue
        # Continuation lines of switch [...]
        if s.startswith("i") and "label %" in s and not ("=" in s or s.startswith("invoke") or s.startswith("call")):
            continue
        if s == "]":
            continue
        inst_count += 1
        if re.search(r"\balloca\b", s):
            alloca_count += 1
        if "llvm.memcpy" in s:
            memcpy_count += 1
        if re.match(r"^(%[^\s=]+\s*=\s*)?load\b", s):
            load_count += 1
        if re.match(r"^store\b", s):
            store_count += 1

    if bb_count == 0 and inst_count > 0:
        bb_count = 1

    return {
        "insts": inst_count,
        "allocas": alloca_count,
        "memcpys": memcpy_count,
        "bbs": bb_count,
        "loads": load_count,
        "stores": store_count,
    }


def main():
    results = {}
    for cid, cfg in CONFIGS.items():
        raw_ll = SCRATCH_DIR / f"bench_{cid}_raw.ll"
        final_ll = SCRATCH_DIR / f"bench_{cid}.ll"
        cmd = [
            RUSTC,
            "--edition=2021",
            "-Copt-level=2",
            "-Cno-prepopulate-passes",
            "-Cpanic=abort",
            "--emit=llvm-ir",
            *cfg["rustc_flags"],
            "-o",
            str(raw_ll),
            str(SRC),
        ]
        subprocess.run(cmd, check=True)
        if cfg["run_opt"]:
            # Adapt LLVM 23 1-arg @llvm.lifetime.{start,end}.p0(ptr) to
            # LLVM 21 (/usr/bin/opt) 2-arg @llvm.lifetime.{start,end}.p0(i64, ptr).
            ir_in = raw_ll.read_text()
            ir_in = re.sub(
                r"call void @llvm\.lifetime\.(start|end)\.p0\(ptr\b",
                r"call void @llvm.lifetime.\1.p0(i64 -1, ptr",
                ir_in,
            )
            ir_in = re.sub(
                r"declare void @llvm\.lifetime\.(start|end)\.p0\(ptr captures\(none\)\)",
                r"declare void @llvm.lifetime.\1.p0(i64 immarg, ptr nocapture)",
                ir_in,
            )
            adapted_ll = SCRATCH_DIR / f"bench_{cid}_adapted.ll"
            adapted_ll.write_text(ir_in)
            opt_cmd = [
                OPT,
                "-passes=default<O2>",
                "-S",
                str(adapted_ll),
                "-o",
                str(final_ll),
            ]
            subprocess.run(opt_cmd, check=True)
        else:
            final_ll.write_text(raw_ll.read_text())

        ir_text = final_ll.read_text()
        parsed = parse_llvm_ir(ir_text)
        module_totals = {
            "num_funcs": len(parsed),
            "insts": sum(v["insts"] for v in parsed.values()),
            "allocas": sum(v["allocas"] for v in parsed.values()),
            "memcpys": sum(v["memcpys"] for v in parsed.values()),
            "bbs": sum(v["bbs"] for v in parsed.values()),
            "loads": sum(v["loads"] for v in parsed.values()),
            "stores": sum(v["stores"] for v in parsed.values()),
        }
        results[cid] = {
            "functions": {fn: parsed.get(fn, {}) for fn in FUNCTIONS},
            "module_totals": module_totals,
        }

    out_json = SCRATCH_DIR / "ablation_results.json"
    out_json.write_text(json.dumps(results, indent=2))

    # Print summary table
    order = ["C0", "C2_raw", "C3_raw", "C1", "C2", "C3"]
    print("=== Empirical Ablation Results (Per-Function) ===")
    for fn in FUNCTIONS:
        print(f"\nFunction: {fn}")
        print(f"{'Config':<8} {'Insts':>8} {'Allocas':>8} {'Memcpys':>8} {'BBs':>6} {'Loads':>8} {'Stores':>8}")
        for cid in order:
            m = results[cid]["functions"][fn]
            print(
                f"{cid:<8} {m.get('insts', 0):>8} {m.get('allocas', 0):>8} "
                f"{m.get('memcpys', 0):>8} {m.get('bbs', 0):>6} "
                f"{m.get('loads', 0):>8} {m.get('stores', 0):>8}"
            )

    print("\n=== Whole-Module Totals (Including Monomorphized Helpers/Closures) ===")
    print(f"{'Config':<8} {'Funcs':>6} {'Insts':>8} {'Allocas':>8} {'Memcpys':>8} {'BBs':>6} {'Loads':>8} {'Stores':>8}")
    for cid in order:
        t = results[cid]["module_totals"]
        print(
            f"{cid:<8} {t['num_funcs']:>6} {t['insts']:>8} {t['allocas']:>8} "
            f"{t['memcpys']:>8} {t['bbs']:>6} {t['loads']:>8} {t['stores']:>8}"
        )


if __name__ == "__main__":
    main()
