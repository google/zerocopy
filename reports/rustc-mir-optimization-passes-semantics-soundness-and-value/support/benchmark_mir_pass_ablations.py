#!/usr/bin/env python3
"""Reproducible MIR optimization pass ablation and inventory probe for Rust 1.99.1."""
import argparse
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

BENCH_SRC = """#![allow(dead_code)]
use std::hint::black_box;

#[derive(Clone, Copy)]
struct Pair { a: u64, b: u64 }

#[inline]
fn wrapper_add(x: u64, y: u64) -> u64 {
    let p = Pair { a: x, b: y };
    let r = &p;
    r.a.wrapping_add(r.b)
}

#[inline]
fn option_map_chain(v: Option<u64>) -> u64 {
    v.map(|x| x.wrapping_mul(3))
     .and_then(|x| if x > 10 { Some(x.wrapping_sub(5)) } else { Some(x + 1) })
     .unwrap_or(0)
}

fn sroa_and_destprop_heavy(n: u64) -> u64 {
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        let tmp = [i, i ^ 0x5555_5555, i.wrapping_mul(7), acc];
        let copy_tmp = tmp;
        let step = wrapper_add(copy_tmp[0], copy_tmp[1]) ^ option_map_chain(Some(copy_tmp[2]));
        acc = acc.wrapping_add(step);
        i += 1;
    }
    acc
}

fn main() {
    let n = black_box(2_000_000u64);
    let mut total = 0u64;
    for round in 0..5u64 {
        total ^= sroa_and_destprop_heavy(n.wrapping_add(round));
    }
    black_box(total);
}
"""


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"

    configs = [
        ("O0_mir0", ["-Copt-level=0", "-Zmir-opt-level=0"]),
        ("O0_mir1_default", ["-Copt-level=0", "-Zmir-opt-level=1"]),
        ("O0_mir2", ["-Copt-level=0", "-Zmir-opt-level=2"]),
        ("O2_mir0", ["-Copt-level=2", "-Zmir-opt-level=0"]),
        ("O2_mir1", ["-Copt-level=2", "-Zmir-opt-level=1"]),
        ("O2_mir2_default", ["-Copt-level=2", "-Zmir-opt-level=2"]),
        ("O2_mir3", ["-Copt-level=2", "-Zmir-opt-level=3"]),
        ("O2_mir4", ["-Copt-level=2", "-Zmir-opt-level=4"]),
        ("O2_no_Inline", ["-Copt-level=2", "-Zmir-enable-passes=-Inline"]),
        ("O2_no_GVN", ["-Copt-level=2", "-Zmir-enable-passes=-GVN"]),
        ("O2_no_SROA", ["-Copt-level=2", "-Zmir-enable-passes=-ScalarReplacementOfAggregates"]),
        ("O2_no_RefProp", ["-Copt-level=2", "-Zmir-enable-passes=-ReferencePropagation"]),
        ("O2_no_DataflowConstProp", ["-Copt-level=2", "-Zmir-enable-passes=-DataflowConstProp"]),
        ("O2_no_JumpThreading", ["-Copt-level=2", "-Zmir-enable-passes=-JumpThreading"]),
        ("O2_no_DestProp", ["-Copt-level=2", "-Zmir-enable-passes=-DestinationPropagation"]),
        ("O2_no_DSE", ["-Copt-level=2", "-Zmir-enable-passes=-DeadStoreElimination-initial,-DeadStoreElimination-final"]),
        ("O2_no_InstSimplify", ["-Copt-level=2", "-Zmir-enable-passes=-InstSimplify-before-inline,-InstSimplify-after-simplifycfg"]),
        ("O2_no_CopyProp", ["-Copt-level=2", "-Zmir-enable-passes=-CopyProp"]),
    ]

    results = []
    with tempfile.TemporaryDirectory() as td:
        wdir = Path(td)
        (wdir / "mir_opt_bench.rs").write_text(BENCH_SRC, encoding="utf-8")
        for label, flags in configs:
            out_bin = wdir / f"bench_{label}"
            out_ll = wdir / f"bench_{label}.ll"
            out_mir = wdir / f"bench_{label}.mir"
            t0 = time.perf_counter()
            subprocess.run(
                ["rustup", "run", args.toolchain, "rustc", "--edition=2024", "mir_opt_bench.rs", "-o", str(out_bin)] + flags,
                cwd=str(wdir),
                env=env,
                check=True,
            )
            compile_ms = (time.perf_counter() - t0) * 1000.0
            subprocess.run(
                ["rustup", "run", args.toolchain, "rustc", "--edition=2024", "--emit=llvm-ir", "mir_opt_bench.rs", "-o", str(out_ll)] + flags,
                cwd=str(wdir),
                env=env,
                check=True,
            )
            subprocess.run(
                ["rustup", "run", args.toolchain, "rustc", "--edition=2024", "--emit=mir", "mir_opt_bench.rs", "-o", str(out_mir)] + flags,
                cwd=str(wdir),
                env=env,
                check=True,
            )
            size_out = subprocess.check_output(["size", str(out_bin)], text=True).splitlines()[1].split()
            text_bytes = int(size_out[0])
            runs = []
            for _ in range(3):
                r0 = time.perf_counter()
                subprocess.run([str(out_bin)], cwd=str(wdir), env=env, check=True)
                runs.append((time.perf_counter() - r0) * 1000.0)
            runs.sort()
            results.append(
                {
                    "label": label,
                    "flags": flags,
                    "mir_lines": len(out_mir.read_text(encoding="utf-8").splitlines()),
                    "llvm_ir_lines": len(out_ll.read_text(encoding="utf-8").splitlines()),
                    "text_section_bytes": text_bytes,
                    "compile_time_ms": round(compile_ms, 2),
                    "runtime_median_ms": round(runs[1], 2),
                }
            )

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps({"toolchain": args.toolchain, "ablation_results": results}, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
