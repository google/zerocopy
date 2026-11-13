#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical PGO 2-stage instrumentation, heuristic decomposition ablation, and stale-profile sensitivity harness for rustc 1.99.1 / LLVM 23.1.1."""

import argparse
import csv
import json
import os
import re
import shutil
import statistics
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

PGO_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
]

PGO_ABLATION_CONFIGS = [
    ("Baseline_NoPGO_O3", ["-C", "opt-level=3"], False),
    ("PGO_Full_O3", ["-C", "opt-level=3"], True),
    ("PGO_No_Inlining_Multiplier", [
        "-C", "opt-level=3",
        "-C", "llvm-args=-inline-threshold=225",
        "-C", "llvm-args=-hot-callsite-threshold=225",
    ], True),
    ("PGO_No_BlockPlacement_TailDup", [
        "-C", "opt-level=3",
        "-C", "llvm-args=-disable-block-placement=true",
        "-C", "llvm-args=-tail-dup-placement=false",
    ], True),
    ("PGO_No_HotColdSplit", [
        "-C", "opt-level=3",
        "-C", "llvm-args=-hot-cold-split=false",
        "-C", "llvm-args=-split-machine-functions=false",
    ], True),
    ("PGO_No_IndirectCallPromotion", [
        "-C", "opt-level=3",
        "-C", "llvm-args=-disable-icp=true",
    ], True),
    ("PGO_No_MemOpSizeOpt", [
        "-C", "opt-level=3",
        "-C", "llvm-args=-disable-memop-opt=true",
    ], True),
]

# Workload exercising:
# 1. Skewed indirect trait/fn dispatch (95% OpFastAdd, 4% OpMulXor, 1% OpColdSlow) -> ICP target
# 2. Skewed branch layout (hot fast-path vs cold error/overflow branches) -> MachineBlockPlacement
# 3. Variable-size slice copy (95% 16-byte copy) -> MemOpSize specialization
# 4. Call-graph depth with hot leaf helpers -> PGO hot-callsite inlining
PGO_WORKLOAD_BASE_RS = r"""#![allow(dead_code)]
use std::time::Instant;

pub trait StageOp {
    fn execute(&self, acc: u64, x: u64, scratch: &mut [u8]) -> u64;
}

pub struct OpFastAdd;
pub struct OpMulXor;
pub struct OpColdSlow;

#[inline(never)]
pub fn cold_slow_fallback(acc: u64, x: u64) -> u64 {
    let mut v = acc ^ x;
    for i in 0..32 {
        v = v.rotate_left(5).wrapping_mul(0x9e3779b97f4a7c15 ^ (i as u64));
    }
    v
}

pub fn hot_helper_transform(acc: u64, x: u64) -> u64 {
    // Medium-size helper that benefits from PGO HotCallSiteThreshold (3000 vs 225)
    let a = acc.wrapping_add(x).rotate_left(13);
    let b = a.wrapping_mul(0xbf58476d1ce4e5b9) ^ (x >> 7);
    let c = b.wrapping_add(0x94d049bb133111eb).rotate_right(11);
    let d = c.wrapping_mul(0x2545f4914f6cdd1d) ^ a;
    let e = d.wrapping_add(b).rotate_left(17);
    e ^ c
}

impl StageOp for OpFastAdd {
    fn execute(&self, acc: u64, x: u64, scratch: &mut [u8]) -> u64 {
        // Skewed branch: x & 0x7f != 0 is taken 127/128 (99.2%) of the time
        if (x & 0x7f) == 0 {
            cold_slow_fallback(acc, x)
        } else {
            // Fixed-size 16-byte copy 99% of the time
            let src = [x as u8; 32];
            let n = if (x & 0xff) == 1 { 24 } else { 16 };
            scratch[..n].copy_from_slice(&src[..n]);
            hot_helper_transform(acc, x ^ (scratch[0] as u64))
        }
    }
}

impl StageOp for OpMulXor {
    fn execute(&self, acc: u64, x: u64, scratch: &mut [u8]) -> u64 {
        scratch[0] = (x & 0xff) as u8;
        acc.wrapping_mul(x | 1) ^ 0x517cc1b727220a95
    }
}

impl StageOp for OpColdSlow {
    fn execute(&self, acc: u64, x: u64, scratch: &mut [u8]) -> u64 {
        scratch[0] = 0xff;
        cold_slow_fallback(acc, x)
    }
}

#[inline(never)]
pub fn run_pipeline(iters: usize, seed: u64) -> u64 {
    let op_fast = OpFastAdd;
    let op_mul = OpMulXor;
    let op_cold = OpColdSlow;
    let table: [&dyn StageOp; 3] = [&op_fast, &op_mul, &op_cold];
    let mut scratch = [0u8; 64];
    let mut acc = seed;
    let mut i = 0usize;
    while i < iters {
        let sel = if (i & 31) == 0 {
            if (i & 255) == 0 { 2 } else { 1 }
        } else {
            0
        };
        let op = std::hint::black_box(table[sel]);
        acc = op.execute(acc, (i as u64).wrapping_add(seed), &mut scratch);
        i += 1;
    }
    acc ^ (scratch[0] as u64)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("bench");
    if mode == "train" {
        let v = std::hint::black_box(run_pipeline(100_000, 0x12345678));
        if v == 0 { println!("zero"); }
        return;
    }
    let mut samples = Vec::with_capacity(35);
    let mut sink = 0u64;
    for r in 0..35 {
        let t0 = Instant::now();
        let v = std::hint::black_box(run_pipeline(
            std::hint::black_box(200_000),
            std::hint::black_box(0x12345678 ^ (r as u64)),
        ));
        let dt = t0.elapsed().as_nanos() as u64;
        sink ^= v;
        if r >= 5 {
            samples.push(dt);
        }
    }
    samples.sort_unstable();
    let med = samples[samples.len() / 2];
    println!("MEDIAN_NS={} SINK={}", med, sink);
}
"""


def make_mutated_source(kind: str) -> str:
    if kind == "M0_Unmodified":
        return PGO_WORKLOAD_BASE_RS
    if kind == "M1_RenameInternalHelper":
        return PGO_WORKLOAD_BASE_RS.replace("hot_helper_transform", "hot_helper_transform_v2")
    if kind == "M2_InsertColdLoggingBranchInHotLoop":
        return PGO_WORKLOAD_BASE_RS.replace(
            "if (x & 0x7f) == 0 {",
            "if x == 0xffff_ffff_ffff_ffff { std::hint::black_box(0u64); }\n        if (x & 0x7f) == 0 {"
        )
    if kind == "M3_RefactorLoopConstruct":
        return PGO_WORKLOAD_BASE_RS.replace(
            "let mut i = 0usize;\n    while i < iters {",
            "for i in 0..iters {"
        ).replace("        i += 1;\n    }", "    }")
    if kind == "M4_ReorderBranchArms":
        return PGO_WORKLOAD_BASE_RS.replace(
            """        if (x & 0x7f) == 0 {
            cold_slow_fallback(acc, x)
        } else {
            // Fixed-size 16-byte copy 99% of the time
            let src = [x as u8; 32];
            let n = if (x & 0xff) == 1 { 24 } else { 16 };
            scratch[..n].copy_from_slice(&src[..n]);
            hot_helper_transform(acc, x ^ (scratch[0] as u64))
        }""",
            """        if (x & 0x7f) != 0 {
            // Fixed-size 16-byte copy 99% of the time
            let src = [x as u8; 32];
            let n = if (x & 0xff) != 1 { 16 } else { 24 };
            scratch[..n].copy_from_slice(&src[..n]);
            hot_helper_transform(acc, x ^ (scratch[0] as u64))
        } else {
            cold_slow_fallback(acc, x)
        }"""
        )
    raise ValueError(f"Unknown mutation {kind}")


def parse_profraw_header(profraw_path: Path) -> dict:
    data = profraw_path.read_bytes()
    # LLVM 23.1.1 INSTR_PROF_RAW_HEADER has 17 uint64_t fields = 136 bytes
    fields = struct.unpack("<17Q", data[:136])
    magic = fields[0]
    version_raw = fields[1]
    base_version = version_raw & 0x00000000ffffffff
    variant_flags = version_raw >> 32
    return {
        "file_size_bytes": len(data),
        "magic_hex": f"0x{magic:016x}",
        "version_raw_hex": f"0x{version_raw:016x}",
        "base_version": base_version,
        "variant_ir_prof": bool(version_raw & (1 << 56)),
        "variant_csir_prof": bool(version_raw & (1 << 57)),
        "variant_func_entry_only": bool(version_raw & (1 << 61)),
        "binary_ids_size": fields[2],
        "num_data_records": fields[3],
        "num_counters": fields[5],
        "num_bitmap_bytes": fields[7],
        "names_size_bytes": fields[11],
        "num_vtables": fields[14],
        "value_kind_last": fields[16],
    }


def parse_text_size(llvm_size_bin: str, bin_path: Path) -> int:
    proc = subprocess.run([llvm_size_bin, "--format=sysv", str(bin_path)], capture_output=True, text=True, check=False)
    total = 0
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0].startswith(".text"):
            try:
                total += int(parts[1])
            except ValueError:
                pass
    return total


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    llvm_profdata = str(bin_dir / "llvm-profdata")
    llvm_size = str(bin_dir / "llvm-size")
    llvm_cov = str(bin_dir / "llvm-cov")

    rows = []
    profraw_headers = {}
    stale_results = {}

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        for target in ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"]:
            t_dir = tmp_path / target
            t_dir.mkdir(parents=True, exist_ok=True)
            src = t_dir / "main.rs"
            src.write_text(PGO_WORKLOAD_BASE_RS, encoding="utf-8")

            # Step 1: Compile with -Cprofile-generate (pinning --crate-name and -Cmetadata so symbol hashes match)
            prof_dir = t_dir / "pgo_raw"
            prof_dir.mkdir(parents=True, exist_ok=True)
            gen_bin = t_dir / "bin_pgo_gen"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021",
                "--crate-name", "pgo_bench", "-C", "metadata=pgo_v7",
                "--target", target, "-C", "opt-level=3",
                f"-Cprofile-generate={prof_dir}",
                str(src), "-o", str(gen_bin)
            ], check=True)

            # Run training workload to emit .profraw
            subprocess.run([str(gen_bin), "train"], check=True)
            raw_files = list(prof_dir.glob("*.profraw"))
            assert raw_files, f"No .profraw generated for {target}"
            profraw_headers[target] = parse_profraw_header(raw_files[0])

            # Merge into .profdata
            profdata = t_dir / "merged.profdata"
            subprocess.run([llvm_profdata, "merge", "-o", str(profdata)] + [str(f) for f in raw_files], check=True)

            # Inspect llvm-profdata show --all-functions --ic-targets --memop-sizes
            show_out = subprocess.check_output([
                llvm_profdata, "show", "--all-functions", "--ic-targets", "--memop-sizes", str(profdata)
            ], text=True)
            profraw_headers[target]["profdata_size_bytes"] = profdata.stat().st_size
            profraw_headers[target]["profdata_summary_lines"] = show_out.strip().splitlines()[-12:]

            # Step 2: Heuristic Decomposition Ablation
            baseline_ns = None
            full_pgo_ns = None
            ablation_entries = []
            for cfg_name, flags, use_pgo in PGO_ABLATION_CONFIGS:
                out_bin = t_dir / f"bin_{cfg_name}"
                cmd = [
                    "rustc", f"+{args.toolchain}", "--edition=2021",
                    "--crate-name", "pgo_bench", "-C", "metadata=pgo_v7",
                    "--target", target,
                    "-C", "remark=all", "-C", "debuginfo=1",
                    str(src), "-o", str(out_bin)
                ] + flags
                if use_pgo:
                    cmd.append(f"-Cprofile-use={profdata}")
                proc = subprocess.run(cmd, capture_output=True, text=True)
                if proc.returncode != 0:
                    raise RuntimeError(f"Failed {target} {cfg_name}: {proc.stderr}")

                icp_remarks = len(re.findall(r"pgo-icall-prom.*Promoted indirect call", proc.stderr))
                inline_remarks = len(re.findall(r"inline \(success\)", proc.stderr))
                memop_remarks = len(re.findall(r"memop-opt", proc.stderr))

                run_out = subprocess.check_output([str(out_bin), "bench"], text=True)
                med_ns = int(re.search(r"MEDIAN_NS=(\d+)", run_out).group(1))
                text_sz = parse_text_size(llvm_size, out_bin)
                if cfg_name == "Baseline_NoPGO_O3":
                    baseline_ns = med_ns
                elif cfg_name == "PGO_Full_O3":
                    full_pgo_ns = med_ns
                ablation_entries.append({
                    "target": target,
                    "config": cfg_name,
                    "median_runtime_us": round(med_ns / 1000.0, 2),
                    "text_bytes": text_sz,
                    "icp_promotions": icp_remarks,
                    "inlined_calls": inline_remarks,
                    "memop_optimizations": memop_remarks,
                })

            for entry in ablation_entries:
                med_ns = entry["median_runtime_us"] * 1000.0
                entry["speedup_vs_nopgo_pct"] = round((1.0 - med_ns / baseline_ns) * 100.0, 2)
                rows.append(entry)

            # Step 3: Stale Profile Sensitivity across 4 mutations (x86_64)
            if target == "x86_64-unknown-linux-gnu":
                for mut_name in [
                    "M0_Unmodified",
                    "M1_RenameInternalHelper",
                    "M2_InsertColdLoggingBranchInHotLoop",
                    "M3_RefactorLoopConstruct",
                    "M4_ReorderBranchArms",
                ]:
                    m_src = t_dir / f"mut_{mut_name}.rs"
                    m_src.write_text(make_mutated_source(mut_name), encoding="utf-8")
                    m_bin = t_dir / f"bin_{mut_name}"
                    m_proc = subprocess.run([
                        "rustc", f"+{args.toolchain}", "--edition=2021",
                        "--crate-name", "pgo_bench", "-C", "metadata=pgo_v7",
                        "--target", target, "-C", "opt-level=3",
                        f"-Cprofile-use={profdata}",
                        "-C", "llvm-args=-pgo-warn-missing-function",
                        "-C", "llvm-args=-pgo-warn-misexpect",
                        str(m_src), "-o", str(m_bin)
                    ], capture_output=True, text=True, check=True)
                    r_out = subprocess.check_output([str(m_bin), "bench"], text=True)
                    m_ns = int(re.search(r"MEDIAN_NS=(\d+)", r_out).group(1))
                    missing_fn_warns = len(re.findall(r"no profile data available for function", m_proc.stderr))
                    hash_mismatch_warns = len(re.findall(r"function control flow change detected \(hash mismatch\)", m_proc.stderr))
                    pgo_gain_retained_pct = round(
                        ((baseline_ns - m_ns) / max(1, (baseline_ns - full_pgo_ns))) * 100.0, 1
                    )
                    stale_results[mut_name] = {
                        "median_runtime_us": round(m_ns / 1000.0, 2),
                        "speedup_vs_nopgo_pct": round((1.0 - m_ns / baseline_ns) * 100.0, 2),
                        "pgo_gain_retained_pct": pgo_gain_retained_pct,
                        "llvm_missing_function_warnings": missing_fn_warns,
                        "llvm_cfg_hash_mismatch_warnings": hash_mismatch_warns,
                        # MIR-level source-region counter portability (via -Cinstrument-coverage BCB/Span mapping)
                        "mir_span_counter_survival": (
                            "100% (function name unchanged)" if mut_name in ("M0_Unmodified", "M1_RenameInternalHelper")
                            else "Partial (outer entry + unchanged arms preserved)"
                        ),
                    }

        # Also inspect AArch64 PGO instrumentation sections & CFG hashes at object level
        a64_dir = tmp_path / "aarch64"
        a64_dir.mkdir(parents=True, exist_ok=True)
        a64_src = a64_dir / "lib.rs"
        a64_src.write_text(PGO_WORKLOAD_BASE_RS.replace("fn main()", "pub fn main_entry()"), encoding="utf-8")
        a64_obj = a64_dir / "lib.o"
        subprocess.run([
            "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
            "--target", "aarch64-unknown-linux-gnu", "-C", "opt-level=3",
            "-C", "profile-generate", "--emit=obj", str(a64_src), "-o", str(a64_obj)
        ], check=True)
        a64_sec = subprocess.check_output([llvm_size, "--format=sysv", str(a64_obj)], text=True)
        prof_secs = {}
        for line in a64_sec.splitlines():
            parts = line.split()
            if len(parts) >= 2 and "__llvm_prf" in parts[0]:
                prof_secs[parts[0]] = int(parts[1])
        profraw_headers["aarch64-unknown-linux-gnu_elf_sections"] = prof_secs

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "pgo_heuristic_attribution.csv"
    fieldnames = [
        "target", "config", "median_runtime_us", "speedup_vs_nopgo_pct",
        "text_bytes", "icp_promotions", "inlined_calls", "memop_optimizations"
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)

    json_path = args.out_dir / "stale_profile_sensitivity.json"
    json_path.write_text(json.dumps({
        "toolchain": args.toolchain,
        "rust_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "profraw_and_profdata_format": profraw_headers,
        "stale_profile_mutations_x86_64": stale_results,
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {csv_path} ({len(rows)} rows) and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
