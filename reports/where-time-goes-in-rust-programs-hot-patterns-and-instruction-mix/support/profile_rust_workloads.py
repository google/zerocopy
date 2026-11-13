#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Workload profiler for Rust 1.99.1 / LLVM 23.1.1: instruction mix, MIR-to-machine bounds-check survival, inlining depth, and -Ctarget-cpu sensitivity."""

import argparse
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

# 8 domain kernels matching P2's 8 benchmark categories:
# 1. slice_bounds_iter: slice indexing & iteration
# 2. iter_combinators: filter/map/fold chains
# 3. utf8_scanner: ASCII/UTF-8 validation & byte scanning
# 4. hash_crc_digest:folded multiply + CRC/SipHash-style mixing
# 5. sort_binary_search: slice binary search + insertion sort
# 6. zerocopy_endian: unaligned little/big-endian packet parsing
# 7. enum_dyn_dispatch: enum switch vs trait object dispatch
# 8. simd_numeric_dot: autovectorized dot product & matrix-vector kernel

BENCH_KERNELS_RS = r"""#![allow(dead_code)]

#[inline(never)]
pub fn k1_slice_bounds_iter(data: &[u32], indices: &[usize]) -> u64 {
    let mut sum = 0u64;
    // Checked indexing (some elided via slice length guard, some surviving for arbitrary indices)
    for &idx in indices {
        if idx < data.len() {
            sum = sum.wrapping_add(data[idx] as u64);
        }
    }
    for i in 0..data.len().saturating_sub(3) {
        sum = sum.wrapping_add((data[i] ^ data[i + 1] ^ data[i + 2] ^ data[i + 3]) as u64);
    }
    sum
}

#[inline(never)]
pub fn k2_iter_combinators(data: &[u32]) -> u64 {
    data.iter()
        .copied()
        .enumerate()
        .filter(|&(i, v)| ((v ^ (i as u32)) & 3) != 0)
        .map(|(i, v)| (v as u64).wrapping_mul((i as u64) | 1).rotate_left(7))
        .fold(0u64, |acc, x| acc.wrapping_add(x ^ 0x9e3779b97f4a7c15))
}

#[inline(never)]
pub fn k3_utf8_scanner(bytes: &[u8]) -> usize {
    let mut ascii_count = 0usize;
    let mut multibyte_lead = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x80 {
            ascii_count += 1;
            i += 1;
        } else if b < 0xE0 {
            multibyte_lead += 1;
            i += 2;
        } else if b < 0xF0 {
            multibyte_lead += 2;
            i += 3;
        } else {
            multibyte_lead += 3;
            i += 4;
        }
    }
    ascii_count ^ (multibyte_lead << 8)
}

#[inline(never)]
pub fn k4_hash_crc_digest(bytes: &[u8], seed: u64) -> u64 {
    let mut h = seed ^ 0xbf58476d1ce4e5b9;
    let mut chunks = bytes.chunks_exact(8);
    for c in &mut chunks {
        let w = u64::from_le_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]);
        h = (h ^ w).rotate_left(23).wrapping_mul(0x94d049bb133111eb);
    }
    for &b in chunks.remainder() {
        h = (h ^ (b as u64)).wrapping_mul(0x2545f4914f6cdd1d);
    }
    h ^ (h >> 32)
}

#[inline(never)]
pub fn k5_sort_binary_search(buf: &mut [u32], queries: &[u32]) -> usize {
    // Small-window insertion sort + binary_search
    let n = buf.len().min(64);
    for i in 1..n {
        let key = buf[i];
        let mut j = i;
        while j > 0 && buf[j - 1] > key {
            buf[j] = buf[j - 1];
            j -= 1;
        }
        buf[j] = key;
    }
    let sorted = &buf[..n];
    let mut hits = 0usize;
    for &q in queries {
        if sorted.binary_search(&q).is_ok() {
            hits += 1;
        }
    }
    hits
}

#[inline(never)]
pub fn k6_zerocopy_endian(bytes: &[u8]) -> u64 {
    let mut acc = 0u64;
    let mut i = 0usize;
    while i + 16 <= bytes.len() {
        let magic = u32::from_be_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        let len = u16::from_be_bytes([bytes[i + 4], bytes[i + 5]]);
        let flags = u16::from_le_bytes([bytes[i + 6], bytes[i + 7]]);
        let payload = u64::from_be_bytes([
            bytes[i + 8], bytes[i + 9], bytes[i + 10], bytes[i + 11],
            bytes[i + 12], bytes[i + 13], bytes[i + 14], bytes[i + 15],
        ]);
        acc = acc.wrapping_add((magic as u64) ^ ((len as u64) << 16) ^ (flags as u64) ^ payload);
        i += 16;
    }
    acc
}

pub trait PacketFilter {
    fn filter(&self, val: u32) -> u32;
}
pub struct XorFilter(pub u32);
impl PacketFilter for XorFilter {
    #[inline(never)]
    fn filter(&self, val: u32) -> u32 { val.rotate_left(11) ^ self.0 }
}
pub struct MulFilter(pub u32);
impl PacketFilter for MulFilter {
    #[inline(never)]
    fn filter(&self, val: u32) -> u32 { val.wrapping_mul(self.0 | 1) }
}

#[inline(never)]
pub fn k7_enum_dyn_dispatch(data: &[u32]) -> u64 {
    let f1 = XorFilter(0x13579bdf);
    let f2 = MulFilter(0x2468ace1);
    let filters: [&dyn PacketFilter; 2] = [&f1, &f2];
    let mut acc = 0u64;
    for (i, &v) in data.iter().enumerate() {
        let f = core::hint::black_box(filters[i & 1]);
        acc = acc.wrapping_add(f.filter(v) as u64);
    }
    acc
}

#[inline(never)]
pub fn k8_simd_numeric_dot(a: &[u32], b: &[u32]) -> u64 {
    let n = a.len().min(b.len());
    let mut sum = 0u64;
    for i in 0..n {
        sum = sum.wrapping_add((a[i].wrapping_mul(b[i]).wrapping_add(a[i] ^ b[i])) as u64);
    }
    sum
}
"""

RUNNER_MAIN_RS = r"""
use std::time::Instant;

fn main() {
    let mut data: Vec<u32> = (0..4096u32).map(|x| x.wrapping_mul(2654435761)).collect();
    let indices: Vec<usize> = (0..4096usize).map(|x| (x * 7) & 4095).collect();
    let bytes: Vec<u8> = (0..16384usize).map(|x| ((x * 31 + 17) & 0x7f) as u8).collect();
    let queries: Vec<u32> = (0..512u32).map(|x| x.wrapping_mul(2654435761)).collect();

    let mut samples = Vec::with_capacity(35);
    let mut sink = 0u64;
    for r in 0..35 {
        let t0 = Instant::now();
        for _ in 0..25 {
            sink ^= k1_slice_bounds_iter(std::hint::black_box(&data), std::hint::black_box(&indices));
            sink ^= k2_iter_combinators(std::hint::black_box(&data));
            sink ^= k3_utf8_scanner(std::hint::black_box(&bytes)) as u64;
            sink ^= k4_hash_crc_digest(std::hint::black_box(&bytes), r as u64);
            sink ^= k5_sort_binary_search(std::hint::black_box(&mut data), std::hint::black_box(&queries)) as u64;
            sink ^= k6_zerocopy_endian(std::hint::black_box(&bytes));
            sink ^= k7_enum_dyn_dispatch(std::hint::black_box(&data));
            sink ^= k8_simd_numeric_dot(std::hint::black_box(&data), std::hint::black_box(&queries));
        }
        let dt = t0.elapsed().as_nanos() as u64;
        if r >= 5 {
            samples.push(dt);
        }
    }
    samples.sort_unstable();
    println!("MEDIAN_NS={} SINK={}", samples[samples.len() / 2], sink);
}
"""

KERNEL_NAMES = [
    "k1_slice_bounds_iter",
    "k2_iter_combinators",
    "k3_utf8_scanner",
    "k4_hash_crc_digest",
    "k5_sort_binary_search",
    "k6_zerocopy_endian",
    "k7_enum_dyn_dispatch",
    "k8_simd_numeric_dot",
]


def classify_function_asm(disasm: str, fn_name: str, arch: str) -> dict:
    # Extract lines belonging to fn_name
    pattern = re.compile(rf"^[0-9a-fA-F]+\s+<[^>]*{re.escape(fn_name)}[^>]*>:", re.MULTILINE)
    m = pattern.search(disasm)
    if not m:
        return {
            "total_insts": 0, "alu_insts": 0, "mem_insts": 0,
            "branch_insts": 0, "simd_insts": 0, "indirect_call_insts": 0,
            "panic_bounds_calls": 0
        }
    start = m.end()
    next_fn = re.search(r"^[0-9a-fA-F]+\s+<[^>]+>:", disasm[start:], re.MULTILINE)
    block = disasm[start:start + next_fn.start()] if next_fn else disasm[start:]

    total = 0
    alu = 0
    mem = 0
    br = 0
    simd = 0
    icall = 0
    bounds_calls = 0

    for line in block.splitlines():
        if "panic_bounds_check" in line or "slice_index_len_fail" in line or "slice_end_index_len_fail" in line:
            bounds_calls += 1
        if not re.match(r"^\s*[0-9a-fA-F]+:", line):
            continue
        parts = line.split("\t", 1)
        if len(parts) < 2:
            continue
        inst_str = parts[1].strip()
        if not inst_str or inst_str.startswith("."):
            continue
        mnem = inst_str.split()[0].lower()
        if mnem in ("nop", "endbr64", "endbr32", "hint"):
            continue
        total += 1

        if arch in ("x86_64", "i686"):
            if mnem.startswith("v") or any(reg in inst_str for reg in ("%xmm", "%ymm", "%zmm", "xmm", "ymm", "zmm")):
                simd += 1
            elif mnem.startswith(("j", "call", "ret", "ud2")):
                br += 1
                if mnem.startswith("call") and ("*" in inst_str or ("%" in inst_str and "%rip" not in inst_str)):
                    icall += 1
            elif "(" in inst_str and mnem not in ("lea", "leaq", "leal"):
                mem += 1
            else:
                alu += 1
        else:  # aarch64
            if any(v in inst_str for v in ("v0.", "v1.", "v2.", "v3.", "v4.", "v5.", "v6.", "v7.", "q0", "q1", "q2", "q3")) or mnem in ("ld1", "st1", "uminv", "addv", "eor", "umull", "umlal"):
                simd += 1
            elif mnem.startswith(("b", "cbz", "cbnz", "tbz", "tbnz", "ret", "blr", "br", "brk")):
                br += 1
                if mnem in ("blr", "br"):
                    icall += 1
            elif mnem.startswith(("ldr", "str", "ldp", "stp", "ldur", "stur", "ldrb", "strb", "ldrh", "strh")):
                mem += 1
            else:
                alu += 1

    return {
        "total_insts": total,
        "alu_insts": alu,
        "mem_insts": mem,
        "branch_insts": br,
        "simd_insts": simd,
        "indirect_call_insts": icall,
        "panic_bounds_calls": bounds_calls,
    }


def count_mir_bounds_checks(mir_text: str, fn_name: str) -> int:
    # Extract MIR body for fn_name
    m = re.search(rf"^fn {re.escape(fn_name)}\(.*?\n\{{(.*?)^\}}", mir_text, re.MULTILINE | re.DOTALL)
    if not m:
        return 0
    body = m.group(1)
    asserts = len(re.findall(r"assert\(.*?(?:out-of-bounds|index out of bounds|BoundsCheck)", body))
    slice_checks = len(re.findall(r"slice_index_len_fail|slice_end_index_len_fail|panic_bounds_check|Index::index", body))
    return asserts + slice_checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    llvm_objdump = str(bin_dir / "llvm-objdump")
    llvm_size = str(bin_dir / "llvm-size")

    mix_rows = []
    cpu_rows = []

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src_lib = tmp_path / "kernels.rs"
        src_lib.write_text("#![no_std]\n" + BENCH_KERNELS_RS, encoding="utf-8")

        # 1. Instruction mix and MIR-to-machine bounds-check survival across x86_64, i686, aarch64
        for target, arch in [
            ("x86_64-unknown-linux-gnu", "x86_64"),
            ("i686-unknown-linux-gnu", "i686"),
            ("aarch64-unknown-linux-gnu", "aarch64"),
        ]:
            t_dir = tmp_path / f"mix_{target}"
            t_dir.mkdir(parents=True, exist_ok=True)
            # Emit unoptimized MIR (-Zmir-opt-level=0) to count initial MIR bounds checks
            mir_o0 = t_dir / "kernels_o0.mir"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", target, "-C", "opt-level=0", "-Z", "mir-opt-level=0",
                "--emit=mir", str(src_lib), "-o", str(mir_o0)
            ], env={**os.environ, "RUSTC_BOOTSTRAP": "1"}, check=True)
            mir_text_o0 = mir_o0.read_text(encoding="utf-8")

            # Emit -O0 object and -O3 object
            obj_o0 = t_dir / "kernels_o0.o"
            obj_o3 = t_dir / "kernels_o3.o"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", target, "-C", "opt-level=0",
                "--emit=obj", str(src_lib), "-o", str(obj_o0)
            ], check=True)
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", target, "-C", "opt-level=3", "-C", " debuginfo=1", "-C", "remark=all",
                "--emit=obj", str(src_lib), "-o", str(obj_o3)
            ] if False else [
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", target, "-C", "opt-level=3",
                "--emit=obj", str(src_lib), "-o", str(obj_o3)
            ], check=True)

            dis_o0 = subprocess.check_output([llvm_objdump, "-d", "-r", "--no-show-raw-insn", str(obj_o0)], text=True)
            dis_o3 = subprocess.check_output([llvm_objdump, "-d", "-r", "--no-show-raw-insn", str(obj_o3)], text=True)

            for kname in KERNEL_NAMES:
                mir_bc = count_mir_bounds_checks(mir_text_o0, kname)
                stats_o0 = classify_function_asm(dis_o0, kname, arch)
                stats_o3 = classify_function_asm(dis_o3, kname, arch)
                total = max(1, stats_o3["total_insts"])
                mix_rows.append({
                    "target": target,
                    "kernel": kname,
                    "mir_bounds_checks_o0": mir_bc,
                    "machine_bounds_panics_o0": stats_o0["panic_bounds_calls"],
                    "machine_bounds_panics_o3": stats_o3["panic_bounds_calls"],
                    "bounds_check_eliminated_pct": round(
                        (1.0 - stats_o3["panic_bounds_calls"] / max(1, stats_o0["panic_bounds_calls"])) * 100.0, 1
                    ) if stats_o0["panic_bounds_calls"] > 0 else 100.0,
                    "o3_total_insts": stats_o3["total_insts"],
                    "o3_alu_pct": round(stats_o3["alu_insts"] * 100.0 / total, 1),
                    "o3_mem_pct": round(stats_o3["mem_insts"] * 100.0 / total, 1),
                    "o3_branch_pct": round(stats_o3["branch_insts"] * 100.0 / total, 1),
                    "o3_simd_pct": round(stats_o3["simd_insts"] * 100.0 / total, 1),
                    "o3_indirect_calls": stats_o3["indirect_call_insts"],
                })

        # 2. Target CPU Microarchitecture Sensitivity (-Ctarget-cpu sweep)
        src_bin = tmp_path / "bench_main.rs"
        src_bin.write_text(BENCH_KERNELS_RS + "\n" + RUNNER_MAIN_RS, encoding="utf-8")

        x86_cpus = ["x86-64", "x86-64-v2", "x86-64-v3", "x86-64-v4", "native"]
        base_x86_ns = None
        for cpu in x86_cpus:
            out_bin = tmp_path / f"bin_x86_{cpu}"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021",
                "--target", "x86_64-unknown-linux-gnu", "-C", "opt-level=3",
                f"-Ctarget-cpu={cpu}", str(src_bin), "-o", str(out_bin)
            ], check=True)
            dis = subprocess.check_output([llvm_objdump, "-d", "-r", "--no-show-raw-insn", str(out_bin)], text=True)
            total_simd = 0
            total_insts = 0
            for kname in KERNEL_NAMES:
                st = classify_function_asm(dis, kname, "x86_64")
                total_simd += st["simd_insts"]
                total_insts += st["total_insts"]
            run_out = subprocess.check_output([str(out_bin)], text=True)
            med_ns = int(re.search(r"MEDIAN_NS=(\d+)", run_out).group(1))
            if base_x86_ns is None:
                base_x86_ns = med_ns
            text_sz = 0
            for line in subprocess.check_output([llvm_size, "--format=sysv", str(out_bin)], text=True).splitlines():
                p = line.split()
                if len(p) >= 2 and p[0] == ".text":
                    text_sz = int(p[1])
            cpu_rows.append({
                "target": "x86_64-unknown-linux-gnu",
                "target_cpu": cpu,
                "kernels_total_insts": total_insts,
                "kernels_simd_insts": total_simd,
                "kernels_simd_share_pct": round(total_simd * 100.0 / max(1, total_insts), 1),
                "binary_text_bytes": text_sz,
                "median_runtime_us": round(med_ns / 1000.0, 2),
                "speedup_vs_baseline_cpu_pct": round((1.0 - med_ns / base_x86_ns) * 100.0, 2),
            })

        a64_cpus = ["generic", "neoverse-n1", "neoverse-v1", "apple-m1"]
        for cpu in a64_cpus:
            out_obj = tmp_path / f"obj_a64_{cpu}.o"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", "aarch64-unknown-linux-gnu", "-C", "opt-level=3",
                f"-Ctarget-cpu={cpu}", "--emit=obj", str(src_lib), "-o", str(out_obj)
            ], check=True)
            dis = subprocess.check_output([llvm_objdump, "-d", "-r", "--no-show-raw-insn", str(out_obj)], text=True)
            total_simd = 0
            total_insts = 0
            for kname in KERNEL_NAMES:
                st = classify_function_asm(dis, kname, "aarch64")
                total_simd += st["simd_insts"]
                total_insts += st["total_insts"]
            text_sz = 0
            for line in subprocess.check_output([llvm_size, "--format=sysv", str(out_obj)], text=True).splitlines():
                p = line.split()
                if len(p) >= 2 and p[0].startswith(".text"):
                    text_sz += int(p[1])
            cpu_rows.append({
                "target": "aarch64-unknown-linux-gnu",
                "target_cpu": cpu,
                "kernels_total_insts": total_insts,
                "kernels_simd_insts": total_simd,
                "kernels_simd_share_pct": round(total_simd * 100.0 / max(1, total_insts), 1),
                "binary_text_bytes": text_sz,
                "median_runtime_us": "",
                "speedup_vs_baseline_cpu_pct": "",
            })

    args.out_dir.mkdir(parents=True, exist_ok=True)
    mix_csv = args.out_dir / "instruction_mix_and_bounds_checks.csv"
    with open(mix_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=[
            "target", "kernel", "mir_bounds_checks_o0",
            "machine_bounds_panics_o0", "machine_bounds_panics_o3", "bounds_check_eliminated_pct",
            "o3_total_insts", "o3_alu_pct", "o3_mem_pct", "o3_branch_pct", "o3_simd_pct", "o3_indirect_calls"
        ])
        w.writeheader()
        w.writerows(mix_rows)

    cpu_csv = args.out_dir / "target_cpu_sensitivity.csv"
    with open(cpu_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=[
            "target", "target_cpu", "kernels_total_insts", "kernels_simd_insts",
            "kernels_simd_share_pct", "binary_text_bytes", "median_runtime_us", "speedup_vs_baseline_cpu_pct"
        ])
        w.writeheader()
        w.writerows(cpu_rows)

    print(f"Wrote {mix_csv} ({len(mix_rows)} rows) and {cpu_csv} ({len(cpu_rows)} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
