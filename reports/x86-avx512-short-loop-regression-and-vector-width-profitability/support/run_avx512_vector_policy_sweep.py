#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Controlled AVX-512 / x86-64-v3 / x86-64-v4 / AArch64 SVE short-loop regression root-cause decomposition and 5-strategy vector-width / tail-folding sweep for rustc 1.99.1 / LLVM 23.1.1."""

import argparse
import csv
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Exact 8 kernels from E3 (`where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix`)
# plus k9_slice_affine_update for controlled trip-count sweeps.
BENCH_KERNELS_RS = r"""#![allow(dead_code)]

#[inline(never)]
pub fn k1_slice_bounds_iter(data: &[u32], indices: &[usize]) -> u64 {
    let mut sum = 0u64;
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

#[inline(never)]
pub fn k9_slice_affine_update(dst: &mut [u32], src: &[u32], scale: u32, bias: u32) {
    let n = dst.len().min(src.len());
    for i in 0..n {
        dst[i] = dst[i].wrapping_add(src[i].wrapping_mul(scale) ^ bias);
    }
}
"""

RUNNER_MAIN_RS = r"""
use std::time::Instant;

fn bench_one<F: FnMut() -> u64>(mut f: F) -> f64 {
    let mut s = Vec::with_capacity(25);
    let mut sink = 0u64;
    for r in 0..25 {
        let t0 = Instant::now();
        for _ in 0..25 { sink ^= f(); }
        let dt = t0.elapsed().as_nanos() as u64;
        if r >= 5 { s.push(dt); }
    }
    s.sort_unstable();
    if sink == 0xdead_beef_cafe_babe { println!("!"); }
    s[s.len() / 2] as f64 / 1000.0
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("e3_suite");

    if mode == "trip_sweep" {
        let trip_n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(32);
        let total_work = 65536usize;
        let outer_reps = (total_work / trip_n.max(1)).max(16);
        let mut a: Vec<u32> = (0..trip_n as u32).map(|x| x.wrapping_mul(2654435761) | 1).collect();
        let b: Vec<u32> = (0..trip_n as u32).map(|x| x.wrapping_mul(1597334677) ^ 0x5a5a5a5a).collect();
        let indices: Vec<usize> = (0..trip_n).map(|x| (x * 7) % trip_n.max(1)).collect();
        let mut samples = Vec::with_capacity(35);
        let mut sink = 0u64;
        for r in 0..35 {
            let t0 = Instant::now();
            for rep in 0..outer_reps {
                sink ^= k8_simd_numeric_dot(std::hint::black_box(&a), std::hint::black_box(&b));
                k9_slice_affine_update(
                    std::hint::black_box(&mut a),
                    std::hint::black_box(&b),
                    (rep as u32) | 3,
                    r as u32,
                );
                sink ^= k1_slice_bounds_iter(std::hint::black_box(&a), std::hint::black_box(&indices));
            }
            let dt = t0.elapsed().as_nanos() as u64;
            if r >= 5 {
                samples.push(dt);
            }
        }
        samples.sort_unstable();
        let med_ns = samples[samples.len() / 2];
        let ns_per_1k_elems = (med_ns as f64) * 1000.0 / ((outer_reps * trip_n) as f64);
        println!("MEDIAN_NS={} NS_PER_1K={:.2} SINK={}", med_ns, ns_per_1k_elems, sink);
        return;
    }

    let mut data: Vec<u32> = (0..4096u32).map(|x| x.wrapping_mul(2654435761)).collect();
    let indices: Vec<usize> = (0..4096usize).map(|x| (x * 7) & 4095).collect();
    let bytes: Vec<u8> = (0..16384usize).map(|x| ((x * 31 + 17) & 0x7f) as u8).collect();
    let queries: Vec<u32> = (0..512u32).map(|x| x.wrapping_mul(2654435761)).collect();

    if mode == "per_kernel" {
        let t1 = bench_one(|| k1_slice_bounds_iter(std::hint::black_box(&data), std::hint::black_box(&indices)));
        let t2 = bench_one(|| k2_iter_combinators(std::hint::black_box(&data)));
        let t3 = bench_one(|| k3_utf8_scanner(std::hint::black_box(&bytes)) as u64);
        let t4 = bench_one(|| k4_hash_crc_digest(std::hint::black_box(&bytes), 1));
        let t5 = bench_one(|| k5_sort_binary_search(std::hint::black_box(&mut data), std::hint::black_box(&queries)) as u64);
        let t6 = bench_one(|| k6_zerocopy_endian(std::hint::black_box(&bytes)));
        let t7 = bench_one(|| k7_enum_dyn_dispatch(std::hint::black_box(&data)));
        let t8 = bench_one(|| k8_simd_numeric_dot(std::hint::black_box(&data), std::hint::black_box(&queries)));
        println!(
            "K1={:.2} K2={:.2} K3={:.2} K4={:.2} K5={:.2} K6={:.2} K7={:.2} K8={:.2}",
            t1, t2, t3, t4, t5, t6, t7, t8
        );
        return;
    }

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

STRATEGIES = [
    ("Default_Unconstrained", []),
    ("Counterfactual_Force512BitZMM", [
        "-C", "target-feature=-prefer-256-bit",
    ]),
    ("StratA_Cap256_NoEVEX512_NoGather", [
        "-C", "target-feature=+prefer-256-bit,-evex512,+prefer-no-gather",
    ]),
    ("StratB_PredicatedTailFold_NoGather", [
        "-C", "target-feature=+prefer-no-gather",
        "-C", "llvm-args=--tail-folding-policy=prefer-fold-tail",
    ]),
    ("StratC_MinTrip64_CheckCap4", [
        "-C", "target-feature=+prefer-no-gather",
        "-C", "llvm-args=--vectorizer-min-trip-count=64",
        "-C", "llvm-args=--runtime-memory-check-threshold=4",
    ]),
    ("StratD_InterleaveCap1_NoGather", [
        "-C", "target-feature=+prefer-no-gather",
        "-C", "llvm-args=--force-vector-interleave=1",
    ]),
    ("StratE_Hybrid_Cap256_NoGather_UF1", [
        "-C", "target-feature=+prefer-256-bit,-evex512,+prefer-no-gather,-avx512vl",
        "-C", "llvm-args=--force-vector-interleave=1",
    ]),
]


def analyze_x86_disasm(disasm: str, fn_names: list[str]) -> dict:
    total_insts = 0
    simd_insts = 0
    xmm_insts = 0
    ymm_insts = 0
    zmm_insts = 0
    kmask_insts = 0
    gather_insts = 0
    branch_insts = 0
    per_kernel = {}

    for fn_name in fn_names:
        pattern = re.compile(rf"^[0-9a-fA-F]+\s+<[^>]*{re.escape(fn_name)}[^>]*>:", re.MULTILINE)
        m = pattern.search(disasm)
        if not m:
            continue
        start = m.end()
        next_fn = re.search(r"^[0-9a-fA-F]+\s+<[^>]+>:", disasm[start:], re.MULTILINE)
        block = disasm[start:start + next_fn.start()] if next_fn else disasm[start:]

        k_tot = k_simd = k_xmm = k_ymm = k_zmm = k_kmask = k_gather = k_br = 0
        for line in block.splitlines():
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
            k_tot += 1
            if mnem.startswith("v") or any(reg in inst_str for reg in ("%xmm", "%ymm", "%zmm", "xmm", "ymm", "zmm")):
                k_simd += 1
            if "zmm" in inst_str:
                k_zmm += 1
            elif "ymm" in inst_str:
                k_ymm += 1
            elif "xmm" in inst_str:
                k_xmm += 1
            if "{%k" in inst_str or mnem.startswith("k"):
                k_kmask += 1
            if "gather" in mnem:
                k_gather += 1
            if mnem.startswith(("j", "call", "ret", "ud2")):
                k_br += 1

        total_insts += k_tot
        simd_insts += k_simd
        xmm_insts += k_xmm
        ymm_insts += k_ymm
        zmm_insts += k_zmm
        kmask_insts += k_kmask
        gather_insts += k_gather
        branch_insts += k_br
        per_kernel[fn_name] = {
            "total_insts": k_tot,
            "simd_insts": k_simd,
            "xmm_insts": k_xmm,
            "ymm_insts": k_ymm,
            "zmm_insts": k_zmm,
            "kmask_insts": k_kmask,
            "gather_insts": k_gather,
            "branch_insts": k_br,
        }

    return {
        "total_insts": total_insts,
        "simd_insts": simd_insts,
        "xmm_insts": xmm_insts,
        "ymm_insts": ymm_insts,
        "zmm_insts": zmm_insts,
        "kmask_insts": kmask_insts,
        "gather_insts": gather_insts,
        "branch_insts": branch_insts,
        "per_kernel": per_kernel,
    }


def analyze_aarch64_disasm(disasm: str, fn_names: list[str]) -> dict:
    total_insts = 0
    neon_insts = 0
    sve_insts = 0
    whilelo_insts = 0
    branch_insts = 0
    for fn_name in fn_names:
        pattern = re.compile(rf"^[0-9a-fA-F]+\s+<[^>]*{re.escape(fn_name)}[^>]*>:", re.MULTILINE)
        m = pattern.search(disasm)
        if not m:
            continue
        start = m.end()
        next_fn = re.search(r"^[0-9a-fA-F]+\s+<[^>]+>:", disasm[start:], re.MULTILINE)
        block = disasm[start:start + next_fn.start()] if next_fn else disasm[start:]
        for line in block.splitlines():
            if not re.match(r"^\s*[0-9a-fA-F]+:", line):
                continue
            parts = line.split("\t", 1)
            if len(parts) < 2:
                continue
            inst_str = parts[1].strip()
            if not inst_str or inst_str.startswith("."):
                continue
            mnem = inst_str.split()[0].lower()
            if mnem in ("nop", "hint"):
                continue
            total_insts += 1
            if mnem.startswith("whilel"):
                whilelo_insts += 1
            if re.search(r"\bz\d+\.", inst_str) or re.search(r"\bp\d+/", inst_str) or mnem.startswith(("whilel", "cntw", "cntd", "cntb", "incw", "incd")):
                sve_insts += 1
            elif re.search(r"\bv\d+\.", inst_str) or re.search(r"\bq\d+\b", inst_str):
                neon_insts += 1
            if mnem.startswith(("b", "cbz", "cbnz", "tbz", "tbnz", "ret", "blr", "br")):
                branch_insts += 1
    return {
        "total_insts": total_insts,
        "neon_insts": neon_insts,
        "sve_insts": sve_insts,
        "whilelo_insts": whilelo_insts,
        "branch_insts": branch_insts,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    llvm_objdump = str(bin_dir / "llvm-objdump")
    llvm_size = str(bin_dir / "llvm-size")

    matrix_rows = []
    trip_sweep_rows = []
    aarch64_rows = []
    per_kernel_breakdown = {}
    per_kernel_timings = {}

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src_bin = tmp_path / "bench_main.rs"
        src_bin.write_text(BENCH_KERNELS_RS + "\n" + RUNNER_MAIN_RS, encoding="utf-8")

        base_ns = None
        for cpu in ["x86-64", "x86-64-v2", "x86-64-v3", "x86-64-v4", "native"]:
            for strat_name, strat_flags in STRATEGIES:
                if cpu in ("x86-64", "x86-64-v2") and strat_name != "Default_Unconstrained":
                    continue
                if cpu == "x86-64-v3" and strat_name not in ("Default_Unconstrained", "StratD_InterleaveCap1_NoGather"):
                    continue
                out_bin = tmp_path / f"bin_{cpu}_{strat_name}"
                cmd = [
                    "rustc", f"+{args.toolchain}", "--edition=2021",
                    "--target", "x86_64-unknown-linux-gnu", "-C", "opt-level=3",
                    f"-Ctarget-cpu={cpu}", str(src_bin), "-o", str(out_bin)
                ] + strat_flags
                subprocess.run(cmd, check=True, stderr=subprocess.DEVNULL)
                dis = subprocess.check_output([llvm_objdump, "-d", "-r", "--no-show-raw-insn", str(out_bin)], text=True)
                st = analyze_x86_disasm(dis, KERNEL_NAMES)
                per_kernel_breakdown[f"{cpu}_{strat_name}"] = st["per_kernel"]

                run_out = subprocess.check_output([str(out_bin), "e3_suite"], text=True)
                med_ns = int(re.search(r"MEDIAN_NS=(\d+)", run_out).group(1))
                if base_ns is None:
                    base_ns = med_ns

                pk_out = subprocess.check_output([str(out_bin), "per_kernel"], text=True).strip()
                per_kernel_timings[f"{cpu}_{strat_name}"] = pk_out

                text_sz = 0
                for line in subprocess.check_output([llvm_size, "--format=sysv", str(out_bin)], text=True).splitlines():
                    p = line.split()
                    if len(p) >= 2 and p[0] == ".text":
                        text_sz = int(p[1])

                matrix_rows.append({
                    "target_cpu": cpu,
                    "strategy": strat_name,
                    "kernels_total_insts": st["total_insts"],
                    "simd_insts": st["simd_insts"],
                    "xmm_128_insts": st["xmm_insts"],
                    "ymm_256_insts": st["ymm_insts"],
                    "zmm_512_insts": st["zmm_insts"],
                    "kmask_insts": st["kmask_insts"],
                    "gather_insts": st["gather_insts"],
                    "branch_insts": st["branch_insts"],
                    "binary_text_bytes": text_sz,
                    "e3_suite_median_us": round(med_ns / 1000.0, 2),
                    "speedup_vs_x86_64_base_pct": round((1.0 - med_ns / base_ns) * 100.0, 2),
                })

                if (cpu == "x86-64" and strat_name == "Default_Unconstrained") or (
                    cpu == "x86-64-v3" and strat_name in ("Default_Unconstrained", "StratD_InterleaveCap1_NoGather")
                ) or (
                    cpu == "x86-64-v4"
                ):
                    for trip_n in [4, 8, 12, 16, 24, 32, 48, 64, 128, 256, 1024, 16384]:
                        t_out = subprocess.check_output([str(out_bin), "trip_sweep", str(trip_n)], text=True)
                        ns_per_1k = float(re.search(r"NS_PER_1K=([0-9.]+)", t_out).group(1))
                        trip_sweep_rows.append({
                            "target_cpu": cpu,
                            "strategy": strat_name,
                            "trip_count_n": trip_n,
                            "ns_per_1k_elems": ns_per_1k,
                        })

        # AArch64 NEON vs SVE (neoverse-v1) comparison
        src_lib = tmp_path / "kernels.rs"
        src_lib.write_text("#![no_std]\n" + BENCH_KERNELS_RS, encoding="utf-8")
        for a64_cpu in ["generic", "neoverse-n1", "neoverse-v1", "apple-m1"]:
            for strat_name, strat_flags in [
                ("Default_Unconstrained", []),
                ("StratB_PredicatedTailFold", [
                    "-C", "llvm-args=--tail-folding-policy=prefer-fold-tail",
                    "-C", "llvm-args=--sve-tail-folding=all",
                ]),
                ("StratD_InterleaveCap1", ["-C", "llvm-args=--force-vector-interleave=1"]),
                ("StratE_PredicatedTail_UF1", [
                    "-C", "llvm-args=--tail-folding-policy=prefer-fold-tail",
                    "-C", "llvm-args=--sve-tail-folding=all",
                    "-C", "llvm-args=--force-vector-interleave=1",
                ]),
            ]:
                if a64_cpu != "neoverse-v1" and strat_name != "Default_Unconstrained":
                    continue
                out_obj = tmp_path / f"obj_a64_{a64_cpu}_{strat_name}.o"
                cmd = [
                    "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                    "--target", "aarch64-unknown-linux-gnu", "-C", "opt-level=3",
                    f"-Ctarget-cpu={a64_cpu}", "--emit=obj", str(src_lib), "-o", str(out_obj)
                ] + strat_flags
                subprocess.run(cmd, check=True, stderr=subprocess.DEVNULL)
                dis = subprocess.check_output([llvm_objdump, "-d", "-r", "--no-show-raw-insn", str(out_obj)], text=True)
                st = analyze_aarch64_disasm(dis, KERNEL_NAMES)
                text_sz = 0
                for line in subprocess.check_output([llvm_size, "--format=sysv", str(out_obj)], text=True).splitlines():
                    p = line.split()
                    if len(p) >= 2 and p[0].startswith(".text"):
                        text_sz += int(p[1])
                aarch64_rows.append({
                    "target": "aarch64-unknown-linux-gnu",
                    "target_cpu": a64_cpu,
                    "strategy": strat_name,
                    "kernels_total_insts": st["total_insts"],
                    "neon_insts": st["neon_insts"],
                    "sve_insts": st["sve_insts"],
                    "whilelo_insts": st["whilelo_insts"],
                    "branch_insts": st["branch_insts"],
                    "object_text_bytes": text_sz,
                })

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "avx512_policy_matrix.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(matrix_rows[0].keys()))
        w.writeheader()
        w.writerows(matrix_rows)

    trip_csv = args.out_dir / "avx512_trip_count_sweep.csv"
    with open(trip_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["target_cpu", "strategy", "trip_count_n", "ns_per_1k_elems"])
        w.writeheader()
        w.writerows(trip_sweep_rows)

    json_path = args.out_dir / "avx512_and_sve_analysis.json"
    json_path.write_text(json.dumps({
        "toolchain": args.toolchain,
        "rust_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "per_kernel_timings_us": per_kernel_timings,
        "per_kernel_breakdown_8_kernels": per_kernel_breakdown,
        "aarch64_neon_vs_sve_strategies": aarch64_rows,
    }, indent=2) + "\n", encoding="utf-8")

    print(f"Wrote {csv_path} ({len(matrix_rows)} rows), {trip_csv} ({len(trip_sweep_rows)} rows), and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
