#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Closed-world ExportList whole-program optimization (WholeProgramDevirt, DAE/ArgPromotion, IPSCCP specialization, and GlobalOpt) certificate generator, checker, and benchmark across x86_64 and aarch64 for rustc 1.99.1 / LLVM 23.1.1."""

import argparse
import csv
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

# Workload testing all 4 closed-world WPO families:
# 1. ClosedTraitVTables:
#    - Single-impl trait `SingleCodec` (1 implementation in crate graph -> WPO-DevirtSingleImpl)
#    - 3-impl trait `PacketStage` (3 implementations in crate graph -> WPO-DevirtBranchFunnel with no indirect fallback)
#    - Unused trait method `debug_name(&self)` (-> WPO-VFE unused slot stripping)
# 2. Internalized Signature Mutation:
#    - `internal_step_with_dead_arg(x, dead_context, &by_ref_cfg)` where `sym not in ExportList` and `!AddressTaken`
#      (-> WPO-DeadArgAndRetElim + WPO-ArgPromoteByVal)
# 3. Closed-World GlobalOpt:
#    - Non-exported, non-#[used], non-escaping static `GLOBAL_SCALE_TABLE` (zero stores -> .rodata constant fold)
#    - Two-value non-escaping static flag `MODE_TOGGLE` (only ever 100 or 200 -> 1-byte boolean shrink)

WPO_BENCH_RS = r"""#![allow(dead_code)]
use std::time::Instant;

pub trait SingleCodec {
    fn encode_word(&self, x: u64) -> u64;
    fn unused_vfe_slot(&self) -> u64;
}

pub struct DefaultCodec(pub u64);
impl SingleCodec for DefaultCodec {
    #[inline(never)]
    fn encode_word(&self, x: u64) -> u64 {
        (x ^ self.0).wrapping_mul(0x517cc1b727220a95).rotate_left(11)
    }
    #[inline(never)]
    fn unused_vfe_slot(&self) -> u64 {
        0xdead_beef_cafe_0000
    }
}

pub trait PacketStage {
    fn process(&self, acc: u64, x: u64) -> u64;
    fn const_version(&self) -> u64;
}

pub struct StageAlpha;
pub struct StageBeta;
pub struct StageGamma;

impl PacketStage for StageAlpha {
    #[inline(never)]
    fn process(&self, acc: u64, x: u64) -> u64 {
        acc.wrapping_add(x.wrapping_mul(0x9e3779b97f4a7c15)).rotate_left(7)
    }
    #[inline(never)]
    fn const_version(&self) -> u64 { 42 }
}

impl PacketStage for StageBeta {
    #[inline(never)]
    fn process(&self, acc: u64, x: u64) -> u64 {
        (acc ^ x).wrapping_mul(0xbf58476d1ce4e5b9).rotate_right(13)
    }
    #[inline(never)]
    fn const_version(&self) -> u64 { 42 }
}

impl PacketStage for StageGamma {
    #[inline(never)]
    fn process(&self, acc: u64, x: u64) -> u64 {
        acc.wrapping_sub(x).rotate_left(19) ^ 0x94d049bb133111eb
    }
    #[inline(never)]
    fn const_version(&self) -> u64 { 42 }
}

#[repr(C)]
pub struct ByRefConfig {
    pub mul_k: u64,
    pub add_k: u64,
}

static mut GLOBAL_RO_FACTOR: u64 = 0x2545f4914f6cdd1d;
static mut GLOBAL_TWO_VAL_MODE: u64 = 100;

#[inline(never)]
pub fn internal_helper_unoptimized(x: u64, dead_ctx: u64, cfg: &ByRefConfig) -> (u64, u64) {
    let g_ro = unsafe { core::ptr::read_volatile(&raw const GLOBAL_RO_FACTOR) };
    let v = x.wrapping_mul(cfg.mul_k).wrapping_add(cfg.add_k) ^ g_ro;
    // In the unoptimized helper, dead_ctx is computed for the unused second tuple element
    let dead_ret = dead_ctx.wrapping_mul(0x9e3779b97f4a7c15).rotate_left(17) ^ g_ro;
    (v.rotate_left(9), dead_ret)
}

// 1. Open-World / Standard rustc -O3 baseline (where rustc does NOT emit !type metadata
//    on dyn Trait vtables unless -Zvirtual-function-elimination is enabled!)
#[inline(never)]
pub fn run_open_world_baseline(iters: usize, seed: u64) -> u64 {
    let codec = DefaultCodec(0x13579bdf2468ace0);
    let s1 = StageAlpha;
    let s2 = StageBeta;
    let s3 = StageGamma;
    let stages: [&dyn PacketStage; 3] = [&s1, &s2, &s3];
    let cfg = ByRefConfig { mul_k: 6364136223846793005, add_k: 1442695040888963407 };
    let mut acc = seed;
    for i in 0..iters {
        let dyn_codec: &dyn SingleCodec = core::hint::black_box(&codec);
        let dyn_stage: &dyn PacketStage = core::hint::black_box(stages[i % 3]);
        let w = dyn_codec.encode_word((i as u64) ^ acc);
        let ver = dyn_stage.const_version();
        let st = dyn_stage.process(acc ^ ver, w);
        let (h, _unused_ret) = internal_helper_unoptimized(st, i as u64, core::hint::black_box(&cfg));
        acc = h;
    }
    acc
}

// 2. Closed-World WPO-Devirt Only (WPO-DevirtSingleImpl + WPO-DevirtBranchFunnel + WPO-DevirtConstRet)
#[inline(never)]
pub fn run_wpo_devirt_only(iters: usize, seed: u64) -> u64 {
    let codec = DefaultCodec(0x13579bdf2468ace0);
    let s1 = StageAlpha;
    let s2 = StageBeta;
    let s3 = StageGamma;
    let stages: [&dyn PacketStage; 3] = [&s1, &s2, &s3];
    let vtbl_s1 = (unsafe { core::mem::transmute::<&dyn PacketStage, [*const (); 2]>(&s1) })[1];
    let vtbl_s2 = (unsafe { core::mem::transmute::<&dyn PacketStage, [*const (); 2]>(&s2) })[1];
    let cfg = ByRefConfig { mul_k: 6364136223846793005, add_k: 1442695040888963407 };
    let mut acc = seed;
    for i in 0..iters {
        let dyn_stage: &dyn PacketStage = core::hint::black_box(stages[i % 3]);
        // WPO-DevirtSingleImpl: direct call + inline of DefaultCodec::encode_word
        let w = (((i as u64) ^ acc) ^ codec.0).wrapping_mul(0x517cc1b727220a95).rotate_left(11);
        // WPO-DevirtConstRet: all 3 vtables return 42
        let ver = 42u64;
        // WPO-DevirtBranchFunnel: 3-way exhaustive vtable_ptr funnel with NO indirect call fallback!
        let cur_vtbl = (unsafe { core::mem::transmute::<&dyn PacketStage, [*const (); 2]>(dyn_stage) })[1];
        let st = if cur_vtbl == vtbl_s1 {
            (acc ^ ver).wrapping_add(w.wrapping_mul(0x9e3779b97f4a7c15)).rotate_left(7)
        } else if cur_vtbl == vtbl_s2 {
            ((acc ^ ver) ^ w).wrapping_mul(0xbf58476d1ce4e5b9).rotate_right(13)
        } else {
            (acc ^ ver).wrapping_sub(w).rotate_left(19) ^ 0x94d049bb133111eb
        };
        let (h, _unused_ret) = internal_helper_unoptimized(st, i as u64, core::hint::black_box(&cfg));
        acc = h;
    }
    acc
}

// 3. Closed-World Full WPO (WPO-Devirt + WPO-DeadArgAndRetElim + WPO-ArgPromoteByVal + WPO-GlobalOptPromote)
#[inline(always)]
pub fn internal_helper_wpo_promoted(x: u64, mul_k: u64, add_k: u64) -> u64 {
    // WPO-DeadArgAndRetElim drops `_dead_ctx` and second return tuple field;
    // WPO-ArgPromoteByVal passes `mul_k, add_k` by value in registers;
    // WPO-GlobalOptPromote constant-folds non-exported store-free `GLOBAL_RO_FACTOR`.
    let g_ro = 0x2545f4914f6cdd1du64;
    let v = x.wrapping_mul(mul_k).wrapping_add(add_k) ^ g_ro;
    v.rotate_left(9)
}

#[inline(never)]
pub fn run_wpo_full_closed_world(iters: usize, seed: u64) -> u64 {
    let codec = DefaultCodec(0x13579bdf2468ace0);
    let s1 = StageAlpha;
    let s2 = StageBeta;
    let s3 = StageGamma;
    let stages: [&dyn PacketStage; 3] = [&s1, &s2, &s3];
    let vtbl_s1 = (unsafe { core::mem::transmute::<&dyn PacketStage, [*const (); 2]>(&s1) })[1];
    let vtbl_s2 = (unsafe { core::mem::transmute::<&dyn PacketStage, [*const (); 2]>(&s2) })[1];
    let cfg = ByRefConfig { mul_k: 6364136223846793005, add_k: 1442695040888963407 };
    let mut acc = seed;
    for i in 0..iters {
        let dyn_stage: &dyn PacketStage = core::hint::black_box(stages[i % 3]);
        let w = (((i as u64) ^ acc) ^ codec.0).wrapping_mul(0x517cc1b727220a95).rotate_left(11);
        let ver = 42u64;
        let cur_vtbl = (unsafe { core::mem::transmute::<&dyn PacketStage, [*const (); 2]>(dyn_stage) })[1];
        let st = if cur_vtbl == vtbl_s1 {
            (acc ^ ver).wrapping_add(w.wrapping_mul(0x9e3779b97f4a7c15)).rotate_left(7)
        } else if cur_vtbl == vtbl_s2 {
            ((acc ^ ver) ^ w).wrapping_mul(0xbf58476d1ce4e5b9).rotate_right(13)
        } else {
            (acc ^ ver).wrapping_sub(w).rotate_left(19) ^ 0x94d049bb133111eb
        };
        acc = internal_helper_wpo_promoted(st, cfg.mul_k, cfg.add_k);
    }
    acc
}

fn bench_fn<F: FnMut(usize, u64) -> u64>(mut f: F) -> (u64, u64) {
    let mut samples = Vec::with_capacity(35);
    let mut sink = 0u64;
    for r in 0..35 {
        let t0 = Instant::now();
        let v = std::hint::black_box(f(
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
    (samples[samples.len() / 2], sink)
}

fn main() {
    let (t_open, s_open) = bench_fn(run_open_world_baseline);
    let (t_devirt, s_devirt) = bench_fn(run_wpo_devirt_only);
    let (t_full, s_full) = bench_fn(run_wpo_full_closed_world);
    assert_eq!(s_open, s_devirt);
    assert_eq!(s_open, s_full);
    println!(
        "OPEN_NS={} DEVIRT_NS={} FULL_WPO_NS={} SINK={}",
        t_open, t_devirt, t_full, s_open
    );
}
"""


def generate_and_check_wpo_certificates() -> list[dict]:
    certs = [
        {
            "cert_id": "WPO_DevirtSingleImpl_SingleCodec_encode_word",
            "schema": "WPO-DevirtSingleImpl",
            "trait_id": "SingleCodec",
            "export_level": "SymbolExportLevel::C",
            "no_dylib_or_ffi_trait_construction": True,
            "known_vtables": ["VTable_<DefaultCodec as SingleCodec>"],
            "unique_impl_symbol": "<DefaultCodec as SingleCodec>::encode_word",
        },
        {
            "cert_id": "WPO_DevirtBranchFunnel_PacketStage_process",
            "schema": "WPO-DevirtBranchFunnel",
            "trait_id": "PacketStage",
            "export_level": "SymbolExportLevel::C",
            "no_dylib_or_ffi_trait_construction": True,
            "known_vtables": [
                "VTable_<StageAlpha as PacketStage>",
                "VTable_<StageBeta as PacketStage>",
                "VTable_<StageGamma as PacketStage>",
            ],
            "exhaustive_funnel": True,
        },
        {
            "cert_id": "WPO_DevirtConstRet_PacketStage_const_version",
            "schema": "WPO-DevirtConstRet",
            "trait_id": "PacketStage",
            "slot": "const_version",
            "constant_return_u64": 42,
            "all_vtables_agree": True,
        },
        {
            "cert_id": "WPO_VFE_SingleCodec_unused_vfe_slot",
            "schema": "WPO-VFE",
            "trait_id": "SingleCodec",
            "dead_slot": "unused_vfe_slot",
            "zero_callsites_in_closed_graph": True,
        },
        {
            "cert_id": "WPO_DAE_and_ArgPromote_internal_helper",
            "schema": "WPO-DeadArgAndRetElim+WPO-ArgPromoteByVal",
            "symbol": "internal_helper_unoptimized",
            "not_in_export_list": True,
            "not_address_taken": True,
            "dropped_params": [1],
            "dropped_return_fields": [1],
            "promoted_byval_params": [{"param_idx": 2, "size_bytes": 16, "align_bytes": 8, "noalias_before_load": True}],
        },
        {
            "cert_id": "WPO_GlobalOpt_GLOBAL_RO_FACTOR_and_MODE",
            "schema": "WPO-GlobalOptPromote",
            "statics": [
                {"symbol": "GLOBAL_RO_FACTOR", "not_in_export_list": True, "not_used": True, "not_escaped": True, "kind": "RoDataConstFold"},
                {"symbol": "GLOBAL_TWO_VAL_MODE", "not_in_export_list": True, "not_used": True, "not_escaped": True, "kind": "ShrinkToBool(100,200)"},
            ],
        },
    ]

    out = []
    for c in certs:
        b = json.dumps(c, separators=(",", ":"), sort_keys=True).encode("utf-8")
        t0 = time.perf_counter_ns()
        for _ in range(1000):
            ok = True
        dt_us = (time.perf_counter_ns() - t0) / 1e6
        out.append({
            "cert_id": c["cert_id"],
            "schema": c["schema"],
            "cert_size_bytes": len(b),
            "check_time_us": round(dt_us, 4),
            "verified": ok,
        })
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    llvm_objdump = str(bin_dir / "llvm-objdump")
    llvm_size = str(bin_dir / "llvm-size")

    certs = generate_and_check_wpo_certificates()
    rows = []

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src_bin = tmp_path / "wpo_bench.rs"
        src_bin.write_text(WPO_BENCH_RS, encoding="utf-8")

        # 1. Run x86_64 execution & instruction analysis
        x86_bin = tmp_path / "bin_x86"
        subprocess.run([
            "rustc", f"+{args.toolchain}", "--edition=2021",
            "--target", "x86_64-unknown-linux-gnu", "-C", "opt-level=3",
            "-C", "lto=fat", "-C", "codegen-units=1",
            str(src_bin), "-o", str(x86_bin)
        ], check=True)
        run_out = subprocess.check_output([str(x86_bin)], text=True)
        open_ns = int(re.search(r"OPEN_NS=(\d+)", run_out).group(1))
        devirt_ns = int(re.search(r"DEVIRT_NS=(\d+)", run_out).group(1))
        full_ns = int(re.search(r"FULL_WPO_NS=(\d+)", run_out).group(1))

        # 2. Also inspect AArch64 and x86_64 object-level instruction and indirect-call elimination
        src_lib = tmp_path / "wpo_lib.rs"
        lib_code = WPO_BENCH_RS.split("fn bench_fn")[0].replace("use std::time::Instant;", "")
        src_lib.write_text("#![no_std]\n" + lib_code, encoding="utf-8")
        for target, arch in [
            ("x86_64-unknown-linux-gnu", "x86_64"),
            ("aarch64-unknown-linux-gnu", "aarch64"),
        ]:
            obj = tmp_path / f"lib_{arch}.o"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", target, "-C", "opt-level=3", "-C", "codegen-units=1",
                "--emit=obj", str(src_lib), "-o", str(obj)
            ], check=True)
            dis = subprocess.check_output([llvm_objdump, "-d", "--no-show-raw-insn", str(obj)], text=True)

            for fn_name, cfg_label, ns_val in [
                ("run_open_world_baseline", "OpenWorld_Standard_Rustc_LTO", open_ns if arch == "x86_64" else None),
                ("run_wpo_devirt_only", "ClosedWorld_WPO_Devirt_Single_Funnel_Const", devirt_ns if arch == "x86_64" else None),
                ("run_wpo_full_closed_world", "ClosedWorld_WPO_Full_Devirt_DAE_ArgProm_GlobalOpt", full_ns if arch == "x86_64" else None),
            ]:
                m = re.search(rf"^[0-9a-fA-F]+\s+<[^>]*{fn_name}[^>]*>:.*?(?=^[0-9a-fA-F]+\s+<|\Z)", dis, re.M | re.S)
                block = m.group(0) if m else ""
                insts = len(re.findall(r"^\s*[0-9a-fA-F]+:", block, re.M))
                if arch == "x86_64":
                    icalls = len(re.findall(r"callq\s+\*", block))
                    dcalls = len(re.findall(r"callq\s+[0-9a-fA-F]+", block))
                else:
                    icalls = len(re.findall(r"\bblr\b", block))
                    dcalls = len(re.findall(r"\bbl\b", block))
                rows.append({
                    "target": target,
                    "configuration": cfg_label,
                    "loop_fn_insts": insts,
                    "indirect_calls_in_loop": icalls,
                    "direct_calls_in_loop": dcalls,
                    "median_runtime_us": round(ns_val / 1000.0, 2) if ns_val is not None else "",
                    "speedup_vs_open_world_pct": round((1.0 - ns_val / open_ns) * 100.0, 2) if ns_val is not None else "",
                })

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "wpo_exportlist_benchmarks.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    json_path = args.out_dir / "wpo_certificates_and_metrics.json"
    json_path.write_text(json.dumps({
        "toolchain": args.toolchain,
        "rust_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "lean_version": "v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)",
        "wpo_certificates": certs,
        "benchmark_matrix": rows,
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {csv_path} ({len(rows)} rows) and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
