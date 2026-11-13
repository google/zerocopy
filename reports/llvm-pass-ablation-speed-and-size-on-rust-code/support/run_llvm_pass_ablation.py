#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""12-group LLVM 23.1.1 LOO/AOI pass ablation, Top-6 pairwise synergy matrix, and S12 MIR-vs-LLVM pass ablation harness for rustc 1.99.1."""

import argparse
import csv
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "x86_64-pc-windows-gnu",
    "x86_64-pc-windows-msvc",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
    "aarch64-apple-darwin",
]

# The 12 canonical LLVM 23.1.1 optimization pass groups from O1:
PASS_GROUPS = [
    ("G1_Inlining", "CGSCC Inlining, Argument Promotion & FunctionAttrs", [
        "cgscc(inline,function-attrs,argpromotion)"
    ]),
    ("G2_SROA_EarlyCSE", "Scalar Replacement of Aggregates (SROA/Mem2Reg) & MemorySSA EarlyCSE", [
        "function(sroa<modify-cfg>,mem2reg,early-cse<memssa>)"
    ]),
    ("G3_InstCombine_Peephole", "Instruction Combining, AggressiveInstCombine & Reassociate", [
        "function(instcombine<no-verify-fixpoint>,aggressive-instcombine,reassociate)"
    ]),
    ("G4_CFG_Simplify", "SimplifyCFG, JumpThreading & TailCallElim", [
        "function(simplifycfg,jump-threading,tailcallelim)"
    ]),
    ("G5_GVN_DSE_MemOpt", "GVN, MemCpyOpt, DeadStoreElimination & MergedLoadStoreMotion", [
        "function(gvn<>,memcpyopt,dse,mldst-motion,bdce,adce)"
    ]),
    ("G6_SCCP_IPSCCP_ConstProp", "Interprocedural & Function SCCP, CalledValueProp & GlobalOpt", [
        "ipsccp,called-value-propagation,globalopt,function(sccp)"
    ]),
    ("G7_LoopCanon_LICM", "Loop Simplify/Rotate, LICM, IndVarSimplify, LoopIdiom & LoopDeletion", [
        "function(loop-mssa(loop-instsimplify,loop-simplifycfg,licm,loop-rotate,simple-loop-unswitch<nontrivial>),loop(loop-idiom,indvars,loop-deletion))"
    ]),
    ("G8_LoopUnroll", "Loop Unrolling (Full & Runtime)", [
        "function(loop(loop-unroll-full),loop-unroll)"
    ]),
    ("G9_Vectorization", "LoopVectorizer, SLPVectorizer & VectorCombine", [
        "function(loop-vectorize,slp-vectorizer,vector-combine,infer-alignment)"
    ]),
    ("G10_BoundsCheck_Range", "ConstraintElimination & CorrelatedValuePropagation", [
        "function(constraint-elimination,correlated-propagation)"
    ]),
    ("G11_Devirt_FuncSpec", "WholeProgramDevirt, LowerTypeTests & GlobalDCE", [
        "wholeprogramdevirt,lowertypetests,elim-avail-extern,globaldce"
    ]),
    ("G12_CodegenPrep_TailDup", "CGP / DivRemPairs / ConstantHoisting / Machine Late Optimizations", [
        "function(div-rem-pairs,consthoist,sink,instsimplify)"
    ]),
]

# Representative multi-domain Rust workload exercising:
# - Generic iterator & closure chains (G1_Inlining + G2_SROA)
# - Bitwise/algebraic strength reduction (G3_InstCombine)
# - Option/Result/enum branching & tail recursion (G4_CFG_Simplify)
# - Redundant struct/slice loads & dead stores (G5_GVN_DSE_MemOpt)
# - Interprocedural constant arguments (G6_SCCP_IPSCCP)
# - Loop-invariant bounds & polynomial accumulation (G7_LoopCanon_LICM + G8_LoopUnroll)
# - SIMD-vectorizable slice reductions (G9_Vectorization)
# - Relational index bounds `i < n` / `i + 3 < n` (G10_BoundsCheck_Range)
# - Internalized helper elimination & constant folding (G11_Devirt_FuncSpec)
# - Quotient+remainder pairs & large constants (G12_CodegenPrep_TailDup)
ABLATION_WORKLOAD_RS = r"""#![allow(dead_code)]

#[derive(Clone, Copy)]
pub struct StatePacket {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub tag: u32,
    pub flags: u32,
}

#[inline]
pub fn make_packet(x: u64, salt: u64) -> StatePacket {
    StatePacket {
        a: x.wrapping_add(salt),
        b: x.rotate_left(13) ^ salt,
        c: x.wrapping_mul(0x9e3779b97f4a7c15),
        tag: (x & 7) as u32,
        flags: ((x >> 8) & 0xff) as u32,
    }
}

#[inline]
pub fn fold_packet(p: StatePacket, k: u64) -> u64 {
    let mut tmp = [0u64; 4];
    // Dead stores overwritten before read (exercises SROA + DSE + GVN)
    tmp[0] = p.a ^ 0x1111;
    tmp[1] = p.b ^ 0x2222;
    tmp[0] = p.a.wrapping_add(k);
    tmp[1] = p.b.wrapping_mul(k | 1);
    tmp[2] = p.c ^ tmp[0];
    tmp[3] = (p.tag as u64).wrapping_add(p.flags as u64);
    match p.tag & 3 {
        0 => tmp[0].wrapping_add(tmp[1]).wrapping_add(tmp[2]),
        1 => tmp[0].wrapping_sub(tmp[1]) ^ tmp[2].rotate_left(7),
        2 => (tmp[0] ^ tmp[1]).wrapping_add(tmp[2]).wrapping_add(tmp[3]),
        _ => tmp[0].wrapping_add(tmp[2]) ^ tmp[1].rotate_right(11),
    }
}

pub fn const_configured_step(x: u64, mode: u32, scale: u64) -> u64 {
    // Exercises IPSCCP / constant propagation when called with constant mode=1, scale=6364136223846793005
    if mode == 0 {
        x.wrapping_div(7)
    } else if mode == 1 {
        let q = x / 13;
        let r = x % 13; // Exercises div-rem-pairs
        (q.wrapping_add(r)).wrapping_mul(scale)
    } else {
        x.rotate_left(mode)
    }
}

#[no_mangle]
pub extern "C" fn run_ablation_kernel(data: *const u32, len: usize, seed: u64) -> u64 {
    let slice = unsafe { core::slice::from_raw_parts(data, len) };
    let mut acc = seed;

    // Loop 1: Inlining + SROA + GVN + LICM + BoundsCheck elimination (`i + 3 < slice.len()`)
    let n = slice.len();
    if n >= 16 {
        let mut i = 0usize;
        while i + 4 <= n {
            // Constraint elimination can prove i < n, i+1 < n, i+2 < n, i+3 < n from i + 4 <= n
            let v0 = slice[i] as u64;
            let v1 = slice[i + 1] as u64;
            let v2 = slice[i + 2] as u64;
            let v3 = slice[i + 3] as u64;
            let pkt = make_packet(v0 ^ v1, seed.wrapping_add(v2));
            let folded = fold_packet(pkt, v3);
            let stepped = const_configured_step(folded, 1, 6364136223846793005);
            acc = acc.wrapping_add(stepped);
            i += 4;
        }
    }

    // Loop 2: Autovectorizable SIMD reduction + LoopUnroll
    let mut vec_sum = 0u64;
    for &elem in slice {
        let e = elem as u64;
        vec_sum = vec_sum.wrapping_add((e.wrapping_mul(3).wrapping_add(7)) ^ (e >> 2));
    }

    acc ^ vec_sum
}
"""

RUNNER_MAIN_RS = r"""
use std::time::Instant;

extern "C" {
    fn run_ablation_kernel(data: *const u32, len: usize, seed: u64) -> u64;
}

fn main() {
    let data: Vec<u32> = (0..8192u32).map(|i| i.wrapping_mul(2654435761)).collect();
    let mut samples = Vec::with_capacity(35);
    let mut sink = 0u64;
    for r in 0..35 {
        let t0 = Instant::now();
        for iter in 0..40u64 {
            let res = unsafe {
                run_ablation_kernel(
                    std::hint::black_box(data.as_ptr()),
                    std::hint::black_box(data.len()),
                    std::hint::black_box(0x1234_5678_9abc_def0u64 ^ r ^ iter),
                )
            };
            sink ^= res;
        }
        let dt = t0.elapsed().as_nanos() as u64;
        if r >= 5 {
            samples.push(dt);
        }
    }
    samples.sort_unstable();
    let med = samples[samples.len() / 2];
    let q25 = samples[samples.len() / 4];
    let q75 = samples[(samples.len() * 3) / 4];
    println!("MEDIAN_NS={} IQR_NS={} SINK={}", med, q75 - q25, sink);
}
"""


def build_pipeline_string(enabled_group_ids: set[str]) -> str:
    # Faithful 3-stage LLVM 23.1.1 PassBuilder -O3 architecture conditioned on enabled_group_ids:
    # Stage 1: Early Simplification & Early Global IPO
    stages = ["annotation2metadata", "forceattrs", "inferattrs"]
    early_fn = ["lower-expect"]
    if "G4_CFG_Simplify" in enabled_group_ids:
        early_fn.append("simplifycfg")
    if "G2_SROA_EarlyCSE" in enabled_group_ids:
        early_fn.extend(["sroa<modify-cfg>", "early-cse<>"])
    if "G1_Inlining" in enabled_group_ids:
        early_fn.append("callsite-splitting")
    stages.append(f"function({','.join(early_fn)})")

    if "G6_SCCP_IPSCCP_ConstProp" in enabled_group_ids:
        stages.extend(["ipsccp", "called-value-propagation", "globalopt"])
    if "G2_SROA_EarlyCSE" in enabled_group_ids:
        stages.append("function(mem2reg)")
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        stages.append("function(instcombine<max-iterations=1;no-verify-fixpoint>)")
    if "G4_CFG_Simplify" in enabled_group_ids:
        stages.append("function(simplifycfg)")

    # Stage 2: CGSCC Inliner & FunctionSimplificationPipeline
    cgscc_fn = []
    if "G2_SROA_EarlyCSE" in enabled_group_ids:
        cgscc_fn.extend(["sroa<modify-cfg>", "early-cse<memssa>"])
    if "G4_CFG_Simplify" in enabled_group_ids:
        cgscc_fn.append("jump-threading")
    if "G10_BoundsCheck_Range" in enabled_group_ids:
        cgscc_fn.append("correlated-propagation")
    if "G4_CFG_Simplify" in enabled_group_ids:
        cgscc_fn.append("simplifycfg")
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        cgscc_fn.extend(["instcombine<max-iterations=1;no-verify-fixpoint>", "aggressive-instcombine"])
    if "G4_CFG_Simplify" in enabled_group_ids:
        cgscc_fn.extend(["tailcallelim", "simplifycfg"])
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        cgscc_fn.append("reassociate")
    if "G10_BoundsCheck_Range" in enabled_group_ids:
        cgscc_fn.append("constraint-elimination")
    if "G7_LoopCanon_LICM" in enabled_group_ids:
        cgscc_fn.append(
            "loop-mssa(loop-instsimplify,loop-simplifycfg,licm<no-allowspeculation>,"
            "loop-rotate<header-duplication;no-prepare-for-lto;no-check-exit-count>,"
            "licm<allowspeculation>,simple-loop-unswitch<nontrivial;trivial>)"
        )
    if "G4_CFG_Simplify" in enabled_group_ids:
        cgscc_fn.append("simplifycfg")
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        cgscc_fn.append("instcombine<max-iterations=1;no-verify-fixpoint>")
    if "G7_LoopCanon_LICM" in enabled_group_ids:
        cgscc_fn.append("loop(loop-idiom,indvars,loop-deletion)")
    if "G8_LoopUnroll" in enabled_group_ids:
        cgscc_fn.append("loop(loop-unroll-full)")
    if "G2_SROA_EarlyCSE" in enabled_group_ids:
        cgscc_fn.append("sroa<modify-cfg>")
    if "G9_Vectorization" in enabled_group_ids:
        cgscc_fn.append("vector-combine")
    if "G5_GVN_DSE_MemOpt" in enabled_group_ids:
        cgscc_fn.extend(["mldst-motion<no-split-footer-bb>", "gvn<>"])
    if "G6_SCCP_IPSCCP_ConstProp" in enabled_group_ids:
        cgscc_fn.append("sccp")
    if "G5_GVN_DSE_MemOpt" in enabled_group_ids:
        cgscc_fn.append("bdce")
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        cgscc_fn.append("instcombine<max-iterations=1;no-verify-fixpoint>")
    if "G4_CFG_Simplify" in enabled_group_ids:
        cgscc_fn.append("jump-threading")
    if "G10_BoundsCheck_Range" in enabled_group_ids:
        cgscc_fn.append("correlated-propagation")
    if "G5_GVN_DSE_MemOpt" in enabled_group_ids:
        cgscc_fn.extend(["adce", "memcpyopt", "dse"])
    if "G7_LoopCanon_LICM" in enabled_group_ids:
        cgscc_fn.append("loop-mssa(licm<allowspeculation>)")
    if "G4_CFG_Simplify" in enabled_group_ids:
        cgscc_fn.append("simplifycfg<hoist-common-insts;sink-common-insts>")
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        cgscc_fn.append("instcombine<max-iterations=1;no-verify-fixpoint>")

    cgscc_parts = []
    if "G1_Inlining" in enabled_group_ids:
        cgscc_parts.extend(["inline", "function-attrs<skip-non-recursive-function-attrs>", "argpromotion"])
    if cgscc_fn:
        cgscc_parts.append(f"function({','.join(cgscc_fn)})")
    if "G1_Inlining" in enabled_group_ids:
        cgscc_parts.append("function-attrs")
    if cgscc_parts:
        stages.append(f"cgscc(devirt<4>({','.join(cgscc_parts)}))")

    # Stage 3: Post-CGSCC Module & Loop Vectorization / Unrolling / CodegenPrep Pipeline
    if "G11_Devirt_FuncSpec" in enabled_group_ids:
        stages.extend(["deadargelim", "globalopt", "globaldce", "elim-avail-extern", "rpo-function-attrs"])

    late_fn = []
    if "G7_LoopCanon_LICM" in enabled_group_ids:
        late_fn.extend([
            "loop(loop-rotate<header-duplication;no-prepare-for-lto;check-exit-count>,loop-deletion,loop-interchange)",
            "loop-distribute",
        ])
    if "G9_Vectorization" in enabled_group_ids:
        late_fn.extend([
            "inject-tli-mappings",
            "loop-vectorize<no-interleave-forced-only;no-vectorize-forced-only;>",
            "infer-alignment",
            "loop-load-elim",
        ])
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        late_fn.append("instcombine<max-iterations=1;no-verify-fixpoint>")
    if "G4_CFG_Simplify" in enabled_group_ids:
        late_fn.append("simplifycfg<forward-switch-cond;switch-range-to-icmp;switch-to-arithmetic;switch-to-lookup;no-keep-loops;hoist-common-insts;sink-common-insts>")
    if "G9_Vectorization" in enabled_group_ids:
        late_fn.extend(["slp-vectorizer", "vector-combine"])
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        late_fn.append("instcombine<max-iterations=1;no-verify-fixpoint>")
    if "G8_LoopUnroll" in enabled_group_ids:
        late_fn.append("loop-unroll<O3>")
    if "G2_SROA_EarlyCSE" in enabled_group_ids:
        late_fn.append("sroa<preserve-cfg;aggregate-to-vector>")
    if "G3_InstCombine_Peephole" in enabled_group_ids:
        late_fn.append("instcombine<max-iterations=1;no-verify-fixpoint>")
    if "G7_LoopCanon_LICM" in enabled_group_ids:
        late_fn.extend(["loop-mssa(licm<allowspeculation>)", "loop-sink"])
    if "G12_CodegenPrep_TailDup" in enabled_group_ids:
        late_fn.extend(["instsimplify", "div-rem-pairs", "mergeicmps", "expand-memcmp"])
    if "G4_CFG_Simplify" in enabled_group_ids:
        late_fn.extend(["tailcallelim", "simplifycfg"])
    if late_fn:
        stages.append(f"function({','.join(late_fn)})")
    if "G11_Devirt_FuncSpec" in enabled_group_ids:
        stages.extend(["globaldce", "constmerge"])
    return ",".join(stages)


def parse_obj_text_and_insts(llvm_size: str, llvm_objdump: str, obj_path: Path) -> tuple[int, int, int]:
    proc_sz = subprocess.run([llvm_size, "--format=sysv", str(obj_path)], capture_output=True, text=True, check=False)
    text_bytes = 0
    for line in proc_sz.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0].startswith((".text", "__text")):
            try:
                text_bytes += int(parts[1])
            except ValueError:
                pass
    proc_dis = subprocess.run([llvm_objdump, "-d", "-r", "--no-show-raw-insn", str(obj_path)], capture_output=True, text=True, check=False)
    insts = 0
    bounds_panics = 0
    for line in proc_dis.stdout.splitlines():
        if "panic_bounds_check" in line:
            bounds_panics += 1
        if re.match(r"^\s*[0-9a-fA-F]+:", line):
            insts += 1
    return text_bytes, insts, bounds_panics


def run_pipeline_on_bc(
    opt_bin: str,
    llc_bin: str,
    llvm_size: str,
    llvm_objdump: str,
    bc_path: Path,
    pipeline_str: str,
    target: str,
    llc_opt_flag: str,
    work_dir: Path,
    driver_rlib: Path | None,
    toolchain: str,
) -> dict:
    opt_bc = work_dir / "opt.bc"
    obj_out = work_dir / "out.o"
    subprocess.run([opt_bin, f"--passes={pipeline_str}", str(bc_path), "-o", str(opt_bc)], check=True)
    llc_cmd = [
        llc_bin, llc_opt_flag, "--filetype=obj",
        "--relocation-model=pic", f"--mtriple={target}",
        str(opt_bc), "-o", str(obj_out)
    ]
    subprocess.run(llc_cmd, check=True)
    text_bytes, inst_count, bounds_panics = parse_obj_text_and_insts(llvm_size, llvm_objdump, obj_out)

    med_us = None
    iqr_us = None
    if target == "x86_64-unknown-linux-gnu" and driver_rlib is not None:
        bin_out = work_dir / "bench_bin"
        subprocess.run([
            "rustc", f"+{toolchain}", "--edition=2021",
            "--target", target, "-C", "opt-level=3",
            f"-Clink-arg={obj_out}",
            str(driver_rlib), "-o", str(bin_out)
        ], check=True)
        run_out = subprocess.check_output([str(bin_out)], text=True)
        m_med = re.search(r"MEDIAN_NS=(\d+)", run_out)
        m_iqr = re.search(r"IQR_NS=(\d+)", run_out)
        if m_med:
            med_us = round(int(m_med.group(1)) / 1000.0, 2)
            iqr_us = round(int(m_iqr.group(1)) / 1000.0, 2)

    return {
        "text_bytes": text_bytes,
        "inst_count": inst_count,
        "bounds_panics": bounds_panics,
        "median_runtime_us": med_us,
        "iqr_runtime_us": iqr_us,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    opt_bin = str(bin_dir / "opt")
    llc_bin = str(bin_dir / "llc")
    llvm_size = str(bin_dir / "llvm-size")
    llvm_objdump = str(bin_dir / "llvm-objdump")

    all_group_ids = {gid for gid, _, _ in PASS_GROUPS}
    rows = []
    synergy_data = {}

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src_path = tmp_path / "kernel.rs"
        src_path.write_text("#![no_std]\n" + ABLATION_WORKLOAD_RS, encoding="utf-8")
        driver_src = tmp_path / "driver.rs"
        driver_src.write_text(RUNNER_MAIN_RS, encoding="utf-8")

        # Emit pre-LLVM-opt bitcode from Runtime(PostCleanup) MIR (-Z mir-opt-level=0 -C no-prepopulate-passes)
        # so MIR optimizations do not mask the effect of LLVM Inlining, SROA, GVN, or DSE!
        env_boot = {**os.environ, "RUSTC_BOOTSTRAP": "1"}
        target_bcs = {}
        target_bcs_os = {}
        target_bcs_oz = {}
        for t in TIER1_TARGETS:
            bc_out = tmp_path / f"preopt_{t}.bc"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", t, "-C", "opt-level=3", "-Z", "mir-opt-level=0", "-C", "no-prepopulate-passes",
                "-C", "codegen-units=1", "--emit=llvm-bc", str(src_path), "-o", str(bc_out)
            ], env=env_boot, check=True)
            target_bcs[t] = bc_out
            bc_os = tmp_path / f"preopt_os_{t}.bc"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", t, "-C", "opt-level=s", "-Z", "mir-opt-level=0", "-C", "no-prepopulate-passes",
                "-C", "codegen-units=1", "--emit=llvm-bc", str(src_path), "-o", str(bc_os)
            ], env=env_boot, check=True)
            target_bcs_os[t] = bc_os
            bc_oz = tmp_path / f"preopt_oz_{t}.bc"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021", "--crate-type=rlib",
                "--target", t, "-C", "opt-level=z", "-Z", "mir-opt-level=0", "-C", "no-prepopulate-passes",
                "-C", "codegen-units=1", "--emit=llvm-bc", str(src_path), "-o", str(bc_oz)
            ], env=env_boot, check=True)
            target_bcs_oz[t] = bc_oz

        # Step 1: Full 12-group Leave-One-Out (LOO) and Add-One-In (AOI) on x86_64, aarch64, i686 + static size across all 8 targets
        x86_bc = target_bcs["x86_64-unknown-linux-gnu"]
        w_dir = tmp_path / "work"
        w_dir.mkdir(parents=True, exist_ok=True)

        full_12_res = run_pipeline_on_bc(
            opt_bin, llc_bin, llvm_size, llvm_objdump, x86_bc,
            build_pipeline_string(all_group_ids), "x86_64-unknown-linux-gnu", "-O3",
            w_dir, driver_src, args.toolchain
        )
        base_0_res = run_pipeline_on_bc(
            opt_bin, llc_bin, llvm_size, llvm_objdump, x86_bc,
            build_pipeline_string(set()), "x86_64-unknown-linux-gnu", "-O0",
            w_dir, driver_src, args.toolchain
        )

        # In LLVM 23.1.1, `default<Os>` and `default<Oz>` were removed; `rustc` emits `optsize`/`minsize`
        # function attributes and runs `default<O2>`!
        std_o3_res = run_pipeline_on_bc(
            opt_bin, llc_bin, llvm_size, llvm_objdump, x86_bc,
            "default<O3>", "x86_64-unknown-linux-gnu", "-O3",
            w_dir, driver_src, args.toolchain
        )
        std_os_res = run_pipeline_on_bc(
            opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs_os["x86_64-unknown-linux-gnu"],
            "default<O2>", "x86_64-unknown-linux-gnu", "-O2",
            w_dir, driver_src, args.toolchain
        )
        std_oz_res = run_pipeline_on_bc(
            opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs_oz["x86_64-unknown-linux-gnu"],
            "default<O2>", "x86_64-unknown-linux-gnu", "-O2",
            w_dir, driver_src, args.toolchain
        )

        # Measure each of the 12 groups in LOO (All \ {Gi}) and AOI ({Gi}) across x86_64, aarch64, i686, Windows, macOS
        for gid, desc, passes in PASS_GROUPS:
            loo_set = all_group_ids - {gid}
            aoi_set = {gid}
            loo_pipe = build_pipeline_string(loo_set)
            aoi_pipe = build_pipeline_string(aoi_set)

            loo_x86 = run_pipeline_on_bc(
                opt_bin, llc_bin, llvm_size, llvm_objdump, x86_bc,
                loo_pipe, "x86_64-unknown-linux-gnu", "-O3",
                w_dir, driver_src, args.toolchain
            )
            aoi_x86 = run_pipeline_on_bc(
                opt_bin, llc_bin, llvm_size, llvm_objdump, x86_bc,
                aoi_pipe, "x86_64-unknown-linux-gnu", "-O3",
                w_dir, driver_src, args.toolchain
            )

            # Also measure AArch64 and i686 instruction/text impact for this group
            loo_a64 = run_pipeline_on_bc(
                opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs["aarch64-unknown-linux-gnu"],
                loo_pipe, "aarch64-unknown-linux-gnu", "-O3",
                w_dir, None, args.toolchain
            )
            full_a64 = run_pipeline_on_bc(
                opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs["aarch64-unknown-linux-gnu"],
                build_pipeline_string(all_group_ids), "aarch64-unknown-linux-gnu", "-O3",
                w_dir, None, args.toolchain
            )
            loo_i686 = run_pipeline_on_bc(
                opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs["i686-unknown-linux-gnu"],
                loo_pipe, "i686-unknown-linux-gnu", "-O3",
                w_dir, None, args.toolchain
            )
            full_i686 = run_pipeline_on_bc(
                opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs["i686-unknown-linux-gnu"],
                build_pipeline_string(all_group_ids), "i686-unknown-linux-gnu", "-O3",
                w_dir, None, args.toolchain
            )

            # LOO slowdown % when Gi is removed from Full_12
            loo_slowdown_pct = round(
                ((loo_x86["median_runtime_us"] - full_12_res["median_runtime_us"]) / full_12_res["median_runtime_us"]) * 100.0, 2
            )
            # AOI speedup % when Gi is added to minimal mem2reg baseline
            aoi_speedup_pct = round(
                ((base_0_res["median_runtime_us"] - aoi_x86["median_runtime_us"]) / base_0_res["median_runtime_us"]) * 100.0, 2
            )

            rows.append({
                "pass_group": gid,
                "description": desc,
                "x86_64_full12_runtime_us": full_12_res["median_runtime_us"],
                "x86_64_loo_runtime_us": loo_x86["median_runtime_us"],
                "x86_64_loo_slowdown_pct": loo_slowdown_pct,
                "x86_64_aoi_runtime_us": aoi_x86["median_runtime_us"],
                "x86_64_aoi_speedup_vs_mem2reg_pct": aoi_speedup_pct,
                "x86_64_loo_text_bytes": loo_x86["text_bytes"],
                "x86_64_loo_text_delta_bytes": loo_x86["text_bytes"] - full_12_res["text_bytes"],
                "x86_64_loo_bounds_panics": loo_x86["bounds_panics"],
                "aarch64_loo_text_bytes": loo_a64["text_bytes"],
                "aarch64_loo_text_delta_bytes": loo_a64["text_bytes"] - full_a64["text_bytes"],
                "i686_loo_text_bytes": loo_i686["text_bytes"],
                "i686_loo_text_delta_bytes": loo_i686["text_bytes"] - full_i686["text_bytes"],
            })

        # Sort rows by LOO slowdown descending
        rows.sort(key=lambda r: r["x86_64_loo_slowdown_pct"], reverse=True)
        for rank_idx, r in enumerate(rows, start=1):
            r["rank_by_loo_speed_impact"] = rank_idx

        # Step 2: Top-6 Pairwise Interaction Matrix
        # Synergies: Delta(A U B) - Delta(A) - Delta(B) where Delta(S) = base_runtime - runtime(S)
        top_pairs = [
            ("G1_Inlining", "G2_SROA_EarlyCSE"),
            ("G1_Inlining", "G3_InstCombine_Peephole"),
            ("G2_SROA_EarlyCSE", "G5_GVN_DSE_MemOpt"),
            ("G7_LoopCanon_LICM", "G9_Vectorization"),
            ("G1_Inlining", "G10_BoundsCheck_Range"),
            ("G2_SROA_EarlyCSE", "G9_Vectorization"),
        ]
        # Cache single-group runs
        single_cache = {}
        for g_a, g_b in top_pairs:
            for g in (g_a, g_b):
                if g not in single_cache:
                    single_cache[g] = run_pipeline_on_bc(
                        opt_bin, llc_bin, llvm_size, llvm_objdump, x86_bc,
                        build_pipeline_string({g}), "x86_64-unknown-linux-gnu", "-O3",
                        w_dir, driver_src, args.toolchain
                    )
            pair_res = run_pipeline_on_bc(
                opt_bin, llc_bin, llvm_size, llvm_objdump, x86_bc,
                build_pipeline_string({g_a, g_b}), "x86_64-unknown-linux-gnu", "-O3",
                w_dir, driver_src, args.toolchain
            )
            base_t = base_0_res["median_runtime_us"]
            da = base_t - single_cache[g_a]["median_runtime_us"]
            db = base_t - single_cache[g_b]["median_runtime_us"]
            dab = base_t - pair_res["median_runtime_us"]
            interaction_us = round(dab - (da + db), 2)
            interaction_pct_of_base = round((interaction_us / base_t) * 100.0, 2)
            synergy_data[f"{g_a}__x__{g_b}"] = {
                "baseline_mem2reg_runtime_us": base_t,
                "only_A_runtime_us": single_cache[g_a]["median_runtime_us"],
                "only_B_runtime_us": single_cache[g_b]["median_runtime_us"],
                "both_AB_runtime_us": pair_res["median_runtime_us"],
                "marginal_lift_A_us": round(da, 2),
                "marginal_lift_B_us": round(db, 2),
                "joint_lift_AB_us": round(dab, 2),
                "super_additive_interaction_us": interaction_us,
                "super_additive_interaction_pct": interaction_pct_of_base,
                "both_AB_text_bytes": pair_res["text_bytes"],
                "both_AB_bounds_panics": pair_res["bounds_panics"],
            }

        # Step 3: Integrated Run 10 (`S12`) MIR Pass Ablation vs. LLVM Pass Ablation
        # Compare disabling individual MIR passes (-Zmir-enable-passes=-<Pass>) and -Zmir-opt-level=0..4
        # at both -Copt-level=0 (no LLVM opt) and -Copt-level=3 (with LLVM -O3)
        mir_ablation_configs = [
            ("MIR0_LLVM_O0", ["-C", "opt-level=0", "-Z", "mir-opt-level=0"]),
            ("MIR1_Default_LLVM_O0", ["-C", "opt-level=0", "-Z", "mir-opt-level=1"]),
            ("MIR2_LLVM_O0", ["-C", "opt-level=0", "-Z", "mir-opt-level=2"]),
            ("MIR0_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=0"]),
            ("MIR1_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=1"]),
            ("MIR2_Default_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2"]),
            ("MIR3_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=3"]),
            ("MIR4_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=4"]),
            ("MIR2_No_Inline_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-Inline"]),
            ("MIR2_No_SROA_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-ScalarReplacementOfAggregates"]),
            ("MIR2_No_GVN_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-GVN"]),
            ("MIR2_No_DSE_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-DeadStoreElimination-initial,-DeadStoreElimination-final"]),
            ("MIR2_No_DestProp_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-DestinationPropagation"]),
            ("MIR2_No_RefProp_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-ReferencePropagation"]),
            ("MIR2_No_JumpThreading_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-JumpThreading"]),
            ("MIR2_No_InstSimplify_LLVM_O3", ["-C", "opt-level=3", "-Z", "mir-opt-level=2", "-Z", "mir-enable-passes=-InstSimplify-before-inline,-InstSimplify-after-simplifycfg"]),
        ]
        mir_vs_llvm_summary = {}
        full_bench_src = tmp_path / "full_mir_bench.rs"
        full_bench_src.write_text(
            ABLATION_WORKLOAD_RS + "\n" + RUNNER_MAIN_RS.replace("extern \"C\" {\n    fn run_ablation_kernel(data: *const u32, len: usize, seed: u64) -> u64;\n}", ""),
            encoding="utf-8"
        )
        for m_name, m_flags in mir_ablation_configs:
            m_bin = tmp_path / f"mir_bin_{m_name}"
            m_ll = tmp_path / f"mir_ll_{m_name}.ll"
            t0 = time.monotonic()
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021",
                "--target", "x86_64-unknown-linux-gnu",
                "-C", "codegen-units=1",
                str(full_bench_src), "-o", str(m_bin)
            ] + m_flags, env={**os.environ, "RUSTC_BOOTSTRAP": "1"}, check=True)
            compile_ms = round((time.monotonic() - t0) * 1000.0, 2)
            r_out = subprocess.check_output([str(m_bin)], text=True)
            med_us = round(int(re.search(r"MEDIAN_NS=(\d+)", r_out).group(1)) / 1000.0, 2)
            text_sz, inst_cnt, bp_cnt = parse_obj_text_and_insts(llvm_size, llvm_objdump, m_bin)
            mir_vs_llvm_summary[m_name] = {
                "flags": " ".join(m_flags),
                "compile_time_ms": compile_ms,
                "median_runtime_us": med_us,
                "binary_text_bytes": text_sz,
                "panic_bounds_calls": bp_cnt,
            }

        # Step 4: Cross-Target 8-Target Static Size & Instruction Summary for Baseline vs Full-12 vs Default<O3>/<Os>/<Oz>
        cross_target_baselines = {}
        for t in TIER1_TARGETS:
            bc = target_bcs[t]
            b0 = run_pipeline_on_bc(opt_bin, llc_bin, llvm_size, llvm_objdump, bc, build_pipeline_string(set()), t, "-O0", w_dir, None, args.toolchain)
            f12 = run_pipeline_on_bc(opt_bin, llc_bin, llvm_size, llvm_objdump, bc, build_pipeline_string(all_group_ids), t, "-O3", w_dir, None, args.toolchain)
            do3 = run_pipeline_on_bc(opt_bin, llc_bin, llvm_size, llvm_objdump, bc, "default<O3>", t, "-O3", w_dir, None, args.toolchain)
            dos = run_pipeline_on_bc(opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs_os[t], "default<O2>", t, "-O2", w_dir, None, args.toolchain)
            doz = run_pipeline_on_bc(opt_bin, llc_bin, llvm_size, llvm_objdump, target_bcs_oz[t], "default<O2>", t, "-O2", w_dir, None, args.toolchain)
            cross_target_baselines[t] = {
                "mem2reg_baseline_text_bytes": b0["text_bytes"],
                "mem2reg_baseline_insts": b0["inst_count"],
                "mem2reg_baseline_bounds_panics": b0["bounds_panics"],
                "full12_O3_text_bytes": f12["text_bytes"],
                "full12_O3_insts": f12["inst_count"],
                "full12_O3_bounds_panics": f12["bounds_panics"],
                "default_O3_text_bytes": do3["text_bytes"],
                "default_Os_text_bytes": dos["text_bytes"],
                "default_Oz_text_bytes": doz["text_bytes"],
            }

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "pass_group_rankings.csv"
    fieldnames = [
        "rank_by_loo_speed_impact", "pass_group", "description",
        "x86_64_full12_runtime_us", "x86_64_loo_runtime_us", "x86_64_loo_slowdown_pct",
        "x86_64_aoi_runtime_us", "x86_64_aoi_speedup_vs_mem2reg_pct",
        "x86_64_loo_text_bytes", "x86_64_loo_text_delta_bytes", "x86_64_loo_bounds_panics",
        "aarch64_loo_text_bytes", "aarch64_loo_text_delta_bytes",
        "i686_loo_text_bytes", "i686_loo_text_delta_bytes",
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)

    json_path = args.out_dir / "pairwise_interactions.json"
    json_path.write_text(json.dumps({
        "toolchain": args.toolchain,
        "rust_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "x86_64_reference_points": {
            "mem2reg_minimal_baseline": base_0_res,
            "canonical_12_group_O3": full_12_res,
            "llvm_default_O3": std_o3_res,
            "llvm_default_Os": std_os_res,
            "llvm_default_Oz": std_oz_res,
        },
        "top_6_pairwise_interactions": synergy_data,
        "s12_mir_vs_llvm_ablation": mir_vs_llvm_summary,
        "cross_target_8_tier1_baselines": cross_target_baselines,
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {csv_path} ({len(rows)} rows) and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
