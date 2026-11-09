#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical LLVM 21.1.8 middle-end pass-ablation benchmark on realistic Rust code."""

import json
import os
import re
import subprocess
import sys
from pathlib import Path

SCRATCH_DIR = Path(__file__).resolve().parent
RUSTC = "/home/user/.cargo/bin/rustc"
OPT = "/usr/bin/opt"
LLC = "/usr/bin/llc"

RUST_SOURCE = r"""
#![no_std]
#![allow(dead_code)]

// 1. Slice iteration and summation with predicate clamping
#[inline]
fn scale_and_clamp(x: u64, factor: u64, cap: u64) -> u64 {
    let prod = x.wrapping_mul(factor);
    if prod > cap { cap } else { prod }
}

#[no_mangle]
pub fn bench_slice_sum(slice: &[u64], factor: u64, cap: u64) -> u64 {
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < slice.len() {
        let v = slice[i];
        let scaled = scale_and_clamp(v, factor, cap);
        acc = acc.wrapping_add(scaled);
        i += 1;
    }
    acc
}

// 2. Struct / Enum protocol state-machine transitions
#[derive(Copy, Clone)]
pub enum ProtoState {
    Idle,
    Header { magic: u32, remaining: u32 },
    Payload { checksum: u32, count: u32 },
    Done { final_crc: u32 },
    Error(u32),
}

#[derive(Copy, Clone)]
pub struct PacketCtx {
    pub state: ProtoState,
    pub total_bytes: u32,
    pub flags: u32,
}

#[inline]
fn step_machine(mut ctx: PacketCtx, word: u32) -> PacketCtx {
    ctx.total_bytes = ctx.total_bytes.wrapping_add(4);
    ctx.state = match ctx.state {
        ProtoState::Idle => {
            if word == 0x5255_5354 {
                ProtoState::Header { magic: word, remaining: 2 }
            } else {
                ProtoState::Error(1)
            }
        }
        ProtoState::Header { magic, remaining } => {
            if remaining <= 1 {
                ProtoState::Payload { checksum: magic ^ word, count: (word & 0x3) + 1 }
            } else {
                ProtoState::Header { magic: magic.wrapping_add(word), remaining: remaining - 1 }
            }
        }
        ProtoState::Payload { checksum, count } => {
            let next_csum = checksum.rotate_left(5) ^ word;
            if count <= 1 {
                ProtoState::Done { final_crc: next_csum }
            } else {
                ProtoState::Payload { checksum: next_csum, count: count - 1 }
            }
        }
        ProtoState::Done { final_crc } => ProtoState::Done { final_crc },
        ProtoState::Error(code) => ProtoState::Error(code),
    };
    ctx
}

#[no_mangle]
pub fn bench_state_machine(w0: u32, w1: u32, w2: u32, w3: u32) -> u32 {
    let mut ctx = PacketCtx {
        state: ProtoState::Idle,
        total_bytes: 0,
        flags: 0x01,
    };
    ctx = step_machine(ctx, w0);
    ctx = step_machine(ctx, w1);
    ctx = step_machine(ctx, w2);
    ctx = step_machine(ctx, w3);
    match ctx.state {
        ProtoState::Done { final_crc } => final_crc ^ ctx.total_bytes,
        ProtoState::Payload { checksum, count } => checksum ^ count ^ ctx.total_bytes,
        ProtoState::Header { magic, remaining } => magic ^ remaining,
        ProtoState::Idle => 0,
        ProtoState::Error(e) => e | 0x8000_0000,
    }
}

// 3. Binary search and bounds-checked array indexing
#[no_mangle]
pub fn bench_binary_search(arr: &[u64], target: u64) -> usize {
    if arr.is_empty() {
        return usize::MAX;
    }
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    while low < high {
        let mid = low + ((high - low) >> 1);
        if mid >= arr.len() {
            break;
        }
        let mid_val = arr[mid];
        if mid_val < target {
            low = mid + 1;
        } else if mid_val > target {
            high = mid;
        } else {
            return mid;
        }
    }
    usize::MAX
}

// 4. Bit-manipulation, demanded-bits masking, and rolling checksum
#[inline]
fn mix_lanes(a: u64, b: u64) -> u64 {
    let x = a.wrapping_add(0).wrapping_mul(1);
    let hi_noise = (b | 0xffff_0000_0000_0000) & 0x0000_ffff_ffff_ffff;
    let rotated = (x ^ hi_noise).rotate_left(13);
    (rotated | 0xffff_ffff_0000_0000) & 0x0000_0000_ffff_ffff
}

#[no_mangle]
pub fn bench_checksum_bits(data: &[u64], seed: u64) -> u32 {
    let mut s1: u64 = seed & 0xffff;
    let mut s2: u64 = (seed >> 16) & 0xffff;
    let mut idx: usize = 0;
    while idx < data.len() {
        let word = data[idx];
        let mixed = mix_lanes(word, s1);
        s1 = (s1.wrapping_add(mixed)) & 0xffff;
        s2 = (s2.wrapping_add(s1)) & 0xffff;
        idx += 1;
    }
    ((s2 << 16) | s1) as u32
}

// 5. Option / Result combinator chains
#[inline]
fn parse_header_byte(b: u8) -> Option<u32> {
    if b >= b'0' && b <= b'9' {
        Some((b - b'0') as u32)
    } else if b >= b'a' && b <= b'f' {
        Some(10 + (b - b'a') as u32)
    } else {
        None
    }
}

#[inline]
fn validate_non_zero(v: u32) -> Result<u32, u32> {
    if v == 0 {
        Err(0xff)
    } else {
        Ok(v.wrapping_mul(16))
    }
}

#[no_mangle]
pub fn bench_option_result_chain(b0: u8, b1: u8, b2: u8, fallback: u32) -> u32 {
    let r0 = parse_header_byte(b0)
        .map(|x| x.wrapping_add(1))
        .ok_or(10u32)
        .and_then(validate_non_zero);
    let r1 = parse_header_byte(b1)
        .and_then(|y| parse_header_byte(b2).map(|z| y.wrapping_mul(16).wrapping_add(z)))
        .ok_or(20u32);
    match (r0, r1) {
        (Ok(v0), Ok(v1)) => v0.wrapping_add(v1),
        (Ok(v0), Err(e1)) => v0 ^ e1,
        (Err(e0), Ok(v1)) => v1 ^ e0,
        (Err(_), Err(_)) => fallback,
    }
}

// 6. Matrix/vector loop with loop-invariant load/compute, SCEV affine recurrence,
// dead scratch store (DSE), and dead diagnostic loop (LoopDeletion)
#[no_mangle]
pub fn bench_matrix_vec_loop(
    mat: &[u64],
    vec: &[u64],
    cfg_scale: &u64,
    out: &mut [u64],
    rows: usize,
    cols: usize,
) -> u64 {
    // Dead diagnostic loop (purely local counter, unused after loop -> LoopDeletion target)
    let mut diag: usize = 0;
    let mut k: usize = 0;
    while k < rows {
        diag = diag.wrapping_add(k ^ 0x5a5a);
        k += 1;
    }

    let mut total_checksum: u64 = 0;
    let mut r: usize = 0;
    while r < rows {
        let mut dot: u64 = 0;
        let mut c: usize = 0;
        let out_ptr = unsafe { out.as_mut_ptr().add(r) };
        let hdr_scale = *cfg_scale;
        while c < cols {
            // Redundant load (*cfg_scale) + loop-invariant compute + SCEV affine index (r * cols + c)
            let scale = (*cfg_scale).wrapping_add(hdr_scale).wrapping_add(1);
            let mat_idx = r.wrapping_mul(cols).wrapping_add(c);
            let m_val = unsafe { *mat.as_ptr().add(mat_idx) };
            let v_val = unsafe { *vec.as_ptr().add(c) };
            dot = dot.wrapping_add(m_val.wrapping_mul(v_val).wrapping_mul(scale));
            c += 1;
        }
        // Overwritten store to *out_ptr (DSE target)
        unsafe {
            *out_ptr = dot.wrapping_add(1);
            *out_ptr = dot;
        }
        total_checksum = total_checksum.wrapping_add(dot);
        r += 1;
    }
    total_checksum
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
"""

BENCH_FNS = [
    "bench_slice_sum",
    "bench_state_machine",
    "bench_binary_search",
    "bench_checksum_bits",
    "bench_option_result_chain",
    "bench_matrix_vec_loop",
]

PIPELINES = [
    ("P0", "Baseline unoptimized (rustc -Copt-level=0)", None),
    (
        "P1",
        "SROA + Mem2Reg + SimplifyCFG",
        "function(sroa<modify-cfg>,simplifycfg)",
    ),
    (
        "P2",
        "P1 + InstCombine + EarlyCSE",
        "function(sroa<modify-cfg>,simplifycfg,instcombine<no-verify-fixpoint>,early-cse<memssa>)",
    ),
    (
        "P3",
        "P1 + Inliner + SROA + InstCombine + SimplifyCFG",
        "function(sroa<modify-cfg>,simplifycfg),cgscc(inline),function(sroa<modify-cfg>,instcombine<no-verify-fixpoint>,simplifycfg),globaldce",
    ),
    (
        "P4",
        "P3 + GVN + MemCpyOpt + DSE + BDCE + ADCE + SCCP + CVP",
        "function(sroa<modify-cfg>,simplifycfg),cgscc(inline),function(sroa<modify-cfg>,instcombine<no-verify-fixpoint>,simplifycfg,gvn<>,memcpyopt,dse,bdce,adce,sccp,correlated-propagation,instcombine<no-verify-fixpoint>,simplifycfg),globaldce",
    ),
    (
        "P5",
        "P4 + Loop(LoopRotate + LICM + IndVarSimplify + LoopDeletion + LoopUnroll)",
        "function(sroa<modify-cfg>,simplifycfg),cgscc(inline),function(sroa<modify-cfg>,instcombine<no-verify-fixpoint>,simplifycfg,gvn<>,memcpyopt,dse,bdce,adce,sccp,correlated-propagation,loop-mssa(loop-instsimplify,loop-simplifycfg,licm<no-allowspeculation>,loop-rotate<header-duplication;no-prepare-for-lto>,licm<allowspeculation>),loop(indvars,loop-deletion,loop-unroll-full),instcombine<no-verify-fixpoint>,jump-threading,correlated-propagation,simplifycfg<bonus-inst-threshold=1;forward-switch-cond;switch-range-to-icmp;switch-to-lookup;hoist-common-insts;sink-common-insts>,instcombine<no-verify-fixpoint>,adce,dse),globaldce",
    ),
    (
        "P6_scalar",
        "LLVM 21.1.8 default<O2> (scalar only: -vectorize-loops=false -unroll-runtime=false)",
        "default<O2>",
    ),
    (
        "P6",
        "Full LLVM 21.1.8 default<O2> (including LoopVectorize + Runtime Unroll)",
        "default<O2>",
    ),
]


def strip_optnone(ll_text: str) -> str:
    # Remove optnone and LLVM-22-only nocreateundeforpoison attribute so LLVM 21 opt/llc can process O0 output
    ll_text = re.sub(r"\boptnone\b", "", ll_text)
    ll_text = re.sub(r"\bnocreateundeforpoison\b", "", ll_text)
    # Preserve Rust reference noalias/readonly semantics on the benchmark entry slice/ref parameters
    ll_text = ll_text.replace(
        "ptr align 8 %mat.0, i64 %mat.1, ptr align 8 %vec.0, i64 %vec.1, ptr align 8 %cfg_scale, ptr align 8 %out.0",
        "ptr noalias readonly align 8 %mat.0, i64 %mat.1, ptr noalias readonly align 8 %vec.0, i64 %vec.1, ptr noalias readonly align 8 %cfg_scale, ptr noalias align 8 %out.0",
    )
    return ll_text


def parse_ir_metrics(ll_text: str):
    """Parse both whole-module and per-benchmark-function instruction counts."""
    lines = ll_text.splitlines()
    in_func = None
    func_stats = {}
    mod_stats = {
        "total_insts": 0,
        "alloca": 0,
        "load": 0,
        "store": 0,
        "load_store": 0,
        "br_switch": 0,
        "call": 0,
        "phi": 0,
        "gep": 0,
    }

    def init_stat():
        return {
            "total_insts": 0,
            "alloca": 0,
            "load": 0,
            "store": 0,
            "load_store": 0,
            "br_switch": 0,
            "call": 0,
            "phi": 0,
            "gep": 0,
        }

    for line in lines:
        m_def = re.match(r"^define\s+.*@([a-zA-Z0-9_$]+)\(", line)
        if m_def:
            in_func = m_def.group(1)
            func_stats[in_func] = init_stat()
            continue
        if in_func is not None:
            if line.startswith("}"):
                in_func = None
                continue
            s = line.strip()
            if not s or s.startswith(";") or s.endswith(":"):
                continue
            # Remove leading label if any
            if ":" in s and not s.startswith("%") and not s.startswith("store") and not s.startswith("call") and not s.startswith("br") and not s.startswith("switch") and not s.startswith("ret"):
                # Could be a label or switch case
                if re.match(r"^[a-zA-Z0-9_$.]+:\s*(;.*)?$", s):
                    continue
            # Check if inside a multi-line switch table `[` ... `]`
            if re.match(r"^i\d+\s+-?\d+,\s*label\s+%", s) or s == "]":
                continue

            # Extract opcode
            m_assign = re.match(r"^%[a-zA-Z0-9_$.]+\s*=\s*([a-z]+)\b", s)
            if m_assign:
                op = m_assign.group(1)
            else:
                m_op = re.match(r"^([a-z]+)\b", s)
                if not m_op:
                    continue
                op = m_op.group(1)

            # Ignore llvm.dbg / lifetime intrinsics if any? Count real instructions
            for st in (mod_stats, func_stats[in_func]):
                st["total_insts"] += 1
                if op == "alloca":
                    st["alloca"] += 1
                elif op == "load":
                    st["load"] += 1
                    st["load_store"] += 1
                elif op == "store":
                    st["store"] += 1
                    st["load_store"] += 1
                elif op in ("br", "switch"):
                    st["br_switch"] += 1
                elif op in ("call", "tail", "musttail", "invoke"):
                    st["call"] += 1
                elif op == "phi":
                    st["phi"] += 1
                elif op == "getelementptr":
                    st["gep"] += 1

    bench_only = init_stat()
    for fn_name in BENCH_FNS:
        if fn_name in func_stats:
            for k in bench_only:
                bench_only[k] += func_stats[fn_name][k]

    return {
        "module": mod_stats,
        "bench_roots": bench_only,
        "per_fn": {k: func_stats.get(k, init_stat()) for k in BENCH_FNS},
    }


def count_asm_insts(asm_text: str) -> int:
    count = 0
    for line in asm_text.splitlines():
        s = line.strip()
        if not s:
            continue
        if s.startswith(".") or s.startswith("#") or s.startswith("//") or s.startswith(";"):
            continue
        if s.endswith(":"):
            continue
        count += 1
    return count


def main():
    SCRATCH_DIR.mkdir(parents=True, exist_ok=True)
    rs_path = SCRATCH_DIR / "bench_suite.rs"
    raw_ll_path = SCRATCH_DIR / "bench_P0_raw.ll"
    p0_ll_path = SCRATCH_DIR / "bench_P0.ll"

    rs_path.write_text(RUST_SOURCE)
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    subprocess.run(
        [
            RUSTC,
            "--edition=2021",
            "--crate-type=lib",
            "-C",
            "opt-level=0",
            "-C",
            "debug-assertions=no",
            "-Z",
            "mir-opt-level=0",
            "-C",
            "no-prepopulate-passes",
            "-C",
            "panic=abort",
            "--emit=llvm-ir",
            "-o",
            str(raw_ll_path),
            str(rs_path),
        ],
        env=env,
        check=True,
    )

    cleaned_ll = strip_optnone(raw_ll_path.read_text())
    p0_ll_path.write_text(cleaned_ll)

    results = {}
    for pid, desc, pipeline in PIPELINES:
        out_ll = SCRATCH_DIR / f"bench_{pid}.ll"
        if pipeline is None:
            out_ll.write_text(cleaned_ll)
        else:
            extra_flags = []
            if pid == "P6_scalar":
                extra_flags = ["-vectorize-loops=false", "-vectorize-slp=false", "-unroll-runtime=false"]
            subprocess.run(
                [
                    OPT,
                    "-S",
                    f"-passes={pipeline}",
                    *extra_flags,
                    str(p0_ll_path),
                    "-o",
                    str(out_ll),
                ],
                check=True,
            )

        ll_text = out_ll.read_text()
        ir_metrics = parse_ir_metrics(ll_text)

        # Run llc -O2 for x86_64 and aarch64
        x86_s = SCRATCH_DIR / f"bench_{pid}_x86_64.s"
        arm_s = SCRATCH_DIR / f"bench_{pid}_aarch64.s"
        subprocess.run(
            [LLC, "-O2", "-mtriple=x86_64-unknown-linux-gnu", str(out_ll), "-o", str(x86_s)],
            check=True,
        )
        subprocess.run(
            [LLC, "-O2", "-mtriple=aarch64-unknown-linux-gnu", str(out_ll), "-o", str(arm_s)],
            check=True,
        )
        ir_metrics["x86_64_asm_insts"] = count_asm_insts(x86_s.read_text())
        ir_metrics["aarch64_asm_insts"] = count_asm_insts(arm_s.read_text())
        ir_metrics["description"] = desc
        ir_metrics["pipeline"] = pipeline or "none"
        results[pid] = ir_metrics

    out_json = SCRATCH_DIR / "ablation_results.json"
    out_json.write_text(json.dumps(results, indent=2))

    print("=== WHOLE MODULE METRICS ===")
    print(f"{'Tier':<5} | {'Total IR':>8} | {'alloca':>6} | {'load':>6} | {'store':>6} | {'br/sw':>6} | {'call':>6} | {'phi':>5} | {'x86_64':>7} | {'aarch64':>7}")
    print("-" * 88)
    for pid, _, _ in PIPELINES:
        m = results[pid]["module"]
        x86 = results[pid]["x86_64_asm_insts"]
        arm = results[pid]["aarch64_asm_insts"]
        print(
            f"{pid:<5} | {m['total_insts']:>8} | {m['alloca']:>6} | {m['load']:>6} | {m['store']:>6} | {m['br_switch']:>6} | {m['call']:>6} | {m['phi']:>5} | {x86:>7} | {arm:>7}"
        )

    print("\n=== 6 BENCHMARK ENTRY FUNCTIONS METRICS ===")
    print(f"{'Tier':<5} | {'Total IR':>8} | {'alloca':>6} | {'load':>6} | {'store':>6} | {'br/sw':>6} | {'call':>6} | {'phi':>5}")
    print("-" * 70)
    for pid, _, _ in PIPELINES:
        m = results[pid]["bench_roots"]
        print(
            f"{pid:<5} | {m['total_insts']:>8} | {m['alloca']:>6} | {m['load']:>6} | {m['store']:>6} | {m['br_switch']:>6} | {m['call']:>6} | {m['phi']:>5}"
        )


if __name__ == "__main__":
    main()
