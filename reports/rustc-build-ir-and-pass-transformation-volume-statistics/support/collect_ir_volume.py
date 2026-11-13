#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Collects MIR statement/terminator counts, pre/post-O3 LLVM IR instruction
counts, inlining call-site deltas, and sysroot (`core`, `alloc`, `std`) symbol
and instruction volumes across all 8 Tier 1 targets on Rust 1.99.1."""

from __future__ import annotations
import json
import os
import re
import subprocess
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = TC_ROOT / "bin" / "rustc"
LLVM_OBJDUMP = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / "llvm-objdump"
LLVM_NM = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / "llvm-nm"

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "aarch64-pc-windows-msvc",
    "i686-pc-windows-msvc",
]

SHARED_BENCHMARK_SUITE_RS = r"""#![no_std]
#![crate_type = "rlib"]
#![allow(dead_code)]

use core::sync::atomic::{AtomicUsize, Ordering};

// 1. hashbrown-style SwissTable probe + FNV/FX hash
#[inline]
pub fn hash_u64(k: u64) -> u64 {
    let mut h = k.wrapping_mul(0x517cc1b727220a95);
    h ^= h >> 32;
    h
}

#[no_mangle]
pub fn bench_hashbrown_lookup(keys: &[u64], vals: &[u64], query: u64) -> Option<u64> {
    let n = keys.len().min(vals.len());
    if n == 0 {
        return None;
    }
    let mut idx = (hash_u64(query) as usize) % n;
    for step in 0..n {
        let k = keys[idx];
        if k == query {
            return Some(vals[idx]);
        }
        if k == u64::MAX {
            return None;
        }
        idx = (idx + step + 1) % n;
    }
    None
}

// 2. memchr / regex-syntax style byte-class DFA & UTF-8 scanner
#[no_mangle]
pub fn bench_utf8_dfa_scan(bytes: &[u8], needle: u8) -> (usize, usize, Option<usize>) {
    let mut i = 0usize;
    let mut ascii_cnt = 0usize;
    let mut multibyte_cnt = 0usize;
    let mut first_hit = None;
    while i < bytes.len() {
        let b = bytes[i];
        if b == needle && first_hit.is_none() {
            first_hit = Some(i);
        }
        if b < 0x80 {
            ascii_cnt += 1;
            i += 1;
        } else if b < 0xE0 && i + 1 < bytes.len() {
            multibyte_cnt += 1;
            i += 2;
        } else if b < 0xF0 && i + 2 < bytes.len() {
            multibyte_cnt += 1;
            i += 3;
        } else if i + 3 < bytes.len() {
            multibyte_cnt += 1;
            i += 4;
        } else {
            break;
        }
    }
    (ascii_cnt, multibyte_cnt, first_hit)
}

// 3. crc32fast / numeric SIMD-friendly slice reduction
#[no_mangle]
pub fn bench_crc32_and_dot(a: &[i32], b: &[i32], out: &mut [i32]) -> (i64, u32) {
    let n = a.len().min(b.len()).min(out.len());
    let mut dot = 0i64;
    let mut crc = 0xFFFF_FFFFu32;
    for i in 0..n {
        let va = a[i];
        let vb = b[i];
        dot = dot.wrapping_add((va as i64).wrapping_mul(vb as i64));
        let sum = va.saturating_add(vb).clamp(-1_000_000, 1_000_000);
        out[i] = sum;
        crc ^= sum as u32;
        for _ in 0..4 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    (dot, !crc)
}

// 4. itoa / integer decimal formatting into stack buffer
#[no_mangle]
pub fn bench_itoa_u64(mut val: u64, out: &mut [u8; 20]) -> usize {
    if val == 0 {
        out[19] = b'0';
        return 1;
    }
    let mut pos = 20usize;
    while val > 0 && pos > 0 {
        pos -= 1;
        out[pos] = b'0' + ((val % 10) as u8);
        val /= 10;
    }
    20 - pos
}

// 5. ryu / IEEE-754 floating-point polynomial evaluation
#[no_mangle]
pub fn bench_fp64_horner(xs: &[f64], coeffs: &[f64], out: &mut [f64]) -> f64 {
    let n = xs.len().min(out.len());
    let mut total = 0.0f64;
    for i in 0..n {
        let x = xs[i];
        let mut p = 0.0f64;
        for &c in coeffs.iter().rev() {
            p = p * x + c;
        }
        let clamped = p.max(-1.0e6).min(1.0e6);
        out[i] = clamped;
        total += clamped;
    }
    total
}

// 6. zerocopy-style layout-verified header parsing & endianness conversion
#[repr(C)]
#[derive(Clone, Copy)]
pub struct WireFrameHeader {
    pub magic: u32,
    pub version: u16,
    pub flags: u16,
    pub payload_len: u64,
    pub checksum: u64,
}

#[no_mangle]
pub fn bench_zerocopy_header_validate(buf: &[u8; 24]) -> Option<WireFrameHeader> {
    let magic = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
    if magic != 0x5A43_5059 {
        return None;
    }
    let version = u16::from_le_bytes([buf[4], buf[5]]);
    let flags = u16::from_le_bytes([buf[6], buf[7]]);
    let payload_len = u64::from_le_bytes([
        buf[8], buf[9], buf[10], buf[11], buf[12], buf[13], buf[14], buf[15],
    ]);
    let checksum = u64::from_le_bytes([
        buf[16], buf[17], buf[18], buf[19], buf[20], buf[21], buf[22], buf[23],
    ]);
    if payload_len > (1 << 20) {
        return None;
    }
    Some(WireFrameHeader { magic, version, flags, payload_len, checksum })
}

// 7. Atomic ring-buffer ticket claim (concurrency & barriers)
#[no_mangle]
pub fn bench_atomic_ticket_claim(
    head: &AtomicUsize,
    tail: &AtomicUsize,
    cap: usize,
    batch: usize,
) -> Option<usize> {
    let cur_head = head.load(Ordering::Relaxed);
    let cur_tail = tail.load(Ordering::Acquire);
    if cap == 0 || cur_head.wrapping_sub(cur_tail) + batch > cap {
        return None;
    }
    head.store(cur_head.wrapping_add(batch), Ordering::Release);
    Some(cur_head)
}

// 8. serde / syn style recursive-descent varint & tag decoder
#[no_mangle]
pub fn bench_varint_stream_decode(stream: &[u8], out_vals: &mut [u64]) -> usize {
    let mut i = 0usize;
    let mut decoded = 0usize;
    while i < stream.len() && decoded < out_vals.len() {
        let mut acc = 0u64;
        let mut shift = 0u32;
        loop {
            if i >= stream.len() || shift >= 64 {
                return decoded;
            }
            let b = stream[i];
            i += 1;
            acc |= ((b & 0x7F) as u64) << shift;
            if (b & 0x80) == 0 {
                break;
            }
            shift += 7;
        }
        out_vals[decoded] = acc;
        decoded += 1;
    }
    decoded
}
"""


def parse_mir_text(mir_text: str) -> dict[str, int]:
    fn_cnt = 0
    bb_cnt = 0
    stmt_cnt = 0
    term_cnt = 0
    in_bb = False
    for raw in mir_text.splitlines():
        line = raw.strip()
        if line.startswith("fn ") and line.endswith("{"):
            fn_cnt += 1
        elif re.match(r"^bb\d+.*:\s*\{$", line):
            bb_cnt += 1
            in_bb = True
        elif in_bb and line == "}":
            in_bb = False
        elif in_bb and line and not line.startswith("//"):
            if any(
                line.startswith(k)
                for k in ("return", "goto", "switchInt", "resume", "unreachable", "drop(", "assert(")
            ) or " -> [" in line or " -> bb" in line:
                term_cnt += 1
            else:
                stmt_cnt += 1
    return {
        "mir_functions": fn_cnt,
        "mir_basic_blocks": bb_cnt,
        "mir_statements": stmt_cnt,
        "mir_terminators": term_cnt,
        "mir_total_ops": stmt_cnt + term_cnt,
    }


def parse_llvm_ir(ll_text: str) -> dict[str, Any]:
    fn_cnt = 0
    bb_cnt = 0
    inst_cnt = 0
    cats = Counter()
    in_fn = False
    for raw in ll_text.splitlines():
        line = raw.strip()
        if line.startswith("define "):
            fn_cnt += 1
            in_fn = True
            continue
        if in_fn and line == "}":
            in_fn = False
            continue
        if not in_fn or not line or line.startswith(";"):
            continue
        if re.match(r"^[a-zA-Z0-9_.-]+:", line):
            bb_cnt += 1
            continue
        if line.startswith("#dbg_") or line.startswith("!"):
            continue
        inst_cnt += 1
        rhs = line.split("=", 1)[1].strip() if "=" in line and not line.startswith("store") else line
        op = rhs.split(None, 1)[0] if rhs else "other"
        if op in {"tail", "musttail", "notail"} and len(rhs.split()) > 1:
            op = rhs.split()[1]
        if op in {"load", "store", "alloca", "fence", "cmpxchg", "atomicrmw"}:
            cats["memory"] += 1
        elif op in {"call", "invoke", "callbr"}:
            cats["calls"] += 1
        elif op in {"br", "switch", "ret", "unreachable", "resume", "landingpad", "cleanuppad", "catchpad"}:
            cats["control_flow"] += 1
        elif op == "phi":
            cats["phi"] += 1
        elif op == "getelementptr":
            cats["gep"] += 1
        elif op in {"icmp", "fcmp", "select"}:
            cats["compare_select"] += 1
        elif op in {"zext", "sext", "trunc", "bitcast", "ptrtoint", "inttoptr", "ptrtoaddr", "fpext", "fptrunc", "fptosi", "fptoui", "sitofp", "uitofp"}:
            cats["casts"] += 1
        else:
            cats["arith_simd_other"] += 1
    return {
        "llvm_functions": fn_cnt,
        "llvm_basic_blocks": bb_cnt,
        "llvm_instructions": inst_cnt,
        "opcode_categories": dict(cats),
    }


def analyze_sysroot_rlib_sizes(target: str) -> dict[str, Any]:
    lib_dir = TC_ROOT / "lib" / "rustlib" / target / "lib"
    out = {}
    for cname in ("core", "alloc", "std"):
        matches = list(lib_dir.glob(f"lib{cname}-*.rlib"))
        if not matches:
            continue
        rlib = matches[0]
        nm_proc = subprocess.run(
            [str(LLVM_NM), "--defined-only", str(rlib)],
            capture_output=True, text=True, check=False,
        )
        t_syms = sum(1 for l in nm_proc.stdout.splitlines() if " T " in l or " t " in l)
        obj_proc = subprocess.run(
            [str(LLVM_OBJDUMP), "-d", "--no-show-raw-insn", str(rlib)],
            capture_output=True, text=True, check=False,
        )
        insts = sum(1 for l in obj_proc.stdout.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:\s+[a-zA-Z]", l))
        out[cname] = {
            "rlib_bytes": rlib.stat().st_size,
            "defined_text_symbols": t_syms,
            "post_o3_machine_instructions": insts,
        }
    return out


def collect_for_target(target: str, tmp_root: Path) -> tuple[str, dict[str, Any]]:
    tdir = tmp_root / target
    tdir.mkdir(parents=True, exist_ok=True)
    src = tdir / "bench_suite.rs"
    src.write_text(SHARED_BENCHMARK_SUITE_RS)

    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    mir_out = subprocess.run(
        [str(RUSTC), "--edition=2021", "--target", target, "-Z", "unpretty=mir", str(src)],
        capture_output=True, text=True, env=env, check=True,
    ).stdout
    mir_stats = parse_mir_text(mir_out)

    ll_o0 = tdir / "o0.ll"
    subprocess.run(
        [
            str(RUSTC), "--edition=2021", "--target", target,
            "-C", "opt-level=0", "-C", "no-prepopulate-passes",
            "--emit=llvm-ir", "-o", str(ll_o0), str(src),
        ],
        capture_output=True, text=True, env=env, check=True,
    )
    o0_stats = parse_llvm_ir(ll_o0.read_text())

    rem_dir = tdir / "remarks"
    rem_dir.mkdir(exist_ok=True)
    ll_o3 = tdir / "o3.ll"
    subprocess.run(
        [
            str(RUSTC), "--edition=2021", "--target", target,
            "-C", "opt-level=3", "-C", "codegen-units=1", "-C", "debuginfo=1",
            "-C", "remark=all", "-Z", f"remark-dir={rem_dir}",
            "--emit=llvm-ir", "-o", str(ll_o3), str(src),
        ],
        capture_output=True, text=True, env=env, check=True,
    )
    o3_stats = parse_llvm_ir(ll_o3.read_text())

    sysroot_stats = analyze_sysroot_rlib_sizes(target)

    fn_ratio = round(o3_stats["llvm_functions"] / max(o0_stats["llvm_functions"], 1), 4)
    inst_ratio = round(o3_stats["llvm_instructions"] / max(o0_stats["llvm_instructions"], 1), 4)
    calls_o0 = o0_stats["opcode_categories"].get("calls", 0)
    calls_o3 = o3_stats["opcode_categories"].get("calls", 0)
    call_reduction_pct = round((1.0 - (calls_o3 / max(calls_o0, 1))) * 100.0, 2)

    return target, {
        "mir": mir_stats,
        "llvm_pre_opt": o0_stats,
        "llvm_post_o3": o3_stats,
        "o3_to_o0_function_ratio": fn_ratio,
        "o3_to_o0_instruction_ratio": inst_ratio,
        "inlining_call_site_reduction_pct": call_reduction_pct,
        "sysroot_rlibs": sysroot_stats,
    }


def main() -> None:
    sup_dir = Path(__file__).resolve().parent
    tmp_root = Path(os.environ.get("TMPDIR", "/tmp")) / "w7_vol_work"
    tmp_root.mkdir(parents=True, exist_ok=True)

    per_target = {}
    with ThreadPoolExecutor(max_workers=4) as ex:
        futs = [ex.submit(collect_for_target, t, tmp_root) for t in TIER1_TARGETS]
        for f in futs:
            t, data = f.result()
            per_target[t] = data

    out_path = sup_dir / "ir_volume_by_target.json"
    out_path.write_text(json.dumps(per_target, indent=2) + "\n")
    print("Collected IR volume across all 8 Tier 1 targets.")
    for t in TIER1_TARGETS:
        d = per_target[t]
        print(
            f"{t}: MIR ops={d['mir']['mir_total_ops']}, "
            f"O0 insts={d['llvm_pre_opt']['llvm_instructions']} ({d['llvm_pre_opt']['llvm_functions']} fns), "
            f"O3 insts={d['llvm_post_o3']['llvm_instructions']} ({d['llvm_post_o3']['llvm_functions']} fns, "
            f"call_red={d['inlining_call_site_reduction_pct']}%), "
            f"std+core+alloc machine_insts="
            f"{sum(v['post_o3_machine_instructions'] for v in d['sysroot_rlibs'].values())}"
        )


if __name__ == "__main__":
    main()
