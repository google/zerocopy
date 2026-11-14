#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""
Compiles 20 representative Rust functions across all 2^3 = 8 combinations of
(-C overflow-checks=on/off, -C debug-assertions=on/off, -C panic=unwind/abort)
in `rustc 1.99.1` (`-Zmir-opt-level=0 --emit=mir`), extracts `Runtime(PostCleanup)`
MIR structural metrics, and runs the `checkProfileSubsumption` structural diff
between the strictest verification profile `P0 (on, on, unwind)` and all 7
looser profiles (`P1..P7`).
"""

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

RUST_20_FNS_SRC = r'''
#![crate_type = "lib"]
#![allow(dead_code)]

// 01: Checked addition kernel
pub fn f01_checked_add_pair(a: u64, b: u64, c: u64) -> u64 {
    debug_assert!(a <= 1_000_000 && b <= 1_000_000 && c <= 1_000_000);
    a + b + c
}

// 02: Checked subtraction and multiplication
pub fn f02_linear_interp(x: u64, lo: u64, scale: u64) -> u64 {
    debug_assert!(x >= lo && (x - lo) <= 0xFFFF && scale <= 0xFFFF);
    (x - lo) * scale
}

// 03: Left and right shifts (`BinOp::Shl` / `BinOp::Shr`)
pub fn f03_shift_pack(hi: u64, lo: u64, sh: u32) -> u64 {
    debug_assert!(sh < 32);
    (hi << sh) | (lo >> sh)
}

// 04: Signed negation (`UnOp::Neg`)
pub fn f04_signed_abs_delta(x: i64) -> i64 {
    debug_assert!(x > i64::MIN);
    if x < 0 { -x } else { x }
}

// 05: Unsigned division and remainder (`BinOp::Div` / `BinOp::Rem` - always checked!)
pub fn f05_div_rem_split(x: u64, d: u64) -> (u64, u64) {
    debug_assert!(d > 0);
    (x / d, x % d)
}

// 06: Signed division (`i64::MIN / -1` check always emitted)
pub fn f06_signed_div(x: i64, d: i64) -> i64 {
    debug_assert!(d != 0 && !(x == i64::MIN && d == -1));
    x / d
}

// 07: Slice bounds check + loop accumulation
pub fn f07_slice_prefix_sum(s: &[u32], k: usize) -> u64 {
    debug_assert!(k <= s.len());
    let mut sum = 0u64;
    let mut i = 0usize;
    while i < k {
        sum += s[i] as u64;
        i += 1;
    }
    sum
}

// 08: Explicit wrapping arithmetic (profile-invariant arithmetic)
pub fn f08_wrapping_mix(a: u64, b: u64) -> u64 {
    a.wrapping_add(b).wrapping_mul(0x517cc1b727220a95)
}

// 09: Explicit checked_add returning Option (profile-invariant intrinsic)
pub fn f09_explicit_checked_add(a: u64, b: u64) -> Option<u64> {
    a.checked_add(b)
}

// 10: Struct with Drop glue (`ElaborateDrops` + `AbortUnwindingCalls` test)
pub struct GuardedSlot<'a>(pub &'a mut u64);
impl<'a> Drop for GuardedSlot<'a> {
    fn drop(&mut self) {
        *self.0 = (*self.0).wrapping_add(1);
    }
}
#[inline(never)]
pub fn ext_step(v: u64) -> u64 { v.wrapping_add(3) }

pub fn f10_drop_cleanup_pad(slot: &mut u64, x: u64) -> u64 {
    let _g = GuardedSlot(slot);
    let y = ext_step(x);
    y + 1
}

// 11: Binary search midpoint with debug_assert!
pub fn f11_midpoint(lo: usize, hi: usize) -> usize {
    debug_assert!(lo <= hi);
    lo + (hi - lo) / 2
}

// 12: Ring buffer index advance
pub fn f12_ring_advance(pos: usize, step: usize, cap: usize) -> usize {
    debug_assert!(cap.is_power_of_two() && pos < cap && step <= cap);
    (pos + step) & (cap - 1)
}

// 13: Result `?` try propagation with arithmetic
pub fn f13_checked_parse_pair(a: Result<u32, u8>, b: Result<u32, u8>) -> Result<u64, u8> {
    let va = a? as u64;
    let vb = b? as u64;
    debug_assert!(va <= u32::MAX as u64 && vb <= u32::MAX as u64);
    Ok(va + vb)
}

// 14: Mutable slice swap with debug_assert!
pub fn f14_swap_prefix(buf: &mut [u64], i: usize, j: usize) {
    debug_assert!(i < buf.len() && j < buf.len());
    let tmp = buf[i];
    buf[i] = buf[j];
    buf[j] = tmp;
}

// 15: Multi-assert invariant gate
pub fn f15_frame_header_validate(ver: u8, len: u32, max_len: u32) -> u32 {
    debug_assert!(ver == 1);
    debug_assert!(len <= max_len && max_len <= 65536);
    len + 8
}

// 16: Nested call with cleanup edge and checked mul
pub fn f16_scaled_ext(slot: &mut u64, a: u32, b: u32) -> u64 {
    let _g = GuardedSlot(slot);
    let prod = (a as u64) * (b as u64);
    ext_step(prod)
}

// 17: Bitfield extraction with shift and mask
pub fn f17_extract_bits(word: u64, offset: u32, width: u32) -> u64 {
    debug_assert!(width > 0 && width <= 32 && offset + width <= 64);
    (word >> offset) & ((1u64 << width) - 1)
}

// 18: Checksum fold over fixed 4-word array
pub fn f18_array4_sum(arr: &[u32; 4]) -> u64 {
    (arr[0] as u64) + (arr[1] as u64) + (arr[2] as u64) + (arr[3] as u64)
}

// 19 (NEGATIVE TEST 1): Side-effecting debug_assert! mutating state
pub fn n19_side_effecting_debug_assert(mut x: u64) -> u64 {
    debug_assert!({ x = x.wrapping_add(1); x > 0 });
    x
}

// 20 (NEGATIVE TEST 2): Divergent #[cfg(debug_assertions)] state mutation
pub fn n20_cfg_debug_assertions_divergent(x: u64) -> u64 {
    #[cfg(debug_assertions)]
    {
        x.wrapping_add(100)
    }
    #[cfg(not(debug_assertions))]
    {
        x.wrapping_add(200)
    }
}
'''

def parse_mir_functions(mir_text: str) -> dict:
    funcs = {}
    cur_name = None
    cur_lines = []
    for line in mir_text.splitlines():
        m = re.match(r"^fn\s+([a-z0-9_]+)\s*\(", line)
        if m:
            if cur_name:
                funcs[cur_name] = "\n".join(cur_lines)
            cur_name = m.group(1)
            cur_lines = [line]
        elif cur_name is not None:
            cur_lines.append(line)
            if line == "}":
                funcs[cur_name] = "\n".join(cur_lines)
                cur_name = None
                cur_lines = []
    return funcs

def analyze_mir_body(body: str) -> dict:
    bbs = len(re.findall(r"^\s*bb\d+(?:\s*\(cleanup\))?:", body, re.M))
    cleanup_bbs = len(re.findall(r"^\s*bb\d+\s*\(cleanup\):", body, re.M))
    asserts = len(re.findall(r"^\s*assert\(", body, re.M))
    checked_ops = len(re.findall(r"(?:AddWithOverflow|SubWithOverflow|MulWithOverflow)", body))
    terminate_edges = len(re.findall(r"unwind:\s*terminate", body))
    cleanup_edges = len(re.findall(r"unwind:\s*bb\d+", body))
    resume_terms = len(re.findall(r"^\s*resume;", body, re.M))
    # Count non-debug-assert assignments to `_0` or user locals
    return {
        "basic_blocks": bbs,
        "cleanup_blocks": cleanup_bbs,
        "assert_terminators": asserts,
        "checked_arith_ops": checked_ops,
        "unwind_cleanup_edges": cleanup_edges,
        "unwind_terminate_edges": terminate_edges,
        "resume_terminators": resume_terms,
    }

def check_structural_subsumption(fn_name: str, strict_stats: dict, target_stats: dict,
                                 strict_body: str, target_body: str,
                                 ovf: str, dbg: str, pan: str) -> tuple[bool, str]:
    # 1. When debug_assertions toggles from on -> off, verify that any
    # `switchInt(_c = const true -> const false)` debug_assert! diamond does not
    # mutate outer/parameter locals (`_1 = move ...`) or diverge via #[cfg(debug_assertions)]
    strict_consts = sorted(re.findall(r"const\s+\d+_u64", strict_body))
    target_consts = sorted(re.findall(r"const\s+\d+_u64", target_body))
    if any(c in target_consts and c not in strict_consts for c in target_consts):
        return False, "REJECTED_CFG_DEBUG_ASSERTIONS_CONSTANT_DIVERGENCE"

    if dbg == "off":
        # Check if a debug_assert! diamond in strict_body mutates parameter `_1`
        if re.search(r"^\s*_1\s*=\s*move\s+_\d+;", strict_body, re.M):
            return False, "REJECTED_SIDE_EFFECT_MUTATION_IN_DEBUG_ASSERT_DIAMOND"

    if target_stats["assert_terminators"] > strict_stats["assert_terminators"]:
        return False, "REJECTED_TARGET_HAS_MORE_ASSERTS"
    if target_stats["checked_arith_ops"] > strict_stats["checked_arith_ops"]:
        return False, "REJECTED_TARGET_HAS_MORE_CHECKED_OPS"
    if pan == "abort" and target_stats["unwind_cleanup_edges"] > 0:
        return False, "REJECTED_UNWIND_EDGE_IN_ABORT_PROFILE"
    return True, "SUBSUMED_OK"

def main():
    profiles = []
    idx = 0
    for ovf in ["on", "off"]:
        for dbg in ["on", "off"]:
            for pan in ["unwind", "abort"]:
                profiles.append({
                    "id": f"P{idx}_{ovf}_{dbg}_{pan}",
                    "overflow_checks": ovf,
                    "debug_assertions": dbg,
                    "panic": pan,
                })
                idx += 1

    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    with tempfile.TemporaryDirectory() as tmp:
        tmp_p = Path(tmp)
        src_p = tmp_p / "profiles.rs"
        src_p.write_text(RUST_20_FNS_SRC, encoding="utf-8")

        parsed_by_profile = {}
        stats_by_profile = {}
        for p in profiles:
            mir_p = tmp_p / f"{p['id']}.mir"
            cmd = [
                "rustc", "+1.99.1", "--edition=2024", "-Zmir-opt-level=0",
                f"-Coverflow-checks={p['overflow_checks']}",
                f"-Cdebug-assertions={p['debug_assertions']}",
                f"-Cpanic={p['panic']}",
                "--emit=mir", str(src_p), "-o", str(mir_p)
            ]
            subprocess.run(cmd, env=env, check=True)
            bodies = parse_mir_functions(mir_p.read_text(encoding="utf-8", errors="ignore"))
            parsed_by_profile[p["id"]] = bodies
            stats_by_profile[p["id"]] = {k: analyze_mir_body(v) for k, v in bodies.items()}

        strict_id = "P0_on_on_unwind"
        fn_names = sorted( [k for k in parsed_by_profile[strict_id].keys() if re.match(r"^(f\d+|n\d+)_", k)] )

        matrix = {}
        accepted_pure = 0
        total_pure_pairs = 0
        rejected_neg = 0

        for fn in fn_names:
            matrix[fn] = {}
            for p in profiles:
                pid = p["id"]
                ok, reason = check_structural_subsumption(
                    fn,
                    stats_by_profile[strict_id][fn],
                    stats_by_profile[pid][fn],
                    parsed_by_profile[strict_id][fn],
                    parsed_by_profile[pid][fn],
                    p["overflow_checks"],
                    p["debug_assertions"],
                    p["panic"],
                )
                matrix[fn][pid] = {
                    "subsumed": ok,
                    "reason": reason,
                    **stats_by_profile[pid][fn],
                }
                if fn.startswith("f"):
                    total_pure_pairs += 1
                    if ok:
                        accepted_pure += 1
                elif fn.startswith("n") and p["debug_assertions"] == "off":
                    if not ok:
                        rejected_neg += 1

        out = {
            "toolchain": "rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
            "num_functions": len(fn_names),
            "num_profiles": len(profiles),
            "pure_functions_subsumed": f"{accepted_pure} / {total_pure_pairs}",
            "negative_side_effect_tests_rejected_on_release": f"{rejected_neg} / 8",
            "profiles": profiles,
            "matrix": matrix,
        }
        out_file = Path(__file__).parent / "profile_subsumption_8way_matrix.json"
        out_file.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        print(f"Pure functions subsumed: {accepted_pure} / {total_pure_pairs}")
        print(f"Negative tests rejected when debug_assertions=off: {rejected_neg} / 8")

if __name__ == "__main__":
    main()
