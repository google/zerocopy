#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""
Benchmarks Tree Borrows Unwind-Landing-Pad Store Sinking (`SinkStoreToCleanupCert`),
Loop-Carried `&mut T` Promotion (`PromoteProtectedMutInLoopCert`), and Uncompensated
Unwind DSE (`DeleteStoreAcrossUnwindCert`) across 8 workloads in `rustc 1.99.1`
(`LLVM 23.1.1`).
"""

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

RUST_BENCH_SRC = r'''
#![allow(dead_code)]

use std::hint::black_box;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

#[inline(never)]
fn may_unwind_step(v: u64, panic_at: u64) -> u64 {
    if v == panic_at {
        panic!("boom");
    }
    v.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1)
}

// ============================================================================
// W01: Overwritten protected `&mut u64` store across a `may_unwind` call
// ============================================================================
#[unsafe(no_mangle)]
#[inline(never)]
pub fn w01_unopt_unwind(x: &mut u64, v: u64, panic_at: u64) {
    *x = v.wrapping_add(1);
    let r = may_unwind_step(v, panic_at);
    *x = r.wrapping_add(2);
}

struct SinkGuard<'a>(&'a mut u64, u64, bool);
impl<'a> Drop for SinkGuard<'a> {
    #[inline(always)]
    fn drop(&mut self) {
        if self.2 {
            *self.0 = self.1;
        }
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn w01_sunk_to_cleanup(x: &mut u64, v: u64, panic_at: u64) {
    let v1 = v.wrapping_add(1);
    let mut g = SinkGuard(x, v1, true);
    let r = may_unwind_step(v, panic_at);
    g.2 = false;
    *g.0 = r.wrapping_add(2);
}

// ============================================================================
// W02: Loop-carried `*acc: &mut u64` accumulation across `may_unwind` calls
// ============================================================================
#[unsafe(no_mangle)]
#[inline(never)]
pub fn w02_loop_unopt_unwind(acc: &mut u64, n: u64, panic_at: u64) {
    for i in 0..n {
        *acc = (*acc).wrapping_add(i);
        let step = may_unwind_step(i, panic_at);
        *acc = (*acc).wrapping_add(step);
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn w02_loop_promoted_with_cleanup_sink(acc: &mut u64, n: u64, panic_at: u64) {
    let mut phi_acc = *acc;
    struct LoopSink<'a>(&'a mut u64, u64, bool);
    impl<'a> Drop for LoopSink<'a> {
        #[inline(always)]
        fn drop(&mut self) {
            if self.2 {
                *self.0 = self.1;
            }
        }
    }
    let mut guard = LoopSink(acc, phi_acc, true);
    for i in 0..n {
        phi_acc = phi_acc.wrapping_add(i);
        guard.1 = phi_acc;
        let step = may_unwind_step(i, panic_at);
        phi_acc = phi_acc.wrapping_add(step);
    }
    guard.2 = false;
    *guard.0 = phi_acc;
}

// ============================================================================
// W03: Multi-field `&mut Cursor` update across `may_unwind`
// ============================================================================
#[repr(C)]
pub struct Cursor {
    pub pos: u64,
    pub rem: u64,
    pub flags: u64,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn w03_cursor_unopt(c: &mut Cursor, step: u64, panic_at: u64) {
    c.pos = c.pos.wrapping_add(step);
    c.rem = c.rem.wrapping_sub(step);
    c.flags = 1;
    let r = may_unwind_step(step, panic_at);
    c.pos = c.pos.wrapping_add(r);
    c.rem = c.rem.wrapping_sub(1);
    c.flags = 2;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn w03_cursor_sunk(c: &mut Cursor, step: u64, panic_at: u64) {
    let p1 = c.pos.wrapping_add(step);
    let r1 = c.rem.wrapping_sub(step);
    struct CursorSink<'a>(&'a mut Cursor, u64, u64, bool);
    impl<'a> Drop for CursorSink<'a> {
        #[inline(always)]
        fn drop(&mut self) {
            if self.3 {
                self.0.pos = self.1;
                self.0.rem = self.2;
                self.0.flags = 1;
            }
        }
    }
    let mut g = CursorSink(c, p1, r1, true);
    let r = may_unwind_step(step, panic_at);
    g.3 = false;
    g.0.pos = p1.wrapping_add(r);
    g.0.rem = r1.wrapping_sub(1);
    g.0.flags = 2;
}

// ============================================================================
// W04: COND-LOCAL-DROP-OVERWRITE (Local scope guard overwrites `*x` on unwind)
// ============================================================================
#[unsafe(no_mangle)]
#[inline(never)]
pub fn w04_drop_overwrite_unopt(x: &mut u64, v: u64, panic_at: u64) {
    struct RollbackGuard<'a>(&'a mut u64, bool);
    impl<'a> Drop for RollbackGuard<'a> {
        #[inline(always)]
        fn drop(&mut self) {
            if self.1 {
                *self.0 = 0xDEAD_BEEF;
            }
        }
    }
    let mut g = RollbackGuard(x, true);
    *g.0 = v.wrapping_add(10); // Dead on both normal AND unwind paths!
    let r = may_unwind_step(v, panic_at);
    g.1 = false;
    *g.0 = r;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn w04_drop_overwrite_dse(x: &mut u64, v: u64, panic_at: u64) {
    struct RollbackGuard<'a>(&'a mut u64, bool);
    impl<'a> Drop for RollbackGuard<'a> {
        #[inline(always)]
        fn drop(&mut self) {
            if self.1 {
                *self.0 = 0xDEAD_BEEF;
            }
        }
    }
    let mut g = RollbackGuard(x, true);
    let r = may_unwind_step(v, panic_at);
    g.1 = false;
    *g.0 = r;
}

fn main() {
    let iters = 200_000u64;

    // 1. Verify exact equivalence on BOTH normal execution and unwinding catch_unwind!
    for panic_at in [u64::MAX, 5u64] {
        let mut x1 = 100u64;
        let mut x2 = 100u64;
        let r1 = catch_unwind(AssertUnwindSafe(|| {
            for i in 0..10 {
                w01_unopt_unwind(&mut x1, i, panic_at);
            }
        }));
        let r2 = catch_unwind(AssertUnwindSafe(|| {
            for i in 0..10 {
                w01_sunk_to_cleanup(&mut x2, i, panic_at);
            }
        }));
        assert_eq!(r1.is_ok(), r2.is_ok());
        assert_eq!(x1, x2, "W01 mismatch on panic_at={}", panic_at);

        let mut a1 = 7u64;
        let mut a2 = 7u64;
        let l1 = catch_unwind(AssertUnwindSafe(|| w02_loop_unopt_unwind(&mut a1, 10, panic_at)));
        let l2 = catch_unwind(AssertUnwindSafe(|| w02_loop_promoted_with_cleanup_sink(&mut a2, 10, panic_at)));
        assert_eq!(l1.is_ok(), l2.is_ok());
        assert_eq!(a1, a2, "W02 mismatch on panic_at={}", panic_at);

        let mut d1 = 99u64;
        let mut d2 = 99u64;
        let o1 = catch_unwind(AssertUnwindSafe(|| w04_drop_overwrite_unopt(&mut d1, 5, panic_at)));
        let o2 = catch_unwind(AssertUnwindSafe(|| w04_drop_overwrite_dse(&mut d2, 5, panic_at)));
        assert_eq!(o1.is_ok(), o2.is_ok());
        assert_eq!(d1, d2, "W04 mismatch on panic_at={}", panic_at);
    }

    // 2. Benchmark hot-path execution latency (no panic)
    let t0 = Instant::now();
    let mut x = 0u64;
    for i in 0..iters {
        w01_unopt_unwind(black_box(&mut x), black_box(i), u64::MAX);
    }
    let w01_unopt_us = t0.elapsed().as_nanos() as f64 / 1000.0;

    let t0 = Instant::now();
    let mut x = 0u64;
    for i in 0..iters {
        w01_sunk_to_cleanup(black_box(&mut x), black_box(i), u64::MAX);
    }
    let w01_sunk_us = t0.elapsed().as_nanos() as f64 / 1000.0;

    let t0 = Instant::now();
    let mut acc1 = 0u64;
    w02_loop_unopt_unwind(black_box(&mut acc1), black_box(iters), u64::MAX);
    let w02_unopt_us = t0.elapsed().as_nanos() as f64 / 1000.0;

    let t0 = Instant::now();
    let mut acc2 = 0u64;
    w02_loop_promoted_with_cleanup_sink(black_box(&mut acc2), black_box(iters), u64::MAX);
    let w02_sunk_us = t0.elapsed().as_nanos() as f64 / 1000.0;
    assert_eq!(acc1, acc2);

    let t0 = Instant::now();
    let mut c1 = Cursor { pos: 0, rem: iters * 2, flags: 0 };
    for i in 0..iters {
        w03_cursor_unopt(black_box(&mut c1), black_box(i), u64::MAX);
    }
    let w03_unopt_us = t0.elapsed().as_nanos() as f64 / 1000.0;

    let t0 = Instant::now();
    let mut c2 = Cursor { pos: 0, rem: iters * 2, flags: 0 };
    for i in 0..iters {
        w03_cursor_sunk(black_box(&mut c2), black_box(i), u64::MAX);
    }
    let w03_sunk_us = t0.elapsed().as_nanos() as f64 / 1000.0;
    assert_eq!((c1.pos, c1.rem, c1.flags), (c2.pos, c2.rem, c2.flags));

    let t0 = Instant::now();
    let mut d1 = 0u64;
    for i in 0..iters {
        w04_drop_overwrite_unopt(black_box(&mut d1), black_box(i), u64::MAX);
    }
    let w04_unopt_us = t0.elapsed().as_nanos() as f64 / 1000.0;

    let t0 = Instant::now();
    let mut d2 = 0u64;
    for i in 0..iters {
        w04_drop_overwrite_dse(black_box(&mut d2), black_box(i), u64::MAX);
    }
    let w04_dse_us = t0.elapsed().as_nanos() as f64 / 1000.0;
    assert_eq!(d1, d2);

    println!("METRIC|W01|{:.2}|{:.2}", w01_unopt_us, w01_sunk_us);
    println!("METRIC|W02|{:.2}|{:.2}", w02_unopt_us, w02_sunk_us);
    println!("METRIC|W03|{:.2}|{:.2}", w03_unopt_us, w03_sunk_us);
    println!("METRIC|W04|{:.2}|{:.2}", w04_unopt_us, w04_dse_us);
}
'''

def parse_fn_asm(asm_text: str) -> dict:
    funcs = {}
    cur = None
    cur_lines = []
    for line in asm_text.splitlines():
        m = re.match(r"^(w0[1-4]_[a-z0-9_]+):", line)
        if m:
            cur = m.group(1)
            cur_lines = []
            continue
        if cur:
            if line.startswith(".Lfunc_end"):
                # Split cur_lines into blocks at labels `.LBB...:` or `.Ltmp...:`
                # Any block that jumps to `_Unwind_Resume` is a cold cleanup landing pad!
                hot_ptr_stores = 0
                cold_cleanup_stores = 0
                total_insts = 0
                in_cold_pad = False
                for idx, l in enumerate(cur_lines):
                    s = l.strip()
                    if s.startswith(".LBB") and s.endswith(":"):
                        # Look ahead to see if this block reaches _Unwind_Resume before retq
                        rest = "\n".join(cur_lines[idx:])
                        next_ret = rest.find("retq")
                        next_unw = rest.find("_Unwind_Resume")
                        if next_unw != -1 and (next_ret == -1 or next_unw < next_ret):
                            in_cold_pad = True
                        else:
                            in_cold_pad = False
                    if not s or s.startswith(".") or s.startswith("#") or s.endswith(":"):
                        continue
                    total_insts += 1
                    # Count stores to the pointer referent `(%r...)` (excluding `%rsp` stack spills)
                    if re.match(r"^(?:movq|addq)\s+.*,\s*(?:\d+)?\(%r(?!sp)[a-z0-9]+\)", s):
                        if in_cold_pad:
                            cold_cleanup_stores += 1
                        else:
                            hot_ptr_stores += 1
                funcs[cur] = {
                    "hot_referent_stores": hot_ptr_stores,
                    "cold_cleanup_referent_stores": cold_cleanup_stores,
                    "total_insts": total_insts,
                }
                cur = None
                continue
            cur_lines.append(line)
    return funcs

def main():
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    with tempfile.TemporaryDirectory() as tmp:
        tmp_p = Path(tmp)
        src_p = tmp_p / "unwind_bench.rs"
        src_p.write_text(RUST_BENCH_SRC, encoding="utf-8")

        # Compile under -C panic=unwind and -C panic=abort
        asm_unwind = tmp_p / "unwind.s"
        bin_unwind = tmp_p / "unwind.bin"
        asm_abort = tmp_p / "abort.s"

        subprocess.run(
            ["rustc", "+1.99.1", "--edition=2024", "-Copt-level=2", "-Cpanic=unwind",
             "--emit=asm", str(src_p), "-o", str(asm_unwind)],
            env=env, check=True
        )
        subprocess.run(
            ["rustc", "+1.99.1", "--edition=2024", "-Copt-level=2", "-Cpanic=unwind",
             "--emit=link", str(src_p), "-o", str(bin_unwind)],
            env=env, check=True
        )
        subprocess.run(
            ["rustc", "+1.99.1", "--edition=2024", "-Copt-level=2", "-Cpanic=abort",
             "--emit=asm", str(src_p), "-o", str(asm_abort)],
            env=env, check=True
        )

        unwind_asm_metrics = parse_fn_asm(asm_unwind.read_text(encoding="utf-8", errors="ignore"))
        abort_asm_metrics = parse_fn_asm(asm_abort.read_text(encoding="utf-8", errors="ignore"))
        run_out = subprocess.check_output([str(bin_unwind)], text=True).splitlines()
        latencies = {}
        for l in run_out:
            if l.startswith("METRIC|"):
                _, w, unopt_us, opt_us = l.split("|")
                latencies[w] = {
                    "unopt_us": float(unopt_us),
                    "sunk_or_dse_us": float(opt_us),
                    "speedup_ratio": round(float(unopt_us) / max(float(opt_us), 0.01), 3),
                }

        out = {
            "toolchain": "rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67, LLVM 23.1.1)",
            "iterations": 200000,
            "latencies_200k_iters_us": latencies,
            "asm_metrics_panic_unwind": unwind_asm_metrics,
            "asm_metrics_panic_abort": abort_asm_metrics,
        }
        out_file = Path(__file__).parent / "unwind_store_sinking_metrics.json"
        out_file.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
