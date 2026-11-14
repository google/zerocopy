#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""
Benchmarks Field-Disjoint `!Unpin` Coroutine Frame Slicing (`PinFieldSplitCert`)
and Unresumed Child-Future `MemCpyOpt` (`UnresumedMoveIsRelocatable`) across
`B02_buffered_stream_parse` and 5 nested `!Unpin` async stream/codec workloads
in `rustc 1.99.1` (`LLVM 23.1.1`).
"""

import json
import os
import re
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

RUST_BENCH_SRC = r'''
#![allow(dead_code, unused_variables)]

use std::future::Future;
use std::hint::black_box;
use std::pin::{Pin, pin};
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::time::Instant;

fn noop_waker() -> Waker {
    fn no_op(_: *const ()) {}
    fn clone(_: *const ()) -> RawWaker { RawWaker::new(core::ptr::null(), &VTABLE) }
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

struct StepYield(u32, u64);
impl Future for StepYield {
    type Output = u64;
    #[inline(always)]
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        if self.0 == 0 {
            Poll::Ready(self.1)
        } else {
            self.0 -= 1;
            Poll::Pending
        }
    }
}

#[inline(always)]
fn drive_to_completion<F: Future>(mut fut: Pin<&mut F>, cx: &mut Context<'_>) -> F::Output {
    loop {
        if let Poll::Ready(v) = fut.as_mut().poll(cx) {
            return v;
        }
    }
}

// ============================================================================
// 1. B02_buffered_stream_parse (from Wave 5 N7)
// Unsplit: `let r = &mut hdr;` across 3 awaits keeps an 80 B coroutine frame
// at T3b because whole-alloca SROA sees the stored interior reference `r`.
// PinFieldSplit: isolates `hdr: [u64; 4]` (32 B pinned slot) from the scalar
// state/yield fields (promoted to SSA registers), and forwards single-base
// `r[k]` to `hdr[k]`.
// ============================================================================

#[inline(always)]
async fn b02_unsplit_coro(seed: u64) -> u64 {
    let mut hdr = [seed, seed + 1, seed + 2, seed + 3];
    let r = &mut hdr;
    r[0] += StepYield(1, 4).await;
    r[1] += StepYield(1, r[0]).await;
    r[2] += StepYield(1, r[1]).await;
    r[0] ^ r[1] ^ r[2] ^ r[3]
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c01_b02_unsplit(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b02_unsplit_coro(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// PinFieldSplit (32 B pinned `hdr` slot + scalar SSA registers for state/temporaries,
// before single-base interior pointer forwarding)
#[repr(C)]
struct PinnedHdr32([u64; 4]);

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c01_b02_split_32b(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let seed = acc ^ i;
        let mut pinned_hdr = PinnedHdr32([seed, seed + 1, seed + 2, seed + 3]);
        let r_ptr: *mut [u64; 4] = black_box(&raw mut pinned_hdr.0);
        let mut state = 0u32;
        let mut child = StepYield(1, 4);
        let out = loop {
            match state {
                0 => {
                    if let Poll::Ready(v) = Pin::new(&mut child).poll(&mut cx) {
                        let h0 = unsafe { (*r_ptr)[0].wrapping_add(v) };
                        unsafe { (*r_ptr)[0] = h0 };
                        child = StepYield(1, h0);
                        state = 1;
                    }
                }
                1 => {
                    if let Poll::Ready(v) = Pin::new(&mut child).poll(&mut cx) {
                        let h1 = unsafe { (*r_ptr)[1].wrapping_add(v) };
                        unsafe { (*r_ptr)[1] = h1 };
                        child = StepYield(1, h1);
                        state = 2;
                    }
                }
                _ => {
                    if let Poll::Ready(v) = Pin::new(&mut child).poll(&mut cx) {
                        unsafe {
                            (*r_ptr)[2] = (*r_ptr)[2].wrapping_add(v);
                            break (*r_ptr)[0] ^ (*r_ptr)[1] ^ (*r_ptr)[2] ^ (*r_ptr)[3];
                        }
                    }
                }
            }
        };
        acc = acc.wrapping_add(out);
    }
    acc
}

// PinFieldSplit + single-base interior pointer forwarding (`r_ptr == &mut hdr` -> `0 B` frame)
#[inline(always)]
async fn b02_split_forwarded_coro(seed: u64) -> u64 {
    let mut hdr0 = seed;
    let mut hdr1 = seed + 1;
    let mut hdr2 = seed + 2;
    let hdr3 = seed + 3;
    hdr0 += StepYield(1, 4).await;
    hdr1 += StepYield(1, hdr0).await;
    hdr2 += StepYield(1, hdr1).await;
    hdr0 ^ hdr1 ^ hdr2 ^ hdr3
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c01_b02_split_0b(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b02_split_forwarded_coro(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// ============================================================================
// 2. C02_framed_codec_varint: 32 B scratch buffer + 6 scalar codec fields
// ============================================================================
#[inline(always)]
async fn c02_unsplit_codec(seed: u64) -> u64 {
    let mut scratch = [seed, seed ^ 0x55, seed.wrapping_mul(3), seed.wrapping_add(7)];
    let slice_ref: &mut [u64; 4] = &mut scratch;
    let mut pos: usize = 0;
    let mut rem: usize = 4;
    let mut tag_acc: u64 = 17;
    let mut limit: u64 = 1024;
    let v0 = StepYield(1, slice_ref[pos]).await;
    slice_ref[0] = v0.wrapping_add(tag_acc);
    pos += 1;
    rem -= 1;
    let v1 = StepYield(1, slice_ref[pos] ^ (rem as u64)).await;
    slice_ref[1] = v1.wrapping_add(limit);
    tag_acc = tag_acc.wrapping_add(slice_ref[0] ^ slice_ref[1]);
    limit -= 1;
    let v2 = StepYield(1, tag_acc).await;
    slice_ref[2] = slice_ref[2].wrapping_add(v2 ^ limit);
    slice_ref[0] ^ slice_ref[1] ^ slice_ref[2] ^ slice_ref[3] ^ (pos as u64) ^ (rem as u64)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c02_codec_unsplit(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(c02_unsplit_codec(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

#[inline(always)]
async fn c02_split_codec(seed: u64) -> u64 {
    let mut s0 = seed;
    let mut s1 = seed ^ 0x55;
    let mut s2 = seed.wrapping_mul(3);
    let s3 = seed.wrapping_add(7);
    let mut pos: usize = 0;
    let mut rem: usize = 4;
    let mut tag_acc: u64 = 17;
    let mut limit: u64 = 1024;
    let v0 = StepYield(1, s0).await;
    s0 = v0.wrapping_add(tag_acc);
    pos += 1;
    rem -= 1;
    let v1 = StepYield(1, s1 ^ (rem as u64)).await;
    s1 = v1.wrapping_add(limit);
    tag_acc = tag_acc.wrapping_add(s0 ^ s1);
    limit -= 1;
    let v2 = StepYield(1, tag_acc).await;
    s2 = s2.wrapping_add(v2 ^ limit);
    s0 ^ s1 ^ s2 ^ s3 ^ (pos as u64) ^ (rem as u64)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c02_codec_split(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(c02_split_codec(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// ============================================================================
// 3. C03_nested_unresumed_child_placement: Nested !Unpin child futures
// ============================================================================
#[inline(always)]
async fn c03_inner_unpin_child(x: u64) -> u64 {
    let mut local_buf = [x, x + 1, x + 2, x + 3];
    let p = &mut local_buf;
    p[0] += StepYield(1, 9).await;
    p[1] += StepYield(1, p[0]).await;
    p[0] ^ p[1] ^ p[2] ^ p[3]
}

#[inline(always)]
async fn c03_outer_unsplit(x: u64) -> u64 {
    let a = c03_inner_unpin_child(x).await;
    let b = c03_inner_unpin_child(a).await;
    b
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c03_nested_unsplit(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(c03_outer_unsplit(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

#[inline(always)]
async fn c03_inner_split(x: u64) -> u64 {
    let mut b0 = x;
    let mut b1 = x + 1;
    let b2 = x + 2;
    let b3 = x + 3;
    b0 += StepYield(1, 9).await;
    b1 += StepYield(1, b0).await;
    b0 ^ b1 ^ b2 ^ b3
}

#[inline(always)]
async fn c03_outer_split(x: u64) -> u64 {
    let a = c03_inner_split(x).await;
    let b = c03_inner_split(a).await;
    b
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c03_nested_split(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(c03_outer_split(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// ============================================================================
// 4. C04_ring_window_checksum: 64 B ring window + 4 scalar cursors
// ============================================================================
#[inline(always)]
async fn c04_ring_unsplit(seed: u64) -> u64 {
    let mut win = [seed; 8];
    let r = &mut win;
    let mut head = 0usize;
    let mut sum = 0u64;
    let v1 = StepYield(1, r[head]).await;
    r[0] = v1;
    head = 1;
    sum = sum.wrapping_add(v1);
    let v2 = StepYield(1, r[head]).await;
    r[1] = v2;
    sum = sum.wrapping_add(v2 ^ r[7]);
    sum ^ r[0] ^ r[1]
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c04_ring_unsplit(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(c04_ring_unsplit(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

#[inline(always)]
async fn c04_ring_split(seed: u64) -> u64 {
    let mut w0 = seed;
    let mut w1 = seed;
    let w7 = seed;
    let mut sum = 0u64;
    let v1 = StepYield(1, w0).await;
    w0 = v1;
    sum = sum.wrapping_add(v1);
    let v2 = StepYield(1, w1).await;
    w1 = v2;
    sum = sum.wrapping_add(v2 ^ w7);
    sum ^ w0 ^ w1
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_c04_ring_split(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(c04_ring_split(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

fn main() {
    let iters = 50_000u64;
    let fns: [(&str, fn(u64) -> u64); 9] = [
        ("C01_B02_unsplit", run_c01_b02_unsplit),
        ("C01_B02_split_32b", run_c01_b02_split_32b),
        ("C01_B02_split_0b", run_c01_b02_split_0b),
        ("C02_codec_unsplit", run_c02_codec_unsplit),
        ("C02_codec_split", run_c02_codec_split),
        ("C03_nested_unsplit", run_c03_nested_unsplit),
        ("C03_nested_split", run_c03_nested_split),
        ("C04_ring_unsplit", run_c04_ring_unsplit),
        ("C04_ring_split", run_c04_ring_split),
    ];
    for (name, f) in fns {
        black_box(f(black_box(1_000)));
        let mut samples = Vec::with_capacity(5);
        for _ in 0..5 {
            let t0 = Instant::now();
            let res = black_box(f(black_box(iters)));
            let dt = t0.elapsed().as_nanos() as f64 / 1000.0;
            samples.push((dt, res));
        }
        samples.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        println!("RES|{}|{:.2}|{}", name, samples[2].0, samples[2].1);
    }
}
'''

def parse_asm(asm_text: str) -> dict:
    funcs = {}
    cur = None
    for line in asm_text.splitlines():
        m = re.match(r"^(run_c0[1-4]_[a-z0-9_]+):", line)
        if m:
            cur = m.group(1)
            funcs[cur] = {"frame_bytes": 0, "inst_count": 0, "memcpy_calls": 0}
            continue
        if cur:
            if line.startswith(".Lfunc_end"):
                cur = None
                continue
            s = line.strip()
            if not s or s.startswith(".") or s.startswith("#") or s.endswith(":"):
                continue
            funcs[cur]["inst_count"] += 1
            m_sub = re.search(r"subq\s+\$(\d+),\s*%rsp", s)
            if m_sub:
                funcs[cur]["frame_bytes"] = max(funcs[cur]["frame_bytes"], int(m_sub.group(1)))
            if "memcpy" in s:
                funcs[cur]["memcpy_calls"] += 1
    return funcs

def main():
    t3b_pipe = (
        "always-inline inline function("
        "sroa early-cse jump-threading correlated-propagation simplifycfg "
        "instcombine<no-verify-fixpoint> sroa gvn memcpyopt dse "
        "jump-threading simplifycfg instcombine<no-verify-fixpoint> dce)"
    )
    stages = [
        ("T0_O0_baseline", None, "0"),
        ("T3b_two_round_sroa_jumpthread_gvn", t3b_pipe, "2"),
        ("T4_full_O3", None, "3"),
    ]
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src_path = tmp_path / "bench.rs"
        src_path.write_text(RUST_BENCH_SRC, encoding="utf-8")

        stage_results = {}
        for sname, pipe, opt_lvl in stages:
            asm_p = tmp_path / f"{sname}.s"
            bin_p = tmp_path / f"{sname}.bin"
            cmd = [
                "rustc", "+1.99.1", "--edition=2024", "-Zmir-opt-level=0",
                "-Coverflow-checks=off", f"-Copt-level={opt_lvl}", "-Ccodegen-units=1"
            ]
            if pipe:
                cmd += ["-Cno-prepopulate-passes", f"-Cpasses={pipe}"]
            subprocess.run(cmd + ["--emit=asm", str(src_path), "-o", str(asm_p)], env=env, check=True)
            subprocess.run(cmd + ["--emit=link", str(src_path), "-o", str(bin_p)], env=env, check=True)
            asm_metrics = parse_asm(asm_p.read_text(encoding="utf-8", errors="ignore"))
            out_lines = subprocess.check_output([str(bin_p)], text=True).splitlines()
            timings = {}
            checksums = {}
            for l in out_lines:
                if l.startswith("RES|"):
                    _, k, us, chk = l.split("|")
                    timings[k] = float(us)
                    checksums[k] = int(chk)
            # Verify split and unsplit checksums agree identically!
            assert checksums["C01_B02_unsplit"] == checksums["C01_B02_split_32b"] == checksums["C01_B02_split_0b"]
            assert checksums["C02_codec_unsplit"] == checksums["C02_codec_split"]
            assert checksums["C03_nested_unsplit"] == checksums["C03_nested_split"]
            assert checksums["C04_ring_unsplit"] == checksums["C04_ring_split"]
            stage_results[sname] = {
                "timings_us": timings,
                "checksums": checksums,
                "asm_metrics": asm_metrics,
            }

        out_json = {
            "toolchain": "rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67, LLVM 23.1.1)",
            "iterations": 50000,
            "stages": stage_results,
        }
        out_file = Path(__file__).parent / "coroutine_pin_sroa_results.json"
        out_file.write_text(json.dumps(out_json, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(out_json, indent=2))

if __name__ == "__main__":
    main()
