#!/usr/bin/env python3
"""
Measures runtime latency, stack frame size (`sub rsp`), `.text` code size, and
surviving `memcpy` calls across 10 async/await and gen workloads under 5
incremental optimization tiers in rustc 1.99.1 (LLVM 23.1.1).
"""

import json
import os
import re
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

BENCH_RUST_SRC = r'''
#![feature(gen_blocks)]
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

// B01: Channel ping-pong (two alternating awaits per message)
#[inline(always)]
async fn b01_channel_step(v: u64) -> u64 {
    let a = StepYield(1, v + 1).await;
    let b = StepYield(1, a * 3).await;
    b ^ (v >> 1)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b01_channel_ping_pong(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b01_channel_step(acc.wrapping_add(i)));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B02: Buffered stream header/payload parser
#[inline(always)]
async fn b02_parse_frame(seed: u64) -> u64 {
    let mut hdr = [seed, seed + 1, seed + 2, seed + 3];
    let r = &mut hdr;
    r[0] += StepYield(1, 4).await;
    r[1] += StepYield(1, r[0]).await;
    r[2] += StepYield(1, r[1]).await;
    r[0] ^ r[1] ^ r[2] ^ r[3]
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b02_buffered_stream_parse(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b02_parse_frame(acc ^ i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B03: Join4 combinator (4 concurrent child futures polled in lockstep)
#[inline(always)]
async fn b03_join4(x: u64) -> u64 {
    let f1 = StepYield(1, x + 1);
    let f2 = StepYield(1, x + 2);
    let f3 = StepYield(1, x + 3);
    let f4 = StepYield(1, x + 4);
    f1.await + f2.await + f3.await + f4.await
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b03_join4_combinator(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b03_join4(i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B04: Select4 branching state machine
#[inline(always)]
async fn b04_select4(x: u64) -> u64 {
    match x & 3 {
        0 => StepYield(1, x + 10).await,
        1 => {
            let a = StepYield(1, x + 20).await;
            StepYield(1, a + 1).await
        }
        2 => {
            let a = StepYield(1, x + 30).await;
            let b = StepYield(1, a + 2).await;
            StepYield(1, b + 3).await
        }
        _ => StepYield(0, x + 40).await,
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b04_select4_state_machine(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b04_select4(i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B05: 8-layer nested poll chain (poll -> poll -> ... -> poll)
#[inline(always)] async fn l1(x: u64) -> u64 { StepYield(1, x + 1).await }
#[inline(always)] async fn l2(x: u64) -> u64 { l1(x).await + StepYield(1, 2).await }
#[inline(always)] async fn l3(x: u64) -> u64 { l2(x).await + 3 }
#[inline(always)] async fn l4(x: u64) -> u64 { l3(x).await + StepYield(1, 4).await }
#[inline(always)] async fn l5(x: u64) -> u64 { l4(x).await + 5 }
#[inline(always)] async fn l6(x: u64) -> u64 { l5(x).await + StepYield(1, 6).await }
#[inline(always)] async fn l7(x: u64) -> u64 { l6(x).await + 7 }
#[inline(always)] async fn l8(x: u64) -> u64 { l7(x).await + StepYield(1, 8).await }
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b05_deep_nested_poll_depth8(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(l8(i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B06: Large 256-byte frame nested future (tests coroutine SROA + MemCpyOpt)
#[inline(always)]
async fn b06_inner_large(x: u64) -> u64 {
    let buf = [x; 32]; // 256 bytes live across await
    let v = StepYield(1, buf[0]).await;
    buf[31].wrapping_add(v)
}
#[inline(always)]
async fn b06_outer_large(x: u64) -> u64 {
    let a = b06_inner_large(x).await;
    let b = b06_inner_large(a).await;
    b
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b06_large_frame_memcpy_elision(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b06_outer_large(i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B07: gen block Fibonacci iterator fold
#[inline(always)]
gen fn b07_fib_gen(seed: u64) -> u64 {
    let mut a = seed;
    let mut b = seed.wrapping_add(1);
    yield a;
    a = a.wrapping_add(b);
    yield b;
    b = b.wrapping_add(a);
    yield a;
    yield b;
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b07_gen_fibonacci_fold(iters: u64) -> u64 {
    let mut acc = 0u64;
    for i in 0..iters {
        for v in b07_fib_gen(i) {
            acc = acc.wrapping_add(v);
        }
    }
    acc
}

// B08: async gen chunked stream consumer
#[inline(always)]
async fn b08_step(x: u64) -> u64 {
    let mut s = 0u64;
    let v1 = StepYield(1, x + 1).await;
    s += v1;
    let v2 = StepYield(1, x + 2).await;
    s += v2;
    let v3 = StepYield(1, x + 3).await;
    s + v3
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b08_async_gen_chunked_sum(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b08_step(i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B09: Tower-style retry + timeout middleware pipeline
#[inline(always)]
async fn b09_retry_mw(req: u64) -> u64 {
    let r1 = StepYield(1, req).await;
    if r1 & 1 == 0 {
        return r1 + 10;
    }
    let _backoff = StepYield(1, 5).await;
    StepYield(1, req + 20).await
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b09_tower_retry_pipeline(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b09_retry_mw(i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

// B10: Multi-way HTTP/2 frame mux dispatcher (6 suspend states)
#[inline(always)]
async fn b10_h2_mux(tag: u64) -> u64 {
    let s0 = StepYield(1, tag).await;
    let s1 = StepYield(1, s0 ^ 1).await;
    let s2 = StepYield(1, s1 + 3).await;
    let s3 = StepYield(1, s2 ^ 7).await;
    let s4 = StepYield(1, s3 + 11).await;
    let s5 = StepYield(1, s4 ^ 15).await;
    s5
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn run_b10_http2_mux_dispatcher(iters: u64) -> u64 {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut acc = 0u64;
    for i in 0..iters {
        let fut = pin!(b10_h2_mux(i));
        acc = acc.wrapping_add(drive_to_completion(fut, &mut cx));
    }
    acc
}

fn main() {
    let iters = 50_000u64;
    let benches: [(&str, fn(u64) -> u64); 10] = [
        ("B01_channel_ping_pong", run_b01_channel_ping_pong),
        ("B02_buffered_stream_parse", run_b02_buffered_stream_parse),
        ("B03_join4_combinator", run_b03_join4_combinator),
        ("B04_select4_state_machine", run_b04_select4_state_machine),
        ("B05_deep_nested_poll_depth8", run_b05_deep_nested_poll_depth8),
        ("B06_large_frame_memcpy_elision", run_b06_large_frame_memcpy_elision),
        ("B07_gen_fibonacci_fold", run_b07_gen_fibonacci_fold),
        ("B08_async_gen_chunked_sum", run_b08_async_gen_chunked_sum),
        ("B09_tower_retry_pipeline", run_b09_tower_retry_pipeline),
        ("B10_http2_mux_dispatcher", run_b10_http2_mux_dispatcher),
    ];
    for (name, f) in benches {
        // Warmup
        black_box(f(black_box(1_000)));
        let mut samples = Vec::with_capacity(5);
        for _ in 0..5 {
            let t0 = Instant::now();
            let res = black_box(f(black_box(iters)));
            let dt = t0.elapsed().as_nanos() as f64 / 1000.0;
            samples.push((dt, res));
        }
        samples.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        let med_us = samples[2].0;
        let chksum = samples[2].1;
        println!("BENCH|{}|{:.2}|{}", name, med_us, chksum);
    }
}
'''

def parse_asm_metrics(asm_text: str) -> dict:
    # Extract per-benchmark function frame size (`subq $IMM, %rsp`), instructions, and memcpy calls
    funcs = {}
    cur_fn = None
    for line in asm_text.splitlines():
        m_fn = re.match(r"^(run_b\d+_[a-z0-9_]+):", line)
        if m_fn:
            cur_fn = m_fn.group(1)
            funcs[cur_fn] = {"frame_bytes": 0, "memcpy_calls": 0, "inst_count": 0, "indirect_jmps": 0}
            continue
        if cur_fn:
            if line.startswith(".Lfunc_end"):
                cur_fn = None
                continue
            s = line.strip()
            if not s or s.startswith(".") or s.startswith("#") or s.endswith(":"):
                continue
            funcs[cur_fn]["inst_count"] += 1
            m_sub = re.search(r"subq\s+\$(\d+),\s*%rsp", s)
            if m_sub:
                funcs[cur_fn]["frame_bytes"] = max(funcs[cur_fn]["frame_bytes"], int(m_sub.group(1)))
            if "memcpy" in s:
                funcs[cur_fn]["memcpy_calls"] += 1
            if s.startswith("jmpq\t*") or s.startswith("jmp\t*"):
                funcs[cur_fn]["indirect_jmps"] += 1
    return funcs

def run_pipeline_stage(tmp_path: Path, stage_name: str, opt_pipeline: str | None, rustc_opt: str) -> dict:
    asm_path = tmp_path / f"{stage_name}.s"
    obj_path = tmp_path / f"{stage_name}.o"
    bin_path = tmp_path / f"{stage_name}.bin"
    src_path = tmp_path / "bench.rs"

    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    base_cmd = ["rustc", "+1.99.1", "--edition=2024", "-Zmir-opt-level=0", "-Coverflow-checks=off", f"-Copt-level={rustc_opt}", "-Ccodegen-units=1"]
    if opt_pipeline is not None:
        base_cmd += ["-Cno-prepopulate-passes", f"-Cpasses={opt_pipeline}"]

    subprocess.run(base_cmd + ["--emit=asm", str(src_path), "-o", str(asm_path)], cwd=str(tmp_path), env=env, check=True)
    subprocess.run(base_cmd + ["--emit=obj", str(src_path), "-o", str(obj_path)], cwd=str(tmp_path), env=env, check=True)
    subprocess.run(base_cmd + ["--emit=link", str(src_path), "-o", str(bin_path)], cwd=str(tmp_path), env=env, check=True)

    asm_metrics = parse_asm_metrics(asm_path.read_text(encoding="utf-8", errors="ignore"))
    size_out = subprocess.check_output(["size", str(obj_path)], text=True).splitlines()[-1].split()
    text_bytes = int(size_out[0])

    run_out = subprocess.check_output([str(bin_path)], text=True)
    timings = {}
    checksums = {}
    for line in run_out.splitlines():
        if line.startswith("BENCH|"):
            _, bname, us, chk = line.split("|")
            timings[bname] = float(us)
            checksums[bname] = int(chk)

    return {
        "stage": stage_name,
        "text_bytes": text_bytes,
        "timings_us": timings,
        "checksums": checksums,
        "asm_metrics": asm_metrics,
    }

def main():
    stages = [
        ("T0_O0_baseline", None, "0"),
        ("T1_inline_only", "always-inline inline function(dce)", "2"),
        ("T2_inline_sroa_memcpyopt", "always-inline inline function(sroa memcpyopt dse dce)", "2"),
        ("T3_plus_jumpthreading_cvp_simplifycfg", "always-inline inline function(sroa memcpyopt dse jump-threading correlated-propagation simplifycfg instcombine<no-verify-fixpoint> simplifycfg dce)", "2"),
        ("T3b_two_round_sroa_jumpthread_gvn", "always-inline inline function(sroa early-cse jump-threading correlated-propagation simplifycfg instcombine<no-verify-fixpoint> sroa gvn memcpyopt dse jump-threading simplifycfg instcombine<no-verify-fixpoint> dce)", "2"),
        ("T4_full_O3", None, "3"),
    ]

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "bench.rs").write_text(BENCH_RUST_SRC, encoding="utf-8")
        results = []
        for sname, pipe, ropt in stages:
            r = run_pipeline_stage(tmp_path, sname, pipe, ropt)
            results.append(r)

        # Verify checksums match across all 5 stages
        base_chk = results[0]["checksums"]
        for r in results[1:]:
            assert r["checksums"] == base_chk, f"Checksum mismatch in {r['stage']}"

        # Compute geomeans and summaries
        summary_table = []
        for r in results:
            us_vals = list(r["timings_us"].values())
            geomean_us = statistics.geometric_mean(us_vals)
            total_frame = sum(m["frame_bytes"] for m in r["asm_metrics"].values())
            total_memcpy = sum(m["memcpy_calls"] for m in r["asm_metrics"].values())
            total_insts = sum(m["inst_count"] for m in r["asm_metrics"].values())
            summary_table.append({
                "stage": r["stage"],
                "geomean_latency_us": round(geomean_us, 2),
                "total_latency_us": round(sum(us_vals), 2),
                "text_bytes": r["text_bytes"],
                "sum_driver_frame_bytes": total_frame,
                "sum_driver_memcpy_calls": total_memcpy,
                "sum_driver_instructions": total_insts,
            })

        out = {
            "toolchain": "rustc 1.99.1 (LLVM 23.1.1)",
            "iterations_per_benchmark": 50000,
            "summary_by_stage": summary_table,
            "stages": results,
        }
        out_path = Path(__file__).parent / "coroutine_ablation_results.json"
        out_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {out_path}")
        print(json.dumps(summary_table, indent=2))

if __name__ == "__main__":
    main()
