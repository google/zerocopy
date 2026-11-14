#!/usr/bin/env python3
"""
Empirical census of 50 representative async/await, gen, async gen, and Coroutine
state machines compiled with rustc 1.99.1 at Runtime(PostCleanup) (-Zmir-opt-level=0).
Extracts pre-StateTransform and post-StateTransform (resume + drop) MIR CFGs,
suspension point counts, SwitchInt dispatch targets, cleanup blocks, and
-Zprint-type-sizes layout packing ratios.
"""

import json
import os
import re
import shutil
import statistics
import subprocess
import tempfile
from pathlib import Path

RUST_SOURCE = r'''
#![feature(coroutines, coroutine_trait, gen_blocks, async_iterator)]
#![allow(dead_code, unused_variables, unused_assignments)]

use core::future::Future;
use core::iter::Iterator;
use core::ops::{Coroutine, CoroutineState};
use core::pin::Pin;
use core::task::{Context, Poll};

pub struct YieldOnce(pub bool);
impl Future for YieldOnce {
    type Output = u64;
    #[inline(never)]
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        if self.0 {
            Poll::Ready(1)
        } else {
            self.0 = true;
            Poll::Pending
        }
    }
}

pub struct DropTracker(pub u64);
impl Drop for DropTracker {
    #[inline(never)]
    fn drop(&mut self) {}
}

#[inline(never)]
pub async fn yield_u64(v: u64) -> u64 {
    YieldOnce(false).await + v
}

// 1-10: Core async fn and self-referential borrow patterns
pub async fn c01_trivial_ready(x: u64) -> u64 { x + 1 }
pub async fn c02_single_await(x: u64) -> u64 { yield_u64(x).await }
pub async fn c03_self_ref_shared(x: u64) -> u64 {
    let local_buf = [x, x + 1, x + 2, x + 3];
    let r: &[u64; 4] = &local_buf;
    let y = yield_u64(r[0]).await;
    r[1] + r[2] + r[3] + y
}
pub async fn c04_self_ref_mut(x: u64) -> u64 {
    let mut local_buf = [x, x + 1, x + 2, x + 3];
    let r: &mut [u64; 4] = &mut local_buf;
    r[0] += 10;
    let y = yield_u64(r[0]).await;
    r[1] += y;
    local_buf[0] + local_buf[1]
}
pub async fn c05_self_ref_split_struct(x: u64) -> u64 {
    struct Pair { a: [u64; 4], b: [u64; 4] }
    let mut p = Pair { a: [x; 4], b: [x + 1; 4] };
    let ra = &mut p.a;
    let y = yield_u64(ra[0]).await;
    p.b[0] += y;
    ra[1] += p.b[0];
    ra[1]
}
pub async fn c06_disjoint_scopes_storage_overlap(x: u64) -> u64 {
    let a = {
        let buf1 = [x; 16];
        let v = yield_u64(buf1[0]).await;
        buf1[15] + v
    };
    let b = {
        let buf2 = [a; 16];
        let v = yield_u64(buf2[0]).await;
        buf2[15] + v
    };
    let c = {
        let buf3 = [b; 16];
        let v = yield_u64(buf3[0]).await;
        buf3[15] + v
    };
    c
}
pub async fn c07_drop_across_three_awaits(x: u64) -> u64 {
    let d1 = DropTracker(x);
    let a = yield_u64(d1.0).await;
    let d2 = DropTracker(a);
    let b = yield_u64(d2.0).await;
    drop(d1);
    let d3 = DropTracker(b);
    let c = yield_u64(d3.0).await;
    c + d2.0 + d3.0
}
pub async fn c08_loop_with_await_and_drop(mut n: u64) -> u64 {
    let mut acc = 0;
    while n > 0 {
        let guard = DropTracker(n);
        acc += yield_u64(guard.0).await;
        n -= 1;
    }
    acc
}
pub async fn c09_branching_awaits(x: u64) -> u64 {
    if x % 2 == 0 {
        let buf_even = [x; 8];
        yield_u64(buf_even[0]).await + buf_even[7]
    } else {
        let buf_odd = [x; 12];
        let a = yield_u64(buf_odd[0]).await;
        yield_u64(a + buf_odd[11]).await
    }
}
pub async fn c10_array_index_across_yield(x: u64, idx: usize) -> u64 {
    let arr = [x, x + 1, x + 2, x + 3, x + 4, x + 5, x + 6, x + 7];
    let saved_idx = idx & 7;
    let v = yield_u64(x).await;
    arr[saved_idx] + v
}

// 11-20: Tokio-style runtime primitives (timers, channels, I/O copy, mutex, semaphore, task spawn)
pub async fn c11_tokio_sleep_retry(attempts: u32) -> Result<u64, u32> {
    let mut i = 0;
    while i < attempts {
        let v = yield_u64(i as u64).await;
        if v > 10 { return Ok(v); }
        let _backoff = yield_u64(100 * (i as u64)).await;
        i += 1;
    }
    Err(attempts)
}
pub async fn c12_tokio_mpsc_send_batch(items: &[u64]) -> u64 {
    let mut sent = 0;
    for &item in items {
        let _permit = yield_u64(item).await;
        sent += 1;
    }
    sent
}
pub async fn c13_tokio_oneshot_recv_timeout(x: u64) -> Result<u64, ()> {
    let a = yield_u64(x).await;
    if a == 0 { return Err(()); }
    let b = yield_u64(a).await;
    Ok(b)
}
pub async fn c14_tokio_io_copy_loop(mut remaining: usize) -> usize {
    let mut buf = [0u8; 256];
    let mut total = 0;
    while remaining > 0 {
        let n_read = yield_u64(buf[0] as u64).await as usize;
        if n_read == 0 { break; }
        buf[0] = (n_read & 0xff) as u8;
        let mut written = 0;
        while written < n_read {
            let nw = yield_u64(written as u64).await as usize;
            written += nw.max(1);
        }
        total += n_read;
        remaining = remaining.saturating_sub(n_read);
    }
    total
}
pub async fn c15_tokio_mutex_lock_and_update(x: u64) -> u64 {
    let _waiter = DropTracker(x);
    let mut state = yield_u64(x).await;
    state += 1;
    let flushed = yield_u64(state).await;
    flushed
}
pub async fn c16_tokio_rwlock_upgrade_flow(x: u64) -> u64 {
    let r_guard = DropTracker(x);
    let v1 = yield_u64(r_guard.0).await;
    drop(r_guard);
    let w_guard = DropTracker(v1);
    let v2 = yield_u64(w_guard.0).await;
    let v3 = yield_u64(v2).await;
    v3
}
pub async fn c17_tokio_semaphore_acquire_many(n: u32) -> u64 {
    let waiter1 = DropTracker(n as u64);
    let p1 = yield_u64(waiter1.0).await;
    let p2 = yield_u64(p1).await;
    let p3 = yield_u64(p2).await;
    p3
}
pub async fn c18_tokio_broadcast_recv_lagged(mut seq: u64) -> u64 {
    loop {
        let msg = yield_u64(seq).await;
        if msg == seq + 1 {
            return msg;
        } else if msg > seq + 1 {
            seq = yield_u64(msg).await;
        } else {
            return 0;
        }
    }
}
pub async fn c19_tokio_watch_changed(mut cur: u64) -> u64 {
    let v1 = yield_u64(cur).await;
    cur = v1;
    let v2 = yield_u64(cur).await;
    cur + v2
}
pub async fn c20_tokio_join_handle_await(id: u64) -> Result<u64, u64> {
    let g = DropTracker(id);
    let status = yield_u64(g.0).await;
    if status == 1 {
        Ok(yield_u64(status).await)
    } else {
        Err(status)
    }
}

// 21-30: Hyper-style HTTP/1.1 & HTTP/2 protocol state machines
pub async fn c21_hyper_http1_parse_headers(mut cursor: usize) -> Result<usize, u32> {
    let mut header_buf = [0u64; 16];
    for slot in header_buf.iter_mut() {
        let b = yield_u64(cursor as u64).await;
        if b == 0 { return Err(400); }
        *slot = b;
        cursor += 1;
        if b == 13 { break; }
    }
    Ok(cursor)
}
pub async fn c22_hyper_http1_chunked_body(mut chunks: usize) -> u64 {
    let mut total = 0;
    while chunks > 0 {
        let hdr = yield_u64(chunks as u64).await;
        if hdr == 0 { break; }
        let payload = yield_u64(hdr).await;
        let crlf = yield_u64(payload).await;
        total += payload + crlf;
        chunks -= 1;
    }
    let _trailers = yield_u64(total).await;
    total
}
pub async fn c23_hyper_http2_frame_dispatcher(mut frames: u32) -> u64 {
    let mut window: i64 = 65535;
    let mut processed = 0;
    while frames > 0 {
        let ftype = yield_u64(frames as u64).await;
        match ftype & 3 {
            0 => {
                let sz = yield_u64(ftype).await as i64;
                window -= sz;
                if window < 16384 {
                    let _upd = yield_u64(window as u64).await;
                    window += 32768;
                }
            }
            1 => {
                let _hdrs = yield_u64(ftype + 1).await;
                let _cont = yield_u64(ftype + 2).await;
            }
            2 => {
                let _ping_ack = yield_u64(ftype + 3).await;
            }
            _ => {
                let _goaway = yield_u64(ftype + 4).await;
                break;
            }
        }
        processed += 1;
        frames -= 1;
    }
    processed
}
pub async fn c24_hyper_client_pool_checkout(key: u64) -> u64 {
    let lookup = yield_u64(key).await;
    if lookup != 0 { return lookup; }
    let dns = yield_u64(key + 1).await;
    let tcp = yield_u64(dns).await;
    let tls = yield_u64(tcp).await;
    let handshake = yield_u64(tls).await;
    handshake
}
pub async fn c25_hyper_server_graceful_shutdown(active: u32) -> u64 {
    let sig = yield_u64(active as u64).await;
    let drain1 = yield_u64(sig).await;
    let drain2 = yield_u64(drain1).await;
    let force_close = yield_u64(drain2).await;
    force_close
}
pub async fn c26_hyper_upgrade_websocket(req_id: u64) -> u64 {
    let hdr = yield_u64(req_id).await;
    let resp = yield_u64(hdr).await;
    let detach = yield_u64(resp).await;
    let frame1 = yield_u64(detach).await;
    let close = yield_u64(frame1).await;
    close
}
pub async fn c27_hyper_body_to_bytes_limit(limit: usize) -> Result<usize, ()> {
    let mut collected = 0usize;
    let mut scratch = [0u64; 8];
    loop {
        let chunk = yield_u64(collected as u64).await as usize;
        if chunk == 0 { return Ok(collected); }
        if collected + chunk > limit { return Err(()); }
        scratch[collected & 7] = chunk as u64;
        collected += chunk;
        let _ack = yield_u64(scratch[collected & 7]).await;
    }
}
pub async fn c28_hyper_tower_retry_middleware(req: u64) -> u64 {
    let mut try_no = 0;
    loop {
        let g = DropTracker(try_no);
        let r = yield_u64(req + try_no).await;
        if r % 2 == 0 || try_no >= 3 { return r; }
        let _sleep = yield_u64(try_no * 10).await;
        let _clone = yield_u64(r).await;
        try_no += 1;
    }
}
pub async fn c29_hyper_h2_stream_send_data(mut bytes: usize) -> usize {
    let mut sent = 0;
    while bytes > 0 {
        let cap = yield_u64(bytes as u64).await as usize;
        let chunk = bytes.min(cap.max(1));
        let _write = yield_u64(chunk as u64).await;
        let _flush = yield_u64(sent as u64).await;
        bytes -= chunk;
        sent += chunk;
    }
    sent
}
pub async fn c30_hyper_keepalive_idle_timer(conn: u64) -> u64 {
    let r1 = yield_u64(conn).await;
    let r2 = yield_u64(r1).await;
    let r3 = yield_u64(r2).await;
    let r4 = yield_u64(r3).await;
    let r5 = yield_u64(r4).await;
    let r6 = yield_u64(r5).await;
    r6
}

// 31-40: Deeply nested Future combinator chains (4 to 10 layers of poll -> poll -> poll)
pub async fn c31_nested_depth2(x: u64) -> u64 {
    c02_single_await(x).await + c03_self_ref_shared(x).await
}
pub async fn c32_nested_depth3(x: u64) -> u64 {
    let a = c31_nested_depth2(x).await;
    c04_self_ref_mut(a).await
}
pub async fn c33_nested_depth4(x: u64) -> u64 {
    let a = c32_nested_depth3(x).await;
    c05_self_ref_split_struct(a).await
}
pub async fn c34_nested_depth5(x: u64) -> u64 {
    let a = c33_nested_depth4(x).await;
    c06_disjoint_scopes_storage_overlap(a).await
}
pub async fn c35_nested_depth6(x: u64) -> u64 {
    let a = c34_nested_depth5(x).await;
    c07_drop_across_three_awaits(a).await
}
pub async fn c36_nested_depth7(x: u64) -> u64 {
    let a = c35_nested_depth6(x).await;
    c09_branching_awaits(a).await
}
pub async fn c37_nested_depth8(x: u64) -> u64 {
    let a = c36_nested_depth7(x).await;
    c11_tokio_sleep_retry(a as u32).await.unwrap_or(0)
}
pub async fn c38_nested_depth9(x: u64) -> u64 {
    let a = c37_nested_depth8(x).await;
    c16_tokio_rwlock_upgrade_flow(a).await
}
pub async fn c39_nested_depth10(x: u64) -> u64 {
    let a = c38_nested_depth9(x).await;
    c24_hyper_client_pool_checkout(a).await
}
pub async fn c40_select_four_branches(x: u64) -> u64 {
    let b1 = c03_self_ref_shared(x).await;
    let b2 = c04_self_ref_mut(b1).await;
    let b3 = c07_drop_across_three_awaits(b2).await;
    let b4 = c22_hyper_http1_chunked_body(b3 as usize).await;
    b4
}

// 41-50: gen fn, gen blocks, async gen, and explicit Coroutine closures
pub gen fn c41_gen_range_step(mut start: u64, end: u64) -> u64 {
    while start < end {
        yield start;
        start += 1;
    }
}
pub gen fn c42_gen_fibonacci(n: u32) -> u64 {
    let (mut a, mut b) = (0u64, 1u64);
    let mut i = 0;
    while i < n {
        yield a;
        let next = a.wrapping_add(b);
        a = b;
        b = next;
        i += 1;
    }
}
pub gen fn c43_gen_with_drop_guards(x: u64) -> u64 {
    let g1 = DropTracker(x);
    yield g1.0;
    let g2 = DropTracker(x + 1);
    yield g1.0 + g2.0;
    drop(g1);
    yield g2.0 * 2;
}
pub gen fn c44_gen_disjoint_buffers(x: u64) -> u64 {
    {
        let b1 = [x; 8];
        yield b1[0] + b1[7];
    }
    {
        let b2 = [x + 1; 8];
        yield b2[0] + b2[7];
    }
}
pub async gen fn c45_async_gen_stream(mut count: u64) -> u64 {
    while count > 0 {
        let item = yield_u64(count).await;
        yield item;
        count -= 1;
    }
}
pub async gen fn c46_async_gen_buffered_chunks(x: u64) -> u64 {
    let buf = [x, x + 1, x + 2, x + 3];
    let r = &buf;
    let a = yield_u64(r[0]).await;
    yield a + r[1];
    let b = yield_u64(r[2]).await;
    yield b + r[3];
}
pub fn c47_raw_coroutine_movable(x: u64) -> impl Coroutine<u64, Yield = u64, Return = u64> {
    #[coroutine]
    move |mut r: u64| {
        let a = yield x + r;
        r = a;
        let b = yield x + r + 1;
        b + x
    }
}
pub fn c48_raw_coroutine_self_ref_static(x: u64) -> impl Coroutine<(), Yield = u64, Return = u64> {
    #[coroutine]
    static move |()| {
        let mut arr = [x, x + 10, x + 20, x + 30];
        let ptr: &mut [u64; 4] = &mut arr;
        ptr[0] += 1;
        yield ptr[0];
        ptr[1] += ptr[0];
        yield ptr[1];
        ptr[2] + ptr[3]
    }
}
pub async fn c49_ten_sequential_suspends(mut x: u64) -> u64 {
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x = yield_u64(x).await;
    x
}
pub async fn c50_twenty_suspend_state_machine(mut x: u64) -> u64 {
    let mut g = DropTracker(x);
    x = yield_u64(x + 1).await;
    x = yield_u64(x + 2).await;
    x = yield_u64(x + 3).await;
    x = yield_u64(x + 4).await;
    x = yield_u64(x + 5).await;
    x = yield_u64(x + 6).await;
    x = yield_u64(x + 7).await;
    x = yield_u64(x + 8).await;
    x = yield_u64(x + 9).await;
    x = yield_u64(x + 10).await;
    x = yield_u64(x + 11).await;
    x = yield_u64(x + 12).await;
    x = yield_u64(x + 13).await;
    x = yield_u64(x + 14).await;
    x = yield_u64(x + 15).await;
    x = yield_u64(x + 16).await;
    x = yield_u64(x + 17).await;
    x = yield_u64(x + 18).await;
    x = yield_u64(x + 19).await;
    x = yield_u64(x + 20).await;
    g.0 = x;
    g.0
}

pub fn size_align_pair<T>(v: &T) -> (usize, usize) {
    (core::mem::size_of_val(v), core::mem::align_of_val(v))
}

#[unsafe(no_mangle)]
pub fn touch_all() -> usize {
    let mut sum = 0usize;
    macro_rules! measure {
        ($e:expr) => {{
            let mut v = $e;
            let (s, a) = size_align_pair(&v);
            sum = sum.wrapping_add(s).wrapping_add(a);
            unsafe { core::ptr::drop_in_place(&mut v); }
            core::mem::forget(v);
        }};
    }
    measure!(c01_trivial_ready(1));
    measure!(c02_single_await(1));
    measure!(c03_self_ref_shared(1));
    measure!(c04_self_ref_mut(1));
    measure!(c05_self_ref_split_struct(1));
    measure!(c06_disjoint_scopes_storage_overlap(1));
    measure!(c07_drop_across_three_awaits(1));
    measure!(c08_loop_with_await_and_drop(1));
    measure!(c09_branching_awaits(1));
    measure!(c10_array_index_across_yield(1, 0));
    measure!(c11_tokio_sleep_retry(1));
    measure!(c12_tokio_mpsc_send_batch(&[1]));
    measure!(c13_tokio_oneshot_recv_timeout(1));
    measure!(c14_tokio_io_copy_loop(1));
    measure!(c15_tokio_mutex_lock_and_update(1));
    measure!(c16_tokio_rwlock_upgrade_flow(1));
    measure!(c17_tokio_semaphore_acquire_many(1));
    measure!(c18_tokio_broadcast_recv_lagged(1));
    measure!(c19_tokio_watch_changed(1));
    measure!(c20_tokio_join_handle_await(1));
    measure!(c21_hyper_http1_parse_headers(1));
    measure!(c22_hyper_http1_chunked_body(1));
    measure!(c23_hyper_http2_frame_dispatcher(1));
    measure!(c24_hyper_client_pool_checkout(1));
    measure!(c25_hyper_server_graceful_shutdown(1));
    measure!(c26_hyper_upgrade_websocket(1));
    measure!(c27_hyper_body_to_bytes_limit(1));
    measure!(c28_hyper_tower_retry_middleware(1));
    measure!(c29_hyper_h2_stream_send_data(1));
    measure!(c30_hyper_keepalive_idle_timer(1));
    measure!(c31_nested_depth2(1));
    measure!(c32_nested_depth3(1));
    measure!(c33_nested_depth4(1));
    measure!(c34_nested_depth5(1));
    measure!(c35_nested_depth6(1));
    measure!(c36_nested_depth7(1));
    measure!(c37_nested_depth8(1));
    measure!(c38_nested_depth9(1));
    measure!(c39_nested_depth10(1));
    measure!(c40_select_four_branches(1));
    measure!(c41_gen_range_step(0, 5));
    measure!(c42_gen_fibonacci(5));
    measure!(c43_gen_with_drop_guards(1));
    measure!(c44_gen_disjoint_buffers(1));
    measure!(c45_async_gen_stream(3));
    measure!(c46_async_gen_buffered_chunks(1));
    measure!(c47_raw_coroutine_movable(1));
    measure!(c48_raw_coroutine_self_ref_static(1));
    measure!(c49_ten_sequential_suspends(1));
    measure!(c50_twenty_suspend_state_machine(1));
    sum
}
'''

def parse_mir_file(path: Path) -> dict:
    text = path.read_text(encoding="utf-8", errors="ignore")
    bbs = re.findall(r"^\s*bb(\d+)\s*(\(cleanup\))?\s*:\s*\{", text, re.MULTILINE)
    total_bbs = len(bbs)
    cleanup_bbs = sum(1 for _, c in bbs if c)
    yield_count = len(re.findall(r"=\s*yield\(", text))
    set_discr = re.findall(r"discriminant\(\(\*_?\d+\)\)\s*=\s*(\d+)", text)
    switch_ints = len(re.findall(r"switchInt\(", text))
    storage_live = len(re.findall(r"StorageLive\(", text))
    storage_dead = len(re.findall(r"StorageDead\(", text))
    drops = len(re.findall(r"^\s*drop\(", text, re.MULTILINE))
    return {
        "total_bbs": total_bbs,
        "cleanup_bbs": cleanup_bbs,
        "yield_count": yield_count,
        "set_discr_variants": sorted(set(int(x) for x in set_discr)),
        "switch_ints": switch_ints,
        "storage_live": storage_live,
        "storage_dead": storage_dead,
        "drops": drops,
    }

def main():
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src_file = tmp_path / "coroutines.rs"
        src_file.write_text(RUST_SOURCE, encoding="utf-8")
        mir_dir = tmp_path / "mir_dump"
        mir_dir.mkdir()

        cmd = [
            "rustc", "+1.99.1",
            "--edition=2024",
            "--crate-type=lib",
            "--emit=obj",
            "-Zunstable-options",
            "-Zmir-opt-level=0",
            f"-Zdump-mir=StateTransform|coroutine_drop",
            f"-Zdump-mir-dir={mir_dir}",
            "-Zprint-type-sizes",
            str(src_file),
            "-o", str(tmp_path / "libcoroutines.rlib"),
        ]
        env = dict(os.environ, RUSTC_BOOTSTRAP="1")
        res = subprocess.run(cmd, capture_output=True, text=True, env=env)
        if res.returncode != 0:
            print(res.stderr)
            raise RuntimeError("rustc failed")
        type_sizes_out = res.stdout + "\n" + res.stderr

        # Parse -Zprint-type-sizes for coroutine layouts
        type_info = {}
        current_name = None
        for line in type_sizes_out.splitlines():
            m = re.match(r"print-type-size type: `([^`]+)`: (\d+) bytes, alignment: (\d+) bytes", line)
            if m:
                tname, sz, al = m.group(1), int(m.group(2)), int(m.group(3))
                if tname.startswith("{coroutine@"):
                    current_name = "c47_raw_coroutine_movable"
                    type_info[current_name] = {
                        "type_name": "{coroutine@coroutines.rs:c47}",
                        "size_bytes": sz,
                        "align_bytes": al,
                        "variants": [],
                    }
                    continue
                if tname.startswith("{static coroutine@"):
                    current_name = "c48_raw_coroutine_self_ref_static"
                    type_info[current_name] = {
                        "type_name": "{static coroutine@coroutines.rs:c48}",
                        "size_bytes": sz,
                        "align_bytes": al,
                        "variants": [],
                    }
                    continue
                if tname.startswith("{") and "body of c" in tname:
                    m_c = re.search(r"(c\d+_[a-z0-9_]+)", tname)
                    if m_c:
                        current_name = m_c.group(1)
                        type_info[current_name] = {
                            "type_name": tname,
                            "size_bytes": sz,
                            "align_bytes": al,
                            "variants": [],
                        }
                        continue
                current_name = None
            elif current_name:
                m_var = re.search(r"variant `([^`]+)`: (\d+) bytes", line)
                if m_var:
                    type_info[current_name]["variants"].append({
                        "name": m_var.group(1),
                        "size_bytes": int(m_var.group(2)),
                    })

        # Match MIR files per c01..c50
        records = []
        for idx in range(1, 51):
            prefix = f"c{idx:02d}_"
            before_files = sorted(mir_dir.glob(f"*{prefix}*StateTransform.before.mir"))
            after_files = sorted(mir_dir.glob(f"*{prefix}*StateTransform.after.mir"))
            resume_files = sorted(mir_dir.glob(f"*{prefix}*coroutine_resume.0.mir"))
            drop_files = sorted(mir_dir.glob(f"*{prefix}*coroutine_drop.0.mir"))

            # Pick the closure/coroutine body file (contains {async_fn#0}, {gen_fn#0}, {async_gen_fn#0}, or {closure#0})
            def pick_closure(files):
                for f in files:
                    if any(k in f.name for k in ("async_fn", "gen_fn", "async_gen_fn", "closure")):
                        return f
                return files[-1] if files else None

            bf = pick_closure(before_files)
            af = pick_closure(after_files) or pick_closure(resume_files)
            df = pick_closure(drop_files)

            cname = None
            for k in type_info:
                if k.startswith(prefix):
                    cname = k
                    break
            if not cname and bf:
                m_n = re.search(r"(c\d+_[a-z0-9_]+)", bf.name)
                cname = m_n.group(1) if m_n else prefix

            before_stats = parse_mir_file(bf) if bf else {}
            after_stats = parse_mir_file(af) if af else {}
            drop_stats = parse_mir_file(df) if df else {}

            tinfo = type_info.get(cname, {"size_bytes": 0, "align_bytes": 1, "variants": []})
            suspend_variants = [v for v in tinfo.get("variants", []) if v["name"].startswith("Suspend")]
            sum_variant_bytes = sum(v["size_bytes"] for v in suspend_variants)
            max_variant_bytes = max((v["size_bytes"] for v in suspend_variants), default=0)

            kind = "async_fn"
            if "_gen_" in cname and "async_gen" not in cname:
                kind = "gen_fn"
            elif "async_gen" in cname:
                kind = "async_gen_fn"
            elif "raw_coroutine" in cname:
                kind = "coroutine_closure"

            records.append({
                "id": f"c{idx:02d}",
                "name": cname,
                "kind": kind,
                "suspend_points_K": before_stats.get("yield_count", len(suspend_variants)),
                "bb_before": before_stats.get("total_bbs", 0),
                "bb_resume_after": after_stats.get("total_bbs", 0),
                "bb_cleanup_after": after_stats.get("cleanup_bbs", 0),
                "bb_drop_shim": drop_stats.get("total_bbs", 0),
                "size_bytes": tinfo.get("size_bytes", 0),
                "align_bytes": tinfo.get("align_bytes", 1),
                "num_variants_total": len(tinfo.get("variants", [])),
                "sum_suspend_variant_payload_bytes": sum_variant_bytes,
                "max_suspend_variant_payload_bytes": max_variant_bytes,
                "storage_live_after": after_stats.get("storage_live", 0),
                "storage_dead_after": after_stats.get("storage_dead", 0),
                "set_discr_variants": after_stats.get("set_discr_variants", []),
            })

        bbs_after = [r["bb_resume_after"] for r in records]
        ks = [r["suspend_points_K"] for r in records]
        sizes = [r["size_bytes"] for r in records]

        out = {
            "toolchain": "rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
            "total_coroutines_analyzed": len(records),
            "summary": {
                "suspend_points_min": min(ks),
                "suspend_points_median": statistics.median(ks),
                "suspend_points_max": max(ks),
                "suspend_points_total": sum(ks),
                "bb_resume_min": min(bbs_after),
                "bb_resume_median": statistics.median(bbs_after),
                "bb_resume_max": max(bbs_after),
                "bb_drop_shim_median": statistics.median([r["bb_drop_shim"] for r in records]),
                "size_bytes_min": min(sizes),
                "size_bytes_median": statistics.median(sizes),
                "size_bytes_max": max(sizes),
            },
            "coroutines": records,
        }
        out_path = Path(__file__).parent / "coroutine_mir_census.json"
        out_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {out_path} ({len(records)} coroutines)")
        print("Summary:", json.dumps(out["summary"], indent=2))

if __name__ == "__main__":
    main()
