// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Twelve representative `-O3` transformations extracted from `rustc 1.99.1`
//! (bundled LLVM 23.1.1) for evaluating derivation formats (`SimCert`,
//! `RelJudg`, and `HybridTrace`).

#![crate_type = "lib"]
#![allow(clippy::needless_range_loop)]

use std::sync::atomic::{AtomicU64, Ordering};

// 1. Vectorized bounds-checked slice loop with runtime alias check and remainder loop.
// When compiled without strict disjointness guarantees via raw pointers + slice wrapper
// or two slices in an unsafe wrapper, LoopVectorize emits `vector.memcheck` when pointers
// may alias, or uses Rust `&mut`/`&` noalias to go directly to `vector.ph` + `vector.body`
// + scalar remainder loop `for.body`. We include both the safe slice loop and a
// raw-pointer-backed slice loop that forces `SCEV` runtime overlap checks (`vector.memcheck`).
#[no_mangle]
pub unsafe fn t01_vector_slice_loop_with_alias_check(
    dst: *mut u32,
    src: *const u32,
    len: usize,
) {
    let mut i = 0;
    while i < len {
        // Bounds-checked style indexing pattern with potential pointer overlap:
        // LLVM LoopVectorize emits `vector.memcheck` comparing `[dst, dst+4*len)`
        // against `[src, src+4*len)`, then `vector.body` (4x/8x SIMD) and scalar remainder.
        *dst.add(i) = (*src.add(i)).wrapping_mul(3).wrapping_add(7);
        i += 1;
    }
}

#[no_mangle]
pub fn t01b_safe_bounds_checked_slice_loop(dst: &mut [u32], src: &[u32]) -> u32 {
    let n = dst.len().min(src.len());
    let mut acc = 0u32;
    for i in 0..n {
        let v = src[i].wrapping_add(1);
        dst[i] = v;
        acc = acc.wrapping_add(v);
    }
    acc
}

// 2. Devirtualization under LTO (`&dyn Trait` indirect vtable call -> direct inlined op).
pub trait TransformOp {
    fn apply(&self, x: u64) -> u64;
}

pub struct AffineScale {
    pub factor: u64,
    pub bias: u64,
}

impl TransformOp for AffineScale {
    fn apply(&self, x: u64) -> u64 {
        x.wrapping_mul(self.factor).wrapping_add(self.bias)
    }
}

fn invoke_dyn(op: &dyn TransformOp, val: u64) -> u64 {
    op.apply(val)
}

#[no_mangle]
pub fn t02_devirtualize_under_lto(x: u64) -> u64 {
    let op = AffineScale { factor: 13, bias: 29 };
    invoke_dyn(&op, x)
}

// 3. GVN and LICM relying on `noalias` and `readonly`.

#[no_mangle]
pub fn t03_gvn_licm_noalias_readonly(
    out: &mut [u64; 64],
    cfg_weight: &u64,
    scale: &u64,
) -> u64 {
    let mut sum = 0u64;
    for i in 0..64 {
        // Because `out: &mut [u64; 64]` carries `!noalias` disjoint from `cfg_weight: &u64`
        // and `scale: &u64` (`readonly noalias`), GVN + LICM hoist `*cfg_weight + *scale`
        // out of the 64-iteration loop across the store `out[i] = ...`.
        let w = (*cfg_weight).wrapping_mul(*scale);
        out[i] = (i as u64).wrapping_add(w);
        sum = sum.wrapping_add(out[i].wrapping_add(*cfg_weight));
    }
    sum
}

// 4. Inlining across unwinding edges (`invoke` + `landingpad` / `cleanuppad` merge).
pub struct DropGuard<'a> {
    pub slot: &'a mut u64,
}

impl<'a> Drop for DropGuard<'a> {
    fn drop(&mut self) {
        *self.slot = self.slot.wrapping_add(0xDEAD_BEEF);
    }
}

#[inline(always)]
fn may_unwind_inner(x: u64, log: &mut u64) -> u64 {
    let _inner_guard = DropGuard { slot: log };
    if x == 0 {
        panic!("zero input in may_unwind_inner");
    }
    x.wrapping_mul(42)
}

#[no_mangle]
pub fn t04_inline_across_unwinding_edges(x: u64, outer_log: &mut u64, inner_log: &mut u64) -> u64 {
    let _outer_guard = DropGuard { slot: outer_log };
    may_unwind_inner(x, inner_log).wrapping_add(1)
}

// 5. SROA and mem2reg (stack struct/tuple alloca split into SSA registers and phi nodes).
#[derive(Clone, Copy)]
pub struct PacketState {
    pub seq: u64,
    pub flags: u32,
    pub crc: u32,
}

#[no_mangle]
pub fn t05_sroa_and_mem2reg(cond: bool, a: u64, b: u32) -> u64 {
    let mut pkt = PacketState {
        seq: a,
        flags: b,
        crc: b ^ 0x5A5A_5A5A,
    };
    if cond {
        pkt.seq = pkt.seq.wrapping_add(100);
        pkt.flags |= 1;
    } else {
        pkt.seq = pkt.seq.wrapping_sub(50);
        pkt.crc = pkt.crc.wrapping_add(7);
    }
    pkt.seq.wrapping_add((pkt.flags as u64) << 32).wrapping_add(pkt.crc as u64)
}

// 6. Addressing-mode selection (`[base + index * 8 + 32]` complex SIB + displacement).
#[repr(C)]
pub struct HeaderAndTable {
    pub magic: u64,
    pub version: u64,
    pub count: u64,
    pub reserved: u64,
    pub entries: [u64; 256],
}

#[no_mangle]
pub fn t06_addressing_mode_selection(tbl: &HeaderAndTable, idx: usize) -> u64 {
    let bounded = idx & 0xFF;
    // Lowers on x86-64 to `mov rax, qword ptr [rdi + 8*rsi + 32]`
    tbl.entries[bounded].wrapping_add(tbl.version)
}

// 7. Register allocation with spills across an opaque external call in a loop.
extern "C" {
    fn external_clobber_call(x: u64) -> u64;
}

#[no_mangle]
pub unsafe fn t07_regalloc_with_spills(
    a0: u64,
    a1: u64,
    a2: u64,
    a3: u64,
    a4: u64,
    a5: u64,
    n: u64,
) -> u64 {
    let mut v0 = a0.wrapping_add(1);
    let mut v1 = a1.wrapping_add(2);
    let mut v2 = a2.wrapping_add(3);
    let mut v3 = a3.wrapping_add(4);
    let mut v4 = a4.wrapping_add(5);
    let mut v5 = a5.wrapping_add(6);
    let mut v6 = a0 ^ a5;
    let mut i = 0u64;
    while i < n {
        let c = external_clobber_call(i.wrapping_add(v0));
        v0 = v0.wrapping_add(c ^ v6);
        v1 = v1.wrapping_mul(3).wrapping_add(v2);
        v2 = v2.wrapping_add(v3 ^ c);
        v3 = v3.wrapping_add(v4);
        v4 = v4.wrapping_add(v5);
        v5 = v5.wrapping_add(v1);
        v6 = v6.rotate_left(7).wrapping_add(v0);
        i += 1;
    }
    v0 ^ v1 ^ v2 ^ v3 ^ v4 ^ v5 ^ v6
}

// 8. Loop unrolling with induction-variable simplification.
#[no_mangle]
pub fn t08_unroll_and_indvar_simplify(buf: &mut [u64; 16], base: u64, step: u64) -> u64 {
    let mut total = 0u64;
    for i in 0..16 {
        let val = base.wrapping_add((i as u64).wrapping_mul(step));
        buf[i] = val;
        total = total.wrapping_add(val);
    }
    total
}

// 9. Transformation of code with atomics (Relaxed load/store coalescing & Acquire/Release ordering).
#[no_mangle]
pub fn t09_atomics_coalesce_and_reorder(
    counter: &AtomicU64,
    flag: &AtomicU64,
    local_scratch: &mut u64,
) -> u64 {
    *local_scratch = local_scratch.wrapping_add(10);
    let r1 = counter.load(Ordering::Relaxed);
    let r2 = counter.load(Ordering::Relaxed);
    let f = flag.load(Ordering::Acquire);
    *local_scratch = local_scratch.wrapping_add(f);
    counter.store(r1.wrapping_add(r2).wrapping_add(1), Ordering::Relaxed);
    r1.wrapping_add(f)
}

// 10. Valid IEEE-754 floating-point rewrites (exact bitwise fneg cancellation and exact power-of-two scale).
#[no_mangle]
pub fn t10_ieee754_fp_valid_rewrites(x: f64, y: f64) -> f64 {
    let neg_twice = -(-x);
    let mul_two = y * 2.0;
    neg_twice + mul_two
}

// 11. Jump threading across correlated branch conditions.
#[no_mangle]
pub fn t11_jump_threading(x: i32, y: i32) -> i32 {
    let mut state = 0;
    if x > 10 {
        state = 1;
    }
    let intermediate = y.wrapping_add(x);
    if state == 1 {
        intermediate.wrapping_mul(2)
    } else {
        intermediate.wrapping_sub(5)
    }
}

// 12. Function merging (two monomorphized functions with identical machine representation).
#[inline(never)]
pub fn t12_mono_a(slice: &[u32], idx: usize) -> u32 {
    slice.get(idx).copied().unwrap_or(0).wrapping_add(0x1234_5678)
}

#[inline(never)]
pub fn t12_mono_b(slice: &[i32], idx: usize) -> i32 {
    slice.get(idx).copied().unwrap_or(0).wrapping_add(0x1234_5678)
}

#[no_mangle]
pub fn t12_merge_functions_entry(a: &[u32], b: &[i32], i: usize) -> u32 {
    t12_mono_a(a, i).wrapping_add(t12_mono_b(b, i) as u32)
}
