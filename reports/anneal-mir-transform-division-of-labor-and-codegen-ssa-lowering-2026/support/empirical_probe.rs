// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Empirical probe exercising `rustc_codegen_ssa` and `rustc_codegen_llvm`
//! MIR-to-LLVM-IR lowering patterns for (`AnLLVM`).

#![no_std]

use core::num::NonZeroU64;

/// 1. `LocalAnalyzer` SSA `OperandRef` vs. `PlaceRef` (`alloca`) classification.
///
/// - Single-assignment dominating temporaries become `LocalRef::Operand`.
/// - Multi-assignment branched locals (`acc`) become `LocalRef::Place` (`alloca`).
/// - Address-taken locals (`pinned`) become `LocalRef::Place` (`alloca`).
#[no_mangle]
pub fn probe_ssa_vs_alloca(cond: bool, x: u64, y: u64) -> u64 {
    let ssa_tmp = x.wrapping_add(1);
    let mut acc = ssa_tmp;
    if cond {
        acc = acc.wrapping_add(y);
    } else {
        acc = acc.wrapping_sub(y);
    }
    let pinned = ssa_tmp;
    let ptr = core::ptr::addr_of!(pinned);
    let loaded = unsafe { *ptr };
    acc.wrapping_add(loaded)
}

/// 2a. `BackendRepr::ScalarPair` for `(u64, u64)`.
#[no_mangle]
pub fn probe_scalar_pair_tuple(pair: (u64, u64)) -> (u64, u64) {
    (pair.1.wrapping_add(1), pair.0)
}

/// 2b. `BackendRepr::ScalarPair` for `&[u8]` (wide pointer: data ptr + len metadata).
#[no_mangle]
pub fn probe_scalar_pair_slice(slice: &[u8]) -> usize {
    slice.len()
}

/// 2c. `BackendRepr::Scalar` and `BackendRepr::ScalarPair` with `NonZeroU64` niche.
#[no_mangle]
pub fn probe_option_nonzero_scalar(opt: Option<NonZeroU64>) -> u64 {
    match opt {
        Some(v) => v.get(),
        None => 0,
    }
}

#[no_mangle]
pub fn probe_option_nonzero_pair(opt: Option<(NonZeroU64, u64)>) -> u64 {
    match opt {
        Some((nz, extra)) => nz.get().wrapping_add(extra),
        None => 0,
    }
}

/// 3. `TagEncoding::Niche` discriminant decode (`codegen_get_discr`) and encode
/// (`codegen_set_discr` / `codegen_tag_value`) with multi-variant niche range.
#[repr(u8)]
#[derive(Copy, Clone)]
pub enum BoundedPayload {
    V10 = 10,
    V11 = 11,
    V12 = 12,
}

#[derive(Copy, Clone)]
pub enum MultiNiche {
    TagA,
    TagB,
    TagC,
    Untagged(BoundedPayload),
}

#[no_mangle]
pub fn probe_multi_niche_decode(val: MultiNiche) -> u8 {
    match val {
        MultiNiche::TagA => 1,
        MultiNiche::TagB => 2,
        MultiNiche::TagC => 3,
        MultiNiche::Untagged(p) => p as u8,
    }
}

#[no_mangle]
pub fn probe_multi_niche_encode(which: u8, p: BoundedPayload) -> MultiNiche {
    match which {
        0 => MultiNiche::TagA,
        1 => MultiNiche::TagB,
        2 => MultiNiche::TagC,
        _ => MultiNiche::Untagged(p),
    }
}

/// 4a. `PassMode::Cast` on a padded `#[repr(C)]` struct (`size = 8, align = 4`,
/// with 3 padding bytes at offsets `1..4`, passed in a single `i64` register
/// under the SysV x86_64 C ABI).
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Padded {
    pub a: u8,
    pub b: u32,
}

#[no_mangle]
pub extern "C" fn probe_pass_mode_cast_modify(mut p: Padded) -> Padded {
    p.a = p.a.wrapping_add(1);
    p.b = p.b.wrapping_add(2);
    p
}

#[no_mangle]
pub extern "C" fn probe_pass_mode_cast_construct(a: u8, b: u32) -> Padded {
    Padded { a, b }
}

#[no_mangle]
pub extern "C" fn probe_pass_mode_cast_caller(a: u8, b: u32) -> Padded {
    let p = Padded { a, b };
    probe_pass_mode_cast_modify(p)
}

/// 4b. `Rvalue::Cast(CastKind::Transmute)` between `(u32, u32)` (`ScalarPair`)
/// and `u64` (`Scalar`), and between `Padded` and `u64`.
#[no_mangle]
pub fn probe_transmute_pair_to_u64(pair: (u32, u32)) -> u64 {
    unsafe { core::mem::transmute::<(u32, u32), u64>(pair) }
}

#[no_mangle]
pub fn probe_transmute_u64_to_pair(bits: u64) -> (u32, u32) {
    unsafe { core::mem::transmute::<u64, (u32, u32)>(bits) }
}

#[no_mangle]
pub fn probe_transmute_padded_to_u64(p: Padded) -> u64 {
    unsafe { core::mem::transmute::<Padded, u64>(p) }
}

/// 5. `CheckedBinaryOp` (`AddWithOverflow`, `MulWithOverflow`) and
/// `TerminatorKind::Assert`.
#[no_mangle]
pub fn probe_checked_arith_and_assert(x: u64, y: u64, z: u64) -> u64 {
    (x + y) * z
}
