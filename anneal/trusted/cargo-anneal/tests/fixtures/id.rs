// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: annotated_id ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.isize false"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    x
}

// === case: unannotated_id ===
//@ pass

pub fn id(x: usize) -> usize {
    x
}

// === case: id_move_via_local ===
//@ pass
//@ mir-contains: "Trusted.MirAst.StatementKind.storageLive 2"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    let y = x;
    y
}

// === case: const_zero_id_unannotated ===
//@ pass

pub fn id(x: usize) -> usize {
    let _ = x;
    0
}

// === case: wrong_id_returns_zero ===
//@ fail(proof, id): "Val.scalar { width := IntWidth.isize, signed := false, bits := BitVec.ofNat 128 0 } = ret\nbut is expected to have type\n  v = ret"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    let _ = x;
    0
}

// === case: u32_wrapping_add_expr ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.i32 false"
//@ mir-contains: "Trusted.MirAst.BinOp.add"

pub fn add(x: u32, y: u32) -> u32 {
    x + y
}

// === case: safe_fn_with_requires ===
//@ pass
//@ mir-contains: "Trusted.MirAst.TerminatorKind.switchInt"

/// anneal:requires x != 0
/// anneal:spec ensures(ret == x)
pub fn clamp_nonzero(x: usize) -> usize {
    if x == 0 {
        1
    } else {
        x
    }
}

// === case: unsafe_fn_with_requires ===
//@ pass
//@ mir-contains: "isUnsafe := true"
//@ mir-contains: "Trusted.MirAst.TerminatorKind.unreachable"

#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

/// # Safety
///
/// `x` must not be zero.
///
/// anneal:requires x != 0
pub unsafe fn nonzero_only(x: usize) -> usize {
    if x == 0 {
        unsafe { core::intrinsics::unreachable() }
    } else {
        x
    }
}

// === case: safe_fn_requires_cannot_guard_ub ===
//@ fail(proof, bad_ub): "mismatch"
//@ mir-contains: "isUnsafe := false"

#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

/// anneal:requires x != 0
pub fn bad_ub(x: usize) -> usize {
    if x == 0 {
        unsafe { core::intrinsics::unreachable() }
    } else {
        x
    }
}

// === case: unknown_spec_ident_rejected ===
//@ fail(spec): "unknown identifier `y`"

/// anneal:spec ensures(ret == y)
pub fn id(x: usize) -> usize {
    x
}

// === case: unsupported_requires_rejected ===
//@ fail(spec): "unsupported `anneal:requires x != 1`"

/// anneal:requires x != 1
pub fn id(x: usize) -> usize {
    x
}

// === case: signed_i32_id ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.i32 true"

/// anneal:spec ensures(ret == x)
pub fn id_i32(x: i32) -> i32 {
    x
}

// === case: wrapping_add_one_capture_unsupported ===
//@ fail(capture): "add_one: bb0 terminator: unsupported terminator"

pub fn add_one(x: usize) -> usize {
    x.wrapping_add(1)
}
