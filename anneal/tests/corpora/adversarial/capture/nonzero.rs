// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Profile v2 now captures these crate-local structs, so every case below
// passes capture as a Profile v2 crate and reaches the proof stage, where the
// corpus's dummy Profile v1 `Specs` cannot instantiate the `SpecsV2` claim.
// None of them exercise semantic `NonZero` niche or validity-invariant
// verification yet; they pin that each candidate `NonZeroUsize` shape is
// captured under Profile v2 (rather than refused or misrouted to Profile v1)
// until invariant verification is implemented.

// === case: struct_captured_v2_nonzero_library ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

/// # Safety
///
/// `x` must not be zero.
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

pub fn get_unchecked(x: NonZeroUsize) -> usize {
    if x.val == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        x.val
    }
}

// === case: struct_captured_v2_zero_returning_safe_ctor ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

// `make_nonzero` breaks the invariant; nothing checks it yet.
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

pub fn make_nonzero(x: usize) -> NonZeroUsize {
    let _ = x;
    NonZeroUsize { val: 0 }
}

/// # Safety
///
/// `x` must not be zero.
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

pub fn get_unchecked(x: NonZeroUsize) -> usize {
    if x.val == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        x.val
    }
}

// === case: struct_captured_v2_pub_field_struct ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

// No field-visibility invariant check runs yet.
#[repr(transparent)]
pub struct NonZeroUsize {
    pub val: usize,
}

pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

/// # Safety
///
/// `x` must not be zero.
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

pub fn get_unchecked(x: NonZeroUsize) -> usize {
    if x.val == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        x.val
    }
}

// === case: struct_captured_v2_zero_returning_unsafe_ctor ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

// No safety or invariant check runs yet.
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    let _ = x;
    NonZeroUsize { val: 0 }
}

// === case: struct_captured_v2_with_requires_clause ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

// Captured; the dummy specification never states this clause.
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// Requires `x != 1` (not stated by the dummy specification).
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

// === case: struct_captured_v2_with_spec_clause ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

// Captured; the dummy specification never states this clause.
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// Ensures `ret == x` (not stated by the dummy specification).
pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

// === case: struct_captured_v2_plain_wrapper ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

#[repr(transparent)]
pub struct Wrapper {
    val: usize,
}

pub fn id(x: usize) -> usize {
    let w = Wrapper { val: x };
    w.val
}
