// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// All cases below currently fail at MIR capture because `Struct` items are
// rejected (`whole-crate obligation is unsupported: Struct`). None of them
// exercise semantic `NonZero` niche or validity-invariant verification yet;
// they pin the capture-refusal boundary across candidate `NonZeroUsize` shapes
// until struct capture and invariant verification are implemented.

// === case: struct_capture_refused_nonzero_library ===
//@ fail(capture): "NonZeroUsize: whole-crate obligation is unsupported: Struct"

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

// === case: struct_capture_refused_zero_returning_safe_ctor ===
//@ fail(capture): "NonZeroUsize: whole-crate obligation is unsupported: Struct"

// Rejected at `Struct` capture before any invariant check on `make_nonzero`.
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

// === case: struct_capture_refused_pub_field_struct ===
//@ fail(capture): "NonZeroUsize: whole-crate obligation is unsupported: Struct"

// Rejected at `Struct` capture before any field-visibility invariant check.
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

// === case: struct_capture_refused_zero_returning_unsafe_ctor ===
//@ fail(capture): "NonZeroUsize: whole-crate obligation is unsupported: Struct"

// Rejected at `Struct` capture before any safety or invariant check.
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    let _ = x;
    NonZeroUsize { val: 0 }
}

// === case: struct_capture_refused_with_requires_clause ===
//@ fail(capture): "NonZeroUsize: whole-crate obligation is unsupported: Struct"

// Real capture refuses `Struct` before any specification check.
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// Requires `x != 1` (unreachable behind `Struct` refusal).
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

// === case: struct_capture_refused_with_spec_clause ===
//@ fail(capture): "NonZeroUsize: whole-crate obligation is unsupported: Struct"

// Real capture refuses `Struct` before any specification check.
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// Ensures `ret == x` (unreachable behind `Struct` refusal).
pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

// === case: struct_capture_refused_plain_wrapper ===
//@ fail(capture): "Wrapper: whole-crate obligation is unsupported: Struct"

#[repr(transparent)]
pub struct Wrapper {
    val: usize,
}

pub fn id(x: usize) -> usize {
    let w = Wrapper { val: x };
    w.val
}
