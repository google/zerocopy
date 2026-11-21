// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Struct capture is now admitted in Tier 2, while `unreachable_unchecked` and
// `anneal:invariant` validity-invariant directives remain unmodeled. The cases
// below pin that updated boundary across candidate `NonZeroUsize` shapes and
// verify a plain struct wrapper end to end.

// === case: unreachable_unchecked_refused_nonzero_library ===
//@ fail(capture): "external `#[track_caller]` call is unsupported: core::hint::unreachable_unchecked"

/// anneal:invariant val != 0
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
///
/// anneal:requires x != 0
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

// === case: unreachable_unchecked_refused_zero_returning_safe_ctor ===
//@ fail(capture): "external `#[track_caller]` call is unsupported: core::hint::unreachable_unchecked"

// Rejected at `unreachable_unchecked` capture before any invariant check.
/// anneal:invariant val != 0
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
///
/// anneal:requires x != 0
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

// === case: unreachable_unchecked_refused_pub_field_struct ===
//@ fail(capture): "external `#[track_caller]` call is unsupported: core::hint::unreachable_unchecked"

// Rejected at `unreachable_unchecked` capture before any visibility check.
/// anneal:invariant val != 0
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
///
/// anneal:requires x != 0
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

// === case: invariant_directive_refused_zero_returning_unsafe_ctor ===
//@ fail(spec): "unsupported `anneal:` doc directive `anneal:invariant val != 0`"

// Struct capture succeeds; the spec stage rejects `invariant` directives.
/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// anneal:requires x != 0
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    let _ = x;
    NonZeroUsize { val: 0 }
}

// === case: invariant_directive_refused_with_requires_clause ===
//@ fail(spec): "unsupported `anneal:` doc directive `anneal:invariant val != 0`"

// Struct capture succeeds; the spec stage rejects `invariant` directives.
/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// anneal:requires x != 1
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

// === case: invariant_directive_refused_with_spec_clause ===
//@ fail(spec): "unsupported `anneal:` doc directive `anneal:invariant val != 0`"

// Struct capture succeeds; the spec stage rejects `invariant` directives.
/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// anneal:spec ensures(ret == x)
pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

// === case: plain_wrapper_supported ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.adtStruct"
//@ mir-contains: "Trusted.MirAst.AggregateKind.adtStruct"
//@ mir-contains: "Trusted.MirAst.ProjectionElem.field"

#[repr(transparent)]
pub struct Wrapper {
    val: usize,
}

pub fn id(x: usize) -> usize {
    let w = Wrapper { val: x };
    w.val
}
