// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Target crate for the `obligation_inventory_probe` `rustc_driver` harness.
//!
//! Exercises all five obligation categories required for exhaustive crate
//! obligation discovery in `rustc 1.99.1 (58cf8f9c3 2026-10-13)`:
//! (a) `unsafe impl` blocks and impl polarities,
//! (b) ADTs, field visibilities, `#[non_exhaustive]`, and `#[unsafe]` fields,
//! (c) trait default methods and safe trait impls on public types,
//! (d) `Drop::drop` impls, drop glue, and compiler shims, and
//! (e) `static`, `const`, and `Body::required_consts` / `mentioned_items`.

#![feature(unsafe_fields, negative_impls)]
#![allow(dead_code, incomplete_features)]

// ============================================================================
// Category (a): `unsafe impl` blocks and impl polarities
// ============================================================================

/// A local unsafe trait with a required method and a default method.
pub unsafe trait LocalUnsafeTrait {
    fn check_invariant(&self) -> bool;

    fn default_unsafe_trait_helper(&self) -> usize {
        if self.check_invariant() { 1 } else { 0 }
    }
}

/// A struct wrapping a raw pointer to test `unsafe impl Send` and `!Sync`.
pub struct RawPtrBox {
    ptr: *mut usize,
}

// Foreign unsafe trait impl (`core::marker::Send`).
unsafe impl Send for RawPtrBox {}

// Negative trait impl (`!core::marker::Sync`).
impl !Sync for RawPtrBox {}

// Local unsafe trait impl on a local type.
unsafe impl LocalUnsafeTrait for RawPtrBox {
    fn check_invariant(&self) -> bool {
        !self.ptr.is_null()
    }
}

/// A generic wrapper with a conditional `unsafe impl`.
pub struct ConditionalWrapper<T>(pub T);

unsafe impl<T: LocalUnsafeTrait> LocalUnsafeTrait for ConditionalWrapper<T> {
    fn check_invariant(&self) -> bool {
        self.0.check_invariant()
    }
}

// ============================================================================
// Category (b): ADTs, field visibilities, `#[non_exhaustive]`, and `#[unsafe]`
// ============================================================================

/// All fields are publicly visible and safe (`allFieldsPubSafe = true`).
pub struct AllPubSafeStruct {
    pub a: usize,
    pub b: bool,
}

/// Has a private field (`allFieldsPubSafe = false`), capable of carrying a
/// custom `AdmissibleAdtInv`.
pub struct EncapsulatedNonZero {
    val: usize,
}

impl EncapsulatedNonZero {
    pub const unsafe fn new_unchecked(val: usize) -> Self {
        Self { val }
    }

    pub fn get(&self) -> usize {
        self.val
    }
}

/// Has a `pub(crate)` field (`allFieldsPubSafe = false` for external callers).
pub struct PubCrateFieldStruct {
    pub(crate) internal: usize,
}

/// A `#[non_exhaustive]` struct whose listed fields are all `pub` safe, yet
/// external callers cannot construct or exhaustively pattern-match it via
/// struct literals (`allFieldsPubSafe = false`).
#[non_exhaustive]
pub struct NonExhaustiveAllPubStruct {
    pub a: usize,
}

/// A struct using `#[unsafe]` fields (RFC 3458 `unsafe_fields`).
pub struct UnsafeFieldStruct {
    pub safe_meta: usize,
    pub unsafe nonzero_inv: usize,
}

/// Unexported inner module versus re-exported inner module items.
mod inner_reexported {
    pub struct ReexportedMixedVis {
        pub pub_field: usize,
        pub(super) super_field: usize,
    }

    pub struct ReexportedAllPub {
        pub x: usize,
    }
}
pub use inner_reexported::{ReexportedAllPub, ReexportedMixedVis};

mod inner_private {
    pub struct UnreachableAllPub {
        pub x: usize,
    }
}

/// A `repr(C)` union (`adt_def.is_union()`).
#[repr(C)]
pub union SampleUnion {
    pub word: usize,
    pub byte: u8,
}

/// A `repr(C)` enum with tuple and struct variants (`adt_def.is_enum()`).
#[repr(C)]
pub enum SampleEnum {
    Empty,
    Tuple(usize),
    Struct { pub_v: usize },
}

// ============================================================================
// Category (c): Trait default methods and safe trait impls on public types
// ============================================================================

/// A local safe trait with a default method that mutates `&mut Self`.
pub trait SafeMutatorTrait {
    fn reset_to_zero(&mut self);

    fn default_zero_out(&mut self) {
        self.reset_to_zero();
    }

    fn overridable_method(&self) -> usize {
        0
    }
}

impl SafeMutatorTrait for EncapsulatedNonZero {
    fn reset_to_zero(&mut self) {
        // Note: A buggy implementation could set `self.val = 0`, violating the
        // non-zero invariant via a trait method or inherited default method!
        self.val = 1;
    }

    fn overridable_method(&self) -> usize {
        self.val
    }
}

impl Clone for EncapsulatedNonZero {
    fn clone(&self) -> Self {
        Self { val: self.val }
    }
    // Inherits `Clone::clone_from(&mut self, source: &Self)` from `core::clone::Clone`!
}

// ============================================================================
// Category (d): `Drop::drop` impls, drop glue, and compiler shims
// ============================================================================

pub struct DropTarget {
    pub state: usize,
}

impl Drop for DropTarget {
    fn drop(&mut self) {
        self.state = 0;
    }
}

/// Has no explicit `Drop` impl, but contains `DropTarget`, so `rustc`
/// synthesizes `InstanceKind::DropGlue` for `OuterWithDropGlue`.
pub struct OuterWithDropGlue {
    pub inner: DropTarget,
    pub tag: usize,
}

/// Exercises `ClosureOnceShim` / `ReifyShim` / `VTableShim` resolution.
pub fn exercise_closures_and_fn_ptrs(x: usize) -> usize {
    let f: fn(usize) -> usize = top_safe_fn;
    let c = |y: usize| y.wrapping_add(x);
    f(c(1))
}

pub fn top_safe_fn(x: usize) -> usize {
    x
}

// ============================================================================
// Category (e): `static`, `const`, and `Body::required_consts` / `mentioned_items`
// ============================================================================

pub const TRIVIAL_CONST: usize = 99;

pub const TOP_LEVEL_CONST: usize = {
    assert!(usize::BITS >= 32);
    42
};

pub static TOP_LEVEL_STATIC: usize = TOP_LEVEL_CONST + 1;

struct PmeAssert<const N: usize>;
impl<const N: usize> PmeAssert<N> {
    const OK: () = assert!(N > 0);
}

const fn pme_checked_helper<const N: usize>() {
    let () = PmeAssert::<N>::OK;
}

/// References both an inline `const { ... }` block and a dead-branch call to
/// `pme_checked_helper::<1>()` to test `required_consts` and `mentioned_items`.
pub fn fn_with_consts_and_dead_branch(x: usize) -> usize {
    const {
        assert!(core::mem::size_of::<usize>() == 8);
    }
    if false {
        pme_checked_helper::<1>();
    }
    x
}
