// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `O1a-Dual` ill-formedness and dead-branch const-evaluation fixtures:
// ill-formed `#[repr(...)]` declarations and failing dead-branch const blocks
// must fail closed during capture with zero capture artifacts.

// === case: repr_c_packed_align_conflict ===
//@ fail(capture): "rustc rejected the compilation"

#[repr(C, packed)]
#[repr(align(8))]
pub struct PackedAligned {
    pub x: u32,
}

pub fn id(x: usize) -> usize {
    x
}

// === case: repr_transparent_duplicate ===
//@ fail(capture): "rustc rejected the compilation"

#[repr(transparent, transparent)]
pub struct DuplicateTransparent(pub u32);

pub fn id(x: usize) -> usize {
    x
}

// === case: repr_c_and_transparent_conflict ===
//@ fail(capture): "rustc rejected the compilation"

#[repr(C, transparent)]
pub struct ConflictingTransparent(pub u32);

pub fn id(x: usize) -> usize {
    x
}

// === case: repr_transparent_multi_non_zst ===
//@ fail(capture): "rustc rejected the compilation"

#[repr(transparent)]
pub struct MultiFieldTransparent {
    pub a: u32,
    pub b: u32,
}

pub fn id(x: usize) -> usize {
    x
}

// === case: dead_branch_const_eval_pme ===
//@ fail(capture): "rustc rejected the compilation"

pub fn dead_branch_pme(x: usize) -> usize {
    if false {
        const { assert!(core::mem::size_of::<u8>() == core::mem::size_of::<u16>()) }
    }
    x
}
