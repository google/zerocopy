// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: empty_crate_no_pub_fns ===
//@ fail(capture): "captured program contains no executable bodies"

// === case: fieldless_enum_supported ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.enum"
//@ mir-contains: "Trusted.MirAst.Rvalue.discriminant"

pub enum E {
    A,
    B,
}

pub fn tag(e: E) -> usize {
    match e {
        E::A => 0,
        E::B => 1,
    }
}

// === case: enum_payload_rejected ===
//@ fail(capture): "enum payloads are unsupported"

pub enum E {
    A(usize),
    B,
}

pub fn f(_e: E) {}

// === case: unsafe_trait_rejected ===
//@ fail(capture): "whole-crate obligation is unsupported: Trait"

pub unsafe trait Bad {}

pub fn id(x: usize) -> usize {
    x
}

// === case: const_item_rejected ===
//@ fail(capture): "whole-crate obligation is unsupported: Const"

pub const ANSWER: usize = 42;

pub fn id(x: usize) -> usize {
    x
}

// === case: uncalled_private_fn_rejected ===
//@ fail(capture): "unused_bad: unsupported type"

fn unused_bad(r: &usize) -> usize {
    *r
}

pub fn id(x: usize) -> usize {
    let _ = unused_bad as fn(&usize) -> usize;
    x
}

// === case: dead_private_fn_also_rejected ===
//@ fail(capture): "completely_unused: unsupported type"

#[allow(dead_code)]
fn completely_unused(r: &usize) -> usize {
    *r
}

pub fn id(x: usize) -> usize {
    x
}

// === case: include_str_external_file_rejected ===
//@ fail(capture): "undeclared compiler read"

pub fn bad() -> usize {
    let _ = include_str!("../Cargo.toml");
    0
}

// === case: env_macro_rejected ===
//@ fail(capture): "environment-dependent source inputs are unsupported"

#[doc = env!("PATH")]
pub fn id(x: usize) -> usize {
    x
}

// === case: zero_variant_enum_rejected ===
//@ fail(capture): "uninhabited zero-variant enums are unsupported"

pub enum Empty {}

pub fn take_empty(x: Empty) -> usize {
    match x {}
}

// === case: single_variant_enum_supported ===
//@ pass
//@ mir-contains: "Trusted.MirAst.EnumTagRepr.zeroSized"

pub enum Single {
    Only,
}

pub fn take_single(_x: Single) -> usize {
    0
}
