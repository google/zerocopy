// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// `O1a-Dual` closed positive `#![feature(...)]` allowlist, primitive-name
// shadowing, and unmodeled codegen-attribute capture refusal fixtures.

// === case: disallowed_lang_feature_ergonomic_clones ===
//@ fail(capture): "#![feature(ergonomic_clones)] is unsupported during capture"

#![feature(ergonomic_clones)]

pub fn id(x: usize) -> usize {
    x
}

// === case: disallowed_lang_feature_specialization ===
//@ fail(capture): "#![feature(specialization)] is unsupported during capture"

#![feature(specialization)]

pub fn id(x: usize) -> usize {
    x
}

// === case: disallowed_lang_feature_doc_cfg ===
//@ fail(capture): "#![feature(doc_cfg)] is unsupported during capture"

#![feature(doc_cfg)]

pub fn id(x: usize) -> usize {
    x
}

// === case: disallowed_lib_feature_core_intrinsics ===
//@ fail(capture): "#![feature(core_intrinsics)] is unsupported during capture"

#![feature(core_intrinsics)]

pub fn id(x: usize) -> usize {
    x
}

// === case: disallowed_lib_feature_ptr_metadata ===
//@ fail(capture): "#![feature(ptr_metadata)] is unsupported during capture"

#![feature(ptr_metadata)]

pub fn id(x: usize) -> usize {
    x
}

// === case: disallowed_lib_feature_const_eval_select ===
//@ fail(capture): "#![feature(const_eval_select)] is unsupported during capture"

#![feature(const_eval_select)]

pub fn id(x: usize) -> usize {
    x
}

// === case: primitive_shadowing_struct_u8 ===
//@ fail(proof, crate): "Trusted.MirSemantics.SpecsV2"

#[allow(non_camel_case_types)]
pub struct u8(pub u16);

pub fn id(x: u8) -> u16 {
    x.0
}

// === case: primitive_shadowing_enum_usize_with_payload ===
//@ fail(capture): "enum payloads are unsupported"

#[allow(non_camel_case_types)]
pub enum usize {
    A(u16),
    B,
}

pub fn id(_x: usize) -> u16 {
    0
}

// === case: unmodeled_attr_no_mangle ===
//@ fail(capture): "NO_MANGLE"

#[unsafe(no_mangle)]
pub fn exported(x: usize) -> usize {
    x
}

// === case: unmodeled_attr_export_name ===
//@ fail(capture): "exported symbol name"

#[unsafe(export_name = "custom_sym")]
pub fn exported(x: usize) -> usize {
    x
}

// === case: unmodeled_attr_link_section ===
//@ fail(capture): "link section"

#[unsafe(link_section = ".text.custom")]
pub fn placed(x: usize) -> usize {
    x
}

// === case: unmodeled_attr_target_feature ===
//@ fail(capture): "target-feature entry obligations are unsupported"

#[target_feature(enable = "avx2")]
pub fn simd(x: usize) -> usize {
    x
}
