// Copyright 2025 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_implicit_prelude]
#![deny(non_ascii_idents)]
#![allow(dead_code)]

include!("include.rs");

// NOTE: We don't derive `FromBytes` because that would result in a trivial
// `is_bit_valid` impl, which would fail to test most or all of the problematic
// generated code.

#[derive(imp::KnownLayout, imp::IntoBytes, imp::Immutable)]
#[repr(C)]
struct TestStruct {
    a: u8,
}

#[derive(imp::KnownLayout, imp::IntoBytes, imp::Immutable)]
#[repr(u8)]
enum TestEnum {
    A = 0,
}

#[derive(imp::KnownLayout, imp::IntoBytes, imp::Immutable)]
#[repr(C)]
union TestUnion {
    a: u8,
}
