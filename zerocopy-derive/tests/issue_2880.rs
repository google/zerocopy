// Copyright 2026 The Fuchsia Authors
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

// Original example from #2880

#[derive(imp::KnownLayout, imp::FromBytes)]
#[repr(C)]
pub struct ifaddrmsg {
    pub ifa_family: u8,    /* Address type */
    pub ifa_prefixlen: u8, /* Prefixlength of address */
    pub ifa_flags: u8,     /* Address flags */
    pub ifa_scope: u8,     /* Address scope */
    pub ifa_index: u32,    /* Interface index */
}
