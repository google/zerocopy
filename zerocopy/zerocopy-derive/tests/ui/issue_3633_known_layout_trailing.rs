// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(non_camel_case_types)]

extern crate zerocopy_renamed;

fn main() {}

type __Zerocopy_Field_trailer = [u8; 8];

#[derive(zerocopy_derive::KnownLayout)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct Packet {
    prefix: u8,
    trailer: __Zerocopy_Field_trailer,
    //~[msrv, stable, nightly]^ ERROR: cannot derive `KnownLayout` because the unqualified identifier `__Zerocopy_Field_trailer` is reserved for generated code
}
