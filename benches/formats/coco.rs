// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy_derive::*;

// The only valid value of this type is the byte `0xC0`
#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(u8)]
enum C0 {
    _XC0 = 0xC0,
}

// The only valid value of this type is the bytes `0xC0C0`.
#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(C)]
struct C0C0(C0, C0);

#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct Packet {
    magic_number: C0C0,
    mug_size: u8,
    temperature: u8,
    marshmallows: [[u8; 2]],
}
