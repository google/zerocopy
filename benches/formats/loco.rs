// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use zerocopy_derive::*;

#[derive(FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct Packet {
    magic_number: [u8; 2],
    mug_size: u8,
    temperature: u8,
    marshmallows: [[u8; 2]],
}
