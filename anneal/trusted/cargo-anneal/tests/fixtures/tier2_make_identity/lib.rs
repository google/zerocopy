// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]

pub type BlockIdentity = [u8; 12];

#[inline]
pub fn make_identity(length: u32, level: u64, offset: u64) -> BlockIdentity {
    let [o0, o1, o2, o3, o4, o5, o6, o7] = (offset | level).to_le_bytes();
    let [l0, l1, l2, l3] = length.to_le_bytes();
    [o0, o1, o2, o3, o4, o5, o6, o7, l0, l1, l2, l3]
}
