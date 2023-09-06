// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use super::*;

// A `u64` with alignment 8.
//
// Though `u64` has alignment 8 on some platforms, it's not guaranteed.
// By contrast, `AU64` is guaranteed to have alignment 8.
#[derive(
    FromZeroes, FromBytes, AsBytes, Eq, PartialEq, Ord, PartialOrd, Default, Debug, Copy, Clone,
)]
#[repr(C, align(8))]
pub(crate) struct AU64(pub(crate) u64);

impl AU64 {
    // Converts `self` using this platform's endianness.
    pub(crate) fn to_bytes(self) -> [u8; 8] {
        transmute!(self)
    }
}

impl Display for AU64 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}
