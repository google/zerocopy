// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[repr(u8)]
pub enum Tag {
    Zero = 0,
    One = 1,
}

const PATTERN: [u8; 4] = [1, 2, 3, 4];

pub fn pack_le_rev(x: u16) -> [u8; 2] {
    let [b0, b1] = x.to_le_bytes();
    [b1, b0]
}

pub fn repeat_unsize_len(v: u8) -> usize {
    let a = [v; 3];
    let s: &[u8] = &a;
    s.len()
}

pub fn tag_eq(a: &Tag, b: &Tag) -> bool {
    match (a, b) {
        (Tag::Zero, Tag::Zero) | (Tag::One, Tag::One) => true,
        _ => false,
    }
}

pub fn matches_pattern(arr: &[u8; 4]) -> bool {
    *arr == PATTERN
}
