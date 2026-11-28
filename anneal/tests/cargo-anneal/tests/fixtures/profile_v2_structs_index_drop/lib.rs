// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[derive(PartialEq)]
pub struct Digest(pub [u8; 4]);

pub struct Pair {
    pub tag: u8,
    pub value: u32,
}

pub fn make_pair(tag: u8, value: u32) -> Pair {
    Pair { tag, value }
}

pub fn pair_tag(p: &Pair) -> u8 {
    p.tag
}

pub fn digest_byte(d: &Digest, i: u8) -> u8 {
    d.0[(i & 3) as usize]
}

pub fn digests_differ(a: &Digest, b: &Digest) -> bool {
    *a != *b
}
