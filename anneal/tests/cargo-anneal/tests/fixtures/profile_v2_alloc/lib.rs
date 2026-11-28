// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::ops::Deref;

pub fn vec_and_box_slice() -> (usize, u8, Vec<u8>, Box<[u8]>, Box<[u8]>) {
    let mut src: Vec<u8> = Vec::with_capacity(1);
    src.push(9);

    let mut v: Vec<u8> = Vec::new();
    v.push(10);
    v.extend_from_slice(src.deref());
    let len0 = v.len();
    let x0 = v[0];

    let b: Box<[u8]> = Box::from(v);
    let c: Box<[u8]> = b.clone();
    (len0, x0, src, b, c)
}

pub fn box_new_and_deref() -> (u64, Box<u64>) {
    let b: Box<u64> = Box::new(0x1234);
    let y = *b;
    (y, b)
}

pub unsafe fn vec_with_cap_arg(cap: usize) -> Vec<u8> {
    Vec::with_capacity(cap)
}

pub fn read_slice_and_box_len(s: &[u8], b: &Box<[u8]>) -> (usize, usize) {
    (s.len(), b.len())
}

/// # Safety
///
/// `push` panics with "capacity overflow" when growing `v` would exceed
/// `isize::MAX` bytes, and Profile v2 does not model panics, so the caller
/// must guarantee `2 * v.capacity() < 2^63`.
pub unsafe fn push_one(v: &mut Vec<u8>) {
    v.push(1);
}
