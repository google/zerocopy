// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

pub unsafe fn subslice<'a>(s: &'a [u8], a: usize, b: usize) -> &'a [u8] {
    &s[a..b]
}

pub unsafe fn opt_unwrap(x: Option<u64>) -> u64 {
    x.unwrap()
}

pub fn checked_scalar(a: u64, b: u64, s: u32) -> (bool, u64, u32) {
    let sum = match a.checked_add(b) {
        Some(v) => v,
        None => a.saturating_add(b),
    };
    (b.is_multiple_of(4), core::cmp::min(sum, b), a.wrapping_shl(s).leading_zeros())
}

pub fn slice_and_replace(s: &[u8], dst: &mut u64, next: u64) -> (bool, u64) {
    (s.is_empty(), core::mem::replace(dst, next))
}

pub fn take_option(opt: &mut Option<u64>) -> (bool, Option<u64>) {
    (opt.is_some(), opt.take())
}
