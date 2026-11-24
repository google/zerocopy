// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

pub fn safe_div_ceil(a: usize, b: usize) -> usize {
    let q = a / b;
    let r = a % b;
    if r != 0 {
        q + 1
    } else {
        q
    }
}

pub fn write_then_div(slot: &mut usize, a: usize, b: usize) -> usize {
    *slot = a;
    a / b
}
