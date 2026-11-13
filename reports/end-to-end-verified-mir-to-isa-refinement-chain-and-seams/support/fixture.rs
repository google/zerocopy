// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Real Anneal-verified fixtures (`add_bounded` from
//! `theory/Anneal/FunctionalTranslation.lean` @ `a7ac07321` and
//! `alloc_passthrough` from `tests/fixtures/refs.rs` @ `b1f15f743`) carried
//! through the 5-link end-to-end MIR -> W6 -> x86-64 ISA chain.

#![crate_type = "rlib"]
#![no_std]

/// anneal:spec ensures(ret == if x <= 1000 && y <= 1000 { x + y } else { 0 })
#[no_mangle]
pub fn add_bounded(x: usize, y: usize) -> usize {
    if x <= 1000 && y <= 1000 {
        x + y
    } else {
        0
    }
}

/// anneal:spec ensures(ret == x)
#[no_mangle]
pub fn alloc_passthrough(x: usize) -> usize {
    let r = &x;
    *r
}
