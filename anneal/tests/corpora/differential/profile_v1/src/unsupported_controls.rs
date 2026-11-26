// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Stage-1 Profile v1 explicit conservative `.unsupported` control fixtures.
//!
//! Captured with `Terminator::Unsupported` (`Call { target: None }`) so the
//! Lean verifier fails closed with `.fault .unsupported`.

pub fn abort_control(x: u32) -> u32 {
    if x == 0 {
        std::process::abort()
    } else {
        x + 1
    }
}

pub unsafe fn hint_unreach() -> u32 {
    unsafe { core::hint::unreachable_unchecked() }
}
