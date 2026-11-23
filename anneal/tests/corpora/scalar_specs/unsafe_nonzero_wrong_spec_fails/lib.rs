// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: unsafe_nonzero_wrong_spec_fails ===
//@ fail(proof, nonzero_only): "Tactic `rfl` failed"

#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

/// # Safety
///
/// `x` must not be zero.
pub unsafe fn nonzero_only(x: usize) -> usize {
    if x == 0 {
        unsafe { core::intrinsics::unreachable() }
    } else {
        x
    }
}
