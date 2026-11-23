// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: safe_fn_requires_cannot_guard_ub ===
//@ fail(proof, bad_ub): "Tactic `rfl` failed"
//@ mir-contains: "isUnsafe := false"

#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

pub fn bad_ub(x: usize) -> usize {
    if x == 0 {
        unsafe { core::intrinsics::unreachable() }
    } else {
        x
    }
}
