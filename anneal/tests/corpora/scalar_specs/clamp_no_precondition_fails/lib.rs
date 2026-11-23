// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: clamp_no_precondition_fails ===
//@ fail(proof, clamp_nonzero): "Tactic `rfl` failed"

pub fn clamp_nonzero(x: usize) -> usize {
    if x == 0 {
        1
    } else {
        x
    }
}
