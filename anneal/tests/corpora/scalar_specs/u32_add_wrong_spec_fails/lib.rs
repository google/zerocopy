// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: u32_add_wrong_spec_fails ===
//@ fail(proof, add): "Tactic `rfl` failed"

pub fn add(x: u32, y: u32) -> u32 {
    x + y
}
