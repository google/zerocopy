// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: nested_ref_rejected ===
//@ fail(capture): "outside the Profile v2 type fragment"

/// Nested reference parameter.
pub fn nested_ref_passthrough(r: &&usize, x: usize) -> usize {
    let _ = **r;
    x
}

// === case: mut_str_ref_rejected ===
//@ fail(capture): "outside the Profile v2 type fragment"

/// Only shared `&str` is admitted; `&mut str` stays refused.
pub fn mut_str_passthrough(s: &mut str) -> usize {
    let _ = s;
    0
}

// === case: ptr_to_ref_rejected ===
//@ fail(capture): "outside the Profile v2 type fragment"

pub fn ptr_to_ref_passthrough(p: *const &usize) -> usize {
    let _ = p;
    0
}
