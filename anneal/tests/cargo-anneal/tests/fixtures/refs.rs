// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: alloc_passthrough_with_spec ===
//@ fail(capture): "alloc_passthrough: unsupported type: &'{erased} usize"

/// anneal:spec ensures(ret == x)
pub fn alloc_passthrough(x: usize) -> usize {
    let r = &x;
    *r
}

// === case: alloc_passthrough_unannotated ===
//@ fail(capture): "alloc_passthrough: unsupported type: &'{erased} usize"

pub fn alloc_passthrough(x: usize) -> usize {
    let r = &x;
    *r
}

// === case: wrong_alloc_passthrough ===
//@ fail(capture): "alloc_passthrough: unsupported type: &'{erased} usize"

/// anneal:spec ensures(ret == x)
pub fn alloc_passthrough(x: usize) -> usize {
    let zero = 0usize;
    let r = &zero;
    let _ = x;
    *r
}
