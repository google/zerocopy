// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: saturating_mul_one_capture_unsupported ===
//@ fail(capture): "mul_one: bb0 terminator: unsupported core call `core::num::<impl usize>::saturating_mul`"

pub fn mul_one(x: usize) -> usize {
    x.saturating_mul(1)
}
