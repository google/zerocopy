// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: wrong_id_returns_zero ===
//@ fail(proof, id): "is not definitionally equal to the right-hand side"

pub fn id(x: usize) -> usize {
    let _ = x;
    0
}
