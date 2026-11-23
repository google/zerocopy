// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: signed_i32_id ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.i32 true"

pub fn id_i32(x: i32) -> i32 {
    x
}
