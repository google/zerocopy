// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: u32_wrapping_add_expr ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.i32 false"
//@ mir-contains: "Trusted.MirAst.BinOp.add"

pub fn add(x: u32, y: u32) -> u32 {
    x + y
}
