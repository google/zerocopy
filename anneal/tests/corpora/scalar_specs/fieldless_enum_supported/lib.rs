// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: fieldless_enum_supported ===
//@ pass
//@ mir-contains: "Trusted.MirAst.MirTy.enum"
//@ mir-contains: "Trusted.MirAst.Rvalue.discriminant"

pub enum E {
    A,
    B,
}

pub fn tag(e: E) -> usize {
    match e {
        E::A => 0,
        E::B => 1,
    }
}
