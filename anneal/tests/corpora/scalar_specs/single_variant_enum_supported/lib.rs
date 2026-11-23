// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: single_variant_enum_supported ===
//@ pass
//@ mir-contains: "Trusted.MirAst.EnumTagRepr.zeroSized"

pub enum Single {
    Only,
}

pub fn take_single(_x: Single) -> usize {
    0
}
