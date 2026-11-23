// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: id_move_via_local ===
//@ pass
//@ mir-contains: "Trusted.MirAst.StatementKind.storageLive 2"

pub fn id(x: usize) -> usize {
    let y = x;
    y
}
