// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

pub fn zero() -> u64 {
    helper()
}

// `saturating_mul` is refused under every MIR profile, so selecting `zero`
// pulls in an unsupported dependency.
fn helper() -> u64 {
    0u64.saturating_mul(0)
}
