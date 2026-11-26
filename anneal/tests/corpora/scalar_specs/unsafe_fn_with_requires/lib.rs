// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: unsafe_fn_with_requires ===
//@ pass
//@ mir-contains: "isUnsafe := true"
//@ mir-contains: "Trusted.MirAst.TerminatorKind.sysrootCall"

#![no_std]

/// # Safety
///
/// `x` must not be zero.
pub unsafe fn nonzero_only(x: usize) -> usize {
    if x == 0 {
        unsafe { usize::MAX.unchecked_add(1) }
    } else {
        x
    }
}
