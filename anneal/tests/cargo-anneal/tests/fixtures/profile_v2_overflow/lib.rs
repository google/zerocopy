// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

/// Saturating increment: the `x < 255` guard makes the overflow check of
/// `x + 1` unreachable, so this never panics under `-Coverflow-checks=yes`.
pub fn guarded_add_u8(x: u8) -> u8 {
    if x < 255 { x + 1 } else { 255 }
}

/// Unguarded increment: wraps `255` to `0` without overflow checks, and
/// panics on `255` with them.
pub fn buggy_add_u8(x: u8) -> u8 {
    x + 1
}

/// Returns a tuple, which only Profile v2 models. Capturing it next to
/// `buggy_add_u8` keeps the program on Profile v2 even when overflow checks
/// are off and `buggy_add_u8` contains no `Assert`.
pub fn zero_pair() -> (u8, u8) {
    (0, 0)
}
