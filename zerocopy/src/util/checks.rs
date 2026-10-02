// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Rust assertions describe the arithmetic promises checked by Aeneas.
//!
//! A total specification with postcondition `True` still requires successful
//! termination: every assertion must pass. The independent calculations below
//! use division and remainder, rather than the production bitwise algorithms.
//! The module is part of the ordinary library so extraction sees exactly the
//! source reviewed here. Its private functions have no runtime callers outside
//! tests; optimized builds can discard them.

// Read the integer explicitly so extraction uses the ordinary scalar remainder
// operation. The proof checks that these guarded arithmetic operations are safe.
#![allow(dead_code, clippy::needless_nonzero_get)]

use core::num::NonZeroUsize;

/// Checks padding and rounding down for every length and supported alignment.
///
/// The explicit guard describes the domain: these helpers require a
/// power-of-two alignment. There is no bound on `len` beyond its Rust type.
/// Neither comparison adds padding to `len`, so `usize::MAX` remains covered.
///
/// ```aeneas
/// spec arithmetic_checks_spec
///   ensures _ => True
/// ```
#[allow(clippy::arithmetic_side_effects)]
fn check_arithmetic(len: usize, align: NonZeroUsize) {
    if !align.get().is_power_of_two() {
        return;
    }
    let remainder = len % align.get();
    let padding = (align.get() - remainder) % align.get();
    assert!(super::padding_needed_for(len, align) == padding);
    assert!(super::round_down_to_next_multiple_of_alignment(len, align) == len - remainder);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_boundaries() {
        for align in [1, 2, 4, 8, 1 << (usize::BITS - 1), 3] {
            let align = NonZeroUsize::new(align).unwrap();
            for len in [0, 1, 7, 8, 9, usize::MAX - 1, usize::MAX] {
                check_arithmetic(len, align);
            }
        }
    }
}
