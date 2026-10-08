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

//! Small callers of the trusted storage boundaries.
//!
//! The proofs check the callers' guards and results. The interpretations of
//! `transmute_unchecked::<u8, bool>` and `copy_unchecked` remain explicit trusted
//! premises; these harnesses do not prove the union or raw-pointer operations
//! inside those helpers. Both boundaries reject forbidden execution before
//! producing a typed value, even when that value is subsequently discarded.

#![allow(dead_code)]

/// Converts precisely the two valid boolean encodings.
///
/// ```aeneas
/// spec checked_bool_spec
///   ensures(raw) r => r = if byte.val < 2 then some (decide (byte.val = 1)) else none
/// ```
fn checked_bool(byte: u8) -> Option<bool> {
    if byte < 2 {
        // SAFETY: The branch restricts `byte` to 0 or 1, the two boolean bit
        // patterns. Both types have size one, satisfying the helper's size
        // assertion. The trusted interpretation checks this same condition
        // before producing a bool; it cannot silently accept another byte.
        Some(unsafe { super::transmute_unchecked(byte) })
    } else {
        None
    }
}

/// Copies a fitting prefix; failure leaves the destination unchanged.
///
/// The returned state in the extracted model includes the updated destination.
/// Its suffix must be preserved, including when the source is empty.
///
/// ```aeneas
/// spec checked_copy_spec
///   ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
///     out.2.val = if src.val.length ≤ dst.val.length
///       then src.val ++ dst.val.drop src.val.length else dst.val
/// ```
fn checked_copy(src: &[u8], dst: &mut [u8]) -> bool {
    if src.len() <= dst.len() {
        // SAFETY: This branch establishes the helper's sole additional
        // requirement, `src.len() <= dst.len()`. The valid input references
        // supply initialized source bytes and an exclusive destination.
        unsafe { super::copy_unchecked(src, dst) };
        true
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_boolean_bytes() {
        for byte in 0..=u8::MAX {
            assert_eq!(
                checked_bool(byte),
                match byte {
                    0 => Some(false),
                    1 => Some(true),
                    _ => None,
                }
            );
        }
    }

    #[test]
    fn copy_boundaries() {
        for len in 0..=4 {
            let mut dst = [9; 3];
            let src = &[1, 2, 3, 4][..len];
            let fits = checked_copy(src, &mut dst);
            assert_eq!(fits, len <= dst.len());
            if fits {
                assert_eq!(&dst[..len], src);
                assert!(dst[len..].iter().all(|byte| *byte == 9));
            } else {
                assert_eq!(dst, [9; 3]);
            }
        }
    }
}
