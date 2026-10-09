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
    if super::validity::bool_encoding(byte) {
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

/// Checks the same scalar predicate used by `NonZero`'s validator, then
/// constructs a nonzero word. Zero remains representable at the input boundary.
///
/// ```aeneas
/// spec checked_nonzero_spec
///   ensures(raw) r => match r with
///     | none => n.val = 0
///     | some value => value.val = n ∧ 0 < value.val.val
/// ```
fn checked_nonzero(n: usize) -> Option<core::num::NonZeroUsize> {
    if super::validity::nonzero_encoding(n) {
        core::num::NonZeroUsize::new(n)
    } else {
        None
    }
}

/// Converts two raw candidate bytes using the checked scalar conversion.
/// Invalid candidates are never constructed as bools, even transiently.
///
/// ```aeneas
/// spec checked_bool_pair_spec
///   ensures(raw) r => match r with
///     | none => ∃ byte ∈ bytes.val, 2 ≤ byte.val
///     | some values => values.val = bytes.val.map (fun byte => decide (byte.val = 1)) ∧
///         ∀ byte ∈ bytes.val, byte.val < 2
/// ```
#[allow(clippy::question_mark)] // Keep branches first-order instead of using a Try dictionary.
fn checked_bool_pair(bytes: [u8; 2]) -> Option<[bool; 2]> {
    let left = super::validity::read_byte(&bytes, 0);
    let right = super::validity::read_byte(&bytes, 1);
    let left = if let Some(left) = checked_bool(left) { left } else { return None };
    let right = if let Some(right) = checked_bool(right) { right } else { return None };
    Some([left, right])
}

/// Validates a concrete boolean slice by checking every raw candidate byte.
///
/// ```aeneas
/// spec bool_slice_valid_spec
///   ensures(raw) r => r = decide (∀ byte ∈ bytes.val, byte.val < 2)
/// ```
#[allow(clippy::arithmetic_side_effects)] // i < bytes.len() rules out overflow of i + 1.
fn bool_slice_valid(bytes: &[u8]) -> bool {
    let mut i = 0;
    while i < bytes.len() {
        if !super::validity::bool_encoding(super::validity::read_byte(bytes, i)) {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TryFromBytes;

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
            assert_eq!(checked_bool(byte), bool::try_read_from_bytes(&[byte]).ok());
        }
    }

    #[test]
    fn boolean_array_and_slice_candidates() {
        for left in 0..=u8::MAX {
            for right in 0..=u8::MAX {
                let bytes = [left, right];
                assert_eq!(checked_bool_pair(bytes), <[bool; 2]>::try_read_from_bytes(&bytes).ok());
                assert_eq!(bool_slice_valid(&bytes), <[bool]>::try_ref_from_bytes(&bytes).is_ok());
            }
        }
        assert!(bool_slice_valid(&[]));
        assert!(bool_slice_valid(&[0, 1, 0, 1]));
        for invalid_index in 0..4 {
            let mut bytes = [0, 1, 0, 1];
            bytes[invalid_index] = 2;
            assert!(!bool_slice_valid(&bytes));
            <[bool]>::try_ref_from_bytes(&bytes).unwrap_err();
        }
    }

    #[test]
    fn nonzero_candidates() {
        for n in [0, 1, 2, 255, 256, usize::MAX / 2, usize::MAX] {
            assert_eq!(
                checked_nonzero(n),
                core::num::NonZeroUsize::try_read_from_bytes(&n.to_ne_bytes()).ok()
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
