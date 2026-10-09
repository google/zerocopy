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

//! The byte-writing part of `IntoBytes`.
//!
//! Keeping size selection here lets Lean check the code used by all three
//! public methods. Obtaining `src` from a typed value remains the separate
//! `IntoBytes::as_bytes` safety argument. These functions receive valid slice
//! references, so they need not reconstruct allocation lifetime or provenance.

/// Writes the whole destination, rejecting unequal lengths without mutation.
///
/// ```aeneas
/// spec write_exact_spec
///   ensures(raw) out => out.1 = decide (src.val.length = dst.val.length) ∧
///     out.2.val = if src.val.length = dst.val.length then src.val else dst.val
/// ```
#[inline]
pub(crate) fn exact(src: &[u8], dst: &mut [u8]) -> bool {
    if dst.len() == src.len() {
        // SAFETY: Equal lengths imply the helper's length requirement. The
        // input references supply an initialized source and exclusive
        // destination, and neither length changes before the copy.
        unsafe { super::copy_unchecked(src, dst) };
        true
    } else {
        false
    }
}

/// Writes a fitting prefix, preserving the suffix and rejecting without mutation.
///
/// ```aeneas
/// spec write_prefix_spec
///   ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
///     out.2.val = if src.val.length ≤ dst.val.length
///       then src.val ++ dst.val.drop src.val.length else dst.val
/// ```
#[inline]
pub(crate) fn prefix(src: &[u8], dst: &mut [u8]) -> bool {
    if src.len() <= dst.len() {
        // SAFETY: This branch establishes the helper's sole extra requirement.
        // It copies only src.len() bytes, leaving the destination suffix alone.
        unsafe { super::copy_unchecked(src, dst) };
        true
    } else {
        false
    }
}

/// Writes a fitting suffix, preserving the prefix and rejecting without mutation.
///
/// ```aeneas
/// spec write_suffix_spec
///   ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
///     out.2.val = if src.val.length ≤ dst.val.length
///       then dst.val.take (dst.val.length - src.val.length) ++ src.val else dst.val
/// ```
#[inline]
pub(crate) fn suffix(src: &[u8], dst: &mut [u8]) -> bool {
    let start = if let Some(start) = dst.len().checked_sub(src.len()) {
        start
    } else {
        return false;
    };
    // SAFETY: Successful subtraction gives start <= dst.len() and
    // src.len() == dst.len() - start. The input references provide the source
    // and destination access conditions required by copy_unchecked_at.
    unsafe { super::copy_unchecked_at(src, dst, start) };
    true
}

/// A concrete padding-free consumer: encode a big-endian word using the public
/// byteorder constructor/accessor, then run the production prefix writer.
/// The tests below compare this composition with `IntoBytes::write_to_prefix`.
///
/// ```aeneas
/// spec write_be_word_prefix_spec
///   ensures(raw) out => out.1 = decide (2 ≤ dst.val.length) ∧
///     out.2.val.map (fun byte => byte.bv) = if 2 ≤ dst.val.length
///       then Rust.Bytes.encodeBE 2 n.val ++ (dst.val.drop 2).map (fun byte => byte.bv)
///       else dst.val.map (fun byte => byte.bv)
/// ```
#[allow(dead_code)]
fn be_word_prefix(n: u16, dst: &mut [u8]) -> bool {
    let value = crate::byteorder::big_endian::U16::new(n);
    prefix(&value.to_bytes(), dst)
}

#[cfg(test)]
mod tests {
    use crate::{byteorder::big_endian::U16, IntoBytes};

    // These exercise the public methods, including their typed-to-byte bridge.
    // Lean checks the shared selection/copying code; these regression tests
    // additionally catch a public method wired to the wrong selection helper.
    #[test]
    fn public_writes() {
        let value = U16::from_bytes([1, 2]);
        for length in 0..=4 {
            for mode in 0..3 {
                let mut storage = [9, 8, 7, 6];
                let dst = &mut storage[..length];
                let accepted = match mode {
                    0 => value.write_to(dst).is_ok(),
                    1 => value.write_to_prefix(dst).is_ok(),
                    _ => value.write_to_suffix(dst).is_ok(),
                };
                let fits = if mode == 0 { length == 2 } else { length >= 2 };
                assert_eq!(accepted, fits);
                let mut expected = [9, 8, 7, 6];
                if fits {
                    let start = if mode == 2 { length - 2 } else { 0 };
                    expected[start..start + 2].copy_from_slice(&[1, 2]);
                }
                assert_eq!(storage, expected);
            }
        }
    }

    #[test]
    fn empty_writes() {
        let value: [u8; 0] = [];
        let mut dst = [9; 3];
        value.write_to(&mut []).unwrap();
        value.write_to(&mut dst).unwrap_err();
        value.write_to_prefix(&mut dst).unwrap();
        value.write_to_suffix(&mut dst).unwrap();
        assert_eq!(dst, [9; 3]);
    }

    #[test]
    fn concrete_word_consumer() {
        for n in [0, 1, 255, 256, u16::MAX] {
            for length in 0..=4 {
                let mut via_array = [9, 8, 7, 6];
                let mut via_into_bytes = via_array;
                let accepted = super::be_word_prefix(n, &mut via_array[..length]);
                let value = U16::new(n);
                assert_eq!(accepted, value.write_to_prefix(&mut via_into_bytes[..length]).is_ok());
                assert_eq!(via_array, via_into_bytes);
            }
        }
    }
}
