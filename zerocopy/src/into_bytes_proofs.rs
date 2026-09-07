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

//! Bounded Kani regression proofs for [`IntoBytes`] byte views and copies.
//!
//! These harnesses cover every `u32`, every byte replacement, and, for copy
//! methods, every destination length from zero through six on Kani's target.
//! They prove concrete value, address, and frame properties against safe
//! standard-library byte-conversion and slice-copy oracles rather than the
//! `IntoBytes` contract for arbitrary types. In particular, Kani does not
//! completely check reference aliasing, pointer provenance, uninitialized
//! memory, or other properties absent from its model. These sized proofs do not
//! exercise custom or nested-DST layout (see #3630).

use crate::IntoBytes;

const VALUE_SIZE: usize = core::mem::size_of::<u32>();
const MAX_DST_LEN: usize = 6;

fn destination_len() -> usize {
    usize::from(kani::any::<u8>() % ((MAX_DST_LEN + 1) as u8))
}

fn expected_after_copy(
    mut destination: [u8; MAX_DST_LEN],
    source: [u8; VALUE_SIZE],
    start: usize,
) -> [u8; MAX_DST_LEN] {
    destination[start..start + VALUE_SIZE].copy_from_slice(&source);
    destination
}

#[kani::proof]
fn prove_into_bytes_as_bytes() {
    let value = kani::any::<u32>();
    let value_address = (&value as *const u32).cast::<u8>();
    let bytes = value.as_bytes();

    // Domain: every `u32` on Kani's target. Establishes exact length, address,
    // and contents. `u32::to_ne_bytes` is the independent safe value oracle;
    // pointer equality remains subject to Kani's provenance-model limits.
    kani::cover!(value == 0);
    kani::cover!(value == u32::MAX);
    kani::cover!(value == 0x01020304);
    assert_eq!(bytes.len(), VALUE_SIZE);
    assert_eq!(bytes.as_ptr(), value_address);
    assert_eq!(bytes, &value.to_ne_bytes());
}

#[kani::proof]
fn prove_into_bytes_as_mut_bytes() {
    let mut values = kani::any::<[u32; 3]>();
    let before = values;
    let replacement = kani::any::<[u8; VALUE_SIZE]>();
    let value_address = (&mut values[1] as *mut u32).cast::<u8>();

    {
        let bytes = values[1].as_mut_bytes();
        assert_eq!(bytes.len(), VALUE_SIZE);
        assert_eq!(bytes.as_mut_ptr(), value_address);
        bytes.copy_from_slice(&replacement);
        assert_eq!(bytes, &replacement);
    }

    // Domain: every three-`u32` input and replacement representation.
    // Establishes exact address and write propagation for the middle element,
    // plus a frame for both neighbors. Safe slice copying and
    // `u32::from_ne_bytes` are the oracles; this is not an aliasing theorem.
    kani::cover!(replacement != before[1].to_ne_bytes());
    kani::cover!(replacement == [0; VALUE_SIZE]);
    kani::cover!(replacement == [u8::MAX; VALUE_SIZE]);
    kani::cover!(before[0] != before[2]);
    assert_eq!(values[0], before[0]);
    assert_eq!(values[1], u32::from_ne_bytes(replacement));
    assert_eq!(values[2], before[2]);
}

#[kani::proof]
fn prove_into_bytes_write_to() {
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = destination;
    let len = destination_len();

    let succeeded = value.write_to(&mut destination[..len]).is_ok();

    // Domain: every `u32`, destination value, and destination length 0..=6.
    // Establishes the exact-length success condition and a whole-buffer frame.
    // The expected buffer is produced with safe `copy_from_slice`.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == VALUE_SIZE - 1);
    kani::cover!(succeeded && len == VALUE_SIZE);
    kani::cover!(!succeeded && len == VALUE_SIZE + 1);
    kani::cover!(!succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && destination != before);

    assert_eq!(succeeded, len == VALUE_SIZE);
    let expected = if len == VALUE_SIZE { expected_after_copy(before, source, 0) } else { before };
    assert_eq!(destination, expected);
}

#[kani::proof]
fn prove_into_bytes_write_to_prefix() {
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = destination;
    let len = destination_len();

    let succeeded = value.write_to_prefix(&mut destination[..len]).is_ok();

    // Domain: every `u32`, destination value, and destination length 0..=6.
    // Establishes the minimum-length success condition, exact prefix write,
    // and preservation of the entire suffix via a safe slice-copy oracle.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == VALUE_SIZE - 1);
    kani::cover!(succeeded && len == VALUE_SIZE);
    kani::cover!(succeeded && len == VALUE_SIZE + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_eq!(succeeded, len >= VALUE_SIZE);
    let expected = if len >= VALUE_SIZE { expected_after_copy(before, source, 0) } else { before };
    assert_eq!(destination, expected);
}

#[kani::proof]
fn prove_into_bytes_write_to_suffix() {
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = destination;
    let len = destination_len();

    let succeeded = value.write_to_suffix(&mut destination[..len]).is_ok();

    // Domain: every `u32`, destination value, and destination length 0..=6.
    // Establishes the minimum-length success condition, exact suffix write,
    // and preservation of the entire prefix via a safe slice-copy oracle.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == VALUE_SIZE - 1);
    kani::cover!(succeeded && len == VALUE_SIZE);
    kani::cover!(succeeded && len == VALUE_SIZE + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_eq!(succeeded, len >= VALUE_SIZE);
    let expected = if len >= VALUE_SIZE {
        expected_after_copy(before, source, len - VALUE_SIZE)
    } else {
        before
    };
    assert_eq!(destination, expected);
}
