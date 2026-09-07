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
//! They prove concrete value, address, and frame properties rather than the
//! `IntoBytes` contract for arbitrary types. In particular, Kani does not
//! completely check reference aliasing, pointer provenance, uninitialized
//! memory, or other properties absent from its model. These sized proofs do not
//! exercise custom or nested-DST layout (see #3630).

use crate::IntoBytes;

const VALUE_SIZE: usize = 4;
const MAX_DST_LEN: usize = 6;

fn destination_len() -> usize {
    usize::from(kani::any::<u8>() % ((MAX_DST_LEN + 1) as u8))
}

fn overwrite(destination: &mut [u8; MAX_DST_LEN], start: usize, source: [u8; VALUE_SIZE]) {
    destination[start] = source[0];
    destination[start + 1] = source[1];
    destination[start + 2] = source[2];
    destination[start + 3] = source[3];
}

#[kani::proof]
fn prove_into_bytes_as_bytes() {
    let value = kani::any::<u32>();
    let value_address = (&value as *const u32).cast::<u8>();
    let bytes = value.as_bytes();

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
        bytes[0] = replacement[0];
        bytes[1] = replacement[1];
        bytes[2] = replacement[2];
        bytes[3] = replacement[3];
        assert_eq!(bytes, &replacement);
    }

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

    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == VALUE_SIZE - 1);
    kani::cover!(succeeded && len == VALUE_SIZE);
    kani::cover!(!succeeded && len == VALUE_SIZE + 1);
    kani::cover!(!succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && destination != before);

    assert_eq!(succeeded, len == VALUE_SIZE);
    let mut expected = before;
    if len == VALUE_SIZE {
        overwrite(&mut expected, 0, source);
    }
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

    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == VALUE_SIZE - 1);
    kani::cover!(succeeded && len == VALUE_SIZE);
    kani::cover!(succeeded && len == VALUE_SIZE + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_eq!(succeeded, len >= VALUE_SIZE);
    let mut expected = before;
    if len >= VALUE_SIZE {
        overwrite(&mut expected, 0, source);
    }
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

    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == VALUE_SIZE - 1);
    kani::cover!(succeeded && len == VALUE_SIZE);
    kani::cover!(succeeded && len == VALUE_SIZE + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_eq!(succeeded, len >= VALUE_SIZE);
    let mut expected = before;
    if len >= VALUE_SIZE {
        overwrite(&mut expected, len - VALUE_SIZE, source);
    }
    assert_eq!(destination, expected);
}
