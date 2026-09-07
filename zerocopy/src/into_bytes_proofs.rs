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
//! Configuration: Uses the common Kani CI configuration documented in
//! `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
//! x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
//! `-Zfunction-contracts`, and one layout selected by `--randomize-layout` per
//! invocation.
//!
//! These harnesses cover every `u32`, every byte replacement, and, for copy
//! methods, every destination length from zero through six on Kani's target.
//! They prove concrete value, address, and frame properties against safe
//! standard-library byte-conversion and slice-copy oracles rather than the
//! `IntoBytes` contract for arbitrary types. In particular, Kani does not
//! completely check reference aliasing, pointer provenance, uninitialized
//! memory, or other properties absent from its model. These sized proofs do not
//! exercise custom or nested-DST layout (see #3630).
//!
//! Oracle basis: `VALUE_SIZE` is not reconstructed from [`IntoBytes`]. Rust
//! defines all values of a `Sized` type to share that type's size [1], while
//! `size_of` and `size_of_val` report the type and pointed-to-value sizes [2][3].
//! Thus `size_of::<u32>()` independently specifies the `size_of_val(self)`
//! length in the target APIs' contracts for this sized monomorphization. Safe
//! `u32::{to,from}_ne_bytes` define the value's native-endian memory
//! representation [4][5], and
//! `copy_from_slice` copies every element into an equal-length destination [6].
//! These operations do not call zerocopy; their independence is from the
//! implementation under proof, not from the pinned compiler, standard library,
//! or Kani translation/model. The conclusions remain specific to `u32`, the
//! configured target's native byte order, and exactly the bounded buffers
//! described above.
//!
//! [1]: https://doc.rust-lang.org/1.93.0/reference/type-layout.html#r-layout.properties.sized
//! [2]: https://doc.rust-lang.org/1.93.0/std/mem/fn.size_of.html
//! [3]: https://doc.rust-lang.org/1.93.0/std/mem/fn.size_of_val.html
//! [4]: https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.to_ne_bytes
//! [5]: https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.from_ne_bytes
//! [6]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.copy_from_slice

use crate::IntoBytes;

const VALUE_SIZE: usize = core::mem::size_of::<u32>();
const MAX_DST_LEN: usize = 6;

fn destination_len() -> usize {
    usize::from(kani::any::<u8>() % ((MAX_DST_LEN + 1) as u8))
}

// Factor the initial view's size and contents together; pointer identity stays
// local because shared and mutable views expose different pointer types.
fn assert_initial_u32_byte_view(bytes: &[u8], before: &[u8; VALUE_SIZE]) {
    assert_eq!(bytes.len(), VALUE_SIZE);
    assert_eq!(bytes, before);
}

fn expected_after_copy(
    mut destination: [u8; MAX_DST_LEN],
    source: [u8; VALUE_SIZE],
    start: usize,
) -> [u8; MAX_DST_LEN] {
    destination[start..start + source.len()].copy_from_slice(&source);
    destination
}

#[kani::proof]
fn prove_into_bytes_as_bytes() {
    let value = kani::any::<u32>();
    // Snapshot both contents and length before invoking the target, so a
    // call-time mutation cannot redefine its own expected result.
    let expected = value.to_ne_bytes();
    let value_address = (&value as *const u32).cast::<u8>();
    let bytes = value.as_bytes();

    // Domain: every `u32` on Kani's target. Establishes exact length, address,
    // initial contents, and absence of call-time value mutation. The
    // pre-call `u32::to_ne_bytes` snapshot is the independent safe value and
    // length oracle; pointer equality remains subject to Kani's provenance
    // model limits.
    kani::cover!(value == 0);
    kani::cover!(value == u32::MAX);
    kani::cover!(value == 0x01020304);
    assert_initial_u32_byte_view(bytes, &expected);
    assert_eq!(bytes.as_ptr(), value_address);
    assert_eq!(value.to_ne_bytes(), expected);
}

#[kani::proof]
fn prove_into_bytes_as_mut_bytes() {
    let mut values = kani::any::<[u32; 3]>();
    let before = values;
    let initial_bytes = before[1].to_ne_bytes();
    let replacement = kani::any::<[u8; VALUE_SIZE]>();
    let value_address = (&mut values[1] as *mut u32).cast::<u8>();

    {
        let bytes = values[1].as_mut_bytes();
        assert_initial_u32_byte_view(bytes, &initial_bytes);
        assert_eq!(bytes.as_mut_ptr(), value_address);
        // The shared helper observes the view before this overwrite, so a
        // call-time mutation is not erased by the replacement write.
        bytes.copy_from_slice(&replacement);
        assert_eq!(bytes, &replacement);
    }

    // Domain: every three-`u32` input and replacement representation.
    // Establishes initial contents, exact address/length, and write propagation
    // for the middle element, plus a frame for both neighbors. Pre-call native
    // bytes, safe slice copying, and `u32::from_ne_bytes` are the oracles; this
    // is not an aliasing theorem.
    kani::cover!(replacement != initial_bytes);
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
    let source_len = source.len();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = destination;
    let len = destination_len();

    let succeeded = value.write_to(&mut destination[..len]).is_ok();

    // Domain: every `u32`, destination value, and destination length 0..=6.
    // Establishes the exact-length success condition and a whole-buffer frame.
    // The expected buffer is produced with safe `copy_from_slice`.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == source_len - 1);
    kani::cover!(succeeded && len == source_len);
    kani::cover!(!succeeded && len == source_len + 1);
    kani::cover!(!succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && destination != before);

    assert_eq!(value.to_ne_bytes(), source);
    assert_eq!(succeeded, len == source_len);
    let expected = if len == source_len { expected_after_copy(before, source, 0) } else { before };
    assert_eq!(destination, expected);
}

#[kani::proof]
fn prove_into_bytes_write_to_prefix() {
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let source_len = source.len();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = destination;
    let len = destination_len();

    let succeeded = value.write_to_prefix(&mut destination[..len]).is_ok();

    // Domain: every `u32`, destination value, and destination length 0..=6.
    // Establishes the minimum-length success condition, exact prefix write,
    // and preservation of the entire suffix via a safe slice-copy oracle.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == source_len - 1);
    kani::cover!(succeeded && len == source_len);
    kani::cover!(succeeded && len == source_len + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_eq!(value.to_ne_bytes(), source);
    assert_eq!(succeeded, len >= source_len);
    let expected = if len >= source_len { expected_after_copy(before, source, 0) } else { before };
    assert_eq!(destination, expected);
}

#[kani::proof]
fn prove_into_bytes_write_to_suffix() {
    let value = kani::any::<u32>();
    let source = value.to_ne_bytes();
    let source_len = source.len();
    let mut destination = kani::any::<[u8; MAX_DST_LEN]>();
    let before = destination;
    let len = destination_len();

    let succeeded = value.write_to_suffix(&mut destination[..len]).is_ok();

    // Domain: every `u32`, destination value, and destination length 0..=6.
    // Establishes the minimum-length success condition, exact suffix write,
    // and preservation of the entire prefix via a safe slice-copy oracle.
    kani::cover!(!succeeded && len == 0);
    kani::cover!(!succeeded && len == source_len - 1);
    kani::cover!(succeeded && len == source_len);
    kani::cover!(succeeded && len == source_len + 1);
    kani::cover!(succeeded && len == MAX_DST_LEN);
    kani::cover!(succeeded && len == MAX_DST_LEN && destination != before);

    assert_eq!(value.to_ne_bytes(), source);
    assert_eq!(succeeded, len >= source_len);
    let expected = if len >= source_len {
        expected_after_copy(before, source, len - source_len)
    } else {
        before
    };
    assert_eq!(destination, expected);
}
