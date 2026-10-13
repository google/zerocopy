// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Checked trait laws are assumptions at generic calls and proofs at impls.
//!
//! These small examples exercise both directions. A generic consumer receives
//! the law of its exact Rust dictionary. A concrete caller must discharge that
//! law for the selected implementation before reusing the consumer.

use core::{marker::PhantomData, mem, num::NonZeroUsize};

use crate::Unaligned;

/// ```aeneas
/// spec unaligned_alignment_spec
///   ensures alignment => (alignment : Nat) = 1
/// ```
fn unaligned_alignment<T: Unaligned>() -> usize {
    mem::align_of::<T>()
}

/// The assertion consumes the callee's checked contract.
///
/// ```aeneas
/// spec unaligned_check_spec
///   ensures _ => True
/// ```
fn check_unaligned<T: Unaligned>() {
    assert!(unaligned_alignment::<T>() == 1);
}

/// An unused trait bound must still contribute its invariant.
///
/// ```aeneas
/// spec unused_unaligned_bound_spec
///   ensures result => result = value
/// ```
// Keep T unused so extraction must preserve the bound's law independently
// of runtime arguments or method calls.
#[allow(clippy::extra_unused_type_parameters)]
fn unused_unaligned_bound<T: Unaligned>(value: usize) -> usize {
    value
}

/// This call also checks the concrete built-in `u8` implementation's law.
///
/// ```aeneas
/// spec concrete_unaligned_check_spec
///   ensures _ => True
/// ```
fn check_byte_unaligned() {
    check_unaligned::<u8>();
}

/// Trait evidence establishes the unsafe constructor's precondition.
///
/// ```aeneas
/// spec divide_by_unaligned_spec
///   ensures result => result = x
/// ```
// Both divisions have divisor one by the Unaligned contract.
// Keep get explicit so extraction checks both standard-library boundaries.
#[allow(clippy::arithmetic_side_effects, clippy::needless_nonzero_get)]
fn divide_by_unaligned<T: Unaligned>(x: usize) -> usize {
    let divisor = 1 / mem::align_of::<T>();
    // SAFETY: Unaligned requires T to have alignment one, so the preceding
    // division computes 1 / 1 = 1. NonZeroUsize::new_unchecked requires a
    // nonzero argument, which divisor = 1 satisfies.
    let divisor = unsafe { NonZeroUsize::new_unchecked(divisor) };
    x / divisor.get()
}

/// The concrete call discharges the actual built-in u8 dictionary's law.
///
/// ```aeneas
/// spec divide_by_byte_alignment_spec
///   ensures result => result = x
/// ```
fn divide_by_byte_alignment(x: usize) -> usize {
    divide_by_unaligned::<u8>(x)
}

/// Encoding and decoding form one total round trip on every byte.
///
/// ```aeneas
/// invariant byte_roundtrip for self =>
///   ∀ byte, (do let encoded ← self.encode byte; self.decode encoded)
///     ⦃ result => result = byte ⦄
/// ```
trait ByteCodec {
    fn encode(byte: u8) -> u8;
    fn decode(byte: u8) -> u8;
}

struct XorCodec;

/// ```aeneas
/// invariant_proof
/// ```
impl ByteCodec for XorCodec {
    fn encode(byte: u8) -> u8 {
        byte ^ 0xaa
    }

    fn decode(byte: u8) -> u8 {
        byte ^ 0xaa
    }
}

/// A generic implementation forwards to the exact supplied dictionary.
struct Forward<C>(PhantomData<C>);

impl<C: ByteCodec> ByteCodec for Forward<C> {
    fn encode(byte: u8) -> u8 {
        C::encode(byte)
    }

    fn decode(byte: u8) -> u8 {
        C::decode(byte)
    }
}

/// ```aeneas
/// spec byte_codec_roundtrip_spec
///   ensures result => result = byte
/// ```
fn byte_codec_roundtrip<C: ByteCodec>(byte: u8) -> u8 {
    C::decode(C::encode(byte))
}

/// Concrete and generic impl proofs compose without changing function bodies.
///
/// ```aeneas
/// spec forwarded_byte_codec_spec
///   ensures result => result = byte
/// ```
fn forwarded_byte_codec(byte: u8) -> u8 {
    byte_codec_roundtrip::<Forward<XorCodec>>(byte)
}

fn require_into_bytes<T: crate::IntoBytes>() {}

/// Forces extraction of the existing array IntoBytes implementation and its
/// primitive and nested dependencies. CI checks the generic implementation law
/// for every count; these concrete uses also exercise Rust's trait selection.
///
/// ```aeneas
/// spec array_into_bytes_spec
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 3#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array U8 3#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Unit 4#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 0#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation
///     (Aeneas.Std.Array (Aeneas.Std.Array Bool 2#usize) 3#usize)
/// ```
fn check_array_into_bytes() {
    require_into_bytes::<[bool; 3]>();
    require_into_bytes::<[u8; 3]>();
    require_into_bytes::<[(); 4]>();
    require_into_bytes::<[bool; 0]>();
    require_into_bytes::<[[bool; 2]; 3]>();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trait_law_examples() {
        check_byte_unaligned();
        assert_eq!(unaligned_alignment::<u8>(), 1);
        assert_eq!(unused_unaligned_bound::<u8>(37), 37);
        for value in [0, 1, 2, 37, usize::MAX - 1, usize::MAX].iter().copied() {
            assert_eq!(divide_by_unaligned::<u8>(value), value);
            assert_eq!(divide_by_byte_alignment(value), value);
        }
        for byte in 0..=u8::MAX {
            assert_eq!(forwarded_byte_codec(byte), byte);
        }
        check_array_into_bytes();
    }
}
