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

//! Shared mechanics and language oracles for Kani proofs.
//!
//! Keep semantic expectations in their individual proof modules unless Rust
//! itself defines the expectation here. This module factors reusable proof
//! operations, including invoking both alignment specializations of a sized
//! validator on arbitrary initialized bytes at controlled physical placements
//! and reading bytes that an independent safe oracle has already established
//! are a valid representation. It also contains the shared byte-level `bool`
//! and `char` language oracles. Unsized validation stays local to the theorem
//! because its pointer cast and metadata are part of what that theorem must
//! expose.
//!
//! There is deliberately no generic `T`-validity oracle here. Generating a `T`
//! can witness only valid values, while materializing arbitrary bytes as `T`
//! before validation would itself be undefined for invalid bytes. Each proof
//! therefore supplies a type-specific safe checked constructor when Rust
//! exposes one and states the residual language rule when it does not. In
//! particular, acceptance by the validator under proof is never itself treated
//! as permission to materialize `T`: a bug in that validator is one of the
//! conditions these proofs are intended to find.
//!
//! Per https://doc.rust-lang.org/1.93.0/reference/behavior-considered-undefined.html#invalid-values:
//!
//! > The Rust compiler assumes that all values produced during program
//! > execution are ‘valid’, and producing an invalid value is hence immediate
//! > UB.

// Give each sized validator two controlled physical placements. The Rust 1.93
// Reference's `repr(C)` algorithm places fields in declaration order, adding
// only the padding required by each field's alignment [1]. At the call sites
// below, `T` is always `ReadOnly<[u8; N]>`, whose alignment is one: `ReadOnly`
// is transparent, arrays have their element's alignment, and `u8` has size one
// while every size is a multiple of its alignment [2][3][5]. Thus `u8`, the
// source type, and `[u8; OFFSET]` all have alignment one, and `value` begins at
// byte offset `OFFSET` for the two instantiated offsets zero and one.
//
// `align(16)` raises the wrapper's alignment to at least 16 [4], so its address
// is a multiple of 16 [5]. For every destination admitted below, its alignment
// is a power of two no greater than 16. Its alignment therefore divides 16:
// the zero-offset placement is aligned for the destination, while the
// one-byte-offset placement is aligned exactly when the destination's
// alignment is one. Assertions backed by the standard library's alignment
// queries check all of these facts before either placement reaches zerocopy.
//
// [1] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#the-c-representation
// [2] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#the-transparent-representation
// [3] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#array-layout
// [4] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#the-alignment-modifiers
// [5] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#size-and-alignment
#[repr(C, align(16))]
pub(crate) struct PositionedProofStorage<T, const OFFSET: usize> {
    pub(crate) _prefix: [u8; OFFSET],
    pub(crate) value: T,
}

// This is the independent physical-alignment oracle for the proof storage.
// `from_ref` converts the reference to its equivalent raw pointer [1], the
// pointer-to-pointer cast leaves the pointer unchanged because both types are
// sized [2], and `is_aligned` reports whether that address is properly aligned
// for `T` [3]. None of these operations calls zerocopy or dereferences the raw
// pointer. In particular, no success or failure from zerocopy's
// `try_into_aligned` decides which placement is aligned.
//
// [1] Per https://doc.rust-lang.org/1.93.0/std/ptr/fn.from_ref.html:
//
//     Converts a reference to a raw pointer.
//
//     For `r: &T`, obtaining a raw pointer is equivalent to `r as *const T`.
//
// [2] Per https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#pointer-to-pointer-cast:
//
//     If `T` and `U` are both sized, the pointer is returned unchanged.
//
// [3] Per https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.is_aligned:
//
//     Returns whether the pointer is properly aligned for `T`.
pub(crate) fn address_is_aligned_for<T, U>(source: &U) -> bool {
    core::ptr::from_ref(source).cast::<T>().is_aligned()
}

// Construct the common non-materializing candidate from caller-positioned,
// initialized, read-only storage. `CastSizedExact` requires the source and
// destination to have exactly the same size. Keeping this operation here makes
// the subtle setup identical across proofs while leaving each theorem's
// semantic oracle and postconditions at its call site.
//
// This helper is target machinery, not an oracle. It deliberately exercises
// zerocopy's `ReadOnly`, `Ptr::from_ref`, `Ptr::transmute_with`,
// `CastSizedExact`, `Initialized`, `BecauseImmutable`, `Ptr::reborrow_shared`,
// and destination `TryFromBytes::is_bit_valid` path with the post-cast
// alignment marker left as `Unaligned`. The resulting theorem is therefore
// conditional on Kani's translation and Rust model for that entire path.
// Within that model the zerocopy path is exercised, not assumed.
//
// TOOL-model limitation: Kani does not completely check reference aliasing,
// pointer provenance, invalid-value, or uninitialized-memory semantics.
// `agent_docs/validation.md` cites Kani's official feature-support and
// undefined-behaviour documentation for these limitations and records the
// exact current toolchain audit.
// Consequently, the TCB for conclusions about this composite path includes
// Kani 0.67's translation of these `Ptr`/cast operations and its bundled Rust
// model. Correctness of the path which depends on those unmodeled semantics is
// a trusted premise, not a conclusion of these harnesses.
macro_rules! sized_validator_candidate {
    ($ty:ty, $source:expr) => {{
        use $crate::{
            pointer::{cast::CastSizedExact, invariant::Initialized, BecauseImmutable, Ptr},
            wrappers::ReadOnly,
        };

        Ptr::from_ref($source)
            .transmute_with::<ReadOnly<$ty>, Initialized, CastSizedExact, BecauseImmutable>()
    }};
}

pub(crate) use sized_validator_candidate;

// Exercise the common candidate with the destination validator's alignment
// parameter left as `Unaligned`. Physical placement is supplied and checked by
// `validate_and_read_sized` rather than inferred from this type-level marker.
macro_rules! validator_accepts_sized_unaligned {
    ($ty:ty, $source:expr) => {{
        let mut candidate = $crate::proof_support::sized_validator_candidate!($ty, $source);
        <$ty as $crate::TryFromBytes>::is_bit_valid(candidate.reborrow_shared())
    }};
}

pub(crate) use validator_accepts_sized_unaligned;

// Exercise the same composite target path with the destination validator's
// alignment parameter instantiated as `Aligned`. `try_into_aligned` remains
// target setup rather than an oracle: the caller first classifies the physical
// address independently, and this check must then agree before changing the
// type-level marker.
macro_rules! validator_accepts_sized_aligned {
    ($ty:ty, $source:expr) => {{
        let candidate = $crate::proof_support::sized_validator_candidate!($ty, $source);
        let mut candidate = match candidate.try_into_aligned() {
            Ok(candidate) => candidate,
            Err(_) => panic!("explicitly aligned proof storage failed the runtime alignment check"),
        };
        <$ty as $crate::TryFromBytes>::is_bit_valid(candidate.reborrow_shared())
    }};
}

pub(crate) use validator_accepts_sized_aligned;

// Check the non-materializing validator against the caller's semantic oracle.
// The oracle expression is evaluated and stored before any zerocopy target is
// called. Only call the public value-reading API when that independent oracle
// supplies a safely constructed value witnessing that these bytes satisfy
// `T`'s validity rules. The witness need not have the same padding bytes, so
// each caller must still cite a layout/validity bridge which establishes
// validity for the exact candidate representation.
//
// Return the value read by the public API on oracle-valid inputs and `None` on
// oracle-invalid inputs. This intentionally does not exercise the public API's
// error path: if that path mistakenly materialized an invalid `T`, merely
// observing its `Result` could already be undefined behavior, and Kani does not
// completely check invalid-value production.
//
// Restricting `$bytes` to an identifier avoids evaluating an input expression
// more than once per call site. The raw validator receives fixed-size copies at
// byte offsets zero and one within separately 16-aligned storage. It runs with
// `Unaligned` at both placements. It also runs with `Aligned` at offset zero
// and, for alignment-one destinations, at offset one. The public API continues
// to read the original initialized bytes and makes its own aligned candidate
// copy.
macro_rules! validate_and_read_sized {
    ($ty:ty, $bytes:ident, $expected:expr) => {{
        use $crate::wrappers::ReadOnly;

        let expected: Option<$ty> = $expected;
        let expected_valid = expected.is_some();
        let aligned_source = $crate::proof_support::PositionedProofStorage::<_, 0> {
            _prefix: [],
            value: ReadOnly::new($bytes),
        };
        let offset_source = $crate::proof_support::PositionedProofStorage::<_, 1> {
            _prefix: [0],
            value: ReadOnly::new($bytes),
        };

        assert!(core::mem::align_of_val(&aligned_source) >= 16);
        assert!(core::mem::align_of_val(&offset_source) >= 16);
        assert_eq!(core::mem::align_of_val(&aligned_source.value), 1);
        assert_eq!(core::mem::align_of_val(&offset_source.value), 1);
        assert!(core::mem::align_of::<$ty>() <= 16);

        let aligned_source_is_aligned =
            $crate::proof_support::address_is_aligned_for::<$ty, _>(&aligned_source.value);
        let offset_source_is_aligned =
            $crate::proof_support::address_is_aligned_for::<$ty, _>(&offset_source.value);
        assert!(aligned_source_is_aligned);
        assert_eq!(offset_source_is_aligned, core::mem::align_of::<$ty>() == 1);

        assert_eq!(
            $crate::proof_support::validator_accepts_sized_unaligned!($ty, &aligned_source.value),
            expected_valid
        );
        assert_eq!(
            $crate::proof_support::validator_accepts_sized_aligned!($ty, &aligned_source.value),
            expected_valid
        );
        assert_eq!(
            $crate::proof_support::validator_accepts_sized_unaligned!($ty, &offset_source.value),
            expected_valid
        );
        if offset_source_is_aligned {
            assert_eq!(
                $crate::proof_support::validator_accepts_sized_aligned!($ty, &offset_source.value),
                expected_valid
            );
        }

        match expected {
            Some(_safe_witness) => {
                match <$ty as $crate::TryFromBytes>::try_read_from_bytes(&$bytes) {
                    Ok(actual) => Some(actual),
                    Err(_) => panic!("public read rejected an independently valid representation"),
                }
            }
            None => None,
        }
    }};
}

pub(crate) use validate_and_read_sized;

/// Interprets a byte using Rust's object representation for `bool`.
///
/// This uses safe `From<bool> for u8` conversions for the two representations
/// Rust can construct. The Reference rules out every other byte. Kani 0.67's
/// Rust toolchain has no safe checked conversion in the other direction, so
/// that final exclusion remains a small, centralized language rule rather than
/// being reconstructed separately in each proof. This function never creates
/// an invalid `bool`.
///
/// Per https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-From%3Cbool%3E-for-u8:
///
/// > Converts from `bool` to `u8`, by turning `false` into `0` and `true` into
/// > `1`.
///
/// Per https://doc.rust-lang.org/1.93.0/reference/types/boolean.html#representation:
///
/// > It is undefined behavior for an object with the boolean type to have any
/// > other bit pattern.
pub(crate) fn bool_from_byte(byte: u8) -> Option<bool> {
    if byte == u8::from(false) {
        Some(false)
    } else if byte == u8::from(true) {
        Some(true)
    } else {
        None
    }
}

/// Interprets four bytes as Rust's native-endian representation of a `char`.
///
/// This composes two safe standard-library operations and never constructs an
/// invalid `char`. `u32::from_ne_bytes` supplies the exact bridge from the
/// candidate bytes to their native-endian integer memory representation;
/// `char::from_u32` supplies the checked bridge from that integer to `char`.
/// The Reference states that `char` uses a 32-bit unsigned-word
/// representation, so `Some` witnesses validity of these exact bytes rather
/// than merely the same abstract character value. This function does not call
/// zerocopy.
///
/// Per https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.from_ne_bytes:
///
/// > Creates a native endian integer value from its memory representation as a
/// > byte array in native endianness.
///
/// Per https://doc.rust-lang.org/1.93.0/std/primitive.char.html#method.from_u32:
///
/// > Converts a `u32` to a `char`.
///
/// > However, the reverse is not true: not all valid `u32`s are valid `char`s.
/// > `from_u32()` will return `None` if the input is not a valid value for a
/// > `char`.
///
/// Per https://doc.rust-lang.org/1.93.0/reference/types/textual.html#character-type:
///
/// > A value of type `char` is a Unicode scalar value (i.e. a code point that
/// > is not a surrogate), represented as a 32-bit unsigned word in the 0x0000
/// > to 0xD7FF or 0xE000 to 0x10FFFF range.
pub(crate) fn char_from_ne_bytes(bytes: [u8; 4]) -> Option<char> {
    char::from_u32(u32::from_ne_bytes(bytes))
}
