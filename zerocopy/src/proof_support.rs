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
//! are a valid representation. It also contains the shared byte-level `bool`,
//! `char`, and `NonZeroU16` language/library oracles. Unsized validation stays
//! local to the theorem because its pointer cast and metadata are part of what
//! that theorem must expose.
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
// Equality checks use the shared `assert_same_usize`/`assert_same_bool`
// kernels below [6]; lower and upper alignment bounds use primitive `usize`
// ordering [7]. These are fail-closed proof-storage setup checks, not
// conclusions about the destination validator.
//
// [1] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#the-c-representation
// [2] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#the-transparent-representation
// [3] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#array-layout
// [4] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#the-alignment-modifiers
// [5] https://doc.rust-lang.org/1.93.0/reference/type-layout.html#size-and-alignment
// [6] https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
//     https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
//     https://doc.rust-lang.org/1.93.0/std/primitive.bool.html#impl-PartialEq-for-bool
// [7] https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialOrd.html
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
    (core::ptr::from_ref(source) as *const T).is_aligned()
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
// called. `Option::is_some` reports whether that stored oracle is `Some` [1],
// and the shared Boolean equality kernel compares each validator result with
// that classification. This is comparison machinery only: the caller's
// type-specific oracle supplies the semantic expectation. Only call the public
// value-reading API when that independent oracle supplies a safely constructed
// value witnessing that these bytes satisfy `T`'s validity rules. The witness
// need not have the same padding bytes, so each caller must still cite a
// layout/validity bridge which establishes validity for the exact candidate
// representation.
//
// [1] https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.is_some
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
// and, for alignment-one destinations, at offset one. Independently, the
// zero-offset copy is validated as `Wrapping<T>` under the `Unaligned` marker.
// That is the exact non-materializing adapter which the public read uses after
// forgetting its aligned local candidate's type-level alignment, so it too is
// compared with the independent oracle on valid and invalid bytes. The public
// API itself continues to read the original initialized bytes and makes its own
// aligned candidate copy; its invalid-input return path remains deliberately
// uninvoked.
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
        $crate::proof_support::assert_same_usize(core::mem::align_of_val(&aligned_source.value), 1);
        $crate::proof_support::assert_same_usize(core::mem::align_of_val(&offset_source.value), 1);
        assert!(core::mem::align_of::<$ty>() <= 16);

        let aligned_source_is_aligned =
            $crate::proof_support::address_is_aligned_for::<$ty, _>(&aligned_source.value);
        let offset_source_is_aligned =
            $crate::proof_support::address_is_aligned_for::<$ty, _>(&offset_source.value);
        assert!(aligned_source_is_aligned);
        $crate::proof_support::assert_same_bool(
            offset_source_is_aligned,
            core::mem::align_of::<$ty>() == 1,
        );

        $crate::proof_support::assert_same_bool(
            $crate::proof_support::validator_accepts_sized_unaligned!($ty, &aligned_source.value),
            expected_valid,
        );
        $crate::proof_support::assert_same_bool(
            $crate::proof_support::validator_accepts_sized_aligned!($ty, &aligned_source.value),
            expected_valid,
        );
        $crate::proof_support::assert_same_bool(
            $crate::proof_support::validator_accepts_sized_unaligned!($ty, &offset_source.value),
            expected_valid,
        );
        if offset_source_is_aligned {
            $crate::proof_support::assert_same_bool(
                $crate::proof_support::validator_accepts_sized_aligned!($ty, &offset_source.value),
                expected_valid,
            );
        }
        $crate::proof_support::assert_same_bool(
            $crate::proof_support::validator_accepts_sized_unaligned!(
                core::num::Wrapping<$ty>,
                &aligned_source.value
            ),
            expected_valid,
        );

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

// Compare two `usize` values through safe, versioned standard-library
// operations. `assert_eq!` compares its operands using `PartialEq`, and
// `usize`'s `PartialEq::eq` tests those values for equality [1]. This helper
// supplies only the equality observation: each caller must separately justify
// why its expected operand is an independent oracle or an explicit policy
// premise. It calls no zerocopy target, but still trusts the compiler, standard
// library, and Kani model.
//
// [1] https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
//     https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
//     https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
pub(crate) fn assert_same_usize(actual: usize, expected: usize) {
    assert_eq!(actual, expected);
}

// Compare two `bool` classifications through the same explicit equality
// kernel. `assert_eq!` delegates to primitive `bool::PartialEq` [1]. As with
// `assert_same_usize`, this helper supplies only comparison mechanics: callers
// must separately justify what each classification means and whether either is
// an independent oracle or an explicit policy premise.
//
// [1] https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
//     https://doc.rust-lang.org/1.93.0/std/primitive.bool.html#impl-PartialEq-for-bool
pub(crate) fn assert_same_bool(actual: bool, expected: bool) {
    assert_eq!(actual, expected);
}

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

/// Safely decodes native-endian bytes as a checked `NonZeroU16` oracle.
///
/// This composes two safe standard-library operations and never constructs an
/// invalid nonzero integer. `u16::from_ne_bytes` supplies the exact bridge from
/// the candidate bytes to their native-endian integer memory representation;
/// `NonZeroU16::new` returns `Some` exactly when that integer is nonzero. The
/// versioned `NonZero` layout rule then establishes that `Some` witnesses the
/// validity and value of these exact bytes, while `None` classifies the sole
/// invalid all-zero representation. This function calls no zerocopy target.
///
/// Per https://doc.rust-lang.org/1.93.0/std/primitive.u16.html#method.from_ne_bytes:
///
/// > Creates a native endian integer value from its memory representation as a
/// > byte array in native endianness.
///
/// Per https://doc.rust-lang.org/1.93.0/std/num/struct.NonZero.html#method.new:
///
/// > Creates a non-zero value if the given value is not zero.
///
/// Per https://doc.rust-lang.org/1.93.0/std/num/struct.NonZero.html#layout:
///
/// > `NonZero<T>` is guaranteed to have the same layout and bit validity as `T`
/// > with the exception that the all-zero bit pattern is invalid.
pub(crate) fn nonzero_u16_from_ne_bytes(bytes: [u8; 2]) -> Option<core::num::NonZeroU16> {
    core::num::NonZeroU16::new(u16::from_ne_bytes(bytes))
}

// Take a pre-operation value snapshot using safe Rust language operations,
// independently of any zerocopy target. Applying unary `*` to `value: &T`
// denotes the referenced location [1]. Because `*value` is the final operand
// of the function-body block, the block evaluates it in value-expression
// context [2]. Evaluating a place expression in that context copies it instead
// of moving it when the type implements `Copy` [3]; the bound makes that
// premise explicit for every use. This records a value, not allocation
// identity or independent storage for pointer-bearing `Copy` types.
//
// [1] https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.deref.result
// [2] https://doc.rust-lang.org/1.93.0/reference/expressions/block-expr.html#r-expr.block.value
// [3] https://doc.rust-lang.org/1.93.0/reference/expressions.html#moved-and-copied-types
pub(crate) fn copy_snapshot<T: Copy>(value: &T) -> T {
    *value
}

// Compare ordered byte values without treating slice or array `PartialEq` as
// an implicit oracle. `slice::len` returns each slice's element count,
// while the factored `assert_same_usize` supplies the documented equality
// observation above. The first assertion therefore requires equal element
// counts. `slice::iter` yields every item from start to end [1],
// `Iterator::copied` copies those items and `Iterator::eq` compares the two
// sequences [2], and `u8::eq` supplies element equality [3]. Rust specifies
// that the final `assert!` panics when that equality expression
// is false and cannot be disabled [4], so—under Kani's assertion/panic
// translation—an ordered-value mismatch cannot silently pass the harness.
// These safe operations call no zerocopy target, so they are
// independent of that target implementation, but not of the compiler,
// standard library, or Kani model. They establish values only, not storage
// identity or provenance.
//
// [1] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.len
//     https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
// [2] https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.copied
//     https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.eq
// [3] https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-PartialEq-for-u8
// [4] https://doc.rust-lang.org/1.93.0/std/macro.assert.html
pub(crate) fn assert_same_u8_elements(actual: &[u8], expected: &[u8]) {
    assert_same_usize(actual.len(), expected.len());
    assert!(actual.iter().copied().eq(expected.iter().copied()));
}
