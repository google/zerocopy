// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(missing_copy_implementations, missing_debug_implementations, missing_docs)]

//! The parameterized invariants of a [`Ptr`][super::Ptr].
//!
//! Invariants are encoded as ([`Aliasing`], [`Alignment`], [`Validity`])
//! triples implementing the [`Invariants`] trait.

/// The invariants of a [`Ptr`][super::Ptr].
pub trait Invariants: Sealed {
    type Aliasing: Aliasing;
    type Alignment: Alignment;
    type Validity: Validity;
}

impl<A: Aliasing, AA: Alignment, V: Validity> Invariants for (A, AA, V) {
    type Aliasing = A;
    type Alignment = AA;
    type Validity = V;
}

/// The aliasing invariant of a [`Ptr`][super::Ptr].
///
/// All aliasing invariants must permit reading from the bytes of a pointer's
/// referent which are not covered by [`UnsafeCell`]s.
///
/// [`UnsafeCell`]: core::cell::UnsafeCell
pub trait Aliasing: Sealed {
    /// Is `Self` [`Exclusive`]?
    #[doc(hidden)]
    const IS_EXCLUSIVE: bool;
}

/// The alignment invariant of a [`Ptr`][super::Ptr].
pub trait Alignment: Sealed {
    #[doc(hidden)]
    #[must_use]
    fn read<T, I, R>(ptr: crate::Ptr<'_, T, I>) -> T
    where
        T: Copy + Read<I::Aliasing, R>,
        I: Invariants<Alignment = Self, Validity = Safe>,
        I::Aliasing: Reference;
}

/// The validity invariant of a [`Ptr`][super::Ptr].
///
/// # Safety
///
/// In this section, we use `Ptr<T, V>` as shorthand for `Ptr<T, I:
/// Invariants<Validity = V>>`.
///
/// Each `V: Validity` defines a set of admissible **referent states** for
/// `Ptr<T, V>`, denoted `S(T, V)`. A referent state records the contents of
/// initialized bytes and which bytes, if any, are uninitialized. Each validity
/// type documents `S(T, V)` for every `T: ?Sized`.
///
/// `Validity` describes only the state of the referent bytes under the typed
/// interpretation `T`. Alignment, aliasing, simultaneous typed access, and
/// other capability/protocol obligations are modeled separately.
///
/// It is guaranteed that the referent of any `ptr: Ptr<T, V>` is a member of
/// `S(T, V)`. Unsafe code must ensure that this guarantee remains true for
/// every existing `Ptr` and every `Ptr` it creates.
///
/// This restricts exact reinterpretations. Given `src: Ptr<T, V>` and
/// `dst: Ptr<U, W>` which refer to exactly the same bytes:
///
/// - If source-side mutation can occur while `dst` is live, every state such a
///   mutation may produce must be in `S(U, W)`.
/// - If `dst` permits mutation while a source interpretation may later become
///   observable again, every state writable through `dst` must be in
///   `S(T, V)`.
///
/// For an exact correspondence these obligations are often discharged by
/// directional subset relations between `S(T, V)` and `S(U, W)`. For DSTs,
/// those relations must be understood over the particular corresponding
/// referents selected by the exact cast; equal byte length alone need not
/// identify equivalent metadata or validity requirements.
///
/// These conditions describe only exact reinterpretations. Shrinking
/// projections may have validity that depends on bytes outside the projected
/// region and require additional reasoning.
pub unsafe trait Validity: Sealed {
    const KIND: ValidityKind;
}

pub enum ValidityKind {
    Uninit,
    AsInitialized,
    Initialized,
    Safe,
}

/// An [`Aliasing`] invariant which is either [`Shared`] or [`Exclusive`].
///
/// # Safety
///
/// Given `A: Reference`, callers may assume that either `A = Shared` or `A =
/// Exclusive`.
pub trait Reference: Aliasing + Sealed {}

/// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a T`.
///
/// The referent of a shared-aliased `Ptr` may be concurrently referenced by any
/// number of shared-aliased `Ptr` or `&T` references, or by any number of
/// `Ptr<U>` or `&U` references as permitted by `T`'s library safety invariants,
/// and may not be concurrently referenced by any exclusively-aliased `Ptr`s or
/// `&mut` references. The referent must not be mutated, except via
/// [`UnsafeCell`]s, and only when permitted by `T`'s library safety invariants.
///
/// [`UnsafeCell`]: core::cell::UnsafeCell
pub enum Shared {}
impl Aliasing for Shared {
    const IS_EXCLUSIVE: bool = false;
}
impl Reference for Shared {}

/// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a mut T`.
///
/// The referent of an exclusively-aliased `Ptr` may not be concurrently
/// referenced by any other `Ptr`s or references, and may not be accessed (read
/// or written) other than via this `Ptr`.
pub enum Exclusive {}
impl Aliasing for Exclusive {
    const IS_EXCLUSIVE: bool = true;
}
impl Reference for Exclusive {}

/// It is unknown whether the pointer is aligned.
pub enum Unaligned {}

impl Alignment for Unaligned {
    #[inline(always)]
    fn read<T, I, R>(ptr: crate::Ptr<'_, T, I>) -> T
    where
        T: Copy + Read<I::Aliasing, R>,
        I: Invariants<Alignment = Self, Validity = Safe>,
        I::Aliasing: Reference,
    {
        (*ptr.into_unalign().as_ref()).into_inner()
    }
}

/// The referent is aligned: for `Ptr<T>`, the referent's address is a multiple
/// of the `T`'s alignment.
pub enum Aligned {}
impl Alignment for Aligned {
    #[inline(always)]
    fn read<T, I, R>(ptr: crate::Ptr<'_, T, I>) -> T
    where
        T: Copy + Read<I::Aliasing, R>,
        I: Invariants<Alignment = Self, Validity = Safe>,
        I::Aliasing: Reference,
    {
        *ptr.as_ref()
    }
}

/// Any bit pattern is allowed in the `Ptr`'s referent, including uninitialized
/// bytes.
pub enum Uninit {}
// SAFETY: `Uninit`'s admissible-state set is well-defined for all `T: ?Sized`.
unsafe impl Validity for Uninit {
    const KIND: ValidityKind = ValidityKind::Uninit;
}

/// The byte ranges initialized in `T` are also initialized in the referent of a
/// `Ptr<T>`.
///
/// Formally: uninitialized bytes may only be present in `Ptr<T>`'s referent
/// where they are guaranteed to be present in `T`. This is a dynamic property:
/// if, at a particular byte offset, a valid enum discriminant is set, the
/// subsequent bytes may only have uninitialized bytes as specified by the
/// corresponding enum.
///
/// Formally, given `len = size_of_val_raw(ptr)`, at every byte offset, `b`, in
/// the range `[0, len)`:
/// - If, in any instance `t: T` of length `len`, the byte at offset `b` in `t`
///   is initialized, then the byte at offset `b` within `*ptr` must be
///   initialized.
/// - Let `c` be the contents of the byte range `[0, b)` in `*ptr`. Let `S` be
///   the subset of valid instances of `T` of length `len` which contain `c` in
///   the offset range `[0, b)`. If, in any instance of `t: T` in `S`, the byte
///   at offset `b` in `t` is initialized, then the byte at offset `b` in `*ptr`
///   must be initialized.
///
///   Pragmatically, this means that if `*ptr` is guaranteed to contain an enum
///   type at a particular offset, and the enum discriminant stored in `*ptr`
///   corresponds to a valid variant of that enum type, then it is guaranteed
///   that the appropriate bytes of `*ptr` are initialized as defined by that
///   variant's bit validity (although note that the variant may contain another
///   enum type, in which case the same rules apply depending on the state of
///   its discriminant, and so on recursively).
pub enum AsInitialized {}
// SAFETY: `AsInitialized`'s admissible-state set is well-defined for all
// `T: ?Sized`.
unsafe impl Validity for AsInitialized {
    const KIND: ValidityKind = ValidityKind::AsInitialized;
}

/// The byte ranges in the referent are fully initialized. In other words, if
/// the referent is `N` bytes long, then it contains a bit-valid `[u8; N]`.
pub enum Initialized {}
// SAFETY: `Initialized`'s validity is well-defined for all `T: ?Sized`, and is
// not a function of any property of `T` other than its bit validity (in fact,
// it's not even a property of `T`'s bit validity, but this is more than we are
// required to uphold).
unsafe impl Validity for Initialized {
    const KIND: ValidityKind = ValidityKind::Initialized;
}

/// The referent state is valid for the typed interpretation `T`, including
/// Rust validity and any referent-local library invariant required before the
/// bytes may be exposed as a `T`. Alignment, aliasing, and simultaneous-access
/// compatibility are modeled separately.
pub enum Safe {}
// SAFETY: `Safe`'s admissible-state set is well-defined for all `T: ?Sized`.
unsafe impl Validity for Safe {
    const KIND: ValidityKind = ValidityKind::Safe;
}

/// Proof helper for casts whose validity requirement does not depend on the
/// referent type.
///
/// Currently this covers `Uninit`, which permits any byte state, and
/// `Initialized`, which requires every referent byte to be initialized
/// regardless of referent type.
///
/// # Safety
///
/// `DT: CastableFrom<ST, SV, DV>` is sound if `SV = DV = Uninit` or `SV = DV =
/// Initialized`.
pub unsafe trait CastableFrom<ST: ?Sized, SV, DV> {}

// SAFETY: `SV = DV = Uninit`.
unsafe impl<ST: ?Sized, DT: ?Sized> CastableFrom<ST, Uninit, Uninit> for DT {}
// SAFETY: `SV = DV = Initialized`.
unsafe impl<ST: ?Sized, DT: ?Sized> CastableFrom<ST, Initialized, Initialized> for DT {}

/// [`Ptr`](crate::Ptr) referents that permit unsynchronized read operations.
///
/// `T: Read<A, R>` implies that a pointer to `T` with aliasing `A` permits
/// unsynchronized read operations. This can be because `A` is [`Exclusive`] or
/// because `T` does not permit interior mutation.
///
/// # Safety
///
/// `T: Read<A, R>` if either of the following conditions holds:
/// - `A` is [`Exclusive`]
/// - `T` implements [`Immutable`](crate::Immutable)
///
/// As a consequence, if `T: Read<A, R>`, then any `Ptr<T, (A, ...)>` is
/// permitted to perform unsynchronized reads from its referent.
pub trait Read<A: Aliasing, R> {}

impl<A: Aliasing, T: ?Sized + crate::Immutable> Read<A, BecauseImmutable> for T {}
impl<T: ?Sized> Read<Exclusive, BecauseExclusive> for T {}

/// Unsynchronized reads are permitted because only one live [`Ptr`](crate::Ptr)
/// or reference may exist to the referent bytes at a time.
#[derive(Copy, Clone, Debug)]
pub enum BecauseExclusive {}

/// Unsynchronized reads are permitted because no live [`Ptr`](crate::Ptr)s or
/// references permit interior mutation.
#[derive(Copy, Clone, Debug)]
pub enum BecauseImmutable {}

use sealed::Sealed;
mod sealed {
    use super::*;

    pub trait Sealed {}

    impl Sealed for Shared {}
    impl Sealed for Exclusive {}

    impl Sealed for Unaligned {}
    impl Sealed for Aligned {}

    impl Sealed for Uninit {}
    impl Sealed for AsInitialized {}
    impl Sealed for Initialized {}
    impl Sealed for Safe {}

    impl<A: Sealed, AA: Sealed, V: Sealed> Sealed for (A, AA, V) {}

    impl Sealed for BecauseImmutable {}
    impl Sealed for BecauseExclusive {}
}
