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
/// In this section, we will use `Ptr<T, V>` as a shorthand for `Ptr<T, I:
/// Invariants<Validity = V>>` for brevity.
///
/// Each `V: Validity` defines a set of allowed referent states, denoted
/// `S(T, V)`, for every `T: ?Sized` and its pointer metadata. A state includes
/// initialization and any library safety invariants required by `V`, not just
/// the values of initialized bytes. `KIND` must describe exactly this set,
/// according to the definitions on [`ValidityKind`].
///
/// A compound validity is a tuple of validity types, one for each logical
/// field of a struct or tuple in declaration order. The field's state must
/// satisfy the corresponding validity; padding outside the fields is
/// unconstrained. These requirements apply recursively to compound components.
/// They do not require the containing type's library safety invariants to
/// hold. For other referent types, or a different number of fields, the set of
/// allowed states is empty. In particular, compound validity does not describe
/// enum or union variants.
///
/// The logical fields of a struct or tuple are its declared fields, except
/// that [`Unalign<T>`][crate::Unalign], [`ReadOnly<T>`][crate::ReadOnly], and
/// [`UnsafeCell<T>`][core::cell::UnsafeCell] inherit the logical fields of `T`.
/// These wrappers contribute no additional level to compound validity:
/// `S(Unalign<T>, V)`, `S(ReadOnly<T>, V)`, and `S(UnsafeCell<T>, V)` are
/// defined by `S(T, V)` when `V` is compound. This rule applies recursively,
/// including to wrappers around fields. For example, `(Safe, Uninit)` on
/// `Unalign<(bool, u32)>` requires a safe `bool` and permits an uninitialized
/// `u32`. The wrappers' alignment and aliasing requirements still apply:
/// shared access through `ReadOnly` must not permit interior mutation, and
/// [`Ptr::get_mut`][super::Ptr::get_mut] requires exclusive access to remove
/// `UnsafeCell`. This transparency is explicit, and is not inferred from a
/// type's representation.
///
/// Equal layout or bit validity does not imply equal `S` sets: compound
/// validity depends on field boundaries and declaration order, and [`Safe`]
/// also requires library safety invariants. A conversion must establish the
/// relationship between the actual source and destination states.
///
/// It is guaranteed that the referent of any `ptr: Ptr<T, V>` is a member of
/// `S(T, V)`. Unsafe code must ensure that this guarantee will be upheld for
/// any existing `Ptr`s or any `Ptr`s that that code creates.
///
/// An important implication of this guarantee is that it restricts which exact
/// reinterpretations are sound. Here, an exact reinterpretation changes the
/// referent type or validity invariant of a `Ptr` while preserving the exact
/// byte range. In particular, given `src: Ptr<T, V>` and `dst: Ptr<U, W>` which
/// refer to the same byte range, the following are necessary (but not
/// sufficient) conditions:
/// - If `S(T, V) = S(U, W)`, then no additional validity-preservation
///   restrictions apply; otherwise,
/// - If `dst` permits mutation of its referent (e.g. via `Exclusive` aliasing
///   or interior mutation under `Shared` aliasing), then it must hold that
///   `S(T, V) ⊇ S(U, W)` - in other words, the reinterpretation must not expand
///   the set of allowed referent states. A violation of this requirement
///   would permit using `dst` to write `x` where `x ∈ S(U, W)` but `x ∉ S(T,
///   V)`, which would violate the guarantee that `src`'s referent may only
///   contain values in `S(T, V)`.
/// - If the referent may be mutated without going through `dst` while `dst` is
///   live (e.g. via interior mutation on a `Shared`-aliased `Ptr` or `&`
///   reference), then it must hold that `S(T, V) ⊆ S(U, W)` - in other words,
///   the reinterpretation must not shrink the set of allowed referent states.
///   A violation of this requirement would permit using `src` or
///   another mechanism (e.g. a `&` reference used to derive `src`) to write `x`
///   where `x ∈ S(T, V)` but `x ∉ S(U, W)`, which would violate the guarantee
///   that `dst`'s referent may only contain values in `S(U, W)`.
///
/// These conditions describe only exact reinterpretations. Shrinking
/// projections may have validity that depends on the relationship between the
/// projected region and bytes outside it, and require additional reasoning.
pub unsafe trait Validity: Sealed {
    const KIND: ValidityKind;
}

/// The interpretation of a [`Validity`] implementation.
///
/// The simple variants have the semantics of the corresponding marker
/// types. `Compound` has the field-wise semantics specified by [`Validity`];
/// its slice lists the logical fields' validity kinds in declaration order.
/// An empty slice describes `()` or a fieldless struct, including either type
/// inside the transparent wrappers specified by `Validity`.
pub enum ValidityKind {
    Uninit,
    AsInitialized,
    Initialized,
    Safe,
    Compound(&'static [ValidityKind]),
}

// SAFETY: `()` describes the empty list of field requirements.
unsafe impl Validity for () {
    const KIND: ValidityKind = ValidityKind::Compound(&[]);
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
// SAFETY: `KIND` names `Uninit`'s unrestricted set of referent states.
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
/// - The byte at offset `b` within `*ptr` must be initialized unless both:
///   - There exists a valid instance `t: T` of length `len`.
///   - In every valid instance `t: T` of length `len`, the byte at offset
///     `b` is uninitialized.
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
///
/// # Uninhabited referents
///
/// If no valid instance of `T` of length `len` exists, the first rule requires
/// every byte of the referent, including padding, to be initialized. In this
/// case, `AsInitialized` has the same requirements as [`Initialized`]. It
/// still does not imply [`Safe`]: initialized storage need not contain a valid
/// value of `T`.
///
/// The following example violates the safety contract of
/// [`Ptr::assume_validity`][super::Ptr::assume_validity]:
///
/// ```no_run
/// use core::mem::MaybeUninit;
/// use zerocopy::{invariant::*, Ptr};
///
/// enum Never {}
///
/// #[repr(u8)]
/// enum E {
///     Variant(Never, u8),
/// }
///
/// let mut storage = MaybeUninit::<E>::uninit();
/// let ptr: Ptr<'_, E, (Exclusive, Unaligned, Uninit)> =
///     Ptr::from_mut(&mut storage).transmute::<E, Uninit, _>();
///
/// // INCORRECT SAFETY ARGUMENT: E has no valid instances, so every valid
/// // instance has an uninitialized byte at every offset. Therefore,
/// // AsInitialized permits the referent to be entirely uninitialized.
/// let _ptr = unsafe { ptr.assume_validity::<AsInitialized>() };
/// ```
///
/// `E` is uninhabited because its only variant contains `Never`, which has no
/// variants. This makes the argument's claim about every valid instance
/// vacuously true, but it does not satisfy the first rule's requirement that
/// at least one such instance exist. The exception therefore does not apply:
/// all bytes of `E`'s storage must be initialized, including its tag.
/// [`MaybeUninit::uninit`][core::mem::MaybeUninit::uninit] does not establish
/// that condition. The `Uninit` pointer is permitted, but the unsafe assertion
/// of `AsInitialized` is not justified.
pub enum AsInitialized {}
// SAFETY: `KIND` names the initialization requirements defined above.
unsafe impl Validity for AsInitialized {
    const KIND: ValidityKind = ValidityKind::AsInitialized;
}

/// The byte ranges in the referent are fully initialized. In other words, if
/// the referent is `N` bytes long, then it contains a bit-valid `[u8; N]`.
pub enum Initialized {}
// SAFETY: `KIND` names the requirement that all referent bytes be initialized.
unsafe impl Validity for Initialized {
    const KIND: ValidityKind = ValidityKind::Initialized;
}

/// The referent of a `Ptr<T>` is valid for `T`, upholding bit validity and any
/// library safety invariants.
pub enum Safe {}
// SAFETY: `KIND` names `Safe`'s bit-validity and library-safety requirements.
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
pub(crate) mod sealed {
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
    impl Sealed for () {}

    impl Sealed for BecauseImmutable {}
    impl Sealed for BecauseExclusive {}
}
