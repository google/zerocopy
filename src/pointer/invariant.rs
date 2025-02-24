// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(missing_copy_implementations, missing_debug_implementations)]

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
pub trait Aliasing: Sealed {
    /// Is `Self` [`Exclusive`]?
    #[doc(hidden)]
    const IS_EXCLUSIVE: bool;
}

/// The alignment invariant of a [`Ptr`][super::Ptr].
pub trait Alignment: Sealed {}

/// The validity invariant of a [`Ptr`][super::Ptr].
pub trait Validity: Sealed {}

/// An [`Aliasing`] invariant which is either [`Shared`] or [`Exclusive`].
///
/// # Safety
///
/// Given `A: Reference`, callers may assume that either `A = Shared` or `A =
/// Exclusive`.
pub trait Reference: Aliasing + Sealed {}

/// No requirement - any invariant is allowed.
pub enum Any {}
impl Aliasing for Any {
    const IS_EXCLUSIVE: bool = false;
}
impl Alignment for Any {}
impl Validity for Any {}

/// The `Ptr<'a, T>` adheres to the aliasing rules of a `&'a T`.
///
/// The referent of a shared-aliased `Ptr` may be concurrently referenced by any
/// number of shared-aliased `Ptr` or `&T` references, and may not be
/// concurrently referenced by any exclusively-aliased `Ptr`s or `&mut T`
/// references. The referent must not be mutated, except via [`UnsafeCell`]s.
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

/// The referent is aligned: for `Ptr<T>`, the referent's address is a multiple
/// of the `T`'s alignment.
pub enum Aligned {}
impl Alignment for Aligned {}

/// The byte ranges initialized in `T` are also initialized in the referent.
///
/// Formally: uninitialized bytes may only be present in `Ptr<T>`'s referent
/// where they are guaranteed to be present in `T`. This is a dynamic property:
/// if, at a particular byte offset, a valid enum discriminant is set, the
/// subsequent bytes may only have uninitialized bytes as specificed by the
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
impl Validity for AsInitialized {}

/// The byte ranges in the referent are fully initialized. In other words, if
/// the referent is `N` bytes long, then it contains a bit-valid `[u8; N]`.
pub enum Initialized {}
impl Validity for Initialized {}

/// The referent is bit-valid for `T`.
pub enum Valid {}
impl Validity for Valid {}

pub mod aliasing_safety {
    use super::*;
    use crate::Immutable;

    /// Pointer conversions which do not violate aliasing.
    ///
    /// `U: AliasingSafe<T, A, R>` implies that a pointer conversion from `T` to
    /// `U` does not violate the aliasing invariant, `A`. This can be because
    /// `A` is [`Exclusive`] or because neither `T` nor `U` permit interior
    /// mutability.
    ///
    /// # Safety
    ///
    /// `U: AliasingSafe<T, A, R>` if either of the following conditions holds:
    /// - `A` is [`Exclusive`]
    /// - `T` and `U` both implement [`Immutable`]
    #[doc(hidden)]
    pub unsafe trait AliasingSafe<T: ?Sized, A: Aliasing, R: AliasingSafeReason> {}

    #[doc(hidden)]
    pub trait AliasingSafeReason: sealed::Sealed {}
    impl<R: AliasingSafeReason> AliasingSafeReason for (R,) {}

    /// The conversion is safe because only one live `Ptr` or reference may exist to
    /// the referent bytes at a time.
    #[derive(Copy, Clone, Debug)]
    #[doc(hidden)]
    pub enum BecauseExclusive {}
    impl AliasingSafeReason for BecauseExclusive {}

    /// The conversion is safe because no live `Ptr`s or references permit mutation.
    #[derive(Copy, Clone, Debug)]
    #[doc(hidden)]
    pub enum BecauseImmutable {}
    impl AliasingSafeReason for BecauseImmutable {}

    /// SAFETY: `T: AliasingSafe<Exclusive, BecauseExclusive>` because for all
    /// `Ptr<'a, T, I>` such that `I::Aliasing = Exclusive`, there cannot exist
    /// other live references to the memory referenced by `Ptr`.
    unsafe impl<T: ?Sized, U: ?Sized> AliasingSafe<T, Exclusive, BecauseExclusive> for U {}

    /// SAFETY: `U: AliasingSafe<T, A, BecauseNoCell>` because for all `Ptr<'a, T,
    /// I>` and `Ptr<'a, U, I>` such that `I::Aliasing = A`, all live references and
    /// live `Ptr`s agree, by invariant on `Immutable`, that the referenced bytes
    /// contain no `UnsafeCell`s, and thus do not permit mutation except via
    /// exclusive aliasing.
    unsafe impl<A, T: ?Sized, U: ?Sized> AliasingSafe<T, A, BecauseImmutable> for U
    where
        A: Aliasing,
        T: Immutable,
        U: Immutable,
    {
    }

    /// This ensures that `U: AliasingSafe<T, A>` implies `T: AliasingSafe<U, A>` in
    /// a manner legible to rustc, which in turn means we can write simpler bounds in
    /// some places.
    ///
    /// SAFETY: Per `U: AliasingSafe<T, A, R>`, either:
    /// - `A` is `Exclusive`
    /// - `T` and `U` both implement `Immutable`
    ///
    /// Neither property depends on which of `T` and `U` are in the `Self` position
    /// vs the first type parameter position.
    unsafe impl<A, T: ?Sized, U: ?Sized, R> AliasingSafe<U, A, (R,)> for T
    where
        A: Aliasing,
        R: AliasingSafeReason,
        U: AliasingSafe<T, A, R>,
    {
    }
}

use sealed::Sealed;
mod sealed {
    use super::*;

    pub trait Sealed {}

    impl Sealed for Any {}

    impl Sealed for Shared {}
    impl Sealed for Exclusive {}

    impl Sealed for Aligned {}

    impl Sealed for AsInitialized {}
    impl Sealed for Initialized {}
    impl Sealed for Valid {}

    impl<A: Sealed, AA: Sealed, V: Sealed> Sealed for (A, AA, V) {}

    impl Sealed for super::aliasing_safety::BecauseExclusive {}
    impl Sealed for super::aliasing_safety::BecauseImmutable {}
    impl<S: Sealed> Sealed for (S,) {}
}
