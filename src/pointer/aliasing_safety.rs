// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Machinery for statically proving the "aliasing-safety" of a `Ptr`.

use crate::{invariant, Immutable};

/// Pointer conversions which do not violate aliasing.
///
/// `U: AliasingSafe<T, A, R>` implies that a pointer conversion from `T` to `U`
/// does not violate the aliasing invariant, `A`. This can be because `A` is
/// [`Exclusive`] or because neither `T` nor `U` permit interior mutability.
///
/// # Safety
///
/// `U: AliasingSafe<T, A, R>` if either of the following conditions holds:
/// - `A` is [`Exclusive`]
/// - `T` and `U` both implement [`Immutable`]
///
/// [`Exclusive`]: crate::pointer::invariant::Exclusive
#[doc(hidden)]
pub unsafe trait AliasingSafe<T: ?Sized, A: invariant::Aliasing, R: AliasingSafeReason> {}

/// Used to prevent user implementations of `AliasingSafeReason`.
mod sealed {
    pub trait Sealed {}

    impl Sealed for super::BecauseExclusive {}
    impl Sealed for super::BecauseImmutable {}
    impl<S: Sealed> Sealed for (S,) {}
}

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
unsafe impl<T: ?Sized, U: ?Sized> AliasingSafe<T, invariant::Exclusive, BecauseExclusive> for U {}

/// SAFETY: `U: AliasingSafe<T, A, BecauseNoCell>` because for all `Ptr<'a, T,
/// I>` and `Ptr<'a, U, I>` such that `I::Aliasing = A`, all live references and
/// live `Ptr`s agree, by invariant on `Immutable`, that the referenced bytes
/// contain no `UnsafeCell`s, and thus do not permit mutation except via
/// exclusive aliasing.
unsafe impl<A, T: ?Sized, U: ?Sized> AliasingSafe<T, A, BecauseImmutable> for U
where
    A: invariant::Aliasing,
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
    A: invariant::Aliasing,
    R: AliasingSafeReason,
    U: AliasingSafe<T, A, R>,
{
}
