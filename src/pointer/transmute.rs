// Copyright 2025 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{cell::UnsafeCell, mem::MaybeUninit};

use crate::{pointer::invariant::*, FromBytes, Immutable, IntoBytes};

/// # Safety
///
/// ## Post-conditions
///
/// Given `Dst: TryTransmuteFromPtr<Src, A, _>`, callers may assume the
/// following:
///
/// Given `src: Ptr<Src, SI>` where `SI: Invariants<Aliasing = A, Validity =
/// SV>`, if the referent of `src` contains a `Dst` which conforms to the
/// validity `DV`, then it is sound to transmute `src` into `dst: Ptr<Dst, DI>`
/// whre `DI: Invariants<Aliasing = A, Validity = DV>`.
///
/// TODO: Mention alignment
///
/// ## Pre-conditions
///
/// Given `src: Ptr<Src, SI>`, `dst: Ptr<Dst, DI>`, `SI: Invariants<Aliasing =
/// A, Validity = SV>`, and `DV: Invariants<Aliasing = A, Validity = DV>`, `Dst:
/// TryTransmuteFromPtr<Src, A, _>` is sound if all of the following
/// hold:
/// - Forwards transmutation: Any of the following hold:
///     - So long as `dst` is active, no mutation of `dst`'s referent is allowed
///       except via `dst` itself
///     - The set of `DV`-valid `Dst`s is a superset of the set of `SV`-valid
///       `Src`s
/// - Reverse transmutation: Any of the following hold:
///     - `dst` does not permit mutation of its referent
///     - The set of `DV`-valid `Dst`s is a subset of the set of `SV`-valid
///       `Src`s
/// - Interior mutation: TODO (ie, at least one of `Exclusive` or `Immutable`
///   required)
///
/// ## Proof
///
/// TODO: Prove that the pre-conditions imply the post-conditions.
pub(crate) unsafe trait TryTransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>
{
}

pub(crate) enum BecauseRead {}

// SAFETY:
// - Forwards transmutation: Since `Src::Inner: Read<A, R>`, one of the
//   following holds:
//   - `Src: Immutable`, so no mutation of `dst`'s referent is permitted via
//     `src`. No other references to the same referent may exist which are typed
//     using `T: !Immutable`, as this would permit violating `Src: Immutable`'s
//     soundness precondition.
//   - Aliasing `A` is `Exclusive`, so `dst` is the only reference permitted to
//     mutate its referent.
// - Reverse transmutation: Since `Src: TransmuteFrom<Dst>`, `Dst`'s validity
//   set is a subset of `Src`'s validity set.
// - Since `Src::Inner: Read` and `Dst::Inner: Read`, one of the following
//   holds:
//   - Aliasing `A` is `Exclusive`, in which case `UnsafeCell`s do not need to
//     agree
//   - `Src::Inner: Immutable` and `Dst::Inner: Immutable`, in which case
//     `UnsafeCell`s trivially agree
unsafe impl<Src, Dst, SV, DV, A, R> TryTransmuteFromPtr<Src, A, SV, DV, (BecauseRead, R)> for Dst
where
    A: Aliasing,
    SV: Validity,
    DV: Validity,
    Src: TransmuteFrom<Dst, DV, SV> + Read<A, R> + ?Sized,
    Dst: Read<A, R> + ?Sized,
{
}

unsafe impl<Src, Dst, SV, DV> TryTransmuteFromPtr<Src, Shared, SV, DV, BecauseImmutable> for Dst
where
    SV: Validity,
    DV: Validity,
    Src: Immutable + ?Sized,
    Dst: Immutable + ?Sized,
{
}

pub(crate) unsafe trait TransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>:
    TryTransmuteFromPtr<Src, A, SV, DV, R> + TransmuteFrom<Src, SV, DV>
{
}

unsafe impl<Src: ?Sized, Dst: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>
    TransmuteFromPtr<Src, A, SV, DV, R> for Dst
where
    Dst: TransmuteFrom<Src, SV, DV> + TryTransmuteFromPtr<Src, A, SV, DV, R>,
{
}

// TODO: What about size equality?
// TODO: What about size equality when the destination type is unsized?
pub(crate) unsafe trait TransmuteFrom<Src: ?Sized, SV, DV> {}

unsafe impl<Src, Dst> TransmuteFrom<Src, Valid, Initialized> for Dst
where
    Src: IntoBytes + ?Sized,
    Dst: ?Sized,
{
}

unsafe impl<Src, Dst> TransmuteFrom<Src, Initialized, Valid> for Dst
where
    Src: ?Sized,
    Dst: FromBytes + ?Sized,
{
}

unsafe impl<T> TransmuteFrom<MaybeUninit<T>, Valid, Uninit> for T {}

unsafe impl<T> TransmuteFrom<T, Uninit, Valid> for MaybeUninit<T> {}
