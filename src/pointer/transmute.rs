// Copyright 2025 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{
    cell::UnsafeCell,
    mem::{ManuallyDrop, MaybeUninit},
    num::Wrapping,
};

use crate::{pointer::invariant::*, FromBytes, Immutable, IntoBytes, Unalign};

define_because!(pub(crate) BecauseBidirectional);
define_because!(pub(crate) BecauseRead);
define_because!(pub(crate) BecauseFoo);
define_because!(BecauseExclusive);
define_because!(BecauseUnchanged);
define_because!(BecauseUnaligned);

// TODO: Confirm that we don't need to explicitly mention size (that should be
// handled automatically by impls, usually via a `TransmuteFrom` bound).

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
/// - `UnsafeCell` agreement: TODO
///
/// ## Proof
///
/// TODO: Prove that the pre-conditions imply the post-conditions.
#[cfg_attr(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS, marker)]
pub(crate) unsafe trait TryTransmuteFromPtr<Src: Validity, A: Aliasing, R>:
    Validity
where
    Self::Inner: CastFrom<Src::Inner>,
{
}

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
unsafe impl<Src, Dst, A, R> TryTransmuteFromPtr<Src, A, (BecauseRead, R)> for Dst
where
    Src: Validity + TransmuteFrom<Dst>,
    Dst: Validity,
    Src::Inner: Read<A, R>,
    Dst::Inner: Read<A, R> + CastFrom<Src::Inner>,
    A: Reference,
{
}

unsafe impl<Src, Dst> TryTransmuteFromPtr<Src, Shared, BecauseImmutable> for Dst
where
    Src: Validity,
    Dst: Validity,
    Src::Inner: Immutable,
    Dst::Inner: Immutable + CastFrom<Src::Inner>,
{
}

// SAFETY:
// - Forwards transmutation: `Dst: TransmuteFrom<Src>` guarantees that
//   the set of `DV`-valid `Dst`s is a supserset of the set of `SV`-valid
//   `Src`s.
// - Reverse transmutation: `Src: TransmuteFrom<Dst, DV, SV>` guarantees that
//   the set of `DV`-valid `Dst`s is a subset of the set of `SV`-valid `Src`s.
// - `UnsafeCell` agreement guaranteed by `Src: UnsafeCellsAgree<Dst> + Dst:
//   UnsafeCellsAgree<Src>`.
unsafe impl<Src, Dst, A> TryTransmuteFromPtr<Src, A, BecauseBidirectional> for Dst
where
    A: Reference,
    Src: Validity + TransmuteFrom<Dst>,
    Dst: Validity + TransmuteFrom<Src>,
    Src::Inner: UnsafeCellsAgree<Dst::Inner>,
    Dst::Inner: UnsafeCellsAgree<Src::Inner> + CastFrom<Src::Inner>,
{
}

// SAFETY:
// - Forwards transmutation: `Src: Immutable` guarantees that no mutation of
//   `dst`'s referent is possible via `src`. No other references to the same
//   referent may exist which are typed using `T: !Immutable`, as this would
//   permit violating `Src: Immutable`'s soundness precondition.
// - Reverse transmutation: `Src: TransmuteFrom<Dst, DV, SV>` guarantees that
//   the set of `DV`-valid `Dst`s is a subset of the set of `SV`-valid `Src`s.
// - `UnsafeCell` agreement guaranteed by `Src: Immutable + Dst: Immutable`.
unsafe impl<Src, Dst, A> TryTransmuteFromPtr<Src, A, BecauseFoo> for Dst
where
    A: Reference,
    Src: Validity + TransmuteFrom<Dst>,
    Dst: Validity,
    Src::Inner: Immutable,
    Dst::Inner: Immutable + CastFrom<Src::Inner>,
{
}

// TODO: Try to delete this impl and see if things still work

// SAFETY:
// - Forwards transmutation: Because aliasing is `Exclusive`, `dst` is the only
//   reference permitted to mutate its referent.
// - Reverse transmutation: `Src: TransmuteFrom<Dst, DV, SV>` guarantees that
//   the set of `DV`-valid `Dst`s is a subset of the set of `SV`-valid `Src`s.
// - `UnsafeCell` agreement is not necessary because aliasing is `Exclusive`.
unsafe impl<Src, Dst> TryTransmuteFromPtr<Src, Exclusive, BecauseExclusive> for Dst
where
    Src: Validity + TransmuteFrom<Dst>,
    Dst: Validity,
    Dst::Inner: CastFrom<Src::Inner>,
{
}

#[cfg_attr(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS, marker)]
pub(crate) unsafe trait TransmuteFromPtr<Src: Validity, A: Aliasing, R>:
    TryTransmuteFromPtr<Src, A, R> + TransmuteFrom<Src>
where
    Self::Inner: CastFrom<Src::Inner>,
{
}

unsafe impl<Src: Validity, Dst: Validity, A: Aliasing, R> TransmuteFromPtr<Src, A, R> for Dst
where
    Dst::Inner: CastFrom<Src::Inner>,
    Dst: TransmuteFrom<Src> + TryTransmuteFromPtr<Src, A, R>,
{
}

#[marker]
pub(crate) unsafe trait TransmuteFromAlignment<Src: ?Sized, SA: Alignment, DA: Alignment, R> {}

pub(crate) unsafe trait CastFrom<Src: ?Sized> {
    /// Casts a `*mut T` to a `*mut Self`.
    ///
    /// # Safety
    ///
    /// The resulting pointer has the same address and provenance as `ptr`, and
    /// addresses the same number of bytes.
    fn cast_from(ptr: *mut Src) -> *mut Self;
}

/// Pairs of types which have `UnsafeCells` covering the same byte ranges.
///
/// # Safety
///
/// Let `t: &T` and `u: &U`. Let `len = min(size_of_val(t), size_of_val(u))`. If
/// `U: UnsafeCellsAgree<T>`, then the first `len` bytes of `t` and the first
/// `len` bytes of `u` have `UnsafeCell`s covering the same byte ranges. This
/// condition must hold for all `t: &T` and for all `u: &U`.
///
/// Note that this safety invariant supports either or both of `T` and `U` being
/// unsized.
pub(crate) unsafe trait UnsafeCellsAgree<T: ?Sized>
where
    T: UnsafeCellsAgree<Self>,
{
}

// SAFETY: `T` has `UnsafeCell`s covering the same byte ranges as itself by
// definition.
unsafe impl<T: ?Sized> UnsafeCellsAgree<T> for T {}

#[marker]
pub(crate) unsafe trait TransmuteFrom<Src: ?Sized> {}

unsafe impl<Src: ?Sized> CastFrom<Src> for Src {
    fn cast_from(ptr: *mut Src) -> *mut Src {
        // SAFETY: `ptr` trivially has the same address as, addresses the same
        // number of bytes as, and has the same provenance as `ptr`.
        ptr
    }
}

unsafe impl<Src: ?Sized> TransmuteFrom<Src> for Src {}

unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<Src, A, A, BecauseUnchanged> for Src {}
unsafe impl<Src: ?Sized, Dst: ?Sized, A: Alignment>
    TransmuteFromAlignment<Src, A, Unknown, BecauseUnaligned> for Dst
{
}

// TODO: Make sure to clarify that, for unsized types, this specifically refers
// to a cast that does not perform a metadata fix-up operation.
pub(crate) unsafe trait SizeGtEq<Other: ?Sized> {}

unsafe impl<T: ?Sized> SizeGtEq<T> for T {}

unsafe impl<Src: ?Sized, Dst: ?Sized> TransmuteFrom<Initialized<Src>> for Valid<Dst>
where
    Dst: FromBytes,
    Src: SizeGtEq<Dst>,
{
}

unsafe impl<Src: ?Sized, Dst: ?Sized> TransmuteFrom<Valid<Src>> for Valid<Dst>
where
    Src: IntoBytes,
    Dst: FromBytes,
    Src: SizeGtEq<Dst>,
{
}

unsafe impl<Src: ?Sized, Dst: ?Sized> TransmuteFrom<Valid<Src>> for Initialized<Dst>
where
    Src: IntoBytes,
    Src: SizeGtEq<Dst>,
{
}

// SAFETY: `MaybeUninit<T>` has `UnsafeCell`s covering the same byte ranges as
// `T`. This is not explicitly documented, but it can be inferred. Per [1] in
// the following safety comment, `MaybeUninit<T>` has the same size as `T`.
// Further, note the signature of `MaybeUninit::assume_init_ref` [1]:
//
//   pub unsafe fn assume_init_ref(&self) -> &T
//
// If the argument `&MaybeUninit<T>` and the returned `&T` had `UnsafeCell`s at
// different offsets, this would be unsound. Its existence is proof that this is
// not the case.
//
// [1] https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#method.assume_init_ref
unsafe impl<T> UnsafeCellsAgree<T> for MaybeUninit<T> {}
// SAFETY: See previous safety comment.
unsafe impl<T> UnsafeCellsAgree<MaybeUninit<T>> for T {}

unsafe impl<Src: Validity> TransmuteFrom<Src> for Valid<MaybeUninit<Src::Inner>> where
    Src::Inner: Sized
{
}
unsafe impl<Src: Validity> TransmuteFrom<Src> for AsInitialized<MaybeUninit<Src::Inner>> where
    Src::Inner: Sized
{
}

unsafe impl<Src> TransmuteFrom<Initialized<Src>> for Initialized<MaybeUninit<Src>> {}

unsafe impl<Src> TransmuteFrom<Initialized<MaybeUninit<Src>>> for Initialized<Src> {}

unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Src, A, A, BecauseUnchanged>
    for MaybeUninit<Src>
{
}
unsafe impl<Src, A: Alignment> TransmuteFromAlignment<MaybeUninit<Src>, A, A, BecauseUnchanged>
    for Src
{
}

unsafe impl<Src> CastFrom<Src> for MaybeUninit<Src> {
    fn cast_from(ptr: *mut Src) -> *mut MaybeUninit<Src> {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `MaybeUninit<Src>` has the same size as `Src` [1], it also preserves
        // size.
        //
        // [1] Per https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#layout-1:
        //
        //   `MaybeUninit<T>` is guaranteed to have the same size, alignment,
        //   and ABI as `T`.
        ptr.cast()
    }
}

unsafe impl<Src> CastFrom<MaybeUninit<Src>> for Src {
    fn cast_from(ptr: *mut MaybeUninit<Src>) -> *mut Src {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `MaybeUninit<Src>` has the same size as `Src` [1], it also preserves
        // size.
        //
        // [1] Per https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#layout-1:
        //
        //   `MaybeUninit<T>` is guaranteed to have the same size, alignment,
        //   and ABI as `T`.
        ptr.cast()
    }
}

// SAFETY: Per [1], `ManuallyDrop<T>` has `UnsafeCell`s covering the same byte
// ranges as `Inner = T`.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`, and is subject to the same layout optimizations as `T`. As a
//   consequence, it has no effect on the assumptions that the compiler makes
//   about its contents.
unsafe impl<T: ?Sized> UnsafeCellsAgree<T> for ManuallyDrop<T> {}
// SAFETY: See previous safety comment.
unsafe impl<T: ?Sized> UnsafeCellsAgree<ManuallyDrop<T>> for T {}

unsafe impl<Src: Validity> TransmuteFrom<Src> for Src::WithInner<ManuallyDrop<Src::Inner>> {}
unsafe impl<Src: Validity> TransmuteFrom<Src::WithInner<ManuallyDrop<Src::Inner>>> for Src {}

unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<Src, A, A, BecauseUnchanged>
    for ManuallyDrop<Src>
{
}
unsafe impl<Src: ?Sized, A: Alignment>
    TransmuteFromAlignment<ManuallyDrop<Src>, A, A, BecauseUnchanged> for Src
{
}

unsafe impl<Src: ?Sized> CastFrom<Src> for ManuallyDrop<Src> {
    fn cast_from(ptr: *mut Src) -> *mut ManuallyDrop<Src> {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `ManuallyDrop<Src>` has the same size as `Src` [1], it also preserves
        // size.
        //
        // [1] Per https://doc.rust-lang.org/nightly/core/mem/struct.ManuallyDrop.html:
        //
        //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
        //   validity as `T`
        ptr as *mut ManuallyDrop<Src>
    }
}

unsafe impl<Src: ?Sized> CastFrom<ManuallyDrop<Src>> for Src {
    fn cast_from(ptr: *mut ManuallyDrop<Src>) -> *mut Src {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `ManuallyDrop<Src>` has the same size as `Src` [1], it also preserves
        // size.
        //
        // [1] Per https://doc.rust-lang.org/nightly/core/mem/struct.ManuallyDrop.html:
        //
        //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
        //   validity as `T`
        ptr as *mut Src
    }
}

// SAFETY: Per [1], `Wrapping<T>` has the same layout as `T`. Since its single
// field (of type `T`) is public, it would be a breaking change to add or remove
// fields. Thus, we know that `Wrapping<T>` contains a `T` (as opposed to just
// having the same size and alignment as `T`) with no pre- or post-padding.
// Thus, `Wrapping<T>` must have `UnsafeCell`s covering the same byte ranges as
// `Inner = T`.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
unsafe impl<T> UnsafeCellsAgree<T> for Wrapping<T> {}
// SAFETY: See previous safety comment.
unsafe impl<T> UnsafeCellsAgree<Wrapping<T>> for T {}

unsafe impl<Src: Validity> TransmuteFrom<Src> for Src::WithInner<Wrapping<Src::Inner>> where
    Src::Inner: Sized
{
}
unsafe impl<Src: Validity> TransmuteFrom<Src::WithInner<Wrapping<Src::Inner>>> for Src where
    Src::Inner: Sized
{
}

unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Src, A, A, BecauseUnchanged>
    for Wrapping<Src>
{
}
unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Wrapping<Src>, A, A, BecauseUnchanged>
    for Src
{
}

unsafe impl<Src> CastFrom<Src> for Wrapping<Src> {
    fn cast_from(ptr: *mut Src) -> *mut Wrapping<Src> {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Wrapping<Src>` has the same size as `Src` [1], it also preserves size.
        //
        // [1] Per https://doc.rust-lang.org/core/num/struct.Wrapping.html#layout-1:
        //
        //   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
        ptr.cast()
    }
}

unsafe impl<Src> CastFrom<Wrapping<Src>> for Src {
    fn cast_from(ptr: *mut Wrapping<Src>) -> *mut Src {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Wrapping<Src>` has the same size as `Src` [1], it also preserves size.
        //
        // [1] Per https://doc.rust-lang.org/core/num/struct.Wrapping.html#layout-1:
        //
        //   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
        ptr.cast()
    }
}

unsafe impl<Src: Validity> TransmuteFrom<Src> for Src::WithInner<UnsafeCell<Src::Inner>> {}
unsafe impl<Src: Validity> TransmuteFrom<Src::WithInner<UnsafeCell<Src::Inner>>> for Src {}

unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<Src, A, A, BecauseUnchanged>
    for UnsafeCell<Src>
{
}
unsafe impl<Src: ?Sized, A: Alignment>
    TransmuteFromAlignment<UnsafeCell<Src>, A, A, BecauseUnchanged> for Src
{
}

unsafe impl<Src: ?Sized> CastFrom<Src> for UnsafeCell<Src> {
    fn cast_from(ptr: *mut Src) -> *mut UnsafeCell<Src> {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `UnsafeCell<Src>` has the same size as `Src`, it also preserves size.
        //
        // [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
        //
        //   `UnsafeCell<T>` has the same in-memory representation as its inner
        //   type `T`.
        ptr as *mut UnsafeCell<Src>
    }
}

unsafe impl<Src: ?Sized> CastFrom<UnsafeCell<Src>> for Src {
    fn cast_from(ptr: *mut UnsafeCell<Src>) -> *mut Src {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `UnsafeCell<Src>` has the same size as `Src`, it also preserves size.
        //
        // [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
        //
        //   `UnsafeCell<T>` has the same in-memory representation as its inner
        //   type `T`.
        ptr as *mut Src
    }
}

// SAFETY: `Unalign<T>` promises to have `UnsafeCell`s covering the same byte
// ranges as `Inner = T`.
unsafe impl<T> UnsafeCellsAgree<T> for Unalign<T> {}
// SAFETY: `Unalign<T>` promises to have `UnsafeCell`s covering the same byte
// ranges as `Inner = T`.
unsafe impl<T> UnsafeCellsAgree<Unalign<T>> for T {}

unsafe impl<Src: Validity> TransmuteFrom<Src> for Src::WithInner<Unalign<Src::Inner>> where
    Src::Inner: Sized
{
}
unsafe impl<Src: Validity> TransmuteFrom<Src::WithInner<Unalign<Src::Inner>>> for Src where
    Src::Inner: Sized
{
}

unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Src, A, Aligned, BecauseUnchanged>
    for Unalign<Src>
{
}
unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Unalign<Src>, A, Unknown, BecauseUnchanged>
    for Src
{
}

unsafe impl<Src> CastFrom<Src> for Unalign<Src> {
    fn cast_from(ptr: *mut Src) -> *mut Unalign<Src> {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Unalign<T>` has the same size as `T`, it also preserves size.
        ptr.cast()
    }
}

unsafe impl<Src> CastFrom<Unalign<Src>> for Src {
    fn cast_from(ptr: *mut Unalign<Src>) -> *mut Src {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Unalign<T>` has the same size as `T`, it also preserves size.
        ptr.cast()
    }
}
