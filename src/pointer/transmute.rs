// Copyright 2024 The Fuchsia Authors
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

use crate::{pointer::invariant::*, Unalign};

/// A type which supports pointer casting from another type, `T`.
///
/// # Safety
///
/// If `U: TransmuteFromPtr<T, A, R>`, then given `t: *const T` which satisfies
/// aliasing `A`, alignment `AA`, and validity `V`, it is sound to treat `t as
/// *const U` as a pointer with aliasing `A`, alignment `MappedAlignment<AA, <U
/// as TransmuteFrom<T>>::AlignmentMapping>`, and validity `MappedValidity<V, <U
/// as TransmuteFrom<T>>::ValidityMapping>`.
///
/// If `A` is `Shared`, then this implies that, in the region referred to by
/// both `t` and `u`, `*t` and `*u` contain `UnsafeCell`s at the same byte
/// ranges. Thus, for `Shared` aliasing, it is not possible for `t` to perform
/// interior mutation which violates `u`'s `Shared` aliasing invariant, or
/// vice-versa.
#[cfg_attr(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS, marker)]
pub(crate) unsafe trait TransmuteFromPtrOld<T: ?Sized, A: Aliasing, R>:
    TransmuteFromOld<T>
{
}

// SAFETY: Let `t: *const T` satisfying `Shared` aliasing, alignment `A`, and
// validity `V`. Let `u = t as *const U`. By safety invariant on `U:
// TransmuteFrom<T>`, `u` satisfies alignment `MappedAlignment<A, <U as
// TransmuteFrom<T>>::AlignmentMapping>`.
//
// Because `U: Immutable`, `u` with aliasing `Shared` will not be permitted to
// write to its referent. Thus, if `t` already satisfies validity `V`, that will
// continue to hold even though we don't require that `T: TransmuteFrom<U>`.
//
// By safety invariant on `U: TransmuteFrom<T>`, `u` satisfies validity
// `MappedValidity<V, <U as TransmuteFrom<T>>::ValidityMapping>`.
//
// By safety invariant on `T: UnsafeCellsAgree<U>`, `t` and `u` reference
// `UnsafeCell`s at the same byte ranges (at least within the region of memory
// which they both address). By `U: Immutable`, that range contains no
// `UnsafeCell`s. Thus, it is not possible for `u` to be used to perform
// interior mutation which violate's `t`'s `Shared` aliasing invariant, and
// vice-versa.
//
// NOTE: We could equivalently implement this for `T: Immutable, U: Immutable`
// and drop the `UnsafeCellsAgree` bounds. However, this permits us to support
// `T: !Immutable`. Perhaps we should eventually add a second impl with `T:
// Immutable, U: Immutable` instead.
unsafe impl<T, U> TransmuteFromPtrOld<T, Shared, BecauseImmutable> for U
where
    T: ?Sized + UnsafeCellsAgree<U>,
    U: ?Sized + TransmuteFromOld<T> + UnsafeCellsAgree<T> + crate::Immutable,
{
}

define_because!(pub(crate) BecauseBidirectional);

// SAFETY: Let `t: *const T` satisfying `Shared` aliasing, alignment `A`, and
// validity `V`. Let `u = t as *const U`. By safety invariant on `U:
// TransmuteFrom<T>`, `u` satisfies alignment `MappedAlignment<A, <U
// as TransmuteFrom<T>>::AlignmentMapping>`.
//
// Because `T: TransmuteFrom<U, ValidityMapping = Preserved>` and `U:
// TransmuteFrom<T, ValidityMapping = Preserved>`, `T` and `U` have identical
// bit validity. Thus, any value written through the resulting `U` pointer will
// satisfy whatever validity invariant is present on the original `T` pointer.
//
// By safety invariant on `U: TransmuteFrom<T>`, `u` satisfies validity
// `MappedValidity<V, <U as TransmuteFrom<T>>::ValidityMapping>`.
//
// By safety invariant on `T: UnsafeCellsAgree<U>`, `t` and `u` reference
// `UnsafeCell`s at the same byte ranges (at least within the region of memory
// which they both address). Thus, if `A` is `Shared`, it is not possible for
// `u` to be used to perform interior mutation which violate's `t` `Shared`
// aliasing invariant, and vice-versa.
//
// TODO(#1945): If we permit arbitrary invariant mappings, we can relax this
// bound and not require `ValidityMapping = Preserved`.
unsafe impl<T, U, A> TransmuteFromPtrOld<T, A, BecauseBidirectional> for U
where
    A: Aliasing,
    T: ?Sized + TransmuteFromOld<U, ValidityMapping = Preserved> + UnsafeCellsAgree<U>,
    U: ?Sized + TransmuteFromOld<T, ValidityMapping = Preserved> + UnsafeCellsAgree<T>,
{
}

define_because!(BecauseExclusive);
unsafe impl<T, U> TransmuteFromPtrOld<T, Exclusive, BecauseExclusive> for U
where
    T: ?Sized + TransmuteFromOld<U, ValidityMapping = Preserved>,
    U: ?Sized + TransmuteFromOld<T, ValidityMapping = Preserved>,
{
}

#[cfg_attr(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS, marker)]
pub(crate) unsafe trait TransmuteFromPtr<Src: ?Sized, A: Aliasing, SV: Validity, DV: Validity, R>:
    CastFrom<Src> + TransmuteFrom<Src, SV, DV>
{
}

unsafe impl<Src, Dst, SV, DV> TransmuteFromPtr<Src, Shared, SV, DV, BecauseImmutable> for Dst
where
    Src: ?Sized + crate::Immutable,
    Dst: ?Sized + TransmuteFrom<Src, SV, DV> + CastFrom<Src> + crate::Immutable,
    SV: Validity,
    DV: Validity,
{
}

unsafe impl<Src, Dst, A, SV, DV> TransmuteFromPtr<Src, A, SV, DV, BecauseBidirectional> for Dst
where
    A: Aliasing,
    Src: ?Sized + TransmuteFrom<Dst, DV, SV> + UnsafeCellsAgree<Dst>,
    Dst: ?Sized + TransmuteFrom<Src, SV, DV> + UnsafeCellsAgree<Src> + CastFrom<Src>,
    SV: Validity,
    DV: Validity,
{
}

unsafe impl<Src, Dst, SV, DV> TransmuteFromPtr<Src, Exclusive, SV, DV, BecauseExclusive> for Dst
where
    Src: ?Sized + TransmuteFrom<Dst, DV, SV>,
    Dst: ?Sized + TransmuteFrom<Src, SV, DV> + CastFrom<Src>,
    SV: Validity,
    DV: Validity,
{
}

pub(crate) unsafe trait TransmuteFromAlignment<Src: ?Sized, SA: Alignment, DA: Alignment> {}

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

pub(crate) unsafe trait TransmuteFrom<Src: ?Sized, SV, DV> {}

/// A type which can be transmuted from another type, `T`.
///
/// # Safety
///
/// If `U: TransmuteFrom<T>`, then the following must hold:
/// - Given `t: *const T`, `t as *const U` must produce a pointer which
///   references the same number of bytes as `t`
/// - If `t: *const T` satisfies the alignment invariant `A`, then `t as *const
///   U` satisfies the alignment invariant `MappedAlignment<A,
///   U::AlignmentMapping>`
/// - If `t: *const T` satisfies the validity invariant `V`, then `t as *const
///   U` satisfies the validity invariant `MappedValidity<V,
///   U::ValidityMapping>`
// TODO(#1940): Relax the safety invariant to support size mismatch and pairs of
// types which require a metadata fix-up.
//
// TODO(#1945): Adopt an alternative encoding of invariant mappings?
pub(crate) unsafe trait TransmuteFromOld<T: ?Sized> {
    type AlignmentMapping: AlignmentMapping;
    type ValidityMapping: ValidityMapping;

    /// Casts a `*mut T` to a `*mut Self`.
    ///
    /// # Safety
    ///
    /// The resulting pointer has the same address and provenance as `ptr`, and
    /// addresses the same number of bytes.
    fn cast_from(ptr: *mut T) -> *mut Self;
}

unsafe impl<Src: ?Sized> CastFrom<Src> for Src {
    fn cast_from(ptr: *mut Src) -> *mut Src {
        // SAFETY: `ptr` trivially has the same address as, addresses the same
        // number of bytes as, and has the same provenance as `ptr`.
        ptr
    }
}

unsafe impl<Src: ?Sized, V: Validity> TransmuteFrom<Src, V, V> for Src {}
unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<Src, A, A> for Src {}

// SAFETY:
// - Given `t: *const T`, `t as *const T` is a no-op, and so trivially produces
//   a pointer which references the same number of bytes as `t`
// - Alignment: See inline safety comment.
// - Validity: See inline safety comment.
unsafe impl<T: ?Sized> TransmuteFromOld<T> for T {
    // Given a `t: *const T` with alignment `A`, `t as *const T` is a no-op, and
    // so trivially satisfies the alignment invariant `MappedAlignment<A,
    // Preserved> = A`.
    type AlignmentMapping = Preserved;
    // Given a `t: *const T` with validity `V`, `t as *const T` is a no-op, and
    // so trivially satisfies the validity invariant `MappedValidity<V,
    // Preserved> = V`.
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut T {
        // SAFETY: `ptr` trivially preserves address, referent size, and
        // provenance.
        ptr
    }
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

unsafe impl<Src, V: Validity> TransmuteFrom<Src, V, Valid> for MaybeUninit<Src> {}
unsafe impl<Src, V: Validity> TransmuteFrom<Src, V, AsInitialized> for MaybeUninit<Src> {}
unsafe impl<Src> TransmuteFrom<Src, Initialized, Initialized> for MaybeUninit<Src> {}

unsafe impl<Src> TransmuteFrom<MaybeUninit<Src>, Initialized, Initialized> for Src {}
unsafe impl<Src, V: Validity> TransmuteFrom<MaybeUninit<Src>, V, Unknown> for Src {}

unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Src, A, A> for MaybeUninit<Src> {}
unsafe impl<Src, A: Alignment> TransmuteFromAlignment<MaybeUninit<Src>, A, A> for Src {}

// SAFETY:
// - Per [1], `MaybeUninit<T>` has the same size as `T`.
// - Alignment: See inline safety comment.
// - Validity: See inline safety comment.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
//
//   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and ABI as
//   `T`
unsafe impl<T> TransmuteFromOld<T> for MaybeUninit<T> {
    // SAFETY: Per [1], `MaybeUninit<T>` has the same layout as `T`, and thus
    // has the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#layout-1:
    //
    //   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and
    //   ABI as `T`.
    type AlignmentMapping = Preserved;
    // SAFETY: `MaybeUninit` has no validity invariants. Thus, any `m: *const
    // MaybeUninit<T>` always satisfies the validity invariant `Valid`.
    type ValidityMapping = Valid;

    fn cast_from(ptr: *mut T) -> *mut MaybeUninit<T> {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `MaybeUninit<T>` has the same size as `T`, it also preserves size.
        ptr.cast()
    }
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

// SAFETY:
// - Per [1], `MaybeUninit<T>` has the same size as `T`.
// - Alignment: See inline safety comment.
// - Validity: See inline safety comment.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
//
//   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and ABI as
//   `T`
unsafe impl<T> TransmuteFromOld<MaybeUninit<T>> for T {
    // SAFETY: Per [1], `MaybeUninit<T>` has the same layout as `T`, and thus
    // has the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#layout-1:
    //
    //   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and
    //   ABI as `T`.
    type AlignmentMapping = Preserved;
    // SAFETY: Any `t: *const T` trivially conforms to the validity invariant
    // `Unknown`.
    type ValidityMapping = Unknown;

    fn cast_from(ptr: *mut MaybeUninit<T>) -> *mut T {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `MaybeUninit<T>` has the same size as `T`, it also preserves size.
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

unsafe impl<Src: ?Sized, V: Validity> TransmuteFrom<Src, V, V> for ManuallyDrop<Src> {}
unsafe impl<Src: ?Sized, V: Validity> TransmuteFrom<ManuallyDrop<Src>, V, V> for Src {}

unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<Src, A, A> for ManuallyDrop<Src> {}
unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<ManuallyDrop<Src>, A, A> for Src {}

// SAFETY:
// - Per [1], `ManuallyDrop<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`
unsafe impl<T: ?Sized> TransmuteFromOld<T> for ManuallyDrop<T> {
    // SAFETY: Per [1], `ManuallyDrop<T>` has the same layout as `T`, and thus
    // has the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/nightly/core/mem/struct.ManuallyDrop.html:
    //
    //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
    //   validity as `T`
    type AlignmentMapping = Preserved;

    // SAFETY: Per [1] (from comment above), `ManuallyDrop<T>` has the same bit
    // validity as `T`.
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut T) -> *mut ManuallyDrop<T> {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `ManuallyDrop<T>` has the same size as `T`, it also preserves size.
        ptr as *mut ManuallyDrop<T>
    }
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

// SAFETY:
// - Per [1], `ManuallyDrop<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`
unsafe impl<T: ?Sized> TransmuteFromOld<ManuallyDrop<T>> for T {
    // SAFETY: Per [1], `ManuallyDrop<T>` has the same layout as `T`, and thus
    // has the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/nightly/core/mem/struct.ManuallyDrop.html:
    //
    //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
    //   validity as `T`
    type AlignmentMapping = Preserved;

    // SAFETY: Per [1] (from comment above), `ManuallyDrop<T>` has the same bit
    // validity as `T`.
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut ManuallyDrop<T>) -> *mut T {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `ManuallyDrop<T>` has the same size as `T`, it also preserves size.
        ptr as *mut T
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

unsafe impl<Src, V: Validity> TransmuteFrom<Src, V, V> for Wrapping<Src> {}
unsafe impl<Src, V: Validity> TransmuteFrom<Wrapping<Src>, V, V> for Src {}

unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Src, A, A> for Wrapping<Src> {}
unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Wrapping<Src>, A, A> for Src {}

// SAFETY:
// - Per [1], `Wrapping<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
unsafe impl<T> TransmuteFromOld<T> for Wrapping<T> {
    // SAFETY: Per [1], `Wrapping<T>` has the same layout as `T`, and thus has
    // the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/core/num/struct.Wrapping.html#layout-1:
    //
    //   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
    type AlignmentMapping = Preserved;

    // SAFETY: `Wrapping<T>` has only one field, which is `pub` [2]. We are also
    // guaranteed per [1] (from the comment above) that `Wrapping<T>` has the
    // same layout as `T`. The only way for both of these to be true
    // simultaneously is for `Wrapping<T>` to have the same bit validity as `T`.
    // In particular, in order to change the bit validity, one of the following
    // would need to happen:
    // - `Wrapping` could change its `repr`, but this would violate the layout
    //   guarantee.
    // - `Wrapping` could add or change its fields, but this would be a
    //   stability-breaking change.
    //
    // [2] https://doc.rust-lang.org/1.82.0/core/num/struct.Wrapping.html
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut Wrapping<T> {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Wrapping<T>` has the same size as `T`, it also preserves size.
        ptr.cast()
    }
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

// SAFETY:
// - Per [1], `Wrapping<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
unsafe impl<T> TransmuteFromOld<Wrapping<T>> for T {
    // SAFETY: Per [1], `Wrapping<T>` has the same layout as `T`, and thus has
    // the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/core/num/struct.Wrapping.html#layout-1:
    //
    //   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
    type AlignmentMapping = Preserved;

    // SAFETY: `Wrapping<T>` has only one field, which is `pub` [2]. We are also
    // guaranteed per [1] (from the comment above) that `Wrapping<T>` has the
    // same layout as `T`. The only way for both of these to be true
    // simultaneously is for `Wrapping<T>` to have the same bit validity as `T`.
    // In particular, in order to change the bit validity, one of the following
    // would need to happen:
    // - `Wrapping` could change its `repr`, but this would violate the layout
    //   guarantee.
    // - `Wrapping` could add or change its fields, but this would be a
    //   stability-breaking change.
    //
    // [2] https://doc.rust-lang.org/1.82.0/core/num/struct.Wrapping.html
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut Wrapping<T>) -> *mut T {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Wrapping<T>` has the same size as `T`, it also preserves size.
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

unsafe impl<Src: ?Sized, V: Validity> TransmuteFrom<Src, V, V> for UnsafeCell<Src> {}
unsafe impl<Src: ?Sized, V: Validity> TransmuteFrom<UnsafeCell<Src>, V, V> for Src {}

unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<Src, A, A> for UnsafeCell<Src> {}
unsafe impl<Src: ?Sized, A: Alignment> TransmuteFromAlignment<UnsafeCell<Src>, A, A> for Src {}

// SAFETY:
// - Per [1], `UnsafeCell<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
//
//   `UnsafeCell<T>` has the same in-memory representation as its inner type
//   `T`.
unsafe impl<T: ?Sized> TransmuteFromOld<T> for UnsafeCell<T> {
    // SAFETY: Per [1] (from comment on impl), `Unalign<T>` has the same
    // representation as `T`, and thus has the same alignment as `T`.
    type AlignmentMapping = Preserved;

    // SAFETY: Per [1], `Unalign<T>` has the same bit validity as `T`.
    // Technically the term "representation" doesn't guarantee this, but the
    // subsequent sentence in the documentation makes it clear that this is the
    // intention.
    //
    // [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
    //
    //   `UnsafeCell<T>` has the same in-memory representation as its inner type
    //   `T`. A consequence of this guarantee is that it is possible to convert
    //   between `T` and `UnsafeCell<T>`.
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut T) -> *mut UnsafeCell<T> {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `UnsafeCell<T>` has the same size as `T`, it also preserves size.
        ptr as *mut UnsafeCell<T>
    }
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

// SAFETY:
// - Per [1], `UnsafeCell<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
//
//   `UnsafeCell<T>` has the same in-memory representation as its inner type
//   `T`.
unsafe impl<T: ?Sized> TransmuteFromOld<UnsafeCell<T>> for T {
    // SAFETY: Per [1] (from comment on impl), `Unalign<T>` has the same
    // representation as `T`, and thus has the same alignment as `T`.
    type AlignmentMapping = Preserved;

    // SAFETY: Per [1], `Unalign<T>` has the same bit validity as `T`.
    // Technically the term "representation" doesn't guarantee this, but the
    // subsequent sentence in the documentation makes it clear that this is the
    // intention.
    //
    // [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
    //
    //   `UnsafeCell<T>` has the same in-memory representation as its inner type
    //   `T`. A consequence of this guarantee is that it is possible to convert
    //   between `T` and `UnsafeCell<T>`.
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut UnsafeCell<T>) -> *mut T {
        // SAFETY: An `as` cast preserves address and provenance. Since
        // `UnsafeCell<T>` has the same size as `T`, it also preserves size.
        ptr as *mut T
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

unsafe impl<Src, V: Validity> TransmuteFrom<Src, V, V> for Unalign<Src> {}
unsafe impl<Src, V: Validity> TransmuteFrom<Unalign<Src>, V, V> for Src {}

unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Src, A, Aligned> for Unalign<Src> {}
unsafe impl<Src, A: Alignment> TransmuteFromAlignment<Unalign<Src>, A, Unknown> for Src {}

// SAFETY: `Unalign<T>` promises to have the same size as `T`.
//
// See inline comments for other safety justifications.
unsafe impl<T> TransmuteFromOld<T> for Unalign<T> {
    // SAFETY: `Unalign<T>` promises to have alignment 1 regardless of `T`'s
    // alignment. Thus, any `u: *const Unalign<T>` is always aligned.
    type AlignmentMapping = Aligned;

    // SAFETY: `Unalign<T>` promises to have the same validity as `T`.
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut Unalign<T> {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Unalign<T>` has the same size as `T`, it also preserves size.
        ptr.cast()
    }
}

unsafe impl<Src> CastFrom<Src> for Unalign<Src> {
    fn cast_from(ptr: *mut Src) -> *mut Unalign<Src> {
        // SAFETY: `.cast()` preserves address and provenance. Since
        // `Unalign<T>` has the same size as `T`, it also preserves size.
        ptr.cast()
    }
}

// SAFETY: `Unalign<T>` promises to have the same size as `T`.
//
// See inline comments for other safety justifications.
unsafe impl<T> TransmuteFromOld<Unalign<T>> for T {
    // SAFETY: `Unalign<T>` promises to have alignment 1 regardless of `T`'s
    // alignment. Thus, an aligned pointer to `Unalign<T>` is not necessarily an
    // aligned pointer to `T`.
    type AlignmentMapping = Unknown;

    // SAFETY: `Unalign<T>` promises to have the same validity as `T`.
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut Unalign<T>) -> *mut T {
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
