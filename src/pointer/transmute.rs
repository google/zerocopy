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

use crate::{
    pointer::invariant::{self, Invariants},
    Unalign,
};

/// A type which has the same layout as the type it wraps.
///
/// # Safety
///
/// `T: TransparentWrapper` implies that `T` has the same size as [`T::Inner`].
/// Further, `T: TransparentWrapper<I>` implies that:
/// - If `T::UnsafeCellVariance = Covariant`, then `T` has `UnsafeCell`s
///   covering the same byte ranges as `T::Inner`.
/// - If a `T` pointer satisfies the alignment invariant `I::Alignment`, then
///   that same pointer, cast to `T::Inner`, satisfies the alignment invariant
///   `<T::AlignmentVariance as AlignmentVariance<I::Alignment>>::Applied`.
/// - If a `T` pointer satisfies the validity invariant `I::Validity`, then that
///   same pointer, cast to `T::Inner`, satisfies the validity invariant
///   `<T::ValidityVariance as ValidityVariance<I::Validity>>::Applied`.
///
/// [`T::Inner`]: TransparentWrapper::Inner
/// [`UnsafeCell`]: core::cell::UnsafeCell
/// [`T::AlignmentVariance`]: TransparentWrapper::AlignmentVariance
/// [`T::ValidityVariance`]: TransparentWrapper::ValidityVariance
#[doc(hidden)]
pub unsafe trait TransparentWrapper<I: Invariants> {
    type Inner: ?Sized;

    type UnsafeCellVariance;
    type AlignmentVariance: AlignmentVariance<I::Alignment>;
    type ValidityVariance: ValidityVariance<I::Validity>;

    /// Casts a wrapper pointer to an inner pointer.
    ///
    /// # Safety
    ///
    /// The resulting pointer has the same address and provenance as `ptr`, and
    /// addresses the same number of bytes.
    fn cast_into_inner(ptr: *mut Self) -> *mut Self::Inner;

    /// Casts an inner pointer to a wrapper pointer.
    ///
    /// # Safety
    ///
    /// The resulting pointer has the same address and provenance as `ptr`, and
    /// addresses the same number of bytes.
    fn cast_from_inner(ptr: *mut Self::Inner) -> *mut Self;
}

#[allow(unreachable_pub)]
#[doc(hidden)]
pub trait AlignmentVariance<I: invariant::Alignment> {
    type Applied: invariant::Alignment;
}

#[allow(unreachable_pub)]
#[doc(hidden)]
pub trait ValidityVariance<I: invariant::Validity> {
    type Applied: invariant::Validity;
}

#[doc(hidden)]
#[allow(missing_copy_implementations, missing_debug_implementations)]
pub enum Covariant {}

impl<I: invariant::Alignment> AlignmentVariance<I> for Covariant {
    type Applied = I;
}

impl<I: invariant::Validity> ValidityVariance<I> for Covariant {
    type Applied = I;
}

#[doc(hidden)]
#[allow(missing_copy_implementations, missing_debug_implementations)]
pub enum Invariant {}

impl<I: invariant::Alignment> AlignmentVariance<I> for Invariant {
    type Applied = invariant::Unknown;
}

impl<I: invariant::Validity> ValidityVariance<I> for Invariant {
    type Applied = invariant::Unknown;
}

// SAFETY:
// - Per [1], `MaybeUninit<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
//
//   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and ABI as
//   `T`
unsafe impl<T, I: Invariants> TransparentWrapper<I> for MaybeUninit<T> {
    type Inner = T;

    // SAFETY: `MaybeUninit<T>` has `UnsafeCell`s covering the same byte ranges
    // as `Inner = T`. This is not explicitly documented, but it can be
    // inferred. Per [1] in the preceding safety comment, `MaybeUninit<T>` has
    // the same size as `T`. Further, note the signature of
    // `MaybeUninit::assume_init_ref` [2]:
    //
    //   pub unsafe fn assume_init_ref(&self) -> &T
    //
    // If the argument `&MaybeUninit<T>` and the returned `&T` had `UnsafeCell`s
    // at different offsets, this would be unsound. Its existence is proof that
    // this is not the case.
    //
    // [2] https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#method.assume_init_ref
    type UnsafeCellVariance = Covariant;
    // SAFETY: Per [1], `MaybeUninit<T>` has the same layout as `T`, and thus
    // has the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#layout-1:
    //
    //   `MaybeUninit<T>` is guaranteed to have the same size, alignment, and
    //   ABI as `T`.
    type AlignmentVariance = Covariant;
    // SAFETY: `MaybeUninit` has no validity invariants. Thus, a valid
    // `MaybeUninit<T>` is not necessarily a valid `T`.
    type ValidityVariance = Invariant;

    #[inline(always)]
    fn cast_into_inner(ptr: *mut MaybeUninit<T>) -> *mut T {
        // SAFETY: Per [1] (from comment above), `MaybeUninit<T>` has the same
        // layout as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        ptr.cast::<T>()
    }

    #[inline(always)]
    fn cast_from_inner(ptr: *mut T) -> *mut MaybeUninit<T> {
        // SAFETY: Per [1] (from comment above), `MaybeUninit<T>` has the same
        // layout as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        ptr.cast::<MaybeUninit<T>>()
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
unsafe impl<T: ?Sized, I: Invariants> TransparentWrapper<I> for ManuallyDrop<T> {
    type Inner = T;

    // SAFETY: Per [1], `ManuallyDrop<T>` has `UnsafeCell`s covering the same
    // byte ranges as `Inner = T`.
    //
    // [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
    //
    //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
    //   validity as `T`, and is subject to the same layout optimizations as
    //   `T`. As a consequence, it has no effect on the assumptions that the
    //   compiler makes about its contents.
    type UnsafeCellVariance = Covariant;
    // SAFETY: Per [1], `ManuallyDrop<T>` has the same layout as `T`, and thus
    // has the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/nightly/core/mem/struct.ManuallyDrop.html:
    //
    //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
    //   validity as `T`
    type AlignmentVariance = Covariant;

    // SAFETY: Per [1] (from comment above), `ManuallyDrop<T>` has the same bit
    // validity as `T`.
    type ValidityVariance = Covariant;

    #[inline(always)]
    fn cast_into_inner(ptr: *mut ManuallyDrop<T>) -> *mut T {
        // SAFETY: Per [1] (from comment above), `ManuallyDrop<T>` has the same
        // layout as `T`. Thus, this cast preserves size even if `T` is unsized.
        //
        // This cast trivially preserves provenance.
        #[allow(clippy::as_conversions)]
        return ptr as *mut T;
    }

    #[inline(always)]
    fn cast_from_inner(ptr: *mut T) -> *mut ManuallyDrop<T> {
        // SAFETY: Per [1] (from comment above), `ManuallyDrop<T>` has the same
        // layout as `T`. Thus, this cast preserves size even if `T` is unsized.
        //
        // This cast trivially preserves provenance.
        #[allow(clippy::as_conversions)]
        return ptr as *mut ManuallyDrop<T>;
    }
}

// SAFETY:
// - Per [1], `Wrapping<T>` has the same size as `T`.
// - See inline comments for other safety justifications.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
unsafe impl<T, I: Invariants> TransparentWrapper<I> for Wrapping<T> {
    type Inner = T;

    // SAFETY: Per [1], `Wrapping<T>` has the same layout as `T`. Since its
    // single field (of type `T`) is public, it would be a breaking change to
    // add or remove fields. Thus, we know that `Wrapping<T>` contains a `T` (as
    // opposed to just having the same size and alignment as `T`) with no pre-
    // or post-padding. Thus, `Wrapping<T>` must have `UnsafeCell`s covering the
    // same byte ranges as `Inner = T`.
    //
    // [1] Per https://doc.rust-lang.org/1.81.0/std/num/struct.Wrapping.html#layout-1:
    //
    //   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
    type UnsafeCellVariance = Covariant;
    // SAFETY: Per [1], `Wrapping<T>` has the same layout as `T`, and thus has
    // the same alignment as `T`.
    //
    // [1] Per https://doc.rust-lang.org/core/num/struct.Wrapping.html#layout-1:
    //
    //   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
    type AlignmentVariance = Covariant;

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
    // [2] https://doc.rust-lang.org/core/num/struct.Wrapping.html
    type ValidityVariance = Covariant;

    #[inline(always)]
    fn cast_into_inner(ptr: *mut Wrapping<T>) -> *mut T {
        // SAFETY: Per [1] (from comment above), `Wrapping<T>` has the same
        // layout as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        ptr.cast::<T>()
    }

    #[inline(always)]
    fn cast_from_inner(ptr: *mut T) -> *mut Wrapping<T> {
        // SAFETY: Per [1] (from comment above), `Wrapping<T>` has the same
        // layout as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        ptr.cast::<Wrapping<T>>()
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
unsafe impl<T: ?Sized, I: Invariants> TransparentWrapper<I> for UnsafeCell<T> {
    type Inner = T;

    // SAFETY: Since we set this to `Invariant`, we make no safety claims.
    type UnsafeCellVariance = Invariant;

    // SAFETY: Per [1] (from comment on impl), `Unalign<T>` has the same
    // representation as `T`, and thus has the same alignment as `T`.
    type AlignmentVariance = Covariant;

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
    type ValidityVariance = Covariant;

    #[inline(always)]
    fn cast_into_inner(ptr: *mut UnsafeCell<T>) -> *mut T {
        // SAFETY: Per [1] (from comment above), `UnsafeCell<T>` has the same
        // representation as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        #[allow(clippy::as_conversions)]
        return ptr as *mut T;
    }

    #[inline(always)]
    fn cast_from_inner(ptr: *mut T) -> *mut UnsafeCell<T> {
        // SAFETY: Per [1] (from comment above), `UnsafeCell<T>` has the same
        // representation as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        #[allow(clippy::as_conversions)]
        return ptr as *mut UnsafeCell<T>;
    }
}

// SAFETY: `Unalign<T>` promises to have the same size as `T`.
//
// See inline comments for other safety justifications.
unsafe impl<T, I: Invariants> TransparentWrapper<I> for Unalign<T> {
    type Inner = T;

    // SAFETY: `Unalign<T>` promises to have `UnsafeCell`s covering the same
    // byte ranges as `Inner = T`.
    type UnsafeCellVariance = Covariant;

    // SAFETY: Since `Unalign<T>` promises to have alignment 1 regardless of
    // `T`'s alignment. Thus, an aligned pointer to `Unalign<T>` is not
    // necessarily an aligned pointer to `T`.
    type AlignmentVariance = Invariant;

    // SAFETY: `Unalign<T>` promises to have the same validity as `T`.
    type ValidityVariance = Covariant;

    #[inline(always)]
    fn cast_into_inner(ptr: *mut Unalign<T>) -> *mut T {
        // SAFETY: Per the safety comment on the impl block, `Unalign<T>` has
        // the size as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        ptr.cast::<T>()
    }

    #[inline(always)]
    fn cast_from_inner(ptr: *mut T) -> *mut Unalign<T> {
        // SAFETY: Per the safety comment on the impl block, `Unalign<T>` has
        // the size as `T`. Thus, this cast preserves size.
        //
        // This cast trivially preserves provenance.
        ptr.cast::<Unalign<T>>()
    }
}
