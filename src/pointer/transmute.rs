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

#[cfg_attr(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS, marker)]
pub(crate) unsafe trait TransmuteFromPtr<T: ?Sized, A: Aliasing, R>:
    TransmuteFrom<T>
{
}

// unsafe impl<T, U> TransmuteFromPtr<T, Inaccessible, BecauseImmutable> for U
// where
//     T: ?Sized,
//     U: ?Sized + TransmuteFrom<T, UnsafeCellAgreement = UnsafeCellsAgree>,
// {
// }

unsafe impl<T, U> TransmuteFromPtr<T, Shared, BecauseImmutable> for U
where
    T: ?Sized + UnsafeCellsAgree<U>,
    U: ?Sized + TransmuteFrom<T> + UnsafeCellsAgree<T> + crate::Immutable,
{
}

define_because!(pub(crate) BecauseBidirectional);
unsafe impl<T, U, A> TransmuteFromPtr<T, A, BecauseBidirectional> for U
where
    A: Aliasing,
    T: ?Sized + TransmuteFrom<U> + UnsafeCellsAgree<U>,
    U: ?Sized + TransmuteFrom<T> + UnsafeCellsAgree<T>,
{
}

// No UnsafeCell agreement required
//
// TODO: The `UnsafeCellAgreement = UnsafeCellsDisagree` bounds are unnecessary,
// but they make it so that, when calling `Ptr::transmute`, it's unambiguous
// whether this impl should apply or the `BecauseBidirectional` impl, and avoids
// the user needing to explicitly provide a reason parameter. Maybe we should
// remove these bounds?
define_because!(BecauseExclusive);
unsafe impl<T, U> TransmuteFromPtr<T, Exclusive, BecauseExclusive> for U
where
    T: ?Sized + TransmuteFrom<U>,
    U: ?Sized + TransmuteFrom<T>,
{
}

// TODO: Add `UnsafeCellAgreement` (sealed) trait

// pub(crate) enum UnsafeCellsAgree {} // Or `UnsafeCellMatch`? Or just `Agree` since it'll always be used in a where bound?
// pub(crate) enum UnsafeCellsDisagree {} // Or `UnsafeCellMismatch`? Or just `Disagree`?

pub(crate) unsafe trait UnsafeCellsAgree<T: ?Sized>
where
    T: UnsafeCellsAgree<Self>,
{
}
unsafe impl<T: ?Sized> UnsafeCellsAgree<T> for T {}
// unsafe impl<T: ?Sized, U: ?Sized + UnsafeCellsAgree<T>> UnsafeCellsAgree<U> for T {}

pub(crate) unsafe trait TransmuteFrom<T: ?Sized> {
    // TODO: This isn't a bidirectional property (you can't have T -> U
    // UnsafeCells agree but U -> T UnsafeCells disagree). Maybe this should be
    // a super-trait or something?
    // type UnsafeCellAgreement;

    // type Mapping: Mapping;
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

unsafe impl<T: ?Sized> TransmuteFrom<T> for T {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    type AlignmentMapping = Preserved;
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut T {
        ptr
    }
}

unsafe impl<T> UnsafeCellsAgree<T> for MaybeUninit<T> {}
unsafe impl<T> TransmuteFrom<T> for MaybeUninit<T> {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    // type Mapping = (Preserved, Preserved, Valid);
    type AlignmentMapping = Preserved;
    type ValidityMapping = Valid;

    fn cast_from(ptr: *mut T) -> *mut MaybeUninit<T> {
        ptr.cast()
    }
}

unsafe impl<T> UnsafeCellsAgree<MaybeUninit<T>> for T {}
unsafe impl<T> TransmuteFrom<MaybeUninit<T>> for T {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    // type Mapping = (Preserved, Preserved, Unknown);
    type AlignmentMapping = Preserved;
    type ValidityMapping = Unknown;

    fn cast_from(ptr: *mut MaybeUninit<T>) -> *mut T {
        ptr.cast()
    }
}

unsafe impl<T: ?Sized> UnsafeCellsAgree<T> for ManuallyDrop<T> {}
unsafe impl<T: ?Sized> TransmuteFrom<T> for ManuallyDrop<T> {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    type AlignmentMapping = Preserved;
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut T) -> *mut ManuallyDrop<T> {
        ptr as *mut ManuallyDrop<T>
    }
}

unsafe impl<T: ?Sized> UnsafeCellsAgree<ManuallyDrop<T>> for T {}
unsafe impl<T: ?Sized> TransmuteFrom<ManuallyDrop<T>> for T {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    type AlignmentMapping = Preserved;
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut ManuallyDrop<T>) -> *mut T {
        ptr as *mut T
    }
}

unsafe impl<T> UnsafeCellsAgree<T> for Wrapping<T> {}
unsafe impl<T> TransmuteFrom<T> for Wrapping<T> {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    type AlignmentMapping = Preserved;
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut Wrapping<T> {
        ptr.cast()
    }
}

unsafe impl<T> UnsafeCellsAgree<Wrapping<T>> for T {}
unsafe impl<T> TransmuteFrom<Wrapping<T>> for T {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    type AlignmentMapping = Preserved;
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut Wrapping<T>) -> *mut T {
        ptr.cast()
    }
}

unsafe impl<T: ?Sized> TransmuteFrom<T> for UnsafeCell<T> {
    // type UnsafeCellAgreement = UnsafeCellsDisagree;
    // type Mapping = (UnsafeCellMismatch, Preserved, Preserved);
    type AlignmentMapping = Preserved;
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut T) -> *mut UnsafeCell<T> {
        ptr as *mut UnsafeCell<T>
    }
}

unsafe impl<T: ?Sized> TransmuteFrom<UnsafeCell<T>> for T {
    // type UnsafeCellAgreement = UnsafeCellsDisagree;
    // type Mapping = (UnsafeCellMismatch, Preserved, Preserved);
    type AlignmentMapping = Preserved;
    type ValidityMapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut UnsafeCell<T>) -> *mut T {
        ptr as *mut T
    }
}

unsafe impl<T> UnsafeCellsAgree<T> for Unalign<T> {}
unsafe impl<T> TransmuteFrom<T> for Unalign<T> {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    // type Mapping = (Preserved, Aligned, Preserved);
    type AlignmentMapping = Aligned;
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut Unalign<T> {
        ptr.cast()
    }
}

unsafe impl<T> UnsafeCellsAgree<Unalign<T>> for T {}
unsafe impl<T> TransmuteFrom<Unalign<T>> for T {
    // type UnsafeCellAgreement = UnsafeCellsAgree;
    // type Mapping = (Preserved, Unknown, Preserved);
    type AlignmentMapping = Unknown;
    type ValidityMapping = Preserved;

    fn cast_from(ptr: *mut Unalign<T>) -> *mut T {
        ptr.cast()
    }
}
