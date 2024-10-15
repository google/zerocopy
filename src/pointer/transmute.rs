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

// T -> U
// U: TransmuteFrom<T, Mapping::Aliasing = Preserved>
// T: Read<A, R>
//
// U: Read<A, R>

/// [`Ptr`](crate::Ptr) referents that disallow mutation.
///
/// `T: NoWrite<A>` implies that a pointer to `T` with aliasing `A` does not
/// permit mutation. This can be because `A` is [`Inaccessible`] or because `A`
/// is [`Shared`] and `T` does not permit interior mutation.
///
/// # Safety
///
/// If `T: NoWrite<A>`, then any `Ptr<T, (A, ...)>` is guaranteed not to be able
/// to mutate its referent.
trait NoWrite<A: Aliasing> {}

impl<T: ?Sized> NoWrite<Inaccessible> for T {}
impl<T: ?Sized + crate::Immutable> NoWrite<Shared> for T {}

pub unsafe trait TransmuteFromPtr<T: ?Sized, A: Aliasing, R>: TransmuteFrom<T> {}

pub enum BecauseNoWrite {}
unsafe impl<T, U, A> TransmuteFromPtr<T, A, BecauseNoWrite> for U
where
    A: Aliasing,
    T: ?Sized,
    U: ?Sized + TransmuteFrom<T> + NoWrite<A>,
{
}

pub enum BecauseBidirectional {}
unsafe impl<T, U, A> TransmuteFromPtr<T, A, BecauseBidirectional> for U
where
    A: Aliasing,
    T: ?Sized + TransmuteFrom<U>,
    U: ?Sized + TransmuteFrom<T>,
{
}

pub unsafe trait TransmuteFrom<T: ?Sized> {
    type Mapping: Mapping;

    /// Casts a `*mut T` to a `*mut Self`.
    ///
    /// # Safety
    ///
    /// The resulting pointer has the same address and provenance as `ptr`, and
    /// addresses the same number of bytes.
    fn cast_from(ptr: *mut T) -> *mut Self;
}

unsafe impl<T: ?Sized> TransmuteFrom<T> for T {
    type Mapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut T {
        ptr
    }
}

unsafe impl<T> TransmuteFrom<T> for MaybeUninit<T> {
    type Mapping = (Preserved, Preserved, Valid);

    fn cast_from(ptr: *mut T) -> *mut MaybeUninit<T> {
        ptr.cast()
    }
}

unsafe impl<T> TransmuteFrom<MaybeUninit<T>> for T {
    type Mapping = (Preserved, Preserved, Unknown);

    fn cast_from(ptr: *mut MaybeUninit<T>) -> *mut T {
        ptr.cast()
    }
}

unsafe impl<T: ?Sized> TransmuteFrom<T> for ManuallyDrop<T> {
    type Mapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut T) -> *mut ManuallyDrop<T> {
        ptr as *mut ManuallyDrop<T>
    }
}

unsafe impl<T: ?Sized> TransmuteFrom<ManuallyDrop<T>> for T {
    type Mapping = Preserved;

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut ManuallyDrop<T>) -> *mut T {
        ptr as *mut T
    }
}

unsafe impl<T> TransmuteFrom<T> for Wrapping<T> {
    type Mapping = Preserved;

    fn cast_from(ptr: *mut T) -> *mut Wrapping<T> {
        ptr.cast()
    }
}

unsafe impl<T> TransmuteFrom<Wrapping<T>> for T {
    type Mapping = Preserved;

    fn cast_from(ptr: *mut Wrapping<T>) -> *mut T {
        ptr.cast()
    }
}

unsafe impl<T: ?Sized> TransmuteFrom<T> for UnsafeCell<T> {
    type Mapping = (UnsafeCellMismatch, Preserved, Preserved);

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut T) -> *mut UnsafeCell<T> {
        ptr as *mut UnsafeCell<T>
    }
}

unsafe impl<T: ?Sized> TransmuteFrom<UnsafeCell<T>> for T {
    type Mapping = (UnsafeCellMismatch, Preserved, Preserved);

    #[allow(clippy::as_conversions)]
    fn cast_from(ptr: *mut UnsafeCell<T>) -> *mut T {
        ptr as *mut T
    }
}

unsafe impl<T> TransmuteFrom<T> for Unalign<T> {
    type Mapping = (Preserved, Aligned, Preserved);

    fn cast_from(ptr: *mut T) -> *mut Unalign<T> {
        ptr.cast()
    }
}

unsafe impl<T> TransmuteFrom<Unalign<T>> for T {
    type Mapping = (Preserved, Unknown, Preserved);

    fn cast_from(ptr: *mut Unalign<T>) -> *mut T {
        ptr.cast()
    }
}

unsafe impl<T, const N: usize> TransmuteFrom<[T; N]> for [T] {
    type Mapping = Preserved;

    fn cast_from(ptr: *mut [T; N]) -> *mut [T] {
        unsafe { core::ptr::slice_from_raw_parts_mut(ptr.cast(), N) }
    }
}
