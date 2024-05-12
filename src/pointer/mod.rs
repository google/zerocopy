// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Abstractions over raw pointers.

mod aliasing_safety;
mod ptr;

pub use aliasing_safety::{AliasingSafe, BecauseExclusive, BecauseImmutable};
pub use ptr::{invariant, Ptr};

use core::ptr::NonNull;

use crate::Unaligned;

/// A shorthand for a maybe-valid, maybe-aligned reference. Used as the argument
/// to [`TryFromBytes::is_bit_valid`].
///
/// [`TryFromBytes::is_bit_valid`]: crate::TryFromBytes::is_bit_valid
pub type Maybe<'a, T, Aliasing = invariant::Shared, Alignment = invariant::Any> =
    Ptr<'a, T, (Aliasing, Alignment, invariant::Initialized)>;

/// A semi-user-facing wrapper type representing a maybe-aligned reference, for
/// use in [`TryFromBytes::is_bit_valid`].
///
/// [`TryFromBytes::is_bit_valid`]: crate::TryFromBytes::is_bit_valid
pub type MaybeAligned<'a, T, Aliasing = invariant::Shared, Alignment = invariant::Any> =
    Ptr<'a, T, (Aliasing, Alignment, invariant::Valid)>;

// These methods are defined on the type alias, `MaybeAligned`, so as to bring
// them to the forefront of the rendered rustdoc for that type alias.
impl<'a, T, Aliasing, Alignment> MaybeAligned<'a, T, Aliasing, Alignment>
where
    T: 'a + ?Sized,
    Aliasing: invariant::Aliasing + invariant::AtLeast<invariant::Shared>,
    Alignment: invariant::Alignment,
{
    /// Reads the value from `MaybeAligned`.
    #[must_use]
    #[inline]
    pub fn read_unaligned(self) -> T
    where
        T: Copy,
    {
        let raw = self.as_non_null().as_ptr();
        // SAFETY: By invariant on `MaybeAligned`, `raw` contains
        // validly-initialized data for `T`. The value is safe to read and
        // return, because `T` is copy.
        unsafe { core::ptr::read_unaligned(raw) }
    }

    /// Views the value as an aligned reference.
    ///
    /// This is only available if `T` is [`Unaligned`].
    #[must_use]
    #[inline]
    pub fn unaligned_as_ref(self) -> &'a T
    where
        T: Unaligned,
    {
        self.bikeshed_recall_aligned().as_ref()
    }
}

/// Checks if the referent is zeroed.
pub(crate) fn is_zeroed<T, I>(ptr: Ptr<'_, T, I>) -> bool
where
    T: crate::Immutable + crate::KnownLayout,
    I: invariant::Invariants<Validity = invariant::Initialized>,
    I::Aliasing: invariant::AtLeast<invariant::Shared>,
{
    ptr.as_bytes::<BecauseImmutable>().as_ref().iter().all(|&byte| byte == 0)
}

pub unsafe trait Pointer<'a, T: ?Sized> {
    type Pointer<U: 'a + ?Sized>: Pointer<'a, U, Aliasing = Self::Aliasing>;
    type Aliasing: invariant::Aliasing;

    fn into_raw(self) -> NonNull<T>;

    fn from_ptr<I>(ptr: Ptr<'a, T, I>) -> Self
    where
        I: invariant::Invariants<
            Aliasing = Self::Aliasing,
            Alignment = invariant::Aligned,
            Validity = invariant::Valid,
        >;
}

unsafe impl<'a, T: ?Sized> Pointer<'a, T> for &'a T {
    type Pointer<U: 'a + ?Sized> = &'a U;
    type Aliasing = invariant::Shared;

    fn into_raw(self) -> NonNull<T> {
        NonNull::from(self)
    }

    fn from_ptr<I>(ptr: Ptr<'a, T, I>) -> Self
    where
        I: invariant::Invariants<
            Aliasing = invariant::Shared,
            Alignment = invariant::Aligned,
            Validity = invariant::Valid,
        >,
    {
        ptr.as_ref()
    }
}

unsafe impl<'a, T: ?Sized> Pointer<'a, T> for &'a mut T {
    type Pointer<U: 'a + ?Sized> = &'a mut U;
    type Aliasing = invariant::Exclusive;

    fn into_raw(self) -> NonNull<T> {
        NonNull::from(self)
    }

    fn from_ptr<I>(ptr: Ptr<'a, T, I>) -> Self
    where
        I: invariant::Invariants<
            Aliasing = invariant::Exclusive,
            Alignment = invariant::Aligned,
            Validity = invariant::Valid,
        >,
    {
        ptr.as_mut()
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> Pointer<'static, T> for alloc::boxed::Box<T> {
    type Pointer<U: 'static + ?Sized> = alloc::boxed::Box<U>;
    type Aliasing = invariant::Owned;

    fn into_raw(self) -> NonNull<T> {
        let ptr = alloc::boxed::Box::into_raw(self);
        // SAFETY: TODO
        unsafe { NonNull::new_unchecked(ptr) }
    }

    fn from_ptr<I>(ptr: Ptr<'static, T, I>) -> Self
    where
        I: invariant::Invariants<
            Aliasing = invariant::Owned,
            Alignment = invariant::Aligned,
            Validity = invariant::Valid,
        >,
    {
        ptr.into_box()
    }
}
