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

pub use aliasing_safety::{AliasingSafe, AliasingSafeReason, BecauseExclusive, BecauseImmutable};
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

pub(crate) unsafe trait IntoPtr<'a, T: ?Sized> {
    type Aliasing: invariant::Aliasing;
    type Alignment: invariant::Alignment;
    type Validity: invariant::Validity;

    /// Converts `s` into a raw pointer to `s`'s referent.
    ///
    /// # Safety
    ///
    /// It is guaranteed to be sound to call `Ptr::new(IntoPtr::into_raw(...))`,
    /// producing a `Ptr<'a, T, (Self::Aliasing, Self::Alignment,
    /// Self::Validity)>`. In particular, all of the safety preconditions of
    /// `Ptr::new` are satisfied. Given `ptr = IntoPtr::into_raw(...)`:
    /// 0. `ptr` is derived from some valid Rust allocation, `A`.
    /// 1. `ptr` has valid provenance for `A`.
    /// 2. `ptr` addresses a byte range which is entirely contained in `A`.
    /// 3. `ptr` addresses a byte range whose length fits in an `isize`.
    /// 4. `ptr` addresses a byte range which does not wrap around the address
    ///    space.
    /// 5. `A` is guaranteed to live for at least `'a`.
    /// 6. `ptr` conforms to the aliasing invariant of `Self::Aliasing`.
    /// 7. `ptr` conforms to the alignment invariant of `Self::Alignment`.
    /// 8. `ptr` conforms to the validity invariant of `Self::Validity`.
    /// 9. During the lifetime 'a, no code will load or store this memory region
    ///    treating `UnsafeCell`s as existing at different ranges than they
    ///    exist in `T`.
    /// 10. During the lifetime 'a, no reference will exist to this memory which
    ///     treats `UnsafeCell`s as existing at different ranges than they exist
    ///     in `T`.
    fn into_raw(s: Self) -> NonNull<T>;

    fn into_ptr(ptr: Self) -> Ptr<'a, T, (Self::Aliasing, Self::Alignment, Self::Validity)>
    where
        Self: Sized,
    {
        let ptr = Self::into_raw(ptr);
        // SAFETY: `Self::into_raw` promises to uphold the safety preconditions
        // of `Ptr::new`.
        unsafe { Ptr::new(ptr) }
    }
}

pub(crate) trait FromPtr<'a, T: ?Sized, I: invariant::Invariants> {
    fn from_ptr(ptr: Ptr<'a, T, I>) -> Self;
}

unsafe impl<'a, T: ?Sized> IntoPtr<'a, T> for &'a T {
    type Aliasing = invariant::Shared;
    type Alignment = invariant::Aligned;
    type Validity = invariant::Valid;

    fn into_raw(ptr: Self) -> NonNull<T> {
        NonNull::from(ptr)
    }
}

unsafe impl<'a, T: ?Sized> IntoPtr<'a, T> for &'a mut T {
    type Aliasing = invariant::Exclusive;
    type Alignment = invariant::Aligned;
    type Validity = invariant::Valid;

    fn into_raw(ptr: Self) -> NonNull<T> {
        NonNull::from(ptr)
    }
}

impl<'a, T: ?Sized, I> FromPtr<'a, T, I> for &'a T
where
    I: invariant::Invariants<Alignment = invariant::Aligned, Validity = invariant::Valid>,
    I::Aliasing: invariant::AtLeast<invariant::Shared>,
{
    fn from_ptr(ptr: Ptr<'a, T, I>) -> Self {
        ptr.as_ref()
    }
}

impl<'a, T: ?Sized, I> FromPtr<'a, T, I> for &'a mut T
where
    I: invariant::Invariants<
        Aliasing = invariant::Exclusive,
        Alignment = invariant::Aligned,
        Validity = invariant::Valid,
    >,
{
    fn from_ptr(ptr: Ptr<'a, T, I>) -> Self {
        ptr.as_mut()
    }
}
