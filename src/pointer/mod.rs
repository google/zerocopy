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

#[cfg(zerocopy_gat)]
use core::ptr::NonNull;

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, sync::Arc};

pub use aliasing_safety::{AliasingSafe, AliasingSafeReason, BecauseExclusive, BecauseImmutable};
pub use ptr::{invariant, Ptr};

use crate::Unaligned;

/// A shorthand for a maybe-valid, maybe-aligned reference. Used as the argument
/// to [`TryFromBytes::is_bit_valid`].
///
/// [`TryFromBytes::is_bit_valid`]: crate::TryFromBytes::is_bit_valid
pub type Maybe<
    'a,
    T,
    Aliasing = invariant::Shared,
    Alignment = invariant::Any,
    Source = invariant::Any,
> = Ptr<'a, T, (Aliasing, Alignment, invariant::Initialized, Source)>;

/// A semi-user-facing wrapper type representing a maybe-aligned reference, for
/// use in [`TryFromBytes::is_bit_valid`].
///
/// [`TryFromBytes::is_bit_valid`]: crate::TryFromBytes::is_bit_valid
pub type MaybeAligned<
    'a,
    T,
    Aliasing = invariant::Shared,
    Alignment = invariant::Any,
    Source = invariant::Any,
> = Ptr<'a, T, (Aliasing, Alignment, invariant::Valid, Source)>;

// These methods are defined on the type alias, `MaybeAligned`, so as to bring
// them to the forefront of the rendered rustdoc for that type alias.
impl<'a, T, Aliasing, Alignment, Source> MaybeAligned<'a, T, Aliasing, Alignment, Source>
where
    T: 'a + ?Sized,
    Aliasing: invariant::Aliasing + invariant::AtLeast<invariant::Shared>,
    Alignment: invariant::Alignment,
    Source: invariant::Source,
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

/// TODO
///
/// # Safety
///
/// TODO
///
/// TODO: All methods' safety post-conditions must be upheld.
#[cfg(zerocopy_gat)]
pub(crate) unsafe trait Pointer<'a, T: ?Sized> {
    /// TODO
    type Pointer<U: 'a + ?Sized>: Pointer<'a, U, Aliasing = Self::Aliasing>;

    /// TODO
    type Aliasing: invariant::Aliasing;

    /// TODO
    type Source: invariant::Source;

    /// TODO
    ///
    /// # Safety
    ///
    /// It is guaranteed to be sound to call `Ptr::new(Pointer::into_raw(...))`,
    /// producing a `Ptr<'a, T, (Self::Aliasing, invariant::Aligned,
    /// invariant::Valid)>`. In particular, all of the safety preconditions of
    /// `Ptr::new` are satisfied. Given `ptr = Pointer::into_raw(...)`:
    /// 0. `ptr` is derived from some valid Rust allocation, `A`.
    /// 1. `ptr` has valid provenance for `A`.
    /// 2. `ptr` addresses a byte range which is entirely contained in `A`.
    /// 3. `ptr` addresses a byte range whose length fits in an `isize`.
    /// 4. `ptr` addresses a byte range which does not wrap around the address
    ///    space.
    /// 5. `A` is guaranteed to live for at least `'a`.
    /// 6. `ptr` conforms to the aliasing invariant of `Self::Aliasing`.
    /// 7. `ptr` is validly-aligned for `T`.
    /// 8. `ptr`'s referent is a bit-valid `T`.
    /// 9. During the lifetime 'a, no code will load or store this memory region
    ///    treating `UnsafeCell`s as existing at different ranges than they
    ///    exist in `T`.
    /// 10. During the lifetime 'a, no reference will exist to this memory which
    ///     treats `UnsafeCell`s as existing at different ranges than they exist
    ///     in `T`.
    fn into_raw(s: Self) -> NonNull<T>;

    fn into_ptr(
        ptr: Self,
    ) -> Ptr<'a, T, (Self::Aliasing, invariant::Aligned, invariant::Valid, Self::Source)>
    where
        Self: Sized,
    {
        let ptr = Self::into_raw(ptr);
        // SAFETY: `Self::into_raw` promises to uphold the safety preconditions
        // of `Ptr::new`.
        unsafe { Ptr::new(ptr) }
    }
}

unsafe trait FromPtr<'a, T, I: invariant::Invariants> {
    fn from_ptr(ptr: Ptr<'a, T, I>) -> Self;
}

#[cfg(zerocopy_gat)]
unsafe impl<'a, T: ?Sized> Pointer<'a, T> for &'a T {
    type Pointer<U: 'a + ?Sized> = &'a U;
    type Aliasing = invariant::Shared;
    type Source = invariant::Ref;

    fn into_raw(ptr: Self) -> NonNull<T> {
        NonNull::from(ptr)
    }
}

unsafe impl<'a, T, I> FromPtr<'a, T, I> for &'a T
where
    I: invariant::Invariants<Alignment = invariant::Aligned, Validity = invariant::Valid>,
    I::Aliasing: invariant::AtLeast<invariant::Shared>,
{
    fn from_ptr(ptr: Ptr<'a, T, I>) -> Self {
        ptr.as_ref()
    }
}

#[cfg(zerocopy_gat)]
unsafe impl<'a, T: ?Sized> Pointer<'a, T> for &'a mut T {
    type Pointer<U: 'a + ?Sized> = &'a mut U;
    type Aliasing = invariant::Exclusive;
    type Source = invariant::Mut;

    fn into_raw(ptr: Self) -> NonNull<T> {
        NonNull::from(ptr)
    }
}

unsafe impl<'a, T, I> FromPtr<'a, T, I> for &'a mut T
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

#[cfg(all(zerocopy_gat, feature = "alloc"))]
unsafe impl<'a, T: 'a + ?Sized> Pointer<'a, T> for Box<T> {
    type Pointer<U: 'a + ?Sized> = Box<U>;
    type Aliasing = invariant::Exclusive;
    type Source = invariant::Box;

    fn into_raw(b: Self) -> NonNull<T> {
        let ptr = Box::into_raw(b);

        unsafe { NonNull::new_unchecked(ptr) }
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'a, T, I> FromPtr<'a, T, I> for Box<T>
where
    I: invariant::Invariants<
        Aliasing = invariant::Exclusive,
        Alignment = invariant::Aligned,
        Validity = invariant::Valid,
        Source = invariant::Box,
    >,
{
    fn from_ptr(ptr: Ptr<'a, T, I>) -> Self {
        // SAFETY: TODO: Something about how `Source = Box` guarantees that this
        // came from `Box::into_raw`. However, there are some question marks:
        // - https://doc.rust-lang.org/std/boxed/index.html#considerations-for-unsafe-code
        // - https://github.com/rust-lang/unsafe-code-guidelines/issues/326
        unsafe { Box::from_raw(ptr.as_non_null().as_ptr()) }
    }
}

#[cfg(all(zerocopy_gat, feature = "alloc"))]
unsafe impl<'a, T: 'a + ?Sized> Pointer<'a, T> for Arc<T> {
    type Pointer<U: 'a + ?Sized> = Arc<U>;
    type Aliasing = invariant::Shared;
    type Source = invariant::Arc;

    fn into_raw(b: Self) -> NonNull<T> {
        let ptr = Arc::into_raw(b);

        unsafe { NonNull::new_unchecked(ptr.cast_mut()) }
    }
}

#[cfg(feature = "alloc")]
unsafe impl<'a, T, I> FromPtr<'a, T, I> for Arc<T>
where
    I: invariant::Invariants<
        Aliasing = invariant::Shared,
        Alignment = invariant::Aligned,
        Validity = invariant::Valid,
        Source = invariant::Arc,
    >,
{
    fn from_ptr(ptr: Ptr<'a, T, I>) -> Self {
        // SAFETY: TODO: Something about how `Source = Arc` guarantees that this
        // came from `Arc::into_raw`.
        unsafe { Arc::from_raw(ptr.as_non_null().as_ptr()) }
    }
}
