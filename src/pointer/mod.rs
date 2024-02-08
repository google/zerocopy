// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Abstractions over raw pointers.

mod ptr;

pub use ptr::{invariant, Ptr};

use crate::{TryFromBytes, Unaligned};

/// A shorthand for a maybe-valid, maybe-aligned reference. Used as the argument
/// to [`TryFromBytes::is_bit_valid`].
pub type Maybe<'a, T, Alignment = invariant::AnyAlignment> =
    Ptr<'a, T, (invariant::Shared, Alignment, invariant::Initialized)>;

// These methods are defined on the type alias, `Maybe`, so as to bring them to
// the forefront of the rendered rustdoc.
impl<'a, T, Alignment> Maybe<'a, T, Alignment>
where
    T: 'a + ?Sized + TryFromBytes,
    Alignment: invariant::Alignment,
{
    /// Checks that `Ptr`'s referent is validly initialized for `T`.
    ///
    /// # Panics
    ///
    /// This method will panic if
    /// [`T::is_bit_valid`][TryFromBytes::is_bit_valid] panics.
    #[inline]
    pub(crate) fn check_valid(self) -> Option<MaybeAligned<'a, T, Alignment>> {
        // This call may panic. If that happens, it doesn't cause any soundness
        // issues, as we have not generated any invalid state which we need to
        // fix before returning.
        if T::is_bit_valid(self.forget_aligned()) {
            // SAFETY: If `T::is_bit_valid`, code may assume that `self`
            // contains a bit-valid instance of `Self`.
            Some(unsafe { self.assume_validity::<invariant::Valid>() })
        } else {
            None
        }
    }
}

/// A semi-user-facing wrapper type representing a maybe-aligned reference, for
/// use in [`TryFromBytes::is_bit_valid`].
pub type MaybeAligned<'a, T, Alignment = invariant::AnyAlignment> =
    Ptr<'a, T, (invariant::Shared, Alignment, invariant::Valid)>;

// These methods are defined on the type alias, `MaybeAligned`, so as to bring
// them to the forefront of the rendered rustdoc for that type alias.
impl<'a, T, Alignment> MaybeAligned<'a, T, Alignment>
where
    T: 'a + ?Sized,
    Alignment: invariant::Alignment,
{
    /// Reads the value from `MaybeAligned`.
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
    #[inline]
    pub fn unaligned_as_ref(self) -> &'a T
    where
        T: Unaligned,
    {
        // SAFETY: The alignment of `T` is 1 and thus is always aligned
        // because `T: Unaligned`.
        let ptr = unsafe { self.assume_alignment::<invariant::Aligned>() };
        ptr.as_ref()
    }
}
