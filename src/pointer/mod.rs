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
    Aliasing: invariant::at_least::Shared,
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
        self.bikeshed_recall_aligned().as_ref()
    }
}

/// Checks if the referent is zeroed.
pub(crate) fn is_zeroed<T, I>(ptr: Ptr<'_, T, I>) -> bool
where
    T: crate::NoCell,
    I: invariant::Invariants<Validity = invariant::Initialized>,
    I::Aliasing: invariant::at_least::Shared,
{
    ptr.as_bytes().as_ref().iter().all(|&byte| byte == 0)
}
