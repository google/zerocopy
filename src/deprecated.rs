// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deprecated items. These are kept separate so that they don't clutter up
//! other modules.

use super::*;

impl<B, T> Ref<B, [T]>
where
    B: ByteSlice,
    T: Immutable,
{
    #[deprecated(since = "0.8.0", note = "`Ref::new` now supports slices")]
    #[doc(hidden)]
    #[inline]
    pub fn new_slice(bytes: B) -> Option<Ref<B, [T]>> {
        Self::new(bytes)
    }
}

impl<B, T> Ref<B, [T]>
where
    B: ByteSlice,
    T: Unaligned + Immutable,
{
    #[deprecated(since = "0.8.0", note = "`Ref::new_unaligned` now supports slices")]
    #[doc(hidden)]
    #[inline(always)]
    pub fn new_slice_unaligned(bytes: B) -> Option<Ref<B, [T]>> {
        Ref::new_unaligned(bytes)
    }
}

impl<'a, B, T> Ref<B, [T]>
where
    B: 'a + IntoByteSlice<'a>,
    T: FromBytes + Immutable,
{
    #[deprecated(since = "0.8.0", note = "`Ref::into_ref` now supports slices")]
    #[doc(hidden)]
    #[inline(always)]
    pub fn into_slice(self) -> &'a [T] {
        self.into_ref()
    }
}

impl<'a, B, T> Ref<B, [T]>
where
    B: 'a + IntoByteSliceMut<'a>,
    T: FromBytes + IntoBytes + Immutable,
{
    #[deprecated(since = "0.8.0", note = "`Ref::into_mut` now supports slices")]
    #[doc(hidden)]
    #[inline(always)]
    pub fn into_mut_slice(self) -> &'a mut [T] {
        self.into_mut()
    }
}

impl<B, T> Ref<B, [T]>
where
    B: SplitByteSlice,
    T: Immutable,
{
    #[deprecated(since = "0.8.0", note = "replaced by `Ref::with_trailing_elements_from_prefix`")]
    #[must_use = "has no side effects"]
    #[doc(hidden)]
    #[inline]
    pub fn new_slice_from_prefix(bytes: B, count: usize) -> Option<(Ref<B, [T]>, B)> {
        Ref::with_trailing_elements_from_prefix(bytes, count)
    }

    #[deprecated(since = "0.8.0", note = "replaced by `Ref::with_trailing_elements_from_suffix`")]
    #[must_use = "has no side effects"]
    #[doc(hidden)]
    #[inline]
    pub fn new_slice_from_suffix(bytes: B, count: usize) -> Option<(B, Ref<B, [T]>)> {
        Ref::with_trailing_elements_from_suffix(bytes, count)
    }
}

impl<B, T> Ref<B, [T]>
where
    B: SplitByteSlice,
    T: Unaligned + Immutable,
{
    #[deprecated(
        since = "0.8.0",
        note = "replaced by `Ref::with_trailing_elements_unaligned_from_prefix`"
    )]
    #[doc(hidden)]
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn new_slice_unaligned_from_prefix(bytes: B, count: usize) -> Option<(Ref<B, [T]>, B)> {
        Ref::with_trailing_elements_unaligned_from_prefix(bytes, count)
    }

    #[deprecated(
        since = "0.8.0",
        note = "replaced by `Ref::with_trailing_elements_unaligned_from_suffix`"
    )]
    #[doc(hidden)]
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn new_slice_unaligned_from_suffix(bytes: B, count: usize) -> Option<(B, Ref<B, [T]>)> {
        Ref::with_trailing_elements_unaligned_from_suffix(bytes, count)
    }
}
