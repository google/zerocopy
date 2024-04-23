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
    T: NoCell,
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
    T: Unaligned + NoCell,
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
    T: FromBytes + NoCell,
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
    T: FromBytes + IntoBytes + NoCell,
{
    #[deprecated(since = "0.8.0", note = "`Ref::into_mut` now supports slices")]
    #[doc(hidden)]
    #[inline(always)]
    pub fn into_mut_slice(self) -> &'a mut [T] {
        self.into_mut()
    }
}
