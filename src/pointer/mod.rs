// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Abstractions over raw pointers.

mod inner;
#[doc(hidden)]
pub mod invariant;
mod ptr;
mod transmute;

#[doc(hidden)]
pub use {inner::PtrInner, transmute::*};
#[doc(hidden)]
pub use {
    invariant::{BecauseExclusive, BecauseImmutable, Read},
    ptr::Ptr,
};

/// A shorthand for a maybe-valid, maybe-aligned reference. Used as the argument
/// to [`TryFromBytes::is_bit_valid`].
///
/// [`TryFromBytes::is_bit_valid`]: crate::TryFromBytes::is_bit_valid
pub type Maybe<'a, T, Aliasing = invariant::Shared, Alignment = invariant::Unaligned> =
    Ptr<'a, T, (Aliasing, Alignment, invariant::Initialized)>;

/// Checks if the referent is zeroed.
pub(crate) fn is_zeroed<T, I>(ptr: Ptr<'_, T, I>) -> bool
where
    T: crate::Immutable + crate::KnownLayout,
    I: invariant::Invariants<Validity = invariant::Initialized>,
    I::Aliasing: invariant::Reference,
{
    ptr.as_bytes::<BecauseImmutable>().as_ref().iter().all(|&byte| byte == 0)
}

#[doc(hidden)]
pub mod cast {
    use core::{marker::PhantomData, mem, ptr::NonNull};

    use crate::{
        layout::{SizeInfo, TrailingSliceLayout},
        KnownLayout,
    };

    /// # Safety
    ///
    /// `cast` must be a provenance-preserving cast which preserves or shrinks the
    /// set of referent bytes.
    pub unsafe trait Cast<Src: ?Sized, Dst: ?Sized> {
        /// # Safety
        ///
        /// `src` must be a non-null pointer which has provenance for its entire
        /// referent. Its referent must be zero-sized or live in a single
        /// allocation.
        unsafe fn cast(src: *mut Src) -> *mut Dst;
    }

    #[derive(Default, Copy, Clone)]
    #[allow(missing_debug_implementations)]
    pub struct IdCast;

    // SAFETY: TODO
    unsafe impl<T: ?Sized> Cast<T, T> for IdCast {
        #[inline(always)]
        unsafe fn cast(src: *mut T) -> *mut T {
            src
        }
    }

    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub enum CastSized {}

    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub enum CastUnsized {}

    // SAFETY: TODO
    unsafe impl<Src, Dst> Cast<Src, Dst> for CastUnsized
    where
        Src: ?Sized + KnownLayout,
        Dst: ?Sized + KnownLayout<PointerMetadata = Src::PointerMetadata>,
    {
        #[inline(always)]
        unsafe fn cast(src: *mut Src) -> *mut Dst {
            static_assert!(Src: ?Sized + KnownLayout, Dst: ?Sized + KnownLayout => {
                let t = <Src as KnownLayout>::LAYOUT;
                let u = <Dst as KnownLayout>::LAYOUT;
                t.align.get() >= u.align.get() && match (t.size_info, u.size_info) {
                    (SizeInfo::Sized { size: t }, SizeInfo::Sized { size: u }) => t == u,
                    (
                        SizeInfo::SliceDst(TrailingSliceLayout { offset: t_offset, elem_size: t_elem_size }),
                        SizeInfo::SliceDst(TrailingSliceLayout { offset: u_offset, elem_size: u_elem_size })
                    ) => t_offset == u_offset && t_elem_size == u_elem_size,
                    _ => false,
                }
            });

            let metadata = Src::pointer_to_metadata(src);
            // SAFETY: The caller promises that `src` is non-null.
            let src = unsafe { NonNull::new_unchecked(src) };
            Dst::raw_from_ptr_len(src.cast::<u8>(), metadata).as_ptr()
        }
    }

    // SAFETY: By the `static_assert!`, `Dst` is no larger than `Src`,
    // and `<*mut Src>::cast` is a provenance-preserving cast.
    unsafe impl<Src, Dst> Cast<Src, Dst> for CastSized {
        #[inline(always)]
        unsafe fn cast(src: *mut Src) -> *mut Dst {
            static_assert!(Src, Dst => mem::size_of::<Src>() >= mem::size_of::<Dst>());
            src.cast::<Dst>()
        }
    }

    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub struct ProjectCast<const VARIANT_ID: u128, const FIELD_ID: u128, F: ?Sized> {
        _never: core::convert::Infallible,
        _phantom: PhantomData<F>,
    }

    // SAFETY: TODO
    unsafe impl<const VARIANT_ID: u128, const FIELD_ID: u128, T: ?Sized, F> Cast<T, T::Type>
        for ProjectCast<VARIANT_ID, FIELD_ID, F>
    where
        T: crate::HasField<F, VARIANT_ID, FIELD_ID>,
    {
        #[inline(always)]
        unsafe fn cast(src: *mut T) -> *mut T::Type {
            // SAFETY: The caller promises that `src` is a non-null pointer
            // whose referent is zero bytes or live in a single allocation.
            unsafe { T::project(src) }
        }
    }

    #[allow(missing_debug_implementations)]
    pub struct TransitiveCast<U: ?Sized, TU, UV> {
        _never: core::convert::Infallible,
        _marker: PhantomData<(TU, UV, U)>,
    }

    // SAFETY: TODO
    unsafe impl<T, U, V, TU, UV> Cast<T, V> for TransitiveCast<U, TU, UV>
    where
        T: ?Sized,
        U: ?Sized,
        V: ?Sized,
        TU: Cast<T, U>,
        UV: Cast<U, V>,
    {
        #[inline(always)]
        unsafe fn cast(t: *mut T) -> *mut V {
            // SAFETY: TODO
            let u = unsafe { TU::cast(t) };
            // SAFETY: TODO
            unsafe { UV::cast(u) }
        }
    }

    pub(crate) struct AsBytesCast;

    // SAFETY: TODO
    unsafe impl<T: ?Sized + KnownLayout> Cast<T, [u8]> for AsBytesCast {
        #[inline(always)]
        unsafe fn cast(src: *mut T) -> *mut [u8] {
            // SAFETY: The caller promises that `src` is non-null.
            let src = unsafe { NonNull::new_unchecked(src) };
            let bytes = match T::size_of_val_raw(src) {
                Some(bytes) => bytes,
                // SAFETY: `KnownLayout::size_of_val_raw` promises to always
                // return `Some` so long as the resulting size fits in a
                // `usize`. By invariant on `PtrInner`, `self` refers to a range
                // of bytes whose size fits in an `isize`, which implies that it
                // also fits in a `usize`.
                None => unsafe { core::hint::unreachable_unchecked() },
            };

            core::ptr::slice_from_raw_parts_mut(src.cast::<u8>().as_ptr(), bytes)
        }
    }
}
