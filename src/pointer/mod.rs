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

    /// A pointer cast or projection.
    ///
    /// # Safety
    ///
    /// `project` must be a provenance-preserving operation which preserves or
    /// shrinks the set of referent bytes.
    pub unsafe trait Project<Src: ?Sized, Dst: ?Sized> {
        /// Projects a pointer from `Src` to `Dst`.
        ///
        /// # Safety
        ///
        /// `src` must be a non-null pointer which has provenance for its entire
        /// referent. Its referent must be zero-sized or live in a single
        /// allocation.
        unsafe fn project(src: *mut Src) -> *mut Dst;
    }

    /// A [`Project`] which preserves the address of the referent – a pointer
    /// cast.
    ///
    /// # Safety
    ///
    /// A `Cast` projection must preserve the address of the referent. It may
    /// shrink the set of referent bytes, and it may change the referent's type.
    pub unsafe trait Cast<Src: ?Sized, Dst: ?Sized>: Project<Src, Dst> {}

    #[derive(Default, Copy, Clone)]
    #[allow(missing_debug_implementations)]
    pub struct IdCast;

    // SAFETY: TODO
    unsafe impl<T: ?Sized> Project<T, T> for IdCast {
        #[inline(always)]
        unsafe fn project(src: *mut T) -> *mut T {
            src
        }
    }

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<T: ?Sized> Cast<T, T> for IdCast {}

    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub enum CastSized {}

    // SAFETY: By the `static_assert!`, `Dst` is no larger than `Src`,
    // and `<*mut Src>::project` is a provenance-preserving cast.
    unsafe impl<Src, Dst> Project<Src, Dst> for CastSized {
        #[inline(always)]
        unsafe fn project(src: *mut Src) -> *mut Dst {
            static_assert!(Src, Dst => mem::size_of::<Src>() >= mem::size_of::<Dst>());
            src.cast::<Dst>()
        }
    }

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<Src, Dst> Cast<Src, Dst> for CastSized {}

    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub enum CastUnsized {}

    // SAFETY: TODO
    unsafe impl<Src, Dst> Project<Src, Dst> for CastUnsized
    where
        Src: ?Sized + KnownLayout,
        Dst: ?Sized + KnownLayout<PointerMetadata = Src::PointerMetadata>,
    {
        #[inline(always)]
        unsafe fn project(src: *mut Src) -> *mut Dst {
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

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<Src, Dst> Cast<Src, Dst> for CastUnsized
    where
        Src: ?Sized + KnownLayout,
        Dst: ?Sized + KnownLayout<PointerMetadata = Src::PointerMetadata>,
    {
    }

    /// A field projection
    ///
    /// `Projection` is a [`Project`] which implements projection by delegating
    /// to an implementation of [`HasField::project`].
    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub struct Projection<F: ?Sized, const VARIANT_ID: i128, const FIELD_ID: i128> {
        _never: core::convert::Infallible,
        _phantom: PhantomData<F>,
    }

    // SAFETY: TODO
    unsafe impl<T: ?Sized, F, const VARIANT_ID: i128, const FIELD_ID: i128> Project<T, T::Type>
        for Projection<F, VARIANT_ID, FIELD_ID>
    where
        T: crate::HasField<F, VARIANT_ID, FIELD_ID>,
    {
        #[inline(always)]
        unsafe fn project(src: *mut T) -> *mut T::Type {
            // SAFETY: The caller promises that `src` is a non-null pointer
            // whose referent is zero bytes or live in a single allocation.
            unsafe { T::project(src) }
        }
    }

    /// A transitive sequence of projections.
    ///
    /// Given `TU: Project` and `UV: Project`, `TransitiveProject<_, TU, UV>` is
    /// a [`Project`] which projects by applying `TU` followed by `UV`.
    ///
    /// If `TU: Cast` and `UV: Cast`, then `TransitiveProject<_, TU, UV>: Cast`.
    #[allow(missing_debug_implementations)]
    pub struct TransitiveProject<U: ?Sized, TU, UV> {
        _never: core::convert::Infallible,
        _marker: PhantomData<(TU, UV, U)>,
    }

    // SAFETY: TODO
    unsafe impl<T, U, V, TU, UV> Project<T, V> for TransitiveProject<U, TU, UV>
    where
        T: ?Sized,
        U: ?Sized,
        V: ?Sized,
        TU: Project<T, U>,
        UV: Project<U, V>,
    {
        #[inline(always)]
        unsafe fn project(t: *mut T) -> *mut V {
            // SAFETY: TODO
            let u = unsafe { TU::project(t) };
            // SAFETY: TODO
            unsafe { UV::project(u) }
        }
    }

    // SAFETY: Since the `Project::project` impl delegates to `TU::project` and
    // `UV::project`, and since `TU` and `UV` are `Cast`, the `Project::project`
    // impl preserves the address of the referent.
    unsafe impl<T, U, V, TU, UV> Cast<T, V> for TransitiveProject<U, TU, UV>
    where
        T: ?Sized,
        U: ?Sized,
        V: ?Sized,
        TU: Cast<T, U>,
        UV: Cast<U, V>,
    {
    }

    /// A cast from `T` to `[u8]`.
    pub(crate) struct AsBytesCast;

    // SAFETY: TODO
    unsafe impl<T: ?Sized + KnownLayout> Project<T, [u8]> for AsBytesCast {
        #[inline(always)]
        unsafe fn project(src: *mut T) -> *mut [u8] {
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

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<T: ?Sized + KnownLayout> Cast<T, [u8]> for AsBytesCast {}
}
