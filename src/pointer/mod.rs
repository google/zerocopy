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
    use core::{marker::PhantomData, mem};

    use crate::{
        layout::{SizeInfo, TrailingSliceLayout},
        HasField, KnownLayout, PtrInner,
    };

    /// A pointer cast or projection.
    ///
    /// # Safety
    ///
    /// The implementation of `project` must satisfy its safety post-condition.
    pub unsafe trait Project<Src: ?Sized, Dst: ?Sized> {
        /// Projects a pointer from `Src` to `Dst`.
        ///
        /// # Safety
        ///
        /// The returned pointer refers to a non-strict subset of the bytes of
        /// `src`'s referent, and has the same provenance as `src`.
        fn project(src: PtrInner<'_, Src>) -> *mut Dst;
    }

    /// A [`Project`] which preserves the address of the referent – a pointer
    /// cast.
    ///
    /// # Safety
    ///
    /// A `Cast` projection must preserve the address of the referent. It may
    /// shrink the set of referent bytes, and it may change the referent's type.
    pub unsafe trait Cast<Src: ?Sized, Dst: ?Sized>: Project<Src, Dst> {}

    /// A no-op pointer cast.
    #[derive(Default, Copy, Clone)]
    #[allow(missing_debug_implementations)]
    pub struct IdCast;

    // SAFETY: `project` returns its argument unchanged, and so it is a
    // provenance-preserving projection which preserves the set of referent
    // bytes.
    unsafe impl<T: ?Sized> Project<T, T> for IdCast {
        #[inline(always)]
        fn project(src: PtrInner<'_, T>) -> *mut T {
            src.as_ptr()
        }
    }

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<T: ?Sized> Cast<T, T> for IdCast {}

    /// A pointer cast which preserves or shrinks the set of referent bytes of
    /// a statically-sized referent.
    ///
    /// # Safety
    ///
    /// The implementation of [`Project`] uses a compile-time assertion to
    /// guarantee that `Dst` is no larger than `Src`. Thus, `CastSized` has a
    /// sound implementation of [`Project`] for all `Src` and `Dst` – the caller
    /// may pass any `Src` and `Dst` without being responsible for soundness.
    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub enum CastSized {}

    // SAFETY: By the `static_assert!`, `Dst` is no larger than `Src`,
    // and so all casts preserve or shrink the set of referent bytes. All
    // operations preserve provenance.
    unsafe impl<Src, Dst> Project<Src, Dst> for CastSized {
        #[inline(always)]
        fn project(src: PtrInner<'_, Src>) -> *mut Dst {
            static_assert!(Src, Dst => mem::size_of::<Src>() >= mem::size_of::<Dst>());
            src.as_ptr().cast::<Dst>()
        }
    }

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<Src, Dst> Cast<Src, Dst> for CastSized {}

    /// A pointer cast which preserves or shrinks the set of referent bytes of
    /// a dynamically-sized referent.
    ///
    /// # Safety
    ///
    /// The implementation of [`Project`] uses a compile-time assertion to
    /// guarantee that the cast preserves the set of referent bytes. Thus,
    /// `CastUnsized` has a sound implementation of [`Project`] for all `Src`
    /// and `Dst` – the caller may pass any `Src` and `Dst` without being
    /// responsible for soundness.
    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub enum CastUnsized {}

    // SAFETY: The `static_assert!` ensures that `Src` and `Dst` have the same
    // `SizeInfo`. Thus, casting preserves the set of referent bytes. All
    // operations are provenance-preserving.
    unsafe impl<Src, Dst> Project<Src, Dst> for CastUnsized
    where
        Src: ?Sized + KnownLayout,
        Dst: ?Sized + KnownLayout<PointerMetadata = Src::PointerMetadata>,
    {
        #[inline(always)]
        fn project(src: PtrInner<'_, Src>) -> *mut Dst {
            // FIXME:
            // - Is the alignment check necessary for soundness? It's not
            //   necessary for the soundness of the `Project` impl, but what
            //   about the soundness of particular use sites?
            // - Do we want this to support shrinking casts as well?
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

            let metadata = Src::pointer_to_metadata(src.as_ptr());
            Dst::raw_from_ptr_len(src.as_non_null().cast::<u8>(), metadata).as_ptr()
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
    /// A `Projection` is a [`Project`] which implements projection by
    /// delegating to an implementation of [`HasField::project`].
    #[allow(missing_debug_implementations, missing_copy_implementations)]
    pub struct Projection<F: ?Sized, const VARIANT_ID: i128, const FIELD_ID: i128> {
        _never: core::convert::Infallible,
        _phantom: PhantomData<F>,
    }

    // SAFETY: `HasField::project` has the same safety post-conditions as
    // `Project::project`.
    unsafe impl<T: ?Sized, F, const VARIANT_ID: i128, const FIELD_ID: i128> Project<T, T::Type>
        for Projection<F, VARIANT_ID, FIELD_ID>
    where
        T: HasField<F, VARIANT_ID, FIELD_ID>,
    {
        #[inline(always)]
        fn project(src: PtrInner<'_, T>) -> *mut T::Type {
            T::project(src)
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
        _projections: PhantomData<(TU, UV)>,
        // On our MSRV (1.56), the debuginfo for a tuple containing both an
        // uninhabited type and a DST causes an ICE. We split `U` from `TU` and
        // `UV` to avoid this situation.
        _u: PhantomData<U>,
    }

    // SAFETY: Since `TU::project` and `UV::project` are each
    // provenance-preserving operations which preserve or shrink the set of
    // referent bytes, so is their composition.
    unsafe impl<T, U, V, TU, UV> Project<T, V> for TransitiveProject<U, TU, UV>
    where
        T: ?Sized,
        U: ?Sized,
        V: ?Sized,
        TU: Project<T, U>,
        UV: Project<U, V>,
    {
        #[inline(always)]
        fn project(t: PtrInner<'_, T>) -> *mut V {
            t.project::<_, TU>().project::<_, UV>().as_ptr()
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

    // SAFETY: `project` constructs a pointer with the same address as `src`
    // and with a referent of the same size as `*src`. It does this using
    // provenance-preserving operations.
    //
    // FIXME(https://github.com/rust-lang/unsafe-code-guidelines/issues/594):
    // Technically, this proof assumes that `*src` is contiguous (the same is
    // true of other proofs in this codebase). Is this guaranteed anywhere?
    unsafe impl<T: ?Sized + KnownLayout> Project<T, [u8]> for AsBytesCast {
        #[inline(always)]
        fn project(src: PtrInner<'_, T>) -> *mut [u8] {
            let bytes = match T::size_of_val_raw(src.as_non_null()) {
                Some(bytes) => bytes,
                // SAFETY: `KnownLayout::size_of_val_raw` promises to always
                // return `Some` so long as the resulting size fits in a
                // `usize`. By invariant on `PtrInner`, `src` refers to a range
                // of bytes whose size fits in an `isize`, which implies that it
                // also fits in a `usize`.
                None => unsafe { core::hint::unreachable_unchecked() },
            };

            core::ptr::slice_from_raw_parts_mut(src.as_ptr().cast::<u8>(), bytes)
        }
    }

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<T: ?Sized + KnownLayout> Cast<T, [u8]> for AsBytesCast {}
}
