// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.
use super::*;
use crate::pointer::{
    BecauseInvariantsEq, BecauseMutationCompatible, MutationCompatible, TransmuteFromPtr,
};

mod def {
    use core::marker::PhantomData;

    use crate::{
        ByteSlice, ByteSliceMut, CloneableByteSlice, CopyableByteSlice, IntoByteSlice,
        IntoByteSliceMut,
    };

    /// A typed reference derived from a byte slice.
    ///
    /// A `Ref<B, T>` is a reference to a `T` which is stored in a byte slice, `B`.
    /// Unlike a native reference (`&T` or `&mut T`), `Ref<B, T>` has the same
    /// mutability as the byte slice it was constructed from (`B`).
    ///
    /// # Examples
    ///
    /// `Ref` can be used to treat a sequence of bytes as a structured type, and
    /// to read and write the fields of that type as if the byte slice reference
    /// were simply a reference to that type.
    ///
    /// ```rust
    /// use zerocopy::*;
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(FromBytes, IntoBytes, KnownLayout, Immutable, Unaligned)]
    /// #[repr(C)]
    /// struct UdpHeader {
    ///     src_port: [u8; 2],
    ///     dst_port: [u8; 2],
    ///     length: [u8; 2],
    ///     checksum: [u8; 2],
    /// }
    ///
    /// #[derive(FromBytes, IntoBytes, KnownLayout, Immutable, Unaligned)]
    /// #[repr(C, packed)]
    /// struct UdpPacket {
    ///     header: UdpHeader,
    ///     body: [u8],
    /// }
    ///
    /// impl UdpPacket {
    ///     pub fn parse<B: ByteSlice>(bytes: B) -> Option<Ref<B, UdpPacket>> {
    ///         Ref::from_bytes(bytes).ok()
    ///     }
    /// }
    /// ```
    pub struct Ref<B, T: ?Sized>(
        // INVARIANTS: The referent (via `.deref`, `.deref_mut`, `.into`) byte
        // slice is aligned to `T`'s alignment and its size corresponds to a
        // valid size for `T`.
        B,
        PhantomData<T>,
    );

    impl<B, T: ?Sized> Ref<B, T> {
        /// Constructs a new `Ref`.
        ///
        /// # Safety
        ///
        /// `bytes` dereferences (via [`deref`], [`deref_mut`], and [`into`]) to
        /// a byte slice which is aligned to `T`'s alignment and whose size is a
        /// valid size for `T`.
        ///
        /// [`deref`]: core::ops::Deref::deref
        /// [`deref_mut`]: core::ops::DerefMut::deref_mut
        /// [`into`]: core::convert::Into::into
        pub(crate) unsafe fn new_unchecked(bytes: B) -> Ref<B, T> {
            // INVARIANTS: The caller has promised that `bytes`'s referent is
            // validly-aligned and has a valid size.
            Ref(bytes, PhantomData)
        }
    }

    impl<B: ByteSlice, T: ?Sized> Ref<B, T> {
        /// Access the byte slice as a [`ByteSlice`].
        ///
        /// # Safety
        ///
        /// The caller promises not to call methods on the returned
        /// [`ByteSlice`] other than `ByteSlice` methods (for example, via
        /// `Any::downcast_ref`).
        ///
        /// `as_byte_slice` promises to return a `ByteSlice` whose referent is
        /// validly-aligned for `T` and has a valid size for `T`.
        pub(crate) unsafe fn as_byte_slice(&self) -> &impl ByteSlice {
            // INVARIANTS: The caller promises not to call methods other than
            // those on `ByteSlice`. Since `B: ByteSlice`, dereference stability
            // guarantees that calling `ByteSlice` methods will not change the
            // address or length of `self.0`'s referent.
            //
            // SAFETY: By invariant on `self.0`, the alignment and size
            // post-conditions are upheld.
            &self.0
        }
    }

    impl<B: ByteSliceMut, T: ?Sized> Ref<B, T> {
        /// Access the byte slice as a [`ByteSliceMut`].
        ///
        /// # Safety
        ///
        /// The caller promises not to call methods on the returned
        /// [`ByteSliceMut`] other than `ByteSliceMut` methods (for example, via
        /// `Any::downcast_mut`).
        ///
        /// `as_byte_slice` promises to return a `ByteSlice` whose referent is
        /// validly-aligned for `T` and has a valid size for `T`.
        pub(crate) unsafe fn as_byte_slice_mut(&mut self) -> &mut impl ByteSliceMut {
            // INVARIANTS: The caller promises not to call methods other than
            // those on `ByteSliceMut`. Since `B: ByteSlice`, dereference
            // stability guarantees that calling `ByteSlice` methods will not
            // change the address or length of `self.0`'s referent.
            //
            // SAFETY: By invariant on `self.0`, the alignment and size
            // post-conditions are upheld.
            &mut self.0
        }
    }

    impl<'a, B: IntoByteSlice<'a>, T: ?Sized> Ref<B, T> {
        /// Access the byte slice as an [`IntoByteSlice`].
        ///
        /// # Safety
        ///
        /// The caller promises not to call methods on the returned
        /// [`IntoByteSlice`] other than `IntoByteSlice` methods (for example,
        /// via `Any::downcast_ref`).
        ///
        /// `as_byte_slice` promises to return a `ByteSlice` whose referent is
        /// validly-aligned for `T` and has a valid size for `T`.
        pub(crate) unsafe fn into_byte_slice(self) -> impl IntoByteSlice<'a> {
            // INVARIANTS: The caller promises not to call methods other than
            // those on `IntoByteSlice`. Since `B: ByteSlice`, dereference
            // stability guarantees that calling `ByteSlice` methods will not
            // change the address or length of `self.0`'s referent.
            //
            // SAFETY: By invariant on `self.0`, the alignment and size
            // post-conditions are upheld.
            self.0
        }
    }

    impl<'a, B: IntoByteSliceMut<'a>, T: ?Sized> Ref<B, T> {
        /// Access the byte slice as an [`IntoByteSliceMut`].
        ///
        /// # Safety
        ///
        /// The caller promises not to call methods on the returned
        /// [`IntoByteSliceMut`] other than `IntoByteSliceMut` methods (for
        /// example, via `Any::downcast_mut`).
        ///
        /// `as_byte_slice` promises to return a `ByteSlice` whose referent is
        /// validly-aligned for `T` and has a valid size for `T`.
        pub(crate) unsafe fn into_byte_slice_mut(self) -> impl IntoByteSliceMut<'a> {
            // INVARIANTS: The caller promises not to call methods other than
            // those on `IntoByteSliceMut`. Since `B: ByteSlice`, dereference
            // stability guarantees that calling `ByteSlice` methods will not
            // change the address or length of `self.0`'s referent.
            //
            // SAFETY: By invariant on `self.0`, the alignment and size
            // post-conditions are upheld.
            self.0
        }
    }

    impl<B: CloneableByteSlice + Clone, T: ?Sized> Clone for Ref<B, T> {
        #[inline]
        fn clone(&self) -> Ref<B, T> {
            // INVARIANTS: Since `B: CloneableByteSlice`, `self.0.clone()` has
            // the same address and length as `self.0`. Since `self.0` upholds
            // the field invariants, so does `self.0.clone()`.
            Ref(self.0.clone(), PhantomData)
        }
    }

    // INVARIANTS: Since `B: CopyableByteSlice`, the copied `Ref`'s `.0` has the
    // same address and length as the original `Ref`'s `.0`. Since the original
    // upholds the field invariants, so does the copy.
    impl<B: CopyableByteSlice + Copy, T: ?Sized> Copy for Ref<B, T> {}
}

#[allow(unreachable_pub)] // This is a false positive on our MSRV toolchain.
pub use def::Ref;

use crate::pointer::{
    invariant::{Aligned, BecauseExclusive, Initialized, Unaligned, Valid},
    BecauseRead, PtrInner,
};

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
{
    #[must_use = "has no side effects"]
    pub(crate) fn sized_from(bytes: B) -> Result<Ref<B, T>, CastError<B, T>> {
        if bytes.len() != mem::size_of::<T>() {
            return Err(SizeError::new(bytes).into());
        }
        if let Err(err) = util::validate_aligned_to::<_, T>(bytes.deref()) {
            return Err(err.with_src(bytes).into());
        }

        // SAFETY: We just validated size and alignment.
        Ok(unsafe { Ref::new_unchecked(bytes) })
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
{
    #[must_use = "has no side effects"]
    pub(crate) fn sized_from_prefix(bytes: B) -> Result<(Ref<B, T>, B), CastError<B, T>> {
        if bytes.len() < mem::size_of::<T>() {
            return Err(SizeError::new(bytes).into());
        }
        if let Err(err) = util::validate_aligned_to::<_, T>(bytes.deref()) {
            return Err(err.with_src(bytes).into());
        }
        let (bytes, suffix) = bytes.split_at(mem::size_of::<T>()).map_err(
            #[inline(always)]
            |b| SizeError::new(b).into(),
        )?;
        // SAFETY: We just validated alignment and that `bytes` is at least as
        // large as `T`. `bytes.split_at(mem::size_of::<T>())?` ensures that the
        // new `bytes` is exactly the size of `T`. By safety postcondition on
        // `SplitByteSlice::split_at` we can rely on `split_at` to produce the
        // correct `bytes` and `suffix`.
        let r = unsafe { Ref::new_unchecked(bytes) };
        Ok((r, suffix))
    }

    #[must_use = "has no side effects"]
    pub(crate) fn sized_from_suffix(bytes: B) -> Result<(B, Ref<B, T>), CastError<B, T>> {
        let bytes_len = bytes.len();
        let split_at = if let Some(split_at) = bytes_len.checked_sub(mem::size_of::<T>()) {
            split_at
        } else {
            return Err(SizeError::new(bytes).into());
        };
        let (prefix, bytes) = bytes.split_at(split_at).map_err(|b| SizeError::new(b).into())?;
        if let Err(err) = util::validate_aligned_to::<_, T>(bytes.deref()) {
            return Err(err.with_src(bytes).into());
        }
        // SAFETY: Since `split_at` is defined as `bytes_len - size_of::<T>()`,
        // the `bytes` which results from `let (prefix, bytes) =
        // bytes.split_at(split_at)?` has length `size_of::<T>()`. After
        // constructing `bytes`, we validate that it has the proper alignment.
        // By safety postcondition on `SplitByteSlice::split_at` we can rely on
        // `split_at` to produce the correct `prefix` and `bytes`.
        let r = unsafe { Ref::new_unchecked(bytes) };
        Ok((prefix, r))
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: KnownLayout + Immutable + ?Sized,
{
    /// Constructs a `Ref` from a byte slice.
    ///
    /// If the length of `source` is not a [valid size of `T`][valid-size], or
    /// if `source` is not appropriately aligned for `T`, this returns `Err`. If
    /// [`T: Unaligned`][t-unaligned], you can [infallibly discard the alignment
    /// error][size-error-from].
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate::KnownLayout#what-is-a-valid-size
    /// [t-unaligned]: crate::Unaligned
    /// [size-error-from]: error/struct.SizeError.html#method.from-1
    /// [slice-dst]: KnownLayout#dynamically-sized-types
    ///
    /// # Compile-Time Assertions
    ///
    /// This method cannot yet be used on unsized types whose dynamically-sized
    /// component is zero-sized. Attempting to use this method on such types
    /// results in a compile-time assertion error; e.g.:
    ///
    /// ```compile_fail,E0080
    /// use zerocopy::*;
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(Immutable, KnownLayout)]
    /// #[repr(C)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::from_bytes(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline]
    pub fn from_bytes(source: B) -> Result<Ref<B, T>, CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        if let Err(e) =
            Ptr::from_ref(source.deref()).try_cast_into_no_leftover::<T, BecauseImmutable>(None)
        {
            return Err(e.with_src(()).with_src(source));
        }
        // SAFETY: `try_cast_into_no_leftover` validates size and alignment.
        Ok(unsafe { Ref::new_unchecked(source) })
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: KnownLayout + Immutable + ?Sized,
{
    /// Constructs a `Ref` from the prefix of a byte slice.
    ///
    /// This method computes the [largest possible size of `T`][valid-size] that
    /// can fit in the leading bytes of `source`, then attempts to return both a
    /// `Ref` to those bytes, and a reference to the remaining bytes. If there
    /// are insufficient bytes, or if `source` is not appropriately aligned,
    /// this returns `Err`. If [`T: Unaligned`][t-unaligned], you can
    /// [infallibly discard the alignment error][size-error-from].
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate::KnownLayout#what-is-a-valid-size
    /// [t-unaligned]: crate::Unaligned
    /// [size-error-from]: error/struct.SizeError.html#method.from-1
    /// [slice-dst]: KnownLayout#dynamically-sized-types
    ///
    /// # Compile-Time Assertions
    ///
    /// This method cannot yet be used on unsized types whose dynamically-sized
    /// component is zero-sized. Attempting to use this method on such types
    /// results in a compile-time assertion error; e.g.:
    ///
    /// ```compile_fail,E0080
    /// use zerocopy::*;
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(Immutable, KnownLayout)]
    /// #[repr(C)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::from_prefix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline]
    pub fn from_prefix(source: B) -> Result<(Ref<B, T>, B), CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let remainder = match Ptr::from_ref(source.deref())
            .try_cast_into::<T, BecauseImmutable>(CastType::Prefix, None)
        {
            Ok((_, remainder)) => remainder,
            Err(e) => {
                return Err(e.with_src(()).with_src(source));
            }
        };

        // SAFETY: `remainder` is constructed as a subset of `source`, and so it
        // cannot have a larger size than `source`. Both of their `len` methods
        // measure bytes (`source` deref's to `[u8]`, and `remainder` is a
        // `Ptr<[u8]>`), so `source.len() >= remainder.len()`. Thus, this cannot
        // underflow.
        #[allow(unstable_name_collisions)]
        let split_at = unsafe { source.len().unchecked_sub(remainder.len()) };
        let (bytes, suffix) = source.split_at(split_at).map_err(|b| SizeError::new(b).into())?;
        // SAFETY: `try_cast_into` validates size and alignment, and returns a
        // `split_at` that indicates how many bytes of `source` correspond to a
        // valid `T`. By safety postcondition on `SplitByteSlice::split_at` we
        // can rely on `split_at` to produce the correct `source` and `suffix`.
        let r = unsafe { Ref::new_unchecked(bytes) };
        Ok((r, suffix))
    }

    /// Constructs a `Ref` from the suffix of a byte slice.
    ///
    /// This method computes the [largest possible size of `T`][valid-size] that
    /// can fit in the trailing bytes of `source`, then attempts to return both
    /// a `Ref` to those bytes, and a reference to the preceding bytes. If there
    /// are insufficient bytes, or if that suffix of `source` is not
    /// appropriately aligned, this returns `Err`. If [`T:
    /// Unaligned`][t-unaligned], you can [infallibly discard the alignment
    /// error][size-error-from].
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate::KnownLayout#what-is-a-valid-size
    /// [t-unaligned]: crate::Unaligned
    /// [size-error-from]: error/struct.SizeError.html#method.from-1
    /// [slice-dst]: KnownLayout#dynamically-sized-types
    ///
    /// # Compile-Time Assertions
    ///
    /// This method cannot yet be used on unsized types whose dynamically-sized
    /// component is zero-sized. Attempting to use this method on such types
    /// results in a compile-time assertion error; e.g.:
    ///
    /// ```compile_fail,E0080
    /// use zerocopy::*;
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(Immutable, KnownLayout)]
    /// #[repr(C)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::from_suffix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline]
    pub fn from_suffix(source: B) -> Result<(B, Ref<B, T>), CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let remainder = match Ptr::from_ref(source.deref())
            .try_cast_into::<T, BecauseImmutable>(CastType::Suffix, None)
        {
            Ok((_, remainder)) => remainder,
            Err(e) => {
                let e = e.with_src(());
                return Err(e.with_src(source));
            }
        };

        let split_at = remainder.len();
        let (prefix, bytes) = source.split_at(split_at).map_err(|b| SizeError::new(b).into())?;
        // SAFETY: `try_cast_into` validates size and alignment, and returns a
        // `split_at` that indicates how many bytes of `source` correspond to a
        // valid `T`. By safety postcondition on `SplitByteSlice::split_at` we
        // can rely on `split_at` to produce the correct `prefix` and `bytes`.
        let r = unsafe { Ref::new_unchecked(bytes) };
        Ok((prefix, r))
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: KnownLayout<PointerMetadata = usize> + Immutable + ?Sized,
{
    /// Constructs a `Ref` from the given bytes with DST length equal to `count`
    /// without copying.
    ///
    /// This method attempts to return a `Ref` to the prefix of `source`
    /// interpreted as a `T` with `count` trailing elements, and a reference to
    /// the remaining bytes. If the length of `source` is not equal to the size
    /// of `Self` with `count` elements, or if `source` is not appropriately
    /// aligned, this returns `Err`. If [`T: Unaligned`][t-unaligned], you can
    /// [infallibly discard the alignment error][size-error-from].
    ///
    /// [t-unaligned]: crate::Unaligned
    /// [size-error-from]: error/struct.SizeError.html#method.from-1
    ///
    /// # Compile-Time Assertions
    ///
    /// This method cannot yet be used on unsized types whose dynamically-sized
    /// component is zero-sized. Attempting to use this method on such types
    /// results in a compile-time assertion error; e.g.:
    ///
    /// ```compile_fail,E0080
    /// use zerocopy::*;
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(Immutable, KnownLayout)]
    /// #[repr(C)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::from_bytes_with_elems(&b"UU"[..], 42); // ⚠ Compile Error!
    /// ```
    #[inline]
    pub fn from_bytes_with_elems(source: B, count: usize) -> Result<Ref<B, T>, CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let expected_len = match T::size_for_metadata(count) {
            Some(len) => len,
            None => return Err(SizeError::new(source).into()),
        };
        if source.len() != expected_len {
            return Err(SizeError::new(source).into());
        }
        Self::from_bytes(source)
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: KnownLayout<PointerMetadata = usize> + Immutable + ?Sized,
{
    /// Constructs a `Ref` from the prefix of the given bytes with DST
    /// length equal to `count` without copying.
    ///
    /// This method attempts to return a `Ref` to the prefix of `source`
    /// interpreted as a `T` with `count` trailing elements, and a reference to
    /// the remaining bytes. If there are insufficient bytes, or if `source` is
    /// not appropriately aligned, this returns `Err`. If [`T:
    /// Unaligned`][t-unaligned], you can [infallibly discard the alignment
    /// error][size-error-from].
    ///
    /// [t-unaligned]: crate::Unaligned
    /// [size-error-from]: error/struct.SizeError.html#method.from-1
    ///
    /// # Compile-Time Assertions
    ///
    /// This method cannot yet be used on unsized types whose dynamically-sized
    /// component is zero-sized. Attempting to use this method on such types
    /// results in a compile-time assertion error; e.g.:
    ///
    /// ```compile_fail,E0080
    /// use zerocopy::*;
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(Immutable, KnownLayout)]
    /// #[repr(C)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::from_prefix_with_elems(&b"UU"[..], 42); // ⚠ Compile Error!
    /// ```
    #[inline]
    pub fn from_prefix_with_elems(
        source: B,
        count: usize,
    ) -> Result<(Ref<B, T>, B), CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let expected_len = match T::size_for_metadata(count) {
            Some(len) => len,
            None => return Err(SizeError::new(source).into()),
        };
        let (prefix, bytes) = source.split_at(expected_len).map_err(SizeError::new)?;
        Self::from_bytes(prefix).map(move |l| (l, bytes))
    }

    /// Constructs a `Ref` from the suffix of the given bytes with DST length
    /// equal to `count` without copying.
    ///
    /// This method attempts to return a `Ref` to the suffix of `source`
    /// interpreted as a `T` with `count` trailing elements, and a reference to
    /// the preceding bytes. If there are insufficient bytes, or if that suffix
    /// of `source` is not appropriately aligned, this returns `Err`. If [`T:
    /// Unaligned`][t-unaligned], you can [infallibly discard the alignment
    /// error][size-error-from].
    ///
    /// [t-unaligned]: crate::Unaligned
    /// [size-error-from]: error/struct.SizeError.html#method.from-1
    ///
    /// # Compile-Time Assertions
    ///
    /// This method cannot yet be used on unsized types whose dynamically-sized
    /// component is zero-sized. Attempting to use this method on such types
    /// results in a compile-time assertion error; e.g.:
    ///
    /// ```compile_fail,E0080
    /// use zerocopy::*;
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(Immutable, KnownLayout)]
    /// #[repr(C)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::from_suffix_with_elems(&b"UU"[..], 42); // ⚠ Compile Error!
    /// ```
    #[inline]
    pub fn from_suffix_with_elems(
        source: B,
        count: usize,
    ) -> Result<(B, Ref<B, T>), CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let expected_len = match T::size_for_metadata(count) {
            Some(len) => len,
            None => return Err(SizeError::new(source).into()),
        };
        let split_at = if let Some(split_at) = source.len().checked_sub(expected_len) {
            split_at
        } else {
            return Err(SizeError::new(source).into());
        };
        // SAFETY: The preceding `source.len().checked_sub(expected_len)`
        // guarantees that `split_at` is in-bounds.
        let (bytes, suffix) = unsafe { source.split_at_unchecked(split_at) };
        Self::from_bytes(suffix).map(move |l| (bytes, l))
    }
}

impl<'a, B, T> Ref<B, T>
where
    B: 'a + IntoByteSlice<'a>,
    T: FromBytes + KnownLayout + Immutable + ?Sized,
{
    /// Converts this `Ref` into a reference.
    ///
    /// `into_ref` consumes the `Ref`, and returns a reference to `T`.
    ///
    /// Note: this is an associated function, which means that you have to call
    /// it as `Ref::into_ref(r)` instead of `r.into_ref()`. This is so that
    /// there is no conflict with a method on the inner type.
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn into_ref(r: Self) -> &'a T {
        // Presumably unreachable, since we've guarded each constructor of `Ref`.
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `IntoByteSlice`.
        let b = unsafe { r.into_byte_slice() };
        let b = b.into_byte_slice();

        if let crate::layout::SizeInfo::Sized { .. } = T::LAYOUT.size_info {
            let ptr = Ptr::from_ref(b);
            // SAFETY: We just checked that `T: Sized`. By invariant on `r`,
            // `b`'s size is equal to `size_of::<T>()`.
            let ptr = unsafe { cast_for_sized::<T, _, _, _>(ptr) };

            // SAFETY: None of the preceding transformations modifies the
            // address of the pointer, and by invariant on `r`, we know that it
            // is validly-aligned.
            let ptr = unsafe { ptr.assume_alignment::<Aligned>() };
            return ptr.as_ref();
        }

        // PANICS: By post-condition on `into_byte_slice`, `b`'s size and
        // alignment are valid for `T`. By post-condition, `b.into_byte_slice()`
        // produces a byte slice with identical address and length to that
        // produced by `b.deref()`.
        let ptr = Ptr::from_ref(b.into_byte_slice())
            .try_cast_into_no_leftover::<T, BecauseImmutable>(None)
            .expect("zerocopy internal error: into_ref should be infallible");
        let ptr = ptr.recall_validity();
        ptr.as_ref()
    }
}

impl<'a, B, T> Ref<B, T>
where
    B: 'a + IntoByteSliceMut<'a>,
    T: FromBytes + IntoBytes + KnownLayout + ?Sized,
{
    /// Converts this `Ref` into a mutable reference.
    ///
    /// `into_mut` consumes the `Ref`, and returns a mutable reference to `T`.
    ///
    /// Note: this is an associated function, which means that you have to call
    /// it as `Ref::into_mut(r)` instead of `r.into_mut()`. This is so that
    /// there is no conflict with a method on the inner type.
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn into_mut(r: Self) -> &'a mut T {
        // Presumably unreachable, since we've guarded each constructor of `Ref`.
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `IntoByteSliceMut`.
        let b = unsafe { r.into_byte_slice_mut() };
        let b = b.into_byte_slice_mut();

        if let crate::layout::SizeInfo::Sized { .. } = T::LAYOUT.size_info {
            let ptr = Ptr::from_mut(b);
            // SAFETY: We just checked that `T: Sized`. By invariant on `r`,
            // `b`'s size is equal to `size_of::<T>()`.
            let ptr = unsafe {
                cast_for_sized::<
                    T,
                    _,
                    (BecauseRead, BecauseExclusive),
                    (BecauseMutationCompatible, BecauseInvariantsEq),
                >(ptr)
            };

            // SAFETY: None of the preceding transformations modifies the
            // address of the pointer, and by invariant on `r`, we know that it
            // is validly-aligned.
            let ptr = unsafe { ptr.assume_alignment::<Aligned>() };
            return ptr.as_mut();
        }

        // PANICS: By post-condition on `into_byte_slice_mut`, `b`'s size and
        // alignment are valid for `T`. By post-condition,
        // `b.into_byte_slice_mut()` produces a byte slice with identical
        // address and length to that produced by `b.deref_mut()`.
        let ptr = Ptr::from_mut(b.into_byte_slice_mut())
            .try_cast_into_no_leftover::<T, BecauseExclusive>(None)
            .expect("zerocopy internal error: into_ref should be infallible");
        let ptr = ptr.recall_validity::<_, (_, (_, _))>();
        ptr.as_mut()
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: ?Sized,
{
    /// Gets the underlying bytes.
    ///
    /// Note: this is an associated function, which means that you have to call
    /// it as `Ref::bytes(r)` instead of `r.bytes()`. This is so that there is
    /// no conflict with a method on the inner type.
    #[inline]
    pub fn bytes(r: &Self) -> &[u8] {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSlice`.
        unsafe { r.as_byte_slice().deref() }
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSliceMut,
    T: ?Sized,
{
    /// Gets the underlying bytes mutably.
    ///
    /// Note: this is an associated function, which means that you have to call
    /// it as `Ref::bytes_mut(r)` instead of `r.bytes_mut()`. This is so that
    /// there is no conflict with a method on the inner type.
    #[inline]
    pub fn bytes_mut(r: &mut Self) -> &mut [u8] {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSliceMut`.
        unsafe { r.as_byte_slice_mut().deref_mut() }
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes,
{
    /// Reads a copy of `T`.
    ///
    /// Note: this is an associated function, which means that you have to call
    /// it as `Ref::read(r)` instead of `r.read()`. This is so that there is no
    /// conflict with a method on the inner type.
    #[must_use = "has no side effects"]
    #[inline]
    pub fn read(r: &Self) -> T {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSlice`.
        let b = unsafe { r.as_byte_slice() };

        // SAFETY: By postcondition on `as_byte_slice`, we know that `b` is a
        // valid size and alignment for `T`. By safety invariant on `ByteSlice`,
        // we know that this is preserved via `.deref()`. Because `T:
        // FromBytes`, it is sound to interpret these bytes as a `T`.
        unsafe { ptr::read(b.deref().as_ptr().cast::<T>()) }
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSliceMut,
    T: IntoBytes,
{
    /// Writes the bytes of `t` and then forgets `t`.
    ///
    /// Note: this is an associated function, which means that you have to call
    /// it as `Ref::write(r, t)` instead of `r.write(t)`. This is so that there
    /// is no conflict with a method on the inner type.
    #[inline]
    pub fn write(r: &mut Self, t: T) {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSliceMut`.
        let b = unsafe { r.as_byte_slice_mut() };

        // SAFETY: By postcondition on `as_byte_slice_mut`, we know that `b` is
        // a valid size and alignment for `T`. By safety invariant on
        // `ByteSlice`, we know that this is preserved via `.deref()`. Writing
        // `t` to the buffer will allow all of the bytes of `t` to be accessed
        // as a `[u8]`, but because `T: IntoBytes`, we know that this is sound.
        unsafe { ptr::write(b.deref_mut().as_mut_ptr().cast::<T>(), t) }
    }
}

impl<B, T> Deref for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + KnownLayout + Immutable + ?Sized,
{
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        // Presumably unreachable, since we've guarded each constructor of `Ref`.
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSlice`.
        let b = unsafe { self.as_byte_slice() };
        let b = b.deref();

        if let crate::layout::SizeInfo::Sized { .. } = T::LAYOUT.size_info {
            let ptr = Ptr::from_ref(b);
            // SAFETY: We just checked that `T: Sized`. By invariant on `r`,
            // `b`'s size is equal to `size_of::<T>()`.
            let ptr = unsafe { cast_for_sized::<T, _, _, _>(ptr) };

            // SAFETY: None of the preceding transformations modifies the
            // address of the pointer, and by invariant on `r`, we know that it
            // is validly-aligned.
            let ptr = unsafe { ptr.assume_alignment::<Aligned>() };
            return ptr.as_ref();
        }

        // PANICS: By postcondition on `as_byte_slice`, `b`'s size and alignment
        // are valid for `T`, and by invariant on `ByteSlice`, these are
        // preserved through `.deref()`, so this `unwrap` will not panic.
        let ptr = Ptr::from_ref(b)
            .try_cast_into_no_leftover::<T, BecauseImmutable>(None)
            .expect("zerocopy internal error: Deref::deref should be infallible");
        let ptr = ptr.recall_validity();
        ptr.as_ref()
    }
}

impl<B, T> DerefMut for Ref<B, T>
where
    B: ByteSliceMut,
    // FIXME(#251): We can't remove `Immutable` here because it's required by
    // the impl of `Deref`, which is a super-trait of `DerefMut`. Maybe we can
    // add a separate inherent method for this?
    T: FromBytes + IntoBytes + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // Presumably unreachable, since we've guarded each constructor of `Ref`.
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSliceMut`.
        let b = unsafe { self.as_byte_slice_mut() };
        let b = b.deref_mut();

        if let crate::layout::SizeInfo::Sized { .. } = T::LAYOUT.size_info {
            let ptr = Ptr::from_mut(b);
            // SAFETY: We just checked that `T: Sized`. By invariant on `r`,
            // `b`'s size is equal to `size_of::<T>()`.
            let ptr = unsafe {
                cast_for_sized::<
                    T,
                    _,
                    (BecauseRead, BecauseExclusive),
                    (BecauseMutationCompatible, BecauseInvariantsEq),
                >(ptr)
            };

            // SAFETY: None of the preceding transformations modifies the
            // address of the pointer, and by invariant on `r`, we know that it
            // is validly-aligned.
            let ptr = unsafe { ptr.assume_alignment::<Aligned>() };
            return ptr.as_mut();
        }

        // PANICS: By postcondition on `as_byte_slice_mut`, `b`'s size and
        // alignment are valid for `T`, and by invariant on `ByteSlice`, these
        // are preserved through `.deref_mut()`, so this `unwrap` will not
        // panic.
        let ptr = Ptr::from_mut(b)
            .try_cast_into_no_leftover::<T, BecauseExclusive>(None)
            .expect("zerocopy internal error: DerefMut::deref_mut should be infallible");
        let ptr = ptr.recall_validity::<_, (_, (_, BecauseExclusive))>();
        ptr.as_mut()
    }
}

impl<T, B> Display for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + Display + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &T = self;
        inner.fmt(fmt)
    }
}

impl<T, B> Debug for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + Debug + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &T = self;
        fmt.debug_tuple("Ref").field(&inner).finish()
    }
}

impl<T, B> Eq for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + Eq + KnownLayout + Immutable + ?Sized,
{
}

impl<T, B> PartialEq for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + PartialEq + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.deref().eq(other.deref())
    }
}

impl<T, B> Ord for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + Ord + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let inner: &T = self;
        let other_inner: &T = other;
        inner.cmp(other_inner)
    }
}

impl<T, B> PartialOrd for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + PartialOrd + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let inner: &T = self;
        let other_inner: &T = other;
        inner.partial_cmp(other_inner)
    }
}

/// # Safety
///
/// `T: Sized` and `ptr`'s referent must have size `size_of::<T>()`.
#[inline(always)]
unsafe fn cast_for_sized<'a, T, A, R, S>(
    ptr: Ptr<'a, [u8], (A, Aligned, Valid)>,
) -> Ptr<'a, T, (A, Unaligned, Valid)>
where
    T: FromBytes + KnownLayout + ?Sized,
    A: crate::invariant::Aliasing,
    [u8]: MutationCompatible<T, A, Initialized, Initialized, R>,
    T: TransmuteFromPtr<T, A, Initialized, Valid, crate::pointer::cast::IdCast, S>,
{
    use crate::pointer::cast::{Cast, Project};

    enum CastForSized {}

    // SAFETY: `CastForSized` is only used below with the input `ptr`, which the
    // caller promises has size `size_of::<T>()`. Thus, the referent produced in
    // this cast has the same size as `ptr`'s referent. All operations preserve
    // provenance.
    unsafe impl<T: ?Sized + KnownLayout> Project<[u8], T> for CastForSized {
        #[inline(always)]
        fn project(src: PtrInner<'_, [u8]>) -> *mut T {
            T::raw_from_ptr_len(
                src.as_non_null().cast(),
                <T::PointerMetadata as crate::PointerMetadata>::from_elem_count(0),
            )
            .as_ptr()
        }
    }

    // SAFETY: The `Project::project` impl preserves referent address.
    unsafe impl<T: ?Sized + KnownLayout> Cast<[u8], T> for CastForSized {}

    ptr.recall_validity::<Initialized, (_, (_, _))>()
        .cast::<_, CastForSized, _>()
        .recall_validity::<Valid, _>()
}

#[cfg(kani)]
mod proofs {
    use core::convert::TryInto as _;

    use super::*;
    use crate::proof_support::{
        assert_same_bool, assert_same_u8_elements, assert_same_usize, copy_snapshot,
    };

    const CAPACITY: usize = 8;
    const SIZE: usize = mem::size_of::<u32>();

    // Configuration: Uses the common Kani CI configuration documented in
    // `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
    // x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
    // `-Zfunction-contracts`, and one layout selected by `--randomize-layout`
    // per invocation. Each harness has unwind bound nine; Kani's unwinding
    // assertions remain enabled, so any reachable path requiring more is a
    // verification failure rather than an excluded input.
    //
    // Rust array layout gives `[u32; 0]` size zero and `u32` alignment [13].
    // The `repr(C)` struct algorithm places the first field at offset zero and
    // gives the struct the maximum alignment of its fields [14]. Thus `bytes`
    // begins at offset zero. The zero-length field gives the backing object
    // `u32` alignment without contributing bytes. These language guarantees,
    // rather than the runtime assertions below, are the layout oracle. Since
    // `repr(C)` fixes field order and placement, `--randomize-layout` does not
    // randomize this struct; the overall proof run still covers only its one
    // selected layout for other Rust-layout types.
    #[repr(C)]
    struct AlignedBytes {
        bytes: [u8; 8],
        _align: [u32; 0],
    }

    /// A safe contiguous view of an eight-byte backing buffer.
    ///
    /// `View::any` covers all 45 pairs satisfying `0 <= start <= end <= 8`,
    /// including every empty view. Keeping range selection here makes the
    /// quantified range identical across the six harnesses without hiding
    /// any zerocopy operation under test.
    #[derive(Clone, Copy)]
    struct View {
        start: usize,
        end: usize,
    }

    impl View {
        fn any() -> Self {
            let start: usize = kani::any();
            let end: usize = kani::any();
            kani::assume(start <= end);
            kani::assume(end <= CAPACITY);
            Self { start, end }
        }

        fn get(self, bytes: &[u8; CAPACITY]) -> &[u8] {
            &bytes[self.start..self.end]
        }

        fn get_mut(self, bytes: &mut [u8; CAPACITY]) -> &mut [u8] {
            &mut bytes[self.start..self.end]
        }
    }

    // This is an explicit zerocopy API-policy oracle, not a Rust-language
    // theorem: `Ref::from_bytes` documents rejection for either invalid size
    // or alignment, while this proof also asserts the intended converse.
    fn construction_oracle(source: &[u8]) -> bool {
        source.len() == SIZE && source.as_ptr().cast::<u32>().is_aligned()
    }

    // This independent value oracle copies from the immutable pre-operation
    // snapshot using safe slice-to-array conversion, then asks `u32` to decode
    // its own native-endian memory representation. `None` exposes rather than
    // hides the exact-size precondition.
    fn value_oracle(original: &[u8; CAPACITY], view: View) -> Option<u32> {
        match view.get(original).try_into() {
            Ok(bytes) => Some(u32::from_ne_bytes(bytes)),
            Err(_) => None,
        }
    }

    // This independent effect oracle uses only the immutable pre-operation
    // snapshot, the replacement value, and safe standard-library operations.
    // It cannot accidentally follow a mutation made by the implementation
    // under test. `selected.len() != SIZE` uses `usize` inequality [24]. When
    // that condition is true, `if` executes its block [34] and `return None`
    // terminates the function with `None` [40]; when false, the block is
    // skipped and the equal-length receiver reaches `copy_from_slice`. Thus
    // `None` exposes rather than hides the equal-length precondition.
    fn write_frame_oracle(
        original: &[u8; CAPACITY],
        view: View,
        replacement: u32,
    ) -> Option<[u8; CAPACITY]> {
        let mut original = copy_snapshot(original);
        {
            let selected = view.get_mut(&mut original);
            if selected.len() != SIZE {
                return None;
            }
            selected.copy_from_slice(&replacement.to_ne_bytes());
        }
        Some(original)
    }

    // Safe repair of the first selected byte is the error-path frame oracle.
    // `first_mut` handles empty views without a manually reconstructed bound.
    fn repair_frame_oracle(
        original: &[u8; CAPACITY],
        view: View,
        replacement: u8,
    ) -> [u8; CAPACITY] {
        let mut original = copy_snapshot(original);
        if let Some(first) = view.get_mut(&mut original).first_mut() {
            *first = replacement;
        }
        original
    }

    // Domain: The constructor harness covers every one of the 45 contiguous
    // ranges of an eight-byte, deliberately `u32`-aligned buffer and every
    // buffer value on Kani's target. The error-restoration harness covers the
    // same values and ranges and every replacement `u8`, then assumes the
    // explicit construction policy rejects its range. `View` records only the
    // two range endpoints; every length used by a policy, cover, or result
    // observation comes directly from `slice::len` on the safely indexed
    // source rather than reconstructed as `end - start`. The immutable
    // `Deref` harness and three mutation harnesses generate the same ranges,
    // then assume the explicit construction policy oracle as setup; their
    // effective range is therefore every generated range whose length is
    // `size_of::<u32>()` and whose start pointer Rust's
    // `is_aligned::<u32>()` observation accepts. Covers witness constructible
    // views at offsets zero and `SIZE`; they do not claim that those witnesses
    // exhaustively classify aligned offsets on every target. Each mutation
    // harness independently covers every buffer value and replacement `u32`;
    // splitting them removes an irrelevant Cartesian product without
    // restricting any individual mutation API's value domain.
    //
    // Kani 0.67 documents that `kani::any::<T>()` creates a symbolic valid
    // `T`, with `Arbitrary` representing all possible valid values of that
    // type [35]. The two `usize` calls in `View::any` therefore initially cover
    // every pair of target `usize` values. Primitive ordering supplies the two
    // Boolean range predicates [25], and Kani documents that `kani::assume`
    // makes a true predicate valid on subsequent paths while successfully
    // exiting paths where it is false [36]. Those two assumptions consequently
    // retain exactly the 45 pairs satisfying `start <= end <= CAPACITY`; they
    // define this domain rather than prove the inequalities. The same `any`
    // contract quantifies each harness's `[u8; CAPACITY]` buffer and its `u8`
    // or `u32` replacement over every valid value of that concrete type.
    // Each successful-operation harness later passes the independently
    // evaluated `construction_oracle(source)` Boolean to the same Kani
    // assumption primitive [36]. Those calls retain exactly the generated
    // views which the explicit size-and-alignment policy accepts, defining the
    // effective operation domain described above without assuming that the
    // target constructor itself succeeds.
    // The error-restoration harness instead assumes the negation of that
    // independently evaluated Boolean, retaining exactly the generated views
    // rejected by the policy. Each harness uses one fixed, stack-backed
    // `AlignedBytes` object and separate fixed-size value snapshots. It
    // performs no dynamic allocation and contains no explicit proof loop. The
    // unwind bound of nine applies to
    // every loop reached in zerocopy or the standard-library oracles, with
    // unwinding assertions enabled.
    //
    // Every `kani::cover!` below creates a cover property for its condition.
    // Kani 0.67 says that `SATISFIED` means it found an execution which reaches
    // that property and triggers the condition [37]. The fail-closed Kani
    // runner described in `agent_docs/validation.md` requires every emitted
    // cover property to be satisfied. The constructor and error-restoration
    // harnesses each cover rejected examples with a three-byte aligned view, a
    // four-byte misaligned view, a three-byte misaligned view, and an empty end
    // view; the constructor also covers accepted views at offsets zero and
    // `SIZE`. Each rejected-view cover group contains both `SIZE - 1`
    // expressions, which equal three without overflow as derived below. The
    // error-restoration `u8` inequality cover witnesses a non-idempotent
    // recovered-source write. The `Deref`, `DerefMut`, `write`, and `into_mut`
    // covers each witness accepted views at offsets zero and
    // `SIZE`; the `DerefMut` and `into_mut` `u32` inequality covers witness
    // non-idempotent typed writes, while `write`'s iterator-inequality cover
    // witnesses a replacement whose native bytes differ from the selected
    // pre-call bytes. These covers establish only existence in the modeled
    // domain, not the correctness or exhaustiveness of a partition.
    //
    // Together, the six harnesses establish: the safe sized
    // `Ref<&mut [u8], u32>` constructor succeeds exactly for a
    // size-and-alignment-valid range; immutable and mutable dereference
    // preserve exact address and contents; each mutation API writes through
    // to exactly the selected bytes; and a construction error returns a slice
    // whose modeled raw address, element count, and ordered bytes match the
    // input. A modeled first-byte write through that returned slice produces
    // the expected whole-buffer final frame. These observations do not prove
    // the returned slice's provenance, reference identity, or lifetime.
    //
    // API-policy oracles: `Ref::from_bytes` documents the rejection direction:
    // invalid source size or alignment returns `Err`. The constructor harness
    // adopts success if and only if both checks pass as an explicit intended
    // zerocopy policy; the converse is a regression assertion, not a quoted
    // documentation claim.
    // For this sized `u32`, the checks are `len == size_of::<u32>()` and the
    // compiler's pointer `is_aligned` observation. Slice `len` supplies the
    // number of source `u8` byte elements [11], while `size_of::<u32>()`
    // independently supplies `u32`'s size in bytes [12]. The primitive-layout
    // table fixes that size at four bytes [38]. Consequently `SIZE: usize` is
    // four, and each `SIZE - 1` cover computes integer subtraction `4 - 1 = 3`;
    // three is representable by `usize`, so the subtraction cannot produce a
    // value below the type's minimum and does not overflow [38]. Primitive
    // `usize` equality supplies only the `==`/`!=` classification mechanics
    // [24]; it does not make this zerocopy policy independent. Rust's lazy
    // Boolean `&&` evaluates its right operand only when its left operand is
    // true, and produces true exactly when both operands are true; Boolean `!`
    // produces the logical negation of its operand [39]. Thus
    // `construction_oracle` accepts exactly when both its independently
    // observed size and alignment predicates hold; the same rules combine or
    // negate predicates in the compound covers, error-kind branches, negative
    // setup assumption, and distinct-byte cover. `ConvertError`
    // documents `Alignment` as an improperly aligned conversion source and
    // `Size` as an incorrectly sized source, while the `CastError` alias
    // documents that reference conversions can emit those two errors [22]. The
    // constructor harness adopts that variant-to-condition mapping as an
    // explicit zerocopy API-policy oracle when exactly one check fails; the
    // safe length and alignment observations identify the failed condition but
    // do not independently choose its error variant. Constructing a `Ref` from
    // the source is expected to preserve its referent address. The constructor
    // is also expected not to mutate the source: its
    // `#[must_use = "has no side effects"]` annotation motivates that policy,
    // but the harness conservatively treats source non-mutation as an adopted
    // zerocopy regression property rather than inferring it from a diagnostic
    // attribute. `CastError::into_src` documents restoration of the conversion
    // source; the harness observes only the modeled address, element count,
    // ordered bytes, and subsequent first-byte write-through described above.
    // These are zerocopy API policies, not independent Rust-language evidence;
    // the constructor harness checks the implementation and error
    // discriminants against them. The immutable-`Deref` and mutation harnesses
    // assume only this independent policy oracle before using the constructor
    // as setup; they never assume that the constructor's result is successful.
    // Their `expect` calls therefore recheck valid-input acceptance, while only
    // the constructor harness classifies rejected views. The
    // error-restoration harness separately assumes policy rejection and
    // rechecks that setup before calling `into_src`.
    //
    // Referent and mutation-placement policies: `Ref`'s type documentation
    // defines it as a reference to a `T` stored in `B`, with `B`'s mutability.
    // On that basis, each target has a separate zerocopy API-policy premise:
    // - Immutable `Deref::deref` returns the `u32` stored in the selected
    //   source bytes, preserving that referent's address and value.
    // - `DerefMut::deref_mut` returns a mutable `T` referent [15]; for this
    //   `Ref`, that referent is the `u32` in the selected source bytes, so an
    //   assignment through it updates exactly that selected storage.
    // - `Ref::write` documents that it writes the bytes of its `T` argument.
    //   The adopted placement policy is that it writes them into this `Ref`'s
    //   selected backing bytes. The same method documentation also promises to
    //   forget the argument. This fixed `T = u32` harness observes only the
    //   resulting backing bytes; because `u32` has no observable destructor,
    //   it does not establish the argument-forgetting or destruction behavior.
    // - `Ref::into_mut` documents that it consumes this `Ref` and returns a
    //   mutable reference to `T`; the adopted placement policy is that the
    //   reference addresses the same selected backing bytes and writes through
    //   to them.
    // These policies connect each target operation to the independently built
    // whole-buffer effect oracle. The byte-conversion and safe-slice contracts
    // below determine the expected bytes, but do not themselves establish where
    // any zerocopy API places a write.
    //
    // Value and effect oracles: safe slice-to-array conversion copies into
    // `[u8; N]` when the slice length is `N` [1]. `u32::{from,to}_ne_bytes`
    // convert between `u32` and its native-endian memory representation [2][3].
    // `copy_from_slice` copies every element into its equal-length receiver
    // [4]. Slice `len` [11] exposes the exact-size precondition in the
    // construction and effect oracles; `SIZE` comes from `size_of::<u32>()`
    // [12], not from a manual byte-width reconstruction. The generator's
    // `start <= end` and `end <= CAPACITY` assumptions use primitive `usize`
    // ordering [25] to define the stated range domain; those comparisons supply
    // mechanics, while the bounds remain explicit proof-domain restrictions.
    // Slice pointer extraction, sized pointer casts, and raw-pointer
    // `is_aligned` supply the alignment observation [5]. Shared and mutable
    // `Range<usize>` indexing selects exactly the half-open
    // `view.start..view.end` sub-slice [6]. `first_mut`, reference
    // dereferencing, and assignment make the repair oracle update exactly the
    // first selected byte when one exists [7][8][9]. Each `if let
    // Some(first)` evaluates its scrutinee and executes its body exactly when
    // the `Some` pattern matches [23][34]. Thus the repair oracle leaves an
    // empty selected slice unchanged and performs exactly the documented
    // first-element assignment otherwise; the same language rule governs the
    // modeled write through the recovered target slice. The error-path cover
    // uses safe `first` on the same indexed pre-call snapshot instead of a
    // manual nonempty test followed by indexing [7]. These standard-library
    // and language operations act on the separate `original` and replacement
    // values and do not call `Ref` or zerocopy. The frame oracles modify only a
    // selected safe sub-slice of the pre-operation snapshot.
    // Every array snapshot, including the copy installed in `AlignedBytes`,
    // uses the shared `copy_snapshot`; its `T: Copy` bound makes Rust's
    // copied-place rule explicit [17]. Every recovered-source byte observation
    // and complete whole-buffer frame uses the shared
    // `assert_same_u8_elements`, which obtains both counts through
    // `slice::len`, compares them through shared `assert_same_usize` [24], and
    // ordered bytes through safe slice iteration [18], copied iteration and
    // iterator equality [19], and `u8` equality [20]. The restored-source
    // length observation uses that same helper. No slice or array `PartialEq`
    // assertion silently supplies a byte oracle.
    // Typed-value assertions compare observed and expected `u32` values using
    // the primitive's documented equality operation [21]. Rust maps `!=` to
    // `PartialEq::ne` [24], and the primitive `u32` and `u8` implementations
    // test whether their operands are not equal [20][21]. Thus the
    // `original_value != replacement` covers in both `DerefMut` and `into_mut`
    // witness non-idempotent typed assignments, while the
    // `error_replacement != *first` cover witnesses a non-idempotent byte
    // repair. These comparisons provide reachability partitions only; they do
    // not prove the later frame assertions.
    //
    // Assertion map: The quantified range and value domains consume [25],
    // [35], and [36] exactly as mapped above. `value_oracle`'s explicit
    // `Result` match consumes the safe conversion contract [1] and Rust's
    // match/variant semantics [23]; its error arm returns `None` directly.
    // The constructor harness's match on `(result, expected_success)` consumes
    // [23] to classify the actual `Result`; either mismatched
    // variant/value arm triggers a deliberately false shared Boolean
    // assertion. The Boolean oracle itself consumes [5]'s alignment
    // observation, [11]-[12]'s independent length and size observations, and
    // [24]'s comparison mechanics, plus [39]'s conjunction semantics. The
    // error-kind assertions additionally consume [23]'s explicit variant
    // matches and the zerocopy variant policy
    // in [22]; neither safe observation selects a `ConvertError` discriminant.
    // The error-restoration harness's separate `Result` match consumes [23];
    // its unexpected `Ok` arm forgets the wrapper, fails a verification
    // assertion, and returns, while its `Err` arm alone reaches `into_src`.
    // Every proof assertion here omits custom formatting arguments. Kani 0.67's
    // verification standard library maps those `assert!` and `assert_eq!`
    // forms, including the shared Boolean assertion, to `kani::assert` [27]. A
    // failed assertion or reachable panic is a failed verification property
    // [28]. Kani does not model stack unwinding [29]; these proof-only failure
    // paths consume no cleanup or post-failure behavior. The `Option::expect`
    // and `Result::expect` setup/extraction calls consume their success-value
    // and failure-panic contracts [30][31]; their failure paths use the same
    // Kani premises [28][29]. The source-derived initial typed-value assertions
    // in the immutable `Deref`, `DerefMut`, and `into_mut` harnesses consume
    // [1], [2], [6], [11], [12], [21], and the applicable immutable or mutable
    // `Deref` placement policy above. Direct post-target typed comparisons
    // occur only in the `DerefMut` and `into_mut` harnesses; they consume the
    // symbolic replacement, assignment semantics [9], [21], and the applicable
    // method-placement policy above. The `Ref::write` harness deliberately
    // performs no `Deref` observation: after constructor setup, its only
    // post-target assertion is the complete backing frame. Its distinct-value
    // cover compares copied iteration over the selected original bytes with
    // consuming array iteration over the replacement bytes [18][19]. The array
    // `IntoIterator` implementation moves each array value in start-to-end
    // order [33]. Every post-mutation
    // whole-buffer frame assertion consumes [3], [4], [6], [11], [12],
    // [17]-[20], [24], [34], and [40], plus the applicable placement policy;
    // the `DerefMut` and `into_mut` frames additionally consume [9]. The
    // constructor, immutable
    // `Deref`, `DerefMut`, and `Ref::write` frames use `mem::forget` [26] to
    // end result ownership without running the wrapper or error destructor.
    // Since ordinary destructor operation would recursively destroy fields
    // [32], this also excludes destruction of their `B`; the separately owned
    // backing object is not forgotten. Those outer frames therefore observe
    // only the named target operation rather than a target-plus-destruction
    // composition. The constructor-classification harness's own whole-buffer
    // frame independently checks the adopted constructor non-mutation policy
    // for every generated buffer and view, across both accepted and rejected
    // cases. The proof-family argument for each of the five consumer or error
    // harnesses composes that separately established producer theorem with its
    // target-specific frame. Thus a constructor mutation cannot be hidden by a
    // compensating consumer or error-path mutation. This is a modular
    // composition of verified harness results, not one harness mechanically
    // importing another as a lemma. The immutable-`Deref` frame additionally
    // consumes its placement/value policy above. The separate error-restoration
    // frame consumes [6]-[9], [11], [17]-[20], [23]-[24], [34], and [40]: an
    // empty selected range is unchanged, while a nonempty range has only its
    // first byte replaced. The modeled-address assertions consume [5]'s sized
    // pointer casts and the
    // reference-to-pointer coercion and address-equality contracts in [10]. The
    // backing-object alignment premise consumes [13]-[14].
    //
    // These oracles are limited to `u32`, `u8: Copy`, exact slice lengths, and
    // this target's native byte order. `is_aligned` establishes only alignment,
    // not pointer validity or provenance; pointer equality observes only
    // addresses, not provenance. The proof trusts the documented indexing,
    // `first_mut`, dereference, and assignment semantics; it does not verify
    // those Rust operations. Its independence is from the implementation under
    // test, not from the toolchain: the oracles share the pinned compiler,
    // standard library, and Kani translation/model.
    //
    // The documented premises are exact:
    // - [1] "Tries to create an array `[T; N]` by copying from a slice `&[T]`"
    //   and "Succeeds if `slice.len() == N`."
    // - [2] "Creates a native endian integer value from its memory
    //   representation"; [3] "Returns the memory representation of this integer
    //   as a byte array in native byte order."
    // - [4] "Copies all elements from `src` into `self`" and "The length of
    //   `src` must be the same as `self`."
    // - [5] `as_ptr` returns a raw pointer to the slice's buffer and
    //   `as_mut_ptr` returns its mutable counterpart. Sized-to-sized pointer
    //   `cast` methods cast to another pointer type, and the Reference says a
    //   sized-to-sized pointer cast returns the pointer unchanged. `is_aligned`
    //   then "Returns whether the pointer is properly aligned for `T`."
    // - [6] The Reference maps shared and mutable `a[b]` syntax to `Index` and
    //   `IndexMut`. The array implementations select the corresponding slice
    //   index output. `Range` is "bounded inclusively below and exclusively
    //   above (`start..end`)" and contains exactly `start <= x < end`. For
    //   `SliceIndex<[T]> for Range<usize>`, `Output = [T]`; `index` and
    //   `index_mut` return a shared or mutable reference to the output "at this
    //   location". The implementation documents a panic if `start > end` or
    //   `end` is out of bounds; `View::any` excludes both cases.
    // - [7] `first_mut` "Returns a mutable reference to the first element of
    //   the slice, or `None` if it is empty."
    // - [8] Dereferencing a pointer "denotes the pointed-to location." For an
    //   expression of type `&mut T` that is a local variable, the resulting
    //   memory location can be assigned to.
    // - [9] Assignment "moves a value into a specified place" and then "either
    //   copies or moves the assigned value to the assigned place."
    // - [10] Rust lists `&T` to `*const T` and `&mut T` to `*mut T` coercions;
    //   raw-pointer equality is "by address."
    // - [11] Slice `len` "Returns the number of elements in the slice." For the
    //   proof's `[u8]` sources, those elements are the source bytes.
    // - [12] `size_of` "Returns the size of a type in bytes." Here its type
    //   argument is the sized primitive `u32`.
    // - [13] An array `[T; N]` has size `size_of::<T>() * N` and `T`'s
    //   alignment. With `T = u32` and `N = 0`, `_align` therefore contributes
    //   no bytes but retains `u32` alignment.
    // - [14] The `repr(C)` struct algorithm places fields in declaration order
    //   at aligned offsets, beginning from offset zero, and gives the struct
    //   the maximum field alignment rounded up to a valid final size.
    // - [15] `DerefMut::deref_mut` returns `&mut Self::Target`; `Ref`'s `Deref`
    //   implementation defines `Target = T`.
    // - [20]-[21] `u8` and `u32` document that `PartialEq::eq` tests whether
    //   its operands are equal and is used by `==`, while `PartialEq::ne`
    //   tests whether they are not equal and is used by `!=`.
    // - [23] A match expression compares its scrutinee with patterns in order.
    //   Tuple patterns match tuple values by structure, enum tuple-struct
    //   patterns select the named variant and its fields, and literal patterns
    //   match the exact literal value. Thus the four patterns used below
    //   distinguish both `Result` variants crossed with both Boolean values.
    // - [24] Comparison operators are syntactic sugar for the corresponding
    //   `PartialEq` methods. In particular, `!=` calls `PartialEq::ne`.
    // - [34] An `if` executes its consequent block when all condition operands
    //   are true and skips it when any is false; `if let` additionally requires
    //   its pattern to match.
    // - [37] Each `kani::cover!` creates a cover property, and `SATISFIED`
    //   means Kani found an execution which triggers its condition.
    // - [38] The primitive-layout table fixes `u32`'s size at four bytes, `-`
    //   is integer subtraction, and subtraction overflows only when its result
    //   is outside the integer type's range.
    // - [39] `&&` is logical AND and evaluates its right operand only when its
    //   left operand is true; `!` on a Boolean is logical negation.
    // - [40] Evaluating `return` moves its argument to the function's output
    //   and transfers control to the caller.
    //
    // [1]: https://doc.rust-lang.org/1.93.0/std/primitive.array.html#impl-TryFrom%3C%26%5BT%5D%3E-for-%5BT;+N%5D
    // [2]: https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.from_ne_bytes
    // [3]: https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#method.to_ne_bytes
    // [4]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.copy_from_slice
    // [5]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_mut_ptr
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.cast
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.cast-1
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.as.pointer.sized
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.is_aligned
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.is_aligned-1
    // [6]: https://doc.rust-lang.org/1.93.0/reference/expressions/array-expr.html#r-expr.array.index.trait
    // https://doc.rust-lang.org/1.93.0/std/primitive.array.html#impl-Index%3CI%3E-for-%5BT;+N%5D
    // https://doc.rust-lang.org/1.93.0/std/primitive.array.html#impl-IndexMut%3CI%3E-for-%5BT;+N%5D
    // https://doc.rust-lang.org/1.93.0/std/ops/struct.Range.html
    // https://doc.rust-lang.org/1.93.0/std/ops/struct.Range.html#impl-SliceIndex%3C%5BT%5D%3E-for-Range%3Cusize%3E
    // [7]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.first
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.first_mut
    // [8]: https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.deref.result
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.deref.mut
    // [9]: https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.assign.intro
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.assign.behavior
    // [10]: https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#r-coerce.types.ref-to-pointer
    // https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#r-coerce.types.mut-to-pointer
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#impl-PartialEq-for-*const+T
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#impl-PartialEq-for-*mut+T
    // [11]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.len
    // [12]: https://doc.rust-lang.org/1.93.0/core/mem/fn.size_of.html
    // [13]: https://doc.rust-lang.org/1.93.0/reference/type-layout.html#array-layout
    // [14]: https://doc.rust-lang.org/1.93.0/reference/type-layout.html#reprc-structs
    // [15]: https://doc.rust-lang.org/1.93.0/core/ops/trait.DerefMut.html#tymethod.deref_mut
    // [17]: https://doc.rust-lang.org/1.93.0/reference/expressions.html#moved-and-copied-types
    // [18]: https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
    // [19]: https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.copied
    // https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.eq
    // [20]: https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-PartialEq-for-u8
    // [21]: https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#impl-PartialEq-for-u32
    // [22]: `crate::error::ConvertError` documents `Alignment` as "The
    // conversion source was improperly aligned" and `Size` as "The conversion
    // source was of incorrect size"; the local `CastError` alias documentation
    // identifies those as the two errors emitted by reference conversions.
    // [23]: https://doc.rust-lang.org/1.93.0/reference/expressions/match-expr.html
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#tuple-patterns
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#tuple-struct-patterns
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#literal-patterns
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#binding-modes
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#wildcard-pattern
    // [24]: https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#method.ne
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#comparison-operators
    // [25]: https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialOrd.html#method.le
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialOrd-for-usize
    // [26]: https://doc.rust-lang.org/1.93.0/core/mem/fn.forget.html
    // [27]: https://github.com/model-checking/kani/blob/kani-0.67.0/library/std/src/lib.rs#L19-L45
    // https://github.com/model-checking/kani/blob/kani-0.67.0/library/std/src/lib.rs#L91-L107
    // [28]: https://github.com/model-checking/kani/blob/kani-0.67.0/docs/src/tutorial-kinds-of-failure.md#L1-L5
    // https://model-checking.github.io/kani/verification-results.html
    // [29]: https://github.com/model-checking/kani/blob/kani-0.67.0/docs/src/rust-feature-support.md#L162-L173
    // [30]: https://doc.rust-lang.org/1.93.0/core/option/enum.Option.html#method.expect
    // [31]: https://doc.rust-lang.org/1.93.0/core/result/enum.Result.html#method.expect
    // [32]: https://doc.rust-lang.org/1.93.0/reference/destructors.html#destructors.operation
    // [33]: https://doc.rust-lang.org/1.93.0/std/primitive.array.html#impl-IntoIterator-for-%5BT;+N%5D
    // [34]: https://doc.rust-lang.org/1.93.0/reference/expressions/if-expr.html
    // https://doc.rust-lang.org/1.93.0/reference/expressions/if-expr.html#if-let-patterns
    // https://doc.rust-lang.org/1.93.0/reference/expressions/if-expr.html#r-expr.if.condition-true
    // https://doc.rust-lang.org/1.93.0/reference/expressions/if-expr.html#r-expr.if.else-if
    // [35]: https://model-checking.github.io/kani/crates/doc/kani/fn.any.html
    // [36]: https://model-checking.github.io/kani/crates/doc/kani/fn.assume.html
    // [37]: https://github.com/model-checking/kani/blob/kani-0.67.0/library/kani/src/lib.rs#L66-L77
    // https://github.com/model-checking/kani/blob/kani-0.67.0/docs/src/verification-results.md#cover-property-results
    // [38]: https://doc.rust-lang.org/1.93.0/reference/type-layout.html#primitive-data-layout
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#overflow
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators
    // [39]: https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#lazy-boolean-operators
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#negation-operators
    // [40]: https://doc.rust-lang.org/1.93.0/reference/expressions/return-expr.html
    //
    // These are not generic `Ref<B, T>` theorems. `Ref::from_bytes` performs no
    // representation-validity check for any `T`; `u32: FromBytes` only enables
    // dereference. Validity rejection requires a separately scoped
    // `TryFromBytes::try_ref_from_bytes` proof. The constructor harness does
    // not establish precedence when size and alignment both fail. None of the
    // harnesses cover custom/nested DST layout (#3630), or properties Kani does
    // not fully model such as aliasing, provenance, validity of returned
    // references for their claimed lifetimes, invalid values, and uninitialized
    // memory. In particular, Kani's undefined-behavior guide says it does not
    // track reference lifetimes [16]. The `Deref`, `DerefMut`,
    // `Ref::into_mut`, and `CastError::into_src` observations therefore do not
    // establish reference identity, provenance, or validity for the full
    // lifetimes promised by their types. The modeled `into_src` dereference and
    // write-through remain TOOL/TCB premises rather than a real-Rust soundness
    // theorem.
    //
    // [16]: https://model-checking.github.io/kani/undefined-behaviour.html

    // Scope: `Ref::from_bytes` result and error-kind classification only. This
    // harness deliberately does not dereference a successful `Ref` or recover
    // an error's source. It forgets either result payload before observing the
    // whole-buffer frame, so that frame excludes destruction of the wrapper,
    // error, and their `B` fields. It proves no generic drop behavior.
    #[kani::proof]
    #[kani::unwind(9)]
    fn prove_sized_u32_from_bytes_classification() {
        let original: [u8; CAPACITY] = kani::any();
        let view = View::any();
        let mut backing = AlignedBytes { bytes: copy_snapshot(&original), _align: [] };
        assert!(backing.bytes.as_mut_ptr().cast::<u32>().is_aligned());

        {
            let source = view.get_mut(&mut backing.bytes);
            let source_len = source.len();
            let source_aligned = source.as_mut_ptr().cast::<u32>().is_aligned();
            let expected_success = construction_oracle(source);
            let result = Ref::<_, u32>::from_bytes(source);

            match (result, expected_success) {
                (Ok(typed), true) => {
                    kani::cover!(view.start == 0 && source_len == SIZE);
                    kani::cover!(view.start == SIZE && source_len == SIZE);
                    mem::forget(typed);
                }
                (Err(err), false) => {
                    kani::cover!(view.start == 0 && source_len == SIZE - 1);
                    kani::cover!(view.start == 1 && source_len == SIZE);
                    kani::cover!(view.start == 1 && source_len == SIZE - 1);
                    kani::cover!(view.start == CAPACITY && source_len == 0);
                    if source_len != SIZE && source_aligned {
                        match &err {
                            ConvertError::Size(_) => {}
                            _ => assert_same_bool(false, true),
                        }
                    } else if source_len == SIZE && !source_aligned {
                        match &err {
                            ConvertError::Alignment(_) => {}
                            _ => assert_same_bool(false, true),
                        }
                    }
                    mem::forget(err);
                }
                (Ok(typed), false) => {
                    mem::forget(typed);
                    assert_same_bool(false, true);
                }
                (Err(err), true) => {
                    mem::forget(err);
                    assert_same_bool(false, true);
                }
            }
        }

        assert_same_u8_elements(&backing.bytes, &original);
    }

    // Scope: successful construction is setup; immutable `Deref::deref` is
    // the operation under proof. For every constructible view and buffer
    // value, it must preserve the selected referent's address and initial
    // value. The harness then forgets the temporary `Ref` before checking the
    // whole-buffer frame, excluding wrapper and `B` destruction and proving no
    // generic drop behavior. It does not establish provenance, reference
    // identity, or lifetime safety.
    #[kani::proof]
    #[kani::unwind(9)]
    fn prove_sized_u32_deref() {
        let original: [u8; CAPACITY] = kani::any();
        let view = View::any();
        let mut backing = AlignedBytes { bytes: copy_snapshot(&original), _align: [] };
        assert!(backing.bytes.as_mut_ptr().cast::<u32>().is_aligned());

        {
            let source = view.get_mut(&mut backing.bytes);
            let source_ptr = source.as_mut_ptr();
            let source_len = source.len();
            kani::assume(construction_oracle(source));
            let expected_value = value_oracle(&original, view)
                .expect("construction oracle requires an exact-size value oracle");
            let typed =
                Ref::<_, u32>::from_bytes(source).expect("constructible view should produce a Ref");

            kani::cover!(view.start == 0 && source_len == SIZE);
            kani::cover!(view.start == SIZE && source_len == SIZE);

            let typed_ref = core::ops::Deref::deref(&typed);
            let typed_ptr: *const u32 = typed_ref;
            assert_eq!(typed_ptr.cast::<u8>(), source_ptr as *const u8);
            assert_eq!(*typed_ref, expected_value);
            mem::forget(typed);
        }

        assert_same_u8_elements(&backing.bytes, &original);
    }

    // Scope: failed construction is setup; `CastError::into_src` is the
    // operation under proof. For every rejected view and replacement byte, the
    // returned slice must preserve the input's modeled address, length, and
    // ordered bytes. A modeled first-byte write through that slice must have
    // the independent repair oracle's whole-buffer frame. This does not prove
    // source-reference identity, provenance, or lifetime safety.
    #[kani::proof]
    #[kani::unwind(9)]
    fn prove_sized_u32_error_into_src() {
        let original: [u8; CAPACITY] = kani::any();
        let error_replacement: u8 = kani::any();
        let view = View::any();
        let mut backing = AlignedBytes { bytes: copy_snapshot(&original), _align: [] };
        assert!(backing.bytes.as_mut_ptr().cast::<u32>().is_aligned());

        {
            let source = view.get_mut(&mut backing.bytes);
            let source_ptr = source.as_mut_ptr();
            let source_len = source.len();
            kani::assume(!construction_oracle(source));
            let err = match Ref::<_, u32>::from_bytes(source) {
                Err(err) => err,
                Ok(typed) => {
                    mem::forget(typed);
                    assert_same_bool(false, true);
                    return;
                }
            };

            kani::cover!(view.start == 0 && source_len == SIZE - 1);
            kani::cover!(view.start == 1 && source_len == SIZE);
            kani::cover!(view.start == 1 && source_len == SIZE - 1);
            kani::cover!(view.start == CAPACITY && source_len == 0);
            if let Some(first) = view.get(&original).first() {
                kani::cover!(error_replacement != *first);
            }
            let recovered = err.into_src();
            assert_eq!(recovered.as_mut_ptr(), source_ptr);
            assert_same_usize(recovered.len(), source_len);
            assert_same_u8_elements(&*recovered, view.get(&original));
            if let Some(first) = recovered.first_mut() {
                *first = error_replacement;
            }
        }

        let expected = repair_frame_oracle(&original, view, error_replacement);
        assert_same_u8_elements(&backing.bytes, &expected);
    }

    // Scope: successful construction is setup; `DerefMut::deref_mut` is the
    // operation under proof. For every constructible view and every original
    // and replacement value, it must preserve address and initial value, and a
    // write through the returned reference must have the exact whole-buffer
    // frame supplied by the independent oracle. After the returned borrow ends,
    // the harness forgets the temporary `Ref`; the outer frame therefore
    // excludes destruction of the wrapper and its `B` field and proves no
    // generic drop behavior.
    #[kani::proof]
    #[kani::unwind(9)]
    fn prove_sized_u32_deref_mut() {
        let original: [u8; CAPACITY] = kani::any();
        let replacement: u32 = kani::any();
        let view = View::any();
        let mut backing = AlignedBytes { bytes: copy_snapshot(&original), _align: [] };
        assert!(backing.bytes.as_mut_ptr().cast::<u32>().is_aligned());

        {
            let source = view.get_mut(&mut backing.bytes);
            let source_ptr = source.as_mut_ptr();
            let source_len = source.len();
            kani::assume(construction_oracle(source));
            let original_value = value_oracle(&original, view)
                .expect("construction oracle requires an exact-size value oracle");
            let mut typed =
                Ref::<_, u32>::from_bytes(source).expect("constructible view should produce a Ref");

            kani::cover!(view.start == 0 && source_len == SIZE);
            kani::cover!(view.start == SIZE && source_len == SIZE);
            kani::cover!(original_value != replacement);

            {
                let typed_mut = core::ops::DerefMut::deref_mut(&mut typed);
                assert_eq!((typed_mut as *mut u32).cast::<u8>(), source_ptr);
                assert_eq!(*typed_mut, original_value);
                *typed_mut = replacement;
            }
            mem::forget(typed);
        }

        let expected = write_frame_oracle(&original, view, replacement)
            .expect("constructible view should have an exact-size frame");
        assert_same_u8_elements(&backing.bytes, &expected);
    }

    // Scope: successful construction is setup; `Ref::write` is the operation
    // under proof. For every constructible view and every original and
    // replacement value, the independent oracle supplies the exact
    // whole-buffer native-byte frame. The harness performs no typed `Deref`
    // observation, so a separate `Deref` regression cannot be misattributed to
    // `write`. It is fixed to `u32` and does not establish `Ref::write`'s
    // separate promise to forget its argument; `u32` destruction is
    // unobservable here. After the target call, the harness uses safe
    // `mem::forget` to consume the wrapper without running its drop glue; this
    // isolates the outer frame from wrapper destruction and proves no generic
    // `Ref` drop behavior. A snapshot-only cover witnesses a replacement whose
    // native bytes differ from the selected pre-call bytes.
    #[kani::proof]
    #[kani::unwind(9)]
    fn prove_sized_u32_write() {
        let original: [u8; CAPACITY] = kani::any();
        let replacement: u32 = kani::any();
        let view = View::any();
        let mut backing = AlignedBytes { bytes: copy_snapshot(&original), _align: [] };
        assert!(backing.bytes.as_mut_ptr().cast::<u32>().is_aligned());

        {
            let source = view.get_mut(&mut backing.bytes);
            let source_len = source.len();
            kani::assume(construction_oracle(source));
            let replacement_bytes = replacement.to_ne_bytes();
            kani::cover!(!view.get(&original).iter().copied().eq(replacement_bytes));
            let mut typed =
                Ref::<_, u32>::from_bytes(source).expect("constructible view should produce a Ref");

            kani::cover!(view.start == 0 && source_len == SIZE);
            kani::cover!(view.start == SIZE && source_len == SIZE);

            Ref::write(&mut typed, replacement);
            mem::forget(typed);
        }

        let expected = write_frame_oracle(&original, view, replacement)
            .expect("constructible view should have an exact-size frame");
        assert_same_u8_elements(&backing.bytes, &expected);
    }

    // Scope: successful construction is setup; `Ref::into_mut` is the
    // operation under proof. For every constructible view and every original
    // and replacement value, its returned reference must preserve address and
    // initial value, and a write through it must have the independent oracle's
    // exact whole-buffer frame.
    #[kani::proof]
    #[kani::unwind(9)]
    fn prove_sized_u32_into_mut() {
        let original: [u8; CAPACITY] = kani::any();
        let replacement: u32 = kani::any();
        let view = View::any();
        let mut backing = AlignedBytes { bytes: copy_snapshot(&original), _align: [] };
        assert!(backing.bytes.as_mut_ptr().cast::<u32>().is_aligned());

        {
            let source = view.get_mut(&mut backing.bytes);
            let source_ptr = source.as_mut_ptr();
            let source_len = source.len();
            kani::assume(construction_oracle(source));
            let original_value = value_oracle(&original, view)
                .expect("construction oracle requires an exact-size value oracle");
            let typed =
                Ref::<_, u32>::from_bytes(source).expect("constructible view should produce a Ref");
            let typed = Ref::into_mut(typed);

            kani::cover!(view.start == 0 && source_len == SIZE);
            kani::cover!(view.start == SIZE && source_len == SIZE);
            kani::cover!(original_value != replacement);

            assert_eq!((typed as *mut u32).cast::<u8>(), source_ptr);
            assert_eq!(*typed, original_value);
            *typed = replacement;
            assert_eq!(*typed, replacement);
        }

        let expected = write_frame_oracle(&original, view, replacement)
            .expect("constructible view should have an exact-size frame");
        assert_same_u8_elements(&backing.bytes, &expected);
    }
}

#[cfg(test)]
#[allow(clippy::assertions_on_result_states)]
mod tests {
    use core::convert::TryInto as _;

    use super::*;
    use crate::util::testutil::*;

    #[test]
    fn test_mut_slice_into_ref() {
        // Prior to #1260/#1299, calling `into_ref` on a `&mut [u8]`-backed
        // `Ref` was not supported.
        let mut buf = [0u8];
        let r = Ref::<&mut [u8], u8>::from_bytes(&mut buf).unwrap();
        assert_eq!(Ref::into_ref(r), &0);
    }

    #[test]
    fn test_address() {
        // Test that the `Deref` and `DerefMut` implementations return a
        // reference which points to the right region of memory.

        let buf = [0];
        let r = Ref::<_, u8>::from_bytes(&buf[..]).unwrap();
        let buf_ptr = buf.as_ptr();
        let deref_ptr: *const u8 = r.deref();
        assert_eq!(buf_ptr, deref_ptr);

        let buf = [0];
        let r = Ref::<_, [u8]>::from_bytes(&buf[..]).unwrap();
        let buf_ptr = buf.as_ptr();
        let deref_ptr = r.deref().as_ptr();
        assert_eq!(buf_ptr, deref_ptr);
    }

    // Verify that values written to a `Ref` are properly shared between the
    // typed and untyped representations, that reads via `deref` and `read`
    // behave the same, and that writes via `deref_mut` and `write` behave the
    // same.
    fn test_new_helper(mut r: Ref<&mut [u8], AU64>) {
        // assert that the value starts at 0
        assert_eq!(*r, AU64(0));
        assert_eq!(Ref::read(&r), AU64(0));

        // Assert that values written to the typed value are reflected in the
        // byte slice.
        const VAL1: AU64 = AU64(0xFF00FF00FF00FF00);
        *r = VAL1;
        assert_eq!(Ref::bytes(&r), &VAL1.to_bytes());
        *r = AU64(0);
        Ref::write(&mut r, VAL1);
        assert_eq!(Ref::bytes(&r), &VAL1.to_bytes());

        // Assert that values written to the byte slice are reflected in the
        // typed value.
        const VAL2: AU64 = AU64(!VAL1.0); // different from `VAL1`
        Ref::bytes_mut(&mut r).copy_from_slice(&VAL2.to_bytes()[..]);
        assert_eq!(*r, VAL2);
        assert_eq!(Ref::read(&r), VAL2);
    }

    // Verify that values written to a `Ref` are properly shared between the
    // typed and untyped representations; pass a value with `typed_len` `AU64`s
    // backed by an array of `typed_len * 8` bytes.
    fn test_new_helper_slice(mut r: Ref<&mut [u8], [AU64]>, typed_len: usize) {
        // Assert that the value starts out zeroed.
        assert_eq!(&*r, vec![AU64(0); typed_len].as_slice());

        // Check the backing storage is the exact same slice.
        let untyped_len = typed_len * 8;
        assert_eq!(Ref::bytes(&r).len(), untyped_len);
        assert_eq!(Ref::bytes(&r).as_ptr(), r.as_ptr().cast::<u8>());

        // Assert that values written to the typed value are reflected in the
        // byte slice.
        const VAL1: AU64 = AU64(0xFF00FF00FF00FF00);
        for typed in &mut *r {
            *typed = VAL1;
        }
        assert_eq!(Ref::bytes(&r), VAL1.0.to_ne_bytes().repeat(typed_len).as_slice());

        // Assert that values written to the byte slice are reflected in the
        // typed value.
        const VAL2: AU64 = AU64(!VAL1.0); // different from VAL1
        Ref::bytes_mut(&mut r).copy_from_slice(&VAL2.0.to_ne_bytes().repeat(typed_len));
        assert!(r.iter().copied().all(|x| x == VAL2));
    }

    #[test]
    fn test_new_aligned_sized() {
        // Test that a properly-aligned, properly-sized buffer works for new,
        // new_from_prefix, and new_from_suffix, and that new_from_prefix and
        // new_from_suffix return empty slices. Test that a properly-aligned
        // buffer whose length is a multiple of the element size works for
        // new_slice.

        // A buffer with an alignment of 8.
        let mut buf = Align::<[u8; 8], AU64>::default();
        // `buf.t` should be aligned to 8, so this should always succeed.
        test_new_helper(Ref::<_, AU64>::from_bytes(&mut buf.t[..]).unwrap());
        {
            // In a block so that `r` and `suffix` don't live too long.
            buf.set_default();
            let (r, suffix) = Ref::<_, AU64>::from_prefix(&mut buf.t[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper(r);
        }
        {
            buf.set_default();
            let (prefix, r) = Ref::<_, AU64>::from_suffix(&mut buf.t[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper(r);
        }

        // A buffer with alignment 8 and length 24. We choose this length very
        // intentionally: if we instead used length 16, then the prefix and
        // suffix lengths would be identical. In the past, we used length 16,
        // which resulted in this test failing to discover the bug uncovered in
        // #506.
        let mut buf = Align::<[u8; 24], AU64>::default();
        // `buf.t` should be aligned to 8 and have a length which is a multiple
        // of `size_of::<AU64>()`, so this should always succeed.
        test_new_helper_slice(Ref::<_, [AU64]>::from_bytes(&mut buf.t[..]).unwrap(), 3);
        buf.set_default();
        let r = Ref::<_, [AU64]>::from_bytes_with_elems(&mut buf.t[..], 3).unwrap();
        test_new_helper_slice(r, 3);

        let ascending: [u8; 24] = (0..24).collect::<Vec<_>>().try_into().unwrap();
        // 16 ascending bytes followed by 8 zeros.
        let mut ascending_prefix = ascending;
        ascending_prefix[16..].copy_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0]);
        // 8 zeros followed by 16 ascending bytes.
        let mut ascending_suffix = ascending;
        ascending_suffix[..8].copy_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0]);
        {
            buf.t = ascending_suffix;
            let (r, suffix) = Ref::<_, [AU64]>::from_prefix_with_elems(&mut buf.t[..], 1).unwrap();
            assert_eq!(suffix, &ascending[8..]);
            test_new_helper_slice(r, 1);
        }
        {
            buf.t = ascending_prefix;
            let (prefix, r) = Ref::<_, [AU64]>::from_suffix_with_elems(&mut buf.t[..], 1).unwrap();
            assert_eq!(prefix, &ascending[..16]);
            test_new_helper_slice(r, 1);
        }
    }

    #[test]
    fn test_new_oversized() {
        // Test that a properly-aligned, overly-sized buffer works for
        // `new_from_prefix` and `new_from_suffix`, and that they return the
        // remainder and prefix of the slice respectively.

        let mut buf = Align::<[u8; 16], AU64>::default();
        {
            // In a block so that `r` and `suffix` don't live too long. `buf.t`
            // should be aligned to 8, so this should always succeed.
            let (r, suffix) = Ref::<_, AU64>::from_prefix(&mut buf.t[..]).unwrap();
            assert_eq!(suffix.len(), 8);
            test_new_helper(r);
        }
        {
            buf.set_default();
            // `buf.t` should be aligned to 8, so this should always succeed.
            let (prefix, r) = Ref::<_, AU64>::from_suffix(&mut buf.t[..]).unwrap();
            assert_eq!(prefix.len(), 8);
            test_new_helper(r);
        }
    }

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn test_new_error() {
        // Fail because the buffer is too large.

        // A buffer with an alignment of 8.
        let buf = Align::<[u8; 16], AU64>::default();
        // `buf.t` should be aligned to 8, so only the length check should fail.
        assert!(Ref::<_, AU64>::from_bytes(&buf.t[..]).is_err());

        // Fail because the buffer is too small.

        // A buffer with an alignment of 8.
        let buf = Align::<[u8; 4], AU64>::default();
        // `buf.t` should be aligned to 8, so only the length check should fail.
        assert!(Ref::<_, AU64>::from_bytes(&buf.t[..]).is_err());
        assert!(Ref::<_, AU64>::from_prefix(&buf.t[..]).is_err());
        assert!(Ref::<_, AU64>::from_suffix(&buf.t[..]).is_err());

        // Fail because the length is not a multiple of the element size.

        let buf = Align::<[u8; 12], AU64>::default();
        // `buf.t` has length 12, but element size is 8.
        assert!(Ref::<_, [AU64]>::from_bytes(&buf.t[..]).is_err());

        // Fail because the buffer is too short.
        let buf = Align::<[u8; 12], AU64>::default();
        // `buf.t` has length 12, but the element size is 8 (and we're expecting
        // two of them). For each function, we test with a length that would
        // cause the size to overflow `usize`, and with a normal length that
        // will fail thanks to the buffer being too short; these are different
        // error paths, and while the error types are the same, the distinction
        // shows up in code coverage metrics.
        let n = (usize::MAX / mem::size_of::<AU64>()) + 1;
        assert!(Ref::<_, [AU64]>::from_bytes_with_elems(&buf.t[..], n).is_err());
        assert!(Ref::<_, [AU64]>::from_bytes_with_elems(&buf.t[..], 2).is_err());
        assert!(Ref::<_, [AU64]>::from_prefix_with_elems(&buf.t[..], n).is_err());
        assert!(Ref::<_, [AU64]>::from_prefix_with_elems(&buf.t[..], 2).is_err());
        assert!(Ref::<_, [AU64]>::from_suffix_with_elems(&buf.t[..], n).is_err());
        assert!(Ref::<_, [AU64]>::from_suffix_with_elems(&buf.t[..], 2).is_err());

        // Fail because the alignment is insufficient.

        // A buffer with an alignment of 8. An odd buffer size is chosen so that
        // the last byte of the buffer has odd alignment.
        let buf = Align::<[u8; 13], AU64>::default();
        // Slicing from 1, we get a buffer with size 12 (so the length check
        // should succeed) but an alignment of only 1, which is insufficient.
        assert!(Ref::<_, AU64>::from_bytes(&buf.t[1..]).is_err());
        assert!(Ref::<_, AU64>::from_prefix(&buf.t[1..]).is_err());
        assert!(Ref::<_, [AU64]>::from_bytes(&buf.t[1..]).is_err());
        assert!(Ref::<_, [AU64]>::from_bytes_with_elems(&buf.t[1..], 1).is_err());
        assert!(Ref::<_, [AU64]>::from_prefix_with_elems(&buf.t[1..], 1).is_err());
        assert!(Ref::<_, [AU64]>::from_suffix_with_elems(&buf.t[1..], 1).is_err());
        // Slicing is unnecessary here because `new_from_suffix` uses the suffix
        // of the slice, which has odd alignment.
        assert!(Ref::<_, AU64>::from_suffix(&buf.t[..]).is_err());

        // Fail due to arithmetic overflow.

        let buf = Align::<[u8; 16], AU64>::default();
        let unreasonable_len = usize::MAX / mem::size_of::<AU64>() + 1;
        assert!(Ref::<_, [AU64]>::from_prefix_with_elems(&buf.t[..], unreasonable_len).is_err());
        assert!(Ref::<_, [AU64]>::from_suffix_with_elems(&buf.t[..], unreasonable_len).is_err());
    }

    #[test]
    #[allow(unstable_name_collisions)]
    #[allow(clippy::as_conversions)]
    fn test_into_ref_mut() {
        #[allow(unused)]
        use crate::util::AsAddress as _;

        let mut buf = Align::<[u8; 8], u64>::default();
        let r = Ref::<_, u64>::from_bytes(&buf.t[..]).unwrap();
        let rf = Ref::into_ref(r);
        assert_eq!(rf, &0u64);
        let buf_addr = (&buf.t as *const [u8; 8]).addr();
        assert_eq!((rf as *const u64).addr(), buf_addr);

        let r = Ref::<_, u64>::from_bytes(&mut buf.t[..]).unwrap();
        let rf = Ref::into_mut(r);
        assert_eq!(rf, &mut 0u64);
        assert_eq!((rf as *mut u64).addr(), buf_addr);

        *rf = u64::MAX;
        assert_eq!(buf.t, [0xFF; 8]);
    }

    #[test]
    fn test_display_debug() {
        let buf = Align::<[u8; 8], u64>::default();
        let r = Ref::<_, u64>::from_bytes(&buf.t[..]).unwrap();
        assert_eq!(format!("{}", r), "0");
        assert_eq!(format!("{:?}", r), "Ref(0)");

        let buf = Align::<[u8; 8], u64>::default();
        let r = Ref::<_, [u64]>::from_bytes(&buf.t[..]).unwrap();
        assert_eq!(format!("{:?}", r), "Ref([0])");
    }

    #[test]
    fn test_eq() {
        let buf1 = 0_u64;
        let r1 = Ref::<_, u64>::from_bytes(buf1.as_bytes()).unwrap();
        let buf2 = 0_u64;
        let r2 = Ref::<_, u64>::from_bytes(buf2.as_bytes()).unwrap();
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_ne() {
        let buf1 = 0_u64;
        let r1 = Ref::<_, u64>::from_bytes(buf1.as_bytes()).unwrap();
        let buf2 = 1_u64;
        let r2 = Ref::<_, u64>::from_bytes(buf2.as_bytes()).unwrap();
        assert_ne!(r1, r2);
    }

    #[test]
    fn test_ord() {
        let buf1 = 0_u64;
        let r1 = Ref::<_, u64>::from_bytes(buf1.as_bytes()).unwrap();
        let buf2 = 1_u64;
        let r2 = Ref::<_, u64>::from_bytes(buf2.as_bytes()).unwrap();
        assert!(r1 < r2);
        assert_eq!(PartialOrd::partial_cmp(&r1, &r2), Some(Ordering::Less));
        assert_eq!(Ord::cmp(&r1, &r2), Ordering::Less);
    }
}

#[cfg(all(test, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS))]
mod benches {
    use test::{self, Bencher};

    use super::*;
    use crate::util::testutil::*;

    #[bench]
    fn bench_from_bytes_sized(b: &mut Bencher) {
        let buf = Align::<[u8; 8], AU64>::default();
        // `buf.t` should be aligned to 8, so this should always succeed.
        let bytes = &buf.t[..];
        b.iter(|| test::black_box(Ref::<_, AU64>::from_bytes(test::black_box(bytes)).unwrap()));
    }

    #[bench]
    fn bench_into_ref_sized(b: &mut Bencher) {
        let buf = Align::<[u8; 8], AU64>::default();
        let bytes = &buf.t[..];
        let r = Ref::<_, AU64>::from_bytes(bytes).unwrap();
        b.iter(|| test::black_box(Ref::into_ref(test::black_box(r))));
    }

    #[bench]
    fn bench_into_mut_sized(b: &mut Bencher) {
        let mut buf = Align::<[u8; 8], AU64>::default();
        let buf = &mut buf.t[..];
        let _ = Ref::<_, AU64>::from_bytes(&mut *buf).unwrap();
        b.iter(move || {
            // SAFETY: The preceding `from_bytes` succeeded, and so we know that
            // `buf` is validly-aligned and has the correct length.
            let r = unsafe { Ref::<&mut [u8], AU64>::new_unchecked(&mut *buf) };
            test::black_box(Ref::into_mut(test::black_box(r)));
        });
    }

    #[bench]
    fn bench_deref_sized(b: &mut Bencher) {
        let buf = Align::<[u8; 8], AU64>::default();
        let bytes = &buf.t[..];
        let r = Ref::<_, AU64>::from_bytes(bytes).unwrap();
        b.iter(|| {
            let temp = test::black_box(r);
            test::black_box(temp.deref());
        });
    }

    #[bench]
    fn bench_deref_mut_sized(b: &mut Bencher) {
        let mut buf = Align::<[u8; 8], AU64>::default();
        let buf = &mut buf.t[..];
        let _ = Ref::<_, AU64>::from_bytes(&mut *buf).unwrap();
        b.iter(|| {
            // SAFETY: The preceding `from_bytes` succeeded, and so we know that
            // `buf` is validly-aligned and has the correct length.
            let r = unsafe { Ref::<&mut [u8], AU64>::new_unchecked(&mut *buf) };
            let mut temp = test::black_box(r);
            test::black_box(temp.deref_mut());
        });
    }
}
