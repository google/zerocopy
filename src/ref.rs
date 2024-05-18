// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use super::*;

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
    /// `Ref` can be used to treat a sequence of bytes as a structured type, and to
    /// read and write the fields of that type as if the byte slice reference were
    /// simply a reference to that type.
    ///
    /// ```rust
    /// # #[cfg(feature = "derive")] { // This example uses derives, and won't compile without them
    /// use zerocopy::{IntoBytes, ByteSliceMut, FromBytes, FromZeros, KnownLayout, Immutable, Ref, SplitByteSlice, Unaligned};
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
    /// struct UdpPacket<B> {
    ///     header: Ref<B, UdpHeader>,
    ///     body: B,
    /// }
    ///
    /// impl<B: SplitByteSlice> UdpPacket<B> {
    ///     pub fn parse(bytes: B) -> Option<UdpPacket<B>> {
    ///         let (header, body) = Ref::unaligned_from_prefix(bytes).ok()?;
    ///         Some(UdpPacket { header, body })
    ///     }
    ///
    ///     pub fn get_src_port(&self) -> [u8; 2] {
    ///         self.header.src_port
    ///     }
    /// }
    ///
    /// impl<B: ByteSliceMut> UdpPacket<B> {
    ///     pub fn with_src_port(&mut self, src_port: [u8; 2]) {
    ///         self.header.src_port = src_port;
    ///     }
    /// }
    /// # }
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

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
{
    #[must_use = "has no side effects"]
    pub(crate) fn sized_from(bytes: B) -> Result<Ref<B, T>, CastError<B, T>> {
        if bytes.len() != mem::size_of::<T>() {
            return Err(SizeError::new(bytes).into());
        }
        if !util::aligned_to::<_, T>(bytes.deref()) {
            return Err(AlignmentError::new(bytes).into());
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
        if !util::aligned_to::<_, T>(bytes.deref()) {
            return Err(AlignmentError::new(bytes).into());
        }
        let (bytes, suffix) =
            try_split_at(bytes, mem::size_of::<T>()).map_err(|b| SizeError::new(b).into())?;
        // SAFETY: We just validated alignment and that `bytes` is at least as
        // large as `T`. `try_split_at(bytes, mem::size_of::<T>())?` ensures
        // that the new `bytes` is exactly the size of `T`. By safety
        // postcondition on `SplitByteSlice::try_split_at` we can rely on
        // `try_split_at` to produce the correct `bytes` and `suffix`.
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
        let (prefix, bytes) =
            try_split_at(bytes, split_at).map_err(|b| SizeError::new(b).into())?;
        if !util::aligned_to::<_, T>(bytes.deref()) {
            return Err(AlignmentError::new(bytes).into());
        }
        // SAFETY: Since `split_at` is defined as `bytes_len - size_of::<T>()`,
        // the `bytes` which results from `let (prefix, bytes) =
        // try_split_at(bytes, split_at)?` has length `size_of::<T>()`. After
        // constructing `bytes`, we validate that it has the proper alignment.
        // By safety postcondition on `SplitByteSlice::try_split_at` we can rely
        // on `try_split_at` to produce the correct `prefix` and `bytes`.
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
    /// if `source` is not appropriately aligned for `T`, this returns `Err`.
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate#what-is-a-valid-size
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
    /// this returns `Err`.
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate#what-is-a-valid-size
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
        #[allow(unstable_name_collisions, clippy::incompatible_msrv)]
        let split_at = unsafe { source.len().unchecked_sub(remainder.len()) };
        let (bytes, suffix) =
            try_split_at(source, split_at).map_err(|b| SizeError::new(b).into())?;
        // SAFETY: `try_cast_into` validates size and alignment, and returns a
        // `split_at` that indicates how many bytes of `source` correspond to a
        // valid `T`. By safety postcondition on `SplitByteSlice::try_split_at`
        // we can rely on `try_split_at` to produce the correct `source` and
        // `suffix`.
        let r = unsafe { Ref::new_unchecked(bytes) };
        Ok((r, suffix))
    }

    /// Constructs a `Ref` from the suffix of a byte slice.
    ///
    /// This method computes the [largest possible size of `T`][valid-size] that
    /// can fit in the trailing bytes of `source`, then attempts to return both
    /// a `Ref` to those bytes, and a reference to the preceding bytes. If there
    /// are insufficient bytes, or if that suffix of `source` is not
    /// appropriately aligned, this returns `Err`.
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate#what-is-a-valid-size
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
        let (prefix, bytes) =
            try_split_at(source, split_at).map_err(|b| SizeError::new(b).into())?;
        // SAFETY: `try_cast_into` validates size and alignment, and returns a
        // `try_split_at` that indicates how many bytes of `source` correspond to
        // a valid `T`. By safety postcondition on
        // `SplitByteSlice::try_split_at` we can rely on `try_split_at` to
        // produce the correct `prefix` and `bytes`.
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
    /// aligned, this returns `Err`.
    #[inline]
    pub fn from_bytes_with_elems(source: B, count: usize) -> Result<Ref<B, T>, CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let expected_len = match count.size_for_metadata(T::LAYOUT) {
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
    /// not appropriately aligned, this returns `Err`.
    #[inline]
    pub fn from_prefix_with_elems(
        source: B,
        count: usize,
    ) -> Result<(Ref<B, T>, B), CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let expected_len = match count.size_for_metadata(T::LAYOUT) {
            Some(len) => len,
            None => return Err(SizeError::new(source).into()),
        };
        if source.len() < expected_len {
            return Err(SizeError::new(source).into());
        }
        let (prefix, bytes) = source.split_at(expected_len);
        Self::from_bytes(prefix).map(move |l| (l, bytes))
    }

    /// Constructs a `Ref` from the suffix of the given bytes with DST length
    /// equal to `count` without copying.
    ///
    /// This method attempts to return a `Ref` to the suffix of `source`
    /// interpreted as a `T` with `count` trailing elements, and a reference to
    /// the preceding bytes. If there are insufficient bytes, or if that suffix
    /// of `source` is not appropriately aligned, this returns `Err`.
    #[inline]
    pub fn from_suffix_with_elems(
        source: B,
        count: usize,
    ) -> Result<(B, Ref<B, T>), CastError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        let expected_len = match count.size_for_metadata(T::LAYOUT) {
            Some(len) => len,
            None => return Err(SizeError::new(source).into()),
        };
        let split_at = if let Some(split_at) = source.len().checked_sub(expected_len) {
            split_at
        } else {
            return Err(SizeError::new(source).into());
        };
        let (bytes, suffix) = source.split_at(split_at);
        Self::from_bytes(suffix).map(move |l| (bytes, l))
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: Unaligned + KnownLayout + Immutable + ?Sized,
{
    /// Constructs a `Ref` for a type with no alignment requirement from a byte
    /// slice.
    ///
    /// If the length of `source` is not a [valid size of `T`][valid-size], this
    /// returns `Err`.
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate#what-is-a-valid-size
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
    /// #[derive(Immutable, KnownLayout, Unaligned)]
    /// #[repr(C, packed)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let f = Ref::<&[u8], ZSTy>::unaligned_from_bytes(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn unaligned_from_bytes(source: B) -> Result<Ref<B, T>, SizeError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        match Ref::from_bytes(source) {
            Ok(dst) => Ok(dst),
            Err(CastError::Size(e)) => Err(e),
            Err(CastError::Alignment(_)) => unreachable!(),
            Err(CastError::Validity(i)) => match i {},
        }
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: Unaligned + KnownLayout + Immutable + ?Sized,
{
    /// Constructs a `Ref` for a type with no alignment requirement from the
    /// prefix of a byte slice.
    ///
    /// This method computes the [largest possible size of `T`][valid-size] that
    /// can fit in the leading bytes of `source`, then attempts to return both a
    /// `Ref` to those bytes, and a reference to the remaining bytes. If there
    /// are insufficient bytes, this returns `Err`.
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate#what-is-a-valid-size
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
    /// #[derive(Immutable, KnownLayout, Unaligned)]
    /// #[repr(C, packed)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::unaligned_from_prefix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn unaligned_from_prefix(source: B) -> Result<(Ref<B, T>, B), SizeError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        Ref::from_prefix(source).map_err(|e| match e {
            CastError::Size(e) => e,
            CastError::Alignment(_) => unreachable!(),
            CastError::Validity(i) => match i {},
        })
    }

    /// Constructs a `Ref` for a type with no alignment requirement from the
    /// suffix of a byte slice.
    ///
    /// This method computes the [largest possible size of `T`][valid-size] that
    /// can fit in the trailing bytes of `source`, then attempts to return both
    /// a `Ref` to those bytes, and a reference to the preceding bytes. If there
    /// are insufficient bytes, this returns `Err`.
    ///
    /// `T` may be a sized type, a slice, or a [slice DST][slice-dst].
    ///
    /// [valid-size]: crate#what-is-a-valid-size
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
    /// #[derive(Immutable, KnownLayout, Unaligned)]
    /// #[repr(C, packed)]
    /// struct ZSTy {
    ///     leading_sized: u16,
    ///     trailing_dst: [()],
    /// }
    ///
    /// let _ = Ref::<_, ZSTy>::unaligned_from_suffix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn unaligned_from_suffix(source: B) -> Result<(B, Ref<B, T>), SizeError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        Ref::from_suffix(source).map_err(|e| match e {
            CastError::Size(e) => e,
            CastError::Alignment(_) => unreachable!(),
            CastError::Validity(i) => match i {},
        })
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: KnownLayout<PointerMetadata = usize> + Unaligned + Immutable + ?Sized,
{
    /// Constructs a `Ref` from the given bytes with DST length equal to `count`
    /// without copying.
    ///
    /// This method attempts to return a `Ref` to the prefix of `source`
    /// interpreted as a `T` with `count` trailing elements, and a reference to
    /// the remaining bytes. If the length of `source` is not equal to the size
    /// of `Self` with `count` elements, this returns `Err`.
    #[inline]
    pub fn unaligned_from_bytes_with_elems(
        source: B,
        count: usize,
    ) -> Result<Ref<B, T>, SizeError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        Self::from_bytes_with_elems(source, count).map_err(|e| match e {
            CastError::Size(e) => e,
            CastError::Alignment(_) => unreachable!(),
            CastError::Validity(i) => match i {},
        })
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: KnownLayout<PointerMetadata = usize> + Unaligned + Immutable + ?Sized,
{
    /// Constructs a `Ref` from the prefix of the given bytes with DST
    /// length equal to `count` without copying.
    ///
    /// This method attempts to return a `Ref` to the prefix of `source`
    /// interpreted as a `T` with `count` trailing elements, and a reference to
    /// the remaining bytes. If there are insufficient bytes, this returns
    /// `Err`.
    #[inline]
    pub fn unaligned_from_prefix_with_elems(
        source: B,
        count: usize,
    ) -> Result<(Ref<B, T>, B), SizeError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        Self::from_prefix_with_elems(source, count).map_err(|e| match e {
            CastError::Size(e) => e,
            CastError::Alignment(_) => unreachable!(),
            CastError::Validity(i) => match i {},
        })
    }

    /// Constructs a `Ref` from the suffix of the given bytes with DST length
    /// equal to `count` without copying.
    ///
    /// This method attempts to return a `Ref` to the suffix of `source`
    /// interpreted as a `T` with `count` trailing elements, and a reference to
    /// the preceding bytes. If there are insufficient bytes, this returns
    /// `Err`.
    #[inline]
    pub fn unaligned_from_suffix_with_elems(
        source: B,
        count: usize,
    ) -> Result<(B, Ref<B, T>), SizeError<B, T>> {
        static_assert_dst_is_not_zst!(T);
        Self::from_suffix_with_elems(source, count).map_err(|e| match e {
            CastError::Size(e) => e,
            CastError::Alignment(_) => unreachable!(),
            CastError::Validity(i) => match i {},
        })
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
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn into_ref(self) -> &'a T {
        // Presumably unreachable, since we've guarded each constructor of `Ref`.
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `IntoByteSlice`.
        let b = unsafe { self.into_byte_slice() };

        // PANICS: By post-condition on `into_byte_slice`, `b`'s size and
        // alignment are valid for `T`. By post-condition, `b.into_byte_slice()`
        // produces a byte slice with identical address and length to that
        // produced by `b.deref()`.
        let ptr = Ptr::from_ref(b.into_byte_slice())
            .try_cast_into_no_leftover::<T, BecauseImmutable>(None)
            .expect("zerocopy internal error: into_ref should be infallible");
        let ptr = ptr.bikeshed_recall_valid();
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
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn into_mut(self) -> &'a mut T {
        // Presumably unreachable, since we've guarded each constructor of `Ref`.
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `IntoByteSliceMut`.
        let b = unsafe { self.into_byte_slice_mut() };

        // PANICS: By post-condition on `into_byte_slice_mut`, `b`'s size and
        // alignment are valid for `T`. By post-condition,
        // `b.into_byte_slice_mut()` produces a byte slice with identical
        // address and length to that produced by `b.deref_mut()`.
        let ptr = Ptr::from_mut(b.into_byte_slice_mut())
            .try_cast_into_no_leftover::<T, BecauseExclusive>(None)
            .expect("zerocopy internal error: into_ref should be infallible");
        let ptr = ptr.bikeshed_recall_valid();
        ptr.as_mut()
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: ?Sized,
{
    /// Gets the underlying bytes.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSlice`.
        unsafe { self.as_byte_slice().deref() }
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSliceMut,
    T: ?Sized,
{
    /// Gets the underlying bytes mutably.
    #[inline]
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSliceMut`.
        unsafe { self.as_byte_slice_mut().deref_mut() }
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes,
{
    /// Reads a copy of `T`.
    #[must_use = "has no side effects"]
    #[inline]
    pub fn read(&self) -> T {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSlice`.
        let b = unsafe { self.as_byte_slice() };

        // SAFETY: By postcondition on `as_byte_slice`, we know that `b` is a
        // valid size and ailgnment for `T`. By safety invariant on `ByteSlice`,
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
    #[inline]
    pub fn write(&mut self, t: T) {
        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSliceMut`.
        let b = unsafe { self.as_byte_slice_mut() };

        // SAFETY: By postcondition on `as_byte_slice_mut`, we know that `b` is
        // a valid size and ailgnment for `T`. By safety invariant on
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
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSlice`.
        let b = unsafe { self.as_byte_slice() };

        // PANICS: By postcondition on `as_byte_slice`, `b`'s size and alignment
        // are valid for `T`, and by invariant on `ByteSlice`, these are
        // preserved through `.deref()`, so this `unwrap` will not panic.
        let ptr = Ptr::from_ref(b.deref())
            .try_cast_into_no_leftover::<T, BecauseImmutable>(None)
            .expect("zerocopy internal error: Deref::deref should be infallible");
        let ptr = ptr.bikeshed_recall_valid();
        ptr.as_ref()
    }
}

impl<B, T> DerefMut for Ref<B, T>
where
    B: ByteSliceMut,
    // TODO(#251): We can't remove `Immutable` here because it's required by
    // the impl of `Deref`, which is a super-trait of `DerefMut`. Maybe we can
    // add a separate inherent method for this?
    T: FromBytes + IntoBytes + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        static_assert_dst_is_not_zst!(T);

        // SAFETY: We don't call any methods on `b` other than those provided by
        // `ByteSliceMut`.
        let b = unsafe { self.as_byte_slice_mut() };

        // PANICS: By postcondition on `as_byte_slice_mut`, `b`'s size and
        // alignment are valid for `T`, and by invariant on `ByteSlice`, these
        // are preserved through `.deref_mut()`, so this `unwrap` will not
        // panic.
        let ptr = Ptr::from_mut(b.deref_mut())
            .try_cast_into_no_leftover::<T, BecauseExclusive>(None)
            .expect("zerocopy internal error: DerefMut::deref_mut should be infallible");
        let ptr = ptr.bikeshed_recall_valid();
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

#[cfg(test)]
#[allow(clippy::assertions_on_result_states)]
mod tests {
    use core::convert::TryInto as _;

    use super::*;
    use crate::util::testutil::*;

    #[test]
    fn test_mut_slice_into_ref() {
        // Prior to #1260/#1299, calling `into_ref` on a `&mut [u8]`-backed
        // `Ref` was not supportd.
        let mut buf = [0u8];
        let r = Ref::<&mut [u8], u8>::from_bytes(&mut buf).unwrap();
        assert_eq!(r.into_ref(), &0);
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
        assert_eq!(r.read(), AU64(0));

        // Assert that values written to the typed value are reflected in the
        // byte slice.
        const VAL1: AU64 = AU64(0xFF00FF00FF00FF00);
        *r = VAL1;
        assert_eq!(r.bytes(), &VAL1.to_bytes());
        *r = AU64(0);
        r.write(VAL1);
        assert_eq!(r.bytes(), &VAL1.to_bytes());

        // Assert that values written to the byte slice are reflected in the
        // typed value.
        const VAL2: AU64 = AU64(!VAL1.0); // different from `VAL1`
        r.bytes_mut().copy_from_slice(&VAL2.to_bytes()[..]);
        assert_eq!(*r, VAL2);
        assert_eq!(r.read(), VAL2);
    }

    // Verify that values written to a `Ref` are properly shared between the
    // typed and untyped representations; pass a value with `typed_len` `AU64`s
    // backed by an array of `typed_len * 8` bytes.
    fn test_new_helper_slice(mut r: Ref<&mut [u8], [AU64]>, typed_len: usize) {
        // Assert that the value starts out zeroed.
        assert_eq!(&*r, vec![AU64(0); typed_len].as_slice());

        // Check the backing storage is the exact same slice.
        let untyped_len = typed_len * 8;
        assert_eq!(r.bytes().len(), untyped_len);
        assert_eq!(r.bytes().as_ptr(), r.as_ptr().cast::<u8>());

        // Assert that values written to the typed value are reflected in the
        // byte slice.
        const VAL1: AU64 = AU64(0xFF00FF00FF00FF00);
        for typed in &mut *r {
            *typed = VAL1;
        }
        assert_eq!(r.bytes(), VAL1.0.to_ne_bytes().repeat(typed_len).as_slice());

        // Assert that values written to the byte slice are reflected in the
        // typed value.
        const VAL2: AU64 = AU64(!VAL1.0); // different from VAL1
        r.bytes_mut().copy_from_slice(&VAL2.0.to_ne_bytes().repeat(typed_len));
        assert!(r.iter().copied().all(|x| x == VAL2));
    }

    // Verify that values written to a `Ref` are properly shared between the
    // typed and untyped representations, that reads via `deref` and `read`
    // behave the same, and that writes via `deref_mut` and `write` behave the
    // same.
    fn test_new_helper_unaligned(mut r: Ref<&mut [u8], [u8; 8]>) {
        // assert that the value starts at 0
        assert_eq!(*r, [0; 8]);
        assert_eq!(r.read(), [0; 8]);

        // Assert that values written to the typed value are reflected in the
        // byte slice.
        const VAL1: [u8; 8] = [0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00];
        *r = VAL1;
        assert_eq!(r.bytes(), &VAL1);
        *r = [0; 8];
        r.write(VAL1);
        assert_eq!(r.bytes(), &VAL1);

        // Assert that values written to the byte slice are reflected in the
        // typed value.
        const VAL2: [u8; 8] = [0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF]; // different from VAL1
        r.bytes_mut().copy_from_slice(&VAL2[..]);
        assert_eq!(*r, VAL2);
        assert_eq!(r.read(), VAL2);
    }

    // Verify that values written to a `Ref` are properly shared between the
    // typed and untyped representations; pass a value with `len` `u8`s backed
    // by an array of `len` bytes.
    fn test_new_helper_slice_unaligned(mut r: Ref<&mut [u8], [u8]>, len: usize) {
        // Assert that the value starts out zeroed.
        assert_eq!(&*r, vec![0u8; len].as_slice());

        // Check the backing storage is the exact same slice.
        assert_eq!(r.bytes().len(), len);
        assert_eq!(r.bytes().as_ptr(), r.as_ptr());

        // Assert that values written to the typed value are reflected in the
        // byte slice.
        let mut expected_bytes = [0xFF, 0x00].iter().copied().cycle().take(len).collect::<Vec<_>>();
        r.copy_from_slice(&expected_bytes);
        assert_eq!(r.bytes(), expected_bytes.as_slice());

        // Assert that values written to the byte slice are reflected in the
        // typed value.
        for byte in &mut expected_bytes {
            *byte = !*byte; // different from `expected_len`
        }
        r.bytes_mut().copy_from_slice(&expected_bytes);
        assert_eq!(&*r, expected_bytes.as_slice());
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
    fn test_new_unaligned_sized() {
        // Test that an unaligned, properly-sized buffer works for
        // `new_unaligned`, `new_unaligned_from_prefix`, and
        // `new_unaligned_from_suffix`, and that `new_unaligned_from_prefix`
        // `new_unaligned_from_suffix` return empty slices. Test that an
        // unaligned buffer whose length is a multiple of the element size works
        // for `new_slice`.

        let mut buf = [0u8; 8];
        test_new_helper_unaligned(Ref::<_, [u8; 8]>::unaligned_from_bytes(&mut buf[..]).unwrap());
        {
            // In a block so that `r` and `suffix` don't live too long.
            buf = [0u8; 8];
            let (r, suffix) = Ref::<_, [u8; 8]>::unaligned_from_prefix(&mut buf[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper_unaligned(r);
        }
        {
            buf = [0u8; 8];
            let (prefix, r) = Ref::<_, [u8; 8]>::unaligned_from_suffix(&mut buf[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper_unaligned(r);
        }

        let mut buf = [0u8; 16];
        // `buf.t` should be aligned to 8 and have a length which is a multiple
        // of `size_of::AU64>()`, so this should always succeed.
        test_new_helper_slice_unaligned(
            Ref::<_, [u8]>::unaligned_from_bytes(&mut buf[..]).unwrap(),
            16,
        );

        buf = [0u8; 16];
        let r = Ref::<_, [u8]>::unaligned_from_bytes_with_elems(&mut buf[..], 16).unwrap();
        test_new_helper_slice_unaligned(r, 16);

        {
            buf = [0u8; 16];
            let (r, suffix) =
                Ref::<_, [u8]>::unaligned_from_prefix_with_elems(&mut buf[..], 8).unwrap();
            assert_eq!(suffix, [0; 8]);
            test_new_helper_slice_unaligned(r, 8);
        }
        {
            buf = [0u8; 16];
            let (prefix, r) =
                Ref::<_, [u8]>::unaligned_from_suffix_with_elems(&mut buf[..], 8).unwrap();
            assert_eq!(prefix, [0; 8]);
            test_new_helper_slice_unaligned(r, 8);
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
    fn test_new_unaligned_oversized() {
        // Test than an unaligned, overly-sized buffer works for
        // `new_unaligned_from_prefix` and `new_unaligned_from_suffix`, and that
        // they return the remainder and prefix of the slice respectively.

        let mut buf = [0u8; 16];
        {
            // In a block so that `r` and `suffix` don't live too long.
            let (r, suffix) = Ref::<_, [u8; 8]>::unaligned_from_prefix(&mut buf[..]).unwrap();
            assert_eq!(suffix.len(), 8);
            test_new_helper_unaligned(r);
        }
        {
            buf = [0u8; 16];
            let (prefix, r) = Ref::<_, [u8; 8]>::unaligned_from_suffix(&mut buf[..]).unwrap();
            assert_eq!(prefix.len(), 8);
            test_new_helper_unaligned(r);
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
        assert!(Ref::<_, [u8; 8]>::unaligned_from_bytes(&buf.t[..]).is_err());

        // Fail because the buffer is too small.

        // A buffer with an alignment of 8.
        let buf = Align::<[u8; 4], AU64>::default();
        // `buf.t` should be aligned to 8, so only the length check should fail.
        assert!(Ref::<_, AU64>::from_bytes(&buf.t[..]).is_err());
        assert!(Ref::<_, [u8; 8]>::unaligned_from_bytes(&buf.t[..]).is_err());
        assert!(Ref::<_, AU64>::from_prefix(&buf.t[..]).is_err());
        assert!(Ref::<_, AU64>::from_suffix(&buf.t[..]).is_err());
        assert!(Ref::<_, [u8; 8]>::unaligned_from_prefix(&buf.t[..]).is_err());
        assert!(Ref::<_, [u8; 8]>::unaligned_from_suffix(&buf.t[..]).is_err());

        // Fail because the length is not a multiple of the element size.

        let buf = Align::<[u8; 12], AU64>::default();
        // `buf.t` has length 12, but element size is 8.
        assert!(Ref::<_, [AU64]>::from_bytes(&buf.t[..]).is_err());
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_bytes(&buf.t[..]).is_err());

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
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_bytes_with_elems(&buf.t[..], n).is_err());
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_bytes_with_elems(&buf.t[..], 2).is_err());
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_prefix_with_elems(&buf.t[..], n).is_err());
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_prefix_with_elems(&buf.t[..], 2).is_err());
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_suffix_with_elems(&buf.t[..], n).is_err());
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_suffix_with_elems(&buf.t[..], 2).is_err());

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
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_prefix_with_elems(
            &buf.t[..],
            unreasonable_len
        )
        .is_err());
        assert!(Ref::<_, [[u8; 8]]>::unaligned_from_suffix_with_elems(
            &buf.t[..],
            unreasonable_len
        )
        .is_err());
    }

    #[test]
    #[allow(unstable_name_collisions)]
    #[allow(clippy::as_conversions)]
    fn test_into_ref_mut() {
        #[allow(unused)]
        use crate::util::AsAddress as _;

        let mut buf = Align::<[u8; 8], u64>::default();
        let r = Ref::<_, u64>::from_bytes(&buf.t[..]).unwrap();
        let rf = r.into_ref();
        assert_eq!(rf, &0u64);
        let buf_addr = (&buf.t as *const [u8; 8]).addr();
        assert_eq!((rf as *const u64).addr(), buf_addr);

        let r = Ref::<_, u64>::from_bytes(&mut buf.t[..]).unwrap();
        let rf = r.into_mut();
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
