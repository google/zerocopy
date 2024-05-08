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

    use crate::{ByteSlice, ByteSliceMut, IntoByteSlice, IntoByteSliceMut};

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
    ///         let (header, body) = Ref::new_unaligned_from_prefix(bytes).ok()?;
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
        // INVARIANTS: The referent (via `.deref`, `.deref_mut`, `.into`) byte slice
        // is aligned to `T`'s alignment and its size corresponds to a valid size
        // for `T`.
        //
        // TODO: Something about not calling other methods.
        B,
        PhantomData<T>,
    );

    impl<B, T: ?Sized> Ref<B, T> {
        /// TODO
        ///
        /// # Safety
        ///
        /// TODO
        pub(crate) unsafe fn new_unchecked(bytes: B) -> Ref<B, T> {
            // INVARIANTS: TODO
            Ref(bytes, PhantomData)
        }
    }

    impl<B: ByteSlice, T: ?Sized> Ref<B, T> {
        /// TODO
        ///
        /// # Safety
        ///
        /// TODO
        pub(crate) unsafe fn as_byte_slice(&self) -> &impl ByteSlice {
            &self.0
        }
    }

    impl<B: ByteSliceMut, T: ?Sized> Ref<B, T> {
        /// TODO
        ///
        /// # Safety
        ///
        /// TODO
        pub(crate) unsafe fn as_byte_slice_mut(&mut self) -> &mut impl ByteSliceMut {
            &mut self.0
        }
    }

    impl<'a, B: IntoByteSlice<'a>, T: ?Sized> Ref<B, T> {
        /// TODO
        ///
        /// # Safety
        ///
        /// TODO
        pub(crate) unsafe fn into_byte_slice(self) -> impl IntoByteSlice<'a> {
            self.0
        }
    }

    impl<'a, B: IntoByteSliceMut<'a>, T: ?Sized> Ref<B, T> {
        /// TODO
        ///
        /// # Safety
        ///
        /// TODO
        pub(crate) unsafe fn into_byte_slice_mut(self) -> impl IntoByteSliceMut<'a> {
            self.0
        }
    }
}

#[allow(unreachable_pub)] // This is a false positive on our MSRV toolchain.
pub use def::Ref;

// TODO: What to do about Copy + Clone?

// impl<B: ByteSlice + Clone, T: ?Sized> Clone for Ref<B, T> {
//     #[inline]
//     fn clone(&self) -> Ref<B, T> {
//         // INVARIANTS: By invariant on `self.0`, it is aligned to `T`'s
//         // alignment and its size corresponds to a valid size for `T`. By safety
//         // invariant on `ByteSlice`, these properties are preserved by `clone`.
//         Ref(self.0.clone(), PhantomData)
//     }
// }

// // INVARIANTS: By invariant on `Ref`'s `.0` field, it is aligned to `T`'s
// // alignment and its size corresponds to a valid size for `T`. By safety
// // invariant on `ByteSlice`, these properties are preserved by `Copy`.
// impl<B: ByteSlice + Copy, T: ?Sized> Copy for Ref<B, T> {}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
{
    #[must_use = "has no side effects"]
    pub(crate) fn new_sized(bytes: B) -> Result<Ref<B, T>, CastError<B, T>> {
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
    pub(crate) fn new_sized_from_prefix(bytes: B) -> Result<(Ref<B, T>, B), CastError<B, T>> {
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
    pub(crate) fn new_sized_from_suffix(bytes: B) -> Result<(B, Ref<B, T>), CastError<B, T>> {
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
        // INVARIANTS: Since `split_at` is defined as `bytes_len -
        // size_of::<T>()`, the `bytes` which results from `let (prefix, bytes)
        // = try_split_at(bytes, split_at)?` has length `size_of::<T>()`. After
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
    /// Constructs a new `Ref`.
    ///
    /// `new` verifies that `bytes.len() == size_of::<T>()` and that `bytes` is
    /// aligned to `align_of::<T>()`, and constructs a new `Ref`. If either of
    /// these checks fail, it returns `None`.
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
    /// let _ = Ref::<_, ZSTy>::new(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline]
    pub fn new(bytes: B) -> Result<Ref<B, T>, CastError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        if let Err(e) = Ptr::from_ref(bytes.deref()).try_cast_into_no_leftover::<T>() {
            return Err(e.with_src(()).with_src(bytes));
        }
        // SAFETY: `try_cast_into_no_leftover` validates size and alignment.
        Ok(unsafe { Ref::new_unchecked(bytes) })
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: KnownLayout + Immutable + ?Sized,
{
    /// Constructs a new `Ref` from the prefix of a byte slice.
    ///
    /// `new_from_prefix` verifies that `bytes.len() >= size_of::<T>()` and that
    /// `bytes` is aligned to `align_of::<T>()`. It consumes the first
    /// `size_of::<T>()` bytes from `bytes` to construct a `Ref`, and returns
    /// the remaining bytes to the caller. If either the length or alignment
    /// checks fail, it returns `None`.
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
    /// let _ = Ref::<_, ZSTy>::new_from_prefix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline]
    pub fn new_from_prefix(bytes: B) -> Result<(Ref<B, T>, B), CastError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        let remainder = match Ptr::from_ref(bytes.deref()).try_cast_into::<T>(CastType::Prefix) {
            Ok((_, remainder)) => remainder,
            Err(e) => {
                return Err(e.with_src(()).with_src(bytes));
            }
        };

        // SAFETY: `remainder` is constructed as a subset of `bytes`, and so it
        // cannot have a larger size than `bytes`. Both of their `len` methods
        // measure bytes (`bytes` deref's to `[u8]`, and `remainder` is a
        // `Ptr<[u8]>`), so `bytes.len() >= remainder.len()`. Thus, this cannot
        // underflow.
        #[allow(unstable_name_collisions, clippy::incompatible_msrv)]
        let split_at = unsafe { bytes.len().unchecked_sub(remainder.len()) };
        let (bytes, suffix) =
            try_split_at(bytes, split_at).map_err(|b| SizeError::new(b).into())?;
        // SAFETY: `try_cast_into` validates size and alignment, and returns a
        // `split_at` that indicates how many bytes of `bytes` correspond to a
        // valid `T`. By safety postcondition on `SplitByteSlice::try_split_at`
        // we can rely on `try_split_at` to produce the correct `bytes` and
        // `suffix`.
        let r = unsafe { Ref::new_unchecked(bytes) };
        Ok((r, suffix))
    }

    /// Constructs a new `Ref` from the suffix of a byte slice.
    ///
    /// `new_from_suffix` verifies that `bytes.len() >= size_of::<T>()` and that
    /// the last `size_of::<T>()` bytes of `bytes` are aligned to
    /// `align_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the preceding bytes to the
    /// caller. If either the length or alignment checks fail, it returns
    /// `None`.
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
    /// let _ = Ref::<_, ZSTy>::new_from_suffix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline]
    pub fn new_from_suffix(bytes: B) -> Result<(B, Ref<B, T>), CastError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        let remainder = match Ptr::from_ref(bytes.deref()).try_cast_into::<T>(CastType::Suffix) {
            Ok((_, remainder)) => remainder,
            Err(e) => {
                let e = e.with_src(());
                return Err(e.with_src(bytes));
            }
        };

        let split_at = remainder.len();
        let (prefix, bytes) =
            try_split_at(bytes, split_at).map_err(|b| SizeError::new(b).into())?;
        // SAFETY: `try_cast_into` validates size and alignment, and returns a
        // `try_split_at` that indicates how many bytes of `bytes` correspond to
        // a valid `T`. By safety postcondition on
        // `SplitByteSlice::try_split_at` we can rely on `try_split_at` to
        // produce the correct `prefix` and `bytes`.
        let r = unsafe { Ref::new_unchecked(bytes) };
        Ok((prefix, r))
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: KnownLayout<PointerMetadata = usize> + Immutable + ?Sized,
{
    // TODO(#29), TODO(#871): Pick a name and make this public. Make sure to
    // update references to this name in `#[deprecated]` attributes elsewhere.
    #[doc(hidden)]
    #[inline]
    pub fn with_trailing_elements_from_prefix(
        bytes: B,
        count: usize,
    ) -> Result<(Ref<B, T>, B), CastError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        let expected_len = match count.size_for_metadata(T::LAYOUT) {
            Some(len) => len,
            None => return Err(SizeError::new(bytes).into()),
        };
        if bytes.len() < expected_len {
            return Err(SizeError::new(bytes).into());
        }
        let (prefix, bytes) = bytes.split_at(expected_len);
        Self::new(prefix).map(move |l| (l, bytes))
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: KnownLayout<PointerMetadata = usize> + Immutable + ?Sized,
{
    // TODO(#29), TODO(#871): Pick a name and make this public. Make sure to
    // update references to this name in `#[deprecated]` attributes elsewhere.
    #[doc(hidden)]
    #[inline]
    pub fn with_trailing_elements_from_suffix(
        bytes: B,
        count: usize,
    ) -> Result<(B, Ref<B, T>), CastError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        let expected_len = match count.size_for_metadata(T::LAYOUT) {
            Some(len) => len,
            None => return Err(SizeError::new(bytes).into()),
        };
        let split_at = if let Some(split_at) = bytes.len().checked_sub(expected_len) {
            split_at
        } else {
            return Err(SizeError::new(bytes).into());
        };
        let (bytes, suffix) = bytes.split_at(split_at);
        Self::new(suffix).map(move |l| (bytes, l))
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: Unaligned + KnownLayout + Immutable + ?Sized,
{
    /// Constructs a new `Ref` for a type with no alignment requirement.
    ///
    /// `new_unaligned` verifies that `bytes.len() == size_of::<T>()` and
    /// constructs a new `Ref`. If the check fails, it returns `None`.
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
    /// let f = Ref::<&[u8], ZSTy>::new_unaligned(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn new_unaligned(bytes: B) -> Result<Ref<B, T>, SizeError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        match Ref::new(bytes) {
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
    /// Constructs a new `Ref` from the prefix of a byte slice for a type with
    /// no alignment requirement.
    ///
    /// `new_unaligned_from_prefix` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the first `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the remaining bytes to the
    /// caller. If the length check fails, it returns `None`.
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
    /// let _ = Ref::<_, ZSTy>::new_unaligned_from_prefix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn new_unaligned_from_prefix(bytes: B) -> Result<(Ref<B, T>, B), SizeError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        Ref::new_from_prefix(bytes).map_err(|e| match e {
            CastError::Size(e) => e,
            CastError::Alignment(_) => unreachable!(),
            CastError::Validity(i) => match i {},
        })
    }

    /// Constructs a new `Ref` from the suffix of a byte slice for a type with
    /// no alignment requirement.
    ///
    /// `new_unaligned_from_suffix` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the preceding bytes to the
    /// caller. If the length check fails, it returns `None`.
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
    /// let _ = Ref::<_, ZSTy>::new_unaligned_from_suffix(&b"UU"[..]); // ⚠ Compile Error!
    /// ```
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn new_unaligned_from_suffix(bytes: B) -> Result<(B, Ref<B, T>), SizeError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        Ref::new_from_suffix(bytes).map_err(|e| match e {
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
    // TODO(#29), TODO(#871): Pick a name and make this public. Make sure to
    // update references to this name in `#[deprecated]` attributes elsewhere.
    #[doc(hidden)]
    #[inline]
    pub fn with_trailing_elements_unaligned_from_prefix(
        bytes: B,
        count: usize,
    ) -> Result<(Ref<B, T>, B), CastError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        Self::with_trailing_elements_from_prefix(bytes, count)
    }
}

impl<B, T> Ref<B, T>
where
    B: SplitByteSlice,
    T: KnownLayout<PointerMetadata = usize> + Unaligned + Immutable + ?Sized,
{
    // TODO(#29), TODO(#871): Pick a name and make this public. Make sure to
    // update references to this name in `#[deprecated]` attributes elsewhere.
    #[doc(hidden)]
    #[inline]
    pub fn with_trailing_elements_unaligned_from_suffix(
        bytes: B,
        count: usize,
    ) -> Result<(B, Ref<B, T>), CastError<B, T>> {
        util::assert_dst_is_not_zst::<T>();
        Self::with_trailing_elements_from_suffix(bytes, count)
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
        util::assert_dst_is_not_zst::<T>();

        // SAFETY: TODO
        let b = unsafe { self.into_byte_slice() };

        // PANICS: By invariant on `Ref`, `self.0.deref()`'s size and alignment
        // are valid for `T`. By invariant on `IntoByteSlice`, `self.into()`
        // produces a byte slice with identical address and length to that
        // produced by `self.0.deref()`.
        let ptr = Ptr::from_ref(b.into())
            .try_cast_into_no_leftover::<T>()
            .expect("zerocopy internal error: into_ref should be infallible");
        let ptr = ptr.bikeshed_recall_valid();
        ptr.as_ref()
    }
}

impl<'a, B, T> Ref<B, T>
where
    B: 'a + IntoByteSliceMut<'a>,
    T: FromBytes + IntoBytes + KnownLayout + Immutable + ?Sized,
{
    /// Converts this `Ref` into a mutable reference.
    ///
    /// `into_mut` consumes the `Ref`, and returns a mutable reference to `T`.
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn into_mut(self) -> &'a mut T {
        // Presumably unreachable, since we've guarded each constructor of `Ref`.
        util::assert_dst_is_not_zst::<T>();

        // SAFETY: TODO
        let b = unsafe { self.into_byte_slice_mut() };

        // PANICS: By invariant on `Ref`, `self.0.deref_mut()`'s size and
        // alignment are valid for `T`. By invariant on `IntoByteSlice`,
        // `self.into()` produces a byte slice with identical address and length
        // to that produced by `self.0.deref_mut()`.
        let ptr = Ptr::from_mut(b.into())
            .try_cast_into_no_leftover::<T>()
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
        // SAFETY: TODO
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
        // SAFETY: TODO
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
        // SAFETY: TODO
        let b = unsafe { self.as_byte_slice() };

        // SAFETY: Because of the invariants on `Ref`, we know that `self.0` was
        // at least `size_of::<T>()` bytes long when it was validated, and that
        // it was at least as aligned as `align_of::<T>()`. Because of the
        // safety invariant on `ByteSlice`, we know that these must still hold
        // when we dereference here. Because `T: FromBytes`, it is sound to
        // interpret these bytes as a `T`.
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
        // SAFETY: TODO
        let b = unsafe { self.as_byte_slice_mut() };

        // SAFETY: Because of the invariants on `Ref`, we know that `self.0` was
        // at least `size_of::<T>()` bytes long when it was validated, and that
        // it was at least as aligned as `align_of::<T>()`. Because of the
        // safety invariant on `ByteSlice`, we know that these must still hold
        // when we dereference here. Writing `t` to the buffer will allow all of
        // the bytes of `t` to be accessed as a `[u8]`, but because `T:
        // IntoBytes`, we know that this is sound.
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
        util::assert_dst_is_not_zst::<T>();

        // SAFETY: TODO
        let b = unsafe { self.as_byte_slice() };

        // PANICS: By invariant on `Ref`, `self.0`'s size and alignment are
        // valid for `T`, and so this `unwrap` will not panic.
        let ptr = Ptr::from_ref(b.deref())
            .try_cast_into_no_leftover::<T>()
            .expect("zerocopy internal error: Deref::deref should be infallible");
        let ptr = ptr.bikeshed_recall_valid();
        ptr.as_ref()
    }
}

impl<B, T> DerefMut for Ref<B, T>
where
    B: ByteSliceMut,
    T: FromBytes + IntoBytes + KnownLayout + Immutable + ?Sized,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        util::assert_dst_is_not_zst::<T>();

        // SAFETY: TODO
        let b = unsafe { self.as_byte_slice_mut() };

        // PANICS: By invariant on `Ref`, `self.0`'s size and alignment are
        // valid for `T`, and so this `unwrap` will not panic.
        let ptr = Ptr::from_mut(b.deref_mut())
            .try_cast_into_no_leftover::<T>()
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
