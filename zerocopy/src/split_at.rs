// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2025 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use super::*;
use crate::pointer::invariant::{Aligned, Exclusive, Invariants, Shared, Valid};

/// Types that can be split in two.
///
/// This trait generalizes Rust's existing support for splitting slices to
/// support slices and slice-based dynamically-sized types ("slice DSTs").
///
/// # Implementation
///
/// **Do not implement this trait yourself!** Instead, use
/// [`#[derive(SplitAt)]`][derive]; e.g.:
///
/// ```
/// # use zerocopy_derive::{SplitAt, KnownLayout};
/// #[derive(SplitAt, KnownLayout)]
/// #[repr(C)]
/// struct MyStruct<T: ?Sized> {
/// # /*
///     ...,
/// # */
///     // `SplitAt` types must have at least one field.
///     field: T,
/// }
/// ```
///
/// This derive performs a sophisticated, compile-time safety analysis to
/// determine whether a type is `SplitAt`.
///
/// # Safety
///
/// This trait does not convey any safety guarantees to code outside this crate.
///
/// You must not rely on the `#[doc(hidden)]` internals of `SplitAt`. Future
/// releases of zerocopy may make backwards-breaking changes to these items,
/// including changes that only affect soundness, which may cause code which
/// uses those items to silently become unsound.
///
#[cfg_attr(feature = "derive", doc = "[derive]: zerocopy_derive::SplitAt")]
#[cfg_attr(
    not(feature = "derive"),
    doc = concat!("[derive]: https://docs.rs/zerocopy/", env!("CARGO_PKG_VERSION"), "/zerocopy/derive.SplitAt.html"),
)]
#[cfg_attr(
    not(no_zerocopy_diagnostic_on_unimplemented_1_78_0),
    diagnostic::on_unimplemented(note = "Consider adding `#[derive(SplitAt)]` to `{Self}`")
)]
// # Safety
//
// The trailing slice is well-aligned for its element type. `Self` is `[T]`, or
// a `repr(C)` or `repr(transparent)` slice DST.
pub unsafe trait SplitAt: KnownLayout<PointerMetadata = usize> {
    /// The element type of the trailing slice.
    type Elem;

    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Unsafely splits `self` in two.
    ///
    /// # Safety
    ///
    /// The caller promises that `l_len` is not greater than the length of
    /// `self`'s trailing slice.
    ///
    #[doc = codegen_section!(
        header = "h5",
        bench = "split_at_unchecked",
        format = "coco",
        arity = 2,
        [
            open
            @index 1
            @title "Unsized"
            @variant "dynamic_size"
        ],
        [
            @index 2
            @title "Dynamically Padded"
            @variant "dynamic_padding"
        ]
    )]
    #[inline]
    #[must_use]
    unsafe fn split_at_unchecked(&self, l_len: usize) -> Split<&Self> {
        // SAFETY: By precondition on the caller, `l_len <= self.len()`.
        unsafe { Split::<&Self>::new(self, l_len) }
    }

    /// Attempts to split `self` in two.
    ///
    /// Returns `None` if `l_len` is greater than the length of `self`'s
    /// trailing slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, Immutable)]
    /// #[repr(C)]
    /// struct Packet {
    ///     length: u8,
    ///     body: [u8],
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let bytes = &[4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::ref_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// // Attempt to split `packet` at `length`.
    /// let split = packet.split_at(packet.length as usize).unwrap();
    ///
    /// // Use the `Immutable` bound on `Packet` to prove that it's okay to
    /// // return concurrent references to `packet` and `rest`.
    /// let (packet, rest) = split.via_immutable();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4]);
    /// assert_eq!(rest, [5, 6, 7, 8, 9]);
    /// ```
    ///
    #[doc = codegen_section!(
        header = "h5",
        bench = "split_at",
        format = "coco",
        arity = 2,
        [
            open
            @index 1
            @title "Unsized"
            @variant "dynamic_size"
        ],
        [
            @index 2
            @title "Dynamically Padded"
            @variant "dynamic_padding"
        ]
    )]
    #[inline]
    #[must_use = "has no side effects"]
    fn split_at(&self, l_len: usize) -> Option<Split<&Self>> {
        MetadataOf::new_in_bounds(self, l_len).map(
            #[inline(always)]
            |l_len| {
                // SAFETY: We have ensured that `l_len <= self.len()` (by
                // post-condition on `MetadataOf::new_in_bounds`)
                unsafe { Split::new(self, l_len.get()) }
            },
        )
    }

    /// Unsafely splits `self` in two.
    ///
    /// # Safety
    ///
    /// The caller promises that `l_len` is not greater than the length of
    /// `self`'s trailing slice.
    ///
    #[doc = codegen_header!("h5", "split_at_mut_unchecked")]
    ///
    /// See [`SplitAt::split_at_unchecked`](#method.split_at_unchecked.codegen).
    #[inline]
    #[must_use]
    unsafe fn split_at_mut_unchecked(&mut self, l_len: usize) -> Split<&mut Self> {
        // SAFETY: By precondition on the caller, `l_len <= self.len()`.
        unsafe { Split::<&mut Self>::new(self, l_len) }
    }

    /// Attempts to split `self` in two.
    ///
    /// Returns `None` if `l_len` is greater than the length of `self`'s
    /// trailing slice, or if the given `l_len` would result in [the trailing
    /// padding](KnownLayout#slice-dst-layout) of the left portion overlapping
    /// the right portion.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, IntoBytes)]
    /// #[repr(C)]
    /// struct Packet<B: ?Sized> {
    ///     length: u8,
    ///     body: B,
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let mut bytes = &mut [4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::<[u8]>::mut_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// {
    ///     // Attempt to split `packet` at `length`.
    ///     let split = packet.split_at_mut(packet.length as usize).unwrap();
    ///
    ///     // Use the `IntoBytes` bound on `Packet` to prove that it's okay to
    ///     // return concurrent references to `packet` and `rest`.
    ///     let (packet, rest) = split.via_into_bytes();
    ///
    ///     assert_eq!(packet.length, 4);
    ///     assert_eq!(packet.body, [1, 2, 3, 4]);
    ///     assert_eq!(rest, [5, 6, 7, 8, 9]);
    ///
    ///     rest.fill(0);
    /// }
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 0, 0, 0, 0, 0]);
    /// ```
    ///
    #[doc = codegen_header!("h5", "split_at_mut")]
    ///
    /// See [`SplitAt::split_at`](#method.split_at.codegen).
    #[inline]
    fn split_at_mut(&mut self, l_len: usize) -> Option<Split<&mut Self>> {
        MetadataOf::new_in_bounds(self, l_len).map(
            #[inline(always)]
            |l_len| {
                // SAFETY: We have ensured that `l_len <= self.len()` (by
                // post-condition on `MetadataOf::new_in_bounds`)
                unsafe { Split::new(self, l_len.get()) }
            },
        )
    }
}

// SAFETY: `[T]`'s trailing slice is `[T]`, which is trivially aligned.
unsafe impl<T> SplitAt for [T] {
    type Elem = T;

    #[inline]
    #[allow(dead_code)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }
}

/// A `T` that has been split into two possibly-overlapping parts.
///
/// For some dynamically sized types, the padding that appears after the
/// trailing slice field [is a dynamic function of the trailing slice
/// length](KnownLayout#slice-dst-layout). If `T` is split at a length that
/// requires trailing padding, the trailing padding of the left part of the
/// split `T` will overlap the right part. If `T` is a mutable reference or
/// permits interior mutation, you must ensure that the left and right parts do
/// not overlap. You can do this at zero-cost using using
/// [`Self::via_immutable`], [`Self::via_into_bytes`], or
/// [`Self::via_unaligned`], or with a dynamic check by using
/// [`Self::via_runtime_check`].
#[derive(Debug)]
pub struct Split<T> {
    /// A pointer to the source slice DST.
    source: T,
    /// The length of the future left half of `source`.
    ///
    /// # Safety
    ///
    /// If `source` is a pointer to a slice DST, `l_len` is no greater than
    /// `source`'s length.
    l_len: usize,
}

impl<T> Split<T> {
    /// Produces a `Split` of `source` with `l_len`.
    ///
    /// # Safety
    ///
    /// `l_len` is no greater than `source`'s length.
    #[inline(always)]
    unsafe fn new(source: T, l_len: usize) -> Self {
        Self { source, l_len }
    }
}

impl<'a, T> Split<&'a T>
where
    T: ?Sized + SplitAt,
{
    #[inline(always)]
    fn into_ptr(self) -> Split<Ptr<'a, T, (Shared, Aligned, Valid)>> {
        let source = Ptr::from_ref(self.source);
        // SAFETY: `Ptr::from_ref(self.source)` points to exactly `self.source`
        // and thus maintains the invariants of `self` with respect to `l_len`.
        unsafe { Split::new(source, self.l_len) }
    }

    /// Produces the split parts of `self`, using [`Immutable`] to ensure that
    /// it is sound to have concurrent references to both parts.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, Immutable)]
    /// #[repr(C)]
    /// struct Packet {
    ///     length: u8,
    ///     body: [u8],
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let bytes = &[4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::ref_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// // Attempt to split `packet` at `length`.
    /// let split = packet.split_at(packet.length as usize).unwrap();
    ///
    /// // Use the `Immutable` bound on `Packet` to prove that it's okay to
    /// // return concurrent references to `packet` and `rest`.
    /// let (packet, rest) = split.via_immutable();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4]);
    /// assert_eq!(rest, [5, 6, 7, 8, 9]);
    /// ```
    ///
    #[doc = codegen_section!(
        header = "h5",
        bench = "split_via_immutable",
        format = "coco",
        arity = 2,
        [
            open
            @index 1
            @title "Unsized"
            @variant "dynamic_size"
        ],
        [
            @index 2
            @title "Dynamically Padded"
            @variant "dynamic_padding"
        ]
    )]
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn via_immutable(self) -> (&'a T, &'a [T::Elem])
    where
        T: Immutable,
    {
        let (l, r) = self.into_ptr().via_immutable();
        (l.as_ref(), r.as_ref())
    }

    /// Produces the split parts of `self`, using [`IntoBytes`] to ensure that
    /// it is sound to have concurrent references to both parts.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, Immutable, IntoBytes)]
    /// #[repr(C)]
    /// struct Packet<B: ?Sized> {
    ///     length: u8,
    ///     body: B,
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let bytes = &[4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::<[u8]>::ref_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// // Attempt to split `packet` at `length`.
    /// let split = packet.split_at(packet.length as usize).unwrap();
    ///
    /// // Use the `IntoBytes` bound on `Packet` to prove that it's okay to
    /// // return concurrent references to `packet` and `rest`.
    /// let (packet, rest) = split.via_into_bytes();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4]);
    /// assert_eq!(rest, [5, 6, 7, 8, 9]);
    /// ```
    ///
    #[doc = codegen_header!("h5", "split_via_into_bytes")]
    ///
    /// See [`Split::via_immutable`](#method.split_via_immutable.codegen).
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn via_into_bytes(self) -> (&'a T, &'a [T::Elem])
    where
        T: IntoBytes,
    {
        let (l, r) = self.into_ptr().via_into_bytes();
        (l.as_ref(), r.as_ref())
    }

    /// Produces the split parts of `self`, using [`Unaligned`] to ensure that
    /// it is sound to have concurrent references to both parts.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, Immutable, Unaligned)]
    /// #[repr(C)]
    /// struct Packet {
    ///     length: u8,
    ///     body: [u8],
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let bytes = &[4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::ref_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// // Attempt to split `packet` at `length`.
    /// let split = packet.split_at(packet.length as usize).unwrap();
    ///
    /// // Use the `Unaligned` bound on `Packet` to prove that it's okay to
    /// // return concurrent references to `packet` and `rest`.
    /// let (packet, rest) = split.via_unaligned();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4]);
    /// assert_eq!(rest, [5, 6, 7, 8, 9]);
    /// ```
    ///
    #[doc = codegen_header!("h5", "split_via_unaligned")]
    ///
    /// See [`Split::via_immutable`](#method.split_via_immutable.codegen).
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn via_unaligned(self) -> (&'a T, &'a [T::Elem])
    where
        T: Unaligned,
    {
        let (l, r) = self.into_ptr().via_unaligned();
        (l.as_ref(), r.as_ref())
    }

    /// Produces the split parts of `self`, using a dynamic check to ensure that
    /// it is sound to have concurrent references to both parts. You should
    /// prefer using [`Self::via_immutable`], [`Self::via_into_bytes`], or
    /// [`Self::via_unaligned`], which have no runtime cost.
    ///
    /// Note that this check is overly conservative if `T` is [`Immutable`]; for
    /// some types, this check will reject some splits which
    /// [`Self::via_immutable`] will accept.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes, IntoBytes, network_endian::U16};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, Immutable, Debug)]
    /// #[repr(C, align(2))]
    /// struct Packet {
    ///     length: U16,
    ///     body: [u8],
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let bytes = [
    ///     4u16.to_be(),
    ///     1u16.to_be(),
    ///     2u16.to_be(),
    ///     3u16.to_be(),
    ///     4u16.to_be()
    /// ];
    ///
    /// let packet = Packet::ref_from_bytes(bytes.as_bytes()).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [0, 1, 0, 2, 0, 3, 0, 4]);
    ///
    /// // Attempt to split `packet` at `length`.
    /// let split = packet.split_at(packet.length.into()).unwrap();
    ///
    /// // Use a dynamic check to prove that it's okay to return concurrent
    /// // references to `packet` and `rest`.
    /// let (packet, rest) = split.via_runtime_check().unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [0, 1, 0, 2]);
    /// assert_eq!(rest, [0, 3, 0, 4]);
    ///
    /// // Attempt to split `packet` at `length - 1`.
    /// let idx = packet.length.get() - 1;
    /// let split = packet.split_at(idx as usize).unwrap();
    ///
    /// // Attempt (and fail) to use a dynamic check to prove that it's okay
    /// // to return concurrent references to `packet` and `rest`. Note that
    /// // this is a case of `via_runtime_check` being overly conservative.
    /// // Although the left and right parts indeed overlap, the `Immutable`
    /// // bound ensures that concurrently referencing these overlapping
    /// // parts is sound.
    /// assert!(split.via_runtime_check().is_err());
    /// ```
    ///
    #[doc = codegen_section!(
        header = "h5",
        bench = "split_via_runtime_check",
        format = "coco",
        arity = 2,
        [
            open
            @index 1
            @title "Unsized"
            @variant "dynamic_size"
        ],
        [
            @index 2
            @title "Dynamically Padded"
            @variant "dynamic_padding"
        ]
    )]
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn via_runtime_check(self) -> Result<(&'a T, &'a [T::Elem]), Self> {
        match self.into_ptr().via_runtime_check() {
            Ok((l, r)) => Ok((l.as_ref(), r.as_ref())),
            Err(s) => Err(s.into_ref()),
        }
    }

    /// Unsafely produces the split parts of `self`.
    ///
    /// # Safety
    ///
    /// If `T` permits interior mutation, the trailing padding bytes of the left
    /// portion must not overlap the right portion. For some dynamically sized
    /// types, the padding that appears after the trailing slice field [is a
    /// dynamic function of the trailing slice
    /// length](KnownLayout#slice-dst-layout). Thus, for some types, this
    /// condition is dependent on the length of the left portion.
    ///
    #[doc = codegen_section!(
        header = "h5",
        bench = "split_via_unchecked",
        format = "coco",
        arity = 2,
        [
            open
            @index 1
            @title "Unsized"
            @variant "dynamic_size"
        ],
        [
            @index 2
            @title "Dynamically Padded"
            @variant "dynamic_padding"
        ]
    )]
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub unsafe fn via_unchecked(self) -> (&'a T, &'a [T::Elem]) {
        // SAFETY: The aliasing of `self.into_ptr()` is not `Exclusive`, but the
        // caller has promised that if `T` permits interior mutation then the
        // left and right portions of `self` split at `l_len` do not overlap.
        let (l, r) = unsafe { self.into_ptr().via_unchecked() };
        (l.as_ref(), r.as_ref())
    }
}

impl<'a, T> Split<&'a mut T>
where
    T: ?Sized + SplitAt,
{
    #[inline(always)]
    fn into_ptr(self) -> Split<Ptr<'a, T, (Exclusive, Aligned, Valid)>> {
        let source = Ptr::from_mut(self.source);
        // SAFETY: `Ptr::from_mut(self.source)` points to exactly `self.source`,
        // and thus maintains the invariants of `self` with respect to `l_len`.
        unsafe { Split::new(source, self.l_len) }
    }

    /// Produces the split parts of `self`, using [`IntoBytes`] to ensure that
    /// it is sound to have concurrent references to both parts.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, IntoBytes)]
    /// #[repr(C)]
    /// struct Packet<B: ?Sized> {
    ///     length: u8,
    ///     body: B,
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let mut bytes = &mut [4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::<[u8]>::mut_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// {
    ///     // Attempt to split `packet` at `length`.
    ///     let split = packet.split_at_mut(packet.length as usize).unwrap();
    ///
    ///     // Use the `IntoBytes` bound on `Packet` to prove that it's okay to
    ///     // return concurrent references to `packet` and `rest`.
    ///     let (packet, rest) = split.via_into_bytes();
    ///
    ///     assert_eq!(packet.length, 4);
    ///     assert_eq!(packet.body, [1, 2, 3, 4]);
    ///     assert_eq!(rest, [5, 6, 7, 8, 9]);
    ///
    ///     rest.fill(0);
    /// }
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 0, 0, 0, 0, 0]);
    /// ```
    ///
    /// # Code Generation
    ///
    /// See [`Split::via_immutable`](#method.split_via_immutable.codegen).
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn via_into_bytes(self) -> (&'a mut T, &'a mut [T::Elem])
    where
        T: IntoBytes,
    {
        let (l, r) = self.into_ptr().via_into_bytes();
        (l.as_mut(), r.as_mut())
    }

    /// Produces the split parts of `self`, using [`Unaligned`] to ensure that
    /// it is sound to have concurrent references to both parts.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, IntoBytes, Unaligned)]
    /// #[repr(C)]
    /// struct Packet<B: ?Sized> {
    ///     length: u8,
    ///     body: B,
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let mut bytes = &mut [4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::<[u8]>::mut_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// {
    ///     // Attempt to split `packet` at `length`.
    ///     let split = packet.split_at_mut(packet.length as usize).unwrap();
    ///
    ///     // Use the `Unaligned` bound on `Packet` to prove that it's okay to
    ///     // return concurrent references to `packet` and `rest`.
    ///     let (packet, rest) = split.via_unaligned();
    ///
    ///     assert_eq!(packet.length, 4);
    ///     assert_eq!(packet.body, [1, 2, 3, 4]);
    ///     assert_eq!(rest, [5, 6, 7, 8, 9]);
    ///
    ///     rest.fill(0);
    /// }
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 0, 0, 0, 0, 0]);
    /// ```
    ///
    /// # Code Generation
    ///
    /// See [`Split::via_immutable`](#method.split_via_immutable.codegen).
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn via_unaligned(self) -> (&'a mut T, &'a mut [T::Elem])
    where
        T: Unaligned,
    {
        let (l, r) = self.into_ptr().via_unaligned();
        (l.as_mut(), r.as_mut())
    }

    /// Produces the split parts of `self`, using a dynamic check to ensure that
    /// it is sound to have concurrent references to both parts. You should
    /// prefer using [`Self::via_into_bytes`] or [`Self::via_unaligned`], which
    /// have no runtime cost.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, IntoBytes, Debug)]
    /// #[repr(C)]
    /// struct Packet<B: ?Sized> {
    ///     length: u8,
    ///     body: B,
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let mut bytes = &mut [4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::<[u8]>::mut_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// {
    ///     // Attempt to split `packet` at `length`.
    ///     let split = packet.split_at_mut(packet.length as usize).unwrap();
    ///
    ///     // Use a dynamic check to prove that it's okay to return concurrent
    ///     // references to `packet` and `rest`.
    ///     let (packet, rest) = split.via_runtime_check().unwrap();
    ///
    ///     assert_eq!(packet.length, 4);
    ///     assert_eq!(packet.body, [1, 2, 3, 4]);
    ///     assert_eq!(rest, [5, 6, 7, 8, 9]);
    ///
    ///     rest.fill(0);
    /// }
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 0, 0, 0, 0, 0]);
    /// ```
    ///
    /// # Code Generation
    ///
    /// See [`Split::via_runtime_check`](#method.split_via_runtime_check.codegen).
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub fn via_runtime_check(self) -> Result<(&'a mut T, &'a mut [T::Elem]), Self> {
        match self.into_ptr().via_runtime_check() {
            Ok((l, r)) => Ok((l.as_mut(), r.as_mut())),
            Err(s) => Err(s.into_mut()),
        }
    }

    /// Unsafely produces the split parts of `self`.
    ///
    /// # Safety
    ///
    /// The trailing padding bytes of the left portion must not overlap the
    /// right portion. For some dynamically sized types, the padding that
    /// appears after the trailing slice field [is a dynamic function of the
    /// trailing slice length](KnownLayout#slice-dst-layout). Thus, for some
    /// types, this condition is dependent on the length of the left portion.
    ///
    /// # Code Generation
    ///
    /// See [`Split::via_unchecked`](#method.split_via_unchecked.codegen).
    #[must_use = "has no side effects"]
    #[inline(always)]
    pub unsafe fn via_unchecked(self) -> (&'a mut T, &'a mut [T::Elem]) {
        // SAFETY: The aliasing of `self.into_ptr()` is `Exclusive`, and the
        // caller has promised that the left and right portions of `self` split
        // at `l_len` do not overlap.
        let (l, r) = unsafe { self.into_ptr().via_unchecked() };
        (l.as_mut(), r.as_mut())
    }
}

impl<'a, T, I> Split<Ptr<'a, T, I>>
where
    T: ?Sized + SplitAt,
    I: Invariants<Alignment = Aligned, Validity = Valid>,
{
    fn into_ref(self) -> Split<&'a T>
    where
        I: Invariants<Aliasing = Shared>,
    {
        // SAFETY: `self.source.as_ref()` points to exactly the same referent as
        // `self.source` and thus maintains the invariants of `self` with
        // respect to `l_len`.
        unsafe { Split::new(self.source.as_ref(), self.l_len) }
    }

    fn into_mut(self) -> Split<&'a mut T>
    where
        I: Invariants<Aliasing = Exclusive>,
    {
        // SAFETY: `self.source.as_mut()` points to exactly the same referent as
        // `self.source` and thus maintains the invariants of `self` with
        // respect to `l_len`.
        unsafe { Split::new(self.source.unify_invariants().as_mut(), self.l_len) }
    }

    /// Produces the length of `self`'s left part.
    #[inline(always)]
    fn l_len(&self) -> MetadataOf<T> {
        // SAFETY: By invariant on `Split`, `self.l_len` is not greater than the
        // length of `self.source`.
        unsafe { MetadataOf::<T>::new_unchecked(self.l_len) }
    }

    /// Produces the split parts of `self`, using [`Immutable`] to ensure that
    /// it is sound to have concurrent references to both parts.
    #[inline(always)]
    fn via_immutable(self) -> (Ptr<'a, T, I>, Ptr<'a, [T::Elem], I>)
    where
        T: Immutable,
        I: Invariants<Aliasing = Shared>,
    {
        // SAFETY: `Aliasing = Shared` and `T: Immutable`.
        unsafe { self.via_unchecked() }
    }

    /// Produces the split parts of `self`, using [`IntoBytes`] to ensure that
    /// it is sound to have concurrent references to both parts.
    #[inline(always)]
    fn via_into_bytes(self) -> (Ptr<'a, T, I>, Ptr<'a, [T::Elem], I>)
    where
        T: IntoBytes,
    {
        // SAFETY: By `T: IntoBytes`, `T` has no padding for any length.
        // Consequently, `T` can be split into non-overlapping parts at any
        // index.
        unsafe { self.via_unchecked() }
    }

    /// Produces the split parts of `self`, using [`Unaligned`] to ensure that
    /// it is sound to have concurrent references to both parts.
    #[inline(always)]
    fn via_unaligned(self) -> (Ptr<'a, T, I>, Ptr<'a, [T::Elem], I>)
    where
        T: Unaligned,
    {
        // SAFETY: By `T: SplitAt + Unaligned`, `T` is either a slice or a
        // `repr(C)` or `repr(transparent)` slice DST that is well-aligned at
        // any address and length. If `T` is a slice DST with alignment 1,
        // `repr(C)` or `repr(transparent)` ensures that no padding is placed
        // after the final element of the trailing slice. Consequently, `T` can
        // be split into strictly non-overlapping parts any any index.
        unsafe { self.via_unchecked() }
    }

    /// Produces the split parts of `self`, using a dynamic check to ensure that
    /// it is sound to have concurrent references to both parts. You should
    /// prefer using [`Self::via_immutable`], [`Self::via_into_bytes`], or
    /// [`Self::via_unaligned`], which have no runtime cost.
    #[inline(always)]
    fn via_runtime_check(self) -> Result<(Ptr<'a, T, I>, Ptr<'a, [T::Elem], I>), Self> {
        let l_len = self.l_len();
        // FIXME(#1290): Once we require `KnownLayout` on all fields, add an
        // `IS_IMMUTABLE` associated const, and add `T::IS_IMMUTABLE ||` to the
        // below check.
        if l_len.padding_needed_for() == 0 {
            // SAFETY: By `T: SplitAt`, `T` is either `[T]`, or a `repr(C)` or
            // `repr(transparent)` slice DST, for which the trailing padding
            // needed to accommodate `l_len` trailing elements is
            // `l_len.padding_needed_for()`. If no trailing padding is required,
            // the left and right parts are strictly non-overlapping.
            Ok(unsafe { self.via_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Unsafely produces the split parts of `self`.
    ///
    /// # Safety
    ///
    /// The caller promises that if `I::Aliasing` is [`Exclusive`] or `T`
    /// permits interior mutation, then `l_len.padding_needed_for() == 0`.
    #[inline(always)]
    unsafe fn via_unchecked(self) -> (Ptr<'a, T, I>, Ptr<'a, [T::Elem], I>) {
        let l_len = self.l_len();
        let inner = self.source.as_inner();

        // SAFETY: By invariant on `Self::l_len`, `l_len` is not greater than
        // the length of `inner`'s trailing slice.
        let (left, right) = unsafe { inner.split_at_unchecked(l_len) };

        // Lemma 0: `left` and `right` conform to the aliasing invariant
        // `I::Aliasing`. Proof: If `I::Aliasing` is `Exclusive` or `T` permits
        // interior mutation, the caller promises that `l_len.padding_needed_for()
        // == 0`. Consequently, by post-condition on `PtrInner::split_at_unchecked`,
        // there is no trailing padding after `left`'s final element that would
        // overlap into `right`. If `I::Aliasing` is shared and `T` forbids interior
        // mutation, then overlap between their referents is permissible.

        // SAFETY:
        // 0. `left` conforms to the aliasing invariant of `I::Aliasing`, by Lemma 0.
        // 1. `left` conforms to the alignment invariant of `I::Alignment, because
        //    the referents of `left` and `Self` have the same address and type
        //    (and, thus, alignment requirement).
        // 2. `left` conforms to the validity invariant of `I::Validity`, neither
        //    the type nor bytes of `left`'s referent have been changed.
        let left = unsafe { Ptr::from_inner(left) };

        // SAFETY:
        // 0. `right` conforms to the aliasing invariant of `I::Aliasing`, by Lemma
        //    0.
        // 1. `right` conforms to the alignment invariant of `I::Alignment, because
        //    if `ptr` with `I::Alignment = Aligned`, then by invariant on `T:
        //    SplitAt`, the trailing slice of `ptr` (from which `right` is derived)
        //    will also be well-aligned.
        // 2. `right` conforms to the validity invariant of `I::Validity`,
        //    because `right: [T::Elem]` is derived from the trailing slice of
        //    `ptr`, which, by contract on `T: SplitAt::Elem`, has type
        //    `[T::Elem]`. The `left` part cannot be used to invalidate `right`,
        //    because the caller promises that if `I::Aliasing` is `Exclusive`
        //    or `T` permits interior mutation, then `l_len.padding_needed_for()
        //    == 0` and thus the parts will be non-overlapping.
        let right = unsafe { Ptr::from_inner(right) };

        (left, right)
    }
}

#[cfg(kani)]
mod proofs {
    use super::*;

    // Configuration: Uses the common Kani CI configuration documented in
    // `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
    // x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
    // `-Zfunction-contracts`, and one layout selected by `--randomize-layout`
    // per invocation.
    //
    // Domain: Each harness considers every initialized `[u32; 8]`, every
    // source length in `0..=8`, and every split point in
    // `0..=source.len()`. The mutable consumer additionally considers every
    // pair of `u32` values written through its left and right results. Separate
    // harnesses cover shared and mutable slices. The two calls to
    // `assume_usize_at_most` in `any_slice_split_case` express exactly the
    // finite length bounds: they pass independently evaluated Rust `usize`
    // ordering results to Kani's assumption primitive as documented below;
    // neither mutation value is constrained. The common covers witness empty,
    // full, leading, trailing, and interior partitions. The two
    // mutable-consumer covers use `partition_first_value_oracle` to separately
    // witness a nonempty left or right partition whose first value changes;
    // covers establish reachability only and do not narrow the universal
    // mutation domain.
    //
    // Proof decomposition:
    // - The two `split_at_*_unchecked` harnesses call only the descriptor
    //   producer under proof. They inspect the private `Split` fields and
    //   establish that, at the post-call observation point, `source` has the
    //   input slice's pre-call contents, length, and modeled start address and
    //   that `l_len` equals the requested split point.
    //   Those expected fields are explicitly a zerocopy representation-policy
    //   oracle, not Rust-level evidence: the local `Split` definition documents
    //   `source` as the source slice-DST pointer and `l_len` as the future left
    //   length, with `l_len <= source.len()`, while `Split::new` says it produces
    //   a `Split` of the supplied `source` with the supplied `l_len`. Direct
    //   field-pattern observation bypasses every descriptor consumer. The
    //   shared producer compares against an independent pre-call array snapshot;
    //   the mutable producer additionally checks that the complete backing
    //   array's final value is unchanged. These are explicit zerocopy final-state
    //   behavior policies for the descriptor-construction operations, grounded
    //   in their documented role of packaging the supplied source and length;
    //   no safe Rust operation independently requires a zerocopy producer to
    //   have any particular post-call element values outside, or even inside,
    //   the logical source slice. The post-call observations cannot detect a
    //   transient write restored before the assertion, so they do not establish
    //   absence of writes.
    // - The two `via_unchecked` harnesses construct a known-good `Split`
    //   literal without calling either descriptor producer. They establish
    //   exact returned lengths and contents for every partition; start
    //   addresses for nonempty partitions; contiguity when both partitions are
    //   nonempty; and the source endpoint via whichever terminal partition is
    //   nonempty. The mutable harness also establishes writes through both
    //   results and the frame condition for the entire backing array. No
    //   address is asserted for an empty returned partition.
    // Thus no harness can pass because of compensating producer and consumer
    // defects.
    //
    // Allocation, source-level size, and loop bounds: The shared descriptor and
    // mutable descriptor harnesses each use two fixed `[u32; 8]` stack arrays,
    // the shared consumer uses one, and the mutable consumer uses three. No
    // harness requests dynamic allocation. Every slice passed to a target,
    // oracle, fill, or elementwise observation has length at most 8. On the
    // pinned target, each array is 32 bytes, the case producer's
    // `([u32; 8], usize, usize)` value is 48 bytes, and `PartitionOracle` is 64
    // bytes. Thus `PartitionOracle`, not a backing array, is the largest
    // explicitly named fixed-size Rust value in these harnesses. Every harness
    // calls `assert_fixed_storage_sizes`, which uses
    // `size_of` ("Returns the size of a type in bytes" [13]) to fail closed if
    // any of those three concrete sizes differs. All size and length equality
    // assertions below use the factored `assert_same_usize`: `assert_eq!`
    // compares through `PartialEq`, and `usize::PartialEq` tests the two values
    // for equality [14]. That helper supplies only equality mechanics; each
    // caller separately supplies a compiler fact, std oracle, or explicit
    // zerocopy policy expectation. This is a source-level bound, not a claim
    // about compiler-generated temporaries or stack-frame layout.
    // Separately, each harness sets the conservative bound `unwind(33)`. That
    // bound is not derived from the storage size, and the proof does not assume
    // how the compiler or Kani lowers these operations: successful unwinding
    // assertions establish that 33 is sufficient for every loop reachable in
    // this exact modeled configuration. They do not establish that 33 is the
    // exact or minimum sufficient bound.
    //
    // Oracle: Rust 1.93 identifies `usize` as an unsigned integer type, and its
    // `PartialOrd::{lt, le, gt}` implementations test less than, less than or
    // equal to, and greater than and are used by the corresponding `<`, `<=`,
    // and `>` operators [16]. `assume_usize_at_most` first evaluates `<=` to a
    // `bool`, then passes the result to `kani::assume`.
    // Kani 0.67 documents that this makes the assumption valid on subsequent
    // paths and successfully exits paths on which it is false [17]. Thus the
    // first call retains exactly `source_len` in `0..=CAPACITY`; the second
    // retains exactly `split` in `0..=source_len`. This is independent of the
    // zerocopy target, but remains conditional on Kani's translation of its
    // assumption primitive as part of the documented tool boundary.
    // These assumptions define the modeled proof domain; the inequalities are
    // premises, not assertions independently proved by the harness. An
    // impossible conjunction could make every later assertion vacuous. The
    // fail-closed cover protocol in `agent_docs/validation.md` separately
    // requires each emitted cover-class property to be `SATISFIED`; those
    // properties witness only the stated reachability cases.
    //
    // Source-prefix bridge: Every target source is constructed from the
    // complete `[u32; CAPACITY]` with `&values[..source_len]` or its mutable
    // counterpart. Rust 1.93 specifies that `..source_len` is a `RangeTo` and,
    // when used as a slicing index, produces the slice of all array elements
    // before `source_len`; its `SliceIndex<[T]>` implementation has output
    // `[T]` and documents an out-of-bounds end as the panic condition [19]. The
    // first domain assumption establishes `source_len <= CAPACITY`, so these
    // constructions select exactly the first `source_len` elements. Since
    // `slice::len` reports a slice's element count [14], each constructed
    // source has `source.len() == source_len`. The second domain assumption
    // therefore entails the unchecked-call precondition
    // `split <= source.len()`. This safe language/library bridge calls no
    // zerocopy target; it trusts the cited Rust contract and Kani's model of the
    // slicing operation.
    //
    // Safe Rust 1.93 `slice::split_at` and `slice::split_at_mut` are independent
    // of zerocopy and supply the expected partitions [1][2]:
    //
    //     Divides one slice into two at an index.
    //
    //     Divides one mutable slice into two at an index.
    //
    // Both contracts continue:
    //
    //     The first will contain all indices from `[0, mid)` (excluding the
    //     index `mid` itself) and the second will contain all indices from
    //     `[mid, len)` (excluding the index `len` itself).
    //
    // `slice::as_ptr` and `slice::as_ptr_range` independently supply address
    // observations [3][4]:
    //
    //     Returns a raw pointer to the slice’s buffer.
    //
    //     Returns the two raw pointers spanning the slice.
    //
    // The latter contract continues:
    //
    //     The returned range is half-open, which means that the end pointer
    //     points one past the last element of the slice.
    //
    // Every pointer assertion is factored through `core::ptr::eq`, whose Rust
    // 1.93 contract says [10]:
    //
    //     Compares raw pointers for equality.
    //
    // The Rust Reference specifies that raw pointers are compared by their
    // address rather than their pointed-to value [11]. All pointers compared
    // here are thin `*const u32` pointers, so no wide-pointer metadata is
    // involved. Safe `slice::len` determines whether each std-oracle partition
    // is nonempty. Each target length is checked against that oracle before its
    // own `len() != 0` gate, so a target defect cannot suppress an applicable
    // address assertion by reporting an empty partition. The `Option` fields
    // record only that applicability: `assert_present_u32_address`
    // pattern-matches the gate and fails on `None`, rather than using `Option`
    // equality. Both address helpers call only this safe `core` operation and
    // no zerocopy target. Pointer comparison ignores provenance [12], so these
    // assertions establish only equality of Kani's modeled addresses. They do
    // not prove allocation identity, compatible provenance, dereferenceability,
    // aliasing, or reference validity.
    //
    // Safe `slice::fill` supplies the write oracle [5]:
    //
    //     Fills `self` with elements by cloning `value`.
    //
    // For primitive `u32`, the versioned `Clone` implementation returns
    // `*self`, and `u32` implements `Copy`; each cloned fill element is
    // therefore exactly the independently generated symbolic input rather
    // than a second zerocopy policy premise [15].
    //
    // The mutation covers classify first-element changes through
    // `partition_first_value_oracle`, not direct array indexing. The helper
    // explicitly coerces the complete array to a slice [9], calls
    // `split_at(source_len)`, then calls `split_at(split)` on that prefix [1].
    // `source_len <= CAPACITY` makes the first split nonpanicking, and
    // `split <= source_len` does the same for the second. Under the stricter
    // cover gates, `split > 0` makes the left `[0, split)` partition nonempty,
    // while `split < source_len` makes the right `[split, source_len)` partition
    // nonempty. Safe `slice::first` returns that partition's first element or
    // `None` exactly when it is empty, and `Option::copied` copies the observed
    // `u32` value [18]. `observed_first_value_changes` then uses
    // `Option::is_some_and`, whose documented contract requires both a `Some`
    // value and a true predicate; primitive `u32`'s `PartialEq::ne`
    // implementation supplies the `original != replacement` predicate
    // [8][18]. Thus the helper returns true exactly when the safe slice
    // observation is present and differs from the independently generated
    // replacement. The helpers and gates ground the two cover classifications
    // in safe Rust observations; as with all covers here, they establish
    // reachability only.
    //
    // Contents and the whole-array frame use `assert_same_u32_elements`, not
    // slice or array `PartialEq`. Safe `slice::iter` returns an iterator which
    // “yields all items from start to end” [6]; `Iterator::copied` “copies all
    // of its elements,” and `Iterator::eq` determines whether one iterator's
    // elements equal another's [7]. `u32::eq` tests two `u32` values for
    // equality [8]. The helper obtains each element count through `slice::len`
    // and compares those counts through `assert_same_usize` [14], so these
    // rules establish the same ordered `u32` values. Whole arrays reach the
    // helper through the Reference's `[T; n]` to `[T]` unsizing coercion [9].
    // These safe operations do not call zerocopy and are independent value
    // oracles; they establish neither allocation identity nor aliasing or
    // provenance.
    //
    // The shared descriptor harness copies its complete array before calling
    // the target. Arrays implement `Copy` when their element type does, and
    // `u32` implements `Copy` [15][20], so `let original = values` creates an
    // independent pre-call value rather than an alias. Both descriptor
    // harnesses also capture `source.as_ptr()` from the exact input slice
    // descriptor before the target call. The resulting content and address
    // assertions therefore cannot let a target-induced source mutation or
    // descriptor change redefine its own expected value. They still remain
    // conditional on Kani's incomplete aliasing and reference-validity model
    // stated below.
    //
    // No cited address contract selects a unique buffer address for an empty
    // returned slice. `partition_oracle` therefore records expected pointers
    // only for nonempty partitions, and `assert_partitions` gates every returned
    // pointer assertion accordingly. Empty cases still establish exact lengths
    // and contents.
    //
    // [1] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at
    // [2] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at_mut
    // [3] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr
    // [4] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr_range
    // [5] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.fill
    // [6] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
    // [7] https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.copied
    // and https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.eq
    // [8] https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#impl-PartialEq-for-u32
    // [9] https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#unsized-coercions
    // [10] https://doc.rust-lang.org/1.93.0/std/ptr/fn.eq.html
    // [11] https://doc.rust-lang.org/1.93.0/reference/types/pointer.html#r-type.pointer.raw.cmp
    // [12] https://doc.rust-lang.org/1.93.0/std/ptr/index.html#provenance
    // [13] https://doc.rust-lang.org/1.93.0/std/mem/fn.size_of.html
    // [14] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.len
    // https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
    // [15] https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#impl-Clone-for-u32
    // https://doc.rust-lang.org/1.93.0/std/primitive.u32.html#impl-Copy-for-u32
    // [16] https://doc.rust-lang.org/1.93.0/std/primitive.usize.html
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialOrd-for-usize
    // [17] https://model-checking.github.io/kani/crates/doc/kani/fn.assume.html
    // [18] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.first
    // https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.copied
    // https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.is_some_and
    // [19] https://doc.rust-lang.org/1.93.0/std/ops/struct.RangeTo.html
    // https://doc.rust-lang.org/1.93.0/std/ops/struct.RangeTo.html#impl-SliceIndex%3C%5BT%5D%3E-for-RangeTo%3Cusize%3E
    // [20] https://doc.rust-lang.org/1.93.0/std/primitive.array.html#impl-Copy-for-%5BT;+N%5D
    //
    // Excludes: Other element types (including ZSTs), larger slices, custom
    // slice DSTs and their padding (see #3630), other targets/layouts, and the
    // aliasing, provenance, and reference-validity obligations that Kani does
    // not fully model. Pointer equality checks Kani's modeled addresses, not
    // provenance. These harnesses do not exercise the checked
    // `SplitAt::split_at` or `SplitAt::split_at_mut` entry points, or
    // `Split::{via_immutable, via_into_bytes, via_unaligned,
    // via_runtime_check}` for either receiver mutability. A successful unwind
    // check applies only to this bounded domain; it is not evidence for larger
    // slices. Returned empty-slice pointer identity and exact/minimal unwind
    // bounds are also excluded. This is not a generic `SplitAt` theorem.
    const CAPACITY: usize = 8;

    struct PartitionOracle {
        left_len: usize,
        right_len: usize,
        left_start: Option<*const u32>,
        right_start: Option<*const u32>,
        source_end: Option<*const u32>,
    }

    fn assert_same_usize(actual: usize, expected: usize) {
        assert_eq!(actual, expected);
    }

    fn assert_fixed_storage_sizes() {
        assert_same_usize(core::mem::size_of::<[u32; CAPACITY]>(), 32);
        assert_same_usize(core::mem::size_of::<([u32; CAPACITY], usize, usize)>(), 48);
        assert_same_usize(core::mem::size_of::<PartitionOracle>(), 64);
    }

    // Domain-bound mechanism: Rust's `usize::PartialOrd` supplies the Boolean
    // ordering observation [16], and Kani consumes that already-evaluated
    // observation as an assumption on subsequent paths [17].
    fn assume_usize_at_most(value: usize, upper: usize) {
        let value_is_at_most_upper = value <= upper;
        kani::assume(value_is_at_most_upper);
    }

    fn any_slice_split_case() -> ([u32; CAPACITY], usize, usize) {
        assert_fixed_storage_sizes();
        let values = kani::any();
        let source_len: usize = kani::any();
        assume_usize_at_most(source_len, CAPACITY);
        let split: usize = kani::any();
        assume_usize_at_most(split, source_len);

        kani::cover!(source_len == 0);
        kani::cover!(source_len == CAPACITY);
        kani::cover!(source_len > 0 && split == 0);
        kani::cover!(source_len > 0 && split == source_len);
        kani::cover!(split > 0 && split < source_len);

        (values, source_len, split)
    }

    fn partition_first_value_oracle(
        values: &[u32; CAPACITY],
        source_len: usize,
        split: usize,
    ) -> (Option<u32>, Option<u32>) {
        let values: &[u32] = values;
        let (source, _) = values.split_at(source_len);
        let (left, right) = source.split_at(split);
        (left.first().copied(), right.first().copied())
    }

    fn observed_first_value_changes(first: Option<u32>, replacement: u32) -> bool {
        first.is_some_and(|original| original != replacement)
    }

    fn partition_oracle(source: &[u32], split: usize) -> PartitionOracle {
        let (left, right) = source.split_at(split);
        PartitionOracle {
            left_len: left.len(),
            right_len: right.len(),
            left_start: if left.len() == 0 { None } else { Some(left.as_ptr()) },
            right_start: if right.len() == 0 { None } else { Some(right.as_ptr()) },
            source_end: if source.len() == 0 { None } else { Some(source.as_ptr_range().end) },
        }
    }

    fn assert_same_u32_elements(actual: &[u32], expected: &[u32]) {
        assert_same_usize(actual.len(), expected.len());
        assert!(actual.iter().copied().eq(expected.iter().copied()));
    }

    fn assert_same_u32_address(actual: *const u32, expected: *const u32) {
        assert!(core::ptr::eq(actual, expected));
    }

    fn assert_present_u32_address(actual: *const u32, expected: Option<*const u32>) {
        match expected {
            Some(expected) => assert_same_u32_address(actual, expected),
            None => panic!("nonempty partition has no oracle address"),
        }
    }

    // Zerocopy representation-policy oracle: the local `Split` representation
    // stores its source pointer and future-left length, and `Split::new` says it
    // produces a `Split` of the supplied arguments. This checks that policy by
    // direct field observation; it is not an independent Rust layout oracle.
    fn assert_split_descriptor_policy(
        actual_source: &[u32],
        actual_l_len: usize,
        expected_contents: &[u32],
        expected_source: *const u32,
        expected_l_len: usize,
    ) {
        assert_same_u32_elements(actual_source, expected_contents);
        assert_same_u32_address(actual_source.as_ptr(), expected_source);
        assert_same_usize(actual_l_len, expected_l_len);
    }

    fn assert_partitions(
        original: &[u32; CAPACITY],
        source_len: usize,
        split: usize,
        oracle: PartitionOracle,
        left: &[u32],
        right: &[u32],
    ) {
        let (expected_left, expected_right) = original[..source_len].split_at(split);
        assert_same_u32_elements(left, expected_left);
        assert_same_u32_elements(right, expected_right);
        assert_same_usize(left.len(), oracle.left_len);
        assert_same_usize(right.len(), oracle.right_len);
        // Gate pointer observations through the already documented `len`
        // oracle. The preceding equalities make a target length disagreement
        // fail before a nonempty expected partition could be skipped.
        if left.len() != 0 {
            assert_present_u32_address(left.as_ptr(), oracle.left_start);
        }
        if right.len() != 0 {
            assert_present_u32_address(right.as_ptr(), oracle.right_start);
            assert_present_u32_address(right.as_ptr_range().end, oracle.source_end);
        } else if left.len() != 0 {
            assert_present_u32_address(left.as_ptr_range().end, oracle.source_end);
        }
        if left.len() != 0 && right.len() != 0 {
            assert_same_u32_address(left.as_ptr_range().end, right.as_ptr());
        }
    }

    // Zerocopy behavior-policy oracle: constructing a mutable `Split`
    // descriptor is intended only to package the supplied source and split
    // length, so the complete backing array must have its original value after
    // the call. The ordered-value helper supplies comparison mechanics, but no
    // safe Rust contract independently chooses this final-state policy for the
    // zerocopy target. This post-call comparison does not detect transient
    // writes which the target restores before returning.
    fn assert_mutable_descriptor_final_state_policy(
        actual: &[u32; CAPACITY],
        original: &[u32; CAPACITY],
    ) {
        assert_same_u32_elements(actual, original);
    }

    fn apply_mutation_oracle(
        expected: &mut [u32; CAPACITY],
        source_len: usize,
        split: usize,
        left_value: u32,
        right_value: u32,
    ) {
        let (left, right) = expected[..source_len].split_at_mut(split);
        left.fill(left_value);
        right.fill(right_value);
    }

    #[kani::proof]
    #[kani::unwind(33)]
    fn prove_slice_split_at_unchecked_descriptor() {
        let (values, source_len, split) = any_slice_split_case();
        let original = values;
        let source = &values[..source_len];
        let expected_source = source.as_ptr();
        // SAFETY: `any_slice_split_case` passes the independently evaluated
        // Rust `split <= source_len` result to Kani through the factored
        // assumption mechanism documented above. The factored source-prefix
        // bridge establishes `source.len() == source_len`, so this entails the
        // bound required by `SplitAt::split_at_unchecked` and exactly the bound
        // on the standard slice operation [1].
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at_unchecked:
        //
        //     The caller has to ensure that `0 <= mid <= self.len()`.
        let parts = unsafe { SplitAt::split_at_unchecked(source, split) };
        let Split { source: actual_source, l_len: actual_l_len } = parts;
        assert_split_descriptor_policy(
            actual_source,
            actual_l_len,
            &original[..source_len],
            expected_source,
            split,
        );
    }

    #[kani::proof]
    #[kani::unwind(33)]
    fn prove_slice_split_at_mut_unchecked_descriptor() {
        let (original, source_len, split) = any_slice_split_case();
        let mut values = original;
        {
            let source = &mut values[..source_len];
            let expected_source = source.as_ptr();
            // SAFETY: `any_slice_split_case` passes the independently evaluated
            // Rust `split <= source_len` result to Kani through the factored
            // assumption mechanism documented above. The factored source-
            // prefix bridge establishes `source.len() == source_len`, so this
            // entails the bound required by `SplitAt::split_at_mut_unchecked`
            // and exactly the bound on the standard mutable slice operation
            // [1].
            //
            // [1] Per https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.split_at_mut_unchecked:
            //
            //     The caller has to ensure that `0 <= mid <= self.len()`.
            let parts = unsafe { SplitAt::split_at_mut_unchecked(source, split) };
            let Split { source: actual_source, l_len: actual_l_len } = parts;
            assert_split_descriptor_policy(
                actual_source,
                actual_l_len,
                &original[..source_len],
                expected_source,
                split,
            );
        }
        assert_mutable_descriptor_final_state_policy(&values, &original);
    }

    #[kani::proof]
    #[kani::unwind(33)]
    fn prove_split_via_unchecked_shared() {
        let (values, source_len, split) = any_slice_split_case();
        let source = &values[..source_len];
        let oracle = partition_oracle(source, split);

        // This literal is the known-good consumer input, not an invocation of
        // either descriptor producer under proof. `any_slice_split_case`
        // establishes `split <= source_len` through the factored Rust-ordering/
        // Kani-assumption mechanism above; the source-prefix bridge establishes
        // `source.len() == source_len`. Together these establish the private
        // `Split` invariant `split <= source.len()`.
        let parts = Split { source, l_len: split };

        // SAFETY: The array and slice layout guarantees [1] place each element
        // immediately after the last, so the two portions have no overlapping
        // padding. This satisfies `Split::via_unchecked`'s conditional
        // no-overlap precondition.
        //
        // [1] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html#array-layout
        // and https://doc.rust-lang.org/1.93.0/reference/type-layout.html#slice-layout:
        //
        //     An array of `[T; N]` has a size of `size_of::<T>() * N` and
        //     the same alignment of `T`.
        //
        //     Arrays are laid out so that the zero-based `nth` element of the
        //     array is offset from the start of the array by
        //     `n * size_of::<T>()` bytes.
        //
        //     Slices have the same layout as the section of the array they
        //     slice.
        let (left, right) = unsafe { parts.via_unchecked() };
        assert_partitions(&values, source_len, split, oracle, left, right);
    }

    #[kani::proof]
    #[kani::unwind(33)]
    fn prove_split_via_unchecked_mut() {
        let (original, source_len, split) = any_slice_split_case();
        let mut values = original;
        let left_value: u32 = kani::any();
        let right_value: u32 = kani::any();
        let mut expected_values = original;
        apply_mutation_oracle(&mut expected_values, source_len, split, left_value, right_value);
        let (left_first, right_first) = partition_first_value_oracle(&original, source_len, split);

        kani::cover!(split > 0 && observed_first_value_changes(left_first, left_value));
        kani::cover!(split < source_len && observed_first_value_changes(right_first, right_value));

        {
            let oracle = partition_oracle(&values[..source_len], split);
            let source = &mut values[..source_len];

            // This literal is the known-good consumer input, not an invocation
            // of either descriptor producer under proof.
            // `any_slice_split_case` establishes `split <= source_len` through
            // the factored Rust-ordering/Kani-assumption mechanism above; the
            // source-prefix bridge establishes
            // `source.len() == source_len`. Together these establish the
            // private `Split` invariant `split <= source.len()`.
            let parts = Split { source, l_len: split };

            // SAFETY: The array and slice layout guarantees [1] place each
            // element immediately after the last, so the two exclusive
            // portions have no overlapping padding. This satisfies
            // `Split::via_unchecked`'s no-overlap precondition.
            //
            // [1] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html#array-layout
            // and https://doc.rust-lang.org/1.93.0/reference/type-layout.html#slice-layout:
            //
            //     An array of `[T; N]` has a size of `size_of::<T>() * N` and
            //     the same alignment of `T`.
            //
            //     Arrays are laid out so that the zero-based `nth` element of
            //     the array is offset from the start of the array by
            //     `n * size_of::<T>()` bytes.
            //
            //     Slices have the same layout as the section of the array they
            //     slice.
            let (left, right) = unsafe { parts.via_unchecked() };

            assert_partitions(&original, source_len, split, oracle, left, right);
            left.fill(left_value);
            right.fill(right_value);
        }
        assert_same_u32_elements(&values, &expected_values);
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "derive")]
    #[test]
    fn test_split_at() {
        use crate::{FromBytes, Immutable, IntoBytes, KnownLayout, SplitAt};

        #[derive(FromBytes, KnownLayout, SplitAt, IntoBytes, Immutable, Debug)]
        #[repr(C)]
        struct SliceDst<const OFFSET: usize> {
            prefix: [u8; OFFSET],
            trailing: [u8],
        }

        #[allow(clippy::as_conversions)]
        fn test_split_at<const OFFSET: usize, const BUFFER_SIZE: usize>() {
            // Test `split_at`
            let n: usize = BUFFER_SIZE - OFFSET;
            let arr = [1; BUFFER_SIZE];
            let dst = SliceDst::<OFFSET>::ref_from_bytes(&arr[..]).unwrap();
            for i in 0..=n {
                let (l, r) = dst.split_at(i).unwrap().via_runtime_check().unwrap();
                let l_sum: u8 = l.trailing.iter().sum();
                let r_sum: u8 = r.iter().sum();
                assert_eq!(l_sum, i as u8);
                assert_eq!(r_sum, (n - i) as u8);
                assert_eq!(l_sum + r_sum, n as u8);
            }

            // Test `split_at_mut`
            let n: usize = BUFFER_SIZE - OFFSET;
            let mut arr = [1; BUFFER_SIZE];
            let dst = SliceDst::<OFFSET>::mut_from_bytes(&mut arr[..]).unwrap();
            for i in 0..=n {
                let (l, r) = dst.split_at_mut(i).unwrap().via_runtime_check().unwrap();
                let l_sum: u8 = l.trailing.iter().sum();
                let r_sum: u8 = r.iter().sum();
                assert_eq!(l_sum, i as u8);
                assert_eq!(r_sum, (n - i) as u8);
                assert_eq!(l_sum + r_sum, n as u8);
            }
        }

        test_split_at::<0, 16>();
        test_split_at::<1, 17>();
        test_split_at::<2, 18>();
    }

    #[cfg(feature = "derive")]
    #[test]
    #[allow(clippy::as_conversions)]
    fn test_split_at_overlapping() {
        use crate::{FromBytes, Immutable, IntoBytes, KnownLayout, SplitAt};

        #[derive(FromBytes, KnownLayout, SplitAt, Immutable)]
        #[repr(C, align(2))]
        struct SliceDst {
            prefix: u8,
            trailing: [u8],
        }

        const N: usize = 16;

        let arr = [1u16; N];
        let dst = SliceDst::ref_from_bytes(arr.as_bytes()).unwrap();

        for i in 0..N {
            let split = dst.split_at(i).unwrap().via_runtime_check();
            if i % 2 == 1 {
                assert!(split.is_ok());
            } else {
                assert!(split.is_err());
            }
        }
    }
    #[test]
    fn test_split_at_unchecked() {
        use crate::SplitAt;
        let mut arr = [1, 2, 3, 4];
        let slice = &arr[..];
        // SAFETY: 2 <= arr.len() (4)
        let split = unsafe { SplitAt::split_at_unchecked(slice, 2) };
        // SAFETY: SplitAt::split_at_unchecked guarantees that the split is valid.
        let (l, r) = unsafe { split.via_unchecked() };
        assert_eq!(l, &[1, 2]);
        assert_eq!(r, &[3, 4]);

        let slice_mut = &mut arr[..];
        // SAFETY: 2 <= arr.len() (4)
        let split = unsafe { SplitAt::split_at_mut_unchecked(slice_mut, 2) };
        // SAFETY: SplitAt::split_at_mut_unchecked guarantees that the split is valid.
        let (l, r) = unsafe { split.via_unchecked() };
        assert_eq!(l, &mut [1, 2]);
        assert_eq!(r, &mut [3, 4]);
    }

    #[test]
    fn test_split_at_via_methods() {
        use crate::{FromBytes, Immutable, IntoBytes, KnownLayout, SplitAt};
        #[derive(FromBytes, KnownLayout, SplitAt, IntoBytes, Immutable, Debug)]
        #[repr(C)]
        struct Packet {
            length: u8,
            body: [u8],
        }

        let arr = [1, 2, 3, 4];
        let packet = Packet::ref_from_bytes(&arr[..]).unwrap();

        let split1 = packet.split_at(2).unwrap();
        let (l, r) = split1.via_immutable();
        assert_eq!(l.length, 1);
        assert_eq!(r, &[4]);

        let split2 = packet.split_at(2).unwrap();
        let (l, r) = split2.via_into_bytes();
        assert_eq!(l.length, 1);
        assert_eq!(r, &[4]);
    }
    #[test]
    fn test_split_at_via_unaligned() {
        use crate::{FromBytes, Immutable, IntoBytes, KnownLayout, SplitAt, Unaligned};
        #[derive(FromBytes, KnownLayout, SplitAt, IntoBytes, Immutable, Unaligned)]
        #[repr(C)]
        struct Packet {
            length: u8,
            body: [u8],
        }

        let arr = [1, 2, 3, 4];
        let packet = Packet::ref_from_bytes(&arr[..]).unwrap();

        let split = packet.split_at(2).unwrap();
        let (l, r) = split.via_unaligned();
        assert_eq!(l.length, 1);
        assert_eq!(r, &[4]);
    }
}
