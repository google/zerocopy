// Copyright 2018 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Utilities for safe zero-copy parsing and serialization.
//!
//! This crate provides utilities which make it easy to perform zero-copy
//! parsing and serialization by allowing zero-copy conversion to/from byte
//! slices.
//!
//! This is enabled by three core marker traits, each of which can be derived
//! (e.g., `#[derive(FromBytes)]`):
//! - [`FromBytes`] indicates that a type may safely be converted from an
//!   arbitrary byte sequence
//! - [`AsBytes`] indicates that a type may safely be converted *to* a byte
//!   sequence
//! - [`Unaligned`] indicates that a type's alignment requirement is 1
//!
//! Types which implement a subset of these traits can then be converted to/from
//! byte sequences with little to no runtime overhead.
//!
//! Note that these traits are ignorant of byte order. For byte order-aware
//! types, see the [`byteorder`] module.

#![cfg_attr(not(test), no_std)]
#![recursion_limit = "2048"]

pub mod byteorder;

pub use crate::byteorder::*;
pub use zerocopy_derive::*;

use core::cell::{Ref, RefMut};
use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;
use core::mem;
use core::ops::{Deref, DerefMut};
use core::slice;

// This is a hack to allow derives of FromBytes, AsBytes, and Unaligned to work
// in this crate. They assume that zerocopy is linked as an extern crate, so
// they access items from it as `zerocopy::Xxx`. This makes that still work.
mod zerocopy {
    pub use crate::*;
}

// implement an unsafe trait for a range of container types
macro_rules! impl_for_composite_types {
    ($trait:ident) => {
        unsafe impl<T> $trait for PhantomData<T> {
            fn only_derive_is_allowed_to_implement_this_trait()
            where
                Self: Sized,
            {
            }
        }
        unsafe impl<T: $trait> $trait for [T] {
            fn only_derive_is_allowed_to_implement_this_trait()
            where
                Self: Sized,
            {
            }
        }
        unsafe impl $trait for () {
            fn only_derive_is_allowed_to_implement_this_trait()
            where
                Self: Sized,
            {
            }
        }
        impl_for_array_sizes!($trait);
    };
}

// implement an unsafe trait for all signed and unsigned primitive types
macro_rules! impl_for_primitives {
    ($trait:ident) => (
        impl_for_primitives!(@inner $trait, u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, f32, f64);
    );
    (@inner $trait:ident, $type:ty) => (
        unsafe impl $trait for $type {
            fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
        }
    );
    (@inner $trait:ident, $type:ty, $($types:ty),*) => (
        unsafe impl $trait for $type {
            fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
        }
        impl_for_primitives!(@inner $trait, $($types),*);
    );
}

// implement an unsafe trait for all array lengths up to 64, plus several
// useful powers-of-two beyond that, plus lengths needed by Fuchsia with
// an element type that implements the trait
macro_rules! impl_for_array_sizes {
    ($trait:ident) => (
        impl_for_array_sizes!(@inner $trait, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 98, 126, 128, 236, 255, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536);
    );
    (@inner $trait:ident, $n:expr) => (
        unsafe impl<T: $trait> $trait for [T; $n] {
            fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
        }
    );
    (@inner $trait:ident, $n:expr, $($ns:expr),*) => (
        unsafe impl<T: $trait> $trait for [T; $n] {
            fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
        }
        impl_for_array_sizes!(@inner $trait, $($ns),*);
    );
}

/// Types for which any byte pattern is valid.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(FromBytes)]`.
///
/// `FromBytes` types can safely be deserialized from an untrusted sequence of
/// bytes because any byte sequence corresponds to a valid instance of the type.
///
/// `FromBytes` is ignorant of byte order. For byte order-aware types, see the
/// [`byteorder`] module.
///
/// # Safety
///
/// If `T: FromBytes`, then unsafe code may assume that it is sound to treat any
/// initialized sequence of bytes of length `size_of::<T>()` as a `T`. If a type
/// is marked as `FromBytes` which violates this contract, it may cause
/// undefined behavior.
///
/// If a type has the following properties, then it is safe to implement
/// `FromBytes` for that type:
/// - If the type is a struct:
///   - All of its fields must implement `FromBytes`
/// - If the type is an enum:
///   - It must be a C-like enum (meaning that all variants have no fields)
///   - It must have a defined representation (`repr`s `C`, `u8`, `u16`, `u32`,
///     `u64`, `usize`, `i8`, `i16`, `i32`, `i64`, or `isize`).
///   - The maximum number of discriminants must be used (so that every possible
///     bit pattern is a valid one). Be very careful when using the `C`,
///     `usize`, or `isize` representations, as their size is
///     platform-dependent.
///
/// # Rationale
///
/// ## Why isn't an explicit representation required for structs?
///
/// Per the [Rust reference](reference),
/// > The representation of a type can change the padding between fields, but
/// does not change the layout of the fields themselves.
///
/// [reference]: https://doc.rust-lang.org/reference/type-layout.html#representations
///
/// Since the layout of structs only consists of padding bytes and field bytes,
/// a struct is soundly `FromBytes` if:
/// 1. its padding is soundly `FromBytes`, and
/// 2. its fields are soundly `FromBytes`.
///
/// The answer to the first question is always yes: padding bytes do not have
/// any validity constraints. A [discussion] of this question in the Unsafe Code
/// Guidelines Working Group concluded that it would be virtually unimaginable
/// for future versions of rustc to add validity constraints to padding bytes.
///
/// [discussion]: https://github.com/rust-lang/unsafe-code-guidelines/issues/174
///
/// Whether a struct is soundly `FromBytes` therefore solely depends on whether
/// its fields are `FromBytes`.
pub unsafe trait FromBytes {
    // NOTE: The Self: Sized bound makes it so that FromBytes is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;
}

/// Types which are safe to treat as an immutable byte slice.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(AsBytes)]`.
///
/// `AsBytes` types can be safely viewed as a slice of bytes. In particular,
/// this means that, in any valid instance of the type, none of the bytes of the
/// instance are uninitialized. This precludes the following types:
/// - Structs with internal padding
/// - Unions in which not all variants have the same length
///
/// `AsBytes` is ignorant of byte order. For byte order-aware types, see the
/// [`byteorder`] module.
///
/// # Custom Derive Errors
///
/// Due to the way that the custom derive for `AsBytes` is implemented, you may
/// get an error like this:
///
/// ```text
/// error[E0080]: evaluation of constant value failed
///   --> lib.rs:1:10
///    |
///  1 | #[derive(AsBytes)]
///    |          ^^^^^^^ attempt to divide by zero
/// ```
///
/// This error means that the type being annotated has padding bytes, which is
/// illegal for `AsBytes` types. Consider either adding explicit struct fields
/// where those padding bytes would be or using `#[repr(packed)]`.
///
/// # Safety
///
/// If `T: AsBytes`, then unsafe code may assume that it is sound to treat any
/// instance of the type as an immutable `[u8]` of length `size_of::<T>()`. If a
/// type is marked as `AsBytes` which violates this contract, it may cause
/// undefined behavior.
///
/// If a type has the following properties, then it is safe to implement
/// `AsBytes` for that type
/// - If the type is a struct:
///   - It must have a defined representation (`repr(C)`, `repr(transparent)`,
///     or `repr(packed)`).
///   - All of its fields must be `AsBytes`
///   - Its layout must have no padding. This is always true for
///     `repr(transparent)` and `repr(packed)`. For `repr(C)`, see the layout
///     algorithm described in the [Rust Reference].
/// - If the type is an enum:
///   - It must be a C-like enum (meaning that all variants have no fields)
///   - It must have a defined representation (`repr`s `C`, `u8`, `u16`, `u32`,
///     `u64`, `usize`, `i8`, `i16`, `i32`, `i64`, or `isize`).
///
/// [Rust Reference]: https://doc.rust-lang.org/reference/type-layout.html
pub unsafe trait AsBytes {
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Get the bytes of this value.
    ///
    /// `as_bytes` provides access to the bytes of this value as an immutable
    /// byte slice.
    fn as_bytes(&self) -> &[u8] {
        unsafe {
            // NOTE: This function does not have a Self: Sized bound.
            // size_of_val works for unsized values too.
            let len = mem::size_of_val(self);
            slice::from_raw_parts(self as *const Self as *const u8, len)
        }
    }

    /// Get the bytes of this value mutably.
    ///
    /// `as_bytes_mut` provides access to the bytes of this value as a mutable
    /// byte slice.
    fn as_bytes_mut(&mut self) -> &mut [u8]
    where
        Self: FromBytes,
    {
        unsafe {
            // NOTE: This function does not have a Self: Sized bound.
            // size_of_val works for unsized values too.
            let len = mem::size_of_val(self);
            slice::from_raw_parts_mut(self as *mut Self as *mut u8, len)
        }
    }
}

// Special case for bool
unsafe impl AsBytes for bool {
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }
}

impl_for_primitives!(FromBytes);
impl_for_primitives!(AsBytes);
impl_for_composite_types!(FromBytes);
impl_for_composite_types!(AsBytes);

/// Types with no alignment requirement.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(Unaligned)]`.
///
/// If `T: Unaligned`, then `align_of::<T>() == 1`.
///
/// # Safety
///
/// If `T: Unaligned`, then unsafe code may assume that it is sound to produce a
/// reference to `T` at any memory location regardless of alignment. If a type
/// is marked as `Unaligned` which violates this contract, it may cause
/// undefined behavior.
pub unsafe trait Unaligned {
    // NOTE: The Self: Sized bound makes it so that Unaligned is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;
}

unsafe impl Unaligned for u8 {
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }
}
unsafe impl Unaligned for i8 {
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }
}
impl_for_composite_types!(Unaligned);

/// A length- and alignment-checked reference to a byte slice which can safely
/// be reinterpreted as another type.
///
/// `LayoutVerified` is a byte slice reference (`&[u8]`, `&mut [u8]`,
/// `Ref<[u8]>`, `RefMut<[u8]>`, etc) with the invaraint that the slice's length
/// and alignment are each greater than or equal to the length and alignment of
/// `T`. Using this invariant, it implements `Deref` for `T` so long as `T:
/// FromBytes` and `DerefMut` so long as `T: FromBytes + AsBytes`.
///
/// # Examples
///
/// `LayoutVerified` can be used to treat a sequence of bytes as a structured
/// type, and to read and write the fields of that type as if the byte slice
/// reference were simply a reference to that type.
///
/// ```rust
/// use zerocopy::{AsBytes, ByteSlice, ByteSliceMut, FromBytes, LayoutVerified, Unaligned};
///
/// #[derive(FromBytes, AsBytes, Unaligned)]
/// #[repr(C)]
/// struct UdpHeader {
///     src_port: [u8; 2],
///     dst_port: [u8; 2],
///     length: [u8; 2],
///     checksum: [u8; 2],
/// }
///
/// struct UdpPacket<B> {
///     header: LayoutVerified<B, UdpHeader>,
///     body: B,
/// }
///
/// impl<B: ByteSlice> UdpPacket<B> {
///     pub fn parse(bytes: B) -> Option<UdpPacket<B>> {
///         let (header, body) = LayoutVerified::new_unaligned_from_prefix(bytes)?;
///         Some(UdpPacket { header, body })
///     }
///
///     pub fn get_src_port(&self) -> [u8; 2] {
///         self.header.src_port
///     }
/// }
///
/// impl<B: ByteSliceMut> UdpPacket<B> {
///     pub fn set_src_port(&mut self, src_port: [u8; 2]) {
///         self.header.src_port = src_port;
///     }
/// }
/// ```
pub struct LayoutVerified<B, T: ?Sized>(B, PhantomData<T>);

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSlice,
{
    /// Construct a new `LayoutVerified`.
    ///
    /// `new` verifies that `bytes.len() == size_of::<T>()` and that `bytes` is
    /// aligned to `align_of::<T>()`, and constructs a new `LayoutVerified`. If
    /// either of these checks fail, it returns `None`.
    #[inline]
    pub fn new(bytes: B) -> Option<LayoutVerified<B, T>> {
        if bytes.len() != mem::size_of::<T>() || !aligned_to(bytes.deref(), mem::align_of::<T>()) {
            return None;
        }
        Some(LayoutVerified(bytes, PhantomData))
    }

    /// Construct a new `LayoutVerified` from the prefix of a byte slice.
    ///
    /// `new_from_prefix` verifies that `bytes.len() >= size_of::<T>()` and that
    /// `bytes` is aligned to `align_of::<T>()`. It consumes the first
    /// `size_of::<T>()` bytes from `bytes` to construct a `LayoutVerified`, and
    /// returns the remaining bytes to the caller. If either the length or
    /// alignment checks fail, it returns `None`.
    #[inline]
    pub fn new_from_prefix(bytes: B) -> Option<(LayoutVerified<B, T>, B)> {
        if bytes.len() < mem::size_of::<T>() || !aligned_to(bytes.deref(), mem::align_of::<T>()) {
            return None;
        }
        let (bytes, suffix) = bytes.split_at(mem::size_of::<T>());
        Some((LayoutVerified(bytes, PhantomData), suffix))
    }

    /// Construct a new `LayoutVerified` from the suffix of a byte slice.
    ///
    /// `new_from_suffix` verifies that `bytes.len() >= size_of::<T>()` and that
    /// the last `size_of::<T>()` bytes of `bytes` are aligned to
    /// `align_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the preceding bytes
    /// to the caller. If either the length or alignment checks fail, it returns
    /// `None`.
    #[inline]
    pub fn new_from_suffix(bytes: B) -> Option<(B, LayoutVerified<B, T>)> {
        let bytes_len = bytes.len();
        if bytes_len < mem::size_of::<T>() {
            return None;
        }
        let (prefix, bytes) = bytes.split_at(bytes_len - mem::size_of::<T>());
        if !aligned_to(bytes.deref(), mem::align_of::<T>()) {
            return None;
        }
        Some((prefix, LayoutVerified(bytes, PhantomData)))
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSlice,
    T: ?Sized,
{
    // Get the underlying bytes.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        &self.0
    }
}

impl<B, T> LayoutVerified<B, [T]>
where
    B: ByteSlice,
{
    /// Construct a new `LayoutVerified` of a slice type.
    ///
    /// `new_slice` verifies that `bytes.len()` is a multiple of
    /// `size_of::<T>()` and that `bytes` is aligned to `align_of::<T>()`, and
    /// constructs a new `LayoutVerified`. If either of these checks fail, it
    /// returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice(bytes: B) -> Option<LayoutVerified<B, [T]>> {
        assert_ne!(mem::size_of::<T>(), 0);
        if bytes.len() % mem::size_of::<T>() != 0
            || !aligned_to(bytes.deref(), mem::align_of::<T>())
        {
            return None;
        }
        Some(LayoutVerified(bytes, PhantomData))
    }
}

fn map_zeroed<B: ByteSliceMut, T: ?Sized>(
    opt: Option<LayoutVerified<B, T>>,
) -> Option<LayoutVerified<B, T>> {
    match opt {
        Some(mut lv) => {
            for b in lv.0.iter_mut() {
                *b = 0;
            }
            Some(lv)
        }
        None => None,
    }
}

fn map_prefix_tuple_zeroed<B: ByteSliceMut, T: ?Sized>(
    opt: Option<(LayoutVerified<B, T>, B)>,
) -> Option<(LayoutVerified<B, T>, B)> {
    match opt {
        Some((mut lv, rest)) => {
            for b in lv.0.iter_mut() {
                *b = 0;
            }
            Some((lv, rest))
        }
        None => None,
    }
}

fn map_suffix_tuple_zeroed<B: ByteSliceMut, T: ?Sized>(
    opt: Option<(B, LayoutVerified<B, T>)>,
) -> Option<(B, LayoutVerified<B, T>)> {
    map_prefix_tuple_zeroed(opt.map(|(a, b)| (b, a))).map(|(a, b)| (b, a))
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSliceMut,
{
    /// Construct a new `LayoutVerified` after zeroing the bytes.
    ///
    /// `new_zeroed` verifies that `bytes.len() == size_of::<T>()` and that
    /// `bytes` is aligned to `align_of::<T>()`, and constructs a new
    /// `LayoutVerified`. If either of these checks fail, it returns `None`.
    ///
    /// If the checks succeed, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    #[inline]
    pub fn new_zeroed(bytes: B) -> Option<LayoutVerified<B, T>> {
        map_zeroed(Self::new(bytes))
    }

    /// Construct a new `LayoutVerified` from the prefix of a byte slice,
    /// zeroing the prefix.
    ///
    /// `new_from_prefix_zeroed` verifies that `bytes.len() >= size_of::<T>()`
    /// and that `bytes` is aligned to `align_of::<T>()`. It consumes the first
    /// `size_of::<T>()` bytes from `bytes` to construct a `LayoutVerified`, and
    /// returns the remaining bytes to the caller. If either the length or
    /// alignment checks fail, it returns `None`.
    ///
    /// If the checks succeed, then the prefix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline]
    pub fn new_from_prefix_zeroed(bytes: B) -> Option<(LayoutVerified<B, T>, B)> {
        map_prefix_tuple_zeroed(Self::new_from_prefix(bytes))
    }

    /// Construct a new `LayoutVerified` from the suffix of a byte slice,
    /// zeroing the suffix.
    ///
    /// `new_from_suffix_zeroed` verifies that `bytes.len() >= size_of::<T>()` and that
    /// the last `size_of::<T>()` bytes of `bytes` are aligned to
    /// `align_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the preceding bytes
    /// to the caller. If either the length or alignment checks fail, it returns
    /// `None`.
    ///
    /// If the checks succeed, then the suffix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline]
    pub fn new_from_suffix_zeroed(bytes: B) -> Option<(B, LayoutVerified<B, T>)> {
        map_suffix_tuple_zeroed(Self::new_from_suffix(bytes))
    }
}

impl<B, T> LayoutVerified<B, [T]>
where
    B: ByteSliceMut,
{
    /// Construct a new `LayoutVerified` of a slice type after zeroing the
    /// bytes.
    ///
    /// `new_slice_zeroed` verifies that `bytes.len()` is a multiple of
    /// `size_of::<T>()` and that `bytes` is aligned to `align_of::<T>()`, and
    /// constructs a new `LayoutVerified`. If either of these checks fail, it
    /// returns `None`.
    ///
    /// If the checks succeed, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_zeroed(bytes: B) -> Option<LayoutVerified<B, [T]>> {
        map_zeroed(Self::new_slice(bytes))
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSlice,
    T: Unaligned,
{
    /// Construct a new `LayoutVerified` for a type with no alignment
    /// requirement.
    ///
    /// `new_unaligned` verifies that `bytes.len() == size_of::<T>()` and
    /// constructs a new `LayoutVerified`. If the check fails, it returns
    /// `None`.
    #[inline]
    pub fn new_unaligned(bytes: B) -> Option<LayoutVerified<B, T>> {
        if bytes.len() != mem::size_of::<T>() {
            return None;
        }
        Some(LayoutVerified(bytes, PhantomData))
    }

    /// Construct a new `LayoutVerified` from the prefix of a byte slice for a
    /// type with no alignment requirement.
    ///
    /// `new_unaligned_from_prefix` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the first `size_of::<T>()` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the remaining bytes
    /// to the caller. If the length check fails, it returns `None`.
    #[inline]
    pub fn new_unaligned_from_prefix(bytes: B) -> Option<(LayoutVerified<B, T>, B)> {
        if bytes.len() < mem::size_of::<T>() {
            return None;
        }
        let (bytes, suffix) = bytes.split_at(mem::size_of::<T>());
        Some((LayoutVerified(bytes, PhantomData), suffix))
    }

    /// Construct a new `LayoutVerified` from the suffix of a byte slice for a
    /// type with no alignment requirement.
    ///
    /// `new_unaligned_from_suffix` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the preceding bytes
    /// to the caller. If the length check fails, it returns `None`.
    #[inline]
    pub fn new_unaligned_from_suffix(bytes: B) -> Option<(B, LayoutVerified<B, T>)> {
        let bytes_len = bytes.len();
        if bytes_len < mem::size_of::<T>() {
            return None;
        }
        let (prefix, bytes) = bytes.split_at(bytes_len - mem::size_of::<T>());
        Some((prefix, LayoutVerified(bytes, PhantomData)))
    }
}

impl<B, T> LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: Unaligned,
{
    /// Construct a new `LayoutVerified` of a slice type with no alignment
    /// requirement.
    ///
    /// `new_slice_unaligned` verifies that `bytes.len()` is a multiple of
    /// `size_of::<T>()` and constructs a new `LayoutVerified`. If the check
    /// fails, it returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_unaligned(bytes: B) -> Option<LayoutVerified<B, [T]>> {
        assert_ne!(mem::size_of::<T>(), 0);
        if bytes.len() % mem::size_of::<T>() != 0 {
            return None;
        }
        Some(LayoutVerified(bytes, PhantomData))
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSliceMut,
    T: Unaligned,
{
    /// Construct a new `LayoutVerified` for a type with no alignment
    /// requirement, zeroing the bytes.
    ///
    /// `new_unaligned_zeroed` verifies that `bytes.len() == size_of::<T>()` and
    /// constructs a new `LayoutVerified`. If the check fails, it returns
    /// `None`.
    ///
    /// If the check succeeds, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    #[inline]
    pub fn new_unaligned_zeroed(bytes: B) -> Option<LayoutVerified<B, T>> {
        map_zeroed(Self::new_unaligned(bytes))
    }

    /// Construct a new `LayoutVerified` from the prefix of a byte slice for a
    /// type with no alignment requirement, zeroing the prefix.
    ///
    /// `new_unaligned_from_prefix_zeroed` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the first `size_of::<T>()` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the remaining bytes
    /// to the caller. If the length check fails, it returns `None`.
    ///
    /// If the check succeeds, then the prefix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline]
    pub fn new_unaligned_from_prefix_zeroed(bytes: B) -> Option<(LayoutVerified<B, T>, B)> {
        map_prefix_tuple_zeroed(Self::new_unaligned_from_prefix(bytes))
    }

    /// Construct a new `LayoutVerified` from the suffix of a byte slice for a
    /// type with no alignment requirement, zeroing the suffix.
    ///
    /// `new_unaligned_from_suffix_zeroed` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the preceding bytes
    /// to the caller. If the length check fails, it returns `None`.
    ///
    /// If the check succeeds, then the suffix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline]
    pub fn new_unaligned_from_suffix_zeroed(bytes: B) -> Option<(B, LayoutVerified<B, T>)> {
        map_suffix_tuple_zeroed(Self::new_unaligned_from_suffix(bytes))
    }
}

impl<B, T> LayoutVerified<B, [T]>
where
    B: ByteSliceMut,
    T: Unaligned,
{
    /// Construct a new `LayoutVerified` for a slice type with no alignment
    /// requirement, zeroing the bytes.
    ///
    /// `new_slice_unaligned_zeroed` verifies that `bytes.len()` is a multiple
    /// of `size_of::<T>()` and constructs a new `LayoutVerified`. If the check
    /// fails, it returns `None`.
    ///
    /// If the check succeeds, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_unaligned_zeroed(bytes: B) -> Option<LayoutVerified<B, [T]>> {
        map_zeroed(Self::new_slice_unaligned(bytes))
    }
}

impl<'a, B, T> LayoutVerified<B, T>
where
    B: 'a + ByteSlice,
    T: FromBytes,
{
    /// Convert this `LayoutVerified` into a reference.
    ///
    /// `into_ref` consumes the `LayoutVerified`, and returns a reference to
    /// `T`.
    pub fn into_ref(self) -> &'a T {
        // NOTE: This is safe because `B` is guaranteed to live for the lifetime
        // `'a`, meaning that a) the returned reference cannot outlive the `B`
        // from which `self` was constructed and, b) no mutable methods on that
        // `B` can be called during the lifetime of the returned reference. See
        // the documentation on `deref_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_helper() }
    }
}

impl<'a, B, T> LayoutVerified<B, T>
where
    B: 'a + ByteSliceMut,
    T: FromBytes + AsBytes,
{
    /// Convert this `LayoutVerified` into a mutable reference.
    ///
    /// `into_mut` consumes the `LayoutVerified`, and returns a mutable
    /// reference to `T`.
    pub fn into_mut(mut self) -> &'a mut T {
        // NOTE: This is safe because `B` is guaranteed to live for the lifetime
        // `'a`, meaning that a) the returned reference cannot outlive the `B`
        // from which `self` was constructed and, b) no other methods - mutable
        // or immutable - on that `B` can be called during the lifetime of the
        // returned reference. See the documentation on `deref_mut_helper` for
        // what invariants we are required to uphold.
        unsafe { self.deref_mut_helper() }
    }
}

impl<'a, B, T> LayoutVerified<B, [T]>
where
    B: 'a + ByteSlice,
    T: FromBytes,
{
    /// Convert this `LayoutVerified` into a slice reference.
    ///
    /// `into_slice` consumes the `LayoutVerified`, and returns a reference to
    /// `[T]`.
    pub fn into_slice(self) -> &'a [T] {
        // NOTE: This is safe because `B` is guaranteed to live for the lifetime
        // `'a`, meaning that a) the returned reference cannot outlive the `B`
        // from which `self` was constructed and, b) no mutable methods on that
        // `B` can be called during the lifetime of the returned reference. See
        // the documentation on `deref_slice_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_slice_helper() }
    }
}

impl<'a, B, T> LayoutVerified<B, [T]>
where
    B: 'a + ByteSliceMut,
    T: FromBytes + AsBytes,
{
    /// Convert this `LayoutVerified` into a mutable slice reference.
    ///
    /// `into_mut_slice` consumes the `LayoutVerified`, and returns a mutable reference to
    /// `[T]`.
    pub fn into_mut_slice(mut self) -> &'a mut [T] {
        // NOTE: This is safe because `B` is guaranteed to live for the lifetime
        // `'a`, meaning that a) the returned reference cannot outlive the `B`
        // from which `self` was constructed and, b) no other methods - mutable
        // or immutable - on that `B` can be called during the lifetime of the
        // returned reference. See the documentation on `deref_mut_slice_helper`
        // for what invariants we are required to uphold.
        unsafe { self.deref_mut_slice_helper() }
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes,
{
    /// Create an immutable reference to `T` with a specific lifetime.
    ///
    /// # Safety
    ///
    /// The type bounds on this method guarantee that it is safe to create an
    /// immutable reference to `T` from `self`. However, since the lifetime `'a`
    /// is not required to be shorter than the lifetime of the reference to
    /// `self`, the caller must guarantee that the lifetime `'a` is valid for
    /// this reference. In particular, the referent must exist for all of `'a`,
    /// and no mutable references to the same memory may be constructed during
    /// `'a`.
    unsafe fn deref_helper<'a>(&self) -> &'a T {
        &*(self.0.as_ptr() as *const T)
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSliceMut,
    T: FromBytes + AsBytes,
{
    /// Create a mutable reference to `T` with a specific lifetime.
    ///
    /// # Safety
    ///
    /// The type bounds on this method guarantee that it is safe to create a
    /// mutable reference to `T` from `self`. However, since the lifetime `'a`
    /// is not required to be shorter than the lifetime of the reference to
    /// `self`, the caller must guarantee that the lifetime `'a` is valid for
    /// this reference. In particular, the referent must exist for all of `'a`,
    /// and no other references - mutable or immutable - to the same memory may
    /// be constructed during `'a`.
    unsafe fn deref_mut_helper<'a>(&mut self) -> &'a mut T {
        &mut *(self.0.as_mut_ptr() as *mut T)
    }
}

impl<B, T> LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes,
{
    /// Create an immutable reference to `[T]` with a specific lifetime.
    ///
    /// # Safety
    ///
    /// `deref_slice_helper` has the same safety requirements as `deref_helper`.
    unsafe fn deref_slice_helper<'a>(&self) -> &'a [T] {
        let len = self.0.len();
        let elem_size = mem::size_of::<T>();
        debug_assert_ne!(elem_size, 0);
        debug_assert_eq!(len % elem_size, 0);
        let elems = len / elem_size;
        slice::from_raw_parts(self.0.as_ptr() as *const T, elems)
    }
}

impl<B, T> LayoutVerified<B, [T]>
where
    B: ByteSliceMut,
    T: FromBytes + AsBytes,
{
    /// Create a mutable reference to `[T]` with a specific lifetime.
    ///
    /// # Safety
    ///
    /// `deref_mut_slice_helper` has the same safety requirements as
    /// `deref_mut_helper`.
    unsafe fn deref_mut_slice_helper<'a>(&mut self) -> &'a mut [T] {
        let len = self.0.len();
        let elem_size = mem::size_of::<T>();
        debug_assert_ne!(elem_size, 0);
        debug_assert_eq!(len % elem_size, 0);
        let elems = len / elem_size;
        slice::from_raw_parts_mut(self.0.as_mut_ptr() as *mut T, elems)
    }
}

fn aligned_to(bytes: &[u8], align: usize) -> bool {
    (bytes as *const _ as *const () as usize) % align == 0
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSliceMut,
    T: ?Sized,
{
    // Get the underlying bytes mutably.
    #[inline]
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl<B, T> Deref for LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes,
{
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        // NOTE: This is safe because the lifetime of `self` is the same as the
        // lifetime of the return value, meaning that a) the returned reference
        // cannot outlive `self` and, b) no mutable methods on `self` can be
        // called during the lifetime of the returned reference. See the
        // documentation on `deref_helper` for what invariants we are required
        // to uphold.
        unsafe { self.deref_helper() }
    }
}

impl<B, T> DerefMut for LayoutVerified<B, T>
where
    B: ByteSliceMut,
    T: FromBytes + AsBytes,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // NOTE: This is safe because the lifetime of `self` is the same as the
        // lifetime of the return value, meaning that a) the returned reference
        // cannot outlive `self` and, b) no other methods on `self` can be
        // called during the lifetime of the returned reference. See the
        // documentation on `deref_mut_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_mut_helper() }
    }
}

impl<B, T> Deref for LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes,
{
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] {
        // NOTE: This is safe because the lifetime of `self` is the same as the
        // lifetime of the return value, meaning that a) the returned reference
        // cannot outlive `self` and, b) no mutable methods on `self` can be
        // called during the lifetime of the returned reference. See the
        // documentation on `deref_slice_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_slice_helper() }
    }
}

impl<B, T> DerefMut for LayoutVerified<B, [T]>
where
    B: ByteSliceMut,
    T: FromBytes + AsBytes,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        // NOTE: This is safe because the lifetime of `self` is the same as the
        // lifetime of the return value, meaning that a) the returned reference
        // cannot outlive `self` and, b) no other methods on `self` can be
        // called during the lifetime of the returned reference. See the
        // documentation on `deref_mut_slice_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_mut_slice_helper() }
    }
}

impl<T, B> Display for LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes + Display,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &T = self;
        inner.fmt(fmt)
    }
}

impl<T, B> Debug for LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes + Debug,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &T = self;
        fmt.debug_tuple("LayoutVerified").field(&inner).finish()
    }
}

impl<T, B> Display for LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes,
    [T]: Display,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &[T] = self;
        inner.fmt(fmt)
    }
}

impl<T, B> Debug for LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + Debug,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &[T] = self;
        fmt.debug_tuple("LayoutVerified").field(&inner).finish()
    }
}

mod sealed {
    use core::cell::{Ref, RefMut};

    pub trait Sealed {}
    impl<'a> Sealed for &'a [u8] {}
    impl<'a> Sealed for &'a mut [u8] {}
    impl<'a> Sealed for Ref<'a, [u8]> {}
    impl<'a> Sealed for RefMut<'a, [u8]> {}
}

// ByteSlice and ByteSliceMut abstract over [u8] references (&[u8], &mut [u8],
// Ref<[u8]>, RefMut<[u8]>, etc). We rely on various behaviors of these
// references such as that a given reference will never changes its length
// between calls to deref() or deref_mut(), and that split_at() works as
// expected. If ByteSlice or ByteSliceMut were not sealed, consumers could
// implement them in a way that violated these behaviors, and would break our
// unsafe code. Thus, we seal them and implement it only for known-good
// reference types. For the same reason, they're unsafe traits.

/// A mutable or immutable reference to a byte slice.
///
/// `ByteSlice` abstracts over the mutability of a byte slice reference, and is
/// implemented for various special reference types such as `Ref<[u8]>` and
/// `RefMut<[u8]>`.
pub unsafe trait ByteSlice: Deref<Target = [u8]> + Sized + self::sealed::Sealed {
    fn as_ptr(&self) -> *const u8;
    fn split_at(self, mid: usize) -> (Self, Self);
}

/// A mutable reference to a byte slice.
///
/// `ByteSliceMut` abstracts over various ways of storing a mutable reference to
/// a byte slice, and is implemented for various special reference types such as
/// `RefMut<[u8]>`.
pub unsafe trait ByteSliceMut: ByteSlice + DerefMut {
    fn as_mut_ptr(&mut self) -> *mut u8;
}

unsafe impl<'a> ByteSlice for &'a [u8] {
    fn as_ptr(&self) -> *const u8 {
        <[u8]>::as_ptr(self)
    }
    fn split_at(self, mid: usize) -> (Self, Self) {
        <[u8]>::split_at(self, mid)
    }
}
unsafe impl<'a> ByteSlice for &'a mut [u8] {
    fn as_ptr(&self) -> *const u8 {
        <[u8]>::as_ptr(self)
    }
    fn split_at(self, mid: usize) -> (Self, Self) {
        <[u8]>::split_at_mut(self, mid)
    }
}
unsafe impl<'a> ByteSlice for Ref<'a, [u8]> {
    fn as_ptr(&self) -> *const u8 {
        <[u8]>::as_ptr(self)
    }
    fn split_at(self, mid: usize) -> (Self, Self) {
        Ref::map_split(self, |slice| <[u8]>::split_at(slice, mid))
    }
}
unsafe impl<'a> ByteSlice for RefMut<'a, [u8]> {
    fn as_ptr(&self) -> *const u8 {
        <[u8]>::as_ptr(self)
    }
    fn split_at(self, mid: usize) -> (Self, Self) {
        RefMut::map_split(self, |slice| <[u8]>::split_at_mut(slice, mid))
    }
}

unsafe impl<'a> ByteSliceMut for &'a mut [u8] {
    fn as_mut_ptr(&mut self) -> *mut u8 {
        <[u8]>::as_mut_ptr(self)
    }
}
unsafe impl<'a> ByteSliceMut for RefMut<'a, [u8]> {
    fn as_mut_ptr(&mut self) -> *mut u8 {
        <[u8]>::as_mut_ptr(self)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unreadable_literal)]

    use core::ops::Deref;
    use core::ptr;

    use super::*;

    // B should be [u8; N]. T will require that the entire structure is aligned
    // to the alignment of T.
    #[derive(Default)]
    struct AlignedBuffer<T, B> {
        buf: B,
        _t: T,
    }

    impl<T, B: Default> AlignedBuffer<T, B> {
        fn clear_buf(&mut self) {
            self.buf = B::default();
        }
    }

    // convert a u64 to bytes using this platform's endianness
    fn u64_to_bytes(u: u64) -> [u8; 8] {
        unsafe { ptr::read(&u as *const u64 as *const [u8; 8]) }
    }

    // convert a u128 to bytes using this platform's endianness
    fn u128_to_bytes(u: u128) -> [u8; 16] {
        unsafe { ptr::read(&u as *const u128 as *const [u8; 16]) }
    }

    #[test]
    fn test_address() {
        // test that the Deref and DerefMut implementations return a reference which
        // points to the right region of memory

        let buf = [0];
        let lv = LayoutVerified::<_, u8>::new(&buf[..]).unwrap();
        let buf_ptr = buf.as_ptr();
        let deref_ptr = lv.deref() as *const u8;
        assert_eq!(buf_ptr, deref_ptr);

        let buf = [0];
        let lv = LayoutVerified::<_, [u8]>::new_slice(&buf[..]).unwrap();
        let buf_ptr = buf.as_ptr();
        let deref_ptr = lv.deref().as_ptr();
        assert_eq!(buf_ptr, deref_ptr);
    }

    // verify that values written to a LayoutVerified are properly shared
    // between the typed and untyped representations
    fn test_new_helper<'a>(mut lv: LayoutVerified<&'a mut [u8], u64>) {
        // assert that the value starts at 0
        assert_eq!(*lv, 0);

        // assert that values written to the typed value are reflected in the
        // byte slice
        const VAL1: u64 = 0xFF00FF00FF00FF00;
        *lv = VAL1;
        assert_eq!(lv.bytes(), &u64_to_bytes(VAL1));

        // assert that values written to the byte slice are reflected in the
        // typed value
        const VAL2: u64 = !VAL1; // different from VAL1
        lv.bytes_mut().copy_from_slice(&u64_to_bytes(VAL2)[..]);
        assert_eq!(*lv, VAL2);
    }

    // verify that values written to a LayoutVerified are properly shared
    // between the typed and untyped representations; pass a value with
    // byte length 16/typed length 2
    fn test_new_helper_slice<'a>(mut lv: LayoutVerified<&'a mut [u8], [u64]>) {
        // assert that the value starts at [0, 0]
        assert_eq!(*lv, [0, 0]);

        // assert that values written to the typed value are reflected in the
        // byte slice
        const VAL1: u64 = 0xFF00FF00FF00FF00;
        const VAL1_DOUBLED: u128 = 0xFF00FF00FF00FF00FF00FF00FF00FF00;
        lv[0] = VAL1;
        lv[1] = VAL1;
        assert_eq!(lv.bytes(), &u128_to_bytes(VAL1_DOUBLED));

        // assert that values written to the byte slice are reflected in the
        // typed value
        const VAL2: u64 = !VAL1; // different from VAL1
        const VAL2_DOUBLED: u128 = !VAL1_DOUBLED;
        lv.bytes_mut().copy_from_slice(&u128_to_bytes(VAL2_DOUBLED)[..]);
        assert_eq!(*lv, [VAL2, VAL2]);
    }

    // verify that values written to a LayoutVerified are properly shared
    // between the typed and untyped representations
    fn test_new_helper_unaligned<'a>(mut lv: LayoutVerified<&'a mut [u8], [u8; 8]>) {
        // assert that the value starts at 0
        assert_eq!(*lv, [0; 8]);

        // assert that values written to the typed value are reflected in the
        // byte slice
        const VAL1: [u8; 8] = [0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00];
        *lv = VAL1;
        assert_eq!(lv.bytes(), &VAL1);

        // assert that values written to the byte slice are reflected in the
        // typed value
        const VAL2: [u8; 8] = [0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF]; // different from VAL1
        lv.bytes_mut().copy_from_slice(&VAL2[..]);
        assert_eq!(*lv, VAL2);
    }

    // verify that values written to a LayoutVerified are properly shared
    // between the typed and untyped representations; pass a value with
    // length 16
    fn test_new_helper_slice_unaligned<'a>(mut lv: LayoutVerified<&'a mut [u8], [u8]>) {
        // assert that the value starts at [0; 16]
        assert_eq!(*lv, [0u8; 16][..]);

        // assert that values written to the typed value are reflected in the
        // byte slice
        const VAL1: [u8; 16] = [
            0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00,
            0xFF, 0x00,
        ];
        lv.copy_from_slice(&VAL1[..]);
        assert_eq!(lv.bytes(), &VAL1);

        // assert that values written to the byte slice are reflected in the
        // typed value
        const VAL2: [u8; 16] = [
            0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF,
            0x00, 0xFF,
        ];
        lv.bytes_mut().copy_from_slice(&VAL2[..]);
        assert_eq!(*lv, VAL2);
    }

    #[test]
    fn test_new_aligned_sized() {
        // Test that a properly-aligned, properly-sized buffer works for new,
        // new_from_preifx, and new_from_suffix, and that new_from_prefix and
        // new_from_suffix return empty slices. Test that a properly-aligned
        // buffer whose length is a multiple of the element size works for
        // new_slice. Test that xxx_zeroed behaves the same, and zeroes the
        // memory.

        // a buffer with an alignment of 8
        let mut buf = AlignedBuffer::<u64, [u8; 8]>::default();
        // buf.buf should be aligned to 8, so this should always succeed
        test_new_helper(LayoutVerified::<_, u64>::new(&mut buf.buf[..]).unwrap());
        buf.buf = [0xFFu8; 8];
        test_new_helper(LayoutVerified::<_, u64>::new_zeroed(&mut buf.buf[..]).unwrap());
        {
            // in a block so that lv and suffix don't live too long
            buf.clear_buf();
            let (lv, suffix) = LayoutVerified::<_, u64>::new_from_prefix(&mut buf.buf[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper(lv);
        }
        {
            buf.buf = [0xFFu8; 8];
            let (lv, suffix) =
                LayoutVerified::<_, u64>::new_from_prefix_zeroed(&mut buf.buf[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper(lv);
        }
        {
            buf.clear_buf();
            let (prefix, lv) = LayoutVerified::<_, u64>::new_from_suffix(&mut buf.buf[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper(lv);
        }
        {
            buf.buf = [0xFFu8; 8];
            let (prefix, lv) =
                LayoutVerified::<_, u64>::new_from_suffix_zeroed(&mut buf.buf[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper(lv);
        }

        // a buffer with alignment 8 and length 16
        let mut buf = AlignedBuffer::<u64, [u8; 16]>::default();
        // buf.buf should be aligned to 8 and have a length which is a multiple
        // of size_of::<u64>(), so this should always succeed
        test_new_helper_slice(LayoutVerified::<_, [u64]>::new_slice(&mut buf.buf[..]).unwrap());
        buf.buf = [0xFFu8; 16];
        test_new_helper_slice(
            LayoutVerified::<_, [u64]>::new_slice_zeroed(&mut buf.buf[..]).unwrap(),
        );
    }

    #[test]
    fn test_new_unaligned_sized() {
        // Test that an unaligned, properly-sized buffer works for
        // new_unaligned, new_unaligned_from_prefix, and
        // new_unaligned_from_suffix, and that new_unaligned_from_prefix
        // new_unaligned_from_suffix return empty slices. Test that an unaligned
        // buffer whose length is a multiple of the element size works for
        // new_slice. Test that xxx_zeroed behaves the same, and zeroes the
        // memory.

        let mut buf = [0u8; 8];
        test_new_helper_unaligned(
            LayoutVerified::<_, [u8; 8]>::new_unaligned(&mut buf[..]).unwrap(),
        );
        buf = [0xFFu8; 8];
        test_new_helper_unaligned(
            LayoutVerified::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf[..]).unwrap(),
        );
        {
            // in a block so that lv and suffix don't live too long
            buf = [0u8; 8];
            let (lv, suffix) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix(&mut buf[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper_unaligned(lv);
        }
        {
            buf = [0xFFu8; 8];
            let (lv, suffix) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf[..])
                    .unwrap();
            assert!(suffix.is_empty());
            test_new_helper_unaligned(lv);
        }
        {
            buf = [0u8; 8];
            let (prefix, lv) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix(&mut buf[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper_unaligned(lv);
        }
        {
            buf = [0xFFu8; 8];
            let (prefix, lv) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf[..])
                    .unwrap();
            assert!(prefix.is_empty());
            test_new_helper_unaligned(lv);
        }

        let mut buf = [0u8; 16];
        // buf.buf should be aligned to 8 and have a length which is a multiple
        // of size_of::<u64>(), so this should always succeed
        test_new_helper_slice_unaligned(
            LayoutVerified::<_, [u8]>::new_slice(&mut buf[..]).unwrap(),
        );
        buf = [0xFFu8; 16];
        test_new_helper_slice_unaligned(
            LayoutVerified::<_, [u8]>::new_slice_zeroed(&mut buf[..]).unwrap(),
        );
    }

    #[test]
    fn test_new_oversized() {
        // Test that a properly-aligned, overly-sized buffer works for
        // new_from_prefix and new_from_suffix, and that they return the
        // remainder and prefix of the slice respectively. Test that xxx_zeroed
        // behaves the same, and zeroes the memory.

        let mut buf = AlignedBuffer::<u64, [u8; 16]>::default();
        {
            // in a block so that lv and suffix don't live too long
            // buf.buf should be aligned to 8, so this should always succeed
            let (lv, suffix) = LayoutVerified::<_, u64>::new_from_prefix(&mut buf.buf[..]).unwrap();
            assert_eq!(suffix.len(), 8);
            test_new_helper(lv);
        }
        {
            buf.buf = [0xFFu8; 16];
            // buf.buf should be aligned to 8, so this should always succeed
            let (lv, suffix) =
                LayoutVerified::<_, u64>::new_from_prefix_zeroed(&mut buf.buf[..]).unwrap();
            // assert that the suffix wasn't zeroed
            assert_eq!(suffix, &[0xFFu8; 8]);
            test_new_helper(lv);
        }
        {
            buf.clear_buf();
            // buf.buf should be aligned to 8, so this should always succeed
            let (prefix, lv) = LayoutVerified::<_, u64>::new_from_suffix(&mut buf.buf[..]).unwrap();
            assert_eq!(prefix.len(), 8);
            test_new_helper(lv);
        }
        {
            buf.buf = [0xFFu8; 16];
            // buf.buf should be aligned to 8, so this should always succeed
            let (prefix, lv) =
                LayoutVerified::<_, u64>::new_from_suffix_zeroed(&mut buf.buf[..]).unwrap();
            // assert that the prefix wasn't zeroed
            assert_eq!(prefix, &[0xFFu8; 8]);
            test_new_helper(lv);
        }
    }

    #[test]
    fn test_new_unaligned_oversized() {
        // Test than an unaligned, overly-sized buffer works for
        // new_unaligned_from_prefix and new_unaligned_from_suffix, and that
        // they return the remainder and prefix of the slice respectively. Test
        // that xxx_zeroed behaves the same, and zeroes the memory.

        let mut buf = [0u8; 16];
        {
            // in a block so that lv and suffix don't live too long
            let (lv, suffix) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix(&mut buf[..]).unwrap();
            assert_eq!(suffix.len(), 8);
            test_new_helper_unaligned(lv);
        }
        {
            buf = [0xFFu8; 16];
            let (lv, suffix) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf[..])
                    .unwrap();
            // assert that the suffix wasn't zeroed
            assert_eq!(suffix, &[0xFF; 8]);
            test_new_helper_unaligned(lv);
        }
        {
            buf = [0u8; 16];
            let (prefix, lv) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix(&mut buf[..]).unwrap();
            assert_eq!(prefix.len(), 8);
            test_new_helper_unaligned(lv);
        }
        {
            buf = [0xFFu8; 16];
            let (prefix, lv) =
                LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf[..])
                    .unwrap();
            // assert that the prefix wasn't zeroed
            assert_eq!(prefix, &[0xFF; 8]);
            test_new_helper_unaligned(lv);
        }
    }

    #[test]
    #[allow(clippy::cyclomatic_complexity)]
    fn test_new_error() {
        // fail because the buffer is too large

        // a buffer with an alignment of 8
        let mut buf = AlignedBuffer::<u64, [u8; 16]>::default();
        // buf.buf should be aligned to 8, so only the length check should fail
        assert!(LayoutVerified::<_, u64>::new(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_zeroed(&mut buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf.buf[..]).is_none());

        // fail because the buffer is too small

        // a buffer with an alignment of 8
        let mut buf = AlignedBuffer::<u64, [u8; 4]>::default();
        // buf.buf should be aligned to 8, so only the length check should fail
        assert!(LayoutVerified::<_, u64>::new(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_zeroed(&mut buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_prefix(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_prefix_zeroed(&mut buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_suffix(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_suffix_zeroed(&mut buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf.buf[..])
            .is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf.buf[..])
            .is_none());

        // fail because the length is not a multiple of the element size

        let mut buf = AlignedBuffer::<u64, [u8; 12]>::default();
        // buf.buf has length 12, but element size is 8
        assert!(LayoutVerified::<_, [u64]>::new_slice(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_zeroed(&mut buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned(&buf.buf[..]).is_none());
        assert!(
            LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_zeroed(&mut buf.buf[..]).is_none()
        );

        // fail because the alignment is insufficient

        // a buffer with an alignment of 8
        let mut buf = AlignedBuffer::<u64, [u8; 12]>::default();
        // slicing from 4, we get a buffer with size 8 (so the length check
        // should succeed) but an alignment of only 4, which is insufficient
        assert!(LayoutVerified::<_, u64>::new(&buf.buf[4..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_zeroed(&mut buf.buf[4..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_prefix(&buf.buf[4..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_prefix_zeroed(&mut buf.buf[4..]).is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice(&buf.buf[4..]).is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_zeroed(&mut buf.buf[4..]).is_none());
        // slicing from 4 should be unnecessary because new_from_suffix[_zeroed]
        // use the suffix of the slice
        assert!(LayoutVerified::<_, u64>::new_from_suffix(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_suffix_zeroed(&mut buf.buf[..]).is_none());
    }

    #[test]
    #[should_panic]
    fn test_new_slice_zst_panics() {
        LayoutVerified::<_, [()]>::new_slice(&[0u8][..]);
    }

    #[test]
    #[should_panic]
    fn test_new_slice_zeroed_zst_panics() {
        LayoutVerified::<_, [()]>::new_slice_zeroed(&mut [0u8][..]);
    }

    #[test]
    #[should_panic]
    fn test_new_slice_unaligned_zst_panics() {
        LayoutVerified::<_, [()]>::new_slice_unaligned(&[0u8][..]);
    }

    #[test]
    #[should_panic]
    fn test_new_slice_unaligned_zeroed_zst_panics() {
        LayoutVerified::<_, [()]>::new_slice_unaligned_zeroed(&mut [0u8][..]);
    }

    #[test]
    fn test_as_bytes_methods() {
        #[derive(Debug, Eq, PartialEq, FromBytes, AsBytes)]
        #[repr(C)]
        struct Foo {
            a: u32,
            b: u32,
        }

        let mut foo = Foo { a: 1, b: 2 };
        // Test that we can access the underlying bytes, and that we get the
        // right bytes and the right number of bytes.
        assert_eq!(foo.as_bytes(), [1, 0, 0, 0, 2, 0, 0, 0]);
        // Test that changes to the underlying byte slices are reflected in the
        // original object.
        foo.as_bytes_mut()[0] = 3;
        assert_eq!(foo, Foo { a: 3, b: 2 });

        // Do the same tests for a slice, which ensures that this logic works
        // for unsized types as well.
        let foo = &mut [Foo { a: 1, b: 2 }, Foo { a: 3, b: 4 }];
        assert_eq!(foo.as_bytes(), [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0]);
        foo.as_bytes_mut()[8] = 5;
        assert_eq!(foo, &mut [Foo { a: 1, b: 2 }, Foo { a: 5, b: 4 }]);
    }

    #[test]
    fn test_array() {
        // This is a hack, as per above in `test_as_bytes_methods`.
        mod zerocopy {
            pub use crate::*;
        }
        #[derive(FromBytes, AsBytes)]
        #[repr(C)]
        struct Foo {
            a: [u16; 33],
        }

        let foo = Foo { a: [0xFFFF; 33] };
        let expected = [0xFFu8; 66];
        assert_eq!(foo.as_bytes(), &expected[..]);
    }

    #[test]
    fn test_display_debug() {
        let buf = AlignedBuffer::<u64, [u8; 8]>::default();
        let lv = LayoutVerified::<_, u64>::new(&buf.buf[..]).unwrap();
        assert_eq!(format!("{}", lv), "0");
        assert_eq!(format!("{:?}", lv), "LayoutVerified(0)");

        let buf = AlignedBuffer::<u64, [u8; 8]>::default();
        let lv = LayoutVerified::<_, [u64]>::new_slice(&buf.buf[..]).unwrap();
        assert_eq!(format!("{:?}", lv), "LayoutVerified([0])");
    }
}
