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
//!
//! # Features
//!
//! `alloc`: By default, `zerocopy` is `no_std`. When the `alloc` feature is
//! enabled, the `alloc` crate is added as a dependency, and some
//! allocation-related functionality is added.
//!
//! `simd`: When the `simd` feature is enabled, `FromBytes` and `AsBytes` impls
//! are emitted for all stable SIMD types which exist on the target platform.
//! Note that the layout of SIMD types is not yet stabilized, so these impls may
//! be removed in the future if layout changes make them invalid. For more
//! information, see the Unsafe Code Guidelines Reference page on the [Layout of
//! packed SIMD vectors][simd-layout].
//!
//! `simd-nightly`: Enables the `simd` feature and adds support for SIMD types
//! which are only available on nightly. Since these types are unstable, support
//! for any type may be removed at any point in the future.
//!
//! [simd-layout]: https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html

#![deny(missing_docs)]
#![cfg_attr(not(test), no_std)]
#![recursion_limit = "2048"]

pub mod byteorder;

pub use crate::byteorder::*;
pub use zerocopy_derive::*;

use core::cell::{Ref, RefMut};
use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;
use core::mem;
use core::ops::{Deref, DerefMut};
use core::ptr;
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
        unsafe impl<T: $trait, const N: usize> $trait for [T; N] {
            fn only_derive_is_allowed_to_implement_this_trait()
            where
                Self: Sized,
            {
            }
        }
    };
}

/// Implements `$trait` for one or more `$type`s.
macro_rules! impl_for_types {
    ($trait:ident, $type:ty) => (
        unsafe impl $trait for $type {
            fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
        }
    );
    ($trait:ident, $type:ty, $($types:ty),*) => (
        unsafe impl $trait for $type {
            fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
        }
        impl_for_types!($trait, $($types),*);
    );
}

/// Implements `$trait` for all signed and unsigned primitive types.
macro_rules! impl_for_primitives {
    ($trait:ident) => {
        impl_for_types!(
            $trait, u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, f32, f64
        );
    };
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

    /// Reads a copy of `Self` from `bytes`.
    ///
    /// If `bytes.len() != size_of::<Self>()`, `read_from` returns `None`.
    fn read_from<B: ByteSlice>(bytes: B) -> Option<Self>
    where
        Self: Sized,
    {
        let lv = LayoutVerified::<_, Unalign<Self>>::new_unaligned(bytes)?;
        Some(lv.read().into_inner())
    }

    /// Reads a copy of `Self` from the prefix of `bytes`.
    ///
    /// `read_from_prefix` reads a `Self` from the first `size_of::<Self>()`
    /// bytes of `bytes`. If `bytes.len() < size_of::<Self>()`, it returns
    /// `None`.
    fn read_from_prefix<B: ByteSlice>(bytes: B) -> Option<Self>
    where
        Self: Sized,
    {
        let (lv, _suffix) = LayoutVerified::<_, Unalign<Self>>::new_unaligned_from_prefix(bytes)?;
        Some(lv.read().into_inner())
    }

    /// Reads a copy of `Self` from the suffix of `bytes`.
    ///
    /// `read_from_suffix` reads a `Self` from the last `size_of::<Self>()`
    /// bytes of `bytes`. If `bytes.len() < size_of::<Self>()`, it returns
    /// `None`.
    fn read_from_suffix<B: ByteSlice>(bytes: B) -> Option<Self>
    where
        Self: Sized,
    {
        let (_prefix, lv) = LayoutVerified::<_, Unalign<Self>>::new_unaligned_from_suffix(bytes)?;
        Some(lv.read().into_inner())
    }

    /// Creates an instance of `Self` from zeroed bytes.
    fn new_zeroed() -> Self
    where
        Self: Sized,
    {
        unsafe {
            // Safe because FromBytes says all bit patterns (including zeroes)
            // are legal.
            core::mem::zeroed()
        }
    }

    /// Creates a `Box<Self>` from zeroed bytes.
    ///
    /// This function is useful for allocating large values on the heap and
    /// zero-initializing them, without ever creating a temporary instance of
    /// `Self` on the stack. For example, `<[u8; 1048576]>::new_box_zeroed()`
    /// will allocate `[u8; 1048576]` directly on the heap; it does not require
    /// storing `[u8; 1048576]` in a temporary variable on the stack.
    ///
    /// On systems that use a heap implementation that supports allocating from
    /// pre-zeroed memory, using `new_box_zeroed` (or related functions) may
    /// have performance benefits.
    ///
    /// Note that `Box<Self>` can be converted to `Arc<Self>` and other
    /// container types without reallocation.
    ///
    /// # Panics
    ///
    /// Panics if allocation of `size_of::<Self>()` bytes fails.
    #[cfg(any(test, feature = "alloc"))]
    fn new_box_zeroed() -> Box<Self>
    where
        Self: Sized,
    {
        // If T is a ZST, then return a proper boxed instance of it. There is no
        // allocation, but Box does require a correct dangling pointer.
        let layout = Layout::new::<Self>();
        if layout.size() == 0 {
            return Box::new(Self::new_zeroed());
        }

        unsafe {
            let ptr = alloc::alloc::alloc_zeroed(layout) as *mut Self;
            if ptr.is_null() {
                alloc::alloc::handle_alloc_error(layout);
            }
            Box::from_raw(ptr)
        }
    }

    /// Creates a `Box<[Self]>` (a boxed slice) from zeroed bytes.
    ///
    /// This function is useful for allocating large values of `[Self]` on the
    /// heap and zero-initializing them, without ever creating a temporary
    /// instance of `[Self; _]` on the stack. For example,
    /// `u8::new_box_slice_zeroed(1048576)` will allocate the slice directly on
    /// the heap; it does not require storing the slice on the stack.
    ///
    /// On systems that use a heap implementation that supports allocating from
    /// pre-zeroed memory, using `new_box_slice_zeroed` may have performance
    /// benefits.
    ///
    /// If `Self` is a zero-sized type, then this function will return a
    /// `Box<[Self]>` that has the correct `len`. Such a box cannot contain any
    /// actual information, but its `len()` property will report the correct
    /// value.
    ///
    /// # Panics
    ///
    /// * Panics if `size_of::<Self>() * len` overflows.
    /// * Panics if allocation of `size_of::<Self>() * len` bytes fails.
    #[cfg(any(test, feature = "alloc"))]
    fn new_box_slice_zeroed(len: usize) -> Box<[Self]>
    where
        Self: Sized,
    {
        // TODO(https://fxbug.dev/80757): Use Layout::repeat() when `alloc_layout_extra` is stabilized
        // This will intentionally panic if it overflows.
        unsafe {
            // from_size_align_unchecked() is sound because slice_len_bytes is
            // guaranteed to be properly aligned (we just multiplied it by
            // size_of::<T>(), which is guaranteed to be aligned).
            let layout = Layout::from_size_align_unchecked(
                size_of::<Self>().checked_mul(len).unwrap(),
                align_of::<Self>(),
            );
            if layout.size() != 0 {
                let ptr = alloc::alloc::alloc_zeroed(layout) as *mut Self;
                if ptr.is_null() {
                    alloc::alloc::handle_alloc_error(layout);
                }
                Box::from_raw(core::slice::from_raw_parts_mut(ptr, len))
            } else {
                // Box<[T]> does not allocate when T is zero-sized or when len
                // is zero, but it does require a non-null dangling pointer for
                // its allocation.
                Box::from_raw(core::slice::from_raw_parts_mut(
                    NonNull::<Self>::dangling().as_ptr(),
                    len,
                ))
            }
        }
    }
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

    /// Gets the bytes of this value.
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

    /// Gets the bytes of this value mutably.
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

    /// Writes a copy of `self` to `bytes`.
    ///
    /// If `bytes.len() != size_of_val(self)`, `write_to` returns `None`.
    fn write_to<B: ByteSliceMut>(&self, mut bytes: B) -> Option<()> {
        if bytes.len() != mem::size_of_val(self) {
            return None;
        }

        bytes.copy_from_slice(self.as_bytes());
        Some(())
    }

    /// Writes a copy of `self` to the prefix of `bytes`.
    ///
    /// `write_to_prefix` writes `self` to the first `size_of_val(self)` bytes
    /// of `bytes`. If `bytes.len() < size_of_val(self)`, it returns `None`.
    fn write_to_prefix<B: ByteSliceMut>(&self, mut bytes: B) -> Option<()> {
        let size = mem::size_of_val(self);
        if bytes.len() < size {
            return None;
        }

        bytes[..size].copy_from_slice(self.as_bytes());
        Some(())
    }

    /// Writes a copy of `self` to the suffix of `bytes`.
    ///
    /// `write_to_suffix` writes `self` to the last `size_of_val(self)` bytes
    /// of `bytes`. If `bytes.len() < size_of_val(self)`, it returns `None`.
    fn write_to_suffix<B: ByteSliceMut>(&self, mut bytes: B) -> Option<()> {
        let start = bytes.len().checked_sub(mem::size_of_val(self))?;
        bytes[start..].copy_from_slice(self.as_bytes());
        Some(())
    }
}

// Special case for bool (it is not included in `impl_for_primitives!`).
impl_for_types!(AsBytes, bool);

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

impl_for_types!(Unaligned, u8, i8);
impl_for_composite_types!(Unaligned);

// SIMD support
//
// Per the Unsafe Code Guidelines Reference [1]:
//
//   Packed SIMD vector types are `repr(simd)` homogeneous tuple-structs
//   containing `N` elements of type `T` where `N` is a power-of-two and the
//   size and alignment requirements of `T` are equal:
//
//   ```rust
//   #[repr(simd)]
//   struct Vector<T, N>(T_0, ..., T_(N - 1));
//   ```
//
//   ...
//
//   The size of `Vector` is `N * size_of::<T>()` and its alignment is an
//   implementation-defined function of `T` and `N` greater than or equal to
//   `align_of::<T>()`.
//
//   ...
//
//   Vector elements are laid out in source field order, enabling random access
//   to vector elements by reinterpreting the vector as an array:
//
//   ```rust
//   union U {
//      vec: Vector<T, N>,
//      arr: [T; N]
//   }
//
//   assert_eq!(size_of::<Vector<T, N>>(), size_of::<[T; N]>());
//   assert!(align_of::<Vector<T, N>>() >= align_of::<[T; N]>());
//
//   unsafe {
//     let u = U { vec: Vector<T, N>(t_0, ..., t_(N - 1)) };
//
//     assert_eq!(u.vec.0, u.arr[0]);
//     // ...
//     assert_eq!(u.vec.(N - 1), u.arr[N - 1]);
//   }
//   ```
//
// Given this background, we can observe that:
// - The size and bit pattern requirements of a SIMD type are equivalent to the
//   equivalent array type. Thus, for any SIMD type whose primitive `T` is
//   `FromBytes`, that SIMD type is also `FromBytes`. The same holds for
//   `AsBytes`.
// - Since no upper bound is placed on the alignment, no SIMD type can be
//   guaranteed to be `Unaligned`.
//
// Also per [1]:
//
//   This chapter represents the consensus from issue #38. The statements in
//   here are not (yet) "guaranteed" not to change until an RFC ratifies them.
//
// See issue #38 [2]. While this behavior is not technically guaranteed, the
// likelihood that the behavior will change such that SIMD types are no longer
// `FromBytes` or `AsBytes` is next to zero, as that would defeat the entire
// purpose of SIMD types. Nonetheless, we put this behavior behind the `simd`
// Cargo feature, which requires consumers to opt into this stability hazard.
//
// [1] https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
// [2] https://github.com/rust-lang/unsafe-code-guidelines/issues/38
#[cfg(feature = "simd")]
mod simd {
    /// Defines a module which implements `FromBytes` and `AsBytes` for a set of
    /// types from a module in `core::arch`.
    ///
    /// `$arch` is both the name of the defined module and the name of the
    /// module in `core::arch`, and `$typ` is the list of items from that module
    /// to implement `FromBytes` and `AsBytes` for.
    macro_rules! simd_arch_mod {
        ($arch:ident, $($typ:ident),*) => {
            mod $arch {
                use core::arch::$arch::{$($typ),*};

                use crate::*;

                impl_for_types!(FromBytes, $($typ),*);
                impl_for_types!(AsBytes, $($typ),*);
            }
        };
    }

    #[cfg(target_arch = "x86")]
    simd_arch_mod!(x86, __m128, __m128d, __m128i, __m256, __m256d, __m256i);
    #[cfg(target_arch = "x86_64")]
    simd_arch_mod!(x86_64, __m128, __m128d, __m128i, __m256, __m256d, __m256i);
    #[cfg(target_arch = "wasm32")]
    simd_arch_mod!(wasm32, v128);
    #[cfg(all(feature = "simd-nightly", target_arch = "powerpc"))]
    simd_arch_mod!(
        powerpc,
        vector_bool_long,
        vector_double,
        vector_signed_long,
        vector_unsigned_long
    );
    #[cfg(all(feature = "simd-nightly", target_arch = "powerpc64"))]
    simd_arch_mod!(
        powerpc64,
        vector_bool_long,
        vector_double,
        vector_signed_long,
        vector_unsigned_long
    );
    #[cfg(all(feature = "simd-nightly", target_arch = "aarch64"))]
    #[rustfmt::skip]
    simd_arch_mod!(
        aarch64, float32x2_t, float32x4_t, float64x1_t, float64x2_t, int8x8_t, int8x8x2_t,
        int8x8x3_t, int8x8x4_t, int8x16_t, int8x16x2_t, int8x16x3_t, int8x16x4_t, int16x4_t,
        int16x8_t, int32x2_t, int32x4_t, int64x1_t, int64x2_t, poly8x8_t, poly8x8x2_t, poly8x8x3_t,
        poly8x8x4_t, poly8x16_t, poly8x16x2_t, poly8x16x3_t, poly8x16x4_t, poly16x4_t, poly16x8_t,
        poly64x1_t, poly64x2_t, uint8x8_t, uint8x8x2_t, uint8x8x3_t, uint8x8x4_t, uint8x16_t,
        uint8x16x2_t, uint8x16x3_t, uint8x16x4_t, uint16x4_t, uint16x8_t, uint32x2_t, uint32x4_t,
        uint64x1_t, uint64x2_t
    );
    #[cfg(all(feature = "simd-nightly", target_arch = "arm"))]
    #[rustfmt::skip]
    simd_arch_mod!(
        arm, float32x2_t, float32x4_t, int8x4_t, int8x8_t, int8x8x2_t, int8x8x3_t, int8x8x4_t,
        int8x16_t, int16x2_t, int16x4_t, int16x8_t, int32x2_t, int32x4_t, int64x1_t, int64x2_t,
        poly8x8_t, poly8x8x2_t, poly8x8x3_t, poly8x8x4_t, poly8x16_t, poly16x4_t, poly16x8_t,
        poly64x1_t, poly64x2_t, uint8x4_t, uint8x8_t, uint8x8x2_t, uint8x8x3_t, uint8x8x4_t,
        uint8x16_t, uint16x2_t, uint16x4_t, uint16x8_t, uint32x2_t, uint32x4_t, uint64x1_t,
        uint64x2_t
    );
}

/// A type with no alignment requirement.
///
/// A `Unalign` wraps a `T`, removing any alignment requirement. `Unalign<T>`
/// has the same size and ABI as `T`, but not necessarily the same alignment.
/// This is useful if a type with an alignment requirement needs to be read from
/// a chunk of memory which provides no alignment guarantees.
///
/// Since `Unalign` has no alignment requirement, the inner `T` may not be
/// properly aligned in memory, and so `Unalign` provides no way of getting a
/// reference to the inner `T`. Instead, the `T` may only be obtained by value
/// (see [`get`] and [`into_inner`]).
///
/// [`get`]: Unalign::get
/// [`into_inner`]: Unalign::into_inner
#[derive(FromBytes, Unaligned, Copy)]
#[repr(C, packed)]
pub struct Unalign<T>(T);

// Note that `Unalign: Clone` only if `T: Copy`. Since the inner `T` may not be
// aligned, there's no way to safely call `T::clone`, and so a `T: Clone` bound
// is not sufficient to implement `Clone` for `Unalign`.
impl<T: Copy> Clone for Unalign<T> {
    fn clone(&self) -> Unalign<T> {
        *self
    }
}

impl<T> Unalign<T> {
    /// Constructs a new `Unalign`.
    pub fn new(val: T) -> Unalign<T> {
        Unalign(val)
    }

    /// Consumes `self`, returning the inner `T`.
    pub fn into_inner(self) -> T {
        let Unalign(val) = self;
        val
    }

    /// Gets an unaligned raw pointer to the inner `T`.
    ///
    /// # Safety
    ///
    /// The returned raw pointer is not necessarily aligned to
    /// `align_of::<T>()`. Most functions which operate on raw pointers require
    /// those pointers to be aligned, so calling those functions with the result
    /// of `get_ptr` will be undefined behavior if alignment is not guaranteed
    /// using some out-of-band mechanism. In general, the only functions which
    /// are safe to call with this pointer are which that are explicitly
    /// documented as being sound to use with an unaligned pointer, such as
    /// [`read_unaligned`].
    ///
    /// [`read_unaligned`]: core::ptr::read_unaligned
    pub fn get_ptr(&self) -> *const T {
        ptr::addr_of!(self.0)
    }

    /// Gets an unaligned mutable raw pointer to the inner `T`.
    ///
    /// # Safety
    ///
    /// The returned raw pointer is not necessarily aligned to
    /// `align_of::<T>()`. Most functions which operate on raw pointers require
    /// those pointers to be aligned, so calling those functions with the result
    /// of `get_ptr` will be undefined behavior if alignment is not guaranteed
    /// using some out-of-band mechanism. In general, the only functions which
    /// are safe to call with this pointer are those which are explicitly
    /// documented as being sound to use with an unaligned pointer, such as
    /// [`read_unaligned`].
    ///
    /// [`read_unaligned`]: core::ptr::read_unaligned
    pub fn get_mut_ptr(&mut self) -> *mut T {
        ptr::addr_of_mut!(self.0)
    }
}

impl<T: Copy> Unalign<T> {
    /// Gets a copy of the inner `T`.
    pub fn get(&self) -> T {
        let Unalign(val) = *self;
        val
    }
}

// SAFETY: Since `T: AsBytes`, we know that it's safe to construct a `&[u8]`
// from an aligned `&T`. Since `&[u8]` itself has no alignment requirements, it
// must also be safe to construct a `&[u8]` from a `&T` at any address. Since
// `Unalign<T>` is `#[repr(packed)]`, everything about its layout except for its
// alignment is the same as `T`'s layout.
unsafe impl<T: AsBytes> AsBytes for Unalign<T> {
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }
}

// Used in `transmute!` below.
#[doc(hidden)]
pub use core::mem::transmute as __real_transmute;

/// Safely transmutes a value of one type to a value of another type of the same
/// size.
///
/// The expression `$e` must have a concrete type, `T`, which implements
/// `AsBytes`. The `transmute!` expression must also have a concrete type, `U`
/// (`U` is inferred from the calling context), and `U` must implement
/// `FromBytes`.
///
/// Note that the `T` produced by the expression `$e` will *not* be dropped.
/// Semantically, its bits will be copied into a new value of type `U`, the
/// original `T` will be forgotten, and the value of type `U` will be returned.
#[macro_export]
macro_rules! transmute {
    ($e:expr) => {{
        // NOTE: This must be a macro (rather than a function with trait bounds)
        // because there's no way, in a generic context, to enforce that two
        // types have the same size. `core::mem::transmute` uses compiler magic
        // to enforce this so long as the types are concrete.

        let e = $e;
        if false {
            // This branch, though never taken, ensures that the type of `e` is
            // `AsBytes` and that the type of this macro invocation expression
            // is `FromBytes`.
            fn transmute<T: $crate::AsBytes, U: $crate::FromBytes>(_t: T) -> U {
                unreachable!()
            }
            transmute(e)
        } else {
            // `core::mem::transmute` ensures that the type of `e` and the type
            // of this macro invocation expression have the same size. We know
            // this transmute is safe thanks to the `AsBytes` and `FromBytes`
            // bounds enforced by the `false` branch.
            //
            // We use `$crate::__real_transmute` because we know it will always
            // be available for crates which are using the 2015 edition of Rust.
            // By contrast, if we were to use `std::mem::transmute`, this macro
            // would not work for such crates in `no_std` contexts, and if we
            // were to use `core::mem::transmute`, this macro would not work in
            // `std` contexts in which `core` was not manually imported. This is
            // not a problem for 2018 edition crates.
            unsafe { $crate::__real_transmute(e) }
        }
    }}
}

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
    /// Constructs a new `LayoutVerified`.
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

    /// Constructs a new `LayoutVerified` from the prefix of a byte slice.
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

    /// Constructs a new `LayoutVerified` from the suffix of a byte slice.
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

impl<B, T> LayoutVerified<B, [T]>
where
    B: ByteSlice,
{
    /// Constructs a new `LayoutVerified` of a slice type.
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

    /// Constructs a new `LayoutVerified` of a slice type from the prefix of a
    /// byte slice.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// first `size_of::<T>() * count` bytes from `bytes` to construct a
    /// `LayoutVerified`, and returns the remaining bytes to the caller. It also
    /// ensures that `sizeof::<T>() * count` does not overflow a `usize`. If any
    /// of the length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_from_prefix` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_from_prefix(bytes: B, count: usize) -> Option<(LayoutVerified<B, [T]>, B)> {
        let expected_len = match mem::size_of::<T>().checked_mul(count) {
            Some(len) => len,
            None => return None,
        };
        if bytes.len() < expected_len {
            return None;
        }
        let (prefix, bytes) = bytes.split_at(expected_len);
        Self::new_slice(prefix).map(move |l| (l, bytes))
    }

    /// Constructs a new `LayoutVerified` of a slice type from the suffix of a
    /// byte slice.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// last `size_of::<T>() * count` bytes from `bytes` to construct a
    /// `LayoutVerified`, and returns the preceding bytes to the caller. It also
    /// ensures that `sizeof::<T>() * count` does not overflow a `usize`. If any
    /// of the length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_from_suffix` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_from_suffix(bytes: B, count: usize) -> Option<(B, LayoutVerified<B, [T]>)> {
        let expected_len = match mem::size_of::<T>().checked_mul(count) {
            Some(len) => len,
            None => return None,
        };
        if bytes.len() < expected_len {
            return None;
        }
        let (bytes, suffix) = bytes.split_at(expected_len);
        Self::new_slice(suffix).map(move |l| (bytes, l))
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
    /// Constructs a new `LayoutVerified` after zeroing the bytes.
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

    /// Constructs a new `LayoutVerified` from the prefix of a byte slice,
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

    /// Constructs a new `LayoutVerified` from the suffix of a byte slice,
    /// zeroing the suffix.
    ///
    /// `new_from_suffix_zeroed` verifies that `bytes.len() >= size_of::<T>()`
    /// and that the last `size_of::<T>()` bytes of `bytes` are aligned to
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
    /// Constructs a new `LayoutVerified` of a slice type after zeroing the
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

    /// Constructs a new `LayoutVerified` of a slice type from the prefix of a
    /// byte slice, after zeroing the bytes.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// first `size_of::<T>() * count` bytes from `bytes` to construct a
    /// `LayoutVerified`, and returns the remaining bytes to the caller. It also
    /// ensures that `sizeof::<T>() * count` does not overflow a `usize`. If any
    /// of the length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// If the checks succeed, then the suffix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_from_prefix_zeroed` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_from_prefix_zeroed(
        bytes: B,
        count: usize,
    ) -> Option<(LayoutVerified<B, [T]>, B)> {
        map_prefix_tuple_zeroed(Self::new_slice_from_prefix(bytes, count))
    }

    /// Constructs a new `LayoutVerified` of a slice type from the prefix of a
    /// byte slice, after zeroing the bytes.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// last `size_of::<T>() * count` bytes from `bytes` to construct a
    /// `LayoutVerified`, and returns the preceding bytes to the caller. It also
    /// ensures that `sizeof::<T>() * count` does not overflow a `usize`. If any
    /// of the length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// If the checks succeed, then the consumed suffix will be initialized to
    /// zero. This can be useful when re-using buffers to ensure that sensitive
    /// data previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_from_suffix_zeroed` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_from_suffix_zeroed(
        bytes: B,
        count: usize,
    ) -> Option<(B, LayoutVerified<B, [T]>)> {
        map_suffix_tuple_zeroed(Self::new_slice_from_suffix(bytes, count))
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSlice,
    T: Unaligned,
{
    /// Constructs a new `LayoutVerified` for a type with no alignment
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

    /// Constructs a new `LayoutVerified` from the prefix of a byte slice for a
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

    /// Constructs a new `LayoutVerified` from the suffix of a byte slice for a
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
    /// Constructs a new `LayoutVerified` of a slice type with no alignment
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

    /// Constructs a new `LayoutVerified` of a slice type with no alignment
    /// requirement from the prefix of a byte slice.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the first `size_of::<T>() * count` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the remaining bytes
    /// to the caller. It also ensures that `sizeof::<T>() * count` does not
    /// overflow a `usize`. If either the length, or overflow checks fail, it
    /// returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_prefix` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_unaligned_from_prefix(
        bytes: B,
        count: usize,
    ) -> Option<(LayoutVerified<B, [T]>, B)> {
        let expected_len = match mem::size_of::<T>().checked_mul(count) {
            Some(len) => len,
            None => return None,
        };
        if bytes.len() < expected_len {
            return None;
        }
        let (prefix, bytes) = bytes.split_at(expected_len);
        Self::new_slice_unaligned(prefix).map(move |l| (l, bytes))
    }

    /// Constructs a new `LayoutVerified` of a slice type with no alignment
    /// requirement from the suffix of a byte slice.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the last `size_of::<T>() * count` bytes from `bytes`
    /// to construct a `LayoutVerified`, and returns the remaining bytes to the
    /// caller. It also ensures that `sizeof::<T>() * count` does not overflow a
    /// `usize`. If either the length, or overflow checks fail, it returns
    /// `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_suffix` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_unaligned_from_suffix(
        bytes: B,
        count: usize,
    ) -> Option<(B, LayoutVerified<B, [T]>)> {
        let expected_len = match mem::size_of::<T>().checked_mul(count) {
            Some(len) => len,
            None => return None,
        };
        if bytes.len() < expected_len {
            return None;
        }
        let (bytes, suffix) = bytes.split_at(expected_len);
        Self::new_slice_unaligned(suffix).map(move |l| (bytes, l))
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSliceMut,
    T: Unaligned,
{
    /// Constructs a new `LayoutVerified` for a type with no alignment
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

    /// Constructs a new `LayoutVerified` from the prefix of a byte slice for a
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

    /// Constructs a new `LayoutVerified` from the suffix of a byte slice for a
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
    /// Constructs a new `LayoutVerified` for a slice type with no alignment
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

    /// Constructs a new `LayoutVerified` of a slice type with no alignment
    /// requirement from the prefix of a byte slice, after zeroing the bytes.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the first `size_of::<T>() * count` bytes from
    /// `bytes` to construct a `LayoutVerified`, and returns the remaining bytes
    /// to the caller. It also ensures that `sizeof::<T>() * count` does not
    /// overflow a `usize`. If either the length, or overflow checks fail, it
    /// returns `None`.
    ///
    /// If the checks succeed, then the prefix will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_prefix_zeroed` panics if `T` is a zero-sized
    /// type.
    #[inline]
    pub fn new_slice_unaligned_from_prefix_zeroed(
        bytes: B,
        count: usize,
    ) -> Option<(LayoutVerified<B, [T]>, B)> {
        map_prefix_tuple_zeroed(Self::new_slice_unaligned_from_prefix(bytes, count))
    }

    /// Constructs a new `LayoutVerified` of a slice type with no alignment
    /// requirement from the suffix of a byte slice, after zeroing the bytes.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the last `size_of::<T>() * count` bytes from `bytes`
    /// to construct a `LayoutVerified`, and returns the remaining bytes to the
    /// caller. It also ensures that `sizeof::<T>() * count` does not overflow a
    /// `usize`. If either the length, or overflow checks fail, it returns
    /// `None`.
    ///
    /// If the checks succeed, then the suffix will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_suffix_zeroed` panics if `T` is a zero-sized
    /// type.
    #[inline]
    pub fn new_slice_unaligned_from_suffix_zeroed(
        bytes: B,
        count: usize,
    ) -> Option<(B, LayoutVerified<B, [T]>)> {
        map_suffix_tuple_zeroed(Self::new_slice_unaligned_from_suffix(bytes, count))
    }
}

impl<'a, B, T> LayoutVerified<B, T>
where
    B: 'a + ByteSlice,
    T: FromBytes,
{
    /// Converts this `LayoutVerified` into a reference.
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
    /// Converts this `LayoutVerified` into a mutable reference.
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
    /// Converts this `LayoutVerified` into a slice reference.
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
    /// Converts this `LayoutVerified` into a mutable slice reference.
    ///
    /// `into_mut_slice` consumes the `LayoutVerified`, and returns a mutable
    /// reference to `[T]`.
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
    /// Creates an immutable reference to `T` with a specific lifetime.
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
    /// Creates a mutable reference to `T` with a specific lifetime.
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
    /// Creates an immutable reference to `[T]` with a specific lifetime.
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
    /// Creates a mutable reference to `[T]` with a specific lifetime.
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
    B: ByteSlice,
    T: ?Sized,
{
    /// Gets the underlying bytes.
    #[inline]
    pub fn bytes(&self) -> &[u8] {
        &self.0
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSliceMut,
    T: ?Sized,
{
    /// Gets the underlying bytes mutably.
    #[inline]
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes,
{
    /// Reads a copy of `T`.
    #[inline]
    pub fn read(&self) -> T {
        // SAFETY: Because of the invariants on `LayoutVerified`, we know that
        // `self.0` is at least `size_of::<T>()` bytes long, and that it is at
        // least as aligned as `align_of::<T>()`. Because `T: FromBytes`, it is
        // sound to interpret these bytes as a `T`.
        unsafe { ptr::read(self.0.as_ptr() as *const T) }
    }
}

impl<B, T> LayoutVerified<B, T>
where
    B: ByteSliceMut,
    T: AsBytes,
{
    /// Writes the bytes of `t` and then forgets `t`.
    #[inline]
    pub fn write(&mut self, t: T) {
        // SAFETY: Because of the invariants on `LayoutVerified`, we know that
        // `self.0` is at least `size_of::<T>()` bytes long, and that it is at
        // least as aligned as `align_of::<T>()`. Writing `t` to the buffer will
        // allow all of the bytes of `t` to be accessed as a `[u8]`, but because
        // `T: AsBytes`, we know this is sound.
        unsafe { ptr::write(self.0.as_mut_ptr() as *mut T, t) }
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
        // SAFETY: This is safe because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no mutable methods on `self`
        // can be called during the lifetime of the returned reference. See the
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
        // SAFETY: This is safe because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no other methods on `self`
        // can be called during the lifetime of the returned reference. See the
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
        // SAFETY: This is safe because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no mutable methods on `self`
        // can be called during the lifetime of the returned reference. See the
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
        // SAFETY: This is safe because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no other methods on `self`
        // can be called during the lifetime of the returned reference. See the
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

impl<T, B> Eq for LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes + Eq,
{
}

impl<T, B> Eq for LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + Eq,
{
}

impl<T, B> PartialEq for LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes + PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.deref().eq(other.deref())
    }
}

impl<T, B> PartialEq for LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.deref().eq(other.deref())
    }
}

impl<T, B> Ord for LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes + Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let inner: &T = self;
        let other_inner: &T = other;
        inner.cmp(other_inner)
    }
}

impl<T, B> Ord for LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let inner: &[T] = self;
        let other_inner: &[T] = other;
        inner.cmp(other_inner)
    }
}

impl<T, B> PartialOrd for LayoutVerified<B, T>
where
    B: ByteSlice,
    T: FromBytes + PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let inner: &T = self;
        let other_inner: &T = other;
        inner.partial_cmp(other_inner)
    }
}

impl<T, B> PartialOrd for LayoutVerified<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let inner: &[T] = self;
        let other_inner: &[T] = other;
        inner.partial_cmp(other_inner)
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
///
/// Note that, while it would be technically possible, `ByteSlice` is not
/// implemented for [`Vec<u8>`], as the only way to implement the [`split_at`]
/// method would involve reallocation, and `split_at` must be a very cheap
/// operation in order for the utilities in this crate to perform as designed.
///
/// [`Vec<u8>`]: std::vec::Vec
/// [`split_at`]: crate::ByteSlice::split_at
pub unsafe trait ByteSlice: Deref<Target = [u8]> + Sized + self::sealed::Sealed {
    /// Gets a raw pointer to the first byte in the slice.
    fn as_ptr(&self) -> *const u8;

    /// Splits the slice at the midpoint.
    ///
    /// `x.split_at(mid)` returns `x[..mid]` and `x[mid..]`.
    ///
    /// # Panics
    ///
    /// `x.split_at(mid)` panics if `mid > x.len()`.
    fn split_at(self, mid: usize) -> (Self, Self);
}

/// A mutable reference to a byte slice.
///
/// `ByteSliceMut` abstracts over various ways of storing a mutable reference to
/// a byte slice, and is implemented for various special reference types such as
/// `RefMut<[u8]>`.
pub unsafe trait ByteSliceMut: ByteSlice + DerefMut {
    /// Gets a mutable raw pointer to the first byte in the slice.
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

#[cfg(any(test, feature = "alloc"))]
mod alloc_support {
    pub(crate) extern crate alloc;
    pub(crate) use super::*;
    pub(crate) use alloc::alloc::Layout;
    pub(crate) use alloc::boxed::Box;
    pub(crate) use alloc::vec::Vec;
    pub(crate) use core::mem::{align_of, size_of};
    pub(crate) use core::ptr::NonNull;

    /// Extends a `Vec<T>` by pushing `additional` new items onto the end of the
    /// vector. The new items are initialized with zeroes.
    ///
    /// # Panics
    ///
    /// Panics if `Vec::reserve(additional)` fails to reserve enough memory.
    pub fn extend_vec_zeroed<T: FromBytes>(v: &mut Vec<T>, additional: usize) {
        insert_vec_zeroed(v, v.len(), additional);
    }

    /// Inserts `additional` new items into `Vec<T>` at `position`.
    /// The new items are initialized with zeroes.
    ///
    /// # Panics
    ///
    /// * Panics if `position > v.len()`.
    /// * Panics if `Vec::reserve(additional)` fails to reserve enough memory.
    pub fn insert_vec_zeroed<T: FromBytes>(v: &mut Vec<T>, position: usize, additional: usize) {
        assert!(position <= v.len());
        v.reserve(additional);
        // The reserve() call guarantees that these cannot overflow:
        // * `ptr.add(position)`
        // * `position + additional`
        // * `v.len() + additional`
        //
        // `v.len() - position` cannot overflow because we asserted that
        // position <= v.len().
        unsafe {
            // This is a potentially overlapping copy.
            let ptr = v.as_mut_ptr();
            ptr.add(position).copy_to(ptr.add(position + additional), v.len() - position);
            ptr.add(position).write_bytes(0, additional);
            v.set_len(v.len() + additional);
        }
    }
}

#[cfg(any(test, feature = "alloc"))]
#[doc(inline)]
pub use alloc_support::*;

#[cfg(test)]
mod tests {
    #![allow(clippy::unreadable_literal)]

    use core::ops::Deref;

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

    #[test]
    fn test_read_write() {
        const VAL: u64 = 0x12345678;
        #[cfg(target_endian = "big")]
        const VAL_BYTES: [u8; 8] = VAL.to_be_bytes();
        #[cfg(target_endian = "little")]
        const VAL_BYTES: [u8; 8] = VAL.to_le_bytes();

        // Test FromBytes::{read_from, read_from_prefix, read_from_suffix}

        assert_eq!(u64::read_from(&VAL_BYTES[..]), Some(VAL));
        // The first 8 bytes are from `VAL_BYTES` and the second 8 bytes are all
        // zeroes.
        let bytes_with_prefix: [u8; 16] = transmute!([VAL_BYTES, [0; 8]]);
        assert_eq!(u64::read_from_prefix(&bytes_with_prefix[..]), Some(VAL));
        assert_eq!(u64::read_from_suffix(&bytes_with_prefix[..]), Some(0));
        // The first 8 bytes are all zeroes and the second 8 bytes are from
        // `VAL_BYTES`
        let bytes_with_suffix: [u8; 16] = transmute!([[0; 8], VAL_BYTES]);
        assert_eq!(u64::read_from_prefix(&bytes_with_suffix[..]), Some(0));
        assert_eq!(u64::read_from_suffix(&bytes_with_suffix[..]), Some(VAL));

        // Test AsBytes::{write_to, write_to_prefix, write_to_suffix}

        let mut bytes = [0u8; 8];
        assert_eq!(VAL.write_to(&mut bytes[..]), Some(()));
        assert_eq!(bytes, VAL_BYTES);
        let mut bytes = [0u8; 16];
        assert_eq!(VAL.write_to_prefix(&mut bytes[..]), Some(()));
        let want: [u8; 16] = transmute!([VAL_BYTES, [0; 8]]);
        assert_eq!(bytes, want);
        let mut bytes = [0u8; 16];
        assert_eq!(VAL.write_to_suffix(&mut bytes[..]), Some(()));
        let want: [u8; 16] = transmute!([[0; 8], VAL_BYTES]);
        assert_eq!(bytes, want);
    }

    #[test]
    fn test_transmute() {
        // Test that memory is transmuted as expected.
        let array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let x: [[u8; 2]; 4] = transmute!(array_of_u8s);
        assert_eq!(x, array_of_arrays);
        let x: [u8; 8] = transmute!(array_of_arrays);
        assert_eq!(x, array_of_u8s);

        // Test that the source expression's value is forgotten rather than
        // dropped.
        #[derive(AsBytes)]
        #[repr(transparent)]
        struct PanicOnDrop(());
        impl Drop for PanicOnDrop {
            fn drop(&mut self) {
                panic!("PanicOnDrop::drop");
            }
        }
        let _: () = transmute!(PanicOnDrop(()));
    }

    #[test]
    fn test_address() {
        // test that the Deref and DerefMut implementations return a reference
        // which points to the right region of memory

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
    // between the typed and untyped representations, that reads via `deref` and
    // `read` behave the same, and that writes via `deref_mut` and `write`
    // behave the same
    fn test_new_helper<'a>(mut lv: LayoutVerified<&'a mut [u8], u64>) {
        // assert that the value starts at 0
        assert_eq!(*lv, 0);
        assert_eq!(lv.read(), 0);

        // assert that values written to the typed value are reflected in the
        // byte slice
        const VAL1: u64 = 0xFF00FF00FF00FF00;
        *lv = VAL1;
        assert_eq!(lv.bytes(), &u64_to_bytes(VAL1));
        *lv = 0;
        lv.write(VAL1);
        assert_eq!(lv.bytes(), &u64_to_bytes(VAL1));

        // assert that values written to the byte slice are reflected in the
        // typed value
        const VAL2: u64 = !VAL1; // different from VAL1
        lv.bytes_mut().copy_from_slice(&u64_to_bytes(VAL2)[..]);
        assert_eq!(*lv, VAL2);
        assert_eq!(lv.read(), VAL2);
    }

    // verify that values written to a LayoutVerified are properly shared
    // between the typed and untyped representations; pass a value with
    // `typed_len` `u64`s backed by an array of `typed_len * 8` bytes.
    fn test_new_helper_slice<'a>(mut lv: LayoutVerified<&'a mut [u8], [u64]>, typed_len: usize) {
        // assert that the value starts out zeroed
        assert_eq!(&*lv, vec![0; typed_len].as_slice());

        // check the backing storage is the exact same slice
        let untyped_len = typed_len * 8;
        assert_eq!(lv.bytes().len(), untyped_len);
        assert_eq!(lv.bytes().as_ptr(), lv.as_ptr() as *const u8);

        // assert that values written to the typed value are reflected in the
        // byte slice
        const VAL1: u64 = 0xFF00FF00FF00FF00;
        for typed in &mut *lv {
            *typed = VAL1;
        }
        assert_eq!(lv.bytes(), VAL1.to_ne_bytes().repeat(typed_len).as_slice());

        // assert that values written to the byte slice are reflected in the
        // typed value
        const VAL2: u64 = !VAL1; // different from VAL1
        lv.bytes_mut().copy_from_slice(&VAL2.to_ne_bytes().repeat(typed_len));
        assert!(lv.iter().copied().all(|x| x == VAL2));
    }

    // verify that values written to a LayoutVerified are properly shared
    // between the typed and untyped representations, that reads via `deref` and
    // `read` behave the same, and that writes via `deref_mut` and `write`
    // behave the same
    fn test_new_helper_unaligned<'a>(mut lv: LayoutVerified<&'a mut [u8], [u8; 8]>) {
        // assert that the value starts at 0
        assert_eq!(*lv, [0; 8]);
        assert_eq!(lv.read(), [0; 8]);

        // assert that values written to the typed value are reflected in the
        // byte slice
        const VAL1: [u8; 8] = [0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00];
        *lv = VAL1;
        assert_eq!(lv.bytes(), &VAL1);
        *lv = [0; 8];
        lv.write(VAL1);
        assert_eq!(lv.bytes(), &VAL1);

        // assert that values written to the byte slice are reflected in the
        // typed value
        const VAL2: [u8; 8] = [0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF]; // different from VAL1
        lv.bytes_mut().copy_from_slice(&VAL2[..]);
        assert_eq!(*lv, VAL2);
        assert_eq!(lv.read(), VAL2);
    }

    // verify that values written to a LayoutVerified are properly shared
    // between the typed and untyped representations; pass a value with
    // `len` `u8`s backed by an array of `len` bytes.
    fn test_new_helper_slice_unaligned<'a>(mut lv: LayoutVerified<&'a mut [u8], [u8]>, len: usize) {
        // assert that the value starts out zeroed
        assert_eq!(&*lv, vec![0u8; len].as_slice());

        // check the backing storage is the exact same slice
        assert_eq!(lv.bytes().len(), len);
        assert_eq!(lv.bytes().as_ptr(), lv.as_ptr());

        // assert that values written to the typed value are reflected in the
        // byte slice
        let mut expected_bytes = [0xFF, 0x00].iter().copied().cycle().take(len).collect::<Vec<_>>();
        lv.copy_from_slice(&expected_bytes);
        assert_eq!(lv.bytes(), expected_bytes.as_slice());

        // assert that values written to the byte slice are reflected in the
        // typed value
        for byte in &mut expected_bytes {
            *byte = !*byte; // different from expected_len
        }
        lv.bytes_mut().copy_from_slice(&expected_bytes);
        assert_eq!(&*lv, expected_bytes.as_slice());
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
        test_new_helper_slice(LayoutVerified::<_, [u64]>::new_slice(&mut buf.buf[..]).unwrap(), 2);
        buf.buf = [0xFFu8; 16];
        test_new_helper_slice(
            LayoutVerified::<_, [u64]>::new_slice_zeroed(&mut buf.buf[..]).unwrap(),
            2,
        );

        {
            buf.clear_buf();
            let (lv, suffix) =
                LayoutVerified::<_, [u64]>::new_slice_from_prefix(&mut buf.buf[..], 1).unwrap();
            assert_eq!(suffix, [0; 8]);
            test_new_helper_slice(lv, 1);
        }
        {
            buf.buf = [0xFFu8; 16];
            let (lv, suffix) =
                LayoutVerified::<_, [u64]>::new_slice_from_prefix_zeroed(&mut buf.buf[..], 1)
                    .unwrap();
            assert_eq!(suffix, [0xFF; 8]);
            test_new_helper_slice(lv, 1);
        }
        {
            buf.clear_buf();
            let (prefix, lv) =
                LayoutVerified::<_, [u64]>::new_slice_from_suffix(&mut buf.buf[..], 1).unwrap();
            assert_eq!(prefix, [0; 8]);
            test_new_helper_slice(lv, 1);
        }
        {
            buf.buf = [0xFFu8; 16];
            let (prefix, lv) =
                LayoutVerified::<_, [u64]>::new_slice_from_suffix_zeroed(&mut buf.buf[..], 1)
                    .unwrap();
            assert_eq!(prefix, [0xFF; 8]);
            test_new_helper_slice(lv, 1);
        }
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
            LayoutVerified::<_, [u8]>::new_slice_unaligned(&mut buf[..]).unwrap(),
            16,
        );
        buf = [0xFFu8; 16];
        test_new_helper_slice_unaligned(
            LayoutVerified::<_, [u8]>::new_slice_unaligned_zeroed(&mut buf[..]).unwrap(),
            16,
        );

        {
            buf = [0u8; 16];
            let (lv, suffix) =
                LayoutVerified::<_, [u8]>::new_slice_unaligned_from_prefix(&mut buf[..], 8)
                    .unwrap();
            assert_eq!(suffix, [0; 8]);
            test_new_helper_slice_unaligned(lv, 8);
        }
        {
            buf = [0xFFu8; 16];
            let (lv, suffix) =
                LayoutVerified::<_, [u8]>::new_slice_unaligned_from_prefix_zeroed(&mut buf[..], 8)
                    .unwrap();
            assert_eq!(suffix, [0xFF; 8]);
            test_new_helper_slice_unaligned(lv, 8);
        }
        {
            buf = [0u8; 16];
            let (prefix, lv) =
                LayoutVerified::<_, [u8]>::new_slice_unaligned_from_suffix(&mut buf[..], 8)
                    .unwrap();
            assert_eq!(prefix, [0; 8]);
            test_new_helper_slice_unaligned(lv, 8);
        }
        {
            buf = [0xFFu8; 16];
            let (prefix, lv) =
                LayoutVerified::<_, [u8]>::new_slice_unaligned_from_suffix_zeroed(&mut buf[..], 8)
                    .unwrap();
            assert_eq!(prefix, [0xFF; 8]);
            test_new_helper_slice_unaligned(lv, 8);
        }
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
    #[allow(clippy::cognitive_complexity)]
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

        // fail beacuse the buffer is too short.
        let mut buf = AlignedBuffer::<u64, [u8; 12]>::default();
        // buf.buf has length 12, but the element size is 8 (and we're expecting two of them).
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_prefix(&buf.buf[..], 2).is_none());
        assert!(
            LayoutVerified::<_, [u64]>::new_slice_from_prefix_zeroed(&mut buf.buf[..], 2).is_none()
        );
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_suffix(&buf.buf[..], 2).is_none());
        assert!(
            LayoutVerified::<_, [u64]>::new_slice_from_suffix_zeroed(&mut buf.buf[..], 2).is_none()
        );
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix(&buf.buf[..], 2)
            .is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix_zeroed(
            &mut buf.buf[..],
            2
        )
        .is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix(&buf.buf[..], 2)
            .is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix_zeroed(
            &mut buf.buf[..],
            2
        )
        .is_none());

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
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_prefix(&buf.buf[4..], 1).is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_prefix_zeroed(&mut buf.buf[4..], 1)
            .is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_suffix(&buf.buf[4..], 1).is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_suffix_zeroed(&mut buf.buf[4..], 1)
            .is_none());
        // slicing from 4 should be unnecessary because new_from_suffix[_zeroed]
        // use the suffix of the slice
        assert!(LayoutVerified::<_, u64>::new_from_suffix(&buf.buf[..]).is_none());
        assert!(LayoutVerified::<_, u64>::new_from_suffix_zeroed(&mut buf.buf[..]).is_none());

        // fail due to arithmetic overflow

        let mut buf = AlignedBuffer::<u64, [u8; 16]>::default();
        let unreasonable_len = std::usize::MAX / mem::size_of::<u64>() + 1;
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_prefix(&buf.buf[..], unreasonable_len)
            .is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_prefix_zeroed(
            &mut buf.buf[..],
            unreasonable_len
        )
        .is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_suffix(&buf.buf[..], unreasonable_len)
            .is_none());
        assert!(LayoutVerified::<_, [u64]>::new_slice_from_suffix_zeroed(
            &mut buf.buf[..],
            unreasonable_len
        )
        .is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix(
            &buf.buf[..],
            unreasonable_len
        )
        .is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix_zeroed(
            &mut buf.buf[..],
            unreasonable_len
        )
        .is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix(
            &buf.buf[..],
            unreasonable_len
        )
        .is_none());
        assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix_zeroed(
            &mut buf.buf[..],
            unreasonable_len
        )
        .is_none());
    }

    // Tests for ensuring that, if a ZST is passed into a slice-like function, we always
    // panic. Since these tests need to be separate per-function, and they tend to take
    // up a lot of space, we generate them using a macro in a submodule instead. The
    // submodule ensures that we can just re-use the name of the function under test for
    // the name of the test itself.
    mod test_zst_panics {
        macro_rules! zst_test {
            ($name:ident($($tt:tt)*)) => {
                #[test]
                #[should_panic = "assertion failed"]
                fn $name() {
                    let mut buffer = [0u8];
                    let lv = $crate::LayoutVerified::<_, [()]>::$name(&mut buffer[..], $($tt)*);
                    unreachable!("should have panicked, got {:?}", lv);
                }
            }
        }
        zst_test!(new_slice());
        zst_test!(new_slice_zeroed());
        zst_test!(new_slice_from_prefix(1));
        zst_test!(new_slice_from_prefix_zeroed(1));
        zst_test!(new_slice_from_suffix(1));
        zst_test!(new_slice_from_suffix_zeroed(1));
        zst_test!(new_slice_unaligned());
        zst_test!(new_slice_unaligned_zeroed());
        zst_test!(new_slice_unaligned_from_prefix(1));
        zst_test!(new_slice_unaligned_from_prefix_zeroed(1));
        zst_test!(new_slice_unaligned_from_suffix(1));
        zst_test!(new_slice_unaligned_from_suffix_zeroed(1));
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

    #[test]
    fn test_eq() {
        let buf = [0u8; 8];
        let lv1 = LayoutVerified::<_, u64>::new(&buf[..]).unwrap();
        let lv2 = LayoutVerified::<_, u64>::new(&buf[..]).unwrap();
        assert_eq!(lv1, lv2);
    }

    #[test]
    fn test_ne() {
        let buf1 = [0u8; 8];
        let lv1 = LayoutVerified::<_, u64>::new(&buf1[..]).unwrap();
        let buf2 = [1u8; 8];
        let lv2 = LayoutVerified::<_, u64>::new(&buf2[..]).unwrap();
        assert_ne!(lv1, lv2);
    }

    #[test]
    fn test_ord() {
        let buf1 = [0u8; 8];
        let lv1 = LayoutVerified::<_, u64>::new(&buf1[..]).unwrap();
        let buf2 = [1u8; 8];
        let lv2 = LayoutVerified::<_, u64>::new(&buf2[..]).unwrap();
        assert!(lv1 < lv2);
    }

    #[test]
    fn test_new_zeroed() {
        assert_eq!(u64::new_zeroed(), 0);
        assert_eq!(<()>::new_zeroed(), ());
    }

    #[test]
    fn test_new_box_zeroed() {
        assert_eq!(*u64::new_box_zeroed(), 0);
    }

    #[test]
    fn test_new_box_zeroed_array() {
        drop(<[u32; 0x1000]>::new_box_zeroed());
    }

    #[test]
    fn test_new_box_zeroed_zst() {
        assert_eq!(*<()>::new_box_zeroed(), ());
    }

    #[test]
    fn test_new_box_slice_zeroed() {
        let mut s: Box<[u64]> = u64::new_box_slice_zeroed(3);
        assert_eq!(s.len(), 3);
        assert_eq!(&*s, &[0, 0, 0]);
        s[1] = 3;
        assert_eq!(&*s, &[0, 3, 0]);
    }

    #[test]
    fn test_new_box_slice_zeroed_empty() {
        let s: Box<[u64]> = u64::new_box_slice_zeroed(0);
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn test_new_box_slice_zeroed_zst() {
        let mut s: Box<[()]> = <()>::new_box_slice_zeroed(3);
        assert_eq!(s.len(), 3);
        assert!(s.get(10).is_none());
        assert_eq!(s[1], ());
        s[2] = ();
    }

    #[test]
    fn test_new_box_slice_zeroed_zst_empty() {
        let s: Box<[()]> = <()>::new_box_slice_zeroed(0);
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn test_extend_vec_zeroed() {
        // test extending when there is an existing allocation
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(v.len(), 6);
        assert_eq!(&*v, &[100, 200, 300, 0, 0, 0]);
        drop(v);

        // test extending when there is no existing allocation
        let mut v: Vec<u64> = Vec::new();
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(v.len(), 3);
        assert_eq!(&*v, &[0, 0, 0]);
        drop(v);
    }

    #[test]
    fn test_extend_vec_zeroed_zst() {
        // test extending when there is an existing (fake) allocation
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(v.len(), 6);
        assert_eq!(&*v, &[(), (), (), (), (), ()]);
        drop(v);

        // test extending when there is no existing (fake) allocation
        let mut v: Vec<()> = Vec::new();
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(&*v, &[(), (), ()]);
        drop(v);
    }

    #[test]
    fn test_insert_vec_zeroed() {
        // insert at start (no existing allocation)
        let mut v: Vec<u64> = Vec::new();
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 2);
        assert_eq!(&*v, &[0, 0]);
        drop(v);

        // insert at start
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 5);
        assert_eq!(&*v, &[0, 0, 100, 200, 300]);
        drop(v);

        // insert at middle
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        insert_vec_zeroed(&mut v, 1, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[100, 0, 200, 300]);
        drop(v);

        // insert at end
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        insert_vec_zeroed(&mut v, 3, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[100, 200, 300, 0]);
        drop(v);
    }

    #[test]
    fn test_insert_vec_zeroed_zst() {
        // insert at start (no existing fake allocation)
        let mut v: Vec<()> = Vec::new();
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 2);
        assert_eq!(&*v, &[(), ()]);
        drop(v);

        // insert at start
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 5);
        assert_eq!(&*v, &[(), (), (), (), ()]);
        drop(v);

        // insert at middle
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        insert_vec_zeroed(&mut v, 1, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[(), (), (), ()]);
        drop(v);

        // insert at end
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        insert_vec_zeroed(&mut v, 3, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[(), (), (), ()]);
        drop(v);
    }
}
