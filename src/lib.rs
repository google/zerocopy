// Copyright 2018 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// After updating the following doc comment, make sure to run the following
// command to update `README.md` based on its contents:
//
//   ./generate-readme.sh > README.md

//! Utilities for safe zero-copy parsing and serialization.
//!
//! This crate provides utilities which make it easy to perform zero-copy
//! parsing and serialization by allowing zero-copy conversion to/from byte
//! slices.
//!
//! This is enabled by four core marker traits, each of which can be derived
//! (e.g., `#[derive(FromZeroes)]`):
//! - [`FromZeroes`] indicates that a sequence of zero bytes represents a valid
//!   instance of a type
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
//! # Cargo Features
//!
//! - **`alloc`**   
//!   By default, `zerocopy` is `no_std`. When the `alloc` feature is enabled,
//!   the `alloc` crate is added as a dependency, and some allocation-related
//!   functionality is added.
//!
//! - **`byteorder`** (enabled by default)   
//!   Adds the [`byteorder`] module and a dependency on the `byteorder` crate.
//!   The `byteorder` module provides byte order-aware equivalents of the
//!   multi-byte primitive numerical types. Unlike their primitive equivalents,
//!   the types in this module have no alignment requirement and support byte
//!   order conversions. This can be useful in handling file formats, network
//!   packet layouts, etc which don't provide alignment guarantees and which may
//!   use a byte order different from that of the execution platform.
//!
//! - **`derive`**   
//!   Provides derives for the core marker traits via the `zerocopy-derive`
//!   crate. These derives are re-exported from `zerocopy`, so it is not
//!   necessary to depend on `zerocopy-derive` directly.   
//!
//!   However, you may experience better compile times if you instead directly
//!   depend on both `zerocopy` and `zerocopy-derive` in your `Cargo.toml`,
//!   since doing so will allow Rust to compile these crates in parallel. To do
//!   so, do *not* enable the `derive` feature, and list both dependencies in
//!   your `Cargo.toml` with the same leading non-zero version number; e.g:
//!
//!   ```toml
//!   [dependencies]
//!   zerocopy = "0.X"
//!   zerocopy-derive = "0.X"
//!   ```
//!
//! - **`simd`**   
//!   When the `simd` feature is enabled, `FromZeroes`, `FromBytes`, and
//!   `AsBytes` impls are emitted for all stable SIMD types which exist on the
//!   target platform. Note that the layout of SIMD types is not yet stabilized,
//!   so these impls may be removed in the future if layout changes make them
//!   invalid. For more information, see the Unsafe Code Guidelines Reference
//!   page on the [layout of packed SIMD vectors][simd-layout].
//!
//! - **`simd-nightly`**   
//!   Enables the `simd` feature and adds support for SIMD types which are only
//!   available on nightly. Since these types are unstable, support for any type
//!   may be removed at any point in the future.
//!
//! [simd-layout]: https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html

// Sometimes we want to use lints which were added after our MSRV.
// `unknown_lints` is `warn` by default and we deny warnings in CI, so without
// this attribute, any unknown lint would cause a CI failure when testing with
// our MSRV.
#![allow(unknown_lints)]
#![deny(renamed_and_removed_lints)]
#![deny(
    anonymous_parameters,
    deprecated_in_future,
    illegal_floating_point_literal_pattern,
    late_bound_lifetime_arguments,
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    path_statements,
    patterns_in_fns_without_body,
    rust_2018_idioms,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    unused_extern_crates,
    unused_qualifications,
    variant_size_differences
)]
#![deny(
    clippy::all,
    clippy::alloc_instead_of_core,
    clippy::arithmetic_side_effects,
    clippy::as_underscore,
    clippy::assertions_on_result_states,
    clippy::as_conversions,
    clippy::correctness,
    clippy::dbg_macro,
    clippy::decimal_literal_representation,
    clippy::get_unwrap,
    clippy::indexing_slicing,
    clippy::missing_safety_doc,
    clippy::obfuscated_if_else,
    clippy::perf,
    clippy::print_stdout,
    clippy::std_instead_of_core,
    clippy::style,
    clippy::suspicious,
    clippy::todo,
    clippy::undocumented_unsafe_blocks,
    clippy::unimplemented,
    clippy::unnested_or_patterns,
    clippy::unwrap_used,
    clippy::use_debug
)]
#![deny(
    rustdoc::bare_urls,
    rustdoc::broken_intra_doc_links,
    rustdoc::invalid_codeblock_attributes,
    rustdoc::invalid_html_tags,
    rustdoc::invalid_rust_codeblocks,
    rustdoc::missing_crate_level_docs,
    rustdoc::private_intra_doc_links
)]
// In test code, it makes sense to weight more heavily towards concise, readable
// code over correct or debuggable code.
#![cfg_attr(test, allow(
    // In tests, you get line numbers and have access to source code, so panic
    // messages are less important. You also often unwrap a lot, which would
    // make expect'ing instead very verbose.
    clippy::unwrap_used,
    // In tests, there's no harm to "panic risks" - the worst that can happen is
    // that your test will fail, and you'll fix it. By contrast, panic risks in
    // production code introduce the possibly of code panicking unexpectedly "in
    // the field".
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
))]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(feature = "simd-nightly", feature(stdsimd))]

#[macro_use]
mod macros;

#[cfg(feature = "byteorder")]
pub mod byteorder;
#[cfg(any(feature = "derive", test))]
#[doc(hidden)]
pub mod derive_util;
// TODO(#252): If we make this pub, come up with a better name.
mod util;
mod wrappers;

#[cfg(feature = "byteorder")]
pub use crate::byteorder::*;
pub use crate::wrappers::*;
#[cfg(any(feature = "derive", test))]
pub use zerocopy_derive::*;

use core::{
    cell::{self, RefMut},
    cmp::Ordering,
    fmt::{self, Debug, Display, Formatter},
    hash::Hasher,
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize, Wrapping,
    },
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
    slice,
};

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use {alloc::boxed::Box, alloc::vec::Vec, core::alloc::Layout};

// This is a hack to allow zerocopy-derive derives to work in this crate. They
// assume that zerocopy is linked as an extern crate, so they access items from
// it as `zerocopy::Xxx`. This makes that still work.
#[cfg(any(feature = "derive", test))]
mod zerocopy {
    pub(crate) use crate::*;
}

/// When performing a byte-slice-to-type cast, is the type taken from the prefix
/// of the byte slice or from the suffix of the byte slice?
#[doc(hidden)]
#[allow(missing_debug_implementations, missing_copy_implementations)]
pub enum CastType {
    Prefix,
    Suffix,
}

/// A trait which carries information about a type's layout that is used by the
/// internals of this crate.
///
/// This trait is not meant for consumption by code outsie of this crate. While
/// the normal semver stability guarantees apply with respect to which types
/// implement this trait and which trait implementations are implied by this
/// trait, no semver stability guarantees are made regarding its internals; they
/// may change at any time, and code which makes use of them may break.
///
/// # Safety
///
/// This trait does not convey any safety guarantees to code outside this crate.
pub unsafe trait KnownLayout: sealed::KnownLayoutSealed {
    #[doc(hidden)]
    const FIXED_PREFIX_SIZE: usize;
    #[doc(hidden)]
    const ALIGN: NonZeroUsize;
    #[doc(hidden)]
    const TRAILING_SLICE_ELEM_SIZE: Option<usize>;

    /// A type which has the same layout as `Self`, but which has no validity
    /// constraints.
    ///
    /// Roughly speaking, this type is equivalent to what the standard library's
    /// [`MaybeUninit<Self>`] would be if it supported unsized types.
    ///
    /// # Safety
    ///
    /// For `T: KnownLayout`, the following must hold:
    /// - Given `m: T::MaybeUninit`, it is sound to write any byte value,
    ///   including an uninitialized byte, at any byte offset in `m`
    /// - `T` and `T::MaybeUninit` have the same alignment requirement
    /// - It is valid to use an `as` cast to convert a `t: *const T` to a `m:
    ///   *const T::MaybeUninit` and vice-versa (and likewise for `*mut T`/`*mut
    ///   T::MaybeUninit`). Regardless of which direction the conversion was
    ///   performed, the sizes of the pointers' referents are always equal (in
    ///   terms of an API which is not yet stable, `size_of_val_raw(t) ==
    ///   size_of_val_raw(m)`).
    /// - `T::MaybeUninit` contains [`UnsafeCell`]s at exactly the same byte
    ///   ranges that `T` does.
    ///
    /// [`MaybeUninit<Self>`]: core::mem::MaybeUninit
    /// [`UnsafeCell`]: core::cell::UnsafeCell
    type MaybeUninit: ?Sized + KnownLayout;

    /// Validates that the memory region at `addr` of length `bytes_len`
    /// satisfies `Self`'s size and alignment requirements, returning `(elems,
    /// split_at, prefix_suffix_bytes)`.
    ///
    ///  In particular, `validate_size_align` validates that:
    /// - `bytes_len` is large enough to hold an instance of `Self`
    /// - If `cast_type` is `Prefix`, `addr` satisfies `Self`'s alignment
    ///   requirements
    /// - If `cast_type` is `Suffix`, `addr + split_at` satisfies `Self`'s
    ///   alignment requirements
    ///
    /// For DSTs, `elems` is the maximum number of trailing slice elements such
    /// that a `Self` with that number of trailing slice elements can fit in the
    /// provided space. For sized types, `elems` is always 0.
    ///
    /// `split_at` indicates the point at which to split the memory region in
    /// order to split it into the `Self` and the prefix or suffix. If
    /// `cast_type` is `Prefix`, `split_at` is the address of the first byte of
    /// the suffix. If `cast_type` is `Suffix`, `split_at` is the address of the
    /// first byte of the `Self`.
    ///
    /// # Panics
    ///
    /// Panics if called on a DST whose trailing slice element type is a
    /// zero-sized type.
    #[doc(hidden)]
    #[inline(always)]
    fn validate_size_align<A: crate::util::AsAddress>(
        addr: A,
        bytes_len: usize,
        cast_type: CastType,
    ) -> Option<(usize, usize, usize)> {
        let trailing_slice_bytes = bytes_len.checked_sub(Self::FIXED_PREFIX_SIZE)?;
        let (elems, self_bytes) = if let Some(elem_size) = Self::TRAILING_SLICE_ELEM_SIZE {
            let elem_size = NonZeroUsize::new(elem_size)
                .expect("attempted to cast to slice type with zero-sized element");
            #[allow(clippy::arithmetic_side_effects)]
            let elems = trailing_slice_bytes / elem_size;
            #[allow(clippy::arithmetic_side_effects)]
            let self_bytes = Self::FIXED_PREFIX_SIZE + (elems * elem_size.get());
            (elems, self_bytes)
        } else {
            (0, Self::FIXED_PREFIX_SIZE)
        };

        // `self_addr` indicates where in the given byte range the `Self` will
        // start. If we're doing a prefix cast, it starts at the beginning. If
        // we're doing a suffix cast, it starts after whatever bytes are
        // remaining.
        #[allow(clippy::arithmetic_side_effects)]
        let (self_addr, split_at) = match cast_type {
            CastType::Prefix => (addr.addr(), self_bytes),
            CastType::Suffix => {
                let split_at = bytes_len - self_bytes;
                (addr.addr() + split_at, split_at)
            }
        };

        #[allow(clippy::arithmetic_side_effects)]
        if self_addr % Self::ALIGN != 0 {
            return None;
        }

        #[allow(clippy::arithmetic_side_effects)]
        let ret = Some((elems, split_at, bytes_len - self_bytes));
        ret
    }

    /// SAFETY: The returned pointer has the same address and provenance as
    /// `bytes`. If `Self` is a DST, the returned pointer's referent has `elems`
    /// elements in its trailing slice.
    #[doc(hidden)]
    fn raw_from_ptr_len(bytes: NonNull<u8>, elems: usize) -> NonNull<Self>;

    /// Converts a pointer at the type level.
    ///
    /// # Safety
    ///
    /// Callers may assume that the memory region addressed by the return value
    /// is the same as that addressed by the argument, and that both the return
    /// value and the argument have the same provenance.
    fn cast_from_maybe_uninit(maybe_uninit: NonNull<Self::MaybeUninit>) -> NonNull<Self>;

    /// Converts a pointer at the type level.
    ///
    /// # Safety
    ///
    /// Callers may assume that the memory region addressed by the return value
    /// is the same as that addressed by the argument, and that both the return
    /// value and the argument have the same provenance.
    fn cast_to_maybe_uninit(slf: NonNull<Self>) -> NonNull<Self::MaybeUninit>;
}

impl<T: KnownLayout> sealed::KnownLayoutSealed for [T] {}
// SAFETY: See inline comments.
unsafe impl<T: KnownLayout> KnownLayout for [T] {
    // `[T]` is a slice type; it has no fields before the trailing slice.
    const FIXED_PREFIX_SIZE: usize = 0;
    // Slices have the same layout as the array they slice. [1] Arrays `[T; _]`
    // have the same alignment as `T`. [2]
    //
    // [1] https://doc.rust-lang.org/reference/type-layout.html#slice-layout
    // [2] https://doc.rust-lang.org/reference/type-layout.html#array-layout
    const ALIGN: NonZeroUsize = if let Some(align) = NonZeroUsize::new(mem::align_of::<T>()) {
        align
    } else {
        unreachable!()
    };
    const TRAILING_SLICE_ELEM_SIZE: Option<usize> = Some(mem::size_of::<T>());

    // SAFETY:
    // - `MaybeUninit` has no bit validity requirements and `[U]` has the same
    //   bit validity requirements as `U`, so `[MaybeUninit<T>]` has no bit
    //   validity requirements. Thus, it is sound to write any byte value,
    //   including an uninitialized byte, at any byte offset.
    // - Since `MaybeUninit<T>` has the same layout as `T`, and `[U]` has the
    //   same alignment as `U`, `[MaybeUninit<T>]` has the same alignment as
    //   `[T]`.
    // - `[T]` and `[MaybeUninit<T>]` are both slice types, and so pointers can
    //   be converted using an `as` cast. Since `T` and `MaybeUninit<T>` have
    //   the same size, and since such a cast preserves the number of elements
    //   in the slice, the referent slices themselves will have the same size.
    // - `MaybeUninit<T>` has the same field offsets as `[T]`, and so it
    //   contains `UnsafeCell`s at exactly the same byte ranges as `[T]`.
    type MaybeUninit = [mem::MaybeUninit<T>];

    // SAFETY: `.cast` preserves address and provenance. The returned pointer
    // refers to an object with `elems` elements by construction.
    #[inline(always)]
    fn raw_from_ptr_len(data: NonNull<u8>, elems: usize) -> NonNull<Self> {
        // TODO(#67): Remove this allow. See NonNullExt for more details.
        #[allow(unstable_name_collisions)]
        NonNull::slice_from_raw_parts(data.cast::<T>(), elems)
    }

    fn cast_from_maybe_uninit(maybe_uninit: NonNull<[mem::MaybeUninit<T>]>) -> NonNull<[T]> {
        let (ptr, len) = (maybe_uninit.cast::<T>(), maybe_uninit.len());
        // TODO(#67): Remove this allow. See NonNullExt for more details.
        #[allow(unstable_name_collisions)]
        NonNull::slice_from_raw_parts(ptr, len)
    }

    fn cast_to_maybe_uninit(slf: NonNull<[T]>) -> NonNull<[mem::MaybeUninit<T>]> {
        let (ptr, len) = (slf.cast::<mem::MaybeUninit<T>>(), slf.len());
        // TODO(#67): Remove this allow. See NonNullExt for more details.
        #[allow(unstable_name_collisions)]
        NonNull::slice_from_raw_parts(ptr, len)
    }
}

/// Implements `KnownLayout` for a sized type.
macro_rules! impl_known_layout {
    (const $constvar:ident : $constty:ty, $tyvar:ident $(: ?$optbound:ident)? => $ty:ty) => {
        impl_known_layout!(@inner const $constvar: $constty, $tyvar $(: ?$optbound)? => $ty);
    };
    ($tyvar:ident $(: ?$optbound:ident)? => $ty:ty) => {
        impl_known_layout!(@inner , $tyvar $(: ?$optbound)? => $ty);
    };
    ($ty:ty) => {
        impl_known_layout!(@inner , => $ty);
    };
    ($($tyvar:ident $(: ?$optbound:ident)? => $ty:ty),*) => {
        $(
            impl_known_layout!(@inner , $tyvar $(: ?$optbound)? => $ty);
        )*
    };
    ($($ty:ty),*) => {
        $(
            impl_known_layout!(@inner , => $ty);
        )*
    };
    (@inner $(const $constvar:ident : $constty:ty)? , $($tyvar:ident $(: ?$optbound:ident)?)? => $ty:ty) => {
        impl<$(const $constvar : $constty,)? $($tyvar $(: ?$optbound)?)?> sealed::KnownLayoutSealed for $ty {}
        // SAFETY: See inline comments.
        unsafe impl<$(const $constvar : $constty,)? $($tyvar $(: ?$optbound)?)?> KnownLayout for $ty {
            const FIXED_PREFIX_SIZE: usize = mem::size_of::<$ty>();
            const ALIGN: NonZeroUsize = if let Some(align) = NonZeroUsize::new(mem::align_of::<$ty>()) {
                align
            } else {
                unreachable!()
            };
            // `T` is sized so it has no trailing slice.
            const TRAILING_SLICE_ELEM_SIZE: Option<usize> = None;

            // SAFETY:
            // - `MaybeUninit` has no validity requirements, so it is sound to
            //   write any byte value, including an uninitialized byte, at any
            //   offset.
            // - `MaybeUninit<T>` has the same layout as `T`, so they have the
            //   same alignment requirement. For the same reason, their sizes
            //   are equal.
            // - Since their sizes are equal, raw pointers to both types are
            //   thin pointers, and thus can be converted using as casts. For
            //   the same reason, the sizes of these pointers' referents are
            //   always equal.
            // - `MaybeUninit<T>` has the same field offsets as `T`, and so it
            //   contains `UnsafeCell`s at exactly the same byte ranges as `T`.
            type MaybeUninit = mem::MaybeUninit<$ty>;

            // SAFETY: `.cast` preserves address and provenance.
            #[inline(always)]
            fn raw_from_ptr_len(bytes: NonNull<u8>, _elems: usize) -> NonNull<Self> {
                bytes.cast::<Self>()
            }

            // SAFETY: `.cast` preserves pointer address and provenance.
            fn cast_from_maybe_uninit(maybe_uninit: NonNull<Self::MaybeUninit>) -> NonNull<Self> {
                maybe_uninit.cast::<Self>()
            }

            // SAFETY: `.cast` preserves pointer address and provenance.
            fn cast_to_maybe_uninit(slf: NonNull<Self>) -> NonNull<Self::MaybeUninit> {
                slf.cast::<Self::MaybeUninit>()
            }
        }
    };
}

#[rustfmt::skip]
impl_known_layout!(
    (),
    u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, f32, f64,
    bool, char,
    NonZeroU8, NonZeroI8, NonZeroU16, NonZeroI16, NonZeroU32, NonZeroI32,
    NonZeroU64, NonZeroI64, NonZeroU128, NonZeroI128, NonZeroUsize, NonZeroIsize
);
impl_known_layout!(T => Option<T>);
impl_known_layout!(T: ?Sized => PhantomData<T>);
impl_known_layout!(T => Wrapping<T>);
impl_known_layout!(T => mem::MaybeUninit<T>);
impl_known_layout!(const N: usize, T => [T; N]);

safety_comment! {
    /// SAFETY:
    /// `str` and `ManuallyDrop<[T]>` have the same representations as `[u8]`
    /// and `[T]` repsectively, including with respect to the locations of
    /// `UnsafeCell`s. `str` has different bit validity than `[u8]`, but that
    /// doesn't affect the soundness of this impl.
    unsafe_impl_known_layout!(#[repr([u8])] str);
    unsafe_impl_known_layout!(T: ?Sized + KnownLayout => #[repr(T)] ManuallyDrop<T>);
    /// SAFETY:
    /// `Cell<T>` and `UnsafeCell<T>` have the same representations, including
    /// (trivially) with respect to the locations of `UnsafeCell`s.
    unsafe_impl_known_layout!(T: ?Sized + KnownLayout => #[repr(cell::UnsafeCell<T>)] cell::Cell<T>);
}

impl<T: ?Sized + sealed::KnownLayoutSealed> sealed::KnownLayoutSealed for cell::UnsafeCell<T> {}
// SAFETY: See inline comments.
unsafe impl<T: ?Sized + KnownLayout> KnownLayout for cell::UnsafeCell<T> {
    // SAFETY: `UnsafeCell<T>` and `T` have the same size, alignment, and
    // trailing element size.
    const FIXED_PREFIX_SIZE: usize = <T as KnownLayout>::FIXED_PREFIX_SIZE;
    const ALIGN: NonZeroUsize = <T as KnownLayout>::ALIGN;
    const TRAILING_SLICE_ELEM_SIZE: Option<usize> = <T as KnownLayout>::TRAILING_SLICE_ELEM_SIZE;

    // SAFETY:
    // - By `MaybeUninit` invariant, it is sound to write any byte - including
    //   an uninitialized byte - at any byte offset in
    //   `UnsafeCell<T::MaybeUninit>`.
    // - `UnsafeCell<T>` and `T` have the same size, alignment, and trailing
    //   element size. Also, by `MaybeUninit` invariants:
    //   - `T` and `T::MaybeUninit` have the same alignment.
    //   - It is valid to cast `*const T` to `*const T::MaybeUninit` and
    //     vice-versa (and likewise for `*mut`), and these operations preserve
    //     pointer referent size.
    //
    //   Thus, these properties hold between `UnsafeCell<T>` and
    //   `UnsafeCell<T::MaybeUninit>`.
    // - `UnsafeCell<T>` and `UnsafeCell<T::MaybeUninit>` trivially have
    //   `UnsafeCell`s in exactly the same locations.
    type MaybeUninit = cell::UnsafeCell<<T as KnownLayout>::MaybeUninit>;

    // SAFETY: All operations preserve address and provenance. Caller
    // has promised that the `as` cast preserves size.
    #[inline(always)]
    fn raw_from_ptr_len(bytes: NonNull<u8>, elems: usize) -> NonNull<Self> {
        let slf = T::raw_from_ptr_len(bytes, elems).as_ptr();
        #[allow(clippy::as_conversions)]
        let slf = slf as *mut cell::UnsafeCell<T>;
        // SAFETY: `.as_ptr()` called on a non-null pointer.
        unsafe { NonNull::new_unchecked(slf) }
    }

    // SAFETY: All operations preserve pointer address and provenance.
    fn cast_from_maybe_uninit(maybe_uninit: NonNull<Self::MaybeUninit>) -> NonNull<Self> {
        #[allow(clippy::as_conversions)]
        let maybe_uninit = maybe_uninit.as_ptr() as *mut <T as KnownLayout>::MaybeUninit;
        // SAFETY: `.as_ptr()` called on a non-null pointer.
        let maybe_uninit = unsafe { NonNull::new_unchecked(maybe_uninit) };
        let repr = <T as KnownLayout>::cast_from_maybe_uninit(maybe_uninit).as_ptr();
        #[allow(clippy::as_conversions)]
        let slf = repr as *mut Self;
        // SAFETY: `.as_ptr()` called on non-null pointer.
        unsafe { NonNull::new_unchecked(slf) }
    }

    // SAFETY: `.cast` preserves pointer address and provenance.
    fn cast_to_maybe_uninit(slf: NonNull<Self>) -> NonNull<Self::MaybeUninit> {
        #[allow(clippy::as_conversions)]
        let repr = slf.as_ptr() as *mut T;
        // SAFETY: `.as_ptr()` called on non-null pointer.
        let repr = unsafe { NonNull::new_unchecked(repr) };
        let maybe_uninit = <T as KnownLayout>::cast_to_maybe_uninit(repr).as_ptr();
        #[allow(clippy::as_conversions)]
        let maybe_uninit = maybe_uninit as *mut cell::UnsafeCell<T::MaybeUninit>;
        // SAFETY: `.as_ptr()` called on non-null pointer.
        unsafe { NonNull::new_unchecked(maybe_uninit) }
    }
}

/// Types for which a sequence of bytes all set to zero represents a valid
/// instance of the type.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(FromZeroes)]` (requires the `derive` Cargo feature).
///
/// Any memory region of the appropriate length which is guaranteed to contain
/// only zero bytes can be viewed as any `FromZeroes` type with no runtime
/// overhead. This is useful whenever memory is known to be in a zeroed state,
/// such memory returned from some allocation routines.
///
/// `FromZeroes` is ignorant of byte order. For byte order-aware types, see the
/// [`byteorder`] module.
///
/// # Safety
///
/// *This section describes what is required in order for `T: FromZeroes`, and
/// what unsafe code may assume of such types. `#[derive(FromZeroes)]` only
/// permits types which satisfy these requirements. If you don't plan on
/// implementing `FromZeroes` manually, and you don't plan on writing unsafe
/// code that operates on `FromZeroes` types, then you don't need to read this
/// section.*
///
/// If `T: FromZeroes`, then unsafe code may assume that:
/// - It is sound to treat any initialized sequence of zero bytes of length
///   `size_of::<T>()` as a `T`.
/// - Given `b: &[u8]` where `b.len() == size_of::<T>()`, `b` is aligned to
///   `align_of::<T>()`, and `b` contains only zero bytes, it is sound to
///   construct a `t: &T` at the same address as `b`, and it is sound for both
///   `b` and `t` to be live at the same time.
///
/// If a type is marked as `FromZeroes` which violates this contract, it may
/// cause undefined behavior.
///
/// If a type has the following properties, then it is sound to implement
/// `FromZeroes` for that type:
/// - If the type is a struct, all of its fields must satisfy the requirements
///   to be `FromZeroes` (they do not actually have to be `FromZeroes`).
/// - If the type is an enum, it must be C-like (meaning that all variants have
///   no fields) and it must have a variant with a discriminant of `0`. See [the
///   reference] for a description of how discriminant values are chosen.
/// - The type must not contain any [`UnsafeCell`]s (this is required in order
///   for it to be sound to construct a `&[u8]` and a `&T` to the same region of
///   memory). The type may contain references or pointers to `UnsafeCell`s so
///   long as those values can themselves be initialized from zeroes
///   (`FromZeroes` is not currently implemented for, e.g.,
///   `Option<&UnsafeCell<_>>`, but it could be one day).
///
/// [the reference]: https://doc.rust-lang.org/reference/items/enumerations.html#custom-discriminant-values-for-fieldless-enumerations
/// [`UnsafeCell`]: core::cell::UnsafeCell
///
/// # Rationale
///
/// ## Why isn't an explicit representation required for structs?
///
/// Per the [Rust reference](reference),
///
/// > The representation of a type can change the padding between fields, but
/// does not change the layout of the fields themselves.
///
/// [reference]: https://doc.rust-lang.org/reference/type-layout.html#representations
///
/// Since the layout of structs only consists of padding bytes and field bytes,
/// a struct is soundly `FromZeroes` if:
/// 1. its padding is soundly `FromZeroes`, and
/// 2. its fields are soundly `FromZeroes`.
///
/// The answer to the first question is always yes: padding bytes do not have
/// any validity constraints. A [discussion] of this question in the Unsafe Code
/// Guidelines Working Group concluded that it would be virtually unimaginable
/// for future versions of rustc to add validity constraints to padding bytes.
///
/// [discussion]: https://github.com/rust-lang/unsafe-code-guidelines/issues/174
///
/// Whether a struct is soundly `FromZeroes` therefore solely depends on whether
/// its fields are `FromZeroes`.
// TODO(#146): Document why we don't require an enum to have an explicit `repr`
// attribute.
pub unsafe trait FromZeroes {
    // The `Self: Sized` bound makes it so that `FromZeroes` is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Overwrites `self` with zeroes.
    ///
    /// Sets every byte in `self` to 0. While this is similar to doing `*self =
    /// Self::new_zeroed()`, it differs in that `zero` does not semantically
    /// drop the current value and replace it with a new one - it simply
    /// modifies the bytes of the existing value.
    fn zero(&mut self) {
        let slf: *mut Self = self;
        let len = mem::size_of_val(self);
        // SAFETY:
        // - `self` is guaranteed by the type system to be valid for writes of
        //   size `size_of_val(self)`.
        // - `u8`'s alignment is 1, and thus `self` is guaranteed to be aligned
        //   as required by `u8`.
        // - Since `Self: FromZeroes`, the all-zeroes instance is a valid
        //   instance of `Self.`
        unsafe { ptr::write_bytes(slf.cast::<u8>(), 0, len) };
    }

    /// Creates an instance of `Self` from zeroed bytes.
    fn new_zeroed() -> Self
    where
        Self: Sized,
    {
        // SAFETY: `FromZeroes` says that the all-zeroes bit pattern is legal.
        unsafe { mem::zeroed() }
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
    #[cfg(feature = "alloc")]
    fn new_box_zeroed() -> Box<Self>
    where
        Self: Sized,
    {
        // If `T` is a ZST, then return a proper boxed instance of it. There is
        // no allocation, but `Box` does require a correct dangling pointer.
        let layout = Layout::new::<Self>();
        if layout.size() == 0 {
            return Box::new(Self::new_zeroed());
        }

        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            let ptr = alloc::alloc::alloc_zeroed(layout).cast::<Self>();
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
    #[cfg(feature = "alloc")]
    fn new_box_slice_zeroed(len: usize) -> Box<[Self]>
    where
        Self: Sized,
    {
        let size = mem::size_of::<Self>()
            .checked_mul(len)
            .expect("mem::size_of::<Self>() * len overflows `usize`");
        let align = mem::align_of::<Self>();
        // On stable Rust versions <= 1.64.0, `Layout::from_size_align` has a
        // bug in which sufficiently-large allocations (those which, when
        // rounded up to the alignment, overflow `isize`) are not rejected,
        // which can cause undefined behavior. See #64 for details.
        //
        // TODO(#67): Once our MSRV is > 1.64.0, remove this assertion.
        #[allow(clippy::as_conversions)]
        let max_alloc = (isize::MAX as usize).saturating_sub(align);
        assert!(size <= max_alloc);
        // TODO(https://github.com/rust-lang/rust/issues/55724): Use
        // `Layout::repeat` once it's stabilized.
        let layout =
            Layout::from_size_align(size, align).expect("total allocation size overflows `isize`");

        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            if layout.size() != 0 {
                let ptr = alloc::alloc::alloc_zeroed(layout).cast::<Self>();
                if ptr.is_null() {
                    alloc::alloc::handle_alloc_error(layout);
                }
                Box::from_raw(slice::from_raw_parts_mut(ptr, len))
            } else {
                // `Box<[T]>` does not allocate when `T` is zero-sized or when
                // `len` is zero, but it does require a non-null dangling
                // pointer for its allocation.
                Box::from_raw(slice::from_raw_parts_mut(NonNull::<Self>::dangling().as_ptr(), len))
            }
        }
    }

    /// Creates a `Vec<Self>` from zeroed bytes.
    ///
    /// This function is useful for allocating large values of `Vec`s and
    /// zero-initializing them, without ever creating a temporary instance of
    /// `[Self; _]` (or many temporary instances of `Self`) on the stack. For
    /// example, `u8::new_vec_zeroed(1048576)` will allocate directly on the
    /// heap; it does not require storing intermediate values on the stack.
    ///
    /// On systems that use a heap implementation that supports allocating from
    /// pre-zeroed memory, using `new_vec_zeroed` may have performance benefits.
    ///
    /// If `Self` is a zero-sized type, then this function will return a
    /// `Vec<Self>` that has the correct `len`. Such a `Vec` cannot contain any
    /// actual information, but its `len()` property will report the correct
    /// value.
    ///
    /// # Panics
    ///
    /// * Panics if `size_of::<Self>() * len` overflows.
    /// * Panics if allocation of `size_of::<Self>() * len` bytes fails.
    #[cfg(feature = "alloc")]
    fn new_vec_zeroed(len: usize) -> Vec<Self>
    where
        Self: Sized,
    {
        Self::new_box_slice_zeroed(len).into()
    }
}

/// Types for which any byte pattern is valid.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(FromBytes)]` (requires the `derive` Cargo feature).
///
/// `FromBytes` types can safely be deserialized from an untrusted sequence of
/// bytes because any byte sequence corresponds to a valid instance of the type.
///
/// `FromBytes` is ignorant of byte order. For byte order-aware types, see the
/// [`byteorder`] module.
///
/// # Safety
///
/// *This section describes what is required in order for `T: FromBytes`, and
/// what unsafe code may assume of such types. `#[derive(FromBytes)]` only
/// permits types which satisfy these requirements. If you don't plan on
/// implementing `FromBytes` manually, and you don't plan on writing unsafe code
/// that operates on `FromBytes` types, then you don't need to read this
/// section.*
///
/// If `T: FromBytes`, then unsafe code may assume that:
/// - It is sound to treat any initialized sequence of bytes of length
///   `size_of::<T>()` as a `T`.
/// - Given `b: &[u8]` where `b.len() == size_of::<T>()` and `b` is aligned to
///   `align_of::<T>()`, it is sound to construct a `t: &T` at the same address
///   as `b`, and it is sound for both `b` and `t` to be live at the same time.
///
/// If a type is marked as `FromBytes` which violates this contract, it may
/// cause undefined behavior.
///
/// If a type has the following properties, then it is sound to implement
/// `FromBytes` for that type:
/// - If the type is a struct, all of its fields must satisfy the requirements
///   to be `FromBytes` (they do not actually have to be `FromBytes`)
/// - If the type is an enum:
///   - It must be a C-like enum (meaning that all variants have no fields).
///   - It must have a defined representation (`repr`s `C`, `u8`, `u16`, `u32`,
///     `u64`, `usize`, `i8`, `i16`, `i32`, `i64`, or `isize`).
///   - The maximum number of discriminants must be used (so that every possible
///     bit pattern is a valid one). Be very careful when using the `C`,
///     `usize`, or `isize` representations, as their size is
///     platform-dependent.
/// - The type must not contain any [`UnsafeCell`]s (this is required in order
///   for it to be sound to construct a `&[u8]` and a `&T` to the same region of
///   memory). The type may contain references or pointers to `UnsafeCell`s so
///   long as those values can themselves be initialized from zeroes
///   (`FromBytes` is not currently implemented for, e.g., `Option<*const
///   UnsafeCell<_>>`, but it could be one day).
///
/// [`UnsafeCell`]: core::cell::UnsafeCell
///
/// # Rationale
///
/// ## Why isn't an explicit representation required for structs?
///
/// Per the [Rust reference](reference),
///
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
pub unsafe trait FromBytes: FromZeroes {
    // The `Self: Sized` bound makes it so that `FromBytes` is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Reads a copy of `Self` from `bytes`.
    ///
    /// If `bytes.len() != size_of::<Self>()`, `read_from` returns `None`.
    fn read_from(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        let r = Ref::<_, Unalign<Self>>::new_unaligned(bytes)?;
        Some(r.read().into_inner())
    }

    /// Reads a copy of `Self` from the prefix of `bytes`.
    ///
    /// `read_from_prefix` reads a `Self` from the first `size_of::<Self>()`
    /// bytes of `bytes`. If `bytes.len() < size_of::<Self>()`, it returns
    /// `None`.
    fn read_from_prefix(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        let (r, _suffix) = Ref::<_, Unalign<Self>>::new_unaligned_from_prefix(bytes)?;
        Some(r.read().into_inner())
    }

    /// Reads a copy of `Self` from the suffix of `bytes`.
    ///
    /// `read_from_suffix` reads a `Self` from the last `size_of::<Self>()`
    /// bytes of `bytes`. If `bytes.len() < size_of::<Self>()`, it returns
    /// `None`.
    fn read_from_suffix(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        let (_prefix, r) = Ref::<_, Unalign<Self>>::new_unaligned_from_suffix(bytes)?;
        Some(r.read().into_inner())
    }
}

/// Types whose validity can be checked at runtime, allowing them to be
/// conditionally converted from byte slices.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(TryFromBytes)]`.
///
/// `TryFromBytes` types can safely be deserialized from an untrusted sequence
/// of bytes by performing a runtime check that the byte sequence contains a
/// valid instance of `Self`.
///
/// `TryFromBytes` is ignorant of byte order. For byte order-aware types, see
/// the [`byteorder`] module.
///
/// # Safety
///
/// Unsafe code may assume that [`is_bit_valid`] is correct: that, if
/// `is_bit_valid(candidate)` returns true, `candidate` contains a valid `Self`,
/// and it is sound to treat `candidate` as a `&Self`.
///
/// Implementations of `TryFromBytes` must ensure that [`is_bit_valid`]
/// satisfies its documented safety invariants.
///
/// It is unsound to implement `TryFromBytes` for a type which contains any
/// `UnsafeCell`s.
///
/// [`is_bit_valid`]: TryFromBytes::is_bit_valid
// TODO(#5): Describe in the documentation that `TryFromBytes` is compositional?
// Describe anything about the `is_bit_valid` impls that the custom derive
// emits?
pub unsafe trait TryFromBytes: KnownLayout {
    /// Does this [`MaybeValid`] contain a valid instance of `Self`?
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that, if `is_bit_valid(candidate)` returns true,
    /// `candidate` contains a valid `Self`, and that it is sound to treat
    /// `candidate` as a `&Self`.
    fn is_bit_valid(candidate: &MaybeValid<Self>) -> bool;

    /// Attempts to interpret a byte slice as a `Self`.
    ///
    /// `try_from_ref` validates that `bytes` contains a valid `Self` as defined
    /// by [`is_bit_valid`]. If it does, then `bytes` is reinterpreted as a
    /// `Self`.
    ///
    /// [`is_bit_valid`]: TryFromBytes::is_bit_valid
    // TODO(#251): In a future in which we distinguish between `FromBytes` and
    // `RefFromBytes`, this requires `where Self: RefFromBytes` to disallow
    // interior mutability.
    #[inline]
    fn try_from_ref(bytes: &[u8]) -> Option<&Self> {
        // TODO(https://github.com/rust-lang/rust/issues/115080): Inline this
        // function once #115080 is resolved.
        #[inline(always)]
        fn try_read_from_inner<T, F>(bytes: &[u8], is_bit_valid: F) -> Option<&T>
        where
            T: ?Sized + KnownLayout,
            F: FnOnce(&MaybeValid<T>) -> bool,
        {
            let maybe_valid = Ref::<_, MaybeValid<T>>::new_foo(bytes)?.into_ref();
            if is_bit_valid(maybe_valid) {
                // SAFETY: `is_bit_valid` promises that it only returns true if
                // its argument contains a valid `T`. This is exactly the safety
                // precondition of `MaybeValid::assume_valid_ref`.
                Some(unsafe { maybe_valid.assume_valid_ref() })
            } else {
                None
            }
        }

        try_read_from_inner(bytes, Self::is_bit_valid)
    }

    /// Attempts to interpret a mutable byte slice as a `Self`.
    ///
    /// `try_from_mut` validates that `bytes` contains a valid `Self` as defined
    /// by [`is_bit_valid`]. If it does, then `bytes` is reinterpreted as a
    /// `Self`.
    ///
    /// [`is_bit_valid`]: TryFromBytes::is_bit_valid
    // TODO(#251): In a future in which we distinguish between `FromBytes` and
    // `RefFromBytes`, this requires `where Self: RefFromBytes` to disallow
    // interior mutability.
    #[inline]
    fn try_from_mut(bytes: &mut [u8]) -> Option<&mut Self>
    where
        Self: AsBytes,
    {
        // TODO(https://github.com/rust-lang/rust/issues/115080): Inline this
        // function once #115080 is resolved.
        #[inline(always)]
        fn try_read_from_mut_inner<T, F>(bytes: &mut [u8], is_bit_valid: F) -> Option<&mut T>
        where
            T: ?Sized + KnownLayout + AsBytes,
            F: FnOnce(&MaybeValid<T>) -> bool,
        {
            let maybe_valid = Ref::<_, MaybeValid<T>>::new_foo(bytes)?.into_mut();
            if is_bit_valid(maybe_valid) {
                // SAFETY: `is_bit_valid` promises that it only returns true if
                // its argument contains a valid `T`. This is exactly the safety
                // precondition of `MaybeValid::assume_valid_mut`.
                Some(unsafe { maybe_valid.assume_valid_mut() })
            } else {
                None
            }
        }

        try_read_from_mut_inner(bytes, Self::is_bit_valid)
    }

    /// Attempts to read a `Self` from a byte slice.
    ///
    /// `try_read_from` validates that `bytes` contains a valid `Self` as
    /// defined by [`is_bit_valid`]. If it does, then that `Self` is copied and
    /// returned by-value.
    ///
    /// [`is_bit_valid`]: TryFromBytes::is_bit_valid
    // TODO(#251): In a future in which we distinguish between `FromBytes` and
    // `RefFromBytes`, this requires `where Self: RefFromBytes` to disallow
    // interior mutability.
    #[inline]
    fn try_read_from(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        // TODO(https://github.com/rust-lang/rust/issues/115080): Inline this
        // function once #115080 is resolved.
        #[inline(always)]
        fn try_read_from_inner<T, F>(bytes: &[u8], is_bit_valid: F) -> Option<T>
        where
            T: KnownLayout + TryFromBytes,
            F: FnOnce(&MaybeValid<T>) -> bool,
        {
            // A note on performance: We unconditionally read `size_of::<T>()`
            // bytes into the local stack frame before validation. This has
            // advantages and disadvantages:
            // - It allows `MaybeValid` to be aligned to `T`, and thus allows
            //   `is_bit_valid` to operate on an aligned value.
            // - It requires us to perform the copy even if validation fails.
            //
            // The authors believe that this is a worthwhile tradeoff. Allowing
            // `is_bit_valid` to operate on an aligned value can make the
            // generated machine code significantly smaller and faster. On the
            // other hand, we expect the vast majority of calls to
            // `try_read_from` to succeed, and in these cases, the copy will not
            // be wasted.
            let maybe_valid = MaybeValid::<T>::read_from(bytes)?;
            if is_bit_valid(&maybe_valid) {
                // SAFETY: `is_bit_valid` promises that it only returns true if
                // its argument contains a valid `T`. This is exactly the safety
                // precondition of `MaybeValid::assume_valid`.
                Some(unsafe { maybe_valid.assume_valid() })
            } else {
                None
            }
        }

        try_read_from_inner(bytes, Self::is_bit_valid)
    }
}

/// Types which are safe to treat as an immutable byte slice.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(AsBytes)]` (requires the `derive` Cargo feature).
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
/// error[E0277]: the trait bound `HasPadding<Foo, true>: ShouldBe<false>` is not satisfied
///   --> lib.rs:23:10
///    |
///  1 | #[derive(AsBytes)]
///    |          ^^^^^^^ the trait `ShouldBe<false>` is not implemented for `HasPadding<Foo, true>`
///    |
///    = help: the trait `ShouldBe<VALUE>` is implemented for `HasPadding<T, VALUE>`
/// ```
///
/// This error indicates that the type being annotated has padding bytes, which
/// is illegal for `AsBytes` types. Consider reducing the alignment of some
/// fields by using types in the [`byteorder`] module, adding explicit struct
/// fields where those padding bytes would be, or using `#[repr(packed)]`. See
/// the Rust Reference's [page on type layout](type-layout) for more information
/// about type layout and padding.
///
/// # Safety
///
/// *This section describes what is required in order for `T: AsBytes`, and what
/// unsafe code may assume of such types. `#[derive(AsBytes)]` only permits
/// types which satisfy these requirements. If you don't plan on implementing
/// `AsBytes` manually, and you don't plan on writing unsafe code that operates
/// on `AsBytes` types, then you don't need to read this section.*
///
/// If `T: AsBytes`, then unsafe code may assume that:
/// - It is sound to treat any `t: T` as an immutable `[u8]` of length
///   `size_of_val(t)`.
/// - Given `t: &T`, it is sound to construct a `b: &[u8]` where `b.len() ==
///   size_of_val(t)` at the same address as `t`, and it is sound for both `b`
///   and `t` to be live at the same time.
///
/// If a type is marked as `AsBytes` which violates this contract, it may cause
/// undefined behavior.
///
/// If a type has the following properties, then it is sound to implement
/// `AsBytes` for that type:
/// - If the type is a struct:
///   - It must have a defined representation (`repr(C)`, `repr(transparent)`,
///     or `repr(packed)`).
///   - All of its fields must satisfy the requirements to be `AsBytes` (they do
///     not actually have to be `AsBytes`).
///   - Its layout must have no padding. This is always true for
///     `repr(transparent)` and `repr(packed)`. For `repr(C)`, see the layout
///     algorithm described in the [Rust Reference].
/// - If the type is an enum:
///   - It must be a C-like enum (meaning that all variants have no fields).
///   - It must have a defined representation (`repr`s `C`, `u8`, `u16`, `u32`,
///     `u64`, `usize`, `i8`, `i16`, `i32`, `i64`, or `isize`).
/// - The type must not contain any [`UnsafeCell`]s (this is required in order
///   for it to be sound to construct a `&[u8]` and a `&T` to the same region of
///   memory). The type may contain references or pointers to `UnsafeCell`s so
///   long as those values can themselves be initialized from zeroes (`AsBytes`
///   is not currently implemented for, e.g., `Option<&UnsafeCell<_>>`, but it
///   could be one day).
///
/// [type-layout]: https://doc.rust-lang.org/reference/type-layout.html
/// [Rust Reference]: https://doc.rust-lang.org/reference/type-layout.html
/// [`UnsafeCell`]: core::cell::UnsafeCell
pub unsafe trait AsBytes {
    // The `Self: Sized` bound makes it so that this function doesn't prevent
    // `AsBytes` from being object safe. Note that other `AsBytes` methods
    // prevent object safety, but those provide a benefit in exchange for object
    // safety. If at some point we remove those methods, change their type
    // signatures, or move them out of this trait so that `AsBytes` is object
    // safe again, it's important that this function not prevent object safety.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Gets the bytes of this value.
    ///
    /// `as_bytes` provides access to the bytes of this value as an immutable
    /// byte slice.
    fn as_bytes(&self) -> &[u8] {
        // Note that this method does not have a `Self: Sized` bound;
        // `size_of_val` works for unsized values too.
        let len = mem::size_of_val(self);
        let slf: *const Self = self;

        // SAFETY:
        // - `slf.cast::<u8>()` is valid for reads for `len *
        //   mem::size_of::<u8>()` many bytes because...
        //   - `slf` is the same pointer as `self`, and `self` is a reference
        //     which points to an object whose size is `len`. Thus...
        //     - The entire region of `len` bytes starting at `slf` is contained
        //       within a single allocation.
        //     - `slf` is non-null.
        //   - `slf` is trivially aligned to `align_of::<u8>() == 1`.
        // - `Self: AsBytes` ensures that all of the bytes of `slf` are
        //   initialized.
        // - Since `slf` is derived from `self`, and `self` is an immutable
        //   reference, the only other references to this memory region that
        //   could exist are other immutable references, and those don't allow
        //   mutation. `AsBytes` prohibits types which contain `UnsafeCell`s,
        //   which are the only types for which this rule wouldn't be
        //   sufficient.
        // - The total size of the resulting slice is no larger than
        //   `isize::MAX` because no allocation produced by safe code can be
        //   larger than `isize::MAX`.
        unsafe { slice::from_raw_parts(slf.cast::<u8>(), len) }
    }

    /// Gets the bytes of this value mutably.
    ///
    /// `as_bytes_mut` provides access to the bytes of this value as a mutable
    /// byte slice.
    fn as_bytes_mut(&mut self) -> &mut [u8]
    where
        Self: FromBytes,
    {
        // Note that this method does not have a `Self: Sized` bound;
        // `size_of_val` works for unsized values too.
        let len = mem::size_of_val(self);
        let slf: *mut Self = self;

        // SAFETY:
        // - `slf.cast::<u8>()` is valid for reads and writes for `len *
        //   mem::size_of::<u8>()` many bytes because...
        //   - `slf` is the same pointer as `self`, and `self` is a reference
        //     which points to an object whose size is `len`. Thus...
        //     - The entire region of `len` bytes starting at `slf` is contained
        //       within a single allocation.
        //     - `slf` is non-null.
        //   - `slf` is trivially aligned to `align_of::<u8>() == 1`.
        // - `Self: AsBytes` ensures that all of the bytes of `slf` are
        //   initialized.
        // - `Self: FromBytes` ensures that no write to this memory region
        //   could result in it containing an invalid `Self`.
        // - Since `slf` is derived from `self`, and `self` is a mutable
        //   reference, no other references to this memory region can exist.
        // - The total size of the resulting slice is no larger than
        //   `isize::MAX` because no allocation produced by safe code can be
        //   larger than `isize::MAX`.
        unsafe { slice::from_raw_parts_mut(slf.cast::<u8>(), len) }
    }

    /// Writes a copy of `self` to `bytes`.
    ///
    /// If `bytes.len() != size_of_val(self)`, `write_to` returns `None`.
    fn write_to(&self, bytes: &mut [u8]) -> Option<()> {
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
    fn write_to_prefix(&self, bytes: &mut [u8]) -> Option<()> {
        let size = mem::size_of_val(self);
        bytes.get_mut(..size)?.copy_from_slice(self.as_bytes());
        Some(())
    }

    /// Writes a copy of `self` to the suffix of `bytes`.
    ///
    /// `write_to_suffix` writes `self` to the last `size_of_val(self)` bytes of
    /// `bytes`. If `bytes.len() < size_of_val(self)`, it returns `None`.
    fn write_to_suffix(&self, bytes: &mut [u8]) -> Option<()> {
        let start = bytes.len().checked_sub(mem::size_of_val(self))?;
        bytes
            .get_mut(start..)
            .expect("`start` should be in-bounds of `bytes`")
            .copy_from_slice(self.as_bytes());
        Some(())
    }
}

/// Types with no alignment requirement.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(Unaligned)]` (requires the `derive` Cargo feature).
///
/// If `T: Unaligned`, then `align_of::<T>() == 1`.
///
/// # Safety
///
/// *This section describes what is required in order for `T: Unaligned`, and
/// what unsafe code may assume of such types. `#[derive(Unaligned)]` only
/// permits types which satisfy these requirements. If you don't plan on
/// implementing `Unaligned` manually, and you don't plan on writing unsafe code
/// that operates on `Unaligned` types, then you don't need to read this
/// section.*
///
/// If `T: Unaligned`, then unsafe code may assume that it is sound to produce a
/// reference to `T` at any memory location regardless of alignment. If a type
/// is marked as `Unaligned` which violates this contract, it may cause
/// undefined behavior.
pub unsafe trait Unaligned {
    // The `Self: Sized` bound makes it so that `Unaligned` is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;
}

safety_comment! {
    /// SAFETY:
    /// Per the reference [1], "the unit tuple (`()`) ... is guaranteed as a
    /// zero-sized type to have a size of 0 and an alignment of 1."
    /// - `TryFromBytes` (with no validator), `FromZeroes`, `FromBytes`: There
    ///   is only one possible sequence of 0 bytes, and `()` is inhabited.
    /// - `AsBytes`: Since `()` has size 0, it contains no padding bytes.
    /// - `Unaligned`: `()` has alignment 1.
    ///
    /// [1] https://doc.rust-lang.org/reference/type-layout.html#tuple-layout
    unsafe_impl!((): TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_unaligned!(());
}

safety_comment! {
    /// SAFETY:
    /// - `TryFromBytes` (with no validator), `FromZeroes`, `FromBytes`: all bit
    ///   patterns are valid for integers [1]
    /// - `AsBytes`: integers have no padding bytes [1]
    /// - `Unaligned` (`u8` and `i8` only): The reference [2] specifies the size
    ///   of `u8` and `i8` as 1 byte. We also know that:
    ///   - Alignment is >= 1
    ///   - Size is an integer multiple of alignment
    ///   - The only value >= 1 for which 1 is an integer multiple is 1
    ///   Therefore, the only possible alignment for `u8` and `i8` is 1.
    ///
    /// [1] TODO(https://github.com/rust-lang/reference/issues/1291): Once the
    ///     reference explicitly guarantees these properties, cite it.
    /// [2] https://doc.rust-lang.org/reference/type-layout.html#primitive-data-layout
    unsafe_impl!(u8: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
    unsafe_impl!(i8: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_unaligned!(u8, i8);
    unsafe_impl!(u16: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i16: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(u32: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i32: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(u64: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i64: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(u128: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(i128: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(usize: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(isize: TryFromBytes, FromZeroes, FromBytes, AsBytes);
}

safety_comment! {
    /// SAFETY:
    /// - `TryFromBytes` (with no validator), `FromZeroes`, `FromBytes`: the
    ///   `{f32,f64}::from_bits` constructors' documentation [1, 2] states that
    ///   they are currently equivalent to `transmute`. [3]
    /// - `AsBytes`: the `{f32,f64}::to_bits` methods' documentation [4,5]
    ///   states that they are currently equivalent to `transmute`. [3]
    ///
    /// TODO: Make these arguments more precisely in terms of the documentation.
    ///
    /// [1] https://doc.rust-lang.org/nightly/std/primitive.f32.html#method.from_bits
    /// [2] https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.from_bits
    /// [3] TODO(https://github.com/rust-lang/reference/issues/1291): Once the
    ///     reference explicitly guarantees these properties, cite it.
    /// [4] https://doc.rust-lang.org/nightly/std/primitive.f32.html#method.to_bits
    /// [5] https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.to_bits
    unsafe_impl!(f32: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(f64: TryFromBytes, FromZeroes, FromBytes, AsBytes);
}

safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`: Per the reference [1], 0x00 is a valid bit pattern for
    ///   `bool`.
    /// - `AsBytes`: Per the reference [1], `bool` always has a size of 1 with
    ///   valid bit patterns 0x01 and 0x00, so the only byte of the bool is
    ///   always initialized
    /// - `Unaligned`: Per the reference [1], "[a]n object with the boolean type
    ///   has a size and alignment of 1 each."
    ///
    /// [1] https://doc.rust-lang.org/reference/types/boolean.html
    unsafe_impl!(bool: FromZeroes, AsBytes, Unaligned);
    assert_unaligned!(bool);
    /// SAFETY:
    /// - Since `bool`'s single byte is always initialized, `MaybeValid<bool>`'s
    ///   single byte must also always be initialized. Thus, it is sound to
    ///   transmute a `MaybeValid<bool>` to a `u8`. Since `u8` has alignment 1,
    ///   there can never be any alignment issues, and so it is sound to
    ///   transmute a `&MaybeValid<bool>` to a `&u8`.
    /// - All values less than 2 are valid instances of `bool` [1], and so this
    ///   is a sound implementation of `TryFromBytes::is_bit_valid`.
    ///
    /// [1] https://doc.rust-lang.org/reference/types/boolean.html
    unsafe_impl!(bool: TryFromBytes; |byte: &u8| *byte < 2);
}
safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`: Per the reference [1], 0x0000 is a valid bit pattern for
    ///   `char`.
    /// - `AsBytes`: `char` is represented as a 32-bit unsigned word (`u32`)
    ///   [1], which is `AsBytes`. Note that unlike `u32`, not all bit patterns
    ///   are valid for `char`.
    ///
    /// [1] https://doc.rust-lang.org/reference/types/textual.html
    unsafe_impl!(char: FromZeroes, AsBytes);
    /// SAFETY:
    /// - Since `char`'s 4 bytes are always initialized, `MaybeValid<char>`'s
    ///   bytes must also always be initialized. Thus, it is sound to transmute
    ///   a `MaybeValid<char>` to a `[u8; 4]`. Since `[u8; 4]` has alignment 1,
    ///   there can never be any alignment issues, and so it is sound to
    ///   transmute a `&MaybeValid<char>` to a `&[u8; 4]`.
    /// - Since we use `from_ne_bytes`, `c` has the same bits as the argument to
    ///   `is_bit_valid`. `char::from_u32` guarantees that it returns `None` if
    ///   its input is not a valid `char` [1], and so this is a sound
    ///   implementation of `TryFromBytes::is_bit_valid`.
    ///
    /// [1] https://doc.rust-lang.org/std/primitive.char.html#method.from_u32
    unsafe_impl!(char: TryFromBytes; |bytes: &[u8; 4]| {
        let c = u32::from_ne_bytes(*bytes);
        char::from_u32(c).is_some()
    });
}
safety_comment! {
    /// SAFETY:
    /// - `FromZeroes`, `AsBytes`, `Unaligned`: Per the reference [1], `str` has
    ///   the same layout as `[u8]`, and `[u8]` is `FromZeroes`, `AsBytes`, and
    ///   `Unaligned`.
    ///
    /// Note that we don't `assert_unaligned!(str)` because `assert_unaligned!`
    /// uses `align_of`, which only works for `Sized` types.
    ///
    /// [1] https://doc.rust-lang.org/reference/type-layout.html#str-layout
    unsafe_impl!(str: FromZeroes, AsBytes, Unaligned);
    /// SAFETY:
    /// - Since `str`'s bytes are all always initialized, `MaybeValid<str>`'s
    ///   bytes must also always be initialized. Thus, it is sound to transmute
    ///   `MaybeValid<str>` to `[u8]`. Since `str` and `[u8]` have the same
    ///   layout, they have the same alignment, and so it is sound to transmute
    ///   `&MaybeValid<str>` to `&u8`.
    /// - `str`'s bit validity requirement is that it is valid UTF-8. [1] Thus,
    ///   if `from_utf8` can successfully convert `bytes` to a `str`, then the
    ///   `str` is valid [2], and so this is a sound implementation of
    ///   `TryFromBytes::is_bit_valid`.
    ///
    /// [1] https://doc.rust-lang.org/reference/types/textual.html
    /// [2] https://doc.rust-lang.org/core/str/fn.from_utf8.html
    unsafe_impl!(str: TryFromBytes; |bytes: &[u8]| {
        core::str::from_utf8(bytes).is_ok()
    });
}

safety_comment! {
    // `NonZeroXxx` is `AsBytes`, but not `FromZeroes` or `FromBytes`.
    //
    /// SAFETY:
    /// - `AsBytes`: `NonZeroXxx` has the same layout as its associated
    ///    primitive. Since it is the same size, this guarantees it has no
    ///    padding - integers have no padding, and there's no room for padding
    ///    if it can represent all of the same values except 0.
    /// - `Unaligned`: `NonZeroU8` and `NonZeroI8` document that
    ///   `Option<NonZeroU8>` and `Option<NonZeroI8>` both have size 1. [1] [2]
    ///   This is worded in a way that makes it unclear whether it's meant as a
    ///   guarantee, but given the purpose of those types, it's virtually
    ///   unthinkable that that would ever change. `Option` cannot be smaller
    ///   than its contained type, which implies that, and `NonZeroX8` are of
    ///   size 1 or 0. `NonZeroX8` can represent multiple states, so they cannot
    ///   be 0 bytes, which means that they must be 1 byte. The only valid
    ///   alignment for a 1-byte type is 1.
    ///
    /// [1] https://doc.rust-lang.org/stable/std/num/struct.NonZeroU8.html
    /// [2] https://doc.rust-lang.org/stable/std/num/struct.NonZeroI8.html
    /// TODO(https://github.com/rust-lang/rust/pull/104082): Cite documentation
    /// that layout is the same as primitive layout.
    unsafe_impl!(NonZeroU8: AsBytes, Unaligned);
    unsafe_impl!(NonZeroI8: AsBytes, Unaligned);
    assert_unaligned!(NonZeroU8, NonZeroI8);
    unsafe_impl!(NonZeroU16: AsBytes);
    unsafe_impl!(NonZeroI16: AsBytes);
    unsafe_impl!(NonZeroU32: AsBytes);
    unsafe_impl!(NonZeroI32: AsBytes);
    unsafe_impl!(NonZeroU64: AsBytes);
    unsafe_impl!(NonZeroI64: AsBytes);
    unsafe_impl!(NonZeroU128: AsBytes);
    unsafe_impl!(NonZeroI128: AsBytes);
    unsafe_impl!(NonZeroUsize: AsBytes);
    unsafe_impl!(NonZeroIsize: AsBytes);

    /// SAFETY:
    /// - `NonZeroXxx` has the same layout as `Xxx`. Also, every byte of
    ///   `NonZeroXxx` is required to be initialized, so it is guaranteed that
    ///   every byte of `MaybeValid<NonZeroXxx>` must also be initialized. Thus,
    ///   it is sound to transmute a `&MaybeValid<NonZeroXxx>` to a `&Xxx`.
    /// - `NonZeroXxx`'s only validity constraint is that it is non-zero, which
    ///   all of these closures ensure. Thus, these closures are sound
    ///   implementations of `TryFromBytes::is_bit_valid`.
    unsafe_impl!(NonZeroU8: TryFromBytes; |n: &u8| *n != 0);
    unsafe_impl!(NonZeroI8: TryFromBytes; |n: &i8| *n != 0);
    unsafe_impl!(NonZeroU16: TryFromBytes; |n: &u16| *n != 0);
    unsafe_impl!(NonZeroI16: TryFromBytes; |n: &i16| *n != 0);
    unsafe_impl!(NonZeroU32: TryFromBytes; |n: &u32| *n != 0);
    unsafe_impl!(NonZeroI32: TryFromBytes; |n: &i32| *n != 0);
    unsafe_impl!(NonZeroU64: TryFromBytes; |n: &u64| *n != 0);
    unsafe_impl!(NonZeroI64: TryFromBytes; |n: &i64| *n != 0);
    unsafe_impl!(NonZeroU128: TryFromBytes; |n: &u128| *n != 0);
    unsafe_impl!(NonZeroI128: TryFromBytes; |n: &i128| *n != 0);
    unsafe_impl!(NonZeroUsize: TryFromBytes; |n: &usize| *n != 0);
    unsafe_impl!(NonZeroIsize: TryFromBytes; |n: &isize| *n != 0);
}
safety_comment! {
    /// SAFETY:
    /// - `TryFromBytes` (with no validator), `FromZeroes`, `FromBytes`,
    ///   `AsBytes`: The Rust compiler reuses `0` value to represent `None`, so
    ///   `size_of::<Option<NonZeroXxx>>() == size_of::<xxx>()`; see
    ///   `NonZeroXxx` documentation.
    /// - `Unaligned`: `NonZeroU8` and `NonZeroI8` document that
    ///   `Option<NonZeroU8>` and `Option<NonZeroI8>` both have size 1. [1] [2]
    ///   This is worded in a way that makes it unclear whether it's meant as a
    ///   guarantee, but given the purpose of those types, it's virtually
    ///   unthinkable that that would ever change. The only valid alignment for
    ///   a 1-byte type is 1.
    ///
    /// [1] https://doc.rust-lang.org/stable/std/num/struct.NonZeroU8.html
    /// [2] https://doc.rust-lang.org/stable/std/num/struct.NonZeroI8.html
    ///
    /// TODO(https://github.com/rust-lang/rust/pull/104082): Cite documentation
    /// for layout guarantees.
    unsafe_impl!(Option<NonZeroU8>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
    unsafe_impl!(Option<NonZeroI8>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_unaligned!(Option<NonZeroU8>, Option<NonZeroI8>);
    unsafe_impl!(Option<NonZeroU16>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI16>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroU32>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI32>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroU64>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI64>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroU128>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroI128>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroUsize>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
    unsafe_impl!(Option<NonZeroIsize>: TryFromBytes, FromZeroes, FromBytes, AsBytes);
}

safety_comment! {
    /// SAFETY:
    /// For all `T`, `PhantomData<T>` has size 0 and alignment 1. [1]
    /// - `TryFromBytes` (with no validator), `FromZeroes`, `FromBytes`: There
    ///   is only one possible sequence of 0 bytes, and `PhantomData` is
    ///   inhabited.
    /// - `AsBytes`: Since `PhantomData` has size 0, it contains no padding
    ///   bytes.
    /// - `Unaligned`: Per the preceding reference, `PhantomData` has alignment
    ///   1.
    ///
    /// [1] https://doc.rust-lang.org/std/marker/struct.PhantomData.html#layout-1
    unsafe_impl!(T: ?Sized => TryFromBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => FromZeroes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => FromBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => AsBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => Unaligned for PhantomData<T>);
    assert_unaligned!(PhantomData<()>, PhantomData<u8>, PhantomData<u64>);
}
safety_comment! {
    /// SAFETY:
    /// `Wrapping<T>` is guaranteed by its docs [1] to have the same layout as
    /// `T`. Also, `Wrapping<T>` is `#[repr(transparent)]`, and has a single
    /// field, which is `pub`. Per the reference [2], this means that the
    /// `#[repr(transparent)]` attribute is "considered part of the public ABI".
    ///
    /// [1] https://doc.rust-lang.org/nightly/core/num/struct.Wrapping.html#layout-1
    /// [2] https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent
    // TODO(#5): Implement `TryFromBytes` for `Wrapping<T>`.
    unsafe_impl!(T: FromZeroes => FromZeroes for Wrapping<T>);
    unsafe_impl!(T: FromBytes => FromBytes for Wrapping<T>);
    unsafe_impl!(T: AsBytes => AsBytes for Wrapping<T>);
    unsafe_impl!(T: Unaligned => Unaligned for Wrapping<T>);
    assert_unaligned!(Wrapping<()>, Wrapping<u8>);
}
safety_comment! {
    // `MaybeUninit<T>` is `FromZeroes` and `FromBytes`, but never `AsBytes`
    // since it may contain uninitialized bytes.
    //
    /// SAFETY:
    /// - `TryFromBytes` (with no validator), `FromZeroes`, `FromBytes`:
    ///   `MaybeUninit<T>` has no restrictions on its contents. Unfortunately,
    ///   in addition to bit validity, these traits also require that
    ///   implementers contain no `UnsafeCell`s. Thus, we require a trait bound
    ///   for `T` in order to ensure that `T` - and thus `MaybeUninit<T>` -
    ///   contains to `UnsafeCell`s. Thus, requiring that `T` implement each of
    ///   these traits is sufficient.
    /// - `Unaligned`: `MaybeUninit<T>` is guaranteed by its documentation [1]
    ///   to have the same alignment as `T`.
    ///
    /// [1] https://doc.rust-lang.org/nightly/core/mem/union.MaybeUninit.html#layout-1
    ///
    /// TODO(https://github.com/google/zerocopy/issues/251): If we split
    /// `FromBytes` and `RefFromBytes`, or if we introduce a separate
    /// `NoCell`/`Freeze` trait, we can relax the trait bounds for `FromZeroes`
    /// and `FromBytes`.
    unsafe_impl!(T: TryFromBytes => TryFromBytes for mem::MaybeUninit<T>);
    unsafe_impl!(T: FromZeroes => FromZeroes for mem::MaybeUninit<T>);
    unsafe_impl!(T: FromBytes => FromBytes for mem::MaybeUninit<T>);
    unsafe_impl!(T: Unaligned => Unaligned for mem::MaybeUninit<T>);
    assert_unaligned!(mem::MaybeUninit<()>, mem::MaybeUninit<u8>);
}
safety_comment! {
    /// SAFETY:
    /// `ManuallyDrop` has the same layout as `T`, and accessing the inner value
    /// is safe (meaning that it's unsound to leave the inner value
    /// uninitialized while exposing the `ManuallyDrop` to safe code). It's nearly
    /// certain that `ManuallyDrop` has the same bit validity as `T`, but this
    /// is technically not yet documented. [1]
    /// - `TryFromBytes`: `ManuallyDrop<T>` has the same layout and bit validity
    ///   as `T`, so it is sound to convert `&MaybeValid<ManuallyDrop<T>>` to
    ///   `&MaybeValid<T>`, and if `T::is_bit_valid` accepts a `T` as valid,
    ///   then that `T` also constitutes a valid `ManuallyDrop<T>`.
    /// - `FromZeroes`, `FromBytes`: Since it has the same layout as `T`, any
    ///   valid `T` is a valid `ManuallyDrop<T>`. If `T: FromZeroes`, a sequence
    ///   of zero bytes is a valid `T`, and thus a valid `ManuallyDrop<T>`. If
    ///   `T: FromBytes`, any sequence of bytes is a valid `T`, and thus a valid
    ///   `ManuallyDrop<T>`.
    /// - `AsBytes`: Since it has the same layout as `T`, and since it's unsound
    ///   to let safe code access a `ManuallyDrop` whose inner value is
    ///   uninitialized, safe code can only ever access a `ManuallyDrop` whose
    ///   contents are a valid `T`. Since `T: AsBytes`, this means that safe
    ///   code can only ever access a `ManuallyDrop` with all initialized bytes.
    /// - `Unaligned`: `ManuallyDrop` has the same layout (and thus alignment)
    ///   as `T`, and `T: Unaligned` guarantees that that alignment is 1.
    ///
    /// [1] https://github.com/rust-lang/rust/pull/115522
    ///
    /// TODO(#5): Implement `TryFromBytes` for `ManuallyDrop<T>` for `T: ?Sized`.
    ///
    /// TODO(https://github.com/rust-lang/rust/pull/115522): Update these docs
    /// once ManuallyDrop bit validity is guaranteed.
    unsafe_impl!(T: TryFromBytes => TryFromBytes for ManuallyDrop<T>; |c: &MaybeValid<ManuallyDrop<T>>| {
        // TODO(https://github.com/rust-lang/rust/issues/115080): Inline this
        // function once #115080 is resolved. That should also let us change the
        // type of `c` in the outer closure to `&MaybeValid<T>` and let the
        // `unsafe_impl!` macro handle the conversion for us, simplifying this
        // body to just `<T as TryFromBytes>::is_bit_valid(c)`.
        #[inline(always)]
        fn is_bit_valid<T: KnownLayout, F: Fn(&MaybeValid<T>) -> bool>(
            c: &MaybeValid<ManuallyDrop<T>>,
            is_bit_valid: F,
        ) -> bool {
            // SAFETY: `ManuallyDrop<T>` has the same layout and bit validity as
            // `T`, so it is sound to convert a `&MaybeValid<ManuallyDrop<T>>`
            // to a `&MaybeValid<T>`.
            //
            // Note: this Clippy warning is only emitted on our MSRV (1.61), but
            // not on later versions of Clippy. Thus, we consider it spurious.
            #[allow(clippy::as_conversions)]
            let candidate = unsafe { &*(c as *const MaybeValid<ManuallyDrop<T>> as *const MaybeValid<T>) };
            is_bit_valid(candidate)
        }
        is_bit_valid(c, T::is_bit_valid)
    });
    unsafe_impl!(T: ?Sized + FromZeroes => FromZeroes for ManuallyDrop<T>);
    unsafe_impl!(T: ?Sized + FromBytes => FromBytes for ManuallyDrop<T>);
    unsafe_impl!(T: ?Sized + AsBytes => AsBytes for ManuallyDrop<T>);
    unsafe_impl!(T: ?Sized + Unaligned => Unaligned for ManuallyDrop<T>);
    assert_unaligned!(ManuallyDrop<()>, ManuallyDrop<u8>);
}
safety_comment! {
    /// SAFETY:
    /// Per the reference [1]:
    ///
    ///   An array of `[T; N]` has a size of `size_of::<T>() * N` and the same
    ///   alignment of `T`. Arrays are laid out so that the zero-based `nth`
    ///   element of the array is offset from the start of the array by `n *
    ///   size_of::<T>()` bytes.
    ///
    ///   ...
    ///
    ///   Slices have the same layout as the section of the array they slice.
    ///
    /// In other words, the layout of a `[T]` or `[T; N]` is a sequence of `T`s
    /// laid out back-to-back with no bytes in between. Therefore, `[T]` or `[T;
    /// N]` are `FromZeroes`, `FromBytes`, and `AsBytes` if `T` is
    /// (respectively). Furthermore, since an array/slice has "the same
    /// alignment of `T`", `[T]` and `[T; N]` are `Unaligned` if `T` is.
    ///
    /// Finally, because of this layout equivalence, an instance of `[T]` or
    /// `[T; N]` is valid if each `T` is valid. Thus, it is sound to implement
    /// `TryFromBytes::is_bit_valid` by calling `is_bit_valid` on each element.
    ///
    /// Note that we don't `assert_unaligned!` for slice types because
    /// `assert_unaligned!` uses `align_of`, which only works for `Sized` types.
    ///
    /// [1] https://doc.rust-lang.org/reference/type-layout.html#array-layout
    unsafe_impl!(const N: usize, T: TryFromBytes => TryFromBytes for [T; N]; |c: &MaybeValid<[T; N]>| {
        <[T] as TryFromBytes>::is_bit_valid(c.as_slice())
    });
    unsafe_impl!(const N: usize, T: FromZeroes => FromZeroes for [T; N]);
    unsafe_impl!(const N: usize, T: FromBytes => FromBytes for [T; N]);
    unsafe_impl!(const N: usize, T: AsBytes => AsBytes for [T; N]);
    unsafe_impl!(const N: usize, T: Unaligned => Unaligned for [T; N]);
    assert_unaligned!([(); 0], [(); 1], [u8; 0], [u8; 1]);
    unsafe_impl!(T: TryFromBytes => TryFromBytes for [T]; |c: &MaybeValid<[T]>| {
        // TODO(https://github.com/rust-lang/rust/issues/115080): Inline this
        // function once #115080 is resolved.
        #[inline(always)]
        fn is_bit_valid<T: KnownLayout, F: Fn(&MaybeValid<T>) -> bool>(
            c: &MaybeValid<[T]>,
            is_bit_valid: F,
        ) -> bool {
            c.as_slice_of_maybe_valids().iter().all(is_bit_valid)
        }
        is_bit_valid(c, T::is_bit_valid)
    });
    unsafe_impl!(T: FromZeroes => FromZeroes for [T]);
    unsafe_impl!(T: FromBytes => FromBytes for [T]);
    unsafe_impl!(T: AsBytes => AsBytes for [T]);
    unsafe_impl!(T: Unaligned => Unaligned for [T]);
}

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
//   `FromZeroes`, `FromBytes`, `TryFromBytes`, or `AsBytes`, that SIMD type is
//   also `FromZeroes`, `FromBytes`, `TryFromBytes`, or `AsBytes` respectively.
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
// `FromZeroes`, `FromBytes`, `TryFromBytes`, or `AsBytes` is next to zero, as
// that would defeat the entire purpose of SIMD types. Nonetheless, we put this
// behavior behind the `simd` Cargo feature, which requires consumers to opt
// into this stability hazard.
//
// [1] https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
// [2] https://github.com/rust-lang/unsafe-code-guidelines/issues/38
#[cfg(feature = "simd")]
mod simd {
    /// Defines a module which implements `FromZeroes`, `FromBytes`,
    /// `TryFromBytes`, and `AsBytes` for a set of types from a module in
    /// `core::arch`.
    ///
    /// `$arch` is both the name of the defined module and the name of the
    /// module in `core::arch`, and `$typ` is the list of items from that module
    /// for which to implement `FromZeroes`, `FromBytes`, `TryFromBytes`, and
    /// `AsBytes`.
    #[allow(unused_macros)] // `allow(unused_macros)` is needed because some
                            // target/feature combinations don't emit any impls
                            // and thus don't use this macro.
    macro_rules! simd_arch_mod {
        ($arch:ident, $($typ:ident),*) => {
            mod $arch {
                use core::arch::$arch::{$($typ),*};

                use crate::*;
                impl_known_layout!($($typ),*);
                safety_comment! {
                    /// SAFETY:
                    /// See comment on module definition for justification.
                    $( unsafe_impl!($typ: TryFromBytes, FromZeroes, FromBytes, AsBytes); )*
                }
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
    #[cfg(target_arch = "aarch64")]
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
    simd_arch_mod!(arm, int8x4_t, uint8x4_t);
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
            const fn transmute<T: $crate::AsBytes, U: $crate::FromBytes>(_t: T) -> U {
                unreachable!()
            }
            transmute(e)
        } else {
            // SAFETY: `core::mem::transmute` ensures that the type of `e` and
            // the type of this macro invocation expression have the same size.
            // We know this transmute is safe thanks to the `AsBytes` and
            // `FromBytes` bounds enforced by the `false` branch.
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
/// use zerocopy::{AsBytes, ByteSlice, ByteSliceMut, FromBytes, FromZeroes, Ref, Unaligned};
///
/// #[derive(FromZeroes, FromBytes, AsBytes, Unaligned)]
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
/// impl<B: ByteSlice> UdpPacket<B> {
///     pub fn parse(bytes: B) -> Option<UdpPacket<B>> {
///         let (header, body) = Ref::new_unaligned_from_prefix(bytes)?;
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
pub struct Ref<B, T: ?Sized>(B, PhantomData<T>);

/// Deprecated: prefer [`Ref`] instead.
#[deprecated(since = "0.7.0", note = "LayoutVerified has been renamed to Ref")]
#[doc(hidden)]
pub type LayoutVerified<B, T> = Ref<B, T>;

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: ?Sized + KnownLayout,
{
    // TODO:
    // - Pick a name
    // - Doc comment
    fn new_foo(bytes: B) -> Option<Ref<B, T>> {
        let (_elems, _split_at, suffix_bytes) =
            T::validate_size_align(bytes.deref(), bytes.len(), CastType::Prefix)?;
        if suffix_bytes != 0 {
            return None;
        }

        // SAFETY: TODO
        Some(Ref(bytes, PhantomData))
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
{
    /// Constructs a new `Ref`.
    ///
    /// `new` verifies that `bytes.len() == size_of::<T>()` and that `bytes` is
    /// aligned to `align_of::<T>()`, and constructs a new `Ref`. If either of
    /// these checks fail, it returns `None`.
    #[inline]
    pub fn new(bytes: B) -> Option<Ref<B, T>> {
        if bytes.len() != mem::size_of::<T>() || !util::aligned_to::<_, T>(bytes.deref()) {
            return None;
        }
        Some(Ref(bytes, PhantomData))
    }

    /// Constructs a new `Ref` from the prefix of a byte slice.
    ///
    /// `new_from_prefix` verifies that `bytes.len() >= size_of::<T>()` and that
    /// `bytes` is aligned to `align_of::<T>()`. It consumes the first
    /// `size_of::<T>()` bytes from `bytes` to construct a `Ref`, and returns
    /// the remaining bytes to the caller. If either the length or alignment
    /// checks fail, it returns `None`.
    #[inline]
    pub fn new_from_prefix(bytes: B) -> Option<(Ref<B, T>, B)> {
        if bytes.len() < mem::size_of::<T>() || !util::aligned_to::<_, T>(bytes.deref()) {
            return None;
        }
        let (bytes, suffix) = bytes.split_at(mem::size_of::<T>());
        Some((Ref(bytes, PhantomData), suffix))
    }

    /// Constructs a new `Ref` from the suffix of a byte slice.
    ///
    /// `new_from_suffix` verifies that `bytes.len() >= size_of::<T>()` and that
    /// the last `size_of::<T>()` bytes of `bytes` are aligned to
    /// `align_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the preceding bytes to the
    /// caller. If either the length or alignment checks fail, it returns
    /// `None`.
    #[inline]
    pub fn new_from_suffix(bytes: B) -> Option<(B, Ref<B, T>)> {
        let bytes_len = bytes.len();
        let split_at = bytes_len.checked_sub(mem::size_of::<T>())?;
        let (prefix, bytes) = bytes.split_at(split_at);
        if !util::aligned_to::<_, T>(bytes.deref()) {
            return None;
        }
        Some((prefix, Ref(bytes, PhantomData)))
    }
}

impl<B, T> Ref<B, [T]>
where
    B: ByteSlice,
{
    /// Constructs a new `Ref` of a slice type.
    ///
    /// `new_slice` verifies that `bytes.len()` is a multiple of
    /// `size_of::<T>()` and that `bytes` is aligned to `align_of::<T>()`, and
    /// constructs a new `Ref`. If either of these checks fail, it returns
    /// `None`.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice(bytes: B) -> Option<Ref<B, [T]>> {
        let remainder = bytes
            .len()
            .checked_rem(mem::size_of::<T>())
            .expect("Ref::new_slice called on a zero-sized type");
        if remainder != 0 || !util::aligned_to::<_, T>(bytes.deref()) {
            return None;
        }
        Some(Ref(bytes, PhantomData))
    }

    /// Constructs a new `Ref` of a slice type from the prefix of a byte slice.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// first `size_of::<T>() * count` bytes from `bytes` to construct a `Ref`,
    /// and returns the remaining bytes to the caller. It also ensures that
    /// `sizeof::<T>() * count` does not overflow a `usize`. If any of the
    /// length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_from_prefix` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_from_prefix(bytes: B, count: usize) -> Option<(Ref<B, [T]>, B)> {
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

    /// Constructs a new `Ref` of a slice type from the suffix of a byte slice.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// last `size_of::<T>() * count` bytes from `bytes` to construct a `Ref`,
    /// and returns the preceding bytes to the caller. It also ensures that
    /// `sizeof::<T>() * count` does not overflow a `usize`. If any of the
    /// length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_from_suffix` panics if `T` is a zero-sized type.
    #[inline]
    pub fn new_slice_from_suffix(bytes: B, count: usize) -> Option<(B, Ref<B, [T]>)> {
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

fn map_zeroed<B: ByteSliceMut, T: ?Sized>(opt: Option<Ref<B, T>>) -> Option<Ref<B, T>> {
    match opt {
        Some(mut r) => {
            r.0.fill(0);
            Some(r)
        }
        None => None,
    }
}

fn map_prefix_tuple_zeroed<B: ByteSliceMut, T: ?Sized>(
    opt: Option<(Ref<B, T>, B)>,
) -> Option<(Ref<B, T>, B)> {
    match opt {
        Some((mut r, rest)) => {
            r.0.fill(0);
            Some((r, rest))
        }
        None => None,
    }
}

fn map_suffix_tuple_zeroed<B: ByteSliceMut, T: ?Sized>(
    opt: Option<(B, Ref<B, T>)>,
) -> Option<(B, Ref<B, T>)> {
    map_prefix_tuple_zeroed(opt.map(|(a, b)| (b, a))).map(|(a, b)| (b, a))
}

impl<B, T> Ref<B, T>
where
    B: ByteSliceMut,
{
    /// Constructs a new `Ref` after zeroing the bytes.
    ///
    /// `new_zeroed` verifies that `bytes.len() == size_of::<T>()` and that
    /// `bytes` is aligned to `align_of::<T>()`, and constructs a new `Ref`. If
    /// either of these checks fail, it returns `None`.
    ///
    /// If the checks succeed, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    #[inline(always)]
    pub fn new_zeroed(bytes: B) -> Option<Ref<B, T>> {
        map_zeroed(Self::new(bytes))
    }

    /// Constructs a new `Ref` from the prefix of a byte slice, zeroing the
    /// prefix.
    ///
    /// `new_from_prefix_zeroed` verifies that `bytes.len() >= size_of::<T>()`
    /// and that `bytes` is aligned to `align_of::<T>()`. It consumes the first
    /// `size_of::<T>()` bytes from `bytes` to construct a `Ref`, and returns
    /// the remaining bytes to the caller. If either the length or alignment
    /// checks fail, it returns `None`.
    ///
    /// If the checks succeed, then the prefix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline(always)]
    pub fn new_from_prefix_zeroed(bytes: B) -> Option<(Ref<B, T>, B)> {
        map_prefix_tuple_zeroed(Self::new_from_prefix(bytes))
    }

    /// Constructs a new `Ref` from the suffix of a byte slice, zeroing the
    /// suffix.
    ///
    /// `new_from_suffix_zeroed` verifies that `bytes.len() >= size_of::<T>()`
    /// and that the last `size_of::<T>()` bytes of `bytes` are aligned to
    /// `align_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the preceding bytes to the
    /// caller. If either the length or alignment checks fail, it returns
    /// `None`.
    ///
    /// If the checks succeed, then the suffix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline(always)]
    pub fn new_from_suffix_zeroed(bytes: B) -> Option<(B, Ref<B, T>)> {
        map_suffix_tuple_zeroed(Self::new_from_suffix(bytes))
    }
}

impl<B, T> Ref<B, [T]>
where
    B: ByteSliceMut,
{
    /// Constructs a new `Ref` of a slice type after zeroing the bytes.
    ///
    /// `new_slice_zeroed` verifies that `bytes.len()` is a multiple of
    /// `size_of::<T>()` and that `bytes` is aligned to `align_of::<T>()`, and
    /// constructs a new `Ref`. If either of these checks fail, it returns
    /// `None`.
    ///
    /// If the checks succeed, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline(always)]
    pub fn new_slice_zeroed(bytes: B) -> Option<Ref<B, [T]>> {
        map_zeroed(Self::new_slice(bytes))
    }

    /// Constructs a new `Ref` of a slice type from the prefix of a byte slice,
    /// after zeroing the bytes.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// first `size_of::<T>() * count` bytes from `bytes` to construct a `Ref`,
    /// and returns the remaining bytes to the caller. It also ensures that
    /// `sizeof::<T>() * count` does not overflow a `usize`. If any of the
    /// length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// If the checks succeed, then the suffix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_from_prefix_zeroed` panics if `T` is a zero-sized type.
    #[inline(always)]
    pub fn new_slice_from_prefix_zeroed(bytes: B, count: usize) -> Option<(Ref<B, [T]>, B)> {
        map_prefix_tuple_zeroed(Self::new_slice_from_prefix(bytes, count))
    }

    /// Constructs a new `Ref` of a slice type from the prefix of a byte slice,
    /// after zeroing the bytes.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count` and that `bytes` is aligned to `align_of::<T>()`. It consumes the
    /// last `size_of::<T>() * count` bytes from `bytes` to construct a `Ref`,
    /// and returns the preceding bytes to the caller. It also ensures that
    /// `sizeof::<T>() * count` does not overflow a `usize`. If any of the
    /// length, alignment, or overflow checks fail, it returns `None`.
    ///
    /// If the checks succeed, then the consumed suffix will be initialized to
    /// zero. This can be useful when re-using buffers to ensure that sensitive
    /// data previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_from_suffix_zeroed` panics if `T` is a zero-sized type.
    #[inline(always)]
    pub fn new_slice_from_suffix_zeroed(bytes: B, count: usize) -> Option<(B, Ref<B, [T]>)> {
        map_suffix_tuple_zeroed(Self::new_slice_from_suffix(bytes, count))
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: Unaligned,
{
    /// Constructs a new `Ref` for a type with no alignment requirement.
    ///
    /// `new_unaligned` verifies that `bytes.len() == size_of::<T>()` and
    /// constructs a new `Ref`. If the check fails, it returns `None`.
    #[inline(always)]
    pub fn new_unaligned(bytes: B) -> Option<Ref<B, T>> {
        Ref::new(bytes)
    }

    /// Constructs a new `Ref` from the prefix of a byte slice for a type with
    /// no alignment requirement.
    ///
    /// `new_unaligned_from_prefix` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the first `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the remaining bytes to the
    /// caller. If the length check fails, it returns `None`.
    #[inline(always)]
    pub fn new_unaligned_from_prefix(bytes: B) -> Option<(Ref<B, T>, B)> {
        Ref::new_from_prefix(bytes)
    }

    /// Constructs a new `Ref` from the suffix of a byte slice for a type with
    /// no alignment requirement.
    ///
    /// `new_unaligned_from_suffix` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the preceding bytes to the
    /// caller. If the length check fails, it returns `None`.
    #[inline(always)]
    pub fn new_unaligned_from_suffix(bytes: B) -> Option<(B, Ref<B, T>)> {
        Ref::new_from_suffix(bytes)
    }
}

impl<B, T> Ref<B, [T]>
where
    B: ByteSlice,
    T: Unaligned,
{
    /// Constructs a new `Ref` of a slice type with no alignment requirement.
    ///
    /// `new_slice_unaligned` verifies that `bytes.len()` is a multiple of
    /// `size_of::<T>()` and constructs a new `Ref`. If the check fails, it
    /// returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline(always)]
    pub fn new_slice_unaligned(bytes: B) -> Option<Ref<B, [T]>> {
        Ref::new_slice(bytes)
    }

    /// Constructs a new `Ref` of a slice type with no alignment requirement
    /// from the prefix of a byte slice.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the first `size_of::<T>() * count` bytes from
    /// `bytes` to construct a `Ref`, and returns the remaining bytes to the
    /// caller. It also ensures that `sizeof::<T>() * count` does not overflow a
    /// `usize`. If either the length, or overflow checks fail, it returns
    /// `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_prefix` panics if `T` is a zero-sized type.
    #[inline(always)]
    pub fn new_slice_unaligned_from_prefix(bytes: B, count: usize) -> Option<(Ref<B, [T]>, B)> {
        Ref::new_slice_from_prefix(bytes, count)
    }

    /// Constructs a new `Ref` of a slice type with no alignment requirement
    /// from the suffix of a byte slice.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the last `size_of::<T>() * count` bytes from `bytes`
    /// to construct a `Ref`, and returns the remaining bytes to the caller. It
    /// also ensures that `sizeof::<T>() * count` does not overflow a `usize`.
    /// If either the length, or overflow checks fail, it returns `None`.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_suffix` panics if `T` is a zero-sized type.
    #[inline(always)]
    pub fn new_slice_unaligned_from_suffix(bytes: B, count: usize) -> Option<(B, Ref<B, [T]>)> {
        Ref::new_slice_from_suffix(bytes, count)
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSliceMut,
    T: Unaligned,
{
    /// Constructs a new `Ref` for a type with no alignment requirement, zeroing
    /// the bytes.
    ///
    /// `new_unaligned_zeroed` verifies that `bytes.len() == size_of::<T>()` and
    /// constructs a new `Ref`. If the check fails, it returns `None`.
    ///
    /// If the check succeeds, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    #[inline(always)]
    pub fn new_unaligned_zeroed(bytes: B) -> Option<Ref<B, T>> {
        map_zeroed(Self::new_unaligned(bytes))
    }

    /// Constructs a new `Ref` from the prefix of a byte slice for a type with
    /// no alignment requirement, zeroing the prefix.
    ///
    /// `new_unaligned_from_prefix_zeroed` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the first `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the remaining bytes to the
    /// caller. If the length check fails, it returns `None`.
    ///
    /// If the check succeeds, then the prefix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline(always)]
    pub fn new_unaligned_from_prefix_zeroed(bytes: B) -> Option<(Ref<B, T>, B)> {
        map_prefix_tuple_zeroed(Self::new_unaligned_from_prefix(bytes))
    }

    /// Constructs a new `Ref` from the suffix of a byte slice for a type with
    /// no alignment requirement, zeroing the suffix.
    ///
    /// `new_unaligned_from_suffix_zeroed` verifies that `bytes.len() >=
    /// size_of::<T>()`. It consumes the last `size_of::<T>()` bytes from
    /// `bytes` to construct a `Ref`, and returns the preceding bytes to the
    /// caller. If the length check fails, it returns `None`.
    ///
    /// If the check succeeds, then the suffix which is consumed will be
    /// initialized to zero. This can be useful when re-using buffers to ensure
    /// that sensitive data previously stored in the buffer is not leaked.
    #[inline(always)]
    pub fn new_unaligned_from_suffix_zeroed(bytes: B) -> Option<(B, Ref<B, T>)> {
        map_suffix_tuple_zeroed(Self::new_unaligned_from_suffix(bytes))
    }
}

impl<B, T> Ref<B, [T]>
where
    B: ByteSliceMut,
    T: Unaligned,
{
    /// Constructs a new `Ref` for a slice type with no alignment requirement,
    /// zeroing the bytes.
    ///
    /// `new_slice_unaligned_zeroed` verifies that `bytes.len()` is a multiple
    /// of `size_of::<T>()` and constructs a new `Ref`. If the check fails, it
    /// returns `None`.
    ///
    /// If the check succeeds, then `bytes` will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice` panics if `T` is a zero-sized type.
    #[inline(always)]
    pub fn new_slice_unaligned_zeroed(bytes: B) -> Option<Ref<B, [T]>> {
        map_zeroed(Self::new_slice_unaligned(bytes))
    }

    /// Constructs a new `Ref` of a slice type with no alignment requirement
    /// from the prefix of a byte slice, after zeroing the bytes.
    ///
    /// `new_slice_from_prefix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the first `size_of::<T>() * count` bytes from
    /// `bytes` to construct a `Ref`, and returns the remaining bytes to the
    /// caller. It also ensures that `sizeof::<T>() * count` does not overflow a
    /// `usize`. If either the length, or overflow checks fail, it returns
    /// `None`.
    ///
    /// If the checks succeed, then the prefix will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_prefix_zeroed` panics if `T` is a zero-sized
    /// type.
    #[inline(always)]
    pub fn new_slice_unaligned_from_prefix_zeroed(
        bytes: B,
        count: usize,
    ) -> Option<(Ref<B, [T]>, B)> {
        map_prefix_tuple_zeroed(Self::new_slice_unaligned_from_prefix(bytes, count))
    }

    /// Constructs a new `Ref` of a slice type with no alignment requirement
    /// from the suffix of a byte slice, after zeroing the bytes.
    ///
    /// `new_slice_from_suffix` verifies that `bytes.len() >= size_of::<T>() *
    /// count`. It consumes the last `size_of::<T>() * count` bytes from `bytes`
    /// to construct a `Ref`, and returns the remaining bytes to the caller. It
    /// also ensures that `sizeof::<T>() * count` does not overflow a `usize`.
    /// If either the length, or overflow checks fail, it returns `None`.
    ///
    /// If the checks succeed, then the suffix will be initialized to zero. This
    /// can be useful when re-using buffers to ensure that sensitive data
    /// previously stored in the buffer is not leaked.
    ///
    /// # Panics
    ///
    /// `new_slice_unaligned_from_suffix_zeroed` panics if `T` is a zero-sized
    /// type.
    #[inline(always)]
    pub fn new_slice_unaligned_from_suffix_zeroed(
        bytes: B,
        count: usize,
    ) -> Option<(B, Ref<B, [T]>)> {
        map_suffix_tuple_zeroed(Self::new_slice_unaligned_from_suffix(bytes, count))
    }
}

impl<'a, B, T> Ref<B, T>
where
    B: 'a + ByteSlice,
    T: FromBytes,
{
    /// Converts this `Ref` into a reference.
    ///
    /// `into_ref` consumes the `Ref`, and returns a reference to `T`.
    pub fn into_ref(self) -> &'a T {
        // SAFETY: This is sound because `B` is guaranteed to live for the
        // lifetime `'a`, meaning that a) the returned reference cannot outlive
        // the `B` from which `self` was constructed and, b) no mutable methods
        // on that `B` can be called during the lifetime of the returned
        // reference. See the documentation on `deref_helper` for what
        // invariants we are required to uphold.
        unsafe { self.deref_helper() }
    }
}

impl<'a, B, T> Ref<B, T>
where
    B: 'a + ByteSliceMut,
    T: FromBytes + AsBytes,
{
    /// Converts this `Ref` into a mutable reference.
    ///
    /// `into_mut` consumes the `Ref`, and returns a mutable reference to `T`.
    pub fn into_mut(mut self) -> &'a mut T {
        // SAFETY: This is sound because `B` is guaranteed to live for the
        // lifetime `'a`, meaning that a) the returned reference cannot outlive
        // the `B` from which `self` was constructed and, b) no other methods -
        // mutable or immutable - on that `B` can be called during the lifetime
        // of the returned reference. See the documentation on
        // `deref_mut_helper` for what invariants we are required to uphold.
        unsafe { self.deref_mut_helper() }
    }
}

impl<'a, B, T> Ref<B, [T]>
where
    B: 'a + ByteSlice,
    T: FromBytes,
{
    /// Converts this `Ref` into a slice reference.
    ///
    /// `into_slice` consumes the `Ref`, and returns a reference to `[T]`.
    pub fn into_slice(self) -> &'a [T] {
        // SAFETY: This is sound because `B` is guaranteed to live for the
        // lifetime `'a`, meaning that a) the returned reference cannot outlive
        // the `B` from which `self` was constructed and, b) no mutable methods
        // on that `B` can be called during the lifetime of the returned
        // reference. See the documentation on `deref_slice_helper` for what
        // invariants we are required to uphold.
        unsafe { self.deref_slice_helper() }
    }
}

impl<'a, B, T> Ref<B, [T]>
where
    B: 'a + ByteSliceMut,
    T: FromBytes + AsBytes,
{
    /// Converts this `Ref` into a mutable slice reference.
    ///
    /// `into_mut_slice` consumes the `Ref`, and returns a mutable reference to
    /// `[T]`.
    pub fn into_mut_slice(mut self) -> &'a mut [T] {
        // SAFETY: This is sound because `B` is guaranteed to live for the
        // lifetime `'a`, meaning that a) the returned reference cannot outlive
        // the `B` from which `self` was constructed and, b) no other methods -
        // mutable or immutable - on that `B` can be called during the lifetime
        // of the returned reference. See the documentation on
        // `deref_mut_slice_helper` for what invariants we are required to
        // uphold.
        unsafe { self.deref_mut_slice_helper() }
    }
}

impl<B, T> Ref<B, T>
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
        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            &*self.0.as_ptr().cast::<T>()
        }
    }
}

impl<B, T> Ref<B, T>
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
        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            &mut *self.0.as_mut_ptr().cast::<T>()
        }
    }
}

impl<B, T> Ref<B, [T]>
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
        // `Ref<_, [T]>` maintains the invariant that `size_of::<T>() > 0`.
        // Thus, neither the mod nor division operations here can panic.
        #[allow(clippy::arithmetic_side_effects)]
        let elems = {
            debug_assert_eq!(len % elem_size, 0);
            len / elem_size
        };
        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            slice::from_raw_parts(self.0.as_ptr().cast::<T>(), elems)
        }
    }
}

impl<B, T> Ref<B, [T]>
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
        // `Ref<_, [T]>` maintains the invariant that `size_of::<T>() > 0`.
        // Thus, neither the mod nor division operations here can panic.
        #[allow(clippy::arithmetic_side_effects)]
        let elems = {
            debug_assert_eq!(len % elem_size, 0);
            len / elem_size
        };
        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            slice::from_raw_parts_mut(self.0.as_mut_ptr().cast::<T>(), elems)
        }
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
        &self.0
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
        &mut self.0
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes,
{
    /// Reads a copy of `T`.
    #[inline]
    pub fn read(&self) -> T {
        // SAFETY: Because of the invariants on `Ref`, we know that `self.0` is
        // at least `size_of::<T>()` bytes long, and that it is at least as
        // aligned as `align_of::<T>()`. Because `T: FromBytes`, it is sound to
        // interpret these bytes as a `T`.
        unsafe { ptr::read(self.0.as_ptr().cast::<T>()) }
    }
}

impl<B, T> Ref<B, T>
where
    B: ByteSliceMut,
    T: AsBytes,
{
    /// Writes the bytes of `t` and then forgets `t`.
    #[inline]
    pub fn write(&mut self, t: T) {
        // SAFETY: Because of the invariants on `Ref`, we know that `self.0` is
        // at least `size_of::<T>()` bytes long, and that it is at least as
        // aligned as `align_of::<T>()`. Writing `t` to the buffer will allow
        // all of the bytes of `t` to be accessed as a `[u8]`, but because `T:
        // AsBytes`, we know this is sound.
        unsafe { ptr::write(self.0.as_mut_ptr().cast::<T>(), t) }
    }
}

impl<B, T> Deref for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes,
{
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: This is sound because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no mutable methods on `self`
        // can be called during the lifetime of the returned reference. See the
        // documentation on `deref_helper` for what invariants we are required
        // to uphold.
        unsafe { self.deref_helper() }
    }
}

impl<B, T> DerefMut for Ref<B, T>
where
    B: ByteSliceMut,
    T: FromBytes + AsBytes,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: This is sound because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no other methods on `self`
        // can be called during the lifetime of the returned reference. See the
        // documentation on `deref_mut_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_mut_helper() }
    }
}

impl<B, T> Deref for Ref<B, [T]>
where
    B: ByteSlice,
    T: FromBytes,
{
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] {
        // SAFETY: This is sound because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no mutable methods on `self`
        // can be called during the lifetime of the returned reference. See the
        // documentation on `deref_slice_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_slice_helper() }
    }
}

impl<B, T> DerefMut for Ref<B, [T]>
where
    B: ByteSliceMut,
    T: FromBytes + AsBytes,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        // SAFETY: This is sound because the lifetime of `self` is the same as
        // the lifetime of the return value, meaning that a) the returned
        // reference cannot outlive `self` and, b) no other methods on `self`
        // can be called during the lifetime of the returned reference. See the
        // documentation on `deref_mut_slice_helper` for what invariants we are
        // required to uphold.
        unsafe { self.deref_mut_slice_helper() }
    }
}

impl<T, B> Display for Ref<B, T>
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

impl<T, B> Display for Ref<B, [T]>
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

impl<T, B> Debug for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + Debug,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &T = self;
        fmt.debug_tuple("Ref").field(&inner).finish()
    }
}

impl<T, B> Debug for Ref<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + Debug,
{
    #[inline]
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let inner: &[T] = self;
        fmt.debug_tuple("Ref").field(&inner).finish()
    }
}

impl<T, B> Eq for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + Eq,
{
}

impl<T, B> Eq for Ref<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + Eq,
{
}

impl<T, B> PartialEq for Ref<B, T>
where
    B: ByteSlice,
    T: FromBytes + PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.deref().eq(other.deref())
    }
}

impl<T, B> PartialEq for Ref<B, [T]>
where
    B: ByteSlice,
    T: FromBytes + PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.deref().eq(other.deref())
    }
}

impl<T, B> Ord for Ref<B, T>
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

impl<T, B> Ord for Ref<B, [T]>
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

impl<T, B> PartialOrd for Ref<B, T>
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

impl<T, B> PartialOrd for Ref<B, [T]>
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
    pub trait ByteSliceSealed {}
    pub trait KnownLayoutSealed {}
}

// ByteSlice and ByteSliceMut abstract over [u8] references (&[u8], &mut [u8],
// Ref<[u8]>, RefMut<[u8]>, etc). We rely on various behaviors of these
// references such as that a given reference will never changes its length
// between calls to deref() or deref_mut(), and that split_at() works as
// expected. If ByteSlice or ByteSliceMut were not sealed, consumers could
// implement them in a way that violated these behaviors, and would break our
// unsafe code. Thus, we seal them and implement it only for known-good
// reference types. For the same reason, they're unsafe traits.

#[allow(clippy::missing_safety_doc)] // TODO(fxbug.dev/99068)
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
/// [`Vec<u8>`]: alloc::vec::Vec
/// [`split_at`]: crate::ByteSlice::split_at
pub unsafe trait ByteSlice:
    Deref<Target = [u8]> + Sized + self::sealed::ByteSliceSealed
{
    /// Gets a raw pointer to the first byte in the slice.
    #[inline]
    fn as_ptr(&self) -> *const u8 {
        <[u8]>::as_ptr(self)
    }

    /// Splits the slice at the midpoint.
    ///
    /// `x.split_at(mid)` returns `x[..mid]` and `x[mid..]`.
    ///
    /// # Panics
    ///
    /// `x.split_at(mid)` panics if `mid > x.len()`.
    fn split_at(self, mid: usize) -> (Self, Self);
}

#[allow(clippy::missing_safety_doc)] // TODO(fxbug.dev/99068)
/// A mutable reference to a byte slice.
///
/// `ByteSliceMut` abstracts over various ways of storing a mutable reference to
/// a byte slice, and is implemented for various special reference types such as
/// `RefMut<[u8]>`.
pub unsafe trait ByteSliceMut: ByteSlice + DerefMut {
    /// Gets a mutable raw pointer to the first byte in the slice.
    #[inline]
    fn as_mut_ptr(&mut self) -> *mut u8 {
        <[u8]>::as_mut_ptr(self)
    }
}

impl<'a> sealed::ByteSliceSealed for &'a [u8] {}
// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for &'a [u8] {
    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        <[u8]>::split_at(self, mid)
    }
}

impl<'a> sealed::ByteSliceSealed for &'a mut [u8] {}
// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for &'a mut [u8] {
    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        <[u8]>::split_at_mut(self, mid)
    }
}

impl<'a> sealed::ByteSliceSealed for cell::Ref<'a, [u8]> {}
// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for cell::Ref<'a, [u8]> {
    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        cell::Ref::map_split(self, |slice| <[u8]>::split_at(slice, mid))
    }
}

impl<'a> sealed::ByteSliceSealed for RefMut<'a, [u8]> {}
// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSlice for RefMut<'a, [u8]> {
    #[inline]
    fn split_at(self, mid: usize) -> (Self, Self) {
        RefMut::map_split(self, |slice| <[u8]>::split_at_mut(slice, mid))
    }
}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSliceMut for &'a mut [u8] {}

// TODO(#61): Add a "SAFETY" comment and remove this `allow`.
#[allow(clippy::undocumented_unsafe_blocks)]
unsafe impl<'a> ByteSliceMut for RefMut<'a, [u8]> {}

// A polyfill for `<*const _>::cast_mut` that we can use before our MSRV is
// 1.65, when that method was stabilized.

// TODO(#67): Once our MSRV is 1.65, remove this.
trait RawPtrExt {
    type Mut;
    fn cast_mut(self) -> Self::Mut;
}

impl<T: ?Sized> RawPtrExt for *const T {
    type Mut = *mut T;
    #[allow(clippy::as_conversions)]
    #[inline(always)]
    fn cast_mut(self) -> *mut T {
        self as *mut T
    }
}

// A polyfill for `<*mut _>::cast_const` that we can use before our MSRV is
// 1.65, when that method was stabilized.
//
// TODO(#67): Once our MSRV is 1.65, remove this.
trait RawMutPtrExt {
    type Const;
    fn cast_const(self) -> Self::Const;
}

impl<T: ?Sized> RawMutPtrExt for *mut T {
    type Const = *const T;
    #[allow(clippy::as_conversions)]
    #[inline(always)]
    fn cast_const(self) -> *const T {
        self as *const T
    }
}

// A polyfill for `NonNull::slice_from_raw_parts` that we can use before our
// MSRV is 1.70, when that function was stabilized.
//
// TODO(#67): Once our MSRV is 1.70, remove this.
trait NonNullExt {
    type SliceOfSelf;

    fn slice_from_raw_parts(data: Self, len: usize) -> Self::SliceOfSelf;
}

impl<T> NonNullExt for NonNull<T> {
    type SliceOfSelf = NonNull<[T]>;

    #[inline(always)]
    fn slice_from_raw_parts(data: Self, len: usize) -> NonNull<[T]> {
        let ptr = ptr::slice_from_raw_parts_mut(data.as_ptr(), len);
        // SAFETY: `ptr` is converted from `data`, which is non-null.
        unsafe { NonNull::new_unchecked(ptr) }
    }
}

#[cfg(feature = "alloc")]
mod alloc_support {
    use alloc::vec::Vec;

    use super::*;

    /// Extends a `Vec<T>` by pushing `additional` new items onto the end of the
    /// vector. The new items are initialized with zeroes.
    ///
    /// # Panics
    ///
    /// Panics if `Vec::reserve(additional)` fails to reserve enough memory.
    pub fn extend_vec_zeroed<T: FromZeroes>(v: &mut Vec<T>, additional: usize) {
        insert_vec_zeroed(v, v.len(), additional);
    }

    /// Inserts `additional` new items into `Vec<T>` at `position`.
    /// The new items are initialized with zeroes.
    ///
    /// # Panics
    ///
    /// * Panics if `position > v.len()`.
    /// * Panics if `Vec::reserve(additional)` fails to reserve enough memory.
    pub fn insert_vec_zeroed<T: FromZeroes>(v: &mut Vec<T>, position: usize, additional: usize) {
        assert!(position <= v.len());
        v.reserve(additional);
        // SAFETY: The `reserve` call guarantees that these cannot overflow:
        // * `ptr.add(position)`
        // * `position + additional`
        // * `v.len() + additional`
        //
        // `v.len() - position` cannot overflow because we asserted that
        // `position <= v.len()`.
        unsafe {
            // This is a potentially overlapping copy.
            let ptr = v.as_mut_ptr();
            #[allow(clippy::arithmetic_side_effects)]
            ptr.add(position).copy_to(ptr.add(position + additional), v.len() - position);
            ptr.add(position).write_bytes(0, additional);
            #[allow(clippy::arithmetic_side_effects)]
            v.set_len(v.len() + additional);
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_extend_vec_zeroed() {
            // Test extending when there is an existing allocation.
            let mut v = vec![100u64, 200, 300];
            extend_vec_zeroed(&mut v, 3);
            assert_eq!(v.len(), 6);
            assert_eq!(&*v, &[100, 200, 300, 0, 0, 0]);
            drop(v);

            // Test extending when there is no existing allocation.
            let mut v: Vec<u64> = Vec::new();
            extend_vec_zeroed(&mut v, 3);
            assert_eq!(v.len(), 3);
            assert_eq!(&*v, &[0, 0, 0]);
            drop(v);
        }

        #[test]
        fn test_extend_vec_zeroed_zst() {
            // Test extending when there is an existing (fake) allocation.
            let mut v = vec![(), (), ()];
            extend_vec_zeroed(&mut v, 3);
            assert_eq!(v.len(), 6);
            assert_eq!(&*v, &[(), (), (), (), (), ()]);
            drop(v);

            // Test extending when there is no existing (fake) allocation.
            let mut v: Vec<()> = Vec::new();
            extend_vec_zeroed(&mut v, 3);
            assert_eq!(&*v, &[(), (), ()]);
            drop(v);
        }

        #[test]
        fn test_insert_vec_zeroed() {
            // Insert at start (no existing allocation).
            let mut v: Vec<u64> = Vec::new();
            insert_vec_zeroed(&mut v, 0, 2);
            assert_eq!(v.len(), 2);
            assert_eq!(&*v, &[0, 0]);
            drop(v);

            // Insert at start.
            let mut v = vec![100u64, 200, 300];
            insert_vec_zeroed(&mut v, 0, 2);
            assert_eq!(v.len(), 5);
            assert_eq!(&*v, &[0, 0, 100, 200, 300]);
            drop(v);

            // Insert at middle.
            let mut v = vec![100u64, 200, 300];
            insert_vec_zeroed(&mut v, 1, 1);
            assert_eq!(v.len(), 4);
            assert_eq!(&*v, &[100, 0, 200, 300]);
            drop(v);

            // Insert at end.
            let mut v = vec![100u64, 200, 300];
            insert_vec_zeroed(&mut v, 3, 1);
            assert_eq!(v.len(), 4);
            assert_eq!(&*v, &[100, 200, 300, 0]);
            drop(v);
        }

        #[test]
        fn test_insert_vec_zeroed_zst() {
            // Insert at start (no existing fake allocation).
            let mut v: Vec<()> = Vec::new();
            insert_vec_zeroed(&mut v, 0, 2);
            assert_eq!(v.len(), 2);
            assert_eq!(&*v, &[(), ()]);
            drop(v);

            // Insert at start.
            let mut v = vec![(), (), ()];
            insert_vec_zeroed(&mut v, 0, 2);
            assert_eq!(v.len(), 5);
            assert_eq!(&*v, &[(), (), (), (), ()]);
            drop(v);

            // Insert at middle.
            let mut v = vec![(), (), ()];
            insert_vec_zeroed(&mut v, 1, 1);
            assert_eq!(v.len(), 4);
            assert_eq!(&*v, &[(), (), (), ()]);
            drop(v);

            // Insert at end.
            let mut v = vec![(), (), ()];
            insert_vec_zeroed(&mut v, 3, 1);
            assert_eq!(v.len(), 4);
            assert_eq!(&*v, &[(), (), (), ()]);
            drop(v);
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
            // This test exists in order to exercise unsafe code, especially
            // when running under Miri.
            #[allow(clippy::unit_cmp)]
            {
                assert_eq!(*<()>::new_box_zeroed(), ());
            }
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
            // This test exists in order to exercise unsafe code, especially
            // when running under Miri.
            #[allow(clippy::unit_cmp)]
            {
                assert_eq!(s[1], ());
            }
            s[2] = ();
        }

        #[test]
        fn test_new_box_slice_zeroed_zst_empty() {
            let s: Box<[()]> = <()>::new_box_slice_zeroed(0);
            assert_eq!(s.len(), 0);
        }

        #[test]
        #[should_panic(expected = "mem::size_of::<Self>() * len overflows `usize`")]
        fn test_new_box_slice_zeroed_panics_mul_overflow() {
            let _ = u16::new_box_slice_zeroed(usize::MAX);
        }

        #[test]
        #[should_panic(expected = "assertion failed: size <= max_alloc")]
        fn test_new_box_slice_zeroed_panics_isize_overflow() {
            let max = usize::try_from(isize::MAX).unwrap();
            let _ = u16::new_box_slice_zeroed((max / mem::size_of::<u16>()) + 1);
        }
    }
}

#[cfg(feature = "alloc")]
#[doc(inline)]
pub use alloc_support::*;

#[cfg(test)]
mod tests {
    #![allow(clippy::unreadable_literal)]

    use core::ops::Deref;

    use static_assertions::assert_impl_all;

    use super::*;
    use crate::util::testutil::*;

    // An unsized type.
    //
    // This is used to test the custom derives of our traits. The `[u8]` type
    // gets a hand-rolled impl, so it doesn't exercise our custom derives.
    #[derive(Debug, Eq, PartialEq, FromZeroes, FromBytes, AsBytes, Unaligned)]
    #[repr(transparent)]
    struct Unsized([u8]);

    impl Unsized {
        fn from_mut_slice(slc: &mut [u8]) -> &mut Unsized {
            // SAFETY: This *probably* sound - since the layouts of `[u8]` and
            // `Unsized` are the same, so are the layouts of `&mut [u8]` and
            // `&mut Unsized`. [1] Even if it turns out that this isn't actually
            // guaranteed by the language spec, we can just change this since
            // it's in test code.
            //
            // [1] https://github.com/rust-lang/unsafe-code-guidelines/issues/375
            unsafe { mem::transmute(slc) }
        }
    }

    #[test]
    fn test_object_safety() {
        fn _takes_from_zeroes(_: &dyn FromZeroes) {}
        fn _takes_from_bytes(_: &dyn FromBytes) {}
        fn _takes_unaligned(_: &dyn Unaligned) {}
    }

    #[test]
    fn test_from_zeroes_only() {
        // Test types that implement `FromZeroes` but not `FromBytes`.

        assert!(!bool::new_zeroed());
        assert_eq!(char::new_zeroed(), '\0');

        #[cfg(feature = "alloc")]
        {
            assert_eq!(bool::new_box_zeroed(), Box::new(false));
            assert_eq!(char::new_box_zeroed(), Box::new('\0'));

            assert_eq!(bool::new_box_slice_zeroed(3).as_ref(), [false, false, false]);
            assert_eq!(char::new_box_slice_zeroed(3).as_ref(), ['\0', '\0', '\0']);

            assert_eq!(bool::new_vec_zeroed(3).as_ref(), [false, false, false]);
            assert_eq!(char::new_vec_zeroed(3).as_ref(), ['\0', '\0', '\0']);
        }

        let mut string = "hello".to_string();
        let s: &mut str = string.as_mut();
        assert_eq!(s, "hello");
        s.zero();
        assert_eq!(s, "\0\0\0\0\0");
    }

    #[test]
    fn test_maybe_valid() {
        let m = MaybeValid::<usize>::default();
        // SAFETY: all bit patterns are valid `usize`s, and `m` is initialized.
        let u = unsafe { m.assume_valid() };
        // This ensures that Miri can see whether `u` (and thus `m`) has been
        // properly initialized.
        assert_eq!(u, u);

        fn bytes_to_maybe_valid(bytes: &mut [u8]) -> &mut MaybeValid<[u8]> {
            // SAFETY: `MaybeValid<[u8]>` has the same layout as `[u8]`, and
            // `bytes` is initialized.
            unsafe {
                #[allow(clippy::as_conversions)]
                let m = &mut *(bytes as *mut [u8] as *mut MaybeValid<[u8]>);
                m
            }
        }

        let mut bytes = [0u8, 1, 2];
        let m = bytes_to_maybe_valid(&mut bytes[..]);

        // SAFETY: `m` was created from a valid `[u8]`.
        let r = unsafe { m.assume_valid_ref() };
        assert_eq!(r.len(), 3);
        assert_eq!(r, [0, 1, 2]);

        // SAFETY: `m` was created from a valid `[u8]`.
        let r = unsafe { m.assume_valid_mut() };
        assert_eq!(r.len(), 3);
        assert_eq!(r, [0, 1, 2]);

        r[0] = 1;
        assert_eq!(bytes, [1, 1, 2]);

        let mut bytes = [0u8, 1, 2];
        let m = bytes_to_maybe_valid(&mut bytes[..]);
        let slc = m.as_slice_of_maybe_valids();
        assert_eq!(slc.len(), 3);
        for i in 0u8..3 {
            // SAFETY: `m` was created from a valid `[u8]`.
            let u = unsafe { slc[usize::from(i)].assume_valid_ref() };
            assert_eq!(u, &i);
        }
    }

    #[test]
    fn test_maybe_valid_as_slice() {
        let mut m = MaybeValid::<[u8; 3]>::default();
        // SAFETY: all bit patterns are valid `[u8; 3]`s, and `m` is
        // initialized.
        unsafe { *m.assume_valid_mut() = [0, 1, 2] };

        let slc = m.as_slice().as_slice_of_maybe_valids();
        assert_eq!(slc.len(), 3);

        for i in 0u8..3 {
            // SAFETY: `m` was initialized as a valid `[u8; 3]`.
            let u = unsafe { slc[usize::from(i)].assume_valid_ref() };
            assert_eq!(u, &i);
        }
    }

    #[test]
    fn test_maybe_valid_from_ref() {
        use core::cell::Cell;

        let u = 1usize;
        let m = MaybeValid::from_ref(&u);
        // SAFETY: `m` was constructed from a valid `&usize`.
        assert_eq!(unsafe { m.assume_valid_ref() }, &1usize);

        // Test that interior mutability doesn't affect correctness or
        // soundness.

        let c = Cell::new(1usize);
        let m = MaybeValid::from_ref(&c);
        // SAFETY: `m` was constructed from a valid `&usize`.
        assert_eq!(unsafe { m.assume_valid_ref() }, &Cell::new(1));

        c.set(2);
        // SAFETY: `m` was constructed from a valid `&usize`.
        assert_eq!(unsafe { m.assume_valid_ref() }, &Cell::new(2));
    }

    #[test]
    fn test_read_write() {
        const VAL: u64 = 0x12345678;
        #[cfg(target_endian = "big")]
        const VAL_BYTES: [u8; 8] = VAL.to_be_bytes();
        #[cfg(target_endian = "little")]
        const VAL_BYTES: [u8; 8] = VAL.to_le_bytes();

        // Test `FromBytes::{read_from, read_from_prefix, read_from_suffix}`.

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

        // Test `AsBytes::{write_to, write_to_prefix, write_to_suffix}`.

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

        // Test that `transmute!` is legal in a const context.
        const ARRAY_OF_U8S: [u8; 8] = [0u8, 1, 2, 3, 4, 5, 6, 7];
        const ARRAY_OF_ARRAYS: [[u8; 2]; 4] = [[0, 1], [2, 3], [4, 5], [6, 7]];
        const X: [[u8; 2]; 4] = transmute!(ARRAY_OF_U8S);
        assert_eq!(X, ARRAY_OF_ARRAYS);
    }

    #[test]
    fn test_address() {
        // Test that the `Deref` and `DerefMut` implementations return a
        // reference which points to the right region of memory.

        let buf = [0];
        let r = Ref::<_, u8>::new(&buf[..]).unwrap();
        let buf_ptr = buf.as_ptr();
        let deref_ptr: *const u8 = r.deref();
        assert_eq!(buf_ptr, deref_ptr);

        let buf = [0];
        let r = Ref::<_, [u8]>::new_slice(&buf[..]).unwrap();
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
        // new_slice. Test that xxx_zeroed behaves the same, and zeroes the
        // memory.

        // A buffer with an alignment of 8.
        let mut buf = Align::<[u8; 8], AU64>::default();
        // `buf.t` should be aligned to 8, so this should always succeed.
        test_new_helper(Ref::<_, AU64>::new(&mut buf.t[..]).unwrap());
        buf.t = [0xFFu8; 8];
        test_new_helper(Ref::<_, AU64>::new_zeroed(&mut buf.t[..]).unwrap());
        {
            // In a block so that `r` and `suffix` don't live too long.
            buf.set_default();
            let (r, suffix) = Ref::<_, AU64>::new_from_prefix(&mut buf.t[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper(r);
        }
        {
            buf.t = [0xFFu8; 8];
            let (r, suffix) = Ref::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper(r);
        }
        {
            buf.set_default();
            let (prefix, r) = Ref::<_, AU64>::new_from_suffix(&mut buf.t[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper(r);
        }
        {
            buf.t = [0xFFu8; 8];
            let (prefix, r) = Ref::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper(r);
        }

        // A buffer with alignment 8 and length 16.
        let mut buf = Align::<[u8; 16], AU64>::default();
        // `buf.t` should be aligned to 8 and have a length which is a multiple
        // of `size_of::<AU64>()`, so this should always succeed.
        test_new_helper_slice(Ref::<_, [AU64]>::new_slice(&mut buf.t[..]).unwrap(), 2);
        buf.t = [0xFFu8; 16];
        test_new_helper_slice(Ref::<_, [AU64]>::new_slice_zeroed(&mut buf.t[..]).unwrap(), 2);

        {
            buf.set_default();
            let (r, suffix) = Ref::<_, [AU64]>::new_slice_from_prefix(&mut buf.t[..], 1).unwrap();
            assert_eq!(suffix, [0; 8]);
            test_new_helper_slice(r, 1);
        }
        {
            buf.t = [0xFFu8; 16];
            let (r, suffix) =
                Ref::<_, [AU64]>::new_slice_from_prefix_zeroed(&mut buf.t[..], 1).unwrap();
            assert_eq!(suffix, [0xFF; 8]);
            test_new_helper_slice(r, 1);
        }
        {
            buf.set_default();
            let (prefix, r) = Ref::<_, [AU64]>::new_slice_from_suffix(&mut buf.t[..], 1).unwrap();
            assert_eq!(prefix, [0; 8]);
            test_new_helper_slice(r, 1);
        }
        {
            buf.t = [0xFFu8; 16];
            let (prefix, r) =
                Ref::<_, [AU64]>::new_slice_from_suffix_zeroed(&mut buf.t[..], 1).unwrap();
            assert_eq!(prefix, [0xFF; 8]);
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
        // for `new_slice`. Test that `xxx_zeroed` behaves the same, and zeroes
        // the memory.

        let mut buf = [0u8; 8];
        test_new_helper_unaligned(Ref::<_, [u8; 8]>::new_unaligned(&mut buf[..]).unwrap());
        buf = [0xFFu8; 8];
        test_new_helper_unaligned(Ref::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf[..]).unwrap());
        {
            // In a block so that `r` and `suffix` don't live too long.
            buf = [0u8; 8];
            let (r, suffix) = Ref::<_, [u8; 8]>::new_unaligned_from_prefix(&mut buf[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper_unaligned(r);
        }
        {
            buf = [0xFFu8; 8];
            let (r, suffix) =
                Ref::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf[..]).unwrap();
            assert!(suffix.is_empty());
            test_new_helper_unaligned(r);
        }
        {
            buf = [0u8; 8];
            let (prefix, r) = Ref::<_, [u8; 8]>::new_unaligned_from_suffix(&mut buf[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper_unaligned(r);
        }
        {
            buf = [0xFFu8; 8];
            let (prefix, r) =
                Ref::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf[..]).unwrap();
            assert!(prefix.is_empty());
            test_new_helper_unaligned(r);
        }

        let mut buf = [0u8; 16];
        // `buf.t` should be aligned to 8 and have a length which is a multiple
        // of `size_of::AU64>()`, so this should always succeed.
        test_new_helper_slice_unaligned(
            Ref::<_, [u8]>::new_slice_unaligned(&mut buf[..]).unwrap(),
            16,
        );
        buf = [0xFFu8; 16];
        test_new_helper_slice_unaligned(
            Ref::<_, [u8]>::new_slice_unaligned_zeroed(&mut buf[..]).unwrap(),
            16,
        );

        {
            buf = [0u8; 16];
            let (r, suffix) =
                Ref::<_, [u8]>::new_slice_unaligned_from_prefix(&mut buf[..], 8).unwrap();
            assert_eq!(suffix, [0; 8]);
            test_new_helper_slice_unaligned(r, 8);
        }
        {
            buf = [0xFFu8; 16];
            let (r, suffix) =
                Ref::<_, [u8]>::new_slice_unaligned_from_prefix_zeroed(&mut buf[..], 8).unwrap();
            assert_eq!(suffix, [0xFF; 8]);
            test_new_helper_slice_unaligned(r, 8);
        }
        {
            buf = [0u8; 16];
            let (prefix, r) =
                Ref::<_, [u8]>::new_slice_unaligned_from_suffix(&mut buf[..], 8).unwrap();
            assert_eq!(prefix, [0; 8]);
            test_new_helper_slice_unaligned(r, 8);
        }
        {
            buf = [0xFFu8; 16];
            let (prefix, r) =
                Ref::<_, [u8]>::new_slice_unaligned_from_suffix_zeroed(&mut buf[..], 8).unwrap();
            assert_eq!(prefix, [0xFF; 8]);
            test_new_helper_slice_unaligned(r, 8);
        }
    }

    #[test]
    fn test_new_oversized() {
        // Test that a properly-aligned, overly-sized buffer works for
        // `new_from_prefix` and `new_from_suffix`, and that they return the
        // remainder and prefix of the slice respectively. Test that
        // `xxx_zeroed` behaves the same, and zeroes the memory.

        let mut buf = Align::<[u8; 16], AU64>::default();
        {
            // In a block so that `r` and `suffix` don't live too long. `buf.t`
            // should be aligned to 8, so this should always succeed.
            let (r, suffix) = Ref::<_, AU64>::new_from_prefix(&mut buf.t[..]).unwrap();
            assert_eq!(suffix.len(), 8);
            test_new_helper(r);
        }
        {
            buf.t = [0xFFu8; 16];
            // `buf.t` should be aligned to 8, so this should always succeed.
            let (r, suffix) = Ref::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[..]).unwrap();
            // Assert that the suffix wasn't zeroed.
            assert_eq!(suffix, &[0xFFu8; 8]);
            test_new_helper(r);
        }
        {
            buf.set_default();
            // `buf.t` should be aligned to 8, so this should always succeed.
            let (prefix, r) = Ref::<_, AU64>::new_from_suffix(&mut buf.t[..]).unwrap();
            assert_eq!(prefix.len(), 8);
            test_new_helper(r);
        }
        {
            buf.t = [0xFFu8; 16];
            // `buf.t` should be aligned to 8, so this should always succeed.
            let (prefix, r) = Ref::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).unwrap();
            // Assert that the prefix wasn't zeroed.
            assert_eq!(prefix, &[0xFFu8; 8]);
            test_new_helper(r);
        }
    }

    #[test]
    fn test_new_unaligned_oversized() {
        // Test than an unaligned, overly-sized buffer works for
        // `new_unaligned_from_prefix` and `new_unaligned_from_suffix`, and that
        // they return the remainder and prefix of the slice respectively. Test
        // that `xxx_zeroed` behaves the same, and zeroes the memory.

        let mut buf = [0u8; 16];
        {
            // In a block so that `r` and `suffix` don't live too long.
            let (r, suffix) = Ref::<_, [u8; 8]>::new_unaligned_from_prefix(&mut buf[..]).unwrap();
            assert_eq!(suffix.len(), 8);
            test_new_helper_unaligned(r);
        }
        {
            buf = [0xFFu8; 16];
            let (r, suffix) =
                Ref::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf[..]).unwrap();
            // Assert that the suffix wasn't zeroed.
            assert_eq!(suffix, &[0xFF; 8]);
            test_new_helper_unaligned(r);
        }
        {
            buf = [0u8; 16];
            let (prefix, r) = Ref::<_, [u8; 8]>::new_unaligned_from_suffix(&mut buf[..]).unwrap();
            assert_eq!(prefix.len(), 8);
            test_new_helper_unaligned(r);
        }
        {
            buf = [0xFFu8; 16];
            let (prefix, r) =
                Ref::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf[..]).unwrap();
            // Assert that the prefix wasn't zeroed.
            assert_eq!(prefix, &[0xFF; 8]);
            test_new_helper_unaligned(r);
        }
    }

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn test_new_error() {
        // Fail because the buffer is too large.

        // A buffer with an alignment of 8.
        let mut buf = Align::<[u8; 16], AU64>::default();
        // `buf.t` should be aligned to 8, so only the length check should fail.
        assert!(Ref::<_, AU64>::new(&buf.t[..]).is_none());
        assert!(Ref::<_, AU64>::new_zeroed(&mut buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned(&buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf.t[..]).is_none());

        // Fail because the buffer is too small.

        // A buffer with an alignment of 8.
        let mut buf = Align::<[u8; 4], AU64>::default();
        // `buf.t` should be aligned to 8, so only the length check should fail.
        assert!(Ref::<_, AU64>::new(&buf.t[..]).is_none());
        assert!(Ref::<_, AU64>::new_zeroed(&mut buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned(&buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf.t[..]).is_none());
        assert!(Ref::<_, AU64>::new_from_prefix(&buf.t[..]).is_none());
        assert!(Ref::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[..]).is_none());
        assert!(Ref::<_, AU64>::new_from_suffix(&buf.t[..]).is_none());
        assert!(Ref::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned_from_prefix(&buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned_from_suffix(&buf.t[..]).is_none());
        assert!(Ref::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf.t[..]).is_none());

        // Fail because the length is not a multiple of the element size.

        let mut buf = Align::<[u8; 12], AU64>::default();
        // `buf.t` has length 12, but element size is 8.
        assert!(Ref::<_, [AU64]>::new_slice(&buf.t[..]).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_zeroed(&mut buf.t[..]).is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned(&buf.t[..]).is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_zeroed(&mut buf.t[..]).is_none());

        // Fail because the buffer is too short.
        let mut buf = Align::<[u8; 12], AU64>::default();
        // `buf.t` has length 12, but the element size is 8 (and we're expecting
        // two of them).
        assert!(Ref::<_, [AU64]>::new_slice_from_prefix(&buf.t[..], 2).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_prefix_zeroed(&mut buf.t[..], 2).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_suffix(&buf.t[..], 2).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_suffix_zeroed(&mut buf.t[..], 2).is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix(&buf.t[..], 2).is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix_zeroed(&mut buf.t[..], 2)
            .is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix(&buf.t[..], 2).is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix_zeroed(&mut buf.t[..], 2)
            .is_none());

        // Fail because the alignment is insufficient.

        // A buffer with an alignment of 8. An odd buffer size is chosen so that
        // the last byte of the buffer has odd alignment.
        let mut buf = Align::<[u8; 13], AU64>::default();
        // Slicing from 1, we get a buffer with size 12 (so the length check
        // should succeed) but an alignment of only 1, which is insufficient.
        assert!(Ref::<_, AU64>::new(&buf.t[1..]).is_none());
        assert!(Ref::<_, AU64>::new_zeroed(&mut buf.t[1..]).is_none());
        assert!(Ref::<_, AU64>::new_from_prefix(&buf.t[1..]).is_none());
        assert!(Ref::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[1..]).is_none());
        assert!(Ref::<_, [AU64]>::new_slice(&buf.t[1..]).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_zeroed(&mut buf.t[1..]).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_prefix(&buf.t[1..], 1).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_prefix_zeroed(&mut buf.t[1..], 1).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_suffix(&buf.t[1..], 1).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_suffix_zeroed(&mut buf.t[1..], 1).is_none());
        // Slicing is unnecessary here because `new_from_suffix[_zeroed]` use
        // the suffix of the slice, which has odd alignment.
        assert!(Ref::<_, AU64>::new_from_suffix(&buf.t[..]).is_none());
        assert!(Ref::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).is_none());

        // Fail due to arithmetic overflow.

        let mut buf = Align::<[u8; 16], AU64>::default();
        let unreasonable_len = usize::MAX / mem::size_of::<AU64>() + 1;
        assert!(Ref::<_, [AU64]>::new_slice_from_prefix(&buf.t[..], unreasonable_len).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_prefix_zeroed(&mut buf.t[..], unreasonable_len)
            .is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_suffix(&buf.t[..], unreasonable_len).is_none());
        assert!(Ref::<_, [AU64]>::new_slice_from_suffix_zeroed(&mut buf.t[..], unreasonable_len)
            .is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix(&buf.t[..], unreasonable_len)
            .is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix_zeroed(
            &mut buf.t[..],
            unreasonable_len
        )
        .is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix(&buf.t[..], unreasonable_len)
            .is_none());
        assert!(Ref::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix_zeroed(
            &mut buf.t[..],
            unreasonable_len
        )
        .is_none());
    }

    // Tests for ensuring that, if a ZST is passed into a slice-like function,
    // we always panic. Since these tests need to be separate per-function, and
    // they tend to take up a lot of space, we generate them using a macro in a
    // submodule instead. The submodule ensures that we can just re-use the name
    // of the function under test for the name of the test itself.
    mod test_zst_panics {
        macro_rules! zst_test {
            ($name:ident($($tt:tt)*), $constructor_in_panic_msg:tt) => {
                #[test]
                #[should_panic = concat!("Ref::", $constructor_in_panic_msg, " called on a zero-sized type")]
                fn $name() {
                    let mut buffer = [0u8];
                    let r = $crate::Ref::<_, [()]>::$name(&mut buffer[..], $($tt)*);
                    unreachable!("should have panicked, got {:?}", r);
                }
            }
        }
        zst_test!(new_slice(), "new_slice");
        zst_test!(new_slice_zeroed(), "new_slice");
        zst_test!(new_slice_from_prefix(1), "new_slice");
        zst_test!(new_slice_from_prefix_zeroed(1), "new_slice");
        zst_test!(new_slice_from_suffix(1), "new_slice");
        zst_test!(new_slice_from_suffix_zeroed(1), "new_slice");
        zst_test!(new_slice_unaligned(), "new_slice_unaligned");
        zst_test!(new_slice_unaligned_zeroed(), "new_slice_unaligned");
        zst_test!(new_slice_unaligned_from_prefix(1), "new_slice_unaligned");
        zst_test!(new_slice_unaligned_from_prefix_zeroed(1), "new_slice_unaligned");
        zst_test!(new_slice_unaligned_from_suffix(1), "new_slice_unaligned");
        zst_test!(new_slice_unaligned_from_suffix_zeroed(1), "new_slice_unaligned");
    }

    #[test]
    fn test_as_bytes_methods() {
        /// Run a series of tests by calling `AsBytes` methods on `t`.
        ///
        /// `bytes` is the expected byte sequence returned from `t.as_bytes()`
        /// before `t` has been modified. `post_mutation` is the expected
        /// sequence returned from `t.as_bytes()` after `t.as_bytes_mut()[0]`
        /// has had its bits flipped (by applying `^= 0xFF`).
        ///
        /// `N` is the size of `t` in bytes.
        fn test<T: FromBytes + AsBytes + Debug + Eq + ?Sized, const N: usize>(
            t: &mut T,
            bytes: &[u8],
            post_mutation: &T,
        ) {
            // Test that we can access the underlying bytes, and that we get the
            // right bytes and the right number of bytes.
            assert_eq!(t.as_bytes(), bytes);

            // Test that changes to the underlying byte slices are reflected in
            // the original object.
            t.as_bytes_mut()[0] ^= 0xFF;
            assert_eq!(t, post_mutation);
            t.as_bytes_mut()[0] ^= 0xFF;

            // `write_to` rejects slices that are too small or too large.
            assert_eq!(t.write_to(&mut vec![0; N - 1][..]), None);
            assert_eq!(t.write_to(&mut vec![0; N + 1][..]), None);

            // `write_to` works as expected.
            let mut bytes = [0; N];
            assert_eq!(t.write_to(&mut bytes[..]), Some(()));
            assert_eq!(bytes, t.as_bytes());

            // `write_to_prefix` rejects slices that are too small.
            assert_eq!(t.write_to_prefix(&mut vec![0; N - 1][..]), None);

            // `write_to_prefix` works with exact-sized slices.
            let mut bytes = [0; N];
            assert_eq!(t.write_to_prefix(&mut bytes[..]), Some(()));
            assert_eq!(bytes, t.as_bytes());

            // `write_to_prefix` works with too-large slices, and any bytes past
            // the prefix aren't modified.
            let mut too_many_bytes = vec![0; N + 1];
            too_many_bytes[N] = 123;
            assert_eq!(t.write_to_prefix(&mut too_many_bytes[..]), Some(()));
            assert_eq!(&too_many_bytes[..N], t.as_bytes());
            assert_eq!(too_many_bytes[N], 123);

            // `write_to_suffix` rejects slices that are too small.
            assert_eq!(t.write_to_suffix(&mut vec![0; N - 1][..]), None);

            // `write_to_suffix` works with exact-sized slices.
            let mut bytes = [0; N];
            assert_eq!(t.write_to_suffix(&mut bytes[..]), Some(()));
            assert_eq!(bytes, t.as_bytes());

            // `write_to_suffix` works with too-large slices, and any bytes
            // before the suffix aren't modified.
            let mut too_many_bytes = vec![0; N + 1];
            too_many_bytes[0] = 123;
            assert_eq!(t.write_to_suffix(&mut too_many_bytes[..]), Some(()));
            assert_eq!(&too_many_bytes[1..], t.as_bytes());
            assert_eq!(too_many_bytes[0], 123);
        }

        #[derive(Debug, Eq, PartialEq, FromZeroes, FromBytes, AsBytes)]
        #[repr(C)]
        struct Foo {
            a: u32,
            b: Wrapping<u32>,
            c: Option<NonZeroU32>,
        }

        let expected_bytes: Vec<u8> = if cfg!(target_endian = "little") {
            vec![1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        } else {
            vec![0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0]
        };
        let post_mutation_expected_a =
            if cfg!(target_endian = "little") { 0x00_00_00_FE } else { 0xFF_00_00_01 };
        test::<_, 12>(
            &mut Foo { a: 1, b: Wrapping(2), c: None },
            expected_bytes.as_bytes(),
            &Foo { a: post_mutation_expected_a, b: Wrapping(2), c: None },
        );
        test::<_, 3>(
            Unsized::from_mut_slice(&mut [1, 2, 3]),
            &[1, 2, 3],
            Unsized::from_mut_slice(&mut [0xFE, 2, 3]),
        );
    }

    #[test]
    fn test_array() {
        #[derive(FromZeroes, FromBytes, AsBytes)]
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
        let buf = Align::<[u8; 8], u64>::default();
        let r = Ref::<_, u64>::new(&buf.t[..]).unwrap();
        assert_eq!(format!("{}", r), "0");
        assert_eq!(format!("{:?}", r), "Ref(0)");

        let buf = Align::<[u8; 8], u64>::default();
        let r = Ref::<_, [u64]>::new_slice(&buf.t[..]).unwrap();
        assert_eq!(format!("{:?}", r), "Ref([0])");
    }

    #[test]
    fn test_eq() {
        let buf1 = 0_u64;
        let r1 = Ref::<_, u64>::new(buf1.as_bytes()).unwrap();
        let buf2 = 0_u64;
        let r2 = Ref::<_, u64>::new(buf2.as_bytes()).unwrap();
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_ne() {
        let buf1 = 0_u64;
        let r1 = Ref::<_, u64>::new(buf1.as_bytes()).unwrap();
        let buf2 = 1_u64;
        let r2 = Ref::<_, u64>::new(buf2.as_bytes()).unwrap();
        assert_ne!(r1, r2);
    }

    #[test]
    fn test_ord() {
        let buf1 = 0_u64;
        let r1 = Ref::<_, u64>::new(buf1.as_bytes()).unwrap();
        let buf2 = 1_u64;
        let r2 = Ref::<_, u64>::new(buf2.as_bytes()).unwrap();
        assert!(r1 < r2);
    }

    #[test]
    fn test_new_zeroed() {
        assert!(!bool::new_zeroed());
        assert_eq!(u64::new_zeroed(), 0);
        // This test exists in order to exercise unsafe code, especially when
        // running under Miri.
        #[allow(clippy::unit_cmp)]
        {
            assert_eq!(<()>::new_zeroed(), ());
        }
    }

    #[test]
    fn test_transparent_packed_generic_struct() {
        #[derive(AsBytes, FromZeroes, FromBytes, Unaligned)]
        #[repr(transparent)]
        struct Foo<T> {
            _t: T,
            _phantom: PhantomData<()>,
        }

        assert_impl_all!(Foo<u32>: FromZeroes, FromBytes, AsBytes);
        assert_impl_all!(Foo<u8>: Unaligned);

        #[derive(AsBytes, FromZeroes, FromBytes, Unaligned)]
        #[repr(packed)]
        struct Bar<T, U> {
            _t: T,
            _u: U,
        }

        assert_impl_all!(Bar<u8, AU64>: FromZeroes, FromBytes, AsBytes, Unaligned);
    }

    #[test]
    fn test_impls() {
        use core::borrow::Borrow;

        // A type that can supply test cases for testing
        // `TryFromBytes::is_bit_valid`. All types passed to `assert_impls!`
        // must implement this trait; that macro uses it to generate runtime
        // tests for `TryFromBytes` impls.
        //
        // All `T: FromBytes` types are provided with a blanket impl. Other
        // types must implement `TryFromBytesTestable` directly (ie using
        // `impl_try_from_bytes_testable!`).
        trait TryFromBytesTestable {
            fn with_passing_test_cases<F: Fn(&Self)>(f: F);
            // Both arguments to `f` have the same contents. The `&[u8]`
            // argument is provided so that the contents may be printed on error
            // for debugging (`MaybeValid: !AsBytes`).
            fn with_failing_test_cases<F: Fn(&MaybeValid<Self>, &[u8])>(f: F);
        }

        impl<T: FromBytes> TryFromBytesTestable for T {
            fn with_passing_test_cases<F: Fn(&Self)>(f: F) {
                // Test with a zeroed value.
                f(&Self::new_zeroed());

                let ffs = {
                    let mut t = Self::new_zeroed();
                    let ptr: *mut T = &mut t;
                    // SAFETY: `T: FromBytes`
                    unsafe { ptr::write_bytes(ptr.cast::<u8>(), 0xFF, mem::size_of::<T>()) };
                    t
                };

                // Test with a value initialized with 0xFF.
                f(&ffs);
            }

            fn with_failing_test_cases<F: Fn(&MaybeValid<Self>, &[u8])>(_f: F) {}
        }

        // Implements `TryFromBytesTestable`.
        //
        // # Safety
        //
        // All failure cases must have a valid size and alignment for `Self`.
        // For unsized types, the failure case's type's trailing slice element
        // must have the same size as `Self`'s trailing slice element so that
        // `as` casting a raw pointer preserves length.
        macro_rules! impl_try_from_bytes_testable {
            // Implements for a type with no type parameters.
            (=> @success $($success_case:expr),* $(, @failure $($failure_case:expr),*)?) => {};
            ($ty:ty $(,$tys:ty)* => @success $($success_case:expr),* $(, @failure $($failure_case:expr),*)?) => {
                impl TryFromBytesTestable for $ty {
                    impl_try_from_bytes_testable!(
                        @methods     @success $($success_case),*
                                 $(, @failure $($failure_case),*)?
                    );
                }
                impl_try_from_bytes_testable!($($tys),* => @success $($success_case),* $(, @failure $($failure_case),*)?);
            };
            // Implements for multiple types with no type parameters.
            ($($($ty:ty),* => @success $($success_case:expr), * $(, @failure $($failure_case:expr),*)?;)*) => {
                $(
                    impl_try_from_bytes_testable!($($ty),* => @success $($success_case),* $(, @failure $($failure_case),*)*);
                )*
            };
            // Implements only the methods; caller must invoke this from inside
            // an impl block.
            (@methods @success $($success_case:expr),* $(, @failure $($failure_case:expr),*)?) => {
                fn with_passing_test_cases<F: Fn(&Self)>(_f: F) {
                    $(
                        _f($success_case.borrow());
                    )*
                }

                fn with_failing_test_cases<F: Fn(&MaybeValid<Self>, &[u8])>(_f: F) {
                    $($(
                        // `unused_qualifications` is spuriously triggered on
                        // `Option::<Self>::None`.
                        #[allow(unused_qualifications)]
                        let case = $failure_case.as_bytes();
                        // SAFETY: Caller promises that this conversion is
                        // valid, and that `m` will be properly sized and
                        // aligned.
                        #[allow(clippy::undocumented_unsafe_blocks)] // spuriously triggered in 1.61
                        let m = unsafe {
                            #[allow(clippy::as_conversions)]
                            let m = &*(case as *const _ as *const MaybeValid<Self>);
                            m
                        };
                        _f(&m, case);
                    )*)?
                }
            };
        }

        // SAFETY: All failure cases use a type with:
        // - the same size as `Self`
        // - the same alignment as `Self`
        // - for unsized types, the same slice element size as `Self`
        impl_try_from_bytes_testable!(
            bool => @success true, false,
                    @failure 2u8, 3u8, 0xFFu8;
            char => @success '\u{0}', '\u{D7FF}', '\u{E000}', '\u{10FFFF}',
                    @failure 0xD800u32, 0xDFFFu32, 0x110000u32;
            str  => @success "", "hello", "❤️🧡💛💚💙💜",
                    @failure [0, 159, 146, 150];
            [u8] => @success [], [0, 1, 2];
            NonZeroU8, NonZeroI8, NonZeroU16, NonZeroI16, NonZeroU32,
            NonZeroI32, NonZeroU64, NonZeroI64, NonZeroU128, NonZeroI128,
            NonZeroUsize, NonZeroIsize
                 => @success Self::new(1).unwrap(),
                    // Doing this instead of `0` ensures that we always satisfy
                    // the size and alignment requirements of `Self` (whereas
                    // `0` may be any integer type with a different size or
                    // alignment than some `NonZeroXxx` types).
                    @failure Option::<Self>::None;
            ManuallyDrop<bool>
                 => @success ManuallyDrop::new(true), ManuallyDrop::new(false),
                    @failure 3u8, 4u8, 0xFFu8;
            // TODO(#321): Add success test cases for `ManuallyDrop<[bool]>`
            // once we have an easy way of converting `[ManuallyDrop<bool>] ->
            // ManuallyDrop<[bool]>`.
            //
            // TODO(#5): Add failure test cases for `ManuallyDrop<[bool]>`
            // once we support generic unsized `MaybeValid`.
            //
            // Here are some suggested test cases:
            //
            //      @success [ManuallyDrop::new(true), ManuallyDrop::new(false)][..],
            //               [ManuallyDrop::new(false), ManuallyDrop::new(true)][..],
            //      @failure [3u8], [4u8], [0xFFu8], [0u8, 1, 0xFF];
            ManuallyDrop<[bool]> => @success;
            mem::MaybeUninit<bool>
                 => @success mem::MaybeUninit::new(false),
                             mem::MaybeUninit::new(true),
                             mem::MaybeUninit::uninit(),
                             // SAFETY: `mem::MaybeUninit<T>` is `FromBytes`
                             // when `T: FromBytes` only because that's a way of
                             // ensuring that it contains no `UnsafeCell`s. Any
                             // bit patterns are still sound.
                             unsafe { core::mem::transmute::<_, mem::MaybeUninit<bool>>(0xFFu8) };
            [bool; 0] => @success [];
            [bool; 1]
                 => @success [true], [false],
                    @failure [2u8], [3u8], [0xFFu8];
            [bool]
                 => @success [true, false], [false, true],
                    @failure [2u8], [3u8], [0xFFu8], [0u8, 1u8, 2u8];


        );

        // Asserts that `$ty` implements any `$trait` and doesn't implement any
        // `!$trait`. Note that all `$trait`s must come before any `!$trait`s.
        //
        // For `T: TryFromBytes`, uses `TryFromBytesTestable` to test success
        // and failure cases for `TryFromBytes::is_bit_valid`.
        macro_rules! assert_impls {
            ($ty:ty: TryFromBytes) => {
                <$ty as TryFromBytesTestable>::with_passing_test_cases(|val| {
                    let m = MaybeValid::from_ref(val);
                    assert!(<$ty as TryFromBytes>::is_bit_valid(m), "{}::is_bit_valid({:?}): got false, expected true", stringify!($ty), val);

                    // TODO(#5): In addition to testing `is_bit_valid`, test the
                    // methods built on top of it. This would both allow us to
                    // test their implementations and actually convert the bytes
                    // to `$ty`, giving Miri a chance to catch if this is
                    // unsound (ie, if our `is_bit_valid` impl is buggy).
                    //
                    // The following code was tried, but it doesn't work because
                    // a) some types are not `AsBytes` and, b) some types are
                    // not `Sized`.
                    //
                    //   let r = <$ty as TryFromBytes>::try_from_ref(val.as_bytes()).unwrap();
                    //   assert_eq!(r, &val);
                    //   let r = <$ty as TryFromBytes>::try_from_mut(val.as_bytes_mut()).unwrap();
                    //   assert_eq!(r, &mut val);
                    //   let v = <$ty as TryFromBytes>::try_read_from(val.as_bytes()).unwrap();
                    //   assert_eq!(v, val);
                });
                <$ty as TryFromBytesTestable>::with_failing_test_cases(|m, bytes| {
                    assert!(!<$ty as TryFromBytes>::is_bit_valid(m), "{}::is_bit_valid({:?}): got true, expected false", stringify!($ty), bytes);
                });

                #[allow(dead_code)]
                const _: () = { static_assertions::assert_impl_all!($ty: TryFromBytes); };
            };
            ($ty:ty: $trait:ident) => {
                #[allow(dead_code)]
                const _: () = { static_assertions::assert_impl_all!($ty: $trait); };
            };
            ($ty:ty: !$trait:ident) => {
                #[allow(dead_code)]
                const _: () = { static_assertions::assert_not_impl_any!($ty: $trait); };
            };
            ($ty:ty: $($trait:ident),* $(,)? $(!$negative_trait:ident),*) => {
                $(
                    assert_impls!($ty: $trait);
                )*

                $(
                    assert_impls!($ty: !$negative_trait);
                )*
            };
        }

        assert_impls!((): TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(u8: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(i8: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(u16: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(i16: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(u32: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(i32: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(u64: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(i64: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(u128: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(i128: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(usize: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(isize: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(f32: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(f64: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);

        assert_impls!(bool: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);
        assert_impls!(char: TryFromBytes, FromZeroes, AsBytes, !FromBytes, !Unaligned);
        assert_impls!(str: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);

        assert_impls!(NonZeroU8: TryFromBytes, AsBytes, Unaligned, !FromZeroes, !FromBytes);
        assert_impls!(NonZeroI8: TryFromBytes, AsBytes, Unaligned, !FromZeroes, !FromBytes);
        assert_impls!(NonZeroU16: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroI16: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroU32: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroI32: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroU64: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroI64: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroU128: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroI128: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroUsize: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);
        assert_impls!(NonZeroIsize: TryFromBytes, AsBytes, !FromZeroes, !FromBytes, !Unaligned);

        assert_impls!(Option<NonZeroU8>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(Option<NonZeroI8>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(Option<NonZeroU16>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroI16>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroU32>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroI32>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroU64>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroI64>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroU128>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroI128>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroUsize>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);
        assert_impls!(Option<NonZeroIsize>: TryFromBytes, FromZeroes, FromBytes, AsBytes, !Unaligned);

        // Implements none of the ZC traits, but implements `KnownLayout` so
        // that types like `MaybeUninit<KnownLayout>` can at least be written
        // down without causing errors so that we can test them.
        struct NotZerocopy;
        impl_known_layout!(NotZerocopy);

        assert_impls!(PhantomData<NotZerocopy>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(PhantomData<[u8]>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);

        assert_impls!(ManuallyDrop<u8>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(ManuallyDrop<[u8]>: FromZeroes, FromBytes, AsBytes, Unaligned, !TryFromBytes);
        assert_impls!(ManuallyDrop<bool>: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);
        assert_impls!(ManuallyDrop<[bool]>: FromZeroes, AsBytes, Unaligned, !FromBytes, !TryFromBytes);
        assert_impls!(ManuallyDrop<NotZerocopy>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
        assert_impls!(ManuallyDrop<[NotZerocopy]>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

        assert_impls!(mem::MaybeUninit<u8>: TryFromBytes, FromZeroes, FromBytes, Unaligned, !AsBytes);
        assert_impls!(mem::MaybeUninit<bool>: TryFromBytes, FromZeroes, Unaligned, !AsBytes, !FromBytes);
        assert_impls!(mem::MaybeUninit<NotZerocopy>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

        assert_impls!(MaybeUninit<u8>: FromZeroes, FromBytes, Unaligned, !TryFromBytes, !AsBytes);
        assert_impls!(MaybeUninit<MaybeUninit<u8>>: FromZeroes, FromBytes, Unaligned, !TryFromBytes, !AsBytes);
        assert_impls!(MaybeUninit<[u8]>: FromZeroes, FromBytes, Unaligned, !TryFromBytes, !AsBytes);
        assert_impls!(MaybeUninit<MaybeUninit<[u8]>>: FromZeroes, FromBytes, Unaligned, !TryFromBytes, !AsBytes);
        assert_impls!(MaybeUninit<NotZerocopy>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
        assert_impls!(MaybeUninit<MaybeUninit<NotZerocopy>>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

        assert_impls!(MaybeValid<u8>: FromZeroes, FromBytes, Unaligned, AsBytes);
        assert_impls!(MaybeValid<MaybeValid<u8>>: Unaligned, AsBytes, !FromZeroes, !FromBytes);
        assert_impls!(MaybeValid<[u8]>: FromZeroes, FromBytes, Unaligned, AsBytes);
        assert_impls!(MaybeValid<NotZerocopy>: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
        assert_impls!(MaybeValid<MaybeValid<NotZerocopy>>: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

        assert_impls!(Wrapping<u8>: FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(Wrapping<NotZerocopy>: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

        assert_impls!(Unalign<u8>: FromZeroes, FromBytes, AsBytes, Unaligned, !TryFromBytes);
        assert_impls!(Unalign<NotZerocopy>: Unaligned, !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes);

        assert_impls!([u8]: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!([bool]: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);
        assert_impls!([NotZerocopy]: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
        assert_impls!([u8; 0]: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!([bool; 0]: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);
        assert_impls!([NotZerocopy; 0]: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
        assert_impls!([u8; 1]: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!([bool; 1]: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);
        assert_impls!([NotZerocopy; 1]: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
    }
}
