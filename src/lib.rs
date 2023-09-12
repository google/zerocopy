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
    clippy::missing_inline_in_public_items,
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
    alloc::Layout,
    cell::{self, RefMut},
    cmp::Ordering,
    fmt::{self, Debug, Display, Formatter},
    hash::Hasher,
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
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
use alloc::{boxed::Box, vec::Vec};

use crate::util::AsAddress as _;

// For each polyfill, as soon as the corresponding feature is stable, the
// polyfill import will be unused because method/function resolution will prefer
// the inherent method/function over a trait method/function. Thus, we suppress
// the `unused_imports` warning.
//
// See the documentation on `util::polyfills` for more information.
#[allow(unused_imports)]
use crate::util::polyfills::{NonNullExt as _, NonNullSliceExt as _};

// This is a hack to allow zerocopy-derive derives to work in this crate. They
// assume that zerocopy is linked as an extern crate, so they access items from
// it as `zerocopy::Xxx`. This makes that still work.
#[cfg(any(feature = "derive", test))]
mod zerocopy {
    pub(crate) use crate::*;
}

/// The layout of a type which might be dynamically-sized.
///
/// `DstLayout` describes the layout of sized types, slice types, and "custom
/// DSTs" - ie, those that are known by the type system to have a trailing slice
/// (as distinguished from `dyn Trait` types - such types *might* have a
/// trailing slice type, but the type system isn't aware of it).
#[doc(hidden)]
#[allow(missing_debug_implementations, missing_copy_implementations)]
#[cfg_attr(test, derive(Copy, Clone, Debug, PartialEq, Eq))]
pub struct DstLayout {
    /// The base size and the alignment of the type:
    /// - For sized types, the size encoded by this `Layout` is
    ///   `size_of::<T>()`. For DSTs, the size represents the size of the type
    ///   when the trailing slice field contains 0 elements.
    /// - For all types, the alignment represents the alignment of the type.
    // TODO: If we end up replacing this with separate size and alignment to
    // make Kani happy, file an issue to eventually adopt the stdlib's
    // `Alignment` type trick.
    _base_layout: Layout,
    /// For sized types, `None`. For DSTs, the size of the element type of the
    /// trailing slice.
    _trailing_slice_elem_size: Option<usize>,
}

#[cfg_attr(test, derive(Copy, Clone, Debug))]
enum CastType {
    Prefix,
    _Suffix,
}

impl DstLayout {
    /// Constructs a `DstLayout` which describes `T`.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that `DstLayout` is the correct layout for `T`.
    const fn for_type<T>() -> DstLayout {
        DstLayout { _base_layout: Layout::new::<T>(), _trailing_slice_elem_size: None }
    }

    /// Constructs a `DstLayout` which describes `[T]`.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that `DstLayout` is the correct layout for `[T]`.
    const fn for_slice<T>() -> DstLayout {
        DstLayout {
            // SAFETY: `[T; 0]` has the same alignment as `T`, but zero size.
            // [1] A slice of length 0 has no size, so 0 is the correct size for
            // the base of the type.
            //
            // [1] https://doc.rust-lang.org/reference/type-layout.html#array-layout
            _base_layout: Layout::new::<[T; 0]>(),
            _trailing_slice_elem_size: Some(mem::size_of::<T>()),
        }
    }

    /// Validates that a cast is sound from a layout perspective.
    ///
    /// Validates that the size and alignment requirements of a type with the
    /// layout described in `self` would not be violated by performing a
    /// `cast_type` cast from a pointer with address `addr` which refers to a
    /// memory region of size `bytes_len`.
    ///
    /// If the cast is valid, `validate_cast` returns `(elems, split_at)`. If
    /// `self` describes a dynamically-sized type, then `elems` is the maximum
    /// number of trailing slice elements for which a cast would be valid (for
    /// sized types, `elem` is meaningless and should be ignored). `split_at` is
    /// the index at which to split the memory region in order for the prefix
    /// (suffix) to contain the result of the cast, and in order for the
    /// remaining suffix (prefix) to contain the leftover bytes.
    ///
    /// There are three conditions under which a cast can fail:
    /// - The smallest possible value for the type is larger than the provided
    ///   memory region
    /// - A prefix cast is requested, and `addr` does not satisfy `self`'s
    ///   alignment requirement
    /// - A suffix cast is requested, and `addr + bytes_len` does not satisfy
    ///   `self`'s alignment requirement (as a consequence, since the size of
    ///   the trailing slice element is a multiple of the alignment, no length
    ///   for the trailing slice will result in a starting address which is
    ///   properly aligned)
    ///
    /// # Safety
    ///
    /// The caller may assume that this implementation is correct, and may rely
    /// on that assumption for the soundness of their code. In particular, the
    /// caller may assume that, if `validate_cast` returns `Some((elems,
    /// split_at))`, then:
    /// - A pointer to the type (for dynamically sized types, this includes
    ///   `elems` as its pointer metadata) describes an object of size `size <=
    ///   bytes_len`
    /// - If this is a prefix cast:
    ///   - `addr` satisfies `self`'s alignment
    ///   - `size == split_at`
    /// - If this is a suffix cast:
    ///   - `split_at == bytes_len - size`
    ///   - `addr + split_at` satisfies `self`'s alignment
    ///
    /// Note that this method does *not* ensure that a pointer constructed from
    /// its return values will be a valid pointer. In particular, this method
    /// does not reason about `isize` overflow, which is a requirement of many
    /// Rust pointer APIs, and may at some point be determined to be a validity
    /// invariant of pointer types themselves. This should never be a problem so
    /// long as the arguments to this method are derived from a known-valid
    /// pointer (e.g., one derived from a safe Rust reference), but it is
    /// nonetheless the caller's responsibility to justify that pointer
    /// arithmetic will not overflow based on a safety argument *other than* the
    /// mere fact that this method returned successfully.
    ///
    /// # Panics
    ///
    /// If `addr + bytes_len` overflows `usize`, `validate_cast` may panic, or
    /// it may return incorrect results. No guarantees are made about when
    /// `validate_cast` will panic. The caller should not rely on
    /// `validate_cast` panicking in any particular condition, even if
    /// `debug_assertions` are enabled.
    const fn validate_cast(
        &self,
        addr: usize,
        bytes_len: usize,
        cast_type: CastType,
    ) -> Option<(usize, usize)> {
        // `debug_assert!`, but with `#[allow(clippy::arithmetic_side_effects)]`.
        macro_rules! __debug_assert {
            ($e:expr $(, $msg:expr)?) => {
                debug_assert!({
                    #[allow(clippy::arithmetic_side_effects)]
                    let e = $e;
                    e
                } $(, $msg)?);
            };
        }

        // Note that, in practice, `elem_size` is always a compile-time
        // constant. We do this check earlier than needed to ensure that we
        // always panic as a result of bugs in the program (such as calling this
        // function on an invalid type) instead of allowing this panic to be
        // hidden if the cast would have failed anyway for runtime reasons (such
        // as a too-small memory region).
        //
        // TODO(#67): Once our MSRV is 1.65, use let-else:
        // https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html#let-else-statements
        let elem_size = match self._trailing_slice_elem_size {
            Some(elem_size) => match NonZeroUsize::new(elem_size) {
                Some(elem_size) => Some(elem_size),
                None => panic!("attempted to cast to slice type with zero-sized element"),
            },
            None => None,
        };

        // Precondition
        __debug_assert!(addr.checked_add(bytes_len).is_some(), "`addr` + `bytes_len` > usize::MAX");

        // We check alignment for `addr` (for prefix casts) or `addr +
        // bytes_len` (for suffix casts). For a prefix cast, the correctness of
        // this check is trivial - `addr` is the address the object will live
        // at.
        //
        // For a suffix cast, we know that all valid sizes for the type are a
        // multiple of the alignment. Thus, a validly-sized instance which lives
        // at a validly-aligned address must also end at a validly-aligned
        // address. Thus, if the end address for a suffix cast (`addr +
        // bytes_len`) is not aligned, then no valid start address will be
        // aligned either.
        let offset = match cast_type {
            CastType::Prefix => 0,
            CastType::_Suffix => bytes_len,
        };

        // Addition is guaranteed not to overflow because `offset <= bytes_len`,
        // and `addr + bytes_len <= usize::MAX` is a precondition of this
        // method. Modulus is guaranteed not to divide by 0 because `.align()`
        // guarantees that its return value is non-zero.
        #[allow(clippy::arithmetic_side_effects)]
        if (addr + offset) % self._base_layout.align() != 0 {
            return None;
        }

        let base_size = self._base_layout.size();

        // LEMMA 0: max_slice_bytes + base_size == bytes_len
        //
        // LEMMA 1: base_size <= bytes_len:
        // - If `base_size > bytes_len`, `bytes_len.checked_sub(base_size)`
        //   returns `None`, and we return.
        //
        // TODO(#67): Once our MSRV is 1.65, use let-else:
        // https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html#let-else-statements
        let max_slice_bytes = if let Some(max_byte_slice) = bytes_len.checked_sub(base_size) {
            max_byte_slice
        } else {
            return None;
        };

        // Lemma 0
        __debug_assert!(max_slice_bytes + base_size == bytes_len);

        // Lemma 1
        __debug_assert!(base_size <= bytes_len);

        let (elems, self_bytes) = if let Some(elem_size) = elem_size {
            // Guaranteed not to divide by 0 because `elem_size` is a
            // `NonZeroUsize`.
            #[allow(clippy::arithmetic_side_effects)]
            let elems = max_slice_bytes / elem_size.get();

            // NOTE: Another option for this step in the algorithm is to set
            // `slice_bytes = elems * elem_size`. However, using multiplication
            // causes Kani to choke. In practice, the compiler is likely to
            // generate identical machine code in both cases. Note that this
            // divide-then-mod approach is trivially optimizable into a single
            // operation that computes both the quotient and the remainder.

            // First line is guaranteed not to mod by 0 because `elem_size` is a
            // `NonZeroUsize`. Second line is guaranteed not to underflow
            // because `rem <= max_slice_bytes` thanks to the mod operation.
            //
            // LEMMA 2: slice_bytes <= max_slice_bytes
            #[allow(clippy::arithmetic_side_effects)]
            let rem = max_slice_bytes % elem_size.get();
            #[allow(clippy::arithmetic_side_effects)]
            let slice_bytes = max_slice_bytes - rem;

            // Lemma 2
            __debug_assert!(slice_bytes <= max_slice_bytes);

            // Guaranteed not to overflow:
            // - max_slice_bytes + base_size == bytes_len       (lemma 0)
            // - slice_bytes                 <= max_slice_bytes (lemma 2)
            // - slice_bytes + base_size     <= bytes_len       (substitution) ------+
            // - bytes_len                   <= usize::MAX      (bytes_len: usize)   |
            // - slice_bytes + base_size     <= usize::MAX      (substitution)       |
            //                                                                       |
            // LEMMA 3: self_bytes <= bytes_len:                                     |
            // - slice_bytes + base_size     <= bytes_len <--------------------------+ (reused for lemma)
            // - slice_bytes                 <= bytes_len
            #[allow(clippy::arithmetic_side_effects)]
            let self_bytes = base_size + slice_bytes;

            // Lemma 3
            __debug_assert!(self_bytes <= bytes_len);

            (elems, self_bytes)
        } else {
            (0, base_size)
        };

        // LEMMA 4: self_bytes <= bytes_len:
        // - `if` branch returns `self_bytes`; lemma 3 guarantees `self_bytes <=
        //   bytes_len`
        // - `else` branch returns `base_size`; lemma 1 guarantees `base_size <=
        //   bytes_len`

        // Lemma 4
        __debug_assert!(self_bytes <= bytes_len);

        let split_at = match cast_type {
            CastType::Prefix => self_bytes,
            // Guaranteed not to underflow because `self_bytes <= bytes_len`
            // (lemma 4).
            #[allow(clippy::arithmetic_side_effects)]
            CastType::_Suffix => bytes_len - self_bytes,
        };

        Some((elems, split_at))
    }

    /// Calls `validate_exact_cast` and ensures that all of `bytes_len` are
    /// used.
    ///
    /// Passes all arguments to `validate_cast`, and passes `CastType::Prefix`.
    /// If the cast would leave any suffix bytes left over,
    /// `validate_exact_cast` returns `None`.
    const fn validate_exact_cast(&self, addr: usize, bytes_len: usize) -> Option<usize> {
        match self.validate_cast(addr, bytes_len, CastType::Prefix) {
            Some((elems, split_at)) if split_at == bytes_len => Some(elems),
            Some(_) | None => None,
        }
    }
}

/// A trait which carries information about a type's layout that is used by the
/// internals of this crate.
///
/// This trait is not meant for consumption by code outside of this crate. While
/// the normal semver stability guarantees apply with respect to which types
/// implement this trait and which trait implementations are implied by this
/// trait, no semver stability guarantees are made regarding its internals; they
/// may change at any time, and code which makes use of them may break.
///
/// # Safety
///
/// This trait does not convey any safety guarantees to code outside this crate.
#[doc(hidden)] // TODO: Remove this once KnownLayout is used by other APIs
pub unsafe trait KnownLayout: sealed::KnownLayoutSealed {
    #[doc(hidden)]
    const LAYOUT: DstLayout;

    /// SAFETY: The returned pointer has the same address and provenance as
    /// `bytes`. If `Self` is a DST, the returned pointer's referent has `elems`
    /// elements in its trailing slice. If `Self` is sized, `elems` is ignored.
    #[doc(hidden)]
    fn raw_from_ptr_len(bytes: NonNull<u8>, elems: usize) -> NonNull<Self>;
}

impl<T: KnownLayout> sealed::KnownLayoutSealed for [T] {}
// SAFETY: Delegates safety to `DstLayout::for_slice`.
unsafe impl<T: KnownLayout> KnownLayout for [T] {
    const LAYOUT: DstLayout = DstLayout::for_slice::<T>();

    // SAFETY: `.cast` preserves address and provenance. The returned pointer
    // refers to an object with `elems` elements by construction.
    #[inline(always)]
    fn raw_from_ptr_len(data: NonNull<u8>, elems: usize) -> NonNull<Self> {
        // TODO(#67): Remove this allow. See NonNullExt for more details.
        #[allow(unstable_name_collisions)]
        NonNull::slice_from_raw_parts(data.cast::<T>(), elems)
    }
}

#[rustfmt::skip]
impl_known_layout!(
    (),
    u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, f32, f64,
    bool, char,
    NonZeroU8, NonZeroI8, NonZeroU16, NonZeroI16, NonZeroU32, NonZeroI32,
    NonZeroU64, NonZeroI64, NonZeroU128, NonZeroI128, NonZeroUsize, NonZeroIsize
);
#[rustfmt::skip]
impl_known_layout!(
    T         => Option<T>,
    T: ?Sized => PhantomData<T>,
    T         => Wrapping<T>,
    T         => MaybeUninit<T>,
);
impl_known_layout!(const N: usize, T => [T; N]);

safety_comment! {
    /// SAFETY:
    /// `str` and `ManuallyDrop<[T]>` have the same representations as `[u8]`
    /// and `[T]` repsectively. `str` has different bit validity than `[u8]`,
    /// but that doesn't affect the soundness of this impl.
    unsafe_impl_known_layout!(#[repr([u8])] str);
    unsafe_impl_known_layout!(T: ?Sized + KnownLayout => #[repr(T)] ManuallyDrop<T>);
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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline]
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
    #[inline]
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
    #[inline(always)]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
/// # What is a "valid instance"?
///
/// In Rust, each type has *bit validity*, which refers to the set of bit
/// patterns which may appear in an instance of that type. It is impossible for
/// safe Rust code to produce values which violate bit validity (ie, values
/// outside of the "valid" set of bit patterns). If `unsafe` code produces an
/// invalid value, this is considered [undefined behavior].
///
/// Rust's bit validity rules are currently being decided, which means that some
/// types have three classes of bit patterns: those which are definitely valid,
/// and whose validity is documented in the language; those which may or may not
/// be considered valid at some point in the future; and those which are
/// definitely invalid.
///
/// Zerocopy takes a conservative approach, and only considers a bit pattern to
/// be valid if its validity is a documenteed guarantee provided by the
/// language.
///
/// For most use cases, Rust's current guarantees align with programmers'
/// intuitions about what ought to be valid. As a result, zerocopy's
/// conservatism should not affect most users. One notable exception is unions,
/// whose bit validity is very up in the air; zerocopy does not permit
/// implementing `TryFromBytes` for any union type.
///
/// If you are negatively affected by lack of support for a particular type,
/// we encourage you to let us know by [filing an issue][github-repo].
///
/// # Safety
///
/// On its own, `T: TryFromBytes` does not make any guarantees about the layout
/// or representation of `T`. It merely provides the ability to perform a
/// validity check at runtime via methods like [`try_from_ref`].
///
/// Currently, it is not possible to stably implement `TryFromBytes` other than
/// by using `#[derive(TryFromBytes)]`. While there are `#[doc(hidden)]` items
/// on this trait that provide well-defined safety invariants, no stability
/// guarantees are made with respect to these items. In particular, future
/// releases of zerocopy may make backwards-breaking changes to these items,
/// including changes that only affect soundness, which may cause code which
/// uses those items to silently become unsound.
///
/// [undefined behavior]: https://raphlinus.github.io/programming/rust/2018/08/17/undefined-behavior.html
/// [github-repo]: https://github.com/google/zerocopy
/// [`try_from_ref`]: TryFromBytes::try_from_ref
pub unsafe trait TryFromBytes: KnownLayout {
    /// Does a given memory range contain a valid instance of `Self`?
    ///
    /// # Safety
    ///
    /// ## Preconditions
    ///
    /// `candidate` must be properly aligned for `Self`, and it must be [valid]
    /// for reads. The total length encoded by the pointer must not overflow an
    /// `isize`. The memory addressed by `candidate` must fall within a single
    /// allocation.
    ///
    /// `candidate` is not required to refer to a valid `Self`. However, it must
    /// satisfy the requirement that uninitialized bytes may only be present
    /// where it is possible for them to be present in `Self`. This is a dynamic
    /// property: if, at a particular byte offset, a valid enum discriminant is
    /// set, the subsequent bytes may only have uninitialized bytes as
    /// specificed by the corresponding enum.
    ///
    /// Formally, given `len = size_of_val_raw(candidate)`, at every byte
    /// offset, `b`, in the range `[0, len)`:
    /// - If, in all instances `s: Self` of length `len`, the byte at offset `b`
    ///   in `s` is initialized, then the byte at offset `b` within `*candidate`
    ///   must be initialized.
    /// - Let `c` be the contents of the byte range `[0, b)` in `*candidate`.
    ///   Let `S` be the subset of valid instances of `Self` of length `len`
    ///   which contain `c` in the offset range `[0, b)`. If, for all instances
    ///   of `s: Self` in `S`, the byte at offset `b` in `s` is initialized,
    ///   then the byte at offset `b` in `*candidate` must be initialized.
    ///
    ///   Pragmatically, this means that if `*candidate` is guaranteed to
    ///   contain an enum type at a particular offset, and the enum discriminant
    ///   stored in `*candidate` corresponds to a valid variant of that enum
    ///   type, then it is guaranteed that the appropriate bytes of `*candidate`
    ///   are initialized as defined by that variant's bit validity (although
    ///   note that the variant may contain another enum type, in which case the
    ///   same rules apply depending on the state of its discriminant, and so on
    ///   recursively).
    ///
    /// ## Postconditions
    ///
    /// Unsafe code may assume that, if `is_bit_valid(candidate)` returns true,
    /// `*candidate` contains a valid `Self`.
    ///
    /// [valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
    #[doc(hidden)]
    unsafe fn is_bit_valid(candidate: NonNull<Self>) -> bool;

    /// Attempts to interpret a byte slice as a `Self`.
    ///
    /// `try_from_ref` validates that `bytes` contains a valid `Self`, and that
    /// it satisfies `Self`'s alignment requirement. If it does, then `bytes` is
    /// reinterpreted as a `Self`.
    ///
    /// Note that Rust's bit validity rules are still being decided. As such,
    /// there exist types whose bit validity is ambiguous. See the
    /// `TryFromBytes` docs for a discussion of how these cases are handled.
    // TODO(#251): In a future in which we distinguish between `FromBytes` and
    // `RefFromBytes`, this requires `where Self: RefFromBytes` to disallow
    // interior mutability.
    #[inline]
    fn try_from_ref(bytes: &[u8]) -> Option<&Self> {
        // PANICS: `bytes` is a `&[u8]`, and so the sum of its address and
        // length cannot overflow `usize`.
        let trailing_elems = Self::LAYOUT.validate_exact_cast(bytes.addr(), bytes.len())?;
        let maybe_self = Self::raw_from_ptr_len(NonNull::from(bytes).cast::<u8>(), trailing_elems);

        // SAFETY:
        // - `bytes` is a `&[u8]`, which guarantees that its length doesn't
        //   overflow `isize` and that it comes from a single allocation
        // - `validate_exact_cast` checked alignment
        // - all bytes of `bytes` are initialized
        if unsafe { !Self::is_bit_valid(maybe_self) } {
            return None;
        }

        // SAFETY:
        // - `is_bit_valid` guaranteed that `*maybe_self` contains a valid
        //   `Self`
        // - Since `Self` is not allowed to contain any `UnsafeCell`s:
        //   - The caller cannot use the `&Self` to perform interior mutation on
        //     a byte range that `bytes` views as not containing `UnsafeCell`s
        //   - The caller cannot use the `&Self` to write invalid values to
        //     `bytes` (namely, uninitialized bytes, as `[u8]` has no other bit
        //     validity constraints)
        // - Since `[u8]` does not contain any `UnsafeCell`s, we are guaranteed
        //   that, having verified that `maybe_self` currently contains a valid
        //   `Self`, code with access to `bytes` cannot cause it to no longer
        //   contain a valid `Self` in the future
        Some(unsafe { &*maybe_self.as_ptr() })
    }

    /// Attempts to interpret a mutable byte slice as a `Self`.
    ///
    /// `try_from_mut` validates that `bytes` contains a valid `Self`, and that
    /// it satisfies `Self`'s alignment requirement. If it does, then `bytes` is
    /// reinterpreted as a `Self`.
    ///
    /// Note that Rust's bit validity rules are still being decided. As such,
    /// there exist types whose bit validity is ambiguous. See the
    /// `TryFromBytes` docs for a discussion of how these cases are handled.
    // TODO(#251): In a future in which we distinguish between `FromBytes` and
    // `RefFromBytes`, this requires `where Self: RefFromBytes` to disallow
    // interior mutability.
    #[inline]
    fn try_from_mut(bytes: &mut [u8]) -> Option<&mut Self>
    where
        Self: AsBytes,
    {
        // PANICS: `bytes` is a `&[u8]`, and so the sum of its address and
        // length cannot overflow `usize`.
        let trailing_elems = Self::LAYOUT.validate_exact_cast(bytes.addr(), bytes.len())?;
        let maybe_self = Self::raw_from_ptr_len(NonNull::from(bytes).cast::<u8>(), trailing_elems);

        // SAFETY:
        // - `bytes` is a `&[u8]`, which guarantees that its length doesn't
        //   overflow `isize` and that it comes from a single allocation
        // - `validate_exact_cast` checked alignment
        // - all bytes of `bytes` are initialized
        if unsafe { !Self::is_bit_valid(maybe_self) } {
            return None;
        }

        // SAFETY:
        // - `is_bit_valid` guaranteed that `*maybe_self` contains a valid
        //   `Self`
        // - Since `Self: AsBytes`, any values written to the returned `&mut
        //   Self` will be valid for `[u8]` once it is accessible again
        // - Since the returned `&mut Self` has the same lifetime as the input
        //   `&mut [u8]`, that input cannot be directly mutated so long as the
        //   returned reference exists. Thus, having verified that `maybe_self`
        //   currently contains a valid `Self`, code with access to `bytes`
        //   cannot cause it to no longer contain a valid `Self` in the future.
        Some(unsafe { &mut *maybe_self.as_ptr() })
    }

    /// Attempts to read a `Self` from a byte slice.
    ///
    /// `try_from_mut` validates that `bytes` contains a valid `Self`. If it
    /// does, then the contents of `bytes` are copied and reinterpreted as a
    /// `Self`.
    ///
    /// Note that Rust's bit validity rules are still being decided. As such,
    /// there exist types whose bit validity is ambiguous. See the
    /// `TryFromBytes` docs for a discussion of how these cases are handled.
    #[inline]
    fn try_read_from(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        // A note on performance: We unconditionally read `size_of::<Self>()`
        // bytes into the local stack frame before validation. This has
        // advantages and disadvantages:
        // - It allows `MaybeUninit` to be aligned to `T`, and thus allows
        //   `is_bit_valid` to operate on an aligned value.
        // - It requires us to perform the copy even if validation fails.
        //
        // The authors believe that this is a worthwhile tradeoff. Allowing
        // `is_bit_valid` to operate on an aligned value can make the generated
        // machine code significantly smaller and faster. On the other hand, we
        // expect the vast majority of calls to `try_read_from` to succeed, and
        // in these cases, the copy will not be wasted.
        let maybe_uninit = MaybeUninit::<Self>::read_from(bytes)?;
        let candidate = NonNull::from(&maybe_uninit).cast::<Self>();

        // SAFETY:
        // - `MaybeUninit<Self>` has the same alignment as `Self`, so this is
        //   aligned
        // - `maybe_uninit` was initialized from `bytes`, so all of its bytes
        //   are initialized
        if unsafe { !Self::is_bit_valid(candidate) } {
            return None;
        }

        // SAFETY: `is_bit_valid` promises that it only returns true if its
        // argument contains a valid `Self`. This is exactly the safety
        // precondition of `assume_init`.
        Some(unsafe { maybe_uninit.assume_init() })
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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline]
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
    #[inline]
    fn write_to_prefix(&self, bytes: &mut [u8]) -> Option<()> {
        let size = mem::size_of_val(self);
        bytes.get_mut(..size)?.copy_from_slice(self.as_bytes());
        Some(())
    }

    /// Writes a copy of `self` to the suffix of `bytes`.
    ///
    /// `write_to_suffix` writes `self` to the last `size_of_val(self)` bytes of
    /// `bytes`. If `bytes.len() < size_of_val(self)`, it returns `None`.
    #[inline]
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
    ///   `{f32,f64}::from_bits` constructors' documentation [1] [2] states that
    ///   they are currently equivalent to `transmute`. [3]
    /// - `AsBytes`: the `{f32,f64}::to_bits` methods' documentation [4] [5]
    ///   states that they are currently equivalent to `transmute`. [3]
    ///
    /// TODO(#61): Make these arguments more precisely in terms of the
    /// documentation.
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
    /// - Since `bool`'s single byte is always initialized, the `is_bit_valid`
    ///   caller is required to ensure that the referent of the `NonNull<bool>`
    ///   argument is initialized. Since `u8` has no alignment requirement, this
    ///   means that, after converting from `NonNull<bool>` to `&u8`, the
    ///   resulting reference is properly aligned and points to a
    ///   properly-initialized `u8`.
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
    /// - `MaybeUninit<char>` has no bit validity requirements, and has the same
    ///   alignment as `char`. Since the `is_bit_valid` caller must promise that
    ///   the provided `NonNull<char>` is properly-aligned and points a region
    ///   which is valid for reads, that's all we need to ensure that converting
    ///   it to a `&MaybeUninit<char>` is sound.
    /// - Since we transmute `c` from the bytes passed to `is_bit_valid` without
    ///   modifying them, and since `char::from_u32` guarantees that it returns
    ///   `None` if its input is not a valid `char` [1], this function only
    ///   returns `true` if its argument is a valid `char`, and so this is a
    ///   sound implementation of `TryFromBytes::is_bit_valid`.
    ///
    /// Note that it might be slightly simpler to treat `candidate` as a `[u8;
    /// 4]` - it would make the code and the safety argument a bit simpler.
    /// However, using `&MaybeUninit<char>` ensures that the compiler preserves
    /// alignment information, which it may be able to use to produce smaller or
    /// better-performing assembly.
    ///
    /// [1] https://doc.rust-lang.org/std/primitive.char.html#method.from_u32
    ///
    /// TODO(https://github.com/rust-lang/reference/pull/1401): Use `&u32`
    /// instead once it's guaranteed that `align_of::<u32>() ==
    /// align_of::<char>()`.
    unsafe_impl!(char: TryFromBytes; |candidate: &MaybeUninit<char>| {
        // SAFETY: `MaybeUninit<u32>` has no bit validity constraints.
        let c: MaybeUninit<u32> = unsafe { mem::transmute(*candidate) };
        // SAFETY: Since all bytes of a `char` must be initialized, the bytes
        // passed to this function must all have been initialized.
        let c = unsafe { c.assume_init() };
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
    /// - Since `str`'s bytes are all always initialized, `is_bit_valid`'s
    ///   caller must ensure that the bytes they pass are all initialized. Since
    ///   `&[u8]` has no alignment requirement and no bit validity requirement
    ///   beyond that its bytes be initialized, it is sound to convert the
    ///   caller's `NonNull<str>` (which they promise is valid for reads) to a
    ///   `&[u8]`.
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
    /// - The caller is required to provide a `NonNull<NonZeroXxx>` which is
    ///   properly aligned and is valid for reads. Since very byte of a
    ///   `NonZeroXxx` must be initialized, the pointer's referent must have all
    ///   its bytes initialized.
    ///
    ///   Since `Xxx` has the same size and alignment as `NonZeroXxx`, the
    ///   provided `NonNull<NonZeroXxx>` is also aligned to `Xxx` and is valid
    ///   for reads of size `Xxx`. Since `Xxx` has no bit validity requirements
    ///   other than that its bytes are initialized, this means that the
    ///   provided `NonNull<NonZeroXxx>` may soundly be converted to a `&Xxx`.
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
    /// [1]
    /// https://doc.rust-lang.org/nightly/core/mem/union.MaybeUninit.html#layout-1
    ///
    /// TODO(https://github.com/google/zerocopy/issues/251): If we split
    /// `FromBytes` and `RefFromBytes`, or if we introduce a separate
    /// `NoCell`/`Freeze` trait, we can relax the trait bounds for `FromZeroes`
    /// and `FromBytes`.
    ///
    /// TODO(#251): Replace these bounds with `NoCell` once we support it.
    unsafe_impl!(T: TryFromBytes => TryFromBytes for MaybeUninit<T>);
    unsafe_impl!(T: TryFromBytes => FromZeroes for MaybeUninit<T>);
    unsafe_impl!(T: TryFromBytes => FromBytes for MaybeUninit<T>);
    unsafe_impl!(T: Unaligned => Unaligned for MaybeUninit<T>);
    assert_unaligned!(MaybeUninit<()>, MaybeUninit<u8>);
}
safety_comment! {
    /// SAFETY:
    /// `ManuallyDrop` has the same layout as `T`, and accessing the inner value
    /// is safe (meaning that it's unsound to leave the inner value
    /// uninitialized while exposing the `ManuallyDrop` to safe code). It's
    /// nearly certain that `ManuallyDrop` has the same bit validity as `T`, but
    /// this is technically not yet documented. [1]
    /// - `TryFromBytes`: `ManuallyDrop<T>` has the same layout and bit validity
    ///   as `T`, so if the provided `NonNull<ManuallyDrop<T>>` satisfies the
    ///   preconditions for `TryFromBytes::<ManuallyDrop<T>>::is_bit_valid`,
    ///   then it is sound to convert it to a `NonNull<T>`, and that pointer
    ///   satisfies the preconditions for `TryFromBytes::<T>::is_bit_valid`.
    ///   For DSTs, `ManuallyDrop<T>` and `T` have the same pointer metadata,
    ///   so pointer casting preserves length.
    ///
    ///   Since their bit validity requirements are the same,
    ///   `TryFromBytes::<T>::is_bit_valid` is a sound implementation of
    ///   `TryFromBytes::<ManuallyDrop<T>>::is_bit_valid`.
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
    /// TODO(https://github.com/rust-lang/rust/pull/115522): Update these docs
    /// once ManuallyDrop bit validity is guaranteed.
    unsafe_impl!(
        T: ?Sized TryFromBytes => TryFromBytes for ManuallyDrop<T>;
        |c: NonNull<T>| unsafe { T::is_bit_valid(c) }
    );
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
    unsafe_impl!(const N: usize, T: TryFromBytes => TryFromBytes for [T; N]; |c: NonNull<[T; N]>| {
        #[allow(unstable_name_collisions)]
        let slice = NonNull::slice_from_raw_parts(c.cast::<T>(), N);
        // SAFETY: The preconditions of `is_bit_valid` are identical for `[T;
        // N]` and for `[T]` if the passed pointer encodes a slice of `N`
        // elements. Thus, if the caller has upheld their preconditions, then we
        // uphold the preconditions for this call.
        unsafe { <[T] as TryFromBytes>::is_bit_valid(slice) }
    });
    unsafe_impl!(const N: usize, T: FromZeroes => FromZeroes for [T; N]);
    unsafe_impl!(const N: usize, T: FromBytes => FromBytes for [T; N]);
    unsafe_impl!(const N: usize, T: AsBytes => AsBytes for [T; N]);
    unsafe_impl!(const N: usize, T: Unaligned => Unaligned for [T; N]);
    assert_unaligned!([(); 0], [(); 1], [u8; 0], [u8; 1]);
    unsafe_impl!(T: TryFromBytes => TryFromBytes for [T]; |c: NonNull<[T]>| {
        let base = c.cast::<T>().as_ptr();
        // TODO(#67): Remove this allow. See NonNulSlicelExt for more details.
        #[allow(unstable_name_collisions)]
        (0..c.len()).all(|i| {
            // TODO(https://github.com/rust-lang/rust/issues/74265): Use
            // `NonNull::get_unchecked_mut`.

            // SAFETY:
            // - `i` is in bounds of `c.len()` by construction, and so the
            //   result of this addition cannot overflow past the end of the
            //   allocation referred to by `c`.
            // - It is a precondition of `is_bit_valid` that the total length
            //   encoded by `c` doesn't overflow `isize`.
            // - Since `c` must point to a valid allocation, and valid
            //   allocations cannot wrap around the address space, we know that
            //   this addition will not wrap around either.
            let elem = unsafe { base.add(i) };
            // SAFETY: `base` is constructed from a `NonNull` pointer, and the
            // addition that produces `elem` is guaranteed not to wrap
            // around/overflow, so `elem >= base > 0`.
            let elem = unsafe { NonNull::new_unchecked(elem) };

            // SAFETY: The caller promises that `c` is aligned and is valid for
            // reads. They also promise that any byte which is always
            // initialized in a valid `[T]` is initialized in `c`'s referent.
            // While the exact, formal property is slightly more complicated
            // (see the safety docs on `is_bit_valid`), what's important is
            // that, for types which are merely the concatenation of other types
            // (structs, tuples, arrays, slices), the property is also
            // compositional - if it holds for the larger type, then by
            // definition it holds for each element of the type. Thus, since the
            // caller has promised that it holds of the entire `[T]`, it must
            // also hold for each individual `T`.
            //
            // Thus, the preconditions for this call are satisfied.
            unsafe { <T as TryFromBytes>::is_bit_valid(elem) }
        })
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
/// # #[cfg(feature = "derive")] { // This example uses derives, and won't compile without them
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
/// # }
/// ```
pub struct Ref<B, T: ?Sized>(B, PhantomData<T>);

/// Deprecated: prefer [`Ref`] instead.
#[deprecated(since = "0.7.0", note = "LayoutVerified has been renamed to Ref")]
#[doc(hidden)]
pub type LayoutVerified<B, T> = Ref<B, T>;

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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline(always)]
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
/// [`split_at`]: crate::ByteSlice::split_at
// It may seem overkill to go to this length to ensure that this doc link never
// breaks. We do this because it simplifies CI - it means that generating docs
// always succeeds, so we don't need special logic to only generate docs under
// certain features.
#[cfg_attr(feature = "alloc", doc = "[`Vec<u8>`]: alloc::vec::Vec")]
#[cfg_attr(
    not(feature = "alloc"),
    doc = "[`Vec<u8>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html"
)]
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
    #[inline(always)]
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
    #[inline]
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

    // This test takes a long time when running under Miri, so we skip it in
    // that case. This is acceptable because this is a logic test that doesn't
    // attempt to expose UB.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_validate_cast() {
        fn layout(
            base_size: usize,
            align: usize,
            _trailing_slice_elem_size: Option<usize>,
        ) -> DstLayout {
            DstLayout {
                _base_layout: Layout::from_size_align(base_size, align).unwrap(),
                _trailing_slice_elem_size,
            }
        }

        /// This macro accepts arguments in the form of:
        ///
        ///           layout(_, _, _).validate_cast(_, _, _), Ok(Some((_, _)))
        ///                  |  |  |                |  |  |            |  |
        ///    base_size ----+  |  |                |  |  |            |  |
        ///    align -----------+  |                |  |  |            |  |
        ///    trailing_size ------+                |  |  |            |  |
        ///    addr --------------------------------+  |  |            |  |
        ///    bytes_len ------------------------------+  |            |  |
        ///    cast_type ---------------------------------+            |  |
        ///    elems --------------------------------------------------+  |
        ///    split_at --------------------------------------------------+
        ///
        /// Each argument can either be an iterator or a wildcard. Each
        /// wildcarded variable is implicitly replaced by an iterator over a
        /// representative sample of values for that variable. Each `test!`
        /// invocation iterates over every combination of values provided by
        /// each variable's iterator (ie, the cartesian product) and validates
        /// that the results are expected.
        ///
        /// The final argument uses the same syntax, but it has a different
        /// meaning:
        /// - If it is `Ok(pat)`, then the pattern `pat` is supplied to
        ///   `assert_matches!` to validate the computed result for each
        ///   combination of input values.
        /// - If it is `Err(msg)`, then `test!` validates that the call to
        ///   `validate_cast` panics with the given panic message.
        ///
        /// Note that the meta-variables that match these variables have the
        /// `tt` type, and some valid expressions are not valid `tt`s (such as
        /// `a..b`). In this case, wrap the expression in parentheses, and it
        /// will become valid `tt`.
        macro_rules! test {
            (
                layout($base_size:tt, $align:tt, $trailing_size:tt)
                .validate_cast($addr:tt, $bytes_len:tt, $cast_type:tt), $expect:pat $(,)?
            ) => {
                itertools::iproduct!(
                    test!(@generate_usize $base_size),
                    test!(@generate_align $align),
                    test!(@generate_opt_usize $trailing_size),
                    test!(@generate_usize $addr),
                    test!(@generate_usize $bytes_len),
                    test!(@generate_cast_type $cast_type)
                ).for_each(|(base_size, align, trailing_size, addr, bytes_len, cast_type)| {
                    let actual = std::panic::catch_unwind(|| {
                        layout(base_size, align, trailing_size).validate_cast(addr, bytes_len, cast_type)
                    }).map_err(|d| {
                        *d.downcast::<&'static str>().expect("expected string panic message").as_ref()
                    });
                    assert_matches::assert_matches!(
                        actual, $expect,
                        "layout({base_size}, {align}, {trailing_size:?}).validate_cast({addr}, {bytes_len}, {cast_type:?})",
                    );
                });
            };
            (@generate_usize _) => { 0..8 };
            (@generate_align _) => { [1, 2, 4, 8, 16] };
            (@generate_opt_usize _) => { [None].into_iter().chain((0..8).map(Some).into_iter()) };
            (@generate_cast_type _) => { [CastType::Prefix, CastType::_Suffix] };
            (@generate_cast_type $variant:ident) => { [CastType::$variant] };
            // Some expressions need to be wrapped in parentheses in order to be
            // valid `tt`s (required by the top match pattern). See the comment
            // below for more details. This arm removes these parentheses to
            // avoid generating an `unused_parens` warning.
            (@$_:ident ($vals:expr)) => { $vals };
            (@$_:ident $vals:expr) => { $vals };
        }

        const EVENS: [usize; 5] = [0, 2, 4, 6, 8];
        const NZ_EVENS: [usize; 5] = [2, 4, 6, 8, 10];
        const ODDS: [usize; 5] = [1, 3, 5, 7, 9];

        // base_size is too big for the memory region.
        test!(layout((1..8), _, ((1..8).map(Some))).validate_cast(_, [0], _), Ok(None));
        test!(layout((2..8), _, ((1..8).map(Some))).validate_cast(_, [1], _), Ok(None));

        // addr is unaligned for prefix cast
        test!(layout(_, [2], [None]).validate_cast(ODDS, _, Prefix), Ok(None));
        test!(layout(_, [2], (NZ_EVENS.map(Some))).validate_cast(ODDS, _, Prefix), Ok(None));

        // addr is aligned, but end of buffer is unaligned for suffix cast
        test!(layout(_, [2], [None]).validate_cast(EVENS, ODDS, _Suffix), Ok(None));
        test!(layout(_, [2], (NZ_EVENS.map(Some))).validate_cast(EVENS, ODDS, _Suffix), Ok(None));

        // Unfortunately, these constants cannot easily be used in the
        // implementation of `validate_cast`, since `panic!` consumes a string
        // literal, not an expression.
        //
        // It's important that these messages be in a separate module. If they
        // were at the function's top level, we'd pass them to `test!` as, e.g.,
        // `Err(TRAILING)`, which would run into a subtle Rust footgun - the
        // `TRAILING` identifier would be treated as a pattern to match rather
        // than a value to check for equality.
        mod msgs {
            pub(super) const TRAILING: &str =
                "attempted to cast to slice type with zero-sized element";
            pub(super) const OVERFLOW: &str = "`addr` + `bytes_len` > usize::MAX";
        }

        // casts with ZST trailing element types are unsupported
        test!(layout(_, _, [Some(0)]).validate_cast(_, _, _), Err(msgs::TRAILING),);

        // addr + bytes_len must not overflow usize
        test!(
            layout(_, [1], (NZ_EVENS.map(Some))).validate_cast([usize::MAX], (1..100), _),
            Err(msgs::OVERFLOW)
        );
        test!(layout(_, [1], [None]).validate_cast((1..100), [usize::MAX], _), Err(msgs::OVERFLOW));
        test!(
            layout([1], [1], [None]).validate_cast(
                [usize::MAX / 2 + 1, usize::MAX],
                [usize::MAX / 2 + 1, usize::MAX],
                _
            ),
            Err(msgs::OVERFLOW)
        );

        // Validates that `validate_cast` satisfies its own documented safety
        // postconditions, and also a few other properties that aren't
        // documented but we want to guarantee anyway.
        fn validate_behavior(
            (layout, addr, bytes_len, cast_type): (DstLayout, usize, usize, CastType),
        ) {
            if let Some((elems, split_at)) = layout.validate_cast(addr, bytes_len, cast_type) {
                let (base_size, align, trailing_elem_size) = (
                    layout._base_layout.size(),
                    layout._base_layout.align(),
                    layout._trailing_slice_elem_size,
                );

                let debug_str = format!(
                    "layout({base_size}, {align}, {trailing_elem_size:?}).validate_cast({addr}, {bytes_len}, {cast_type:?}) => ({elems}, {split_at})",
                );

                // If this is a sized type (no trailing slice), then `elems` is
                // meaningless, but in practice we set it to 0. Callers are not
                // allowed to rely on this, but a lot of math is nicer if
                // they're able to, and some callers might accidentally do that.
                assert!(!(trailing_elem_size.is_none() && elems != 0), "{}", debug_str);

                let resulting_size = base_size + (elems * trailing_elem_size.unwrap_or(0));
                // Test that, for unsized types, `validate_cast` computed the
                // largest possible value that fits in the given byte range.
                assert!(
                    trailing_elem_size
                        .map(|elem_size| resulting_size + elem_size > bytes_len)
                        .unwrap_or(true),
                    "{}",
                    debug_str
                );

                // Test safety postconditions guaranteed by `validate_cast`.
                assert!(resulting_size <= bytes_len);
                match cast_type {
                    CastType::Prefix => {
                        assert_eq!(addr % align, 0, "{}", debug_str);
                        assert_eq!(resulting_size, split_at, "{}", debug_str);
                    }
                    CastType::_Suffix => {
                        assert_eq!(split_at, bytes_len - resulting_size, "{}", debug_str);
                        assert_eq!((addr + split_at) % align, 0, "{}", debug_str);
                    }
                }
            }
        }

        let layouts = itertools::iproduct!(0..8, [1, 2, 4, 8], (1..8).map(Some).chain([None]))
            .filter(|(size, align, trailing_elem_size)| {
                size % align == 0 && trailing_elem_size.unwrap_or(*align) % align == 0
            })
            .map(|(s, a, t)| layout(s, a, t));
        itertools::iproduct!(layouts, 0..8, 0..8, [CastType::Prefix, CastType::_Suffix])
            .for_each(validate_behavior);
    }

    #[test]
    fn test_known_layout() {
        // Test that `$ty` and `ManuallyDrop<$ty>` have the expected layout.
        // Test that `PhantomData<$ty>` has the same layout as `()` regardless
        // of `$ty`.
        macro_rules! test {
            ($ty:ty, $expect:expr) => {
                let expect = $expect;
                assert_eq!(<$ty as KnownLayout>::LAYOUT, expect);
                assert_eq!(<ManuallyDrop<$ty> as KnownLayout>::LAYOUT, expect);
                assert_eq!(<PhantomData<$ty> as KnownLayout>::LAYOUT, <() as KnownLayout>::LAYOUT);
            };
        }

        let layout = |base_size, align, _trailing_slice_elem_size| DstLayout {
            _base_layout: Layout::from_size_align(base_size, align).unwrap(),
            _trailing_slice_elem_size,
        };

        test!((), layout(0, 1, None));
        test!(u8, layout(1, 1, None));
        // Use `align_of` because `u64` alignment may be smaller than 8 on some
        // platforms.
        test!(u64, layout(8, mem::align_of::<u64>(), None));
        test!(AU64, layout(8, 8, None));

        test!(Option<&'static ()>, usize::LAYOUT);

        test!([()], layout(0, 1, Some(0)));
        test!([u8], layout(0, 1, Some(1)));
        test!(str, layout(0, 1, Some(1)));
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
            fn with_failing_test_cases<F: Fn(&[u8])>(f: F);
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

            fn with_failing_test_cases<F: Fn(&[u8])>(_f: F) {}
        }

        // Implements `TryFromBytesTestable`.
        macro_rules! impl_try_from_bytes_testable {
            // Base case for recursion (when the list of types has run out).
            (=> @success $($success_case:expr),* $(, @failure $($failure_case:expr),*)?) => {};
            // Implements for type(s) with no type parameters.
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

                fn with_failing_test_cases<F: Fn(&[u8])>(_f: F) {
                    $($(
                        // `unused_qualifications` is spuriously triggered on
                        // `Option::<Self>::None`.
                        #[allow(unused_qualifications)]
                        let case = $failure_case.as_bytes();
                        _f(case.as_bytes());
                    )*)?
                }
            };
        }

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
            // TODO(#321): Add success test cases for `ManuallyDrop<[u8]>` and
            // `ManuallyDrop<[bool]>` once we have an easy way of converting
            // `[ManuallyDrop<T>] -> ManuallyDrop<[T]>`. Here are some suggested
            // test cases:
            //
            //      @success [ManuallyDrop::new(true), ManuallyDrop::new(false)][..],
            //               [ManuallyDrop::new(false), ManuallyDrop::new(true)][..],
            ManuallyDrop<[u8]> => @success;
            ManuallyDrop<[bool]>
                 => @success,
                    @failure [2u8], [3u8], [0xFFu8], [0u8, 1u8, 2u8];
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
                    let c = NonNull::from(val);
                    // SAFETY:
                    // - Since `val` is a normal reference, `c` is guranteed to
                    //   be aligned, to point to a single allocation, and to
                    //   have a size which doesn't overflow `isize`.
                    // - Since `val` is a valid `$ty`, `c`'s referent satisfies
                    //   the bit validity constraints of `is_bit_valid`, which
                    //   are a superset of the bit validity constraints of
                    //   `$ty`.
                    let res = unsafe { <$ty as TryFromBytes>::is_bit_valid(c) };
                    assert!(res, "{}::is_bit_valid({:?}): got false, expected true", stringify!($ty), val);

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
                #[allow(clippy::as_conversions)]
                <$ty as TryFromBytesTestable>::with_failing_test_cases(|c| {
                    let res = <$ty as TryFromBytes>::try_from_ref(c);
                    assert!(res.is_none(), "{}::is_bit_valid({:?}): got true, expected false", stringify!($ty), c);
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

        // Implements none of the ZC traits.
        struct NotZerocopy;

        assert_impls!(PhantomData<NotZerocopy>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(PhantomData<[u8]>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);

        assert_impls!(ManuallyDrop<u8>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(ManuallyDrop<[u8]>: TryFromBytes, FromZeroes, FromBytes, AsBytes, Unaligned);
        assert_impls!(ManuallyDrop<bool>: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);
        assert_impls!(ManuallyDrop<[bool]>: TryFromBytes, FromZeroes, AsBytes, Unaligned, !FromBytes);
        assert_impls!(ManuallyDrop<NotZerocopy>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
        assert_impls!(ManuallyDrop<[NotZerocopy]>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

        assert_impls!(MaybeUninit<u8>: TryFromBytes, FromZeroes, FromBytes, Unaligned, !AsBytes);
        assert_impls!(MaybeUninit<bool>: TryFromBytes, FromZeroes, FromBytes, Unaligned, !AsBytes);
        assert_impls!(MaybeUninit<MaybeUninit<u8>>: TryFromBytes, FromZeroes, FromBytes, Unaligned, !AsBytes);
        assert_impls!(MaybeUninit<MaybeUninit<bool>>: TryFromBytes, FromZeroes, FromBytes, Unaligned, !AsBytes);
        assert_impls!(MaybeUninit<NotZerocopy>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
        assert_impls!(MaybeUninit<MaybeUninit<NotZerocopy>>: !TryFromBytes, !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

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
