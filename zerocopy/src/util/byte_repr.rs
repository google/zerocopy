// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{
    cell::{Cell, UnsafeCell},
    mem::ManuallyDrop,
    num::Wrapping,
};

use crate::{
    pointer::{cast::CastExact, SizeEq},
    wrappers::ReadOnly,
};

/// Proof that two types have equivalent representations under a particular
/// exact referent mapping.
///
/// `ByteReprEq<R>` chooses a [`CastExact`] from `ReadOnly<Self>` to
/// `ReadOnly<R>`. For dynamically-sized types, that cast defines which `R`
/// pointer metadata corresponds to each `Self` pointer metadata value.
///
/// # Safety
///
/// For every possible `ReadOnly<Self>` referent, let `src` denote that
/// referent, and let `dst` denote the `ReadOnly<R>` referent produced by
/// [`Self::Cast`]. For every possible state of their common byte range, `src`
/// must satisfy [`Safe`] validity for `Self` if and only if `dst` satisfies
/// `Safe` validity for `R`.
///
/// This requirement applies only to referents related by `Self::Cast`. It makes
/// no claim about other `Self` and `R` metadata values which happen to produce
/// the same referent size.
///
/// [`Safe`]: crate::pointer::invariant::Safe
pub(crate) unsafe trait ByteReprEq<R: ?Sized> {
    type Cast: CastExact<ReadOnly<Self>, ReadOnly<R>>;
}

// SAFETY: `Wrapping<T>` is `#[repr(transparent)]` with one public field of type
// `T` [1][2], and the standard library guarantees that it has the same layout
// and ABI as `T` [1]. Thus the exact cast selected below maps the unique
// `Wrapping<T>` referent shape to the same bytes as `T`, and the wrapper adds no
// representation validity requirement beyond that of its `T` field. `Safe`
// validity is therefore equivalent on the two corresponding referents.
//
// [1] Per https://doc.rust-lang.org/1.85.0/core/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
//
// [2] Definition from https://doc.rust-lang.org/1.85.0/core/num/struct.Wrapping.html:
//
//   `pub struct Wrapping<T>(pub T);`
unsafe impl<T> ByteReprEq<T> for Wrapping<T> {
    type Cast = <ReadOnly<T> as SizeEq<ReadOnly<Wrapping<T>>>>::CastFrom;
}

// SAFETY: The standard library guarantees that `ManuallyDrop<T>` has the same
// layout and bit validity as `T`, and is subject to the same layout
// optimizations [1]. Therefore, for every `T: ?Sized`, the exact cast selected
// below maps each `ManuallyDrop<T>` referent to a `T` referent over the same
// bytes with equivalent `Safe` validity.
//
// [1] Per https://doc.rust-lang.org/1.85.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`, and is subject to the same layout optimizations as `T`.
unsafe impl<T: ?Sized> ByteReprEq<T> for ManuallyDrop<T> {
    type Cast = <ReadOnly<T> as SizeEq<ReadOnly<ManuallyDrop<T>>>>::CastFrom;
}

// SAFETY: The standard library guarantees that `Cell<T>` has the same in-memory
// representation as `T` [1]. Therefore, for every `T: ?Sized`, the exact cast
// selected below maps each `Cell<T>` referent to a `T` referent over the same
// bytes with equivalent `Safe` validity.
//
// [1] Per https://doc.rust-lang.org/1.85.0/std/cell/struct.Cell.html#memory-layout:
//
//   `Cell<T>` has the same memory layout and caveats as `UnsafeCell<T>`. In
//   particular, this means that `Cell<T>` has the same in-memory representation
//   as its inner type `T`.
unsafe impl<T: ?Sized> ByteReprEq<T> for Cell<T> {
    type Cast = <ReadOnly<T> as SizeEq<ReadOnly<Cell<T>>>>::CastFrom;
}

// SAFETY: The standard library guarantees that `UnsafeCell<T>` has the same
// in-memory representation as `T` [1]. Therefore, for every `T: ?Sized`, the
// exact cast selected below maps each `UnsafeCell<T>` referent to a `T` referent
// over the same bytes with equivalent `Safe` validity.
//
// [1] Per https://doc.rust-lang.org/1.85.0/std/cell/struct.UnsafeCell.html#memory-layout:
//
//   `UnsafeCell<T>` has the same in-memory representation as its inner type
//   `T`. A consequence of this guarantee is that it is possible to convert
//   between `T` and `UnsafeCell<T>`.
unsafe impl<T: ?Sized> ByteReprEq<T> for UnsafeCell<T> {
    type Cast = <ReadOnly<T> as SizeEq<ReadOnly<UnsafeCell<T>>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "8"))]
// SAFETY: `AtomicBool` and `bool` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicBool` has the
// same size and bit validity as `bool` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicBool.html
unsafe impl ByteReprEq<bool> for core::sync::atomic::AtomicBool {
    type Cast = <ReadOnly<bool> as SizeEq<ReadOnly<core::sync::atomic::AtomicBool>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "8"))]
// SAFETY: `AtomicI8` and `i8` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicI8` has the
// same size and bit validity as `i8` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI8.html
unsafe impl ByteReprEq<i8> for core::sync::atomic::AtomicI8 {
    type Cast = <ReadOnly<i8> as SizeEq<ReadOnly<core::sync::atomic::AtomicI8>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "8"))]
// SAFETY: `AtomicU8` and `u8` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicU8` has the
// same size and bit validity as `u8` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU8.html
unsafe impl ByteReprEq<u8> for core::sync::atomic::AtomicU8 {
    type Cast = <ReadOnly<u8> as SizeEq<ReadOnly<core::sync::atomic::AtomicU8>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "16"))]
// SAFETY: `AtomicI16` and `i16` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicI16` has the
// same size and bit validity as `i16` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI16.html
unsafe impl ByteReprEq<i16> for core::sync::atomic::AtomicI16 {
    type Cast = <ReadOnly<i16> as SizeEq<ReadOnly<core::sync::atomic::AtomicI16>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "16"))]
// SAFETY: `AtomicU16` and `u16` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicU16` has the
// same size and bit validity as `u16` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU16.html
unsafe impl ByteReprEq<u16> for core::sync::atomic::AtomicU16 {
    type Cast = <ReadOnly<u16> as SizeEq<ReadOnly<core::sync::atomic::AtomicU16>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "32"))]
// SAFETY: `AtomicI32` and `i32` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicI32` has the
// same size and bit validity as `i32` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI32.html
unsafe impl ByteReprEq<i32> for core::sync::atomic::AtomicI32 {
    type Cast = <ReadOnly<i32> as SizeEq<ReadOnly<core::sync::atomic::AtomicI32>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "32"))]
// SAFETY: `AtomicU32` and `u32` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicU32` has the
// same size and bit validity as `u32` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU32.html
unsafe impl ByteReprEq<u32> for core::sync::atomic::AtomicU32 {
    type Cast = <ReadOnly<u32> as SizeEq<ReadOnly<core::sync::atomic::AtomicU32>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "64"))]
// SAFETY: `AtomicI64` and `i64` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicI64` has the
// same size and bit validity as `i64` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI64.html
unsafe impl ByteReprEq<i64> for core::sync::atomic::AtomicI64 {
    type Cast = <ReadOnly<i64> as SizeEq<ReadOnly<core::sync::atomic::AtomicI64>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "64"))]
// SAFETY: `AtomicU64` and `u64` are both `Sized`, so they have no nontrivial
// pointer metadata. The standard library guarantees that `AtomicU64` has the
// same size and bit validity as `u64` [1]. The exact cast selected below
// therefore relates their unique referent shapes with equivalent `Safe`
// validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU64.html
unsafe impl ByteReprEq<u64> for core::sync::atomic::AtomicU64 {
    type Cast = <ReadOnly<u64> as SizeEq<ReadOnly<core::sync::atomic::AtomicU64>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "ptr"))]
// SAFETY: `AtomicIsize` and `isize` are both `Sized`, so they have no
// nontrivial pointer metadata. The standard library guarantees that
// `AtomicIsize` has the same size and bit validity as `isize` [1]. The exact
// cast selected below therefore relates their unique referent shapes with
// equivalent `Safe` validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicIsize.html
unsafe impl ByteReprEq<isize> for core::sync::atomic::AtomicIsize {
    type Cast = <ReadOnly<isize> as SizeEq<ReadOnly<core::sync::atomic::AtomicIsize>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "ptr"))]
// SAFETY: `AtomicUsize` and `usize` are both `Sized`, so they have no
// nontrivial pointer metadata. The standard library guarantees that
// `AtomicUsize` has the same size and bit validity as `usize` [1]. The exact
// cast selected below therefore relates their unique referent shapes with
// equivalent `Safe` validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicUsize.html
unsafe impl ByteReprEq<usize> for core::sync::atomic::AtomicUsize {
    type Cast = <ReadOnly<usize> as SizeEq<ReadOnly<core::sync::atomic::AtomicUsize>>>::CastFrom;
}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "ptr"))]
// SAFETY: `AtomicPtr<T>` and `*mut T` are both `Sized`, so they have no
// nontrivial pointer metadata. The standard library guarantees that
// `AtomicPtr<T>` has the same size and bit validity as `*mut T` [1]. The exact
// cast selected below therefore relates their unique referent shapes with
// equivalent `Safe` validity.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicPtr.html
unsafe impl<T> ByteReprEq<*mut T> for core::sync::atomic::AtomicPtr<T> {
    type Cast = <ReadOnly<*mut T> as SizeEq<ReadOnly<core::sync::atomic::AtomicPtr<T>>>>::CastFrom;
}

// Keep the legacy comparison implementation live for lint purposes; this is a
// zero-effect invocation of an assertion-only arm before the replacement macro
// below shadows it.
const _: () = {
    impl_for_transmute_from!(@assert_is_supported_trait FromZeros);
};

/// Implements one of the supported byte traits for `$ty` by transferring the
/// corresponding implementation on `$repr` through `ByteReprEq`.
///
/// Calling this macro is safe; the generated impl requires the representation
/// witness and the source trait implementation as ordinary type bounds.
macro_rules! impl_for_transmute_from {
    (
        $(#[$attr:meta])*
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?)?
        => $trait:ident for $ty:ty [$repr:ty]
    ) => {
        const _: () = {
            $(#[$attr])*
            #[allow(non_local_definitions)]

            // SAFETY: Fix an arbitrary concrete referent shape of `$ty`.
            // `$ty: ByteReprEq<$repr>` supplies an exact cast to one particular
            // `$repr` referent shape over the same bytes and guarantees that
            // `Safe` validity is equivalent on those two corresponding
            // referents. `$repr: $trait` supplies the property being
            // transferred. `@assert_is_supported_trait` rejects every trait
            // except the four cases below:
            //
            // - `FromZeros`: the all-zero representation is `Safe` for the
            //   corresponding `$repr`; representation equivalence makes the
            //   same bytes `Safe` for `$ty`.
            // - `FromBytes`: every fully initialized representation is `Safe`
            //   for the corresponding `$repr`; representation equivalence makes
            //   every such representation `Safe` for `$ty`.
            // - `IntoBytes`: every `Safe` `$ty` representation is also `Safe`
            //   for its corresponding `$repr`. `$repr: IntoBytes` therefore
            //   guarantees that every byte in the common exact referent range
            //   is initialized.
            // - `TryFromBytes`: the generated `is_safe` implementation below
            //   uses the witness's exact cast to validate the corresponding
            //   `$repr` referent. On success, representation equivalence makes
            //   the original `$ty` referent `Safe`.
            unsafe impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?)?> $trait for $ty
            where
                $ty: $crate::util::byte_repr::ByteReprEq<$repr>,
                $repr: $trait,
            {
                #[allow(dead_code, clippy::missing_inline_in_public_items)]
                #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
                fn only_derive_is_allowed_to_implement_this_trait() {
                    impl_for_transmute_from!(@assert_is_supported_trait $trait);
                }

                impl_for_transmute_from!(
                    @is_safe
                    $(<$tyvar $(: $(? $optbound +)* $($bound +)*)?>)?
                    $trait for $ty [$repr]
                );
            }
        };
    };
    (@assert_is_supported_trait TryFromBytes) => {};
    (@assert_is_supported_trait FromZeros) => {};
    (@assert_is_supported_trait FromBytes) => {};
    (@assert_is_supported_trait IntoBytes) => {};
    (
        @is_safe
        $(<$tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?>)?
        TryFromBytes for $ty:ty [$repr:ty]
    ) => {
        #[inline(always)]
        fn is_safe<Alignment>(candidate: $crate::Maybe<'_, Self, Alignment>) -> bool
        where
            Alignment: $crate::invariant::Alignment,
        {
            // The transmute below changes only the referent type while keeping
            // validity `Initialized`. That validity has type-independent
            // semantics; `BecauseImmutable` is applicable because both
            // `ReadOnly<Self>` and `ReadOnly<$repr>` are immutable. The cast is
            // exactly the metadata-aware correspondence chosen by
            // `ByteReprEq`.
            let candidate = candidate.transmute_with::<
                $crate::wrappers::ReadOnly<$repr>,
                $crate::pointer::invariant::Initialized,
                <Self as $crate::util::byte_repr::ByteReprEq<$repr>>::Cast,
                $crate::pointer::BecauseImmutable,
            >();

            // SAFETY: If the delegated validator returns `true`, the mapped
            // referent is `Safe` for `$repr`. `ByteReprEq` guarantees that
            // `Safe` validity is equivalent between this mapped `$repr`
            // referent and the original `Self` referent. Returning the delegated
            // result therefore satisfies `TryFromBytes::is_safe`'s contract.
            <$repr as TryFromBytes>::is_safe(candidate)
        }
    };
    (
        @is_safe
        $(<$tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?>)?
        $trait:ident for $ty:ty [$repr:ty]
    ) => {
        // Trait other than `TryFromBytes`; no `is_safe` impl.
    };
}
