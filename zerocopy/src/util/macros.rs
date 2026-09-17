// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

/// Unsafely implements trait(s) for a type.
///
/// # Safety
///
/// The trait impl must be sound.
///
/// When implementing `TryFromBytes`:
/// - If no `is_safe` impl is provided, then it must be valid for `is_safe` to
///   unconditionally return `true`. In other words, it must be the case that any
///   initialized sequence of bytes constitutes a valid instance of `$ty`.
/// - If an `is_safe` impl is provided, then the impl of `is_safe` must only
///   return `true` if its argument refers to a valid `$ty`.
macro_rules! unsafe_impl {
    ($(#[$attr:meta])* $ty:ty: $trait:ident $(; |$candidate:ident| $is_safe:expr)?) => {{
        crate::util::macros::__unsafe();

        $(#[$attr])*
        // SAFETY: The caller promises that this is sound.
        unsafe impl $trait for $ty {
            unsafe_impl!(@method $trait $(; |$candidate| $is_safe)?);
        }
    }};

    ($(#[$attrs:meta])* $ty:ty: $($traits:ident),*) => {
        unsafe_impl!(@impl_traits_with_packed_attrs { $(#[$attrs])* } $ty: $($traits),*)
    };

    (@impl_traits_with_packed_attrs $attrs:tt $ty:ty: $($traits:ident),*) => {{
        $( unsafe_impl!(@unpack_attrs $attrs $ty: $traits); )*
    }};

    (@unpack_attrs { $(#[$attrs:meta])* } $ty:ty: $traits:ident) => {
        unsafe_impl!($(#[$attrs])* $ty: $traits);
    };

    (
        $(#[$attr:meta])*
        const $constname:ident : $constty:ident $(,)?
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty $(; |$candidate:ident| $is_safe:expr)?
    ) => {
        unsafe_impl!(
            @inner
            $(#[$attr])*
            @const $constname: $constty,
            $($tyvar $(: $(? $optbound +)* + $($bound +)*)?,)*
            => $trait for $ty $(; |$candidate| $is_safe)?
        );
    };
    (
        $(#[$attr:meta])*
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty $(; |$candidate:ident| $is_safe:expr)?
    ) => {{
        unsafe_impl!(
            @inner
            $(#[$attr])*
            $($tyvar $(: $(? $optbound +)* + $($bound +)*)?,)*
            => $trait for $ty $(; |$candidate| $is_safe)?
        );
    }};
    (
        @inner
        $(#[$attr:meta])*
        $(@const $constname:ident : $constty:ident,)*
        $($tyvar:ident $(: $(? $optbound:ident +)* + $($bound:ident +)* )?,)*
        => $trait:ident for $ty:ty $(; |$candidate:ident| $is_safe:expr)?
    ) => {{
        crate::util::macros::__unsafe();

        $(#[$attr])*
        #[allow(non_local_definitions)]
        // SAFETY: The caller promises that this is sound.
        unsafe impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?),* $(, const $constname: $constty,)*> $trait for $ty {
            unsafe_impl!(@method $trait $(; |$candidate| $is_safe)?);
        }
    }};

    (@method TryFromBytes ; |$candidate:ident| $is_safe:expr) => {
        #[allow(clippy::missing_inline_in_public_items, dead_code)]
        #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
        fn only_derive_is_allowed_to_implement_this_trait() {}

        #[inline]
        fn is_safe<Alignment>($candidate: Maybe<'_, Self, Alignment>) -> bool
        where
            Alignment: crate::invariant::Alignment,
        {
            $is_safe
        }
    };
    (@method TryFromBytes) => {
        #[allow(clippy::missing_inline_in_public_items)]
        #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
        fn only_derive_is_allowed_to_implement_this_trait() {}
        #[inline(always)]
        fn is_safe<Alignment>(_candidate: Maybe<'_, Self, Alignment>) -> bool
        where
            Alignment: crate::invariant::Alignment,
        {
            true
        }
    };
    (@method $trait:ident) => {
        #[allow(clippy::missing_inline_in_public_items, dead_code)]
        #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
        fn only_derive_is_allowed_to_implement_this_trait() {}
    };
    (@method $trait:ident; |$_candidate:ident| $_is_safe:expr) => {
        compile_error!("Can't provide `is_safe` impl for trait other than `TryFromBytes`");
    };
}

/// Proof that two types have exactly the same valid referent sizes.
///
/// A byte length `n` is a valid referent size for `T` if a `T` referent may
/// occupy exactly `n` bytes.
///
/// # Safety
///
/// For every byte length `n`, `n` must be a valid referent size for `Self` if
/// and only if it is a valid referent size for `R`.
///
/// If both types are `Sized`, this reduces to
/// `size_of::<Self>() == size_of::<R>()`.
pub(crate) unsafe trait SameSizeForTransmute<R: ?Sized> {}

// SAFETY: Per [1], `Wrapping<T>` has the same layout and ABI as `T`. Both types
// are `Sized`, so this implies `size_of::<Wrapping<T>>() == size_of::<T>()`.
// Thus their valid referent-size sets are equal.
//
// [1] Per https://doc.rust-lang.org/1.85.0/core/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`.
unsafe impl<T> SameSizeForTransmute<T> for core::num::Wrapping<T> {}

// SAFETY: Per [1], `ManuallyDrop<T>` has the same layout as `T`. Thus any
// referent size admitted by one type is admitted by the other, including when
// `T` is dynamically sized, so their valid referent-size sets are equal.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`.
unsafe impl<T: ?Sized> SameSizeForTransmute<T> for core::mem::ManuallyDrop<T> {}

// SAFETY: Per [1], `Cell<T>` has the same in-memory representation as `T`.
// Therefore the two types admit exactly the same referent byte lengths,
// including when `T` is dynamically sized.
//
// [1] Per https://doc.rust-lang.org/1.85.0/std/cell/struct.Cell.html#memory-layout:
//
//   `Cell<T>` has the same memory layout and caveats as `UnsafeCell<T>`. In
//   particular, this means that `Cell<T>` has the same in-memory representation
//   as its inner type `T`.
unsafe impl<T: ?Sized> SameSizeForTransmute<T> for core::cell::Cell<T> {}

// SAFETY: Per [1], `UnsafeCell<T>` has the same in-memory representation as
// `T`. Therefore the two types admit exactly the same referent byte lengths,
// including when `T` is dynamically sized.
//
// [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
//
//   `UnsafeCell<T>` has the same in-memory representation as its inner type
//   `T`.
unsafe impl<T: ?Sized> SameSizeForTransmute<T> for core::cell::UnsafeCell<T> {}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "8"))]
// SAFETY: `AtomicBool` and `bool` are both `Sized`. Per [1], `AtomicBool` has
// the same size as `bool`, so their singleton valid referent-size sets are
// equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicBool.html
unsafe impl SameSizeForTransmute<bool> for core::sync::atomic::AtomicBool {}
#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "8"))]
// SAFETY: `AtomicI8` and `i8` are both `Sized`. Per [1], `AtomicI8` has the same
// size as `i8`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI8.html
unsafe impl SameSizeForTransmute<i8> for core::sync::atomic::AtomicI8 {}
#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "8"))]
// SAFETY: `AtomicU8` and `u8` are both `Sized`. Per [1], `AtomicU8` has the same
// size as `u8`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU8.html
unsafe impl SameSizeForTransmute<u8> for core::sync::atomic::AtomicU8 {}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "16"))]
// SAFETY: `AtomicI16` and `i16` are both `Sized`. Per [1], `AtomicI16` has the
// same size as `i16`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI16.html
unsafe impl SameSizeForTransmute<i16> for core::sync::atomic::AtomicI16 {}
#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "16"))]
// SAFETY: `AtomicU16` and `u16` are both `Sized`. Per [1], `AtomicU16` has the
// same size as `u16`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU16.html
unsafe impl SameSizeForTransmute<u16> for core::sync::atomic::AtomicU16 {}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "32"))]
// SAFETY: `AtomicI32` and `i32` are both `Sized`. Per [1], `AtomicI32` has the
// same size as `i32`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI32.html
unsafe impl SameSizeForTransmute<i32> for core::sync::atomic::AtomicI32 {}
#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "32"))]
// SAFETY: `AtomicU32` and `u32` are both `Sized`. Per [1], `AtomicU32` has the
// same size as `u32`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU32.html
unsafe impl SameSizeForTransmute<u32> for core::sync::atomic::AtomicU32 {}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "64"))]
// SAFETY: `AtomicI64` and `i64` are both `Sized`. Per [1], `AtomicI64` has the
// same size as `i64`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI64.html
unsafe impl SameSizeForTransmute<i64> for core::sync::atomic::AtomicI64 {}
#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "64"))]
// SAFETY: `AtomicU64` and `u64` are both `Sized`. Per [1], `AtomicU64` has the
// same size as `u64`, so their singleton valid referent-size sets are equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU64.html
unsafe impl SameSizeForTransmute<u64> for core::sync::atomic::AtomicU64 {}

#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "ptr"))]
// SAFETY: `AtomicIsize` and `isize` are both `Sized`. Per [1], `AtomicIsize`
// has the same size as `isize`, so their singleton valid referent-size sets are
// equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicIsize.html
unsafe impl SameSizeForTransmute<isize> for core::sync::atomic::AtomicIsize {}
#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "ptr"))]
// SAFETY: `AtomicUsize` and `usize` are both `Sized`. Per [1], `AtomicUsize`
// has the same size as `usize`, so their singleton valid referent-size sets are
// equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicUsize.html
unsafe impl SameSizeForTransmute<usize> for core::sync::atomic::AtomicUsize {}
#[cfg(all(not(no_zerocopy_target_has_atomics_1_60_0), target_has_atomic = "ptr"))]
// SAFETY: `AtomicPtr<T>` and `*mut T` are both `Sized`. Per [1], `AtomicPtr<T>`
// has the same size as `*mut T`, so their singleton valid referent-size sets are
// equal.
//
// [1] https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicPtr.html
unsafe impl<T> SameSizeForTransmute<*mut T> for core::sync::atomic::AtomicPtr<T> {}

/// Implements `$trait` for `$ty` where `$ty: TransmuteFrom<$repr>` (and
/// vice-versa).
///
/// Calling this macro is safe; the bounds it emits establish the premises used
/// by the generated trait impl.
macro_rules! impl_for_transmute_from {
    (
        $(#[$attr:meta])*
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?)?
        => $trait:ident for $ty:ty [$repr:ty]
    ) => {
        const _: () = {
            $(#[$attr])*
            #[allow(non_local_definitions)]

            // SAFETY: The generated `unsafe impl $trait for $ty` has four
            // compile-time premises, checked by `is_trait::<$ty, $repr>()`:
            //
            // - `$ty: SameSizeForTransmute<$repr>` proves that `$ty` and
            //   `$repr` have exactly the same valid referent sizes.
            // - `$ty: TransmuteFrom<$repr, Safe, Safe>` proves
            //   `Safe($repr) ⊆ Safe($ty)` whenever their referents have equal
            //   size.
            // - `$repr: TransmuteFrom<$ty, Safe, Safe>` proves the reverse
            //   inclusion on the same equal-size domain.
            // - `$repr: $trait` supplies the trait property being transferred.
            //
            // The first premise means that every valid size of either type is
            // also valid for the other, so the two `TransmuteFrom` implications
            // apply at every size relevant to either type. The supported traits
            // are then discharged as follows:
            //
            // - `FromZeros`: for every valid `$ty` size, the all-zero `$repr`
            //   state is `Safe`; forward inclusion makes those same bytes
            //   `Safe` for `$ty`.
            // - `FromBytes`: for every valid `$ty` size, every initialized
            //   `$repr` state is `Safe`; forward inclusion makes every such
            //   state `Safe` for `$ty`.
            // - `IntoBytes`: every `Safe` `$ty` state has a size valid for
            //   `$repr`; reverse inclusion makes the same bytes `Safe` for
            //   `$repr`, and `$repr: IntoBytes` establishes that all of those
            //   bytes are initialized.
            // - `TryFromBytes`: the generated validator below delegates to
            //   `$repr`; a successful `$repr` validity check combined with
            //   forward inclusion establishes validity for `$ty`.
            unsafe impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?)?> $trait for $ty {
                #[allow(dead_code, clippy::missing_inline_in_public_items)]
                #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
                fn only_derive_is_allowed_to_implement_this_trait() {
                    use crate::pointer::{*, invariant::Safe};

                    impl_for_transmute_from!(@assert_is_supported_trait $trait);

                    fn is_trait<T, R>()
                    where
                        T: crate::util::macros::SameSizeForTransmute<R>
                            + TransmuteFrom<R, Safe, Safe>
                            + ?Sized,
                        R: TransmuteFrom<T, Safe, Safe> + $trait + ?Sized,
                    {
                    }

                    #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
                    fn f<$($tyvar $(: $(? $optbound +)* $($bound +)*)?)?>() {
                        is_trait::<$ty, $repr>();
                    }
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
            // SAFETY: `candidate` has a valid `Self` referent size. By
            // `SameSizeForTransmute<$repr>`, that byte length is also a valid
            // `$repr` referent size. If the delegated `$repr` validator returns
            // `true`, its contract establishes that these bytes are `Safe` for
            // `$repr`; `Self: TransmuteFrom<$repr, Safe, Safe>` then establishes
            // that the same equal-length byte state is `Safe` for `Self`.
            // Returning the delegated result therefore satisfies
            // `TryFromBytes::is_safe`'s postcondition.
            <$repr as TryFromBytes>::is_safe(candidate.transmute::<_, _, BecauseImmutable>())
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

/// Implements a trait for a type, bounding on each member of the power set of
/// a set of type variables. This is useful for implementing traits for tuples
/// or `fn` types.
///
/// The last argument is the name of a macro which will be called in every
/// `impl` block, and is expected to expand to the name of the type for which to
/// implement the trait.
///
/// For example, the invocation:
/// ```ignore
/// unsafe_impl_for_power_set!(A, B => Foo for type!(...))
/// ```
/// ...expands to:
/// ```ignore
/// unsafe impl       Foo for type!()     { ... }
/// unsafe impl<B>    Foo for type!(B)    { ... }
/// unsafe impl<A, B> Foo for type!(A, B) { ... }
/// ```
macro_rules! unsafe_impl_for_power_set {
    (
        $first:ident $(, $rest:ident)* $(-> $ret:ident)? => $trait:ident for $macro:ident!(...)
        $(; |$candidate:ident| $is_safe:expr)?
    ) => {
        unsafe_impl_for_power_set!(
            $($rest),* $(-> $ret)? => $trait for $macro!(...)
            $(; |$candidate| $is_safe)?
        );
        unsafe_impl_for_power_set!(
            @impl $first $(, $rest)* $(-> $ret)? => $trait for $macro!(...)
            $(; |$candidate| $is_safe)?
        );
    };
    (
        $(-> $ret:ident)? => $trait:ident for $macro:ident!(...)
        $(; |$candidate:ident| $is_safe:expr)?
    ) => {
        unsafe_impl_for_power_set!(
            @impl $(-> $ret)? => $trait for $macro!(...)
            $(; |$candidate| $is_safe)?
        );
    };
    (
        @impl $($vars:ident),* $(-> $ret:ident)? => $trait:ident for $macro:ident!(...)
        $(; |$candidate:ident| $is_safe:expr)?
    ) => {
        unsafe_impl!(
            $($vars,)* $($ret)? => $trait for $macro!($($vars),* $(-> $ret)?)
            $(; |$candidate| $is_safe)?
        );
    };
}

/// Expands to an `Option<extern "C" fn>` type with the given argument types and
/// return type. Designed for use with `unsafe_impl_for_power_set`.
macro_rules! opt_extern_c_fn {
    ($($args:ident),* -> $ret:ident) => { Option<extern "C" fn($($args),*) -> $ret> };
}

/// Expands to an `Option<unsafe extern "C" fn>` type with the given argument
/// types and return type. Designed for use with `unsafe_impl_for_power_set`.
macro_rules! opt_unsafe_extern_c_fn {
    ($($args:ident),* -> $ret:ident) => { Option<unsafe extern "C" fn($($args),*) -> $ret> };
}

/// Expands to an `Option<fn>` type with the given argument types and return
/// type. Designed for use with `unsafe_impl_for_power_set`.
macro_rules! opt_fn {
    ($($args:ident),* -> $ret:ident) => { Option<fn($($args),*) -> $ret> };
}

/// Expands to an `Option<unsafe fn>` type with the given argument types and
/// return type. Designed for use with `unsafe_impl_for_power_set`.
macro_rules! opt_unsafe_fn {
    ($($args:ident),* -> $ret:ident) => { Option<unsafe fn($($args),*) -> $ret> };
}

#[allow(rustdoc::private_intra_doc_links)]
/// Implements trait(s) for a type or verifies the given implementation by
/// referencing an existing (derived) implementation.
///
/// This macro exists so that we can provide zerocopy-derive as an optional
/// dependency and still get the benefit of using its derives to validate that
/// our trait impls are sound.
#[cfg_attr(__ZEROCOPY_INTERNAL_USE_ONLY_DEV_MODE, macro_export)]
#[doc(hidden)]
macro_rules! impl_or_verify {
    (
        const $constname:ident : $constty:ident $(,)?
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty
    ) => {
        impl_or_verify!(@impl { unsafe_impl!(
            const $constname: $constty, $($tyvar $(: $(? $optbound +)* $($bound +)*)?),* => $trait for $ty
        ); });
        impl_or_verify!(@verify $trait, {
            impl<const $constname: $constty, $($tyvar $(: $(? $optbound +)* $($bound +)*)?),*> Subtrait for $ty {}
        });
    };
    (
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty $(; |$candidate:ident| $is_safe:expr)?
    ) => {
        impl_or_verify!(@impl { unsafe_impl!(
            $($tyvar $(: $(? $optbound +)* $($bound +)*)?),* => $trait for $ty
            $(; |$candidate| $is_safe)?
        ); });
        impl_or_verify!(@verify $trait, {
            impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?),*> Subtrait for $ty {}
        });
    };
    (@impl $impl_block:tt) => {
        #[cfg(not(any(feature = "derive", test)))]
        { $impl_block };
    };
    (@verify $trait:ident, $impl_block:tt) => {
        #[cfg(any(feature = "derive", test))]
        {
            #[allow(dead_code)]
            trait Subtrait: $trait {}
            $impl_block
        };
    };
}

macro_rules! impl_known_layout {
    ($(const $constvar:ident : $constty:ty, $tyvar:ident $(: ?$optbound:ident)? => $ty:ty),* $(,)?) => {
        $(impl_known_layout!(@inner const $constvar: $constty, $tyvar $(: ?$optbound)? => $ty);)*
    };
    ($($tyvar:ident $(: ?$optbound:ident)? => $ty:ty),* $(,)?) => {
        $(impl_known_layout!(@inner , $tyvar $(: ?$optbound)? => $ty);)*
    };
    ($($(#[$attrs:meta])* $ty:ty),*) => { $(impl_known_layout!(@inner , => $(#[$attrs])* $ty);)* };
    (@inner $(const $constvar:ident : $constty:ty)? , $($tyvar:ident $(: ?$optbound:ident)?)? => $(#[$attrs:meta])* $ty:ty) => {
        const _: () = {
            use core::ptr::NonNull;

            #[allow(non_local_definitions)]
            $(#[$attrs])*
            unsafe impl<$($tyvar $(: ?$optbound)?)? $(, const $constvar : $constty)?> KnownLayout for $ty {
                #[allow(clippy::missing_inline_in_public_items)]
                #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
                fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}

                type PointerMetadata = ();
                type MaybeUninit = core::mem::MaybeUninit<Self>;
                const LAYOUT: crate::DstLayout = crate::DstLayout::for_type::<$ty>();

                #[inline(always)]
                fn raw_from_ptr_len(bytes: NonNull<u8>, _meta: ()) -> NonNull<Self> {
                    bytes.cast::<Self>()
                }

                #[inline(always)]
                fn pointer_to_metadata(_ptr: *mut Self) -> () {}
            }
        };
    };
}

macro_rules! unsafe_impl_known_layout {
    ($($tyvar:ident: ?Sized + KnownLayout =>)? #[repr($repr:ty)] $ty:ty) => {{
        use core::ptr::NonNull;

        crate::util::macros::__unsafe();

        #[allow(non_local_definitions)]
        unsafe impl<$($tyvar: ?Sized + KnownLayout)?> KnownLayout for $ty {
            #[allow(dead_code, clippy::missing_inline_in_public_items)]
            #[cfg_attr(all(coverage_nightly, __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS), coverage(off))]
            fn only_derive_is_allowed_to_implement_this_trait() {}

            type PointerMetadata = <$repr as KnownLayout>::PointerMetadata;
            type MaybeUninit = <$repr as KnownLayout>::MaybeUninit;
            const LAYOUT: DstLayout = <$repr as KnownLayout>::LAYOUT;

            #[inline(always)]
            fn raw_from_ptr_len(bytes: NonNull<u8>, meta: <$repr as KnownLayout>::PointerMetadata) -> NonNull<Self> {
                #[allow(clippy::as_conversions)]
                let ptr = <$repr>::raw_from_ptr_len(bytes, meta).as_ptr() as *mut Self;
                unsafe { NonNull::new_unchecked(ptr) }
            }

            #[inline(always)]
            fn pointer_to_metadata(ptr: *mut Self) -> Self::PointerMetadata {
                #[allow(clippy::as_conversions)]
                let ptr = ptr as *mut $repr;
                <$repr>::pointer_to_metadata(ptr)
            }
        }
    }};
}

macro_rules! assert_unaligned {
    ($($tys:ty),*) => {
        $(
            #[cfg(test)]
            static_assertions::const_assert_eq!(core::mem::align_of::<$tys>(), 1);
        )*
    };
}

macro_rules! maybe_const_trait_bounded_fn {
    ($(#[$attr:meta])* $vis:vis const fn $name:ident($($args:ident $(: $arg_tys:ty)?),* $(,)?) $(-> $ret_ty:ty)? $body:block) => {
        #[cfg(not(no_zerocopy_generic_bounds_in_const_fn_1_61_0))]
        $(#[$attr])* $vis const fn $name($($args $(: $arg_tys)?),*) $(-> $ret_ty)? $body

        #[cfg(no_zerocopy_generic_bounds_in_const_fn_1_61_0)]
        $(#[$attr])* $vis fn $name($($args $(: $arg_tys)?),*) $(-> $ret_ty)? $body
    };
}

macro_rules! const_panic {
    (@non_panic $($_arg:tt)+) => {{
        let panic: [_; 0] = [];
        #[allow(unconditional_panic)]
        panic[0]
    }};
    ($($arg:tt)+) => {{
        #[cfg(not(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0))]
        panic!($($arg)+);
        #[cfg(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0)]
        const_panic!(@non_panic $($arg)+)
    }};
}

macro_rules! const_assert {
    ($e:expr) => {{
        #[cfg(not(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0))]
        assert!($e);
        #[cfg(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0)]
        {
            let e = $e;
            if !e {
                let _: () = const_panic!(@non_panic concat!("assertion failed: ", stringify!($e)));
            }
        }
    }};
    ($e:expr, $($args:tt)+) => {{
        #[cfg(not(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0))]
        assert!($e, $($args)+);
        #[cfg(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0)]
        {
            let e = $e;
            if !e {
                let _: () = const_panic!(@non_panic concat!("assertion failed: ", stringify!($e), ": ", stringify!($arg)), $($args)*);
            }
        }
    }};
}

macro_rules! const_debug_assert {
    ($e:expr $(, $msg:expr)?) => {{
        #[cfg(not(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0))]
        debug_assert!($e $(, $msg)?);
        #[cfg(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0)]
        {
            if cfg!(debug_assertions) {
                let e = $e;
                if !e {
                    let _: () = const_panic!(@non_panic concat!("assertion failed: ", stringify!($e) $(, ": ", $msg)?));
                }
            }
        }
    }}
}

macro_rules! const_unreachable {
    () => {{
        #[cfg(not(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0))]
        unreachable!();

        #[cfg(no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0)]
        loop {}
    }};
}

macro_rules! static_assert {
    (Self $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )? => $condition:expr $(, $args:tt)*) => {{
        trait StaticAssert { const ASSERT: bool; }
        impl<T $(: $(? $optbound +)* $($bound +)*)?> StaticAssert for T {
            const ASSERT: bool = { const_assert!($condition $(, $args)*); $condition };
        }
        const_assert!(<Self as StaticAssert>::ASSERT);
    }};
    ($($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),* => $condition:expr $(, $args:tt)*) => {{
        trait StaticAssert { const ASSERT: bool; }
        impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?,)*> StaticAssert for ($(core::marker::PhantomData<$tyvar>,)*) {
            const ASSERT: bool = { const_assert!($condition $(, $args)*); $condition };
        }
        const_assert!(<($(core::marker::PhantomData<$tyvar>,)*) as StaticAssert>::ASSERT);
    }};
}

macro_rules! static_assert_dst_is_not_zst {
    ($tyvar:ident) => {{
        use crate::KnownLayout;
        static_assert!($tyvar: ?Sized + KnownLayout => {
            let dst_is_zst = match $tyvar::LAYOUT.size_info {
                crate::SizeInfo::Sized { .. } => false,
                crate::SizeInfo::SliceDst(TrailingSliceLayout { elem_size, .. }) => elem_size == 0,
            };
            !dst_is_zst
        }, "cannot call this method on a dynamically-sized type whose trailing slice element is zero-sized");
    }}
}

#[macro_export]
#[doc(hidden)]
macro_rules! define_cast {
    (unsafe { $vis:vis $name:ident $(<$tyvar:ident $(: ?$optbound:ident)?>)? = $src:ty => $dst:ty }) => {
        #[allow(missing_debug_implementations, missing_copy_implementations, unreachable_pub)]
        $vis enum $name {}

        unsafe impl $(<$tyvar $(: ?$optbound)?>)? $crate::pointer::cast::Project<$src, $dst> for $name {
            fn project(src: $crate::pointer::PtrInner<'_, $src>) -> *mut $dst {
                #[allow(clippy::as_conversions)]
                return src.as_ptr() as *mut $dst;
            }
        }
        unsafe impl $(<$tyvar $(: ?$optbound)?>)? $crate::pointer::cast::Cast<$src, $dst> for $name {}
    };
}

macro_rules! unsafe_impl_for_transparent_wrapper {
    ($vis:vis T $(: ?$optbound:ident)? => $wrapper:ident<T>) => {{
        crate::util::macros::__unsafe();
        use crate::pointer::{TransmuteFrom, cast::{CastExact, TransitiveProject}, SizeEq, invariant::Safe};
        use crate::wrappers::ReadOnly;

        unsafe impl<T $(: ?$optbound)?> TransmuteFrom<T, Safe, Safe> for $wrapper<T> {}
        unsafe impl<T $(: ?$optbound)?> TransmuteFrom<$wrapper<T>, Safe, Safe> for T {}
        define_cast!(unsafe { $vis CastToWrapper<T $(: ?$optbound)? > = T => $wrapper<T> });
        unsafe impl<T $(: ?$optbound)?> CastExact<T, $wrapper<T>> for CastToWrapper {}
        define_cast!(unsafe { $vis CastFromWrapper<T $(: ?$optbound)? > = $wrapper<T> => T });
        unsafe impl<T $(: ?$optbound)?> CastExact<$wrapper<T>, T> for CastFromWrapper {}

        impl<T $(: ?$optbound)?> SizeEq<T> for $wrapper<T> { type CastFrom = CastToWrapper; }
        impl<T $(: ?$optbound)?> SizeEq<$wrapper<T>> for T { type CastFrom = CastFromWrapper; }

        impl<T $(: ?$optbound)?> SizeEq<ReadOnly<T>> for $wrapper<T> {
            type CastFrom = TransitiveProject<T, <T as SizeEq<ReadOnly<T>>>::CastFrom, CastToWrapper>;
        }
        impl<T $(: ?$optbound)?> SizeEq<$wrapper<T>> for ReadOnly<T> {
            type CastFrom = TransitiveProject<T, CastFromWrapper, <ReadOnly<T> as SizeEq<$wrapper<T>>>::CastFrom>;
        }
        impl<T $(: ?$optbound)?> SizeEq<ReadOnly<T>> for ReadOnly<$wrapper<T>> {
            type CastFrom = TransitiveProject<$wrapper<T>, <$wrapper<T> as SizeEq<ReadOnly<T>>>::CastFrom, <ReadOnly<$wrapper<T>> as SizeEq<$wrapper<T>>>::CastFrom>;
        }
        impl<T $(: ?$optbound)?> SizeEq<ReadOnly<$wrapper<T>>> for ReadOnly<T> {
            type CastFrom = TransitiveProject<$wrapper<T>, <$wrapper<T> as SizeEq<ReadOnly<$wrapper<T>>>>::CastFrom, <ReadOnly<T> as SizeEq<$wrapper<T>>>::CastFrom>;
        }
    }};
}

macro_rules! impl_transitive_transmute_from {
    ($($tyvar:ident $(: ?$optbound:ident)?)? => $t:ty => $u:ty => $v:ty) => {
        const _: () = {
            use crate::pointer::{TransmuteFrom, SizeEq, invariant::Safe};
            impl<$($tyvar $(: ?$optbound)?)?> SizeEq<$t> for $v
            where $u: SizeEq<$t>, $v: SizeEq<$u>,
            {
                type CastFrom = cast::TransitiveProject<$u, <$u as SizeEq<$t>>::CastFrom, <$v as SizeEq<$u>>::CastFrom>;
            }
            unsafe impl<$($tyvar $(: ?$optbound)?)?> TransmuteFrom<$t, Safe, Safe> for $v
            where $u: TransmuteFrom<$t, Safe, Safe>, $v: TransmuteFrom<$u, Safe, Safe>,
            {}
        };
    };
}

#[inline(always)]
pub(crate) const unsafe fn __unsafe() {}

#[allow(unused)]
macro_rules! docstring {
    ($(#[doc = $content:expr])*) => { concat!($($content, "\n",)*) }
}

#[allow(unused)]
macro_rules! codegen_header {
    ($level:expr, $name:expr) => {
        concat!("\n<", $level, " id='method.", $name, ".codegen'>\n    <a class='doc-anchor' href='#method.", $name, ".codegen'>§</a>\n    Code Generation\n</", $level, ">\n")
    };
}

#[rustfmt::skip]
#[allow(unused)]
macro_rules! tabs {
    (name = $name:expr, arity = $arity:literal, $([$($open:ident)? @index $n:literal @title $title:literal $(#[doc = $content:expr])*]),*) => {
        concat!("\n<div class='codegen-tabs' style='--arity: ", $arity ,"'>", $(concat!("\n    <details name='tab-", $name,"' style='--n: ", $n ,"'", $(stringify!($open),)*">\n        <summary><h6>", $title, "</h6></summary>\n        <div>\n\n", $($content, "\n",)* "\n\\\n        </div>\n    </details>"),)* "</div>")
    }
}

#[allow(unused)]
macro_rules! codegen_example {
    (format = $format:expr, bench = $bench:expr) => {
        tabs!(
            name = $bench,
            arity = 4,
            [@index 1 @title "Format" #[doc = include_str!(concat!("../benches/formats/", $format, ".rs"))]],
            [@index 2 @title "Benchmark" #[doc = include_str!(concat!("../benches/", $bench, ".rs"))]],
            [open @index 3 @title "Assembly" #[doc = include_str!(concat!("../benches/", $bench, ".x86-64"))]],
            [@index 4 @title "Machine Code Analysis" #[doc = include_str!(concat!("../benches/", $bench, ".x86-64.mca"))]]
        )
    }
}

#[allow(unused)]
macro_rules! codegen_example_suite {
    (bench = $bench:expr, format = $format:expr, arity = $arity:literal, $([$($open:ident)? @index $index:literal @title $title:literal @variant $variant:literal]),*) => {
        tabs!(name = $bench, arity = $arity, $([$($open)* @index $index @title $title #[doc = codegen_example!(format = concat!($format, "_", $variant), bench = concat!($bench, "_", $variant))]]),*)
    }
}

#[allow(unused)]
macro_rules! codegen_preamble {
    () => { docstring!(///
/// This abstraction is safe and cheap, but does not necessarily
/// have zero runtime cost. The codegen you experience in practice
/// will depend on optimization level, the layout of the destination
/// type, and what the compiler can prove about the source.
///
) }
}

#[allow(unused)]
#[cfg(not(doc))]
macro_rules! codegen_section {
    (header = $level:expr, bench = $bench:expr, format = $format:expr, arity = $arity:literal, $([$($open:ident)? @index $index:literal @title $title:literal @variant $variant:literal]),*) => { "" };
    (header = $level:expr, bench = $bench:expr, format = $format:expr,) => { "" };
}

#[allow(unused)]
#[cfg(doc)]
macro_rules! codegen_section {
    (header = $level:expr, bench = $bench:expr, format = $format:expr, arity = $arity:literal, $([$($open:ident)? @index $index:literal @title $title:literal @variant $variant:literal]),*) => {
        concat!(codegen_header!($level, $bench), codegen_preamble!(), docstring!(///
/// The below examples illustrate typical codegen for increasingly complex types:
///
), codegen_example_suite!(bench = $bench, format = $format, arity = $arity, $([$($open)* @index $index @title $title @variant $variant]),*))
    };
    (header = $level:expr, bench = $bench:expr, format = $format:expr,) => {
        concat!(codegen_header!($level, $bench), codegen_preamble!(), codegen_example!(format = $format, bench = $bench))
    };
}
