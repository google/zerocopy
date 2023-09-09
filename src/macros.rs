// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

/// Documents multiple unsafe blocks with a single safety comment.
///
/// Invoked as:
///
/// ```rust,ignore
/// safety_comment! {
///     // Non-doc comments come first.
///     /// SAFETY:
///     /// Safety comment starts on its own line.
///     macro_1!(args);
///     macro_2! { args };
///     /// SAFETY:
///     /// Subsequent safety comments are allowed but not required.
///     macro_3! { args };
/// }
/// ```
///
/// The macro invocations are emitted, each decorated with the following
/// attribute: `#[allow(clippy::undocumented_unsafe_blocks)]`.
macro_rules! safety_comment {
    (#[doc = r" SAFETY:"] $($(#[doc = $_doc:literal])* $macro:ident!$args:tt;)*) => {
        #[allow(clippy::undocumented_unsafe_blocks)]
        const _: () = { $($macro!$args;)* };
    }
}

/// Unsafely implements trait(s) for a type.
///
/// # Safety
///
/// The trait impl must be sound.
///
/// When implementing `TryFromBytes`:
/// - If no `is_bit_valid` impl is provided, then it must be valid for
///   `is_bit_valid` to unconditionally return `true`. In other words, it must
///   be the case that any initialized sequence of bytes constitutes a valid
///   instance of `$ty`.
/// - If an `is_bit_valid` impl is provided, then:
///   - If the provided closure takes a `NonNull<$repr>` argument, then given a
///     `NonNull<$ty>` which satisfies the preconditions of
///     `TryFromBytes::<$ty>::is_bit_valid`, it must be guaranteed that a
///     `NonNull<$repr>` with the same address, provenance, and pointer metadata
///     satisfies the preconditions of `TryFromBytes::<$repr>::is_bit_valid`.
///   - If the provided closure takes a `&$repr` argument, then given a
///     `NonNull<$ty>` which satisfies the preconditions of
///     `TryFromBytes::<$ty>::is_bit_valid`, it must be sound to convert it to a
///     `$repr` pointer with the same address, provenance, and pointer metadata,
///     and to subsequently dereference that pointer as a `&$repr`.
///   - The impl of `is_bit_valid` must only return `true` for its argument
///     `NonNull<$repr>` if the original `NonNull<$ty>` refers to a valid `$ty`.
macro_rules! unsafe_impl {
    // Implement `$trait` for `$ty` with no bounds.
    ($ty:ty: $trait:ident $(; |$candidate:ident: &$repr:ty| $is_bit_valid:expr)?) => {
        unsafe impl $trait for $ty {
            unsafe_impl!(@method $trait $(; |$candidate: &$repr| $is_bit_valid)?);
        }
    };
    // Implement all `$traits` for `$ty` with no bounds.
    ($ty:ty: $($traits:ident),*) => {
        $( unsafe_impl!($ty: $traits); )*
    };
    // This arm is identical to the following one, except it contains a
    // preceding `const`. If we attempt to handle these with a single arm, there
    // is an inherent ambiguity between `const` (the keyword) and `const` (the
    // ident match for `$tyvar:ident`).
    //
    // To explain how this works, consider the following invocation:
    //
    //   unsafe_impl!(const N: usize, T: ?Sized + Copy => Clone for Foo<T>);
    //
    // In this invocation, here are the assignments to meta-variables:
    //
    //   |---------------|------------|
    //   | Meta-variable | Assignment |
    //   |---------------|------------|
    //   | $constname    |  N         |
    //   | $constty      |  usize     |
    //   | $tyvar        |  T         |
    //   | $optbound     |  Sized     |
    //   | $bound        |  Copy      |
    //   | $trait        |  Clone     |
    //   | $ty           |  Foo<T>    |
    //   |---------------|------------|
    //
    // The following arm has the same behavior with the exception of the lack of
    // support for a leading `const` parameter.
    (
        const $constname:ident : $constty:ident $(,)?
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty $(; |$candidate:ident $(: &$ref_repr:ty)? $(: NonNull<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe_impl!(
            @inner
            @const $constname: $constty,
            $($tyvar $(: $(? $optbound +)* + $($bound +)*)?,)*
            => $trait for $ty $(; |$candidate $(: &$ref_repr)? $(: NonNull<$ptr_repr>)?| $is_bit_valid)?
        );
    };
    (
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty $(; |$candidate:ident $(: &$ref_repr:ty)? $(: NonNull<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe_impl!(
            @inner
            $($tyvar $(: $(? $optbound +)* + $($bound +)*)?,)*
            => $trait for $ty $(; |$candidate $(: &$ref_repr)? $(: NonNull<$ptr_repr>)?| $is_bit_valid)?
        );
    };
    (
        @inner
        $(@const $constname:ident : $constty:ident,)*
        $($tyvar:ident $(: $(? $optbound:ident +)* + $($bound:ident +)* )?,)*
        => $trait:ident for $ty:ty $(; |$candidate:ident $(: &$ref_repr:ty)? $(: NonNull<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe impl<$(const $constname: $constty,)* $($tyvar $(: $(? $optbound +)* $($bound +)*)?),*> $trait for $ty {
            unsafe_impl!(@method $trait $(; |$candidate: $(&$ref_repr)? $(NonNull<$ptr_repr>)?| $is_bit_valid)?);
        }
    };

    (@method TryFromBytes ; |$candidate:ident: &$repr:ty| $is_bit_valid:expr) => {
        #[inline]
        unsafe fn is_bit_valid(candidate: NonNull<Self>) -> bool {
            // SAFETY: The caller has promised that it is sound to perform this
            // pointer cast and dereference.
            #[allow(clippy::as_conversions)]
            let $candidate = unsafe { &*(candidate.as_ptr() as *const $repr) };
            $is_bit_valid
        }

        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}
    };
    (@method TryFromBytes ; |$candidate:ident: NonNull<$repr:ty>| $is_bit_valid:expr) => {
        #[inline]
        unsafe fn is_bit_valid(candidate: NonNull<Self>) -> bool {
            // SAFETY: `candidate` is a non-null pointer. The caller has
            // promised that it is sound to invoke their `$is_bit_valid` with
            // this pointer.
            #[allow(clippy::as_conversions)]
            let $candidate = unsafe { NonNull::new_unchecked(candidate.as_ptr() as *mut $repr) };
            $is_bit_valid
        }

        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}
    };
    (@method TryFromBytes) => {
        #[inline(always)] unsafe fn is_bit_valid(_: NonNull<Self>) -> bool { true }
        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}
    };
    (@method $trait:ident) => {
        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}
    };
    (@method $trait:ident; |$_candidate:ident $(: &$_ref_repr:ty)? $(: NonNull<$_ptr_repr:ty>)?| $_is_bit_valid:expr) => {
        compile_error!("Can't provide `is_bit_valid` impl for trait other than `TryFromBytes`");
    };
}

/// Implements trait(s) for a type or verifies the given implementation by
/// referencing an existing (derived) implementation.
///
/// This macro exists so that we can provide zerocopy-derive as an optional
/// dependency and still get the benefit of using its derives to validate that
/// our trait impls are sound.
///
/// When compiling without `--cfg 'feature = "derive"` and without `--cfg test`,
/// `impl_or_verify!` emits the provided trait impl. When compiling with either
/// of those cfgs, it is expected that the type in question is deriving the
/// traits instead. In this case, `impl_or_verify!` emits code which validates
/// that the given trait impl is at least as restrictive as the the impl emitted
/// by the custom derive. This has the effect of confirming that the impl which
/// is emitted when the `derive` feature is disabled is actually sound (on the
/// assumption that the impl emitted by the custom derive is sound).
///
/// The caller is still required to provide a safety comment (e.g. using the
/// `safety_comment!` macro) . The reason for this restriction is that, while
/// `impl_or_verify!` can guarantee that the provided impl is sound when it is
/// compiled with the appropriate cfgs, there is no way to guarantee that it is
/// ever compiled with those cfgs. In particular, it would be possible to
/// accidentally place an `impl_or_verify!` call in a context that is only ever
/// compiled when the `derive` feature is disabled. If that were to happen,
/// there would be nothing to prevent an unsound trait impl from being emitted.
/// Requiring a safety comment reduces the likelihood of emitting an unsound
/// impl in this case, and also provides useful documentation for readers of the
/// code.
///
/// ## Example
///
/// ```rust,ignore
/// // Note that these derives are gated by `feature = "derive"`
/// #[cfg_attr(any(feature = "derive", test), derive(FromZeroes, FromBytes, AsBytes, Unaligned))]
/// #[repr(transparent)]
/// struct Wrapper<T>(T);
///
/// safety_comment! {
///     /// SAFETY:
///     /// `Wrapper<T>` is `repr(transparent)`, so it is sound to implement any
///     /// zerocopy trait if `T` implements that trait.
///     impl_or_verify!(T: FromZeroes => FromZeroes for Wrapper<T>);
///     impl_or_verify!(T: FromBytes => FromBytes for Wrapper<T>);
///     impl_or_verify!(T: AsBytes => AsBytes for Wrapper<T>);
///     impl_or_verify!(T: Unaligned => Unaligned for Wrapper<T>);
/// }
/// ```
macro_rules! impl_or_verify {
    // The following two match arms follow the same pattern as their
    // counterparts in `unsafe_impl!`; see the documentation on those arms for
    // more details.
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
        => $trait:ident for $ty:ty
    ) => {
        impl_or_verify!(@impl { unsafe_impl!(
            $($tyvar $(: $(? $optbound +)* $($bound +)*)?),* => $trait for $ty
        ); });
        impl_or_verify!(@verify $trait, {
            impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?),*> Subtrait for $ty {}
        });
    };
    (
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty
    ) => {
        unsafe_impl!(
            @inner
            $($tyvar $(: $(? $optbound +)* + $($bound +)*)?,)*
            => $trait for $ty
        );
    };
    (@impl $impl_block:tt) => {
        #[cfg(not(any(feature = "derive", test)))]
        const _: () = { $impl_block };
    };
    (@verify $trait:ident, $impl_block:tt) => {
        #[cfg(any(feature = "derive", test))]
        const _: () = {
            trait Subtrait: $trait {}
            $impl_block
        };
    };
}

/// Implements `KnownLayout` for a sized type.
macro_rules! impl_known_layout {
    ($(const $constvar:ident : $constty:ty, $tyvar:ident $(: ?$optbound:ident)? => $ty:ty),* $(,)?) => {
        $(impl_known_layout!(@inner const $constvar: $constty, $tyvar $(: ?$optbound)? => $ty);)*
    };
    ($($($tyvar:ident $(: ?$optbound:ident)?),* => $ty:ty),* $(,)?) => {
        $(impl_known_layout!(@inner , $($tyvar $(: ?$optbound)?),* => $ty);)*
    };
    ($($ty:ty),*) => { $(impl_known_layout!(@inner , => $ty);)* };
    (@inner $(const $constvar:ident : $constty:ty)? , $($tyvar:ident $(: ?$optbound:ident)?),* => $ty:ty) => {
        const _: () = {
            use core::ptr::NonNull;

            impl<$(const $constvar : $constty,)? $($tyvar $(: ?$optbound)?),*> sealed::KnownLayoutSealed for $ty {}
            // SAFETY: Delegates safety to `DstLayout::for_type`.
            unsafe impl<$(const $constvar : $constty,)? $($tyvar $(: ?$optbound)?),*> KnownLayout for $ty {
                const LAYOUT: DstLayout = DstLayout::for_type::<$ty>();

                // SAFETY: `.cast` preserves address and provenance.
                #[inline(always)]
                fn raw_from_ptr_len(bytes: NonNull<u8>, _elems: usize) -> NonNull<Self> {
                    bytes.cast::<Self>()
                }
            }
        };
    };
}

/// Implements `KnownLayout` for a type in terms of the implementation of
/// another type with the same representation.
///
/// # Safety
///
/// - `$ty` and `$repr` must have the same:
///   - Fixed prefix size
///   - Alignment
///   - (For DSTs) trailing slice element size
/// - It must be valid to perform an `as` cast from `*mut $repr` to `*mut $ty`,
///   and this operation must preserve referent size (ie, `size_of_val_raw`).
macro_rules! unsafe_impl_known_layout {
    ($($tyvar:ident: ?Sized + KnownLayout =>)? #[repr($repr:ty)] $ty:ty) => {
        const _: () = {
            use core::ptr::NonNull;

            impl<$($tyvar: ?Sized + KnownLayout)?> sealed::KnownLayoutSealed for $ty {}
            unsafe impl<$($tyvar: ?Sized + KnownLayout)?> KnownLayout for $ty {
                const LAYOUT: DstLayout = <$repr as KnownLayout>::LAYOUT;

                // SAFETY: All operations preserve address and provenance. Caller
                // has promised that the `as` cast preserves size.
                #[inline(always)]
                #[allow(unused_qualifications)] // for `core::ptr::NonNull`
                fn raw_from_ptr_len(bytes: NonNull<u8>, elems: usize) -> NonNull<Self> {
                    #[allow(clippy::as_conversions)]
                    let ptr = <$repr>::raw_from_ptr_len(bytes, elems).as_ptr() as *mut Self;
                    // SAFETY: `ptr` was converted from `bytes`, which is non-null.
                    unsafe { NonNull::new_unchecked(ptr) }
                }
            }
        };
    };
}

/// Uses `align_of` to confirm that a type or set of types have alignment 1.
///
/// Note that `align_of<T>` requires `T: Sized`, so this macro doesn't work for
/// unsized types.
macro_rules! assert_unaligned {
    ($ty:ty) => {
        // We only compile this assertion under `cfg(test)` to avoid taking an
        // extra non-dev dependency (and making this crate more expensive to
        // compile for our dependents).
        #[cfg(test)]
        static_assertions::const_assert_eq!(core::mem::align_of::<$ty>(), 1);
    };
    ($($ty:ty),*) => {
        $(assert_unaligned!($ty);)*
    };
}
