// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

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
    (#[doc = r" SAFETY:"] $($(#[$attr:meta])* $macro:ident!$args:tt;)*) => {
        #[allow(clippy::undocumented_unsafe_blocks, unused_attributes)]
        const _: () = { $($(#[$attr])* $macro!$args;)* };
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
///   - Regardless of whether the provided closure takes a `Ptr<$repr>` or
///     `&$repr` argument, if `$ty` and `$repr` are different types, then it
///     must be the case that, given `t: *mut $ty` and `let r = t as *mut
///     $repr`:
///     - `r` refers to an object of equal or lesser size than the object
///       referred to by `t`.
///     - `r` refers to an object with `UnsafeCell`s at the same byte ranges as
///       the object referred to by `t`.
///   - If the provided closure takes a `&$repr` argument, then given a `Ptr<'a,
///     $ty>` which satisfies the preconditions of
///     `TryFromBytes::<$ty>::is_bit_valid`, it must be guaranteed that the
///     memory referenced by that `Ptr` always contains a valid `$repr`.
///   - The impl of `is_bit_valid` must only return `true` for its argument
///     `Ptr<$repr>` if the original `Ptr<$ty>` refers to a valid `$ty`.
macro_rules! unsafe_impl {
    // Implement `$trait` for `$ty` with no bounds.
    ($(#[$attr:meta])* $ty:ty: $trait:ident $(; |$candidate:ident: MaybeAligned<$repr:ty>| $is_bit_valid:expr)?) => {
        $(#[$attr])*
        unsafe impl $trait for $ty {
            unsafe_impl!(@method $trait $(; |$candidate: MaybeAligned<$repr>| $is_bit_valid)?);
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
        $(#[$attr:meta])*
        const $constname:ident : $constty:ident $(,)?
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe_impl!(
            @inner
            $(#[$attr])*
            @const $constname: $constty,
            $($tyvar $(: $(? $optbound +)* + $($bound +)*)?,)*
            => $trait for $ty $(; |$candidate $(: MaybeAligned<$ref_repr>)? $(: Maybe<$ptr_repr>)?| $is_bit_valid)?
        );
    };
    (
        $(#[$attr:meta])*
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),*
        => $trait:ident for $ty:ty $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe_impl!(
            @inner
            $(#[$attr])*
            $($tyvar $(: $(? $optbound +)* + $($bound +)*)?,)*
            => $trait for $ty $(; |$candidate $(: MaybeAligned<$ref_repr>)? $(: Maybe<$ptr_repr>)?| $is_bit_valid)?
        );
    };
    (
        @inner
        $(#[$attr:meta])*
        $(@const $constname:ident : $constty:ident,)*
        $($tyvar:ident $(: $(? $optbound:ident +)* + $($bound:ident +)* )?,)*
        => $trait:ident for $ty:ty $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        $(#[$attr])*
        #[allow(non_local_definitions)]
        unsafe impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?),* $(, const $constname: $constty,)*> $trait for $ty {
            unsafe_impl!(@method $trait $(; |$candidate: $(MaybeAligned<$ref_repr>)? $(Maybe<$ptr_repr>)?| $is_bit_valid)?);
        }
    };

    (@method TryFromBytes ; |$candidate:ident: MaybeAligned<$repr:ty>| $is_bit_valid:expr) => {
        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}

        #[inline]
        fn is_bit_valid<AA: invariant::at_least::Shared>(candidate: Maybe<'_, Self, AA>) -> bool {
            // SAFETY:
            // - The argument to `cast_unsized` is `|p| p as *mut _` as required
            //   by that method's safety precondition.
            // - The caller has promised that the cast results in an object of
            //   equal or lesser size.
            // - The caller has promised that the destination type has
            //   `UnsafeCell`s at the same byte ranges as the source type.
            #[allow(clippy::as_conversions)]
            let candidate = unsafe { candidate.cast_unsized::<$repr, _>(|p| p as *mut _) };

            // SAFETY: The caller has promised that the referenced memory region
            // will contain a valid `$repr`.
            let $candidate = unsafe { candidate.assume_validity::<crate::pointer::invariant::Valid>() };
            $is_bit_valid
        }
    };
    (@method TryFromBytes ; |$candidate:ident: Maybe<$repr:ty>| $is_bit_valid:expr) => {
        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}

        #[inline]
        fn is_bit_valid<AA: invariant::at_least::Shared>(candidate: Maybe<'_, Self, AA>) -> bool {
            // SAFETY:
            // - The argument to `cast_unsized` is `|p| p as *mut _` as required
            //   by that method's safety precondition.
            // - The caller has promised that the cast results in an object of
            //   equal or lesser size.
            // - The caller has promised that the destination type has
            //   `UnsafeCell`s at the same byte ranges as the source type.
            #[allow(clippy::as_conversions)]
            let $candidate = unsafe { candidate.cast_unsized::<$repr, _>(|p| p as *mut _) };

            // Restore the invariant that the referent bytes are initialized.
            // SAFETY: The above cast does not uninitialize any referent bytes;
            // they remain initialized.
            let $candidate = unsafe { $candidate.assume_validity::<crate::pointer::invariant::Initialized>() };

            $is_bit_valid
        }
    };
    (@method TryFromBytes) => {
        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}
        #[inline(always)] fn is_bit_valid<A: invariant::at_least::Shared>(_: Maybe<'_, Self, A>) -> bool { true }
    };
    (@method $trait:ident) => {
        #[allow(clippy::missing_inline_in_public_items)]
        fn only_derive_is_allowed_to_implement_this_trait() {}
    };
    (@method $trait:ident; |$_candidate:ident $(: &$_ref_repr:ty)? $(: NonNull<$_ptr_repr:ty>)?| $_is_bit_valid:expr) => {
        compile_error!("Can't provide `is_bit_valid` impl for trait other than `TryFromBytes`");
    };
}

/// Implements a trait for a type, bounding on each memeber of the power set of
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
        $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe_impl_for_power_set!(
            $($rest),* $(-> $ret)? => $trait for $macro!(...)
            $(; |$candidate $(: MaybeAligned<$ref_repr>)? $(: Maybe<$ptr_repr>)?| $is_bit_valid)?
        );
        unsafe_impl_for_power_set!(
            @impl $first $(, $rest)* $(-> $ret)? => $trait for $macro!(...)
            $(; |$candidate $(: MaybeAligned<$ref_repr>)? $(: Maybe<$ptr_repr>)?| $is_bit_valid)?
        );
    };
    (
        $(-> $ret:ident)? => $trait:ident for $macro:ident!(...)
        $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe_impl_for_power_set!(
            @impl $(-> $ret)? => $trait for $macro!(...)
            $(; |$candidate $(: MaybeAligned<$ref_repr>)? $(: Maybe<$ptr_repr>)?| $is_bit_valid)?
        );
    };
    (
        @impl $($vars:ident),* $(-> $ret:ident)? => $trait:ident for $macro:ident!(...)
        $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        unsafe_impl!(
            $($vars,)* $($ret)? => $trait for $macro!($($vars),* $(-> $ret)?)
            $(; |$candidate $(: MaybeAligned<$ref_repr>)? $(: Maybe<$ptr_repr>)?| $is_bit_valid)?
        );
    };
}

/// Expands to an `Option<extern "C" fn>` type with the given argument types and
/// return type. Designed for use with `unsafe_impl_for_power_set`.
macro_rules! opt_extern_c_fn {
    ($($args:ident),* -> $ret:ident) => { Option<extern "C" fn($($args),*) -> $ret> };
}

/// Expands to a `Option<fn>` type with the given argument types and return
/// type. Designed for use with `unsafe_impl_for_power_set`.
macro_rules! opt_fn {
    ($($args:ident),* -> $ret:ident) => { Option<fn($($args),*) -> $ret> };
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
/// Finally, if a `TryFromBytes::is_bit_valid` impl is provided, it must adhere
/// to the safety preconditions of [`unsafe_impl!`].
///
/// ## Example
///
/// ```rust,ignore
/// // Note that these derives are gated by `feature = "derive"`
/// #[cfg_attr(any(feature = "derive", test), derive(FromZeros, FromBytes, IntoBytes, Unaligned))]
/// #[repr(transparent)]
/// struct Wrapper<T>(T);
///
/// safety_comment! {
///     /// SAFETY:
///     /// `Wrapper<T>` is `repr(transparent)`, so it is sound to implement any
///     /// zerocopy trait if `T` implements that trait.
///     impl_or_verify!(T: FromZeros => FromZeros for Wrapper<T>);
///     impl_or_verify!(T: FromBytes => FromBytes for Wrapper<T>);
///     impl_or_verify!(T: IntoBytes => IntoBytes for Wrapper<T>);
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
        => $trait:ident for $ty:ty $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        impl_or_verify!(@impl { unsafe_impl!(
            $($tyvar $(: $(? $optbound +)* $($bound +)*)?),* => $trait for $ty
            $(; |$candidate $(: MaybeAligned<$ref_repr>)? $(: Maybe<$ptr_repr>)?| $is_bit_valid)?
        ); });
        impl_or_verify!(@verify $trait, {
            impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?),*> Subtrait for $ty {}
        });
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
    ($($tyvar:ident $(: ?$optbound:ident)? => $ty:ty),* $(,)?) => {
        $(impl_known_layout!(@inner , $tyvar $(: ?$optbound)? => $ty);)*
    };
    ($($ty:ty),*) => { $(impl_known_layout!(@inner , => $ty);)* };
    (@inner $(const $constvar:ident : $constty:ty)? , $($tyvar:ident $(: ?$optbound:ident)?)? => $ty:ty) => {
        const _: () = {
            use core::ptr::NonNull;

            // SAFETY: Delegates safety to `DstLayout::for_type`.
            unsafe impl<$($tyvar $(: ?$optbound)?)? $(, const $constvar : $constty)?> KnownLayout for $ty {
                #[allow(clippy::missing_inline_in_public_items)]
                fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}

                #[allow(unused_qualifications)]
                const LAYOUT: crate::DstLayout = crate::DstLayout::for_type::<$ty>();

                // SAFETY: `.cast` preserves address and provenance.
                //
                // TODO(#429): Add documentation to `.cast` that promises that
                // it preserves provenance.
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

            #[allow(non_local_definitions)]
            unsafe impl<$($tyvar: ?Sized + KnownLayout)?> KnownLayout for $ty {
                #[allow(clippy::missing_inline_in_public_items)]
                fn only_derive_is_allowed_to_implement_this_trait() {}

                const LAYOUT: DstLayout = <$repr as KnownLayout>::LAYOUT;

                // SAFETY: All operations preserve address and provenance.
                // Caller has promised that the `as` cast preserves size.
                //
                // TODO(#429): Add documentation to `NonNull::new_unchecked`
                // that it preserves provenance.
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

/// Emits a function definition as either `const fn` or `fn` depending on
/// whether the current toolchain version supports `const fn` with generic trait
/// bounds.
macro_rules! maybe_const_trait_bounded_fn {
    // This case handles both `self` methods (where `self` is by value) and
    // non-method functions. Each `$args` may optionally be followed by `:
    // $arg_tys:ty`, which can be omitted for `self`.
    ($(#[$attr:meta])* $vis:vis const fn $name:ident($($args:ident $(: $arg_tys:ty)?),* $(,)?) $(-> $ret_ty:ty)? $body:block) => {
        #[cfg(zerocopy_generic_bounds_in_const_fn)]
        $(#[$attr])* $vis const fn $name($($args $(: $arg_tys)?),*) $(-> $ret_ty)? $body

        #[cfg(not(zerocopy_generic_bounds_in_const_fn))]
        $(#[$attr])* $vis fn $name($($args $(: $arg_tys)?),*) $(-> $ret_ty)? $body
    };
}

/// Either panic (if the current Rust toolchain supports panicking in `const
/// fn`) or evaluate a constant that will cause an array indexing error whose
/// error message will include the format string.
///
/// The type that this expression evaluates to must be `Copy`, or else the
/// non-panicking desugaring will fail to compile.
macro_rules! const_panic {
    ($fmt:literal) => {{
        #[cfg(zerocopy_panic_in_const)]
        panic!($fmt);
        #[cfg(not(zerocopy_panic_in_const))]
        const_panic!(@non_panic $fmt)
    }};
    (@non_panic $fmt:expr) => {{
        // This will type check to whatever type is expected based on the call
        // site.
        let panic: [_; 0] = [];
        // This will always fail (since we're indexing into an array of size 0.
        #[allow(unconditional_panic)]
        panic[0]
    }}
}

/// Either assert (if the current Rust toolchain supports panicking in `const
/// fn`) or evaluate the expression and, if it evaluates to `false`, call
/// `const_panic!`.
macro_rules! const_assert {
    ($e:expr) => {{
        #[cfg(zerocopy_panic_in_const)]
        assert!($e);
        #[cfg(not(zerocopy_panic_in_const))]
        {
            let e = $e;
            if !e {
                let _: () = const_panic!(@non_panic concat!("assertion failed: ", stringify!($e)));
            }
        }
    }}
}

/// Like `const_assert!`, but relative to `debug_assert!`.
macro_rules! const_debug_assert {
    ($e:expr $(, $msg:expr)?) => {{
        #[cfg(zerocopy_panic_in_const)]
        debug_assert!($e $(, $msg)?);
        #[cfg(not(zerocopy_panic_in_const))]
        {
            // Use this (rather than `#[cfg(debug_assertions)]`) to ensure that
            // `$e` is always compiled even if it will never be evaluated at
            // runtime.
            if cfg!(debug_assertions) {
                let e = $e;
                if !e {
                    let _: () = const_panic!(@non_panic concat!("assertion failed: ", stringify!($e) $(, ": ", $msg)?));
                }
            }
        }
    }}
}

/// Either invoke `unreachable!()` or `loop {}` depending on whether the Rust
/// toolchain supports panicking in `const fn`.
macro_rules! const_unreachable {
    () => {{
        #[cfg(zerocopy_panic_in_const)]
        unreachable!();

        #[cfg(not(zerocopy_panic_in_const))]
        loop {}
    }};
}
