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
    //
    // The 2 arms under this one are there so we can apply
    // N attributes for each one of M trait implementations.
    // The simple solution of:
    //
    // ($(#[$attrs:meta])* $ty:ty: $($traits:ident),*) => {
    //     $( unsafe_impl!( $(#[$attrs])* $ty: $traits ) );*
    // }
    //
    // Won't work. The macro processor sees that the outer repetition
    // contains both $attrs and $traits and expects them to match the same
    // amount of fragments.
    //
    // To solve this we must:
    // 1. Pack the attributes into a single token tree fragment we can match over.
    // 2. Expand the traits.
    // 3. Unpack and expand the attributes.
    ($(#[$attrs:meta])* $ty:ty: $($traits:ident),*) => {
        unsafe_impl!(@impl_traits_with_packed_attrs { $(#[$attrs])* } $ty: $($traits),*)
    };

    (@impl_traits_with_packed_attrs $attrs:tt $ty:ty: $($traits:ident),*) => {
        $( unsafe_impl!(@unpack_attrs $attrs $ty: $traits); )*
    };

    (@unpack_attrs { $(#[$attrs:meta])* } $ty:ty: $traits:ident) => {
        unsafe_impl!($(#[$attrs])* $ty: $traits);
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
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn only_derive_is_allowed_to_implement_this_trait() {}

        #[inline]
        fn is_bit_valid<AA: crate::pointer::invariant::Reference>(candidate: Maybe<'_, Self, AA>) -> bool {
            // SAFETY:
            // - The cast preserves address. The caller has promised that the
            //   cast results in an object of equal or lesser size, and so the
            //   cast returns a pointer which references a subset of the bytes
            //   of `p`.
            // - The cast preserves provenance.
            // - The caller has promised that the destination type has
            //   `UnsafeCell`s at the same byte ranges as the source type.
            #[allow(clippy::as_conversions)]
            let candidate = unsafe { candidate.cast_unsized_unchecked::<$repr, _>(|p| p as *mut _) };

            let $candidate = candidate.bikeshed_recall_valid();
            $is_bit_valid
        }
    };
    (@method TryFromBytes ; |$candidate:ident: Maybe<$repr:ty>| $is_bit_valid:expr) => {
        #[allow(clippy::missing_inline_in_public_items)]
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn only_derive_is_allowed_to_implement_this_trait() {}

        #[inline]
        fn is_bit_valid<AA: crate::pointer::invariant::Reference>(candidate: Maybe<'_, Self, AA>) -> bool {
            // SAFETY:
            // - The cast preserves address. The caller has promised that the
            //   cast results in an object of equal or lesser size, and so the
            //   cast returns a pointer which references a subset of the bytes
            //   of `p`.
            // - The cast preserves provenance.
            // - The caller has promised that the destination type has
            //   `UnsafeCell`s at the same byte ranges as the source type.
            #[allow(clippy::as_conversions)]
            let $candidate = unsafe { candidate.cast_unsized_unchecked::<$repr, _>(|p| p as *mut _) };

            $is_bit_valid
        }
    };
    (@method TryFromBytes) => {
        #[allow(clippy::missing_inline_in_public_items)]
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn only_derive_is_allowed_to_implement_this_trait() {}
        #[inline(always)] fn is_bit_valid<AA: crate::pointer::invariant::Reference>(_: Maybe<'_, Self, AA>) -> bool { true }
    };
    (@method $trait:ident) => {
        #[allow(clippy::missing_inline_in_public_items)]
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn only_derive_is_allowed_to_implement_this_trait() {}
    };
    (@method $trait:ident; |$_candidate:ident $(: &$_ref_repr:ty)? $(: NonNull<$_ptr_repr:ty>)?| $_is_bit_valid:expr) => {
        compile_error!("Can't provide `is_bit_valid` impl for trait other than `TryFromBytes`");
    };
}

/// Implements `$trait` for a type which is `TransmuteFromOld<$repr>` where `$repr:
/// $trait`.
///
/// Calling this macro is safe; the internals of the macro emit appropriate
/// trait bounds which ensure that the given impl is sound.
macro_rules! impl_for_transmute_from {
    (
        $(#[$attr:meta])*
        $($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?)?
        => $trait:ident for $ty:ty[$repr:ty] $(; |$candidate:ident $(: MaybeAligned<$ref_repr:ty>)? $(: Maybe<$ptr_repr:ty>)?| $is_bit_valid:expr)?
    ) => {
        $(#[$attr])*
        #[allow(non_local_definitions)]

        // This block implements `$trait` for `$ty` under the following
        // conditions:
        // - `$ty: TransmuteFromOld<$repr>`
        // - `$repr: $trait`
        // - For some invariant `Xxx`, `$ty::Mapping: Mapping<Xxx = Preserved>`
        //   (`Xxx` is determined by the `@define_is_transmute_from` macro
        //   arms). This bound ensures that some layout property is the same
        //   between `$ty` and `$repr`. Which layout property this is depends on
        //   the trait being implemented (for example, `FromBytes` is not
        //   concerned with alignment, but is concerned with bit validity).
        //
        // In other words, `$ty` is guaranteed to soundly implement `$trait`
        // because some property of its layout is the same as `$repr`, which
        // implements `$trait`. Most of the complexity in this macro is to
        // ensure that the above-mentioned conditions are actually met, and that
        // the proper invariant (ie, the proper layout property) is chosen.

        // SAFETY:
        // - `is_transmute_from<R, T>` requires:
        //   - `R: $trait`
        //   - `T: TransmuteFromOld<R>`
        //   - `T::Mapping: Mapping<$invariant = Preserved>`
        // - `is_transmute_from<$repr, $ty>` is called in the body
        //
        // This enforces that `$repr: $trait`, `$ty: TransmuteFromOld<$repr>`, and
        // `$trait::Mapping: Mapping<$invariant = Preserved>`. `$invariant` is
        // chosen below in the `@define_is_transmute_from` macro arms, which
        // contain the full safety proofs. They use the facts in this safety
        // comment as preconditions for their proofs. The safety proof is
        // slightly different for each trait.
        unsafe impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?)?> $trait for $ty {
            #[allow(dead_code, clippy::missing_inline_in_public_items)]
            #[cfg_attr(coverage_nightly, coverage(off))]
            fn only_derive_is_allowed_to_implement_this_trait() {
                use crate::pointer::transmute::*;

                impl_for_transmute_from!(@define_is_transmute_from $trait);
                is_transmute_from::<$repr, $ty>();
            }

            impl_for_transmute_from!(
                @is_bit_valid
                $(<$tyvar $(: $(? $optbound +)* $($bound +)*)?>)?
                $trait for $ty[$repr]
            );
        }
    };
    (@define_is_transmute_from Immutable) => {
        // SAFETY: `T::Mapping: Mapping<Aliasing = Preserved>` ensures that `T`
        // and `R` have `UnsafeCell`s at the same byte offsets. If this weren't
        // the case, then it would be unsound to map `Shared` to `Shared` when
        // transmuting from `R` to `T`. `R: Immutable` implies that `R` has no
        // `UnsafeCell`s, and so `T` doesn't either. Since `T = $ty`, `$ty` can
        // soundly implement `Immutable`.
        #[cfg_attr(coverage_nightly, coverage(off))]
        const fn is_transmute_from<R, T>()
        where
            R: ?Sized + Immutable + UnsafeCellsAgree<T>,
            T: TransmuteFromOld<R> + UnsafeCellsAgree<R> +  ?Sized,
        {}
    };
    (@define_is_transmute_from FromZeros) => {
        // SAFETY: `T::Mapping: Mapping<Validity = Preserved>` requires that `T`
        // has the same bit validity as `R`. `R: FromZeros` implies that the
        // all-zeros bit pattern is a bit-valid instance of `R`, and so the
        // all-zeros bit pattern is a bit-valid instance of `T`. Since `T =
        // $ty`, `$ty` can soundly implement `FromZeros`.
        impl_for_transmute_from!(@define_is_transmute_from FromZeros, ValidityMapping)
    };
    (@define_is_transmute_from FromBytes) => {
        // SAFETY: `T::Mapping: Mapping<Validity = Preserved>` requires that `T`
        // has the same bit validity as `R`. `R: FromBytes` implies that any
        // initialized bit pattern is a bit-valid instance of `R`, and so the
        // any initialized bit pattern is a bit-valid instance of `T`. Since `T
        // = $ty`, `$ty` can soundly implement `FromBytes`.
        impl_for_transmute_from!(@define_is_transmute_from FromBytes, ValidityMapping)
    };
    (@define_is_transmute_from IntoBytes) => {
        // SAFETY: `T::Mapping: Mapping<Validity = Preserved>` requires that `T`
        // has the same bit validity as `R`. `R: IntoBytes` implies that no
        // bit-valid instance of `R` contains uninitialized bytes, and so no
        // bit-valid instance of `T` does either. Since `T = $ty`, `$ty` can
        // soundly implement `IntoBytes`.
        impl_for_transmute_from!(@define_is_transmute_from IntoBytes, ValidityMapping)
    };
    (@define_is_transmute_from Unaligned) => {
        // SAFETY: `T::Mapping: Mapping<Alignment = Preserved>` requires that
        // `T` has the same alignment as `R`. `R: Unaligned` implies that
        // `align_of::<R>() == 1`, and so `align_of::<T>() == 1`. Since `T =
        // $ty`, `$ty` can soundly implement `Unaligned`.
        impl_for_transmute_from!(@define_is_transmute_from Unaligned, AlignmentMapping)
    };
    (@define_is_transmute_from TryFromBytes) => {
        // SAFETY: `T::Mapping: Mapping<Validity = Preserved>` requires that `T`
        // has the same bit validity as `R`. `R: TryFromBytes` implies that `<R
        // as TryFromBytes>::is_bit_valid(c)` only returns `true` if `c`
        // references a bit-valid instance of `R`. Thus, `<R as
        // TryFromBytes>::is_bit_valid(c)` only returns `true` if `c` references
        // a bit-valid instance of `T`. Below, we implement `<T as
        // TryFromBytes>::is_bit_valid` by deferring to `<R as
        // TryFromBytes>::is_bit_valid`. Since `T = $ty`, it is sound for `$ty`
        // to implement `TryFromBytes` with this `is_bit_valid` implementation.
        impl_for_transmute_from!(@define_is_transmute_from TryFromBytes, ValidityMapping)
    };
    (@define_is_transmute_from $trait:ident, $invariant:ident) => {
        #[cfg_attr(coverage_nightly, coverage(off))]
        const fn is_transmute_from<R, T>()
        where
            R: ?Sized + $trait,
            T: TransmuteFromOld<R, $invariant = crate::pointer::invariant::Preserved> +  ?Sized,
        {}
    };
    (
        @is_bit_valid
        $(<$tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?>)?
        TryFromBytes for $ty:ty[$repr:ty]
    ) => {
        // SAFETY: See safety comment in `(@define_is_transmute_from
        // TryFromBytes)` macro arm for an explanation of why this is a sound
        // implementation of `is_bit_valid`.
        #[inline]
        fn is_bit_valid<A: crate::pointer::invariant::Reference>(candidate: Maybe<'_, Self, A>) -> bool {
            <$repr as TryFromBytes>::is_bit_valid(candidate.transmute_old::<$repr, _>())
        }
    };
    (
        @is_bit_valid
        $(<$tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?>)?
        $trait:ident for $ty:ty[$repr:ty]
    ) => {
        // Trait other than `TryFromBytes`; no `is_bit_valid` impl.
    };
}

/// Implements `TransmuteFromOld<UnsafeCell<$native>>` for an atomic type and
/// vice-versa.
///
/// # Safety
///
/// The caller promises that `$atomic` is an atomic type whose natie equivalent
/// is `$native`.
#[cfg(any(
    target_has_atomic = "8",
    target_has_atomic = "16",
    target_has_atomic = "32",
    target_has_atomic = "64",
    target_has_atomic = "ptr"
))]
macro_rules! unsafe_impl_transmute_from_for_atomic {
    ($(#[$attr:meta])* $(,)?) => {};
    ($(#[$attr:meta])* $atomic:ty [$native:ty], $($atomics:ty [$natives:ty]),* $(,)?) => {
        $(#[$attr])*
        // SAFETY: See safety comment in next match arm.
        unsafe impl crate::pointer::transmute::TransmuteFromOld<UnsafeCell<$native>> for $atomic {
            // SAFETY: See safety comment in next match arm.
            unsafe_impl_transmute_from_for_atomic!(@inner UnsafeCell<$native> => $atomic | Unknown);
        }
        // SAFETY: See safety comment in next match arm.
        unsafe impl crate::pointer::transmute::TransmuteFromOld<$atomic> for UnsafeCell<$native> {
            // SAFETY: See safety comment in next match arm.
            unsafe_impl_transmute_from_for_atomic!(@inner $atomic => UnsafeCell<$native> | Preserved);
        }

        // SAFETY: See safety comment in next match arm.
        unsafe impl crate::pointer::transmute::UnsafeCellsAgree<$atomic> for UnsafeCell<$native> {}
        // SAFETY: See safety comment in next match arm.
        unsafe impl crate::pointer::transmute::UnsafeCellsAgree<UnsafeCell<$native>> for $atomic {}

        unsafe_impl_transmute_from_for_atomic!($(#[$attr])* $($atomics [$natives],)*);
    };
    ($(#[$attr:meta])* $tyvar:ident => $atomic:ty [$native:ty]) => {
        // We implement `TransmuteFromOld<$native>` for `$atomic`. The caller has
        // promised that `$atomic` and `$native` are an atomic type and its
        // native counterpart, respectively. Per [1], `$atomic` and `$native`
        // have the same size. Per [1], `$native` and `UnsafeCell<$native>` have
        // the same size.
        //
        // [1] Per (for example) https://doc.rust-lang.org/1.81.0/std/sync/atomic/struct.AtomicU64.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type
        //
        // [2] Per https://doc.rust-lang.org/1.81.0/std/cell/struct.UnsafeCell.html#memory-layout:
        //
        //   `UnsafeCell<T>` has the same in-memory representation as its inner
        //   type `T`.
        $(#[$attr])*
        unsafe impl<$tyvar> crate::pointer::transmute::TransmuteFromOld<UnsafeCell<$native>> for $atomic {
            // SAFETY: It is always trivially sound to produce a `Ptr` with
            // `Unknown` alignment.
            unsafe_impl_transmute_from_for_atomic!(@inner UnsafeCell<$native> => $atomic | Unknown);
        }

        unsafe impl<$tyvar> crate::pointer::transmute::TransmuteFromOld<$atomic> for UnsafeCell<$native> {
            // SAFETY: Per [1], an atomic's alignment is equal to its size. This
            // is the maximum possible alignment for any non-zero-sized type
            // since size must be a multiple of alignment [2]. Thus, if
            // `UnsafeCell<$native>` (which has the same size as `$atomic` as
            // proven above) is well-aligned, then so is an `$atomic` at the
            // same memory address.
            //
            // [1] Per (for example) https://doc.rust-lang.org/1.81.0/std/sync/atomic/struct.AtomicU64.html:
            //
            //   However, the alignment of this type is always equal to its
            //   size, even on targets where `u64`` has a lesser alignment.
            //
            // [2] Per https://doc.rust-lang.org/1.81.0/reference/type-layout.html#size-and-alignment:
            //
            //   The size of a value is always a multiple of its alignment.
            unsafe_impl_transmute_from_for_atomic!(@inner $atomic => UnsafeCell<$native> | Preserved);
        }

        // SAFETY: It is "obvious" that each atomic type contains a single
        // `UnsafeCell` that covers all bytes of the type, but we can also prove
        // it:
        // - Since `$atomic` provides an API which permits loading and storing
        //   values of type `$native` via a `&self` (shared) reference, *some*
        //   interior mutation must be happening, and interior mutation can only
        //   happen via `UnsafeCell`. Further, there must be enough bytes in
        //   `$atomic` covered by an `UnsafeCell` to hold every possible value
        //   of `$native`.
        // - Per [1], `$atomic` has the same size as `$native`. This on its own
        //   isn't enough: it would still be possible for `$atomic` to store
        //   `$native` using a compact representation (for `$native` types for
        //   which some bit patterns are illegal). However, this is ruled out by
        //   the fact that `$atomic` has the same bit validity as `$native` [1].
        //   Thus, we can conclude that every byte of `$atomic` must be covered
        //   by an `UnsafeCell`.
        //
        // Thus, every byte of `$atomic` is covered by an `UnsafeCell`, and so
        // `$atomic` and `UnsafeCell<$native>` have `UnsafeCell`s covering the
        // same byte ranges. That is required in order for `Preserved` to be the
        // correct aliasing mapping.
        //
        // [1] Per (for example) https://doc.rust-lang.org/1.81.0/std/sync/atomic/struct.AtomicU64.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type
        unsafe impl<$tyvar> crate::pointer::transmute::UnsafeCellsAgree<$atomic> for UnsafeCell<$native> {}
        // SAFETY: See above.
        unsafe impl<$tyvar> crate::pointer::transmute::UnsafeCellsAgree<UnsafeCell<$native>> for $atomic {}
    };
    // # Safety
    //
    // The caller promises that `$alignment_mapping` is sound.
    (@inner $from:ty => $to:ty | $alignment_mapping:ident) => {
        // The caller guarantees the safety of this mapping.
        type AlignmentMapping = crate::pointer::invariant::$alignment_mapping;
        // SAFETY: Per [1], all atomic types have the same bit validity as their
        // native counterparts. The caller has promised that `$atomic` and
        // `$native` are an atomic type and its native counterpart,
        // respectively.
        //
        // [1] Per (for example) https://doc.rust-lang.org/1.81.0/std/sync/atomic/struct.AtomicU64.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type
        type ValidityMapping = crate::pointer::invariant::Preserved;

        #[inline(always)]
        #[allow(clippy::as_conversions)]
        fn cast_from(ptr: *mut $from) -> *mut $to {
            ptr as *mut $to
        }
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
    ($($(#[$attrs:meta])* $ty:ty),*) => { $(impl_known_layout!(@inner , => $(#[$attrs])* $ty);)* };
    (@inner $(const $constvar:ident : $constty:ty)? , $($tyvar:ident $(: ?$optbound:ident)?)? => $(#[$attrs:meta])* $ty:ty) => {
        const _: () = {
            use core::ptr::NonNull;

            #[allow(non_local_definitions)]
            $(#[$attrs])*
            // SAFETY: Delegates safety to `DstLayout::for_type`.
            unsafe impl<$($tyvar $(: ?$optbound)?)? $(, const $constvar : $constty)?> KnownLayout for $ty {
                #[allow(clippy::missing_inline_in_public_items)]
                #[cfg_attr(coverage_nightly, coverage(off))]
                fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}

                type PointerMetadata = ();

                // SAFETY: `CoreMaybeUninit<T>::LAYOUT` and `T::LAYOUT` are
                // identical because `CoreMaybeUninit<T>` has the same size and
                // alignment as `T` [1], and `CoreMaybeUninit` admits
                // uninitialized bytes in all positions.
                //
                // [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
                //
                //   `MaybeUninit<T>` is guaranteed to have the same size,
                //   alignment, and ABI as `T`
                type MaybeUninit = core::mem::MaybeUninit<Self>;

                const LAYOUT: crate::DstLayout = crate::DstLayout::for_type::<$ty>();

                // SAFETY: `.cast` preserves address and provenance.
                //
                // TODO(#429): Add documentation to `.cast` that promises that
                // it preserves provenance.
                #[inline(always)]
                fn raw_from_ptr_len(bytes: NonNull<u8>, _meta: ()) -> NonNull<Self> {
                    bytes.cast::<Self>()
                }

                #[inline(always)]
                fn pointer_to_metadata(_ptr: *mut Self) -> () {
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
                #[cfg_attr(coverage_nightly, coverage(off))]
                fn only_derive_is_allowed_to_implement_this_trait() {}

                type PointerMetadata = <$repr as KnownLayout>::PointerMetadata;
                type MaybeUninit = <$repr as KnownLayout>::MaybeUninit;

                const LAYOUT: DstLayout = <$repr as KnownLayout>::LAYOUT;

                // SAFETY: All operations preserve address and provenance.
                // Caller has promised that the `as` cast preserves size.
                //
                // TODO(#429): Add documentation to `NonNull::new_unchecked`
                // that it preserves provenance.
                #[inline(always)]
                fn raw_from_ptr_len(bytes: NonNull<u8>, meta: <$repr as KnownLayout>::PointerMetadata) -> NonNull<Self> {
                    #[allow(clippy::as_conversions)]
                    let ptr = <$repr>::raw_from_ptr_len(bytes, meta).as_ptr() as *mut Self;
                    // SAFETY: `ptr` was converted from `bytes`, which is non-null.
                    unsafe { NonNull::new_unchecked(ptr) }
                }

                #[inline(always)]
                fn pointer_to_metadata(ptr: *mut Self) -> Self::PointerMetadata {
                    #[allow(clippy::as_conversions)]
                    let ptr = ptr as *mut $repr;
                    <$repr>::pointer_to_metadata(ptr)
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
    ($($tys:ty),*) => {
        $(
            // We only compile this assertion under `cfg(test)` to avoid taking
            // an extra non-dev dependency (and making this crate more expensive
            // to compile for our dependents).
            #[cfg(test)]
            static_assertions::const_assert_eq!(core::mem::align_of::<$tys>(), 1);
        )*
    };
}

/// Asserts at compile time that `$condition` is true for `Self` or the given
/// `$tyvar`s. Unlike `assert!`, this is *strictly* a compile-time check; it
/// cannot be evaluated in a runtime context. The condition is checked after
/// monomorphization and, upon failure, emits a compile error.
macro_rules! static_assert {
    (Self $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )? => $condition:expr $(, $args:tt)*) => {{
        trait StaticAssert {
            const ASSERT: bool;
        }

        impl<T $(: $(? $optbound +)* $($bound +)*)?> StaticAssert for T {
            const ASSERT: bool = {
                assert!($condition $(, $args)*);
                $condition
            };
        }

        assert!(<Self as StaticAssert>::ASSERT);
    }};
    ($($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),* => $condition:expr $(, $args:tt)*) => {{
        trait StaticAssert {
            const ASSERT: bool;
        }

        impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?,)*> StaticAssert for ($($tyvar,)*) {
            const ASSERT: bool = {
                assert!($condition $(, $args)*);
                $condition
            };
        }

        assert!(<($($tyvar,)*) as StaticAssert>::ASSERT);
    }};
}

/// Assert at compile time that `tyvar` does not have a zero-sized DST
/// component.
macro_rules! static_assert_dst_is_not_zst {
    ($tyvar:ident) => {{
        use crate::KnownLayout;
        static_assert!($tyvar: ?Sized + KnownLayout => {
            let dst_is_zst = match $tyvar::LAYOUT.size_info {
                crate::SizeInfo::Sized { .. } => false,
                crate::SizeInfo::SliceDst(TrailingSliceLayout { elem_size, .. }) => {
                    elem_size == 0
                }
            };
            !dst_is_zst
        }, "cannot call this method on a dynamically-sized type whose trailing slice element is zero-sized");
    }}
}

macro_rules! define_because {
    ($(#[$attr:meta])* $vis:vis $name:ident) => {
        #[cfg(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS)]
        $(#[$attr])*
        $vis type $name = ();
        #[cfg(not(__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS))]
        $(#[$attr])*
        $vis enum $name {}
    };
}
