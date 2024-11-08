// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// After updating the following doc comment, make sure to run the following
// command to update `README.md` based on its contents:
//
//   cargo -q run --manifest-path ../tools/Cargo.toml -p generate-readme > README.md

//! Support for unsafe fields.
//!
//! This crate provides the [`unsafe_fields!`] macro, which can be used to mark
//! fields as unsafe. Unsafe fields automatically have their types wrapped using
//! the [`Unsafe`] wrapper type. An `Unsafe` is intended to be used to for
//! struct, enum, or union fields which carry safety invariants. All accessors
//! are `unsafe`, which requires any use of an `Unsafe` field to be inside an
//! `unsafe` block. One exception is [`Unsafe::as_ref`], which is available when
//! the `zerocopy_0_8` feature is enabled. See its docs for more information.
//!
//! An unsafe field has the type `Unsafe<O, F, const NAME_HASH: u128>`. `O` is
//! the enclosing type (struct, enum, or union), `F` is the type of the field,
//! and `NAME_HASH` is the hash of the field's name. `O` prevents swapping
//! unsafe fields of the same `F` type between different enclosing types, and
//! `NAME_HASH` prevents swapping different fields of the same `F` type within
//! the same enclosing type. Note that swapping the same field between instances
//! of the same type [cannot be prevented](crate#limitations).
//!
//! [immutable]: zerocopy_0_8::Immutable
//!
//! # Examples
//!
//! ```rust
//! use unsafe_fields::{unsafe_fields, Unsafe};
//!
//! unsafe_fields! {
//!     /// A `usize` which is guaranteed to be even.
//!     pub struct EvenUsize {
//!         // INVARIANT: `n` is even.
//!         #[unsafe]
//!         n: usize,
//!     }
//! }
//!
//! impl EvenUsize {
//!     /// Constructs a new `EvenUsize`.
//!     ///
//!     /// Returns `None` if `n` is odd.
//!     pub fn new(n: usize) -> Option<EvenUsize> {
//!         if n % 2 != 0 {
//!             return None;
//!         }
//!         // SAFETY: We just confirmed that `n` is even.
//!         let n = unsafe { Unsafe::new(n) };
//!         Some(EvenUsize { n })
//!     }
//! }
//! ```
//!
//! Attempting to swap unsafe fields of the same type is prevented:
//!
//! ```rust,compile_fail,E0308
//! use unsafe_fields::{unsafe_fields, Unsafe};
//!
//! unsafe_fields! {
//!     /// A range.
//!     pub struct Range {
//!         // INVARIANT: `lo <= hi`.
//!         #[unsafe]
//!         lo: usize,
//!         #[unsafe]
//!         hi: usize,
//!     }
//! }
//!
//! impl Range {
//!     pub fn swap(&mut self) {
//!         // ERROR: Mismatched types
//!         core::mem::swap(&mut self.lo, &mut self.hi);
//!     }
//! }
//! ```
//!
//! # Limitations
//!
//! Note that we cannot prevent `Unsafe`s from being swapped between the same
//! field in instances of the same type:
//!
//! ```rust
//! use unsafe_fields::{unsafe_fields, Unsafe};
//!
//! unsafe_fields! {
//!     /// A `usize` which is guaranteed to be even.
//!     pub struct EvenUsize {
//!         // INVARIANT: `n` is even.
//!         #[unsafe]
//!         n: usize,
//!     }
//! }
//!
//! pub fn swap(a: &mut EvenUsize, b: &mut EvenUsize) {
//!     core::mem::swap(&mut a.n, &mut b.n);
//! }
//! ```

// Sometimes we want to use lints which were added after our MSRV.
// `unknown_lints` is `warn` by default and we deny warnings in CI, so without
// this attribute, any unknown lint would cause a CI failure when testing with
// our MSRV.
#![allow(unknown_lints, non_local_definitions, unreachable_patterns)]
#![deny(renamed_and_removed_lints)]
#![deny(
    anonymous_parameters,
    deprecated_in_future,
    late_bound_lifetime_arguments,
    missing_docs,
    path_statements,
    patterns_in_fns_without_body,
    rust_2018_idioms,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    unused_extern_crates,
    // We intentionally choose not to deny `unused_qualifications`. When items
    // are added to the prelude (e.g., `core::mem::size_of`), this has the
    // consequence of making some uses trigger this lint on the latest toolchain
    // (e.g., `mem::size_of`), but fixing it (e.g. by replacing with `size_of`)
    // does not work on older toolchains.
    //
    // We tested a more complicated fix in #1413, but ultimately decided that,
    // since this lint is just a minor style lint, the complexity isn't worth it
    // - it's fine to occasionally have unused qualifications slip through,
    // especially since these do not affect our user-facing API in any way.
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
    clippy::double_must_use,
    clippy::get_unwrap,
    clippy::indexing_slicing,
    clippy::missing_const_for_fn,
    clippy::missing_inline_in_public_items,
    clippy::missing_safety_doc,
    clippy::must_use_candidate,
    clippy::must_use_unit,
    clippy::obfuscated_if_else,
    clippy::perf,
    clippy::print_stdout,
    clippy::return_self_not_must_use,
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
#![allow(clippy::type_complexity)]
#![deny(
    rustdoc::bare_urls,
    rustdoc::broken_intra_doc_links,
    rustdoc::invalid_codeblock_attributes,
    rustdoc::invalid_html_tags,
    rustdoc::invalid_rust_codeblocks,
    rustdoc::missing_crate_level_docs,
    rustdoc::private_intra_doc_links
)]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

use core::marker::PhantomData;

/// A field with safety invariants.
///
/// `Unsafe` should not be named directly - instead, use [`unsafe_fields!`] to
/// declare a type with unsafe fields.
///
/// See the [crate-level documentation](crate) for more information.
#[repr(transparent)]
pub struct Unsafe<O: ?Sized, F: ?Sized, const NAME_HASH: u128> {
    _marker: PhantomData<O>,
    // INVARIANT: `field` is only modified via public `unsafe` methods. User code is never
    // invoked implicitly except via public `unsafe` methods.
    field: F,
}

// NOTE on design: It may seem counter-intuitive to offer an impl of traits that
// don't require `unsafe` to call. Unfortunately, this is a fundamental
// requirement if users want to be able to mark their types as `Copy`. Luckily,
// we can implement `Copy` (and its unavoidable super-trait, `Clone`) without
// invoking user code or opening up the possibility of modifying the field. We
// do this by only implementing `Copy` and `Clone` when `F: Copy`. For `Clone`,
// the user is still able to provide a manual impl, so this does not
// fundamentally restrict what behavior can be supported.
impl<O: ?Sized, F: Copy, const NAME_HASH: u128> Copy for Unsafe<O, F, { NAME_HASH }> {}
impl<O: ?Sized, F: Copy, const NAME_HASH: u128> Clone for Unsafe<O, F, { NAME_HASH }> {
    #[inline(always)]
    #[allow(clippy::non_canonical_clone_impl)]
    fn clone(&self) -> Self {
        // SAFETY: We don't call any user-defined code here (only make a
        // bit-for-bit copy of `self.field`), so there's no way to accidentally
        // invoke user-defined code or modify `self.field`.
        Unsafe { _marker: PhantomData, field: self.field }
    }
}

impl<O: ?Sized, F: ?Sized, const NAME_HASH: u128> Unsafe<O, F, { NAME_HASH }> {
    /// Gets a reference to the inner value.
    ///
    /// If [`F: Immutable`][immutable], prefer [`as_ref`], which is safe.
    ///
    /// [immutable]: zerocopy_0_8::Immutable
    /// [`as_ref`]: Unsafe::as_ref
    ///
    /// # Safety
    ///
    /// The caller is responsible for upholding any safety invariants associated
    /// with this field.
    #[inline(always)]
    pub const unsafe fn as_ref_unchecked(&self) -> &F {
        // SAFETY: This method is unsafe to call.
        &self.field
    }

    /// Gets a reference to the inner value safely so long as the inner value is
    /// immutable.
    ///
    /// If [`F: Immutable`][immutable], then `F` does not permit interior
    /// mutation, and so it is safe to return a reference to it.
    ///
    /// [immutable]: zerocopy_0_8::Immutable
    #[inline(always)]
    #[cfg(feature = "zerocopy_0_8")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "zerocopy_0_8")))]
    pub const fn as_ref(&self) -> &F
    where
        F: zerocopy_0_8::Immutable,
    {
        // SAFETY: `F: Immutable` guarantees that the returned `&F` cannot be
        // used to mutate `self`, and so it cannot be used to violate any
        // invariant.
        unsafe { self.as_ref_unchecked() }
    }

    /// Gets a mutable reference to the inner value.
    ///
    /// # Safety
    ///
    /// The caller is responsible for upholding any safety invariants associated
    /// with this field.
    #[inline(always)]
    pub unsafe fn as_mut(&mut self) -> &mut F {
        // SAFETY: This method is unsafe to call.
        &mut self.field
    }
}

impl<O: ?Sized, F, const NAME_HASH: u128> Unsafe<O, F, { NAME_HASH }> {
    /// Constructs a new `Unsafe`.
    ///
    /// # Safety
    ///
    /// The caller is responsible for upholding any safety invariants associated
    /// with this field.
    #[inline(always)]
    pub const unsafe fn new(field: F) -> Unsafe<O, F, { NAME_HASH }> {
        // SAFETY: This method is unsafe to call.
        Unsafe { _marker: PhantomData, field }
    }

    /// Extracts the inner `F` from `self`.
    #[inline(always)]
    pub const fn into(self) -> F {
        use core::mem::ManuallyDrop;
        let slf = ManuallyDrop::new(self);

        #[repr(C)]
        union Transmute<Src, Dst> {
            src: ManuallyDrop<Src>,
            dst: ManuallyDrop<Dst>,
        }

        // We'd like to just return `self.field` here, but Rust would drop
        // `self` in doing that, which we don't want. Even destructuring (ie,
        // `let Unsafe { field, .. } = self`) also causes a drop. We also can't
        // use `mem::transmute` because that requires all types to be concrete,
        // so a union transmute is our only option.
        //
        // SAFETY: `ManuallyDrop<Unsafe<_, F, _>>` has the same size and bit
        // validity as `Unsafe<_, F, _>`. [1] `Unsafe<_, F, _>` is
        // `#[repr(transparent)]` and has no other fields, and so it has the
        // same size and bit validity as `F`.
        //
        // [1] Per https://doc.rust-lang.org/1.81.0/core/mem/struct.ManuallyDrop.html:
        //
        //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
        //   validity as `T`
        let dst = unsafe { Transmute { src: slf }.dst };

        ManuallyDrop::into_inner(dst)
    }
}

/// Defines a type with unsafe fields.
///
/// See the [crate-level documentation](crate) for more information.
// TODO: Allow specifying *which* fields are unsafe.
#[macro_export]
macro_rules! unsafe_fields {
    ($(#[$attr:meta])* $vis:vis struct $name:ident {
        $($(#[$field_attr:tt])? $field:ident: $field_ty:ty),* $(,)?
    }) => {
        $(#[$attr])*
        $vis struct $name {
            $(
                $field: unsafe_fields!(@field $(#[$field_attr])? $field: $field_ty),
            )*
        }
    };

    (
        $( #[$attr:meta] )*
        $vis:vis enum $name:ident {
            $(
                $(#[$variant_attrs:meta])*
                $variant:ident $({
                    $(
                        $(#[$field_attr:ident])?
                        $field:ident: $field_ty:ty
                    ),+ $(,)?
                })?
                $((
                    $(
                        $field_ty2:ty
                    ),+ $(,)?
                ))?
            ),+ $(,)?
        }
    ) => {
        $(#[$attr])*
        $vis enum $name {
            $(
                $(#[$variant_attrs])*
                $variant $({
                    $(
                        $field: unsafe_fields!(@field $(#[$field_attr])? $field: $field_ty),
                    )*
                })?
                $((
                    $(
                        $field_ty2,
                    )+
                ))?
            ),+
        }
    };

    (@field #[unsafe] $field:ident: $field_ty:ty) => {
        $crate::Unsafe<Self, $field_ty, {$crate::macro_util::hash_field_name(stringify!($field))}>
    };
    (@field $_field:ident: $field_ty:ty) => {
        $field_ty
    }
}

#[doc(hidden)]
pub mod macro_util {
    // TODO: Implement a stronger hash function so we can basically just ignore
    // collisions. If users encounter collisions in practice, we can just deal
    // with it then, publish a new version, and tell them to upgrade.
    #[inline(always)]
    #[must_use]
    #[allow(clippy::as_conversions, clippy::indexing_slicing, clippy::arithmetic_side_effects)]
    pub const fn hash_field_name(field_name: &str) -> u128 {
        // An implementation of FxHasher, although returning a u128. Probably
        // not as strong as it could be, but probably more collision resistant
        // than normal 64-bit FxHasher.
        let field_name = field_name.as_bytes();
        let mut hash = 0u128;
        let mut i = 0;
        while i < field_name.len() {
            // This is just FxHasher's `0x517cc1b727220a95` constant
            // concatenated back-to-back.
            const K: u128 = 0x517cc1b727220a95517cc1b727220a95;
            hash = (hash.rotate_left(5) ^ (field_name[i] as u128)).wrapping_mul(K);
            i += 1;
        }
        hash
    }
}

#[cfg(test)]
#[allow(clippy::missing_const_for_fn)]
mod tests {
    use super::*;

    unsafe_fields! {
        /// A `Foo`.
        #[allow(unused)]
        struct Foo {
            #[unsafe]
            a: usize,
            b: usize,
        }
    }

    unsafe_fields! {
        /// A `Bar`.
        #[allow(unused)]
        struct Bar {
            #[unsafe]
            a: usize,
            #[unsafe]
            b: usize,
        }
    }

    #[test]
    #[allow(clippy::undocumented_unsafe_blocks)]
    fn test_unsafe_fields() {
        let mut _foo = Foo { a: unsafe { Unsafe::new(0) }, b: 0 };
        let mut _bar = Bar { a: unsafe { Unsafe::new(0) }, b: unsafe { Unsafe::new(0) } };
    }

    unsafe_fields! {
        #[allow(unused)]
        enum FooEnum {
            UnitA,
            UnitB,
            StructVariantA {
                a: i32,
                #[unsafe]
                b: String,
            },
            StructVariantB {
                #[unsafe]
                a: usize,
                #[unsafe]
                b: String,
            },
            TupleVariant(i32, String, usize),
        }
    }
    #[test]
    #[allow(clippy::undocumented_unsafe_blocks)]
    fn test_unsafe_fields_enum() {
        let mut _foofoo_a =
            FooEnum::StructVariantA { a: 0, b: unsafe { Unsafe::new(String::from("foo")) } };
        let mut _foofoo_b = FooEnum::StructVariantB {
            a: unsafe { Unsafe::new(0) },
            b: unsafe { Unsafe::new(String::from("foo")) },
        };
        let mut _foo_c = FooEnum::UnitA;
        let mut _foo_d = FooEnum::TupleVariant(1, String::from("foo"), 0);
    }
}

/// This module exists so that we can use rustdoc to perform compile-fail tests
/// rather than having to set up an entire trybuild set suite.
///
/// ```compile_fail,E0308
/// use unsafe_fields::*;
///
/// unsafe_fields! {
///     struct Foo {
///         #[unsafe]
///         a: usize,
///         b: usize,
///     }
/// }
///
/// impl Foo {
///     // Swapping an unsafe field with a non-unsafe field is a compile error.
///     fn swap(&mut self) {
///         core::mem::swap(&mut self.a, &mut self.b);
///     }
/// }
/// ```
///
/// ```compile_fail,E0308
/// use unsafe_fields::*;
///
/// unsafe_fields! {
///     struct Foo {
///         #[unsafe]
///         a: usize,
///         #[unsafe]
///         b: usize,
///     }
/// }
///
/// impl Foo {
///     // Swapping an unsafe field with another unsafe field is a compile
///     // error.
///     fn swap(&mut self) {
///         core::mem::swap(&mut self.a, &mut self.b);
///     }
/// }
/// ```
///
/// ```compile_fail,E0308
/// use unsafe_fields::*;
///
/// unsafe_fields! {
///     struct Foo {
///         #[unsafe]
///         a: usize,
///     }
/// }
///
/// unsafe_fields! {
///     struct Bar {
///         #[unsafe]
///         a: usize,
///     }
/// }
///
/// // Swapping identically-named unsafe fields from different types is a
/// // compile error.
/// fn swap(foo: &mut Foo, bar: &mut Bar) {
///     core::mem::swap(&mut foo.a, &mut bar.a);
/// }
/// ```
#[doc(hidden)]
pub mod compile_fail {}
