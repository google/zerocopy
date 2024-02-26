// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Derive macros for [zerocopy]'s traits.
//!
//! [zerocopy]: https://docs.rs/zerocopy

// Sometimes we want to use lints which were added after our MSRV.
// `unknown_lints` is `warn` by default and we deny warnings in CI, so without
// this attribute, any unknown lint would cause a CI failure when testing with
// our MSRV.
#![allow(unknown_lints)]
#![deny(renamed_and_removed_lints)]
#![deny(clippy::all, clippy::missing_safety_doc, clippy::undocumented_unsafe_blocks)]
#![deny(
    rustdoc::bare_urls,
    rustdoc::broken_intra_doc_links,
    rustdoc::invalid_codeblock_attributes,
    rustdoc::invalid_html_tags,
    rustdoc::invalid_rust_codeblocks,
    rustdoc::missing_crate_level_docs,
    rustdoc::private_intra_doc_links
)]
#![recursion_limit = "128"]

mod ext;
mod repr;

use quote::quote_spanned;

use {
    proc_macro2::Span,
    quote::quote,
    syn::{
        parse_quote, parse_quote_spanned, Data, DataEnum, DataStruct, DataUnion, DeriveInput,
        Error, Expr, ExprLit, GenericParam, Ident, Lit, Path, Type, WherePredicate,
    },
};

use {crate::ext::*, crate::repr::*};

// Unwraps a `Result<_, Vec<Error>>`, converting any `Err` value into a
// `TokenStream` and returning it.
macro_rules! try_or_print {
    ($e:expr) => {
        match $e {
            Ok(x) => x,
            Err(errors) => return print_all_errors(errors).into(),
        }
    };
}

// TODO(https://github.com/rust-lang/rust/issues/54140): Some errors could be
// made better if we could add multiple lines of error output like this:
//
// error: unsupported representation
//   --> enum.rs:28:8
//    |
// 28 | #[repr(transparent)]
//    |
// help: required by the derive of FromBytes
//
// Instead, we have more verbose error messages like "unsupported representation
// for deriving FromZeros, FromBytes, IntoBytes, or Unaligned on an enum"
//
// This will probably require Span::error
// (https://doc.rust-lang.org/nightly/proc_macro/struct.Span.html#method.error),
// which is currently unstable. Revisit this once it's stable.

/// Defines a derive function named `$outer` which parses its input
/// `TokenStream` as a `DeriveInput` and then invokes the `$inner` function.
///
/// Note that the separate `$outer` parameter is required - proc macro functions
/// are currently required to live at the crate root, and so the caller must
/// specify the name in order to avoid name collisions.
macro_rules! derive {
    ($trait:ident => $outer:ident => $inner:ident) => {
        #[proc_macro_derive($trait)]
        pub fn $outer(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
            let ast = syn::parse_macro_input!(ts as DeriveInput);
            $inner(&ast).into()
        }
    };
}

derive!(KnownLayout => derive_known_layout => derive_known_layout_inner);
derive!(NoCell => derive_no_cell => derive_no_cell_inner);
derive!(TryFromBytes => derive_try_from_bytes => derive_try_from_bytes_inner);
derive!(FromZeros => derive_from_zeros => derive_from_zeros_inner);
derive!(FromBytes => derive_from_bytes => derive_from_bytes_inner);
derive!(IntoBytes => derive_into_bytes => derive_into_bytes_inner);
derive!(Unaligned => derive_unaligned => derive_unaligned_inner);

/// Deprecated: prefer [`FromZeros`] instead.
#[deprecated(since = "0.8.0", note = "`FromZeroes` was renamed to `FromZeros`")]
#[doc(hidden)]
#[proc_macro_derive(FromZeroes)]
pub fn derive_from_zeroes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive_from_zeros(ts)
}

/// Deprecated: prefer [`IntoBytes`] instead.
#[deprecated(since = "0.8.0", note = "`AsBytes` was renamed to `IntoBytes`")]
#[doc(hidden)]
#[proc_macro_derive(AsBytes)]
pub fn derive_as_bytes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive_into_bytes(ts)
}

fn derive_known_layout_inner(ast: &DeriveInput) -> proc_macro2::TokenStream {
    let is_repr_c_struct = match &ast.data {
        Data::Struct(..) => {
            let reprs = try_or_print!(repr::reprs::<Repr>(&ast.attrs));
            if reprs.iter().any(|(_meta, repr)| repr == &Repr::C) {
                Some(reprs)
            } else {
                None
            }
        }
        Data::Enum(..) | Data::Union(..) => None,
    };

    let fields = ast.data.fields();

    let (self_bounds, extras) = if let (Some(reprs), Some((trailing_field, leading_fields))) =
        (is_repr_c_struct, fields.split_last())
    {
        let (_name, trailing_field_ty) = trailing_field;
        let leading_fields_tys = leading_fields.iter().map(|(_name, ty)| ty);

        let core_path = quote!(::zerocopy::macro_util::core_reexport);
        let repr_align = reprs
            .iter()
            .find_map(
                |(_meta, repr)| {
                    if let Repr::Align(repr_align) = repr {
                        Some(repr_align)
                    } else {
                        None
                    }
                },
            )
            .map(|repr_align| quote!(#core_path::num::NonZeroUsize::new(#repr_align as usize)))
            .unwrap_or(quote!(#core_path::option::Option::None));

        let repr_packed = reprs
            .iter()
            .find_map(|(_meta, repr)| match repr {
                Repr::Packed => Some(1),
                Repr::PackedN(repr_packed) => Some(*repr_packed),
                _ => None,
            })
            .map(|repr_packed| quote!(#core_path::num::NonZeroUsize::new(#repr_packed as usize)))
            .unwrap_or(quote!(#core_path::option::Option::None));

        (
            SelfBounds::None,
            quote!(
                // SAFETY: `LAYOUT` accurately describes the layout of `Self`.
                // The layout of `Self` is reflected using a sequence of
                // invocations of `DstLayout::{new_zst,extend,pad_to_align}`.
                // The documentation of these items vows that invocations in
                // this manner will acurately describe a type, so long as:
                //
                //  - that type is `repr(C)`,
                //  - its fields are enumerated in the order they appear,
                //  - the presence of `repr_align` and `repr_packed` are correctly accounted for.
                //
                // We respect all three of these preconditions here. This
                // expansion is only used if `is_repr_c_struct`, we enumerate
                // the fields in order, and we extract the values of `align(N)`
                // and `packed(N)`.
                const LAYOUT: ::zerocopy::DstLayout = {
                    use ::zerocopy::macro_util::core_reexport::num::NonZeroUsize;
                    use ::zerocopy::{DstLayout, KnownLayout};

                    let repr_align = #repr_align;
                    let repr_packed = #repr_packed;

                    DstLayout::new_zst(repr_align)
                        #(.extend(DstLayout::for_type::<#leading_fields_tys>(), repr_packed))*
                        .extend(<#trailing_field_ty as KnownLayout>::LAYOUT, repr_packed)
                        .pad_to_align()
                };

                // SAFETY:
                // - The recursive call to `raw_from_ptr_len` preserves both address and provenance.
                // - The `as` cast preserves both address and provenance.
                // - `NonNull::new_unchecked` preserves both address and provenance.
                #[inline(always)]
                fn raw_from_ptr_len(
                    bytes: ::zerocopy::macro_util::core_reexport::ptr::NonNull<u8>,
                    elems: usize,
                ) -> ::zerocopy::macro_util::core_reexport::ptr::NonNull<Self> {
                    use ::zerocopy::{KnownLayout};
                    let trailing = <#trailing_field_ty as KnownLayout>::raw_from_ptr_len(bytes, elems);
                    let slf = trailing.as_ptr() as *mut Self;
                    // SAFETY: Constructed from `trailing`, which is non-null.
                    unsafe { ::zerocopy::macro_util::core_reexport::ptr::NonNull::new_unchecked(slf) }
                }
            ),
        )
    } else {
        // For enums, unions, and non-`repr(C)` structs, we require that
        // `Self` is sized, and as a result don't need to reason about the
        // internals of the type.
        (
            SelfBounds::SIZED,
            quote!(
                // SAFETY: `LAYOUT` is guaranteed to accurately describe the
                // layout of `Self`, because that is the documented safety
                // contract of `DstLayout::for_type`.
                const LAYOUT: ::zerocopy::DstLayout = ::zerocopy::DstLayout::for_type::<Self>();

                // SAFETY: `.cast` preserves address and provenance.
                //
                // TODO(#429): Add documentation to `.cast` that promises that
                // it preserves provenance.
                #[inline(always)]
                fn raw_from_ptr_len(
                    bytes: ::zerocopy::macro_util::core_reexport::ptr::NonNull<u8>,
                    _elems: usize,
                ) -> ::zerocopy::macro_util::core_reexport::ptr::NonNull<Self> {
                    bytes.cast::<Self>()
                }
            ),
        )
    };

    match &ast.data {
        Data::Struct(strct) => {
            let require_trait_bound_on_field_types = if self_bounds == SelfBounds::SIZED {
                FieldBounds::None
            } else {
                FieldBounds::TRAILING_SELF
            };

            // A bound on the trailing field is required, since structs are
            // unsized if their trailing field is unsized. Reflecting the layout
            // of an usized trailing field requires that the field is
            // `KnownLayout`.
            impl_block(
                ast,
                strct,
                Trait::KnownLayout,
                require_trait_bound_on_field_types,
                self_bounds,
                None,
                Some(extras),
            )
        }
        Data::Enum(enm) => {
            // A bound on the trailing field is not required, since enums cannot
            // currently be unsized.
            impl_block(
                ast,
                enm,
                Trait::KnownLayout,
                FieldBounds::None,
                SelfBounds::SIZED,
                None,
                Some(extras),
            )
        }
        Data::Union(unn) => {
            // A bound on the trailing field is not required, since unions
            // cannot currently be unsized.
            impl_block(
                ast,
                unn,
                Trait::KnownLayout,
                FieldBounds::None,
                SelfBounds::SIZED,
                None,
                Some(extras),
            )
        }
    }
}

fn derive_no_cell_inner(ast: &DeriveInput) -> proc_macro2::TokenStream {
    match &ast.data {
        Data::Struct(strct) => impl_block(
            ast,
            strct,
            Trait::NoCell,
            FieldBounds::ALL_SELF,
            SelfBounds::None,
            None,
            None,
        ),
        Data::Enum(enm) => {
            impl_block(ast, enm, Trait::NoCell, FieldBounds::ALL_SELF, SelfBounds::None, None, None)
        }
        Data::Union(unn) => {
            impl_block(ast, unn, Trait::NoCell, FieldBounds::ALL_SELF, SelfBounds::None, None, None)
        }
    }
}

fn derive_try_from_bytes_inner(ast: &DeriveInput) -> proc_macro2::TokenStream {
    match &ast.data {
        Data::Struct(strct) => derive_try_from_bytes_struct(ast, strct),
        Data::Enum(enm) => derive_try_from_bytes_enum(ast, enm),
        Data::Union(unn) => derive_try_from_bytes_union(ast, unn),
    }
}

fn derive_from_zeros_inner(ast: &DeriveInput) -> proc_macro2::TokenStream {
    let try_from_bytes = derive_try_from_bytes_inner(ast);
    let from_zeros = match &ast.data {
        Data::Struct(strct) => derive_from_zeros_struct(ast, strct),
        Data::Enum(enm) => derive_from_zeros_enum(ast, enm),
        Data::Union(unn) => derive_from_zeros_union(ast, unn),
    };
    IntoIterator::into_iter([try_from_bytes, from_zeros]).collect()
}

fn derive_from_bytes_inner(ast: &DeriveInput) -> proc_macro2::TokenStream {
    let from_zeros = derive_from_zeros_inner(ast);
    let from_bytes = match &ast.data {
        Data::Struct(strct) => derive_from_bytes_struct(ast, strct),
        Data::Enum(enm) => derive_from_bytes_enum(ast, enm),
        Data::Union(unn) => derive_from_bytes_union(ast, unn),
    };

    IntoIterator::into_iter([from_zeros, from_bytes]).collect()
}

fn derive_into_bytes_inner(ast: &DeriveInput) -> proc_macro2::TokenStream {
    match &ast.data {
        Data::Struct(strct) => derive_into_bytes_struct(ast, strct),
        Data::Enum(enm) => derive_into_bytes_enum(ast, enm),
        Data::Union(unn) => derive_into_bytes_union(ast, unn),
    }
}

fn derive_unaligned_inner(ast: &DeriveInput) -> proc_macro2::TokenStream {
    match &ast.data {
        Data::Struct(strct) => derive_unaligned_struct(ast, strct),
        Data::Enum(enm) => derive_unaligned_enum(ast, enm),
        Data::Union(unn) => derive_unaligned_union(ast, unn),
    }
}

// A struct is `TryFromBytes` if:
// - all fields are `TryFromBytes`

fn derive_try_from_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    let extras = Some({
        let fields = strct.fields();
        let field_names = fields.iter().map(|(name, _ty)| name);
        let field_tys = fields.iter().map(|(_name, ty)| ty);
        quote!(
            // SAFETY: We use `is_bit_valid` to validate that each field is
            // bit-valid, and only return `true` if all of them are. The bit
            // validity of a struct is just the composition of the bit
            // validities of its fields, so this is a sound implementation of
            // `is_bit_valid`.
            fn is_bit_valid<A: ::zerocopy::pointer::invariant::at_least::Shared>(
                mut candidate: ::zerocopy::Maybe<Self, A>
            ) -> bool {
                true #(&& {
                    // SAFETY: `project` is a field projection of `candidate`,
                    // and `Self` is a struct type. The candidate will have
                    // `UnsafeCell`s at exactly the same ranges as its
                    // projection, because the projection is a field of the
                    // candidate struct.
                    let field_candidate = unsafe {
                        let project = |slf: *mut Self|
                            ::zerocopy::macro_util::core_reexport::ptr::addr_of_mut!((*slf).#field_names);

                        candidate.reborrow().project(project)
                    };

                    <#field_tys as ::zerocopy::TryFromBytes>::is_bit_valid(field_candidate)
                })*
            }
        )
    });
    impl_block(
        ast,
        strct,
        Trait::TryFromBytes,
        FieldBounds::ALL_SELF,
        SelfBounds::None,
        None,
        extras,
    )
}

// A union is `TryFromBytes` if:
// - all of its fields are `TryFromBytes` and `NoCell`

fn derive_try_from_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#5): Remove the `NoCell` bound.
    let field_type_trait_bounds =
        FieldBounds::All(&[TraitBound::Slf, TraitBound::Other(Trait::NoCell)]);
    let extras = Some({
        let fields = unn.fields();
        let field_names = fields.iter().map(|(name, _ty)| name);
        let field_tys = fields.iter().map(|(_name, ty)| ty);
        quote!(
            // SAFETY: We use `is_bit_valid` to validate that any field is
            // bit-valid; we only return `true` if at least one of them is. The
            // bit validity of a union is not yet well defined in Rust, but it
            // is guaranteed to be no more strict than this definition. See #696
            // for a more in-depth discussion.
            fn is_bit_valid<A: ::zerocopy::pointer::invariant::at_least::Shared>(
                mut candidate: ::zerocopy::Maybe<Self, A>
            ) -> bool {
                false #(|| {
                    // SAFETY: `project` is a field projection of `candidate`,
                    // and `Self` is a union type. The candidate and projection
                    // agree exactly on where their `UnsafeCell` ranges are,
                    // because `Self: NoCell` is enforced by
                    // `self_type_trait_bounds`.
                    let field_candidate = unsafe {
                        let project = |slf: *mut Self|
                            ::zerocopy::macro_util::core_reexport::ptr::addr_of_mut!((*slf).#field_names);

                        candidate.reborrow().project(project)
                    };

                    <#field_tys as ::zerocopy::TryFromBytes>::is_bit_valid(field_candidate)
                })*
            }
        )
    });
    impl_block(
        ast,
        unn,
        Trait::TryFromBytes,
        field_type_trait_bounds,
        SelfBounds::None,
        None,
        extras,
    )
}

const STRUCT_UNION_ALLOWED_REPR_COMBINATIONS: &[&[StructRepr]] = &[
    &[StructRepr::C],
    &[StructRepr::Transparent],
    &[StructRepr::Packed],
    &[StructRepr::C, StructRepr::Packed],
];

fn derive_try_from_bytes_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_fieldless() {
        return Error::new_spanned(ast, "only field-less enums can implement TryFromBytes")
            .to_compile_error();
    }

    let reprs = try_or_print!(ENUM_TRY_FROM_BYTES_CFG.validate_reprs(ast));

    // Figure out whether the enum could in theory implement `FromBytes`.
    let from_bytes = enum_size_from_repr(reprs.as_slice())
        .map(|size| {
            // As of this writing, `enm.is_fieldless()` is redundant since we've
            // already checked for it and returned if the check failed. However, if
            // we ever remove that check, then without a similar check here, this
            // code would become unsound.
            enm.is_fieldless() && enm.variants.len() == 1usize << size
        })
        .unwrap_or(false);

    let variant_names = enm.variants.iter().map(|v| &v.ident);
    let is_bit_valid_body = if from_bytes {
        // If the enum could implement `FromBytes`, we can avoid emitting a
        // match statement. This is faster to compile, and generates code which
        // performs better.
        quote!({
            // Prevent an "unused" warning.
            let _ = candidate;
            // SAFETY: If the enum could implement `FromBytes`, then all bit
            // patterns are valid. Thus, this is a sound implementation.
            true
        })
    } else {
        quote!(
            use ::zerocopy::macro_util::core_reexport;
            // SAFETY:
            // - `cast` is implemented as required.
            // - By definition, `*mut Self` and `*mut [u8; size_of::<Self>()]`
            //   are types of the same size.
            // - Since we validate that this type is a field-less enum, it
            //   cannot contain any `UnsafeCell`s. Neither does `[u8; N]`.
            let discriminant = unsafe { candidate.cast_unsized(|p: *mut Self| p as *mut [core_reexport::primitive::u8; core_reexport::mem::size_of::<Self>()]) };
            // SAFETY: Since `candidate` has the invariant `Initialized`, we
            // know that `candidate`'s referent (and thus `discriminant`'s
            // referent) are fully initialized. Since all of the allowed `repr`s
            // are types for which all bytes are always initialized, we know
            // that `discriminant`'s referent has all of its bytes initialized.
            // Since `[u8; N]`'s validity invariant is just that all of its
            // bytes are initialized, we know that `discriminant`'s referent is
            // bit-valid.
            let discriminant = unsafe { discriminant.assume_valid() };
            let discriminant = discriminant.read_unaligned();

            false #(|| {
                let v = Self::#variant_names{};
                // SAFETY: All of the allowed `repr`s for `Self` guarantee that
                // `Self`'s discriminant bytes are all initialized. Since we
                // validate that `Self` has no fields, it has no bytes other
                // than the discriminant. Thus, it is sound to transmute any
                // instance of `Self` to `[u8; size_of::<Self>()]`.
                let d: [core_reexport::primitive::u8; core_reexport::mem::size_of::<Self>()] = unsafe { core_reexport::mem::transmute(v) };
                // SAFETY: Here we check that the bits of the argument
                // `candidate` are equal to the bits of a `Self` constructed
                // using safe code. If this condition passes, then we know that
                // `candidate` refers to a bit-valid `Self`.
                discriminant == d
            })*
        )
    };

    let extras = Some(quote!(
        // SAFETY: We use `is_bit_valid` to validate that the bit pattern
        // corresponds to one of the field-less enum's variant discriminants.
        // Thus, this is a sound implementation of `is_bit_valid`.
        fn is_bit_valid<A: ::zerocopy::pointer::invariant::at_least::Shared>(
            candidate: ::zerocopy::Ptr<
                '_,
                Self,
                (
                    A,
                    ::zerocopy::pointer::invariant::Any,
                    ::zerocopy::pointer::invariant::Initialized,
                ),
            >,
        ) -> ::zerocopy::macro_util::core_reexport::primitive::bool {
            #is_bit_valid_body
        }
    ));
    impl_block(ast, enm, Trait::TryFromBytes, FieldBounds::ALL_SELF, SelfBounds::None, None, extras)
}

#[rustfmt::skip]
const ENUM_TRY_FROM_BYTES_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        allowed_combinations_message: r#"TryFromBytes requires repr of "C", "u8", "u16", "u32", "u64", "usize", "i8", or "i16", "i32", "i64", or "isize""#,
        derive_unaligned: false,
        allowed_combinations: &[
            &[C],
            &[U8],
            &[U16],
            &[U32],
            &[U64],
            &[Usize],
            &[I8],
            &[I16],
            &[I32],
            &[I64],
            &[Isize],
        ],
        disallowed_but_legal_combinations: &[],
    }
};

// A struct is `FromZeros` if:
// - all fields are `FromZeros`

fn derive_from_zeros_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    impl_block(ast, strct, Trait::FromZeros, FieldBounds::ALL_SELF, SelfBounds::None, None, None)
}

// An enum is `FromZeros` if:
// - all of its variants are fieldless
// - one of the variants has a discriminant of `0`

fn derive_from_zeros_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_fieldless() {
        return Error::new_spanned(ast, "only field-less enums can implement FromZeros")
            .to_compile_error();
    }

    // We don't actually care what the repr is; we just care that it's one of
    // the allowed ones.
    try_or_print!(ENUM_FROM_ZEROS_INTO_BYTES_CFG.validate_reprs(ast));

    let has_explicit_zero_discriminant =
        enm.variants.iter().filter_map(|v| v.discriminant.as_ref()).any(|(_, e)| {
            if let Expr::Lit(ExprLit { lit: Lit::Int(i), .. }) = e {
                i.base10_parse::<usize>().ok() == Some(0)
            } else {
                false
            }
        });
    // If the first variant of an enum does not specify its discriminant, it is set to zero:
    // https://doc.rust-lang.org/reference/items/enumerations.html#custom-discriminant-values-for-fieldless-enumerations
    let has_implicit_zero_discriminant =
        enm.variants.iter().next().map(|v| v.discriminant.is_none()) == Some(true);

    if !has_explicit_zero_discriminant && !has_implicit_zero_discriminant {
        return Error::new_spanned(
            ast,
            "FromZeros only supported on enums with a variant that has a discriminant of `0`",
        )
        .to_compile_error();
    }

    impl_block(ast, enm, Trait::FromZeros, FieldBounds::ALL_SELF, SelfBounds::None, None, None)
}

// Unions are `FromZeros` if
// - all fields are `FromZeros` and `NoCell`

fn derive_from_zeros_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#5): Remove the `NoCell` bound. It's only necessary for
    // compatibility with `derive(TryFromBytes)` on unions; not for soundness.
    let field_type_trait_bounds =
        FieldBounds::All(&[TraitBound::Slf, TraitBound::Other(Trait::NoCell)]);
    impl_block(ast, unn, Trait::FromZeros, field_type_trait_bounds, SelfBounds::None, None, None)
}

// A struct is `FromBytes` if:
// - all fields are `FromBytes`

fn derive_from_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    impl_block(ast, strct, Trait::FromBytes, FieldBounds::ALL_SELF, SelfBounds::None, None, None)
}

// An enum is `FromBytes` if:
// - Every possible bit pattern must be valid, which means that every bit
//   pattern must correspond to a different enum variant. Thus, for an enum
//   whose layout takes up N bytes, there must be 2^N variants.
// - Since we must know N, only representations which guarantee the layout's
//   size are allowed. These are `repr(uN)` and `repr(iN)` (`repr(C)` implies an
//   implementation-defined size). `usize` and `isize` technically guarantee the
//   layout's size, but would require us to know how large those are on the
//   target platform. This isn't terribly difficult - we could emit a const
//   expression that could call `core::mem::size_of` in order to determine the
//   size and check against the number of enum variants, but a) this would be
//   platform-specific and, b) even on Rust's smallest bit width platform (32),
//   this would require ~4 billion enum variants, which obviously isn't a thing.

fn derive_from_bytes_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_fieldless() {
        return Error::new_spanned(ast, "only field-less enums can implement FromBytes")
            .to_compile_error();
    }

    let reprs = try_or_print!(ENUM_FROM_BYTES_CFG.validate_reprs(ast));

    let variants_required = 1usize
        << enum_size_from_repr(reprs.as_slice())
            .expect("internal error: `validate_reprs` has already validated that the reprs guarantee the enum's size");
    if enm.variants.len() != variants_required {
        return Error::new_spanned(
            ast,
            format!(
                "FromBytes only supported on {} enum with {} variants",
                reprs[0], variants_required
            ),
        )
        .to_compile_error();
    }

    impl_block(ast, enm, Trait::FromBytes, FieldBounds::ALL_SELF, SelfBounds::None, None, None)
}

// Returns `None` if the enum's size is not guaranteed by the repr.
fn enum_size_from_repr(reprs: &[EnumRepr]) -> Option<usize> {
    match reprs {
        [EnumRepr::U8] | [EnumRepr::I8] => Some(8),
        [EnumRepr::U16] | [EnumRepr::I16] => Some(16),
        _ => None,
    }
}

#[rustfmt::skip]
const ENUM_FROM_BYTES_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        allowed_combinations_message: r#"FromBytes requires repr of "u8", "u16", "i8", or "i16""#,
        derive_unaligned: false,
        allowed_combinations: &[
            &[U8],
            &[U16],
            &[I8],
            &[I16],
        ],
        disallowed_but_legal_combinations: &[
            &[C],
            &[U32],
            &[I32],
            &[U64],
            &[I64],
            &[Usize],
            &[Isize],
        ],
    }
};

// Unions are `FromBytes` if
// - all fields are `FromBytes` and `NoCell`

fn derive_from_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#5): Remove the `NoCell` bound. It's only necessary for
    // compatibility with `derive(TryFromBytes)` on unions; not for soundness.
    let field_type_trait_bounds =
        FieldBounds::All(&[TraitBound::Slf, TraitBound::Other(Trait::NoCell)]);
    impl_block(ast, unn, Trait::FromBytes, field_type_trait_bounds, SelfBounds::None, None, None)
}

fn derive_into_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_INTO_BYTES_CFG.validate_reprs(ast));
    let is_transparent = reprs.contains(&StructRepr::Transparent);
    let is_packed = reprs.contains(&StructRepr::Packed);
    let num_fields = strct.fields().len();

    let (padding_check, require_unaligned_fields) = if is_transparent || is_packed {
        // No padding check needed.
        // - repr(transparent): The layout and ABI of the whole struct is the
        //   same as its only non-ZST field (meaning there's no padding outside
        //   of that field) and we require that field to be `IntoBytes` (meaning
        //   there's no padding in that field).
        // - repr(packed): Any inter-field padding bytes are removed, meaning
        //   that any padding bytes would need to come from the fields, all of
        //   which we require to be `IntoBytes` (meaning they don't have any
        //   padding).
        (None, false)
    } else if reprs.contains(&StructRepr::C) && num_fields <= 1 {
        // No padding check needed. A repr(C) struct with zero or one field has
        // no padding.
        (None, false)
    } else if ast.generics.params.is_empty() {
        // Since there are no generics, we can emit a padding check. This is
        // more permissive than the next case, which requires that all field
        // types implement `Unaligned`.
        (Some(PaddingCheck::Struct), false)
    } else {
        // Based on the allowed reprs, we know that this type must be repr(C) by
        // the time we get here, but the soundness of this impl relies on it, so
        // let's double-check.
        assert!(reprs.contains(&StructRepr::C));
        // We can't use a padding check since there are generic type arguments.
        // Instead, we require all field types to implement `Unaligned`. This
        // ensures that the `repr(C)` layout algorithm will not insert any
        // padding.
        //
        // TODO(#10): Support type parameters for non-transparent, non-packed
        // structs without requiring `Unaligned`.
        (None, true)
    };

    let field_bounds = if require_unaligned_fields {
        FieldBounds::All(&[TraitBound::Slf, TraitBound::Other(Trait::Unaligned)])
    } else {
        FieldBounds::ALL_SELF
    };

    impl_block(ast, strct, Trait::IntoBytes, field_bounds, SelfBounds::None, padding_check, None)
}

const STRUCT_UNION_INTO_BYTES_CFG: Config<StructRepr> = Config {
    // Since `disallowed_but_legal_combinations` is empty, this message will
    // never actually be emitted.
    allowed_combinations_message: r#"IntoBytes requires either a) repr "C" or "transparent" with all fields implementing IntoBytes or, b) repr "packed""#,
    derive_unaligned: false,
    allowed_combinations: STRUCT_UNION_ALLOWED_REPR_COMBINATIONS,
    disallowed_but_legal_combinations: &[],
};

// An enum is `IntoBytes` if it is field-less and has a defined repr.

fn derive_into_bytes_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_fieldless() {
        return Error::new_spanned(ast, "only field-less enums can implement IntoBytes")
            .to_compile_error();
    }

    // We don't care what the repr is; we only care that it is one of the
    // allowed ones.
    try_or_print!(ENUM_FROM_ZEROS_INTO_BYTES_CFG.validate_reprs(ast));
    impl_block(ast, enm, Trait::IntoBytes, FieldBounds::None, SelfBounds::None, None, None)
}

#[rustfmt::skip]
const ENUM_FROM_ZEROS_INTO_BYTES_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        // Since `disallowed_but_legal_combinations` is empty, this message will
        // never actually be emitted.
        allowed_combinations_message: r#"Deriving this trait requires repr of "C", "u8", "u16", "u32", "u64", "usize", "i8", "i16", "i32", "i64", or "isize""#,
        derive_unaligned: false,
        allowed_combinations: &[
            &[C],
            &[U8],
            &[U16],
            &[I8],
            &[I16],
            &[U32],
            &[I32],
            &[U64],
            &[I64],
            &[Usize],
            &[Isize],
        ],
        disallowed_but_legal_combinations: &[],
    }
};

// A union is `IntoBytes` if:
// - all fields are `IntoBytes`
// - `repr(C)`, `repr(transparent)`, or `repr(packed)`
// - no padding (size of union equals size of each field type)

fn derive_into_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#10): Support type parameters.
    if !ast.generics.params.is_empty() {
        return Error::new(Span::call_site(), "unsupported on types with type parameters")
            .to_compile_error();
    }

    try_or_print!(STRUCT_UNION_INTO_BYTES_CFG.validate_reprs(ast));

    impl_block(
        ast,
        unn,
        Trait::IntoBytes,
        FieldBounds::ALL_SELF,
        SelfBounds::None,
        Some(PaddingCheck::Union),
        None,
    )
}

// A struct is `Unaligned` if:
// - `repr(align)` is no more than 1 and either
//   - `repr(C)` or `repr(transparent)` and
//     - all fields `Unaligned`
//   - `repr(packed)`

fn derive_unaligned_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_UNALIGNED_CFG.validate_reprs(ast));
    let field_bounds = if !reprs.contains(&StructRepr::Packed) {
        FieldBounds::ALL_SELF
    } else {
        FieldBounds::None
    };

    impl_block(ast, strct, Trait::Unaligned, field_bounds, SelfBounds::None, None, None)
}

const STRUCT_UNION_UNALIGNED_CFG: Config<StructRepr> = Config {
    // Since `disallowed_but_legal_combinations` is empty, this message will
    // never actually be emitted.
    allowed_combinations_message: r#"Unaligned requires either a) repr "C" or "transparent" with all fields implementing Unaligned or, b) repr "packed""#,
    derive_unaligned: true,
    allowed_combinations: STRUCT_UNION_ALLOWED_REPR_COMBINATIONS,
    disallowed_but_legal_combinations: &[],
};

// An enum is `Unaligned` if:
// - No `repr(align(N > 1))`
// - `repr(u8)` or `repr(i8)`

fn derive_unaligned_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_fieldless() {
        return Error::new_spanned(ast, "only field-less enums can implement Unaligned")
            .to_compile_error();
    }

    // The only valid reprs are `u8` and `i8`, and optionally `align(1)`. We
    // don't actually care what the reprs are so long as they satisfy that
    // requirement.
    let _: Vec<repr::EnumRepr> = try_or_print!(ENUM_UNALIGNED_CFG.validate_reprs(ast));

    // field-less enums cannot currently have type parameters, so this value of
    // true for `require_trait_bound_on_field_types` doesn't really do anything.
    // But it's marginally more future-proof in case that restriction is lifted
    // in the future.
    impl_block(ast, enm, Trait::Unaligned, FieldBounds::ALL_SELF, SelfBounds::None, None, None)
}

#[rustfmt::skip]
const ENUM_UNALIGNED_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        allowed_combinations_message:
            r#"Unaligned requires repr of "u8" or "i8", and no alignment (i.e., repr(align(N > 1)))"#,
        derive_unaligned: true,
        allowed_combinations: &[
            &[U8],
            &[I8],
        ],
        disallowed_but_legal_combinations: &[
            &[C],
            &[U16],
            &[U32],
            &[U64],
            &[Usize],
            &[I16],
            &[I32],
            &[I64],
            &[Isize],
        ],
    }
};

// Like structs, a union is `Unaligned` if:
// - `repr(align)` is no more than 1 and either
//   - `repr(C)` or `repr(transparent)` and
//     - all fields `Unaligned`
//   - `repr(packed)`

fn derive_unaligned_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_UNALIGNED_CFG.validate_reprs(ast));
    let field_type_trait_bounds = if !reprs.contains(&StructRepr::Packed) {
        FieldBounds::ALL_SELF
    } else {
        FieldBounds::None
    };

    impl_block(ast, unn, Trait::Unaligned, field_type_trait_bounds, SelfBounds::None, None, None)
}

// This enum describes what kind of padding check needs to be generated for the
// associated impl.
enum PaddingCheck {
    // Check that the sum of the fields' sizes exactly equals the struct's size.
    Struct,
    // Check that the size of each field exactly equals the union's size.
    Union,
}

impl PaddingCheck {
    /// Returns the ident of the macro to call in order to validate that a type
    /// passes the padding check encoded by `PaddingCheck`.
    fn validator_macro_ident(&self) -> Ident {
        let s = match self {
            PaddingCheck::Struct => "struct_has_padding",
            PaddingCheck::Union => "union_has_padding",
        };

        Ident::new(s, Span::call_site())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Trait {
    KnownLayout,
    NoCell,
    TryFromBytes,
    FromZeros,
    FromBytes,
    IntoBytes,
    Unaligned,
    Sized,
}

impl Trait {
    fn path(&self) -> Path {
        let span = Span::call_site();
        let root = if *self == Self::Sized {
            quote_spanned!(span=> ::zerocopy::macro_util::core_reexport::marker)
        } else {
            quote_spanned!(span=> ::zerocopy)
        };
        let ident = Ident::new(&format!("{:?}", self), span);
        parse_quote_spanned! {span=> #root::#ident}
    }
}

#[derive(Debug, Eq, PartialEq)]
enum TraitBound {
    Slf,
    Other(Trait),
}

#[derive(Debug, Eq, PartialEq)]
enum FieldBounds<'a> {
    None,
    All(&'a [TraitBound]),
    Trailing(&'a [TraitBound]),
}

impl<'a> FieldBounds<'a> {
    const ALL_SELF: FieldBounds<'a> = FieldBounds::All(&[TraitBound::Slf]);
    const TRAILING_SELF: FieldBounds<'a> = FieldBounds::Trailing(&[TraitBound::Slf]);
}

#[derive(Debug, Eq, PartialEq)]
enum SelfBounds<'a> {
    None,
    All(&'a [Trait]),
}

impl<'a> SelfBounds<'a> {
    const SIZED: Self = Self::All(&[Trait::Sized]);
}

/// Normalizes a slice of bounds by replacing [`TraitBound::Slf`] with `slf`.
fn normalize_bounds(slf: Trait, bounds: &[TraitBound]) -> impl '_ + Iterator<Item = Trait> {
    bounds.iter().map(move |bound| match bound {
        TraitBound::Slf => slf,
        TraitBound::Other(trt) => *trt,
    })
}

fn impl_block<D: DataExt>(
    input: &DeriveInput,
    data: &D,
    trt: Trait,
    field_type_trait_bounds: FieldBounds,
    self_type_trait_bounds: SelfBounds,
    padding_check: Option<PaddingCheck>,
    extras: Option<proc_macro2::TokenStream>,
) -> proc_macro2::TokenStream {
    // In this documentation, we will refer to this hypothetical struct:
    //
    //   #[derive(FromBytes)]
    //   struct Foo<T, I: Iterator>
    //   where
    //       T: Copy,
    //       I: Clone,
    //       I::Item: Clone,
    //   {
    //       a: u8,
    //       b: T,
    //       c: I::Item,
    //   }
    //
    // We extract the field types, which in this case are `u8`, `T`, and
    // `I::Item`. We re-use the existing parameters and where clauses. If
    // `require_trait_bound == true` (as it is for `FromBytes), we add where
    // bounds for each field's type:
    //
    //   impl<T, I: Iterator> FromBytes for Foo<T, I>
    //   where
    //       T: Copy,
    //       I: Clone,
    //       I::Item: Clone,
    //       T: FromBytes,
    //       I::Item: FromBytes,
    //   {
    //   }
    //
    // NOTE: It is standard practice to only emit bounds for the type parameters
    // themselves, not for field types based on those parameters (e.g., `T` vs
    // `T::Foo`). For a discussion of why this is standard practice, see
    // https://github.com/rust-lang/rust/issues/26925.
    //
    // The reason we diverge from this standard is that doing it that way for us
    // would be unsound. E.g., consider a type, `T` where `T: FromBytes` but
    // `T::Foo: !FromBytes`. It would not be sound for us to accept a type with
    // a `T::Foo` field as `FromBytes` simply because `T: FromBytes`.
    //
    // While there's no getting around this requirement for us, it does have the
    // pretty serious downside that, when lifetimes are involved, the trait
    // solver ties itself in knots:
    //
    //     #[derive(Unaligned)]
    //     #[repr(C)]
    //     struct Dup<'a, 'b> {
    //         a: PhantomData<&'a u8>,
    //         b: PhantomData<&'b u8>,
    //     }
    //
    //     error[E0283]: type annotations required: cannot resolve `core::marker::PhantomData<&'a u8>: zerocopy::Unaligned`
    //      --> src/main.rs:6:10
    //       |
    //     6 | #[derive(Unaligned)]
    //       |          ^^^^^^^^^
    //       |
    //       = note: required by `zerocopy::Unaligned`

    let type_ident = &input.ident;
    let trait_path = trt.path();
    let fields = data.fields();

    fn bound_tt(ty: &Type, traits: impl Iterator<Item = Trait>) -> WherePredicate {
        let traits = traits.map(|t| t.path());
        parse_quote!(#ty: #(#traits)+*)
    }
    let field_type_bounds: Vec<_> = match (field_type_trait_bounds, &fields[..]) {
        (FieldBounds::All(traits), _) => {
            fields.iter().map(|(_name, ty)| bound_tt(ty, normalize_bounds(trt, traits))).collect()
        }
        (FieldBounds::None, _) | (FieldBounds::Trailing(..), []) => vec![],
        (FieldBounds::Trailing(traits), [.., last]) => {
            vec![bound_tt(last.1, normalize_bounds(trt, traits))]
        }
    };

    // Don't bother emitting a padding check if there are no fields.
    #[allow(unstable_name_collisions)] // See `BoolExt` below
    #[allow(clippy::incompatible_msrv)] // Work around https://github.com/rust-lang/rust-clippy/issues/12280
    let padding_check_bound = padding_check.and_then(|check| (!fields.is_empty()).then_some(check)).map(|check| {
        let fields = fields.iter().map(|(_name, ty)| ty);
        let validator_macro = check.validator_macro_ident();
        parse_quote!(
            ::zerocopy::macro_util::HasPadding<#type_ident, {::zerocopy::#validator_macro!(#type_ident, #(#fields),*)}>:
                ::zerocopy::macro_util::ShouldBe<false>
        )
    });

    let self_bounds: Option<WherePredicate> = match self_type_trait_bounds {
        SelfBounds::None => None,
        SelfBounds::All(traits) => Some(bound_tt(&parse_quote!(Self), traits.iter().copied())),
    };

    let bounds = input
        .generics
        .where_clause
        .as_ref()
        .map(|where_clause| where_clause.predicates.iter())
        .into_iter()
        .flatten()
        .chain(field_type_bounds.iter())
        .chain(padding_check_bound.iter())
        .chain(self_bounds.iter());

    // The parameters with trait bounds, but without type defaults.
    let params = input.generics.params.clone().into_iter().map(|mut param| {
        match &mut param {
            GenericParam::Type(ty) => ty.default = None,
            GenericParam::Const(cnst) => cnst.default = None,
            GenericParam::Lifetime(_) => {}
        }
        quote!(#param)
    });

    // The identifiers of the parameters without trait bounds or type defaults.
    let param_idents = input.generics.params.iter().map(|param| match param {
        GenericParam::Type(ty) => {
            let ident = &ty.ident;
            quote!(#ident)
        }
        GenericParam::Lifetime(l) => {
            let ident = &l.lifetime;
            quote!(#ident)
        }
        GenericParam::Const(cnst) => {
            let ident = &cnst.ident;
            quote!({#ident})
        }
    });

    quote! {
        // TODO(#553): Add a test that generates a warning when
        // `#[allow(deprecated)]` isn't present.
        #[allow(deprecated)]
        unsafe impl < #(#params),* > #trait_path for #type_ident < #(#param_idents),* >
        where
            #(#bounds,)*
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}

            #extras
        }
    }
}

fn print_all_errors(errors: Vec<Error>) -> proc_macro2::TokenStream {
    errors.iter().map(Error::to_compile_error).collect()
}

// A polyfill for `Option::then_some`, which was added after our MSRV.
//
// The `#[allow(unused)]` is necessary because, on sufficiently recent toolchain
// versions, `b.then_some(...)` resolves to the inherent method rather than to
// this trait, and so this trait is considered unused.
//
// TODO(#67): Remove this once our MSRV is >= 1.62.
#[allow(unused)]
trait BoolExt {
    fn then_some<T>(self, t: T) -> Option<T>;
}

impl BoolExt for bool {
    fn then_some<T>(self, t: T) -> Option<T> {
        if self {
            Some(t)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_repr_orderings() {
        // Validate that the repr lists in the various configs are in the
        // canonical order. If they aren't, then our algorithm to look up in
        // those lists won't work.

        // TODO(https://github.com/rust-lang/rust/issues/53485): Remove once
        // `Vec::is_sorted` is stabilized.
        fn is_sorted_and_deduped<T: Clone + Ord>(ts: &[T]) -> bool {
            let mut sorted = ts.to_vec();
            sorted.sort();
            sorted.dedup();
            ts == sorted.as_slice()
        }

        fn elements_are_sorted_and_deduped<T: Clone + Ord>(lists: &[&[T]]) -> bool {
            lists.iter().all(|list| is_sorted_and_deduped(list))
        }

        fn config_is_sorted<T: KindRepr + Clone>(config: &Config<T>) -> bool {
            elements_are_sorted_and_deduped(config.allowed_combinations)
                && elements_are_sorted_and_deduped(config.disallowed_but_legal_combinations)
        }

        assert!(config_is_sorted(&STRUCT_UNION_UNALIGNED_CFG));
        assert!(config_is_sorted(&ENUM_FROM_BYTES_CFG));
        assert!(config_is_sorted(&ENUM_UNALIGNED_CFG));
    }

    #[test]
    fn test_config_repr_no_overlap() {
        // Validate that no set of reprs appears in both the
        // `allowed_combinations` and `disallowed_but_legal_combinations` lists.

        fn overlap<T: Eq>(a: &[T], b: &[T]) -> bool {
            a.iter().any(|elem| b.contains(elem))
        }

        fn config_overlaps<T: KindRepr + Eq>(config: &Config<T>) -> bool {
            overlap(config.allowed_combinations, config.disallowed_but_legal_combinations)
        }

        assert!(!config_overlaps(&STRUCT_UNION_UNALIGNED_CFG));
        assert!(!config_overlaps(&ENUM_FROM_BYTES_CFG));
        assert!(!config_overlaps(&ENUM_UNALIGNED_CFG));
    }
}
