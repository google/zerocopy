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

use {
    proc_macro2::Span,
    quote::quote,
    syn::{
        parse_quote, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Error, Expr, ExprLit,
        GenericParam, Ident, Lit,
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

#[proc_macro_derive(KnownLayout)]
pub fn derive_known_layout(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);

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

    let (require_self_sized, extras) = if let (
        Some(reprs),
        Some((trailing_field, leading_fields)),
    ) = (is_repr_c_struct, fields.split_last())
    {
        let (_name, trailing_field_ty) = trailing_field;
        let leading_fields_tys = leading_fields.iter().map(|(_name, ty)| ty);

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
            .map(|repr_align| quote!(NonZeroUsize::new(#repr_align as usize)))
            .unwrap_or(quote!(None));

        let repr_packed = reprs
            .iter()
            .find_map(|(_meta, repr)| match repr {
                Repr::Packed => Some(1),
                Repr::PackedN(repr_packed) => Some(*repr_packed),
                _ => None,
            })
            .map(|repr_packed| quote!(NonZeroUsize::new(#repr_packed as usize)))
            .unwrap_or(quote!(None));

        (
            false,
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
            true,
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
            let require_trait_bound_on_field_types = if require_self_sized {
                RequireBoundedFields::No
            } else {
                RequireBoundedFields::Trailing
            };

            // A bound on the trailing field is required, since structs are
            // unsized if their trailing field is unsized. Reflecting the layout
            // of an usized trailing field requires that the field is
            // `KnownLayout`.
            impl_block(
                &ast,
                strct,
                Trait::KnownLayout,
                require_trait_bound_on_field_types,
                require_self_sized,
                None,
                Some(extras),
            )
        }
        Data::Enum(enm) => {
            // A bound on the trailing field is not required, since enums cannot
            // currently be unsized.
            impl_block(
                &ast,
                enm,
                Trait::KnownLayout,
                RequireBoundedFields::No,
                true,
                None,
                Some(extras),
            )
        }
        Data::Union(unn) => {
            // A bound on the trailing field is not required, since unions
            // cannot currently be unsized.
            impl_block(
                &ast,
                unn,
                Trait::KnownLayout,
                RequireBoundedFields::No,
                true,
                None,
                Some(extras),
            )
        }
    }
    .into()
}

#[proc_macro_derive(NoCell)]
pub fn derive_no_cell(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => {
            impl_block(&ast, strct, Trait::NoCell, RequireBoundedFields::Yes, false, None, None)
        }
        Data::Enum(enm) => {
            impl_block(&ast, enm, Trait::NoCell, RequireBoundedFields::Yes, false, None, None)
        }
        Data::Union(unn) => {
            impl_block(&ast, unn, Trait::NoCell, RequireBoundedFields::Yes, false, None, None)
        }
    }
    .into()
}

#[proc_macro_derive(TryFromBytes)]
pub fn derive_try_from_bytes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_try_from_bytes_struct(&ast, strct),
        Data::Enum(enm) => derive_try_from_bytes_enum(&ast, enm),
        Data::Union(unn) => derive_try_from_bytes_union(&ast, unn),
    }
    .into()
}

#[proc_macro_derive(FromZeros)]
pub fn derive_from_zeros(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_from_zeros_struct(&ast, strct),
        Data::Enum(enm) => derive_from_zeros_enum(&ast, enm),
        Data::Union(unn) => derive_from_zeros_union(&ast, unn),
    }
    .into()
}

/// Deprecated: prefer [`FromZeros`] instead.
#[deprecated(since = "0.8.0", note = "`FromZeroes` was renamed to `FromZeros`")]
#[doc(hidden)]
#[proc_macro_derive(FromZeroes)]
pub fn derive_from_zeroes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive_from_zeros(ts)
}

#[proc_macro_derive(FromBytes)]
pub fn derive_from_bytes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_from_bytes_struct(&ast, strct),
        Data::Enum(enm) => derive_from_bytes_enum(&ast, enm),
        Data::Union(unn) => derive_from_bytes_union(&ast, unn),
    }
    .into()
}

#[proc_macro_derive(IntoBytes)]
pub fn derive_as_bytes(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_as_bytes_struct(&ast, strct),
        Data::Enum(enm) => derive_as_bytes_enum(&ast, enm),
        Data::Union(unn) => derive_as_bytes_union(&ast, unn),
    }
    .into()
}

#[proc_macro_derive(Unaligned)]
pub fn derive_unaligned(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse_macro_input!(ts as DeriveInput);
    match &ast.data {
        Data::Struct(strct) => derive_unaligned_struct(&ast, strct),
        Data::Enum(enm) => derive_unaligned_enum(&ast, enm),
        Data::Union(unn) => derive_unaligned_union(&ast, unn),
    }
    .into()
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
            fn is_bit_valid(candidate: zerocopy::Maybe<Self>) -> bool {
                true #(&& {
                    // SAFETY: `project` is a field projection of `candidate`,
                    // and `Self` is a struct type.
                    let field_candidate = unsafe {
                        let project = |slf: *mut Self|
                            ::core::ptr::addr_of_mut!((*slf).#field_names);

                        candidate.project(project)
                    };

                    <#field_tys as zerocopy::TryFromBytes>::is_bit_valid(field_candidate)
                })*
            }
        )
    });
    impl_block(ast, strct, Trait::TryFromBytes, RequireBoundedFields::Yes, false, None, extras)
}

// A union is `TryFromBytes` if:
// - any of its fields are `TryFromBytes`

fn derive_try_from_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
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
            fn is_bit_valid(candidate: zerocopy::Maybe<Self>) -> bool {
                false #(|| {
                    // SAFETY: `project` is a field projection of `candidate`,
                    // and `Self` is a union type.
                    let field_candidate = unsafe {
                        let project = |slf: *mut Self|
                            ::core::ptr::addr_of_mut!((*slf).#field_names);

                        candidate.project(project)
                    };

                    <#field_tys as zerocopy::TryFromBytes>::is_bit_valid(field_candidate)
                })*
            }
        )
    });
    impl_block(ast, unn, Trait::TryFromBytes, RequireBoundedFields::Yes, false, None, extras)
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

    // We don't actually care what the repr is; we just care that it's one of
    // the allowed ones.
    try_or_print!(ENUM_TRY_FROM_BYTES_CFG.validate_reprs(ast));
    let variant_names = enm.variants.iter().map(|v| &v.ident);
    let extras = Some(quote!(
        // SAFETY: We use `is_bit_valid` to validate that the bit pattern
        // corresponds to one of the field-less enum's variant discriminants.
        // Thus, this is a sound implementation of `is_bit_valid`.
        fn is_bit_valid(
            candidate: ::zerocopy::Ptr<
                '_,
                Self,
                (
                    ::zerocopy::pointer::invariant::Shared,
                    ::zerocopy::pointer::invariant::AnyAlignment,
                    ::zerocopy::pointer::invariant::AsInitialized,
                ),
            >,
        ) -> ::zerocopy::macro_util::core_reexport::primitive::bool {
            use ::zerocopy::macro_util::core_reexport;
            // SAFETY:
            // - `cast` is implemented as required.
            // - By definition, `*mut Self` and `*mut [u8; size_of::<Self>()]`
            //   are types of the same size.
            let discriminant = unsafe { candidate.cast_unsized(|p: *mut Self| p as *mut [core_reexport::primitive::u8; core_reexport::mem::size_of::<Self>()]) };
            // SAFETY: Since `candidate` has the invariant `AsInitialized`, we
            // know that `candidate`'s referent (and thus `discriminant`'s
            // referent) is as-initialized as `Self`. Since all of the allowed
            // `repr`s are types for which all bytes are always initialized, we
            // know that `discriminant`'s referent has all of its bytes
            // initialized. Since `[u8; N]`'s validity invariant is just that
            // all of its bytes are initialized, we know that `discriminant`'s
            // referent is bit-valid.
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
        }
    ));
    impl_block(ast, enm, Trait::TryFromBytes, RequireBoundedFields::Yes, false, None, extras)
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
    impl_block(ast, strct, Trait::FromZeros, RequireBoundedFields::Yes, false, None, None)
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
    try_or_print!(ENUM_FROM_ZEROS_AS_BYTES_CFG.validate_reprs(ast));

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

    impl_block(ast, enm, Trait::FromZeros, RequireBoundedFields::Yes, false, None, None)
}

// Like structs, unions are `FromZeros` if
// - all fields are `FromZeros`

fn derive_from_zeros_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    impl_block(ast, unn, Trait::FromZeros, RequireBoundedFields::Yes, false, None, None)
}

// A struct is `FromBytes` if:
// - all fields are `FromBytes`

fn derive_from_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    impl_block(ast, strct, Trait::FromBytes, RequireBoundedFields::Yes, false, None, None)
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

    let variants_required = match reprs.as_slice() {
        [EnumRepr::U8] | [EnumRepr::I8] => 1usize << 8,
        [EnumRepr::U16] | [EnumRepr::I16] => 1usize << 16,
        // `validate_reprs` has already validated that it's one of the preceding
        // patterns.
        _ => unreachable!(),
    };
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

    impl_block(ast, enm, Trait::FromBytes, RequireBoundedFields::Yes, false, None, None)
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

// Like structs, unions are `FromBytes` if
// - all fields are `FromBytes`

fn derive_from_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    impl_block(ast, unn, Trait::FromBytes, RequireBoundedFields::Yes, false, None, None)
}

// A struct is `IntoBytes` if:
// - all fields are `IntoBytes`
// - `repr(C)` or `repr(transparent)` and
//   - no padding (size of struct equals sum of size of field types)
// - `repr(packed)`

fn derive_as_bytes_struct(ast: &DeriveInput, strct: &DataStruct) -> proc_macro2::TokenStream {
    let reprs = try_or_print!(STRUCT_UNION_AS_BYTES_CFG.validate_reprs(ast));
    let is_transparent = reprs.contains(&StructRepr::Transparent);
    let is_packed = reprs.contains(&StructRepr::Packed);

    // TODO(#10): Support type parameters for non-transparent, non-packed
    // structs.
    if !ast.generics.params.is_empty() && !is_transparent && !is_packed {
        return Error::new(
            Span::call_site(),
            "unsupported on generic structs that are not repr(transparent) or repr(packed)",
        )
        .to_compile_error();
    }

    // We don't need a padding check if the struct is repr(transparent) or
    // repr(packed).
    // - repr(transparent): The layout and ABI of the whole struct is the same
    //   as its only non-ZST field (meaning there's no padding outside of that
    //   field) and we require that field to be `IntoBytes` (meaning there's no
    //   padding in that field).
    // - repr(packed): Any inter-field padding bytes are removed, meaning that
    //   any padding bytes would need to come from the fields, all of which
    //   we require to be `IntoBytes` (meaning they don't have any padding).
    let padding_check = if is_transparent || is_packed { None } else { Some(PaddingCheck::Struct) };
    impl_block(ast, strct, Trait::IntoBytes, RequireBoundedFields::Yes, false, padding_check, None)
}

const STRUCT_UNION_AS_BYTES_CFG: Config<StructRepr> = Config {
    // Since `disallowed_but_legal_combinations` is empty, this message will
    // never actually be emitted.
    allowed_combinations_message: r#"IntoBytes requires either a) repr "C" or "transparent" with all fields implementing IntoBytes or, b) repr "packed""#,
    derive_unaligned: false,
    allowed_combinations: STRUCT_UNION_ALLOWED_REPR_COMBINATIONS,
    disallowed_but_legal_combinations: &[],
};

// An enum is `IntoBytes` if it is field-less and has a defined repr.

fn derive_as_bytes_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    if !enm.is_fieldless() {
        return Error::new_spanned(ast, "only field-less enums can implement IntoBytes")
            .to_compile_error();
    }

    // We don't care what the repr is; we only care that it is one of the
    // allowed ones.
    try_or_print!(ENUM_FROM_ZEROS_AS_BYTES_CFG.validate_reprs(ast));
    impl_block(ast, enm, Trait::IntoBytes, RequireBoundedFields::No, false, None, None)
}

#[rustfmt::skip]
const ENUM_FROM_ZEROS_AS_BYTES_CFG: Config<EnumRepr> = {
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

fn derive_as_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#10): Support type parameters.
    if !ast.generics.params.is_empty() {
        return Error::new(Span::call_site(), "unsupported on types with type parameters")
            .to_compile_error();
    }

    try_or_print!(STRUCT_UNION_AS_BYTES_CFG.validate_reprs(ast));

    impl_block(
        ast,
        unn,
        Trait::IntoBytes,
        RequireBoundedFields::Yes,
        false,
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
    let require_trait_bounds_on_field_types = (!reprs.contains(&StructRepr::Packed)).into();

    impl_block(ast, strct, Trait::Unaligned, require_trait_bounds_on_field_types, false, None, None)
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
    impl_block(ast, enm, Trait::Unaligned, RequireBoundedFields::Yes, false, None, None)
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
    let require_trait_bound_on_field_types = (!reprs.contains(&StructRepr::Packed)).into();

    impl_block(ast, unn, Trait::Unaligned, require_trait_bound_on_field_types, false, None, None)
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

#[derive(Debug, Eq, PartialEq)]
enum Trait {
    KnownLayout,
    NoCell,
    TryFromBytes,
    FromZeros,
    FromBytes,
    IntoBytes,
    Unaligned,
}

impl Trait {
    fn ident(&self) -> Ident {
        Ident::new(format!("{:?}", self).as_str(), Span::call_site())
    }
}

#[derive(Debug, Eq, PartialEq)]
enum RequireBoundedFields {
    No,
    Yes,
    Trailing,
}

impl From<bool> for RequireBoundedFields {
    fn from(do_require: bool) -> Self {
        match do_require {
            true => Self::Yes,
            false => Self::No,
        }
    }
}

fn impl_block<D: DataExt>(
    input: &DeriveInput,
    data: &D,
    trt: Trait,
    require_trait_bound_on_field_types: RequireBoundedFields,
    require_self_sized: bool,
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
    let trait_ident = trt.ident();
    let fields = data.fields();

    let bound_tt = |ty| parse_quote!(#ty: ::zerocopy::#trait_ident);
    let field_type_bounds: Vec<_> = match (require_trait_bound_on_field_types, &fields[..]) {
        (RequireBoundedFields::Yes, _) => fields.iter().map(|(_name, ty)| bound_tt(ty)).collect(),
        (RequireBoundedFields::No, _) | (RequireBoundedFields::Trailing, []) => vec![],
        (RequireBoundedFields::Trailing, [.., last]) => vec![bound_tt(&last.1)],
    };

    // Don't bother emitting a padding check if there are no fields.
    #[allow(unstable_name_collisions)] // See `BoolExt` below
    let padding_check_bound = padding_check.and_then(|check| (!fields.is_empty()).then_some(check)).map(|check| {
        let fields = fields.iter().map(|(_name, ty)| ty);
        let validator_macro = check.validator_macro_ident();
        parse_quote!(
            ::zerocopy::macro_util::HasPadding<#type_ident, {::zerocopy::#validator_macro!(#type_ident, #(#fields),*)}>:
                ::zerocopy::macro_util::ShouldBe<false>
        )
    });

    let self_sized_bound = if require_self_sized { Some(parse_quote!(Self: Sized)) } else { None };

    let bounds = input
        .generics
        .where_clause
        .as_ref()
        .map(|where_clause| where_clause.predicates.iter())
        .into_iter()
        .flatten()
        .chain(field_type_bounds.iter())
        .chain(padding_check_bound.iter())
        .chain(self_sized_bound.iter());

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
        unsafe impl < #(#params),* > ::zerocopy::#trait_ident for #type_ident < #(#param_idents),* >
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
// TODO(#67): Remove this once our MSRV is >= 1.62.
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
