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

mod r#enum;
mod ext;
mod repr;

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::{punctuated::Punctuated, token::Colon, PredicateType};

use {
    proc_macro2::Span,
    quote::quote,
    syn::{
        parse_quote, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Error, Expr, ExprLit,
        ExprUnary, GenericParam, Ident, Lit, Path, Type, UnOp, WherePredicate,
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
derive!(Immutable => derive_no_cell => derive_no_cell_inner);
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

        let core_path = quote!(::zerocopy::util::macro_util::core_reexport);
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
                type PointerMetadata = <#trailing_field_ty as ::zerocopy::KnownLayout>::PointerMetadata;

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
                    use ::zerocopy::util::macro_util::core_reexport::num::NonZeroUsize;
                    use ::zerocopy::{DstLayout, KnownLayout};

                    let repr_align = #repr_align;
                    let repr_packed = #repr_packed;

                    DstLayout::new_zst(repr_align)
                        #(.extend(DstLayout::for_type::<#leading_fields_tys>(), repr_packed))*
                        .extend(<#trailing_field_ty as KnownLayout>::LAYOUT, repr_packed)
                        .pad_to_align()
                };

                // SAFETY:
                // - The returned pointer has the same address and provenance as
                //   `bytes`:
                //   - The recursive call to `raw_from_ptr_len` preserves both
                //     address and provenance.
                //   - The `as` cast preserves both address and provenance.
                //   - `NonNull::new_unchecked` preserves both address and
                //     provenance.
                // - If `Self` is a slice DST, the returned pointer encodes
                //   `elems` elements in the trailing slice:
                //   - This is true of the recursive call to `raw_from_ptr_len`.
                //   - `trailing.as_ptr() as *mut Self` preserves trailing slice
                //     element count [1].
                //   - `NonNull::new_unchecked` preserves trailing slice element
                //     count.
                //
                // [1] Per https://doc.rust-lang.org/reference/expressions/operator-expr.html#pointer-to-pointer-cast:
                //
                //   `*const T`` / `*mut T` can be cast to `*const U` / `*mut U`
                //   with the following behavior:
                //     ...
                //     - If `T` and `U` are both unsized, the pointer is also
                //       returned unchanged. In particular, the metadata is
                //       preserved exactly.
                //
                //       For instance, a cast from `*const [T]` to `*const [U]`
                //       preserves the number of elements. ... The same holds
                //       for str and any compound type whose unsized tail is a
                //       slice type, such as struct `Foo(i32, [u8])` or `(u64, Foo)`.
                #[inline(always)]
                fn raw_from_ptr_len(
                    bytes: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<u8>,
                    meta: Self::PointerMetadata,
                ) -> ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self> {
                    use ::zerocopy::KnownLayout;
                    let trailing = <#trailing_field_ty as KnownLayout>::raw_from_ptr_len(bytes, meta);
                    let slf = trailing.as_ptr() as *mut Self;
                    // SAFETY: Constructed from `trailing`, which is non-null.
                    unsafe { ::zerocopy::util::macro_util::core_reexport::ptr::NonNull::new_unchecked(slf) }
                }

                #[inline(always)]
                fn pointer_to_metadata(ptr: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self>) -> Self::PointerMetadata {
                    // SAFETY: `ptr` is non-null.
                    let ptr = unsafe { ::zerocopy::util::macro_util::core_reexport::ptr::NonNull::new_unchecked(ptr.as_ptr() as *mut _) };
                    <#trailing_field_ty>::pointer_to_metadata(ptr)
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
                type PointerMetadata = ();

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
                    bytes: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<u8>,
                    _meta: (),
                ) -> ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self>
                {
                    bytes.cast::<Self>()
                }

                #[inline(always)]
                fn pointer_to_metadata(
                    _ptr: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self>,
                ) -> () {
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
            Trait::Immutable,
            FieldBounds::ALL_SELF,
            SelfBounds::None,
            None,
            None,
        ),
        Data::Enum(enm) => impl_block(
            ast,
            enm,
            Trait::Immutable,
            FieldBounds::ALL_SELF,
            SelfBounds::None,
            None,
            None,
        ),
        Data::Union(unn) => impl_block(
            ast,
            unn,
            Trait::Immutable,
            FieldBounds::ALL_SELF,
            SelfBounds::None,
            None,
            None,
        ),
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
            fn is_bit_valid<A: ::zerocopy::pointer::invariant::Aliasing + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>>(
                mut candidate: ::zerocopy::Maybe<Self, A>
            ) -> bool {
                true #(&& {
                    // SAFETY:
                    // - `project` is a field projection, and so it addresses a
                    //   subset of the bytes addressed by `slf`
                    // - ..., and so it preserves provenance
                    // - ..., and `*slf` is a struct, so `UnsafeCell`s exist at
                    //   the same byte ranges in the returned pointer's referent
                    //   as they do in `*slf`
                    let field_candidate = unsafe {
                        let project = |slf: *mut Self|
                            ::zerocopy::util::macro_util::core_reexport::ptr::addr_of_mut!((*slf).#field_names);

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
// - all of its fields are `TryFromBytes` and `Immutable`

fn derive_try_from_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#5): Remove the `Immutable` bound.
    let field_type_trait_bounds =
        FieldBounds::All(&[TraitBound::Slf, TraitBound::Other(Trait::Immutable)]);
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
            fn is_bit_valid<A: ::zerocopy::pointer::invariant::Aliasing + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>>(
                mut candidate: ::zerocopy::Maybe<Self, A>
            ) -> bool {
                false #(|| {
                    // SAFETY:
                    // - `project` is a field projection, and so it addresses a
                    //   subset of the bytes addressed by `slf`
                    // - ..., and so it preserves provenance
                    // - Since `Self: Immutable` is enforced by
                    //   `self_type_trait_bounds`, neither `*slf` nor the
                    //   returned pointer's referent contain any `UnsafeCell`s
                    let field_candidate = unsafe {
                        let project = |slf: *mut Self|
                            ::zerocopy::util::macro_util::core_reexport::ptr::addr_of_mut!((*slf).#field_names);

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
    let reprs = try_or_print!(ENUM_TRY_FROM_BYTES_CFG.validate_reprs(ast));

    // The enum derive requires some extra scaffolding
    let extra = Some(r#enum::derive_is_bit_valid(&ast.ident, &reprs, &ast.generics, enm));

    impl_block(ast, enm, Trait::TryFromBytes, FieldBounds::ALL_SELF, SelfBounds::None, None, extra)
}

#[rustfmt::skip]
const ENUM_TRY_FROM_BYTES_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        allowed_combinations_message: r#"TryFromBytes requires an enum repr of a primitive, "C", or "C" with a primitive"#,
        derive_unaligned: false,
        allowed_combinations: &[
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
            &[C],
            &[C, U8],
            &[C, U16],
            &[C, U32],
            &[C, U64],
            &[C, Usize],
            &[C, I8],
            &[C, I16],
            &[C, I32],
            &[C, I64],
            &[C, Isize],
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
// - one of the variants has a discriminant of `0`

// Returns `Ok(index)` if variant `index` of the enum has a discriminant of
// zero. If `Err(bool)` is returned, the boolean is true if the enum has unknown
// discriminants (e.g. discriminants set to const expressions which we can't
// evaluate in a proc macro). If the enum has unknown discriminants, then it
// might have a zero variant that we just can't detect.
fn find_zero_variant(enm: &DataEnum) -> Result<usize, bool> {
    // Discriminants can be anywhere in the range [i128::MIN, u128::MAX] because
    // the discriminant type may be signed or unsigned. Since we only care about
    // tracking the discriminant when it's less than or equal to zero, we can
    // avoid u128 -> i128 conversions and bounds checking by making the "next
    // discriminant" value implicitly negative.
    // Technically 64 bits is enough, but 128 is better for future compatibility
    // with https://github.com/rust-lang/rust/issues/56071
    let mut next_negative_discriminant = Some(0);

    // Sometimes we encounter explicit discriminants that we can't know the
    // value of (e.g. a constant expression that requires evaluation). These
    // could evaluate to zero or a negative number, but we can't assume that
    // they do (no false positives allowed!). So we treat them like strictly-
    // positive values that can't result in any zero variants, and track whether
    // we've encountered any unknown discriminants.
    let mut has_unknown_discriminants = false;

    for (i, v) in enm.variants.iter().enumerate() {
        match v.discriminant.as_ref() {
            // Implicit discriminant
            None => {
                match next_negative_discriminant.as_mut() {
                    Some(0) => return Ok(i),
                    // n is nonzero so subtraction is always safe
                    Some(n) => *n -= 1,
                    None => (),
                }
            }
            // Explicit positive discriminant
            Some((_, Expr::Lit(ExprLit { lit: Lit::Int(int), .. }))) => {
                match int.base10_parse::<u128>().ok() {
                    Some(0) => return Ok(i),
                    Some(_) => next_negative_discriminant = None,
                    None => {
                        // Numbers should never fail to parse, but just in case:
                        has_unknown_discriminants = true;
                        next_negative_discriminant = None;
                    }
                }
            }
            // Explicit negative discriminant
            Some((_, Expr::Unary(ExprUnary { op: UnOp::Neg(_), expr, .. }))) => match &**expr {
                Expr::Lit(ExprLit { lit: Lit::Int(int), .. }) => {
                    match int.base10_parse::<u128>().ok() {
                        Some(0) => return Ok(i),
                        // x is nonzero so subtraction is always safe
                        Some(x) => next_negative_discriminant = Some(x - 1),
                        None => {
                            // Numbers should never fail to parse, but just in
                            // case:
                            has_unknown_discriminants = true;
                            next_negative_discriminant = None;
                        }
                    }
                }
                // Unknown negative discriminant (e.g. const repr)
                _ => {
                    has_unknown_discriminants = true;
                    next_negative_discriminant = None;
                }
            },
            // Unknown discriminant (e.g. const expr)
            _ => {
                has_unknown_discriminants = true;
                next_negative_discriminant = None;
            }
        }
    }

    Err(has_unknown_discriminants)
}

fn derive_from_zeros_enum(ast: &DeriveInput, enm: &DataEnum) -> proc_macro2::TokenStream {
    // We don't actually care what the repr is; we just care that it's one of
    // the allowed ones.
    try_or_print!(ENUM_FROM_ZEROS_INTO_BYTES_CFG.validate_reprs(ast));

    let zero_variant = match find_zero_variant(enm) {
        Ok(index) => enm.variants.iter().nth(index).unwrap(),
        // Has unknown variants
        Err(true) => {
            return Error::new_spanned(
                ast,
                "FromZeros only supported on enums with a variant that has a discriminant of `0`\n\
                help: This enum has discriminants which are not literal integers. One of those may \
                define or imply which variant has a discriminant of zero. Use a literal integer to \
                define or imply the variant with a discriminant of zero.",
            )
            .to_compile_error();
        }
        // Does not have unknown variants
        Err(false) => {
            return Error::new_spanned(
                ast,
                "FromZeros only supported on enums with a variant that has a discriminant of `0`",
            )
            .to_compile_error();
        }
    };

    let explicit_bounds = zero_variant
        .fields
        .iter()
        .map(|field| {
            let ty = &field.ty;
            parse_quote! { #ty: ::zerocopy::FromZeros }
        })
        .collect::<Vec<WherePredicate>>();

    impl_block(
        ast,
        enm,
        Trait::FromZeros,
        FieldBounds::Explicit(explicit_bounds),
        SelfBounds::None,
        None,
        None,
    )
}

// Unions are `FromZeros` if
// - all fields are `FromZeros` and `Immutable`

fn derive_from_zeros_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#5): Remove the `Immutable` bound. It's only necessary for
    // compatibility with `derive(TryFromBytes)` on unions; not for soundness.
    let field_type_trait_bounds =
        FieldBounds::All(&[TraitBound::Slf, TraitBound::Other(Trait::Immutable)]);
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
// - all fields are `FromBytes` and `Immutable`

fn derive_from_bytes_union(ast: &DeriveInput, unn: &DataUnion) -> proc_macro2::TokenStream {
    // TODO(#5): Remove the `Immutable` bound. It's only necessary for
    // compatibility with `derive(TryFromBytes)` on unions; not for soundness.
    let field_type_trait_bounds =
        FieldBounds::All(&[TraitBound::Slf, TraitBound::Other(Trait::Immutable)]);
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
    // We don't care what the repr is; we only care that it is one of the
    // allowed ones.
    let reprs = try_or_print!(ENUM_FROM_ZEROS_INTO_BYTES_CFG.validate_reprs(ast));
    let repr = r#enum::tag_repr(&reprs)
        .expect("cannot derive IntoBytes for enum without a well-defined repr");
    let tag_type_definition = r#enum::generate_tag_enum(repr, enm);

    impl_block(
        ast,
        enm,
        Trait::IntoBytes,
        FieldBounds::ALL_SELF,
        SelfBounds::None,
        Some(PaddingCheck::Enum { tag_type_definition }),
        None,
    )
}

#[rustfmt::skip]
const ENUM_FROM_ZEROS_INTO_BYTES_CFG: Config<EnumRepr> = {
    use EnumRepr::*;
    Config {
        // Since `disallowed_but_legal_combinations` is empty, this message will
        // never actually be emitted.
        allowed_combinations_message: r#"FromZeros requires an enum repr of a primitive, "C", or "C" with a primitive"#,
        derive_unaligned: false,
        allowed_combinations: &[
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
            &[C],
            &[C, U8],
            &[C, U16],
            &[C, U32],
            &[C, U64],
            &[C, Usize],
            &[C, I8],
            &[C, I16],
            &[C, I32],
            &[C, I64],
            &[C, Isize],
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
    // The only valid reprs are `u8` and `i8`, and optionally `align(1)`. We
    // don't actually care what the reprs are so long as they satisfy that
    // requirement.
    let _: Vec<repr::EnumRepr> = try_or_print!(ENUM_UNALIGNED_CFG.validate_reprs(ast));

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
            &[C, U8],
            &[C, I8],
        ],
        disallowed_but_legal_combinations: &[
            &[U16],
            &[U32],
            &[U64],
            &[Usize],
            &[I16],
            &[I32],
            &[I64],
            &[Isize],
            &[C],
            &[C, U16],
            &[C, U32],
            &[C, U64],
            &[C, Usize],
            &[C, I16],
            &[C, I32],
            &[C, I64],
            &[C, Isize],
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
    // Check that every variant of the enum contains no padding.
    //
    // Because doing so requires a tag enum, this padding check requires an
    // additional `TokenStream` which defines the tag enum as `___ZerocopyTag`.
    Enum { tag_type_definition: TokenStream },
}

impl PaddingCheck {
    /// Returns the ident of the macro to call in order to validate that a type
    /// passes the padding check encoded by `PaddingCheck`.
    fn validator_macro_ident(&self) -> Ident {
        let s = match self {
            PaddingCheck::Struct => "struct_has_padding",
            PaddingCheck::Union => "union_has_padding",
            PaddingCheck::Enum { .. } => "enum_has_padding",
        };

        Ident::new(s, Span::call_site())
    }

    /// Sometimes performing the padding check requires some additional
    /// "context" code. For enums, this is the definition of the tag enum.
    fn validator_macro_context(&self) -> Option<&TokenStream> {
        match self {
            PaddingCheck::Struct | PaddingCheck::Union => None,
            PaddingCheck::Enum { tag_type_definition } => Some(tag_type_definition),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Trait {
    KnownLayout,
    Immutable,
    TryFromBytes,
    FromZeros,
    FromBytes,
    IntoBytes,
    Unaligned,
    Sized,
}

impl ToTokens for Trait {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ident = Ident::new(&format!("{:?}", self), Span::call_site());
        tokens.extend(core::iter::once(TokenTree::Ident(ident)));
    }
}

impl Trait {
    fn crate_path(&self) -> Path {
        match self {
            Self::Sized => parse_quote!(::zerocopy::util::macro_util::core_reexport::marker::#self),
            _ => parse_quote!(::zerocopy::#self),
        }
    }

    fn derive_path(&self) -> Path {
        match self {
            Self::Sized => panic!("no derive path for builtin types"),
            _ => parse_quote!(::zerocopy_derive::#self),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum TraitBound {
    Slf,
    Other(Trait),
}

enum FieldBounds<'a> {
    None,
    All(&'a [TraitBound]),
    Trailing(&'a [TraitBound]),
    Explicit(Vec<WherePredicate>),
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
    let trait_path = trt.crate_path();
    let fields = data.fields();
    let variants = data.variants();
    let tag = data.tag();

    fn bound_tt(ty: &Type, traits: impl Iterator<Item = Trait>) -> WherePredicate {
        let traits = traits.map(|t| t.crate_path());
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
        (FieldBounds::Explicit(bounds), _) => bounds,
    };

    // Don't bother emitting a padding check if there are no fields.
    #[allow(unstable_name_collisions)] // See `BoolExt` below
    // Work around https://github.com/rust-lang/rust-clippy/issues/12280
    #[allow(clippy::incompatible_msrv)]
    let padding_check_bound =
        padding_check.and_then(|check| (!fields.is_empty()).then_some(check)).map(|check| {
            let variant_types = variants.iter().map(|var| {
                let types = var.iter().map(|(_name, ty)| ty);
                quote!([#(#types),*])
            });
            let validator_context = check.validator_macro_context();
            let validator_macro = check.validator_macro_ident();
            let t = tag.iter();
            // We have to manually construct a bound here because the validator
            // context may include type definitions and syn cannot parse type
            // definitions in const exprs without the `full` feature enabled.
            // Constructing these bounds "verbatim" gets around this issue.
            let bounded_ty = Type::Verbatim(quote! {
                ::zerocopy::util::macro_util::HasPadding<
                    #type_ident,
                    {
                        #validator_context
                        ::zerocopy::#validator_macro!(#type_ident, #(#t,)* #(#variant_types),*)
                    }
                >
            });
            let mut bounds = Punctuated::new();
            bounds.push(parse_quote! { ::zerocopy::util::macro_util::ShouldBe<false> });
            WherePredicate::Type(PredicateType {
                lifetimes: None,
                bounded_ty,
                colon_token: Colon::default(),
                bounds,
            })
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
