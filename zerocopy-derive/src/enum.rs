// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse_quote, spanned::Spanned as _, DataEnum, DeriveInput, Error, Expr, ExprLit, ExprUnary,
    Fields, Ident, Index, Lit, UnOp,
};

use crate::{
    derive_has_field_struct_union, derive_try_from_bytes_inner, repr::EnumRepr, Ctx, DataExt,
    FieldBounds, ImplBlockBuilder, Trait,
};

/// Generates a tag enum for the given enum. This generates an enum with the
/// same non-align `repr`s, variants, and corresponding discriminants, but none
/// of the fields.
pub(crate) fn generate_tag_enum(ctx: &Ctx, repr: &EnumRepr, data: &DataEnum) -> TokenStream {
    let zerocopy_crate = &ctx.zerocopy_crate;
    let variants = data.variants.iter().map(|v| {
        let ident = &v.ident;
        if let Some((eq, discriminant)) = &v.discriminant {
            quote! { #ident #eq #discriminant }
        } else {
            quote! { #ident }
        }
    });

    // Don't include any `repr(align)` when generating the tag enum, as that
    // could add padding after the tag but before any variants, which is not the
    // correct behavior.
    let repr = match repr {
        EnumRepr::Transparent(span) => quote::quote_spanned! { *span => #[repr(transparent)] },
        EnumRepr::Compound(c, _) => quote! { #c },
    };

    quote! {
        #repr
        #[allow(dead_code)]
        enum ___ZerocopyTag {
            #(#variants,)*
        }

        // SAFETY: `___ZerocopyTag` has no fields, and so it does not permit
        // interior mutation.
        unsafe impl #zerocopy_crate::Immutable for ___ZerocopyTag {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }
    }
}

fn tag_ident(variant_ident: &Ident) -> Ident {
    ident!(("___ZEROCOPY_TAG_{}", variant_ident), variant_ident.span())
}

/// Generates a constant for the tag associated with each variant of the enum.
/// When we match on the enum's tag, each arm matches one of these constants. We
/// have to use constants here because:
///
/// - The type that we're matching on is not the type of the tag, it's an
///   integer of the same size as the tag type and with the same bit patterns.
/// - We can't read the enum tag as an enum because the bytes may not represent
///   a valid variant.
/// - Patterns do not currently support const expressions, so we have to assign
///   these constants to names rather than use them inline in the `match`
///   statement.
fn generate_tag_consts(data: &DataEnum) -> TokenStream {
    let tags = data.variants.iter().map(|v| {
        let variant_ident = &v.ident;
        let tag_ident = tag_ident(variant_ident);

        quote! {
            // This casts the enum variant to its discriminant, and then
            // converts the discriminant to the target integral type via a
            // numeric cast [1].
            //
            // Because these are the same size, this is defined to be a no-op
            // and therefore is a lossless conversion [2].
            //
            // [1] Per https://doc.rust-lang.org/1.81.0/reference/expressions/operator-expr.html#enum-cast:
            //
            //   Casts an enum to its discriminant.
            //
            // [2] Per https://doc.rust-lang.org/1.81.0/reference/expressions/operator-expr.html#numeric-cast:
            //
            //   Casting between two integers of the same size (e.g. i32 -> u32)
            //   is a no-op.
            const #tag_ident: ___ZerocopyTagPrimitive =
                ___ZerocopyTag::#variant_ident as ___ZerocopyTagPrimitive;
        }
    });

    quote! {
        #(#tags)*
    }
}

fn variant_struct_ident(variant_ident: &Ident) -> Ident {
    ident!(("___ZerocopyVariantStruct_{}", variant_ident), variant_ident.span())
}

/// Generates variant structs for the given enum variant.
///
/// These are structs associated with each variant of an enum. They are
/// `repr(C)` tuple structs with the same fields as the variant after a
/// `MaybeUninit<___ZerocopyInnerTag>`.
///
/// In order to unify the generated types for `repr(C)` and `repr(int)` enums,
/// we use a "fused" representation with fields for both an inner tag and an
/// outer tag. Depending on the repr, we will set one of these tags to the tag
/// type and the other to `()`. This lets us generate the same code but put the
/// tags in different locations.
fn generate_variant_structs(ctx: &Ctx, data: &DataEnum) -> TokenStream {
    let (impl_generics, ty_generics, where_clause) = ctx.ast.generics.split_for_impl();

    let enum_name = &ctx.ast.ident;

    // All variant structs have a `PhantomData<MyEnum<...>>` field because we
    // don't know which generic parameters each variant will use, and unused
    // generic parameters are a compile error.
    let core = ctx.core_path();
    let phantom_ty = quote! {
        #core::marker::PhantomData<#enum_name #ty_generics>
    };

    let variant_structs = data.variants.iter().filter_map(|variant| {
        // We don't generate variant structs for unit variants because we only
        // need to check the tag. This helps cut down our generated code a bit.
        if matches!(variant.fields, Fields::Unit) {
            return None;
        }

        let variant_struct_ident = variant_struct_ident(&variant.ident);
        let field_types = variant.fields.iter().map(|f| &f.ty);

        let variant_struct = parse_quote! {
            #[repr(C)]
            struct #variant_struct_ident #impl_generics (
                #core::mem::MaybeUninit<___ZerocopyInnerTag>,
                #(#field_types,)*
                #phantom_ty,
            ) #where_clause;
        };

        // We do this rather than emitting `#[derive(::zerocopy::TryFromBytes)]`
        // because that is not hygienic, and this is also more performant.
        let try_from_bytes_impl =
            derive_try_from_bytes_inner(&ctx.with_input(&variant_struct), Trait::TryFromBytes)
                .expect("derive_try_from_bytes_inner should not fail on synthesized type");

        Some(quote! {
            #variant_struct
            #try_from_bytes_impl
        })
    });

    quote! {
        #(#variant_structs)*
    }
}

fn variants_union_field_ident(ident: &Ident) -> Ident {
    // Field names are prefixed with `__field_` to prevent name collision
    // with the `__nonempty` field.
    ident!(("__field_{}", ident), ident.span())
}

fn generate_variants_union(ctx: &Ctx, data: &DataEnum) -> TokenStream {
    let generics = &ctx.ast.generics;
    let (_, ty_generics, _) = generics.split_for_impl();

    let fields = data.variants.iter().filter_map(|variant| {
        // We don't generate variant structs for unit variants because we only
        // need to check the tag. This helps cut down our generated code a bit.
        if matches!(variant.fields, Fields::Unit) {
            return None;
        }

        let field_name = variants_union_field_ident(&variant.ident);
        let variant_struct_ident = variant_struct_ident(&variant.ident);

        let core = ctx.core_path();
        Some(quote! {
            #field_name: #core::mem::ManuallyDrop<
                #variant_struct_ident #ty_generics
            >,
        })
    });

    let variants_union = parse_quote! {
        #[repr(C)]
        union ___ZerocopyVariants #generics {
            #(#fields)*
            // Enums can have variants with no fields, but unions must
            // have at least one field. So we just add a trailing unit
            // to ensure that this union always has at least one field.
            // Because this union is `repr(C)`, this unit type does not
            // affect the layout.
            __nonempty: (),
        }
    };

    let has_field =
        derive_has_field_struct_union(&ctx.with_input(&variants_union), &variants_union.data);

    quote! {
        #variants_union
        #has_field
    }
}

/// Generates an implementation of `is_bit_valid` for an arbitrary enum.
///
/// The general process is:
///
/// 1. Generate a tag enum. This is an enum with the same repr, variants, and
///    corresponding discriminants as the original enum, but without any fields
///    on the variants. This gives us access to an enum where the variants have
///    the same discriminants as the one we're writing `is_bit_valid` for.
/// 2. Make constants from the variants of the tag enum. We need these because
///    we can't put const exprs in match arms.
/// 3. Generate variant structs. These are structs which have the same fields as
///    each variant of the enum, and are `#[repr(C)]` with an optional "inner
///    tag".
/// 4. Generate a variants union, with one field for each variant struct type.
/// 5. And finally, our raw enum is a `#[repr(C)]` struct of an "outer tag" and
///    the variants union.
///
/// See these reference links for fully-worked example decompositions.
///
/// - `repr(C)`: <https://doc.rust-lang.org/reference/type-layout.html#reprc-enums-with-fields>
/// - `repr(int)`: <https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-enums-with-fields>
/// - `repr(C, int)`: <https://doc.rust-lang.org/reference/type-layout.html#combining-primitive-representations-of-enums-with-fields-and-reprc>
pub(crate) fn derive_is_bit_valid(
    ctx: &Ctx,
    data: &DataEnum,
    repr: &EnumRepr,
) -> Result<TokenStream, Error> {
    let trait_path = Trait::TryFromBytes.crate_path(ctx);
    let tag_enum = generate_tag_enum(ctx, repr, data);
    let tag_consts = generate_tag_consts(data);

    let (outer_tag_type, inner_tag_type) = if repr.is_c() {
        (quote! { ___ZerocopyTag }, quote! { () })
    } else if repr.is_primitive() {
        (quote! { () }, quote! { ___ZerocopyTag })
    } else {
        return Err(Error::new(
            ctx.ast.span(),
            "must have #[repr(C)] or #[repr(Int)] attribute in order to guarantee this type's memory layout",
        ));
    };

    let variant_structs = generate_variant_structs(ctx, data);
    let variants_union = generate_variants_union(ctx, data);

    let (impl_generics, ty_generics, where_clause) = ctx.ast.generics.split_for_impl();

    let zerocopy_crate = &ctx.zerocopy_crate;
    let has_fields = data.variants().into_iter().flat_map(|(variant, fields)| {
        let variant_ident = &variant.unwrap().ident;
        let variants_union_field_ident = variants_union_field_ident(variant_ident);
        let field: Box<syn::Type> = parse_quote!(());
        fields.into_iter().enumerate().map(move |(idx, (vis, ident, ty))| {
            // Rust does not presently support explicit visibility modifiers on
            // enum fields, but we guard against the possibility to ensure this
            // derive remains sound.
            assert!(matches!(vis, syn::Visibility::Inherited));
            let variant_struct_field_index = Index::from(idx + 1);
            let (_, ty_generics, _) = ctx.ast.generics.split_for_impl();
            ImplBlockBuilder::new(
                ctx,
                data,
                Trait::HasField {
                    variant_id: parse_quote!({ #zerocopy_crate::ident_id!(#variant_ident) }),
                    // Since Rust does not presently support explicit visibility
                    // modifiers on enum fields, any public type is suitable
                    // here; we use `()`.
                    field: field.clone(),
                    field_id: parse_quote!({ #zerocopy_crate::ident_id!(#ident) }),
                },
                FieldBounds::None,
            )
            .inner_extras(quote! {
                type Type = #ty;

                #[inline(always)]
                fn project(slf: #zerocopy_crate::pointer::PtrInner<'_, Self>) -> *mut Self::Type {
                    use #zerocopy_crate::pointer::cast::{CastSized, Projection};

                    slf.project::<___ZerocopyRawEnum #ty_generics, CastSized>()
                        .project::<_, Projection<_, { #zerocopy_crate::STRUCT_VARIANT_ID }, { #zerocopy_crate::ident_id!(variants) }>>()
                        .project::<_, Projection<_, { #zerocopy_crate::UNION_VARIANT_ID }, { #zerocopy_crate::ident_id!(#variants_union_field_ident) }>>()
                        .project::<_, Projection<_, { #zerocopy_crate::STRUCT_VARIANT_ID }, { #zerocopy_crate::ident_id!(value) }>>()
                        .project::<_, Projection<_, { #zerocopy_crate::STRUCT_VARIANT_ID }, { #zerocopy_crate::ident_id!(#variant_struct_field_index) }>>()
                        .as_ptr()
                }
            })
            .build()
        })
    });

    let core = ctx.core_path();
    let match_arms = data.variants.iter().map(|variant| {
        let tag_ident = tag_ident(&variant.ident);
        let variant_struct_ident = variant_struct_ident(&variant.ident);
        let variants_union_field_ident = variants_union_field_ident(&variant.ident);

        if matches!(variant.fields, Fields::Unit) {
            // Unit variants don't need any further validation beyond checking
            // the tag.
            quote! {
                #tag_ident => true
            }
        } else {
            quote! {
                #tag_ident => {
                    // SAFETY: Since we know that the tag is `#tag_ident`, we
                    // know that no other `&`s exist which refer to this enum
                    // as any other variant.
                    let variant_md = unsafe { variants.cast_unchecked::<
                        #core::mem::ManuallyDrop<#variant_struct_ident #ty_generics>,
                        #zerocopy_crate::pointer::cast::Projection<
                            _,
                            { #zerocopy_crate::UNION_VARIANT_ID },
                            { #zerocopy_crate::ident_id!(#variants_union_field_ident) }
                        >
                    >() };
                    let variant = variant_md.cast::<
                        #variant_struct_ident #ty_generics,
                        #zerocopy_crate::pointer::cast::CastSized,
                        #zerocopy_crate::pointer::BecauseInvariantsEq
                    >();
                    <
                        #variant_struct_ident #ty_generics as #trait_path
                    >::is_bit_valid(variant)
                }
            }
        }
    });

    let generics = &ctx.ast.generics;
    let raw_enum: DeriveInput = parse_quote! {
        #[repr(C)]
        struct ___ZerocopyRawEnum #generics {
            tag: ___ZerocopyOuterTag,
            variants: ___ZerocopyVariants #ty_generics,
        }
    };

    let self_ident = &ctx.ast.ident;
    let invariants_eq_impl = quote! {
        // SAFETY: `___ZerocopyRawEnum` is designed to have the same layout,
        // validity, and invariants as `Self`.
        unsafe impl #impl_generics #zerocopy_crate::pointer::InvariantsEq<___ZerocopyRawEnum #ty_generics> for #self_ident #ty_generics #where_clause {}
    };

    let raw_enum_projections =
        derive_has_field_struct_union(&ctx.with_input(&raw_enum), &raw_enum.data);

    let raw_enum = quote! {
        #raw_enum
        #invariants_eq_impl
        #raw_enum_projections
    };

    Ok(quote! {
        // SAFETY: We use `is_bit_valid` to validate that the bit pattern of the
        // enum's tag corresponds to one of the enum's discriminants. Then, we
        // check the bit validity of each field of the corresponding variant.
        // Thus, this is a sound implementation of `is_bit_valid`.
        fn is_bit_valid<___ZerocopyAliasing>(
            candidate: #zerocopy_crate::Maybe<'_, Self, ___ZerocopyAliasing>,
        ) -> #core::primitive::bool
        where
            ___ZerocopyAliasing: #zerocopy_crate::pointer::invariant::Reference,
        {
            #tag_enum

            type ___ZerocopyTagPrimitive = #zerocopy_crate::util::macro_util::SizeToTag<
                { #core::mem::size_of::<___ZerocopyTag>() },
            >;

            #tag_consts

            type ___ZerocopyOuterTag = #outer_tag_type;
            type ___ZerocopyInnerTag = #inner_tag_type;

            // SAFETY: `___ZerocopyRawEnum` is designed to match the layout of
            // the `Self` enum, which has a `___ZerocopyTag` tag as its first
            // field.
            //
            // `project` is implemented using a cast which preserves or shrinks
            // the set of referent bytes and preserves provenance.
            unsafe impl #generics #zerocopy_crate::HasField<(), { #zerocopy_crate::STRUCT_VARIANT_ID }, { #zerocopy_crate::ident_id!(tag) }> for ___ZerocopyRawEnum #ty_generics {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                type Type = ___ZerocopyTag;

                #[inline(always)]
                fn project(slf: #zerocopy_crate::pointer::PtrInner<'_, Self>) -> *mut Self::Type {
                    slf.as_ptr().cast()
                }
            }

            #variant_structs

            #variants_union

            #raw_enum

            #(#has_fields)*

            let mut raw_enum = candidate.cast::<
                ___ZerocopyRawEnum #ty_generics,
                #zerocopy_crate::pointer::cast::CastSized,
                #zerocopy_crate::pointer::BecauseInvariantsEq
            >();

            let tag = {
                let tag_ptr = raw_enum.reborrow().project::<
                    (),
                    { #zerocopy_crate::ident_id!(tag) }
                >().cast::<
                    ___ZerocopyTagPrimitive,
                    #zerocopy_crate::pointer::cast::CastSized,
                    _
                >();
                tag_ptr.recall_validity::<_, (_, (_, _))>().read_unaligned::<#zerocopy_crate::BecauseImmutable>()
            };

            let variants = raw_enum.project::<_, { #zerocopy_crate::ident_id!(variants) }>();

            match tag {
                #(#match_arms,)*
                _ => false,
            }
        }
    })
}

/// Returns `Ok(index)` if variant `index` of the enum has a discriminant of
/// zero. If `Err(bool)` is returned, the boolean is true if the enum has
/// unknown discriminants (e.g. discriminants set to const expressions which we
/// can't evaluate in a proc macro). If the enum has unknown discriminants, then
/// it might have a zero variant that we just can't detect.
pub(crate) fn find_zero_variant(enm: &DataEnum) -> Result<usize, bool> {
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
