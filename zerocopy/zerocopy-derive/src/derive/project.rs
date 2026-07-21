// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse_quote, spanned::Spanned as _, Data, DataEnum, DeriveInput, Error, Expr, Fields, Ident,
    Index, Type,
};

use crate::{
    repr::{EnumRepr, StructUnionRepr},
    util::{
        const_block, generate_tag_enum, Client, Ctx, DataExt, FieldBounds, FieldProjection,
        ImplBlockBuilder, Trait,
    },
};

pub(crate) fn tag_ident(variant: &Ident) -> Ident {
    ident!(("___ZEROCOPY_TAG_{}", variant), variant.span())
}

pub(crate) fn variant_struct_ident(variant: &Ident) -> Ident {
    ident!(("___ZerocopyVariantStruct_{}", variant), variant.span())
}

pub(crate) fn variants_union_field_ident(variant: &Ident) -> Ident {
    ident!(("__field_{}", variant), variant.span())
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
pub(crate) fn generate_tag_consts(data: &DataEnum) -> TokenStream {
    let tags = data.variants.iter().map(|variant| {
        let variant_ident = &variant.ident;
        let tag = tag_ident(variant_ident);

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
            const #tag: ___ZerocopyTagPrimitive =
                ___ZerocopyTag::#variant_ident as ___ZerocopyTagPrimitive;
        }
    });

    quote! {
        #(#tags)*
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum Validity {
    Uninit,
    Initialized,
    Valid,
}

impl Validity {
    fn as_type(self, ctx: &Ctx) -> Type {
        let zerocopy_crate = &ctx.zerocopy_crate;
        match self {
            Validity::Uninit => parse_quote!(#zerocopy_crate::invariant::Uninit),
            Validity::Initialized => {
                parse_quote!(#zerocopy_crate::invariant::Initialized)
            }
            Validity::Valid => parse_quote!(#zerocopy_crate::invariant::Valid),
        }
    }

    /// Computes the output validity of projecting a struct or union field.
    ///
    /// Struct fields preserve all three validity invariants. Union fields
    /// preserve `Uninit` and `Initialized`, but a valid union does not imply
    /// that any particular field is valid or initialized, so `Valid` is
    /// weakened to `Uninit`.
    fn output_validity_for_struct_or_union(self, data: &Data) -> Self {
        match (data, self) {
            (Data::Struct(_), validity)
            | (Data::Union(_), validity @ Validity::Uninit)
            | (Data::Union(_), validity @ Validity::Initialized) => validity,
            (Data::Union(_), Validity::Valid) => Validity::Uninit,
            (Data::Enum(_), _) => unreachable!(),
        }
    }
}

/// Emits a `ProjectField` impl for a struct or union field.
///
/// The corresponding `HasField` impl must satisfy its safety contract, and
/// must project the field identified by `projection`. The output alignment is
/// derived from `ctx`: ordinary fields preserve the input alignment, while
/// fields of packed types are conservatively treated as unaligned. `Validity`
/// likewise computes the output validity rather than permitting callers to
/// supply an arbitrary mapping: structs preserve validity, while a valid union
/// field is conservatively treated as uninitialized.
fn derive_struct_union_project_field(
    ctx: &Ctx,
    data: &dyn DataExt,
    client: Client,
    projection: FieldProjection,
    input_validity: Validity,
) -> TokenStream {
    let output_validity =
        input_validity.output_validity_for_struct_or_union(&ctx.ast.data).as_type(ctx);
    let input_validity = input_validity.as_type(ctx);
    let zerocopy_crate = &ctx.zerocopy_crate;
    let projection_preserves_alignment = StructUnionRepr::from_attrs(&ctx.ast.attrs)
        .map(|repr| repr.get_packed().is_none())
        .unwrap();
    let output_alignment = if projection_preserves_alignment {
        quote! { ___ZcAlignment }
    } else {
        quote! { #zerocopy_crate::invariant::Unaligned }
    };
    ImplBlockBuilder::new(
        ctx,
        data,
        Trait::ProjectField {
            client,
            projection,
            invariants: parse_quote!((___ZcAliasing, ___ZcAlignment, #input_validity)),
        },
        FieldBounds::None,
    )
    .param_extras(vec![
        parse_quote!(___ZcAliasing: #zerocopy_crate::invariant::Aliasing),
        parse_quote!(___ZcAlignment: #zerocopy_crate::invariant::Alignment),
    ])
    .inner_extras(quote! {
        // SAFETY: Struct and union projections do not depend on the value of
        // the referent, and are therefore infallible.
        type Error = #zerocopy_crate::util::macro_util::core_reexport::convert::Infallible;

        // SAFETY: Projection preserves aliasing. It also preserves alignment
        // unless the containing type is packed. `Validity` computes the output
        // validity from the input validity and whether `Self` is a struct or
        // union: struct fields preserve validity; union fields preserve
        // `Uninit` and `Initialized`, while `Valid` is weakened to `Uninit`.
        type Invariants = (___ZcAliasing, #output_alignment, #output_validity);
    })
    .build()
}

/// Returns the projection variant ID for the struct or union described by
/// `ctx`.
///
/// This intentionally does not handle enums: an enum field's variant ID
/// identifies its source variant rather than the representation of its
/// containing type.
pub(crate) fn struct_union_variant_id(ctx: &Ctx) -> Box<Expr> {
    let zerocopy_crate = &ctx.zerocopy_crate;
    match &ctx.ast.data {
        Data::Struct(_) => parse_quote!({ #zerocopy_crate::STRUCT_VARIANT_ID }),
        Data::Union(_) => {
            if StructUnionRepr::from_attrs(&ctx.ast.attrs).map(|repr| repr.is_c()).unwrap() {
                parse_quote!({ #zerocopy_crate::REPR_C_UNION_VARIANT_ID })
            } else {
                parse_quote!({ #zerocopy_crate::UNION_VARIANT_ID })
            }
        }
        Data::Enum(_) => unreachable!("struct_union_variant_id called for enum"),
    }
}

/// Generates field projection implementations for a struct or union.
///
/// `repr(C)` unions use `REPR_C_UNION_VARIANT_ID`, so their projections
/// additionally implement `pointer::cast::Cast`. Other unions use
/// `UNION_VARIANT_ID`.
pub(crate) fn derive_projection_struct_union(
    ctx: &Ctx,
    data: &dyn DataExt,
    client: Client,
) -> TokenStream {
    let fields = ctx.ast.data.fields();
    if fields.is_empty() {
        return quote! {};
    }

    let field_tokens = fields.iter().map(|(vis, ident, _)| {
        let ident = ident!(("ẕ{}", ident), ident.span());
        quote! {
            #vis enum #ident {}
        }
    });

    let zerocopy_crate = &ctx.zerocopy_crate;
    let variant_id = struct_union_variant_id(ctx);

    let core = ctx.core_path();
    let has_tag = ImplBlockBuilder::new(ctx, data, Trait::HasTag { client }, FieldBounds::None)
        .inner_extras(quote! {
            type Tag = ();
            type ProjectToTag = #zerocopy_crate::pointer::cast::CastToUnit;
        })
        .build();

    let has_fields = fields.iter().map(move |(_, ident, ty)| {
        let field_token = ident!(("ẕ{}", ident), ident.span());
        let projection = FieldProjection {
            variant_id: variant_id.clone(),
            field: parse_quote!(#field_token),
            field_id: parse_quote!({ #zerocopy_crate::ident_id!(#ident) }),
        };
        let has_field_trait = Trait::HasField { client, projection: projection.clone() };
        let has_field_path = has_field_trait.crate_path(ctx);
        let has_field = ImplBlockBuilder::new(ctx, data, has_field_trait, FieldBounds::None)
            .inner_extras(quote! {
                type Type = #ty;

                #[inline(always)]
                fn project(
                    slf: #zerocopy_crate::pointer::PtrInner<'_, Self>,
                ) -> *mut <Self as #has_field_path>::Type {
                    let slf = slf.as_ptr();
                    // SAFETY: By invariant on `PtrInner`, `slf` is a non-null
                    // pointer whose referent is zero-sized or lives in a valid
                    // allocation. Since `#ident` is a struct or union field of
                    // `Self`, this projection preserves or shrinks the referent
                    // size, and so the resulting referent also fits in the same
                    // allocation.
                    unsafe { #core::ptr::addr_of_mut!((*slf).#ident) }
                }
            })
            .build();

        let derive_struct_union_project_field = |validity| {
            derive_struct_union_project_field(ctx, data, client, projection.clone(), validity)
        };

        let project_uninit = derive_struct_union_project_field(Validity::Uninit);
        let project_initialized = derive_struct_union_project_field(Validity::Initialized);
        let project_valid = derive_struct_union_project_field(Validity::Valid);

        quote! {
            #has_field
            #project_uninit
            #project_initialized
            #project_valid
        }
    });

    const_block(field_tokens.into_iter().chain(Some(has_tag)).chain(has_fields).map(Some))
}

fn generate_project_variant_structs(ctx: &Ctx, data: &DataEnum, client: Client) -> TokenStream {
    let (impl_generics, ty_generics, where_clause) = ctx.ast.generics.split_for_impl();
    let enum_name = &ctx.ast.ident;
    let core = ctx.core_path();
    let phantom_ty = quote! {
        #core::marker::PhantomData<#enum_name #ty_generics>
    };
    let variant_structs = data.variants.iter().filter_map(|variant| {
        if matches!(variant.fields, Fields::Unit) {
            return None;
        }

        let ident = variant_struct_ident(&variant.ident);
        let field_types = variant.fields.iter().map(|field| &field.ty);
        let variant_struct: DeriveInput = parse_quote! {
            #[repr(C)]
            struct #ident #impl_generics (
                #core::mem::MaybeUninit<___ZerocopyInnerTag>,
                #(#field_types,)*
                #phantom_ty,
            ) #where_clause;
        };
        let projections = derive_projection_struct_union(
            &ctx.with_input(&variant_struct),
            &variant_struct.data,
            client,
        );

        Some(quote! {
            #variant_struct
            #projections
        })
    });

    quote! {
        #(#variant_structs)*
    }
}

fn generate_project_variants_union(ctx: &Ctx, data: &DataEnum, client: Client) -> TokenStream {
    let generics = &ctx.ast.generics;
    let (_, ty_generics, _) = generics.split_for_impl();
    let core = ctx.core_path();
    let fields = data.variants.iter().filter_map(|variant| {
        if matches!(variant.fields, Fields::Unit) {
            return None;
        }
        let field_name = variants_union_field_ident(&variant.ident);
        let variant_struct = variant_struct_ident(&variant.ident);
        Some(quote! {
            #field_name: #core::mem::ManuallyDrop<#variant_struct #ty_generics>,
        })
    });

    let variants_union: DeriveInput = parse_quote! {
        #[repr(C)]
        union ___ZerocopyVariants #generics {
            #(#fields)*
            // A fieldless enum produces no variant structs, but a union must
            // have at least one field. This unit does not affect `repr(C)`
            // layout.
            __nonempty: (),
        }
    };
    let projections = derive_projection_struct_union(
        &ctx.with_input(&variants_union),
        &variants_union.data,
        client,
    );

    quote! {
        #variants_union
        #projections
    }
}

/// Emits a `ProjectField` impl for an enum field.
///
/// The returned tokens contain an `unsafe impl`, so the following conditions
/// must hold:
///
/// - The corresponding `HasField` impl satisfies its safety contract, projects
///   to the field identified by `projection`, and preserves the input pointer's
///   alignment invariant.
/// - The enum described by `ctx.ast` and `data` has the layout modeled by
///   `___ZerocopyRawEnum` and its nested variant types.
/// - The corresponding `HasTag` impl projects to the enum's tag, and the tag
///   selected by `variant` identifies the variant containing the projected
///   field.
/// - `projection.variant_id` is `ident_id!(variant)`, and
///   `projection.field_id` identifies the projected field within that variant.
/// - While projecting a valid field, the tag cannot change between
///   `is_projectable` reading it and `HasField::project` projecting the field.
fn derive_enum_project_field(
    ctx: &Ctx,
    data: &DataEnum,
    client: Client,
    variant: &Ident,
    projection: &FieldProjection,
    validity: Validity,
) -> TokenStream {
    let zerocopy_crate = &ctx.zerocopy_crate;
    let (error, is_projectable, aliasing_bound) = if validity == Validity::Valid {
        assert!(!matches!(validity, Validity::Uninit | Validity::Initialized));
        let has_tag_path = Trait::HasTag { client }.crate_path(ctx);
        let core = ctx.core_path();
        (
            quote! { () },
            quote! {
                #[inline(always)]
                fn is_projectable(
                    tag: #zerocopy_crate::pointer::Ptr<
                        '_,
                        <Self as #has_tag_path>::Tag,
                        (
                            ___ZcAliasing,
                            ___ZcAlignment,
                            #zerocopy_crate::invariant::Valid,
                        ),
                    >,
                ) -> #core::result::Result<(), ()> {
                    let tag = tag.read::<#zerocopy_crate::BecauseImmutable>();
                    if tag == ___ZerocopyTag::#variant {
                        #core::result::Result::Ok(())
                    } else {
                        #core::result::Result::Err(())
                    }
                }
            },
            parse_quote!(___ZcAliasing: #zerocopy_crate::invariant::Reference),
        )
    } else {
        (
            quote! { #zerocopy_crate::util::macro_util::core_reexport::convert::Infallible },
            quote! {},
            parse_quote!(___ZcAliasing: #zerocopy_crate::invariant::Aliasing),
        )
    };

    let validity = validity.as_type(ctx);
    let project_field_trait = Trait::ProjectField {
        client,
        projection: projection.clone(),
        invariants: parse_quote!((___ZcAliasing, ___ZcAlignment, #validity)),
    };

    ImplBlockBuilder::new(ctx, data, project_field_trait, FieldBounds::None)
        .param_extras(vec![
            aliasing_bound,
            parse_quote!(___ZcAlignment: #zerocopy_crate::invariant::Alignment),
        ])
        .inner_extras(quote! {
            type Error = #error;
            type Invariants = (___ZcAliasing, ___ZcAlignment, #validity);
            #is_projectable
        })
        .build()
}

pub(crate) fn derive_has_field_enum(
    ctx: &Ctx,
    data: &DataEnum,
    repr: &EnumRepr,
    client: Client,
) -> TokenStream {
    // `derive_enum_project_field` relies on the enum having one of the two
    // field-carrying enum representations modeled by the generated raw types.
    // Keep this as a release assertion so that a future caller cannot emit the
    // unsafe impls for an enum whose layout is not modeled.
    assert!(
        repr.is_c() || repr.is_primitive(),
        "enum field projections require repr(C) or a primitive representation",
    );

    let zerocopy_crate = &ctx.zerocopy_crate;
    let has_fields = data.variants().into_iter().flat_map(|(variant, fields)| {
        let variant_ident = &variant.unwrap().ident;

        fields.into_iter().enumerate().map(move |(idx, (vis, ident, ty))| {
            // Rust does not presently support explicit visibility modifiers on
            // enum fields. Keep this assertion so that a future language
            // change cannot silently invalidate the visibility invariant.
            assert!(matches!(vis, syn::Visibility::Inherited));
            let projection = FieldProjection {
                variant_id: parse_quote!({ #zerocopy_crate::ident_id!(#variant_ident) }),
                field: parse_quote!(()),
                field_id: parse_quote!({ #zerocopy_crate::ident_id!(#ident) }),
            };
            let variants_union_field = variants_union_field_ident(variant_ident);
            // The generated variant struct's first field is its inner tag.
            let variant_struct_field_index = Index::from(idx + 1);
            let (_, ty_generics, _) = ctx.ast.generics.split_for_impl();
            let has_field_trait = Trait::HasField {
                client,
                projection: projection.clone(),
            };
            let has_field_path = has_field_trait.crate_path(ctx);
            let client_path = client.crate_path(ctx);
            let has_field = ImplBlockBuilder::new(ctx, data, has_field_trait, FieldBounds::None)
                .inner_extras(quote! {
                    type Type = #ty;

                    #[inline(always)]
                    fn project(
                        slf: #zerocopy_crate::pointer::PtrInner<'_, Self>,
                    ) -> *mut <Self as #has_field_path>::Type {
                        use #zerocopy_crate::pointer::cast::{CastSized, Projection};

                        slf.project::<___ZerocopyRawEnum #ty_generics, CastSized>()
                            .project::<_, Projection<#client_path, _, { #zerocopy_crate::STRUCT_VARIANT_ID }, { #zerocopy_crate::ident_id!(variants) }>>()
                            .project::<_, Projection<#client_path, _, { #zerocopy_crate::REPR_C_UNION_VARIANT_ID }, { #zerocopy_crate::ident_id!(#variants_union_field) }>>()
                            .project::<_, Projection<#client_path, _, { #zerocopy_crate::STRUCT_VARIANT_ID }, { #zerocopy_crate::ident_id!(value) }>>()
                            .project::<_, Projection<#client_path, _, { #zerocopy_crate::STRUCT_VARIANT_ID }, { #zerocopy_crate::ident_id!(#variant_struct_field_index) }>>()
                            .as_ptr()
                    }
                })
                .build();

            // SAFETY: `projection` is constructed from the current field and
            // `variant_ident`, and that same `variant_ident` is passed to
            // `derive_enum_project_field` and used to select the variants union
            // field through which `has_field` projects. Thus the `HasField`
            // impl, `ProjectField` impls, and valid projection's tag check all
            // identify the same enum field. `idx` is the current field's
            // zero-based position, and the generated variant struct prepends
            // its inner tag before reproducing the enum fields in source order,
            // so `idx + 1` selects that same field. The assertion above enforces
            // that `repr` is `repr(C)` or a primitive representation;
            // `___ZerocopyRawEnum` and its nested types model exactly the
            // representations specified by [1] and [2]. Those representations
            // use `repr(C)` structs for variant fields, so field projection
            // preserves alignment. `ProjectionValidity` ensures that the
            // validity mapping and tag check meet the remaining conditions
            // documented on `derive_enum_project_field`. The corresponding
            // `HasTag` impl projects to the raw representation's tag using
            // `CastSized`.
            //
            // [1] Per https://doc.rust-lang.org/1.56.0/reference/type-layout.html#reprc-enums-with-fields:
            //
            //   The representation of a `repr(C)` enum with fields is a
            //   `repr(C)` struct with two fields [...]: a `repr(C)` version of
            //   the enum with all fields removed ("the tag") [and] a `repr(C)`
            //   union of `repr(C)` structs for the fields of each variant [...].
            //
            // [2] Per https://doc.rust-lang.org/1.56.0/reference/type-layout.html#primitive-representation-of-enums-with-fields:
            //
            //   The representation of a primitive representation enum is a
            //   `repr(C)` union of `repr(C)` structs for each variant with a
            //   field. The first field of each struct in the union is [...] the
            //   tag and the remaining fields are the fields of that variant.
            let derive_enum_project_field = |validity| {
                derive_enum_project_field(ctx, data, client, variant_ident, &projection, validity)
            };

            let uninit = derive_enum_project_field(Validity::Uninit);
            let initialized = derive_enum_project_field(Validity::Initialized);
            let valid = derive_enum_project_field(Validity::Valid);

            quote! {
                #has_field
                #uninit
                #initialized
                #valid
            }
        })
    });

    quote! {
        #(#has_fields)*
    }
}

fn derive_enum(ctx: &Ctx, data: &DataEnum, client: Client) -> Result<TokenStream, Error> {
    // With no fields, there are no `HasField` or `ProjectField` impls to emit,
    // and therefore no representation requirement to enforce.
    if data.fields().is_empty() {
        return Ok(TokenStream::new());
    }

    let repr = EnumRepr::from_attrs(&ctx.ast.attrs)?;
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

    let tag_enum = generate_tag_enum(ctx, &repr, data);
    let tag_consts = generate_tag_consts(data);
    let variant_structs = generate_project_variant_structs(ctx, data, client);
    let variants_union = generate_project_variants_union(ctx, data, client);
    let zerocopy_crate = &ctx.zerocopy_crate;
    let core = ctx.core_path();
    let (_, ty_generics, _) = ctx.ast.generics.split_for_impl();
    let generics = &ctx.ast.generics;
    let raw_enum: DeriveInput = parse_quote! {
        #[repr(C)]
        struct ___ZerocopyRawEnum #generics {
            tag: ___ZerocopyOuterTag,
            variants: ___ZerocopyVariants #ty_generics,
        }
    };
    let raw_projections =
        derive_projection_struct_union(&ctx.with_input(&raw_enum), &raw_enum.data, client);
    let has_tag = ImplBlockBuilder::new(ctx, data, Trait::HasTag { client }, FieldBounds::None)
        .inner_extras(quote! {
            type Tag = ___ZerocopyTag;
            type ProjectToTag = #zerocopy_crate::pointer::cast::CastSized;
        })
        .build();
    let has_fields = derive_has_field_enum(ctx, data, &repr, client);

    Ok(quote! {
        #tag_enum

        type ___ZerocopyTagPrimitive = #zerocopy_crate::util::macro_util::SizeToTag<
            { #core::mem::size_of::<___ZerocopyTag>() },
        >;

        #tag_consts

        type ___ZerocopyOuterTag = #outer_tag_type;
        type ___ZerocopyInnerTag = #inner_tag_type;

        #variant_structs
        #variants_union

        #raw_enum
        #raw_projections

        #has_tag
        #has_fields
    })
}

pub(crate) fn derive(ctx: &Ctx, _top_level: Trait) -> Result<TokenStream, Error> {
    match &ctx.ast.data {
        Data::Struct(strct) => {
            Ok(derive_projection_struct_union(ctx, strct, Client::ProjectDerive))
        }
        Data::Union(unn) => Ok(derive_projection_struct_union(ctx, unn, Client::ProjectDerive)),
        Data::Enum(enm) => derive_enum(ctx, enm, Client::ProjectDerive),
    }
}
