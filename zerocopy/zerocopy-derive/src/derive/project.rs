// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//

use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse_quote, spanned::Spanned as _, Data, DataEnum, DeriveInput, Error, Expr, Fields, Ident,
    Index, Type,
};

use crate::{
    repr::{EnumRepr, StructUnionRepr},
    util::{
        const_block, generate_tag_enum, Client, Ctx, DataExt, FieldBounds, ImplBlockBuilder, Trait,
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

fn field_alignment(ctx: &Ctx) -> TokenStream {
    let zerocopy_crate = &ctx.zerocopy_crate;
    let fields_preserve_alignment = StructUnionRepr::from_attrs(&ctx.ast.attrs)
        .map(|repr| repr.get_packed().is_none())
        .unwrap();
    if fields_preserve_alignment {
        quote! { ___ZcAlignment }
    } else {
        quote! { #zerocopy_crate::invariant::Unaligned }
    }
}

#[derive(Clone)]
struct FieldProjection {
    variant_id: Box<Expr>,
    field: Box<Type>,
    field_id: Box<Expr>,
}

struct ProjectionInvariants {
    input_validity: Type,
    output_validity: Type,
    output_alignment: TokenStream,
}

fn derive_project_field(
    ctx: &Ctx,
    data: &dyn DataExt,
    client: Client,
    projection: FieldProjection,
    invariants: ProjectionInvariants,
) -> TokenStream {
    let FieldProjection { variant_id, field, field_id } = projection;
    let ProjectionInvariants { input_validity, output_validity, output_alignment } = invariants;
    let zerocopy_crate = &ctx.zerocopy_crate;
    ImplBlockBuilder::new(
        ctx,
        data,
        Trait::ProjectField {
            client,
            variant_id,
            field,
            field_id,
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
        // unless the containing type is packed. The caller-selected validity
        // mapping is justified by the kind of product or sum type being
        // projected.
        type Invariants = (___ZcAliasing, #output_alignment, #output_validity);
    })
    .build()
}

/// Generates field projection implementations for a struct or union.
///
/// `repr_c_union` selects `REPR_C_UNION_VARIANT_ID` for unions whose
/// projections must additionally implement `pointer::cast::Cast`.
pub(crate) fn derive_has_field_struct_union(
    ctx: &Ctx,
    data: &dyn DataExt,
    client: Client,
    repr_c_union: bool,
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
    let variant_id: Box<Expr> = match &ctx.ast.data {
        Data::Struct(_) => parse_quote!({ #zerocopy_crate::STRUCT_VARIANT_ID }),
        Data::Union(_) if repr_c_union => {
            debug_assert!(StructUnionRepr::from_attrs(&ctx.ast.attrs)
                .map(|repr| repr.is_c())
                .unwrap_or(false));
            parse_quote!({ #zerocopy_crate::REPR_C_UNION_VARIANT_ID })
        }
        Data::Union(_) => parse_quote!({ #zerocopy_crate::UNION_VARIANT_ID }),
        Data::Enum(_) => unreachable!(),
    };

    let core = ctx.core_path();
    let has_tag = ImplBlockBuilder::new(ctx, data, Trait::HasTag { client }, FieldBounds::None)
        .inner_extras(quote! {
            type Tag = ();
            type ProjectToTag = #zerocopy_crate::pointer::cast::CastToUnit;
        })
        .build();

    let output_alignment = field_alignment(ctx);
    let has_fields = fields.iter().map(move |(_, ident, ty)| {
        let field_token = ident!(("ẕ{}", ident), ident.span());
        let projection = FieldProjection {
            variant_id: variant_id.clone(),
            field: parse_quote!(#field_token),
            field_id: parse_quote!({ #zerocopy_crate::ident_id!(#ident) }),
        };
        let has_field_trait = Trait::HasField {
            client,
            variant_id: projection.variant_id.clone(),
            field: projection.field.clone(),
            field_id: projection.field_id.clone(),
        };
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

        let uninit = derive_project_field(
            ctx,
            data,
            client,
            projection.clone(),
            ProjectionInvariants {
                input_validity: parse_quote!(#zerocopy_crate::invariant::Uninit),
                output_validity: parse_quote!(#zerocopy_crate::invariant::Uninit),
                output_alignment: output_alignment.clone(),
            },
        );
        let initialized = derive_project_field(
            ctx,
            data,
            client,
            projection.clone(),
            ProjectionInvariants {
                input_validity: parse_quote!(#zerocopy_crate::invariant::Initialized),
                output_validity: parse_quote!(#zerocopy_crate::invariant::Initialized),
                output_alignment: output_alignment.clone(),
            },
        );
        let valid_output = if matches!(&ctx.ast.data, Data::Struct(_)) {
            parse_quote!(#zerocopy_crate::invariant::Valid)
        } else {
            // A valid union need not contain a valid (or initialized) instance
            // of any particular field. `Uninit` is the strongest validity
            // invariant that holds for every field projection.
            parse_quote!(#zerocopy_crate::invariant::Uninit)
        };
        let valid = derive_project_field(
            ctx,
            data,
            client,
            projection,
            ProjectionInvariants {
                input_validity: parse_quote!(#zerocopy_crate::invariant::Valid),
                output_validity: valid_output,
                output_alignment: output_alignment.clone(),
            },
        );

        quote! {
            #has_field
            #uninit
            #initialized
            #valid
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
        let projections = derive_has_field_struct_union(
            &ctx.with_input(&variant_struct),
            &variant_struct.data,
            client,
            false,
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
    let projections = derive_has_field_struct_union(
        &ctx.with_input(&variants_union),
        &variants_union.data,
        client,
        true,
    );

    quote! {
        #variants_union
        #projections
    }
}

fn derive_enum_project_field(
    ctx: &Ctx,
    data: &DataEnum,
    client: Client,
    projection: FieldProjection,
    validity: Type,
    variant_tag: Option<&Ident>,
) -> TokenStream {
    let FieldProjection { variant_id, field, field_id } = projection;
    let zerocopy_crate = &ctx.zerocopy_crate;
    let project_field_trait = Trait::ProjectField {
        client,
        variant_id,
        field,
        field_id,
        invariants: parse_quote!((___ZcAliasing, ___ZcAlignment, #validity)),
    };

    let mut params = vec![
        parse_quote!(___ZcAliasing: #zerocopy_crate::invariant::Aliasing),
        parse_quote!(___ZcAlignment: #zerocopy_crate::invariant::Alignment),
    ];
    let (error, is_projectable) = if let Some(variant_tag) = variant_tag {
        params[0] = parse_quote!(___ZcAliasing: #zerocopy_crate::invariant::Reference);
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
                    let tag = tag.read::<#zerocopy_crate::BecauseImmutable>()
                        as ___ZerocopyTagPrimitive;
                    if tag == #variant_tag {
                        #core::result::Result::Ok(())
                    } else {
                        #core::result::Result::Err(())
                    }
                }
            },
        )
    } else {
        (
            quote! { #zerocopy_crate::util::macro_util::core_reexport::convert::Infallible },
            quote! {},
        )
    };

    ImplBlockBuilder::new(ctx, data, project_field_trait, FieldBounds::None)
        .param_extras(params)
        .inner_extras(quote! {
            type Error = #error;
            type Invariants = (___ZcAliasing, ___ZcAlignment, #validity);
            #is_projectable
        })
        .build()
}

pub(crate) fn derive_has_field_enum(ctx: &Ctx, data: &DataEnum, client: Client) -> TokenStream {
    let zerocopy_crate = &ctx.zerocopy_crate;
    let has_fields = data.variants().into_iter().flat_map(|(variant, fields)| {
        let variant_ident = &variant.unwrap().ident;
        let variants_union_field = variants_union_field_ident(variant_ident);
        let variant_id: Box<Expr> =
            parse_quote!({ #zerocopy_crate::ident_id!(#variant_ident) });
        let variant_tag = tag_ident(variant_ident);

        fields.into_iter().enumerate().map(move |(idx, (vis, ident, ty))| {
            // Rust does not presently support explicit visibility modifiers on
            // enum fields. Keep this assertion so that a future language
            // change cannot silently invalidate the visibility invariant.
            assert!(matches!(vis, syn::Visibility::Inherited));
            let projection = FieldProjection {
                variant_id: variant_id.clone(),
                field: parse_quote!(()),
                field_id: parse_quote!({ #zerocopy_crate::ident_id!(#ident) }),
            };
            let variant_struct_field_index = Index::from(idx + 1);
            let (_, ty_generics, _) = ctx.ast.generics.split_for_impl();
            let has_field_trait = Trait::HasField {
                client,
                variant_id: projection.variant_id.clone(),
                field: projection.field.clone(),
                field_id: projection.field_id.clone(),
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

            let uninit = derive_enum_project_field(
                ctx,
                data,
                client,
                projection.clone(),
                parse_quote!(#zerocopy_crate::invariant::Uninit),
                None,
            );
            let initialized = derive_enum_project_field(
                ctx,
                data,
                client,
                projection.clone(),
                parse_quote!(#zerocopy_crate::invariant::Initialized),
                None,
            );
            let valid = derive_enum_project_field(
                ctx,
                data,
                client,
                projection,
                parse_quote!(#zerocopy_crate::invariant::Valid),
                Some(&variant_tag),
            );

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
        derive_has_field_struct_union(&ctx.with_input(&raw_enum), &raw_enum.data, client, false);
    let has_tag = ImplBlockBuilder::new(ctx, data, Trait::HasTag { client }, FieldBounds::None)
        .inner_extras(quote! {
            type Tag = ___ZerocopyTag;
            type ProjectToTag = #zerocopy_crate::pointer::cast::CastSized;
        })
        .build();
    let has_fields = derive_has_field_enum(ctx, data, client);

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
            Ok(derive_has_field_struct_union(ctx, strct, Client::ProjectDerive, false))
        }
        Data::Union(unn) => {
            Ok(derive_has_field_struct_union(ctx, unn, Client::ProjectDerive, false))
        }
        Data::Enum(enm) => derive_enum(ctx, enm, Client::ProjectDerive),
    }
}
