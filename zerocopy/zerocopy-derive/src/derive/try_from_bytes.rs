// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
use proc_macro2::TokenStream;
use quote::quote;
use syn::{spanned::Spanned as _, Data, DataEnum, DataStruct, DataUnion, Error};

use crate::{
    derive::project::{
        derive_enum, derive_projection_struct_union, generate_tag_consts, struct_union_variant_id,
        tag_ident,
    },
    repr::EnumRepr,
    util::{
        enum_size_from_repr, generate_tag_enum, Client, Ctx, DataExt, FieldBounds,
        ImplBlockBuilder, Trait, TraitBound,
    },
};

/// Generates an implementation of `is_bit_valid` for an arbitrary enum.
///
/// For an enum with fields, [`derive_enum`] generates the representation model
/// and projection impls. This function reads the tag, matches it against the
/// enum's discriminants, and validates each field of the selected variant
/// through those projections. A fieldless enum needs only the generated tag
/// enum and discriminant constants.
pub(crate) fn derive_is_bit_valid(
    ctx: &Ctx,
    data: &DataEnum,
    repr: &EnumRepr,
) -> Result<TokenStream, Error> {
    if !(repr.is_c() || repr.is_primitive()) {
        return Err(Error::new(
            ctx.ast.span(),
            "must have #[repr(C)] or #[repr(Int)] attribute in order to guarantee this type's memory layout",
        ));
    }

    let trait_path = Trait::TryFromBytes.crate_path(ctx);
    let zerocopy_crate = &ctx.zerocopy_crate;
    let core = ctx.core_path();
    let projections = if data.fields().is_empty() {
        let tag_enum = generate_tag_enum(ctx, repr, data);
        let tag_consts = generate_tag_consts(data);
        quote! {
            #tag_enum

            type ___ZerocopyTagPrimitive = #zerocopy_crate::util::macro_util::SizeToTag<
                { #core::mem::size_of::<___ZerocopyTag>() },
            >;

            #tag_consts
        }
    } else {
        derive_enum(ctx, data, Client::TryFromBytesDerive)?
    };

    let match_arms = data.variants().into_iter().map(|(variant, fields)| {
        let variant = &variant.unwrap().ident;
        let tag = tag_ident(variant);
        let field_names = fields.iter().map(|(_, name, _)| name);
        let field_tys = fields.iter().map(|(_, _, ty)| ty);
        quote! {
            #tag => true #(&& {
                let field_candidate = #zerocopy_crate::into_inner!(
                    candidate.reborrow().project::<
                        #zerocopy_crate::project_clients::TryFromBytesDerive,
                        _,
                        { #zerocopy_crate::ident_id!(#variant) },
                        { #zerocopy_crate::ident_id!(#field_names) },
                    >()
                );
                <#field_tys as #trait_path>::is_bit_valid(field_candidate)
            })*
        }
    });

    Ok(quote! {
        // SAFETY: We use `is_bit_valid` to validate that the bit pattern of the
        // enum's tag corresponds to one of the enum's discriminants. Then, we
        // check the bit validity of each field of the corresponding variant.
        // Thus, this is a sound implementation of `is_bit_valid`.
        #[inline]
        fn is_bit_valid<___ZcAlignment>(
            mut candidate: #zerocopy_crate::Maybe<'_, Self, ___ZcAlignment>,
        ) -> #core::primitive::bool
        where
            ___ZcAlignment: #zerocopy_crate::invariant::Alignment,
        {
            #projections

            let tag = candidate
                .reborrow()
                .cast::<
                    ___ZerocopyTagPrimitive,
                    #zerocopy_crate::pointer::cast::CastSized,
                    (#zerocopy_crate::pointer::BecauseRead, _),
                >()
                .recall_validity::<_, (_, (_, _))>()
                .read::<#zerocopy_crate::BecauseImmutable>();

            match tag {
                #(#match_arms,)*
                _ => false,
            }
        }
    })
}
pub(crate) fn derive_try_from_bytes(ctx: &Ctx, top_level: Trait) -> Result<TokenStream, Error> {
    match &ctx.ast.data {
        Data::Struct(strct) => derive_try_from_bytes_struct(ctx, strct, top_level),
        Data::Enum(enm) => derive_try_from_bytes_enum(ctx, enm, top_level),
        Data::Union(unn) => Ok(derive_try_from_bytes_union(ctx, unn, top_level)),
    }
}
fn derive_try_from_bytes_struct(
    ctx: &Ctx,
    strct: &DataStruct,
    top_level: Trait,
) -> Result<TokenStream, Error> {
    let extras = try_gen_trivial_is_bit_valid(ctx, top_level).unwrap_or_else(|| {
        let zerocopy_crate = &ctx.zerocopy_crate;
        let fields = strct.fields();
        let field_names = fields.iter().map(|(_vis, name, _ty)| name);
        let field_tys = fields.iter().map(|(_vis, _name, ty)| ty);
        let core = ctx.core_path();
        quote!(
            // SAFETY: We use `is_bit_valid` to validate that each field is
            // bit-valid, and only return `true` if all of them are. The bit
            // validity of a struct is just the composition of the bit
            // validities of its fields, so this is a sound implementation
            // of `is_bit_valid`.
            #[inline]
            fn is_bit_valid<___ZcAlignment>(
                mut candidate: #zerocopy_crate::Maybe<'_, Self, ___ZcAlignment>,
            ) -> #core::primitive::bool
            where
                ___ZcAlignment: #zerocopy_crate::invariant::Alignment,
            {
                true #(&& {
                    let field_candidate = #zerocopy_crate::into_inner!(candidate.reborrow().project::<
                        #zerocopy_crate::project_clients::TryFromBytesDerive,
                        _,
                        { #zerocopy_crate::STRUCT_VARIANT_ID },
                        { #zerocopy_crate::ident_id!(#field_names) }
                    >());
                    <#field_tys as #zerocopy_crate::TryFromBytes>::is_bit_valid(field_candidate)
                })*
            }
        )
    });
    Ok(ImplBlockBuilder::new(ctx, strct, Trait::TryFromBytes, FieldBounds::ALL_SELF)
        .inner_extras(extras)
        .outer_extras(derive_projection_struct_union(ctx, strct, Client::TryFromBytesDerive))
        .build())
}
fn derive_try_from_bytes_union(ctx: &Ctx, unn: &DataUnion, top_level: Trait) -> TokenStream {
    let field_type_trait_bounds = FieldBounds::All(&[TraitBound::Slf]);

    let zerocopy_crate = &ctx.zerocopy_crate;
    let union_variant_id = struct_union_variant_id(ctx);
    let extras = try_gen_trivial_is_bit_valid(ctx, top_level).unwrap_or_else(|| {
        let fields = unn.fields();
        let field_names = fields.iter().map(|(_vis, name, _ty)| name);
        let field_tys = fields.iter().map(|(_vis, _name, ty)| ty);
        let core = ctx.core_path();
        quote!(
            // SAFETY: We use `is_bit_valid` to validate that any field is
            // bit-valid; we only return `true` if at least one of them is.
            // The bit validity of a union is not yet well defined in Rust,
            // but it is guaranteed to be no more strict than this
            // definition. See #696 for a more in-depth discussion.
            #[inline]
            fn is_bit_valid<___ZcAlignment>(
                mut candidate: #zerocopy_crate::Maybe<'_, Self, ___ZcAlignment>,
            ) -> #core::primitive::bool
            where
                ___ZcAlignment: #zerocopy_crate::invariant::Alignment,
            {
                false #(|| {
                    let field_candidate = #zerocopy_crate::into_inner!(
                        candidate.reborrow().project::<
                            #zerocopy_crate::project_clients::TryFromBytesDerive,
                            _,
                            { #union_variant_id },
                            { #zerocopy_crate::ident_id!(#field_names) },
                        >()
                    );

                    <#field_tys as #zerocopy_crate::TryFromBytes>::is_bit_valid(field_candidate)
                })*
            }
        )
    });
    ImplBlockBuilder::new(ctx, unn, Trait::TryFromBytes, field_type_trait_bounds)
        .inner_extras(extras)
        .outer_extras(derive_projection_struct_union(ctx, unn, Client::TryFromBytesDerive))
        .build()
}
fn derive_try_from_bytes_enum(
    ctx: &Ctx,
    enm: &DataEnum,
    top_level: Trait,
) -> Result<TokenStream, Error> {
    let repr = EnumRepr::from_attrs(&ctx.ast.attrs)?;

    // If an enum has no fields, it has a well-defined integer representation,
    // and every possible bit pattern corresponds to a valid discriminant tag,
    // then it *could* be `FromBytes` (even if the user hasn't derived
    // `FromBytes`). This holds if, for `repr(uN)` or `repr(iN)`, there are 2^N
    // variants.
    let could_be_from_bytes = enum_size_from_repr(&repr)
        .map(|size| enm.fields().is_empty() && enm.variants.len() == 1usize << size)
        .unwrap_or(false);

    let trivial_is_bit_valid = try_gen_trivial_is_bit_valid(ctx, top_level);
    let extra = match (trivial_is_bit_valid, could_be_from_bytes) {
        (Some(is_bit_valid), _) => is_bit_valid,
        // SAFETY: It would be sound for the enum to implement `FromBytes`, as
        // required by `gen_trivial_is_bit_valid_unchecked`.
        (None, true) => unsafe { gen_trivial_is_bit_valid_unchecked(ctx) },
        (None, false) => match derive_is_bit_valid(ctx, enm, &repr) {
            Ok(extra) => extra,
            Err(_) if ctx.skip_on_error => return Ok(TokenStream::new()),
            Err(e) => return Err(e),
        },
    };

    Ok(ImplBlockBuilder::new(ctx, enm, Trait::TryFromBytes, FieldBounds::ALL_SELF)
        .inner_extras(extra)
        .build())
}
fn try_gen_trivial_is_bit_valid(ctx: &Ctx, top_level: Trait) -> Option<proc_macro2::TokenStream> {
    // If the top-level trait is `FromBytes` and `Self` has no type parameters,
    // then the `FromBytes` derive will fail compilation if `Self` is not
    // actually soundly `FromBytes`, and so we can rely on that for our
    // `is_bit_valid` impl. It's plausible that we could make changes - or Rust
    // could make changes (such as the "trivial bounds" language feature) - that
    // make this no longer true. To hedge against these, we include an explicit
    // `Self: FromBytes` check in the generated `is_bit_valid`, which is
    // bulletproof.
    //
    // If `ctx.skip_on_error` is true, we can't rely on the `FromBytes` derive
    // to fail compilation if `Self` is not actually soundly `FromBytes`.
    if matches!(top_level, Trait::FromBytes)
        && ctx.ast.generics.params.is_empty()
        && !ctx.skip_on_error
    {
        let zerocopy_crate = &ctx.zerocopy_crate;
        let core = ctx.core_path();
        Some(quote!(
            // SAFETY: See inline.
            #[inline(always)]
            fn is_bit_valid<___ZcAlignment>(
                _candidate: #zerocopy_crate::Maybe<'_, Self, ___ZcAlignment>,
            ) -> #core::primitive::bool
            where
                ___ZcAlignment: #zerocopy_crate::invariant::Alignment,
            {
                if false {
                    fn assert_is_from_bytes<T>()
                    where
                        T: #zerocopy_crate::FromBytes,
                        T: ?#core::marker::Sized,
                    {
                    }

                    assert_is_from_bytes::<Self>();
                }

                // SAFETY: The preceding code only compiles if `Self:
                // FromBytes`. Thus, this code only compiles if all initialized
                // byte sequences represent valid instances of `Self`.
                true
            }
        ))
    } else {
        None
    }
}

/// # Safety
///
/// All initialized bit patterns must be valid for `Self`.
unsafe fn gen_trivial_is_bit_valid_unchecked(ctx: &Ctx) -> proc_macro2::TokenStream {
    let zerocopy_crate = &ctx.zerocopy_crate;
    let core = ctx.core_path();
    quote!(
        // SAFETY: The caller of `gen_trivial_is_bit_valid_unchecked` has
        // promised that all initialized bit patterns are valid for `Self`.
        #[inline(always)]
        fn is_bit_valid<___ZcAlignment>(
            _candidate: #zerocopy_crate::Maybe<'_, Self, ___ZcAlignment>,
        ) -> #core::primitive::bool
        where
            ___ZcAlignment: #zerocopy_crate::invariant::Alignment,
        {
            true
        }
    )
}
