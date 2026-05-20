use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{Data, DataEnum, DataStruct, DataUnion, Error, Type};

use crate::{
    repr::{EnumRepr, StructUnionRepr},
    util::{
        generate_tag_enum, Ctx, DataExt, FieldBounds, ImplBlockBuilder, PaddingCheck, Trait,
        TraitBound,
    },
    SelfBounds,
};

pub(crate) fn derive_initialize_into_bytes(
    ctx: &Ctx,
    top_level: Trait,
) -> Result<TokenStream, Error> {
    try_gen_trivial_initialize_into_bytes(ctx, top_level).map(Ok).unwrap_or_else(|| {
        match &ctx.ast.data {
            Data::Struct(strct) => derive_initialize_into_bytes_struct(ctx, strct),
            Data::Enum(enm) => derive_initialize_into_bytes_enum(ctx, enm),
            Data::Union(unn) => derive_initialize_into_bytes_union(ctx, unn),
        }
    })
}

fn try_gen_trivial_initialize_into_bytes(
    ctx: &Ctx,
    top_level: Trait,
) -> Option<proc_macro2::TokenStream> {
    // If the top-level trait is `IntoBytes`, `IntoBytes` derive will fail
    // compilation if `Self` is not actually soundly `IntoBytes`, and so we can
    // rely on that for our `zeroize` impl. It's plausible that we could
    // make changes - or Rust could make changes (such as the "trivial bounds"
    // language feature) - that make this no longer true. To hedge against
    // these, we include an explicit `Self: IntoBytes` check in the generated
    // `is_bit_valid`, which is bulletproof.
    //
    // If `ctx.skip_on_error` is true, we can't rely on the `IntoBytes` derive
    // to fail compilation if `Self` is not actually soundly `IntoBytes`.
    if matches!(top_level, Trait::IntoBytes)
        && ctx.ast.generics.params.is_empty()
        && !ctx.skip_on_error
    {
        let zerocopy_crate = &ctx.zerocopy_crate;
        let core = ctx.core_path();

        Some(
            ImplBlockBuilder::new(
                ctx,
                &ctx.ast.data,
                Trait::InitializeIntoBytes,
                FieldBounds::ALL_SELF,
            )
            .self_type_trait_bounds(SelfBounds::All(&[Trait::IntoBytes]))
            .inner_extras(quote!(
                // SAFETY: See inline.
                #[inline(always)]
                fn initialize_padding(ptr: #zerocopy_crate::Ptr<'_, Self, (
                    #zerocopy_crate::invariant::Exclusive,
                    #zerocopy_crate::invariant::Unaligned,
                    #zerocopy_crate::invariant::AsInitialized)>
                ) {
                    if false {
                        fn assert_is_into_bytes<T>()
                        where
                            T: #zerocopy_crate::IntoBytes,
                            T: ?#core::marker::Sized,
                        {
                        }

                        assert_is_into_bytes::<Self>();
                    }
                }
            ))
            .build(),
        )
    } else {
        None
    }
}

fn derive_initialize_into_bytes_struct(
    ctx: &Ctx,
    strct: &DataStruct,
) -> Result<TokenStream, Error> {
    let zerocopy_crate = &ctx.zerocopy_crate;
    let core: TokenStream = ctx.core_path();

    // TODO: This is just the default-repr sized case. We also need a

    let field_offsets_and_layouts = ctx.ast.data.fields().into_iter().map(
        |(_, name, ty)| quote!((#core::mem::offset_of!(Self, #name), #core::mem::size_of::<#ty>())),
    );

    let subfield_zeroizations = ctx.ast.data.fields().into_iter().map(|(_, name, ty)| {
        quote! {{
            // TODO: Need to also emit `AsInitialized`/`Valid` projection impls
            // either here or in `TryFromBytes`.
            let field = #zerocopy_crate::into_inner!(ptr.reborrow().project::<
                _,
                { #zerocopy_crate::STRUCT_VARIANT_ID },
                { #zerocopy_crate::ident_id!(#name) }
            >());
            <#ty as #zerocopy_crate::InitializeIntoBytes>::initialize_padding(field);
        }}
    });

    Ok(ImplBlockBuilder::new(ctx, &ctx.ast.data, Trait::InitializeIntoBytes, FieldBounds::ALL_SELF)
        .self_type_trait_bounds(SelfBounds::All(&[Trait::Sized, Trait::TryFromBytes]))
        .inner_extras(quote!(
            // SAFETY: See inline. TODO
            #[inline(always)]
            fn initialize_padding(mut ptr: #zerocopy_crate::Ptr<'_, Self, (
                #zerocopy_crate::invariant::Exclusive,
                #zerocopy_crate::invariant::Unaligned,
                #zerocopy_crate::invariant::AsInitialized)>
            ) {
                let mut fields = &#zerocopy_crate::util::sort_fields([
                    #(#field_offsets_and_layouts,)*
                ])[..];

                let mut start = 0;

                // Zeroize padding between fields.
                while let [(offset, size), rest @ ..] = fields {
                    fields = rest;

                    // Zero-out any padding between `start` and the field.
                    {
                        let ptr = ptr.as_inner().as_non_null().as_ptr() as *mut _ as *mut u8;
                        let ptr = unsafe { ptr.add(start) };
                        unsafe { #core::ptr::write_bytes(ptr, 0, *offset - start) };
                    }

                    // Advance `start`.
                    start += size;
                }

                // Zeroize padding after the trailing field.
                {
                    let ptr = ptr.as_inner().as_non_null().as_ptr() as *mut _ as *mut u8;
                    let ptr = unsafe { ptr.add(start) };
                    unsafe { #core::ptr::write_bytes(ptr, 0, #core::mem::size_of::<Self>() - start) };
                }

                // Zeroize padding inside fields.
                #(#subfield_zeroizations)*
            }
        ))
        .build())
}

fn derive_initialize_into_bytes_enum(ctx: &Ctx, enm: &DataEnum) -> Result<TokenStream, Error> {
    // TODO: Can this be outside the MVP?
    todo!()
}

fn derive_initialize_into_bytes_union(ctx: &Ctx, unn: &DataUnion) -> Result<TokenStream, Error> {
    // TODO: Can this be outside the MVP?
    todo!()
}
