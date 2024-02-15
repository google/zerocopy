// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use ::proc_macro2::TokenStream;
use ::quote::quote;
use ::syn::{DataEnum, Fields, Generics, Ident, Variant};
use syn::Index;

use crate::EnumRepr;

struct RawIdents {
    r#enum: Ident,
    discriminant: Ident,
    discriminant_value_prefix: String,
    fields: Ident,
    variant_prefix: String,
}

impl RawIdents {
    fn for_enum(ident: &Ident) -> Self {
        Self {
            r#enum: Ident::new(&format!("Raw{ident}Enum"), ident.span()),
            discriminant: Ident::new(&format!("Raw{ident}Discriminant"), ident.span()),
            discriminant_value_prefix: format!("RAW_DISCRIMINANT_"),
            fields: Ident::new(&format!("Raw{ident}Fields"), ident.span()),
            variant_prefix: format!("Raw{ident}Variant"),
        }
    }

    fn discriminant_const(&self, variant: &Ident) -> Ident {
        Ident::new(&format!("{}{}", self.discriminant_value_prefix, variant), variant.span())
    }

    fn variant_struct(&self, variant: &Ident) -> Ident {
        Ident::new(&format!("{}{}", self.variant_prefix, variant), variant.span())
    }
}

/// Generates an implementation of `is_bit_valid` for the given enum input.
pub fn derive_is_bit_valid(
    reprs: &[EnumRepr],
    ident: &Ident,
    generics: &Generics,
    data: &DataEnum,
) -> TokenStream {
    let idents = RawIdents::for_enum(ident);

    if reprs.contains(&EnumRepr::C) {
        derive_is_bit_valid_c(data, generics, &idents)
    } else {
        derive_is_bit_valid_primitive(data, generics, discriminant_repr(reprs), &idents)
    }
}

pub fn discriminant_repr(reprs: &[EnumRepr]) -> &EnumRepr {
    if reprs.contains(&EnumRepr::C) {
        reprs.iter().filter(|&r| r != &EnumRepr::C).next().unwrap_or(&EnumRepr::C)
    } else {
        reprs.first().unwrap()
    }
}

pub fn generate_discriminant_type(data: &DataEnum, repr: &EnumRepr, name: &Ident) -> TokenStream {
    let variants = data.variants.iter().map(|v| {
        let ident = &v.ident;
        if let Some((eq, discriminant)) = &v.discriminant {
            quote! { #ident #eq #discriminant }
        } else {
            quote! { #ident }
        }
    });

    quote! {
        #[repr(#repr)]
        #[allow(dead_code)]
        enum #name {
            #(#variants),*
        }
    }
}

fn generate_discriminant_consts(data: &DataEnum, idents: &RawIdents) -> TokenStream {
    let discriminant = &idents.discriminant;

    let consts = data.variants.iter().map(|v| {
        let ident = &v.ident;
        let const_ident = idents.discriminant_const(ident);
        quote! {
            const #const_ident: [u8; ::core::mem::size_of::<#discriminant>()] = unsafe { ::core::mem::transmute(#discriminant::#ident) };
        }
    });

    quote! {
        #(#consts)*
    }
}

fn generate_variant_struct(
    variant: &Variant,
    generics: &Generics,
    idents: &RawIdents,
    with_tag: bool,
) -> TokenStream {
    let discriminant_ident = &idents.discriminant;
    let variant_struct_ident = idents.variant_struct(&variant.ident);

    let type_params = generics.type_params().map(|p| &p.ident);
    let phantom_ty = quote! {
        ::core::marker::PhantomData<(#(#type_params,)*)>
    };
    let (impl_generics, _, where_clause) = generics.split_for_impl();

    match &variant.fields {
        Fields::Named(fields) => {
            let tag_field =
                if with_tag { Some(quote! { __tag: #discriminant_ident, }) } else { None };

            let struct_fields = fields.named.iter().map(|f| {
                let ident = &f.ident;
                let ty = &f.ty;
                quote! {
                    pub #ident: #ty
                }
            });

            let field_checks = fields.named.iter().map(|f| {
                let ident = &f.ident;
                let ty = &f.ty;
                quote! {
                    <#ty as TryFromBytes>::is_bit_valid(unsafe { this.project(|this| ::core::ptr::addr_of_mut!((*this).#ident)) })
                }
            });

            quote! {
                #[repr(C)]
                #[allow(non_snake_case)]
                struct #variant_struct_ident #impl_generics #where_clause {
                    #tag_field
                    #(#struct_fields,)*
                    _phantom: #phantom_ty,
                }

                impl #variant_struct_ident #impl_generics #where_clause {
                    fn is_bit_valid(this: ::zerocopy::Maybe<'_, Self>) -> bool {
                        true #(&& #field_checks)*
                    }
                }
            }
        }
        Fields::Unnamed(fields) => {
            let tag_field = if with_tag { Some(quote! { #discriminant_ident, }) } else { None };

            let struct_fields = fields.unnamed.iter().map(|f| {
                let ty = &f.ty;
                quote! {
                    pub #ty
                }
            });

            let field_checks = fields.unnamed.iter().enumerate().map(|(i, f)| {
                let i = Index::from(i + tag_field.is_some() as usize);
                let ty = &f.ty;
                quote! {
                    <#ty as TryFromBytes>::is_bit_valid(unsafe { this.project(|this| ::core::ptr::addr_of_mut!((*this).#i)) })
                }
            });

            quote! {
                #[repr(C)]
                #[allow(non_snake_case)]
                struct #variant_struct_ident #impl_generics (
                    #tag_field
                    #(#struct_fields,)*
                    #phantom_ty,
                ) #where_clause;

                impl #variant_struct_ident #impl_generics #where_clause {
                    fn is_bit_valid(this: ::zerocopy::Maybe<'_, Self>) -> bool {
                        true #(&& #field_checks)*
                    }
                }
            }
        }
        Fields::Unit => {
            let tag_field = if with_tag { Some(quote! { #discriminant_ident, }) } else { None };

            quote! {
                #[repr(C)]
                #[allow(non_snake_case)]
                struct #variant_struct_ident #impl_generics (
                    #tag_field
                    #phantom_ty,
                ) #where_clause;

                impl #variant_struct_ident #impl_generics #where_clause {
                    fn is_bit_valid(_: ::zerocopy::Maybe<'_, Self>) -> bool { true }
                }
            }
        }
    }
}

fn derive_is_bit_valid_c(data: &DataEnum, generics: &Generics, idents: &RawIdents) -> TokenStream {
    let discriminant_type = generate_discriminant_type(data, &EnumRepr::C, &idents.discriminant);
    let discriminant_consts = generate_discriminant_consts(data, idents);
    let variant_structs = data
        .variants
        .iter()
        .map(|variant| generate_variant_struct(variant, generics, idents, false));

    let raw_ident = &idents.r#enum;
    let discriminant_ident = &idents.discriminant;
    let fields_ident = &idents.fields;

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let variant_idents = data.variants.iter().map(|v| &v.ident);
    let variant_struct_idents = data.variants.iter().map(|v| idents.variant_struct(&v.ident));

    let match_arms = data.variants.iter().map(|variant| {
        let value_ident = idents.discriminant_const(&variant.ident);
        let variant_struct = idents.variant_struct(&variant.ident);

        quote! {
            #value_ident => {
                let candidate = unsafe { fields.cast_unsized(|p: *mut #fields_ident| p as *mut #variant_struct).assume_initialized() };
                #variant_struct::is_bit_valid(candidate)
            }
        }
    });

    quote! {
        // SAFETY: We use `is_bit_valid` to validate that the bit pattern
        // corresponds to one of the enum's variant discriminants. Then, we
        // check the bit validity of each field of that variant. Thus, this is a
        // sound implementation of `is_bit_valid`.
        fn is_bit_valid(
            candidate: ::zerocopy::Ptr<
                '_,
                Self,
                (
                    ::zerocopy::pointer::invariant::Shared,
                    ::zerocopy::pointer::invariant::AnyAlignment,
                    ::zerocopy::pointer::invariant::Initialized,
                ),
            >,
        ) -> ::zerocopy::macro_util::core_reexport::primitive::bool {
            use ::zerocopy::macro_util::core_reexport;

            #discriminant_type
            #discriminant_consts
            #(#variant_structs)*

            #[repr(C)]
            #[allow(non_snake_case)]
            union #fields_ident #impl_generics #where_clause {
                #(
                    pub #variant_idents: ::core::mem::ManuallyDrop<
                        #variant_struct_idents #ty_generics,
                    >,
                )*
            }

            #[repr(C)]
            struct #raw_ident #impl_generics #where_clause {
                pub __tag: #discriminant_ident,
                pub fields: #fields_ident #ty_generics,
            }

            // SAFETY:
            // - `cast` is implemented as required.
            // - By definition, `*mut Self` and `*mut [u8; size_of::<Self>()]`
            //   are types of the same size.
            let discriminant = unsafe { candidate.cast_unsized(|p: *mut Self| p as *mut [core_reexport::primitive::u8; core_reexport::mem::size_of::<#discriminant_ident>()]) };
            // SAFETY: Since `candidate` has the invariant `Initialized`, we
            // know that `candidate`'s referent (and thus `discriminant`'s
            // referent) is as-initialized as `Self`. Since all of the allowed
            // `repr`s are types for which all bytes are always initialized, we
            // know that `discriminant`'s referent has all of its bytes
            // initialized. Since `[u8; N]`'s validity invariant is just that
            // all of its bytes are initialized, we know that `discriminant`'s
            // referent is bit-valid.
            let discriminant = unsafe { discriminant.assume_valid() };
            let discriminant = discriminant.read_unaligned();

            let fields = unsafe {
                candidate
                    .cast_unsized(|p: *mut Self| p as *mut #raw_ident)
                    .assume_initialized()
                    .project(|p: *mut #raw_ident| ::core::ptr::addr_of_mut!((*p).fields))
            };

            match discriminant {
                #(#match_arms,)*
                _ => false,
            }
        }
    }
}

fn derive_is_bit_valid_primitive(
    data: &DataEnum,
    generics: &Generics,
    int: &EnumRepr,
    idents: &RawIdents,
) -> TokenStream {
    let discriminant_type = generate_discriminant_type(data, int, &idents.discriminant);
    let discriminant_consts = generate_discriminant_consts(data, idents);
    let variant_structs = data
        .variants
        .iter()
        .map(|variant| generate_variant_struct(variant, generics, idents, true));

    let discriminant_ident = &idents.discriminant;

    let match_arms = data.variants.iter().map(|variant| {
        let value_ident = idents.discriminant_const(&variant.ident);
        let variant_struct = idents.variant_struct(&variant.ident);

        quote! {
            #value_ident => {
                let candidate = unsafe { candidate.cast_unsized(|p: *mut Self| p as *mut #variant_struct).assume_initialized() };
                #variant_struct::is_bit_valid(candidate)
            }
        }
    });

    quote! {
        // SAFETY: We use `is_bit_valid` to validate that the bit pattern
        // corresponds to one of the enum's variant discriminants. Then, we
        // check the bit validity of each field of that variant. Thus, this is a
        // sound implementation of `is_bit_valid`.
        fn is_bit_valid(
            candidate: ::zerocopy::Ptr<
                '_,
                Self,
                (
                    ::zerocopy::pointer::invariant::Shared,
                    ::zerocopy::pointer::invariant::AnyAlignment,
                    ::zerocopy::pointer::invariant::Initialized,
                ),
            >,
        ) -> ::zerocopy::macro_util::core_reexport::primitive::bool {
            use ::zerocopy::macro_util::core_reexport;

            #discriminant_type
            #discriminant_consts
            #(#variant_structs)*

            // SAFETY:
            // - `cast` is implemented as required.
            // - By definition, `*mut Self` and `*mut [u8; size_of::<Self>()]`
            //   are types of the same size.
            let discriminant = unsafe { candidate.cast_unsized(|p: *mut Self| p as *mut [core_reexport::primitive::u8; core_reexport::mem::size_of::<#discriminant_ident>()]) };
            // SAFETY: Since `candidate` has the invariant `Initialized`, we
            // know that `candidate`'s referent (and thus `discriminant`'s
            // referent) is as-initialized as `Self`. Since all of the allowed
            // `repr`s are types for which all bytes are always initialized, we
            // know that `discriminant`'s referent has all of its bytes
            // initialized. Since `[u8; N]`'s validity invariant is just that
            // all of its bytes are initialized, we know that `discriminant`'s
            // referent is bit-valid.
            let discriminant = unsafe { discriminant.assume_valid() };
            let discriminant = discriminant.read_unaligned();

            match discriminant {
                #(#match_arms,)*
                _ => false,
            }
        }
    }
}
