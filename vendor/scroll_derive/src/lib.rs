#![recursion_limit = "1024"]

extern crate proc_macro;

use proc_macro2::Span;
use quote::{ToTokens, format_ident, quote};
use syn::Ident;

fn extract_idents_and_offset(
    fields: &syn::punctuated::Punctuated<syn::Field, syn::token::Comma>,
) -> (Vec<(proc_macro2::TokenStream, &syn::Field)>, syn::Ident) {
    // first iterate idents
    let idents: Vec<_> = fields
        .into_iter()
        .enumerate()
        .map(|(i, f)| {
            let ident = f.ident.as_ref().map(|i| quote! {#i}).unwrap_or({
                let t = proc_macro2::Literal::usize_unsuffixed(i);
                quote! {#t}
            });
            (ident, f)
        })
        .collect();
    // iterate until we have no field that matches our offset
    let offset = fresh_name(
        &fields,
        proc_macro2::Ident::new("offset", Span::call_site()),
    );

    (idents, offset)
}

/// Generates a fresh name that will not clash with any field named the same
/// NB: there is probably a more efficient algorithm than this worst case O^2 runtime, but even for
/// a struct with hundreds of fields all clashing with increasing _ prefixes, which is a highly
/// degenerate example input, it is fine.
fn fresh_name(
    fields: &syn::punctuated::Punctuated<syn::Field, syn::token::Comma>,
    mut target: proc_macro2::Ident,
) -> Ident {
    while fields.iter().any(|f| {
        f.ident
            .as_ref()
            .map(|ident| ident == &target)
            .unwrap_or(false)
    }) {
        target = format_ident!("_{target}");
    }
    target
}

fn extract_lifetime(
    gp: &syn::punctuated::Punctuated<syn::GenericParam, syn::token::Comma>,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let mut lifetimes = gp
        .iter()
        .filter_map(|param: &syn::GenericParam| match param {
            syn::GenericParam::Lifetime(lifetime) => Some(lifetime.lifetime.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    if lifetimes.len() > 1 {
        panic!("Pread cannot be derived for multiple lifetimes")
    }
    let lifetime = lifetimes
        .pop()
        .unwrap_or(syn::Lifetime::new("'a", Span::call_site()));
    // alpha rename/make the thing fresh
    let alpha = format!("'{}_fresh", lifetime.ident.to_string());
    (
        lifetime.to_token_stream(),
        syn::Lifetime::new(&alpha.to_string(), lifetime.span()).to_token_stream(),
    )
}

fn impl_field(
    ident: &proc_macro2::TokenStream,
    ty: &syn::Type,
    src: &proc_macro2::Ident,
    default_ctx: &proc_macro2::TokenStream,
    custom_ctx: Option<&proc_macro2::TokenStream>,
    offset: &Ident,
    noctx: bool,
) -> proc_macro2::TokenStream {
    let ctx = custom_ctx.unwrap_or(default_ctx);
    match ty {
        syn::Type::Group(group) => impl_field(
            ident,
            &group.elem,
            src,
            default_ctx,
            custom_ctx,
            offset,
            noctx,
        ),
        _ => {
            if noctx {
                quote! {
                    let #ident = #src.gread::<#ty>(#offset)?;
                }
            } else {
                quote! {
                    let #ident = #src.gread_with::<#ty>(#offset, #ctx)?;
                }
            }
        }
    }
}

/// Retrieve the field attribute with given ident e.g:
/// ```ignore
/// #[attr_ident(..)]
/// field: T,
/// ```
fn get_attr<'a>(attr_ident: &str, field: &'a syn::Field) -> Option<&'a syn::Attribute> {
    field
        .attrs
        .iter()
        .find(|attr| attr.path().is_ident(attr_ident))
}

/// Gets the `TokenStream` for the custom ctx set in the `ctx` attribute. e.g. `expr` in the following
/// ```ignore
/// #[scroll(ctx = expr)]
/// field: T,
/// ```
fn custom_ctx(field: &syn::Field, noctx: &mut bool) -> Option<proc_macro2::TokenStream> {
    get_attr("scroll", field).and_then(|x| {
        // parsed #[scroll..]
        // `expr` is `None` if the `ctx` key is not used.
        let mut attrib = None;
        let res = x.parse_nested_meta(|meta| {
            // parsed #[scroll(..)]
            if meta.path.is_ident("ctx") {
                // parsed #[scroll(ctx..)]
                let value = meta.value()?; // parsed #[scroll(ctx = ..)]
                attrib = Some(value.parse::<syn::Expr>()?.into_token_stream()); // parsed #[scroll(ctx = expr)]
                return Ok(());
            }
            if meta.path.is_ident("noctx") {
                // parsed #[scroll(noctx)]
                *noctx = true;
                return Ok(());
            }
            Err(meta.error(match meta.path.get_ident() {
                Some(ident) => format!("unrecognized attribute: {ident}"),
                None => "unrecognized and invalid attribute".to_owned(),
            }))
        });
        match res {
            Ok(()) => attrib,
            Err(e) => Some(e.into_compile_error()),
        }
    })
}

fn impl_struct(
    name: &syn::Ident,
    fields: &syn::punctuated::Punctuated<syn::Field, syn::Token![,]>,
    generics: &syn::Generics,
    unnamed: bool,
) -> proc_macro2::TokenStream {
    let offset = fresh_name(
        fields,
        syn::Ident::new("offset", proc_macro2::Span::call_site()),
    );
    let src = fresh_name(
        fields,
        syn::Ident::new("src", proc_macro2::Span::call_site()),
    );
    let ctx = fresh_name(
        fields,
        syn::Ident::new("ctx", proc_macro2::Span::call_site()),
    )
    .to_token_stream();
    let (items, item_assignments) = fields
        .iter()
        .enumerate()
        .map(|(i, f)| {
            let (ident, prefixed_ident) = &f
                .ident
                .as_ref()
                .map(|i| (quote! {#i}, quote! {#i}))
                .unwrap_or({
                    let t = proc_macro2::Literal::usize_unsuffixed(i);
                    let suf = if unnamed {
                        syn::Ident::new(&format!("_{t}"), proc_macro2::Span::call_site())
                            .into_token_stream()
                    } else {
                        t.clone().to_token_stream()
                    };
                    (quote! {#t}, suf)
                });
            let ty = &f.ty;
            // parse the `expr` out of #[scroll(ctx = expr)]
            let mut noctx = false;
            let custom_ctx = custom_ctx(f, &mut noctx);
            (
                impl_field(
                    &prefixed_ident,
                    ty,
                    &src,
                    &ctx,
                    custom_ctx.as_ref(),
                    &offset,
                    noctx,
                ),
                quote! { #ident: #prefixed_ident },
            )
        })
        .collect::<(Vec<_>, Vec<_>)>();

    let gl = &generics.lt_token;
    let gp = &generics.params;
    let gg = &generics.gt_token;
    let gn = gp.iter().map(|param: &syn::GenericParam| match param {
        syn::GenericParam::Type(t) => {
            let ident = &t.ident;
            quote! { #ident }
        }
        p => quote! { #p },
    });

    let (lifetime, _fresh_lifetime) = extract_lifetime(gp);
    let gn = quote! { #gl #( #gn ),* #gg };
    // drop the lifetime from our generic params, since we already grabbed it
    let initial_generic_params = gp
        .iter()
        .filter_map(|param: &syn::GenericParam| match param {
            syn::GenericParam::Lifetime(_) => None,
            p => Some(p),
        })
        .collect::<Vec<_>>();
    let lhs_gp = if !initial_generic_params.is_empty() {
        quote! { #( #initial_generic_params ),* }
    } else {
        quote! {}
    };

    let gw = if !gp.is_empty() {
        let gi = gp.iter().filter_map(|param: &syn::GenericParam| match param {
            syn::GenericParam::Type(t) => Some({
                let ident = &t.ident;
                quote! {
                    #ident : ::scroll::ctx::TryFromCtx<#lifetime, ::scroll::Endian, Error = ::scroll::Error>,
                    ::scroll::Error : ::std::convert::From<< #ident as ::scroll::ctx::TryFromCtx<#lifetime, ::scroll::Endian>>::Error>,
                    < #ident as ::scroll::ctx::TryFromCtx<#lifetime, ::scroll::Endian>>::Error : ::std::convert::From<scroll::Error>
                }
            }),
            syn::GenericParam::Lifetime(_) => None,
            p => Some(quote! { #p })
        }).collect::<Vec<_>>();
        if !gi.is_empty() {
            // NB: that extra comma after * is very important
            quote! { #( #gi ),*,  }
        } else {
            quote! {}
        }
    } else {
        quote! {}
    };

    quote! {
     impl<#lifetime, #lhs_gp > ::scroll::ctx::TryFromCtx<#lifetime, ::scroll::Endian> for #name #gn
         where #gw #name #gn : #lifetime {
            // TODO: allow passing user error here
            type Error = ::scroll::Error;
            #[inline]
            fn try_from_ctx(#src: &#lifetime [u8], #ctx: ::scroll::Endian) -> ::scroll::export::result::Result<(Self, usize), Self::Error> {
              use ::scroll::Pread;
              let #offset = &mut 0;
              #(#items)*
              Ok((Self { #(#item_assignments,)* }, *#offset))
            }
        }
    }
}

fn ensure_fieldless(variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>) {
    for variant in variants {
        if !variant.fields.is_empty() {
            panic!("Deriving enums in scroll must be primitive, fieldless enums");
        }
    }
}

const VALID_PRIMITIVE_REPRS: &[&'static str] = &[
    "i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128",
];

fn extract_repr_type(ast: &syn::DeriveInput) -> syn::Ident {
    let mut repr_type: Option<syn::Ident> = None;
    for attr in &ast.attrs {
        if attr.path().is_ident("repr") {
            let _ = attr.parse_nested_meta(|meta| {
                for prim in VALID_PRIMITIVE_REPRS {
                    if meta.path.is_ident(prim) {
                        repr_type = meta.path.get_ident().cloned();
                        return Ok(());
                    }
                }
                Ok(())
            });
        };
    }
    let Some(repr_type) = repr_type else {
        panic!("Deriving pread on enum requires repr with one of: {VALID_PRIMITIVE_REPRS:?}");
    };
    repr_type
}

fn impl_try_from_ctx_enum(
    name: &syn::Ident,
    repr_type: syn::Ident,
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
) -> proc_macro2::TokenStream {
    let variant_consts = variants.iter().map(|variant| {
        let ident = &variant.ident;
        let const_name = format_ident!("_{}", ident.to_string().to_uppercase());
        quote! {
            const #const_name: #repr_type = #name::#ident as #repr_type;
        }
    });
    let variant_cases = variants.iter().map(|variant| {
        let ident = &variant.ident;
        let const_name = format_ident!("_{}", ident.to_string().to_uppercase());
        quote! {
            #const_name => #name::#ident,
        }
    });
    let static_msg = format!(
        "No variants matched a discriminant of type {}",
        repr_type.to_string()
    );
    quote! {
     impl<'a> ::scroll::ctx::TryFromCtx<'a, ::scroll::Endian> for #name {
            type Error = ::scroll::Error;
            #[inline]
            fn try_from_ctx(src: &'a [u8], ctx: ::scroll::Endian) -> ::scroll::export::result::Result<(Self, usize), Self::Error> {
              use ::scroll::Pread;
              #(#variant_consts)*
              let offset = &mut 0;
              let val = match src.gread_with::<#repr_type>(offset, ctx)? {
                  #(#variant_cases)*
                  _ => return Err(::scroll::Error::BadInput { size: *offset, msg: #static_msg})
              };
              Ok((val, *offset))
            }
        }
    }
}

fn validate_enum(ast: &syn::DeriveInput, data: &syn::DataEnum) -> Ident {
    let repr_type = extract_repr_type(ast);
    ensure_fieldless(&data.variants);
    repr_type
}

fn impl_try_from_ctx(ast: &syn::DeriveInput) -> proc_macro2::TokenStream {
    let name = &ast.ident;
    let generics = &ast.generics;
    match &ast.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => impl_struct(name, &fields.named, generics, false),
            syn::Fields::Unnamed(fields) => impl_struct(name, &fields.unnamed, generics, true),
            _ => {
                panic!("Pread can not be derived for unit structs")
            }
        },
        syn::Data::Enum(data) => {
            let repr_type = validate_enum(ast, data);
            impl_try_from_ctx_enum(&ast.ident, repr_type, &data.variants)
        }
        _ => panic!("Pread can only be derived for structs and primitive enums"),
    }
}

#[proc_macro_derive(Pread, attributes(scroll))]
pub fn derive_pread(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    let generated = impl_try_from_ctx(&ast);
    generated.into()
}

fn impl_pwrite_field(
    ident: &proc_macro2::TokenStream,
    ty: &syn::Type,
    default_ctx: &proc_macro2::TokenStream,
    custom_ctx: Option<&proc_macro2::TokenStream>,
    offset: &proc_macro2::Ident,
    noctx: bool,
) -> proc_macro2::TokenStream {
    let ctx = custom_ctx.unwrap_or(default_ctx);
    match ty {
        syn::Type::Array(array) => match &array.len {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(int),
                ..
            }) => {
                let size = int.base10_parse::<usize>().unwrap();
                quote! {
                    for i in 0..#size {
                        dst.gwrite_with(&self.#ident[i], #offset, #ctx)?;
                    }
                }
            }
            _ => panic!("Pwrite derive with bad array constexpr"),
        },
        syn::Type::Group(group) => {
            impl_pwrite_field(ident, &group.elem, default_ctx, custom_ctx, offset, noctx)
        }
        syn::Type::Reference(reference) => match *reference.elem {
            syn::Type::Slice(_) => {
                quote! {
                    dst.gwrite_with(self.#ident, #offset, ())?
                }
            }
            syn::Type::Path(ref path) => {
                if path.path.get_ident().unwrap().to_string().as_str() == "str" {
                    quote! {
                        dst.gwrite(self.#ident, #offset)?
                    }
                } else {
                    quote! {
                        dst.gwrite_with(self.#ident, #offset, #ctx)?
                    }
                }
            }
            _ => {
                quote! {
                    dst.gwrite_with(self.#ident, #offset, #ctx)?
                }
            }
        },
        _ => {
            quote! {
                dst.gwrite_with(&self.#ident, #offset, #ctx)?
            }
        }
    }
}

fn impl_try_into_ctx(
    name: &syn::Ident,
    fields: &syn::punctuated::Punctuated<syn::Field, syn::Token![,]>,
    generics: &syn::Generics,
) -> proc_macro2::TokenStream {
    let (idents, offset) = extract_idents_and_offset(fields);
    let ctx = fresh_name(
        fields,
        syn::Ident::new("ctx", proc_macro2::Span::call_site()),
    )
    .to_token_stream();
    let items: Vec<_> = idents
        .iter()
        .map(|(ident, f)| {
            let ty = &f.ty;
            let mut noctx = false;
            let custom_ctx = custom_ctx(f, &mut noctx);
            impl_pwrite_field(ident, ty, &ctx, custom_ctx.as_ref(), &offset, noctx)
        })
        .collect();

    let gl = &generics.lt_token;
    let gp = &generics.params;
    let gg = &generics.gt_token;
    let gn = gp.iter().map(|param: &syn::GenericParam| match param {
        syn::GenericParam::Type(t) => {
            let ident = &t.ident;
            quote! { #ident }
        }
        p => quote! { #p },
    });
    let gn = quote! { #gl #( #gn ),* #gg };
    // it's always important to keep it _fresh_ when we pwrite
    let (_lifetime, fresh_lifetime) = extract_lifetime(gp);
    let gwref = if !gp.is_empty() {
        let gi: Vec<_> = gp.iter().filter_map(|param: &syn::GenericParam| match param {
            syn::GenericParam::Type(t) => {
                let ident = &t.ident;
                Some(quote! {
                    &#fresh_lifetime #ident : ::scroll::ctx::TryIntoCtx<::scroll::Endian>,
                    ::scroll::Error: ::std::convert::From<<&#fresh_lifetime #ident as ::scroll::ctx::TryIntoCtx<::scroll::Endian>>::Error>,
                    <&#fresh_lifetime #ident as ::scroll::ctx::TryIntoCtx<::scroll::Endian>>::Error: ::std::convert::From<scroll::Error>
                })
            },
            syn::GenericParam::Lifetime(_) => None,
            p => Some(quote! { #p }),
        }).collect();
        if !gi.is_empty() {
            quote! { where #( #gi ),* }
        } else {
            quote! {}
        }
    } else {
        quote! {}
    };
    let gw = if !gp.is_empty() {
        let gi = gp.iter().filter_map(|param: &syn::GenericParam| match param {
            syn::GenericParam::Type(t) => {
                let ident = &t.ident;
                Some(quote! {
                    #ident : ::scroll::ctx::TryIntoCtx<::scroll::Endian>,
                    ::scroll::Error: ::std::convert::From<<#ident as ::scroll::ctx::TryIntoCtx<::scroll::Endian>>::Error>,
                    <#ident as ::scroll::ctx::TryIntoCtx<::scroll::Endian>>::Error: ::std::convert::From<scroll::Error>
                })
            },
            syn::GenericParam::Lifetime(_) => None,
            p => Some(quote! { #p }),
        });
        quote! { where Self: ::std::marker::Copy, #( #gi ),* }
    } else {
        quote! {}
    };

    quote! {
        impl<#fresh_lifetime, #gp > ::scroll::ctx::TryIntoCtx<::scroll::Endian> for &#fresh_lifetime #name #gn #gwref {
            type Error = ::scroll::Error;
            #[inline]
            fn try_into_ctx(self, dst: &mut [u8], #ctx: ::scroll::Endian) -> ::scroll::export::result::Result<usize, Self::Error> {
                use ::scroll::Pwrite;
                let #offset = &mut 0;
                #(#items;)*
                Ok(*#offset)
            }
        }

        impl #gl #gp #gg ::scroll::ctx::TryIntoCtx<::scroll::Endian> for #name #gn #gw {
            type Error = ::scroll::Error;
            #[inline]
            fn try_into_ctx(self, dst: &mut [u8], ctx: ::scroll::Endian) -> ::scroll::export::result::Result<usize, Self::Error> {
                (&self).try_into_ctx(dst, ctx)
            }
        }
    }
}

fn impl_try_into_ctx_primitive_enum(
    name: &Ident,
    repr_type: Ident,
    _variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
) -> proc_macro2::TokenStream {
    quote! {
        impl ::scroll::ctx::TryIntoCtx<::scroll::Endian> for &'_ #name {
            type Error = ::scroll::Error;
            #[inline]
            fn try_into_ctx(self, dst: &mut [u8], ctx: ::scroll::Endian) -> ::scroll::export::result::Result<usize, Self::Error> {
                use ::scroll::Pwrite;
                // SAFETY: https://doc.rust-lang.org/std/mem/fn.discriminant.html#accessing-the-numeric-value-of-the-discriminant
                // > If an enum has opted-in to having a primitive representation for its discriminant,
                // > then it’s possible to use pointers to read the memory location storing the discriminant.
                // NB: the derive macro ensures that we are a primitive (and also fieldless) enum
                dst.pwrite_with(unsafe { *<*const _>::from(self).cast::<#repr_type>() }, 0, ctx)
            }
        }

        impl ::scroll::ctx::TryIntoCtx<::scroll::Endian> for #name {
            type Error = ::scroll::Error;
            #[inline]
            fn try_into_ctx(self, dst: &mut [u8], ctx: ::scroll::Endian) -> ::scroll::export::result::Result<usize, Self::Error> {
                (&self).try_into_ctx(dst, ctx)
            }
        }
    }
}

fn impl_pwrite(ast: &syn::DeriveInput) -> proc_macro2::TokenStream {
    let name = &ast.ident;
    let generics = &ast.generics;
    match &ast.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => impl_try_into_ctx(name, &fields.named, generics),
            syn::Fields::Unnamed(fields) => impl_try_into_ctx(name, &fields.unnamed, generics),
            _ => {
                panic!("Pwrite can not be derived for unit structs")
            }
        },
        syn::Data::Enum(data) => {
            let repr_type = validate_enum(ast, data);
            impl_try_into_ctx_primitive_enum(&ast.ident, repr_type, &data.variants)
        }
        _ => panic!("Pwrite can only be derived for structs and primitive enums"),
    }
}

#[proc_macro_derive(Pwrite, attributes(scroll))]
pub fn derive_pwrite(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    let generated = impl_pwrite(&ast);
    generated.into()
}

fn size_with(
    name: &syn::Ident,
    fields: &syn::punctuated::Punctuated<syn::Field, syn::Token![,]>,
    generics: &syn::Generics,
) -> proc_macro2::TokenStream {
    let items: Vec<_> = fields
        .iter()
        .map(|f| {
            let ty = &f.ty;
            let mut noctx = false;
            let custom_ctx = custom_ctx(f, &mut noctx).map(|x| quote! {&#x});
            let default_ctx =
                syn::Ident::new("ctx", proc_macro2::Span::call_site()).into_token_stream();
            let ctx = custom_ctx.unwrap_or(default_ctx);
            match ty {
                syn::Type::Reference(_) => {
                    panic!("SizeWith cannot be derived for references")
                }
                syn::Type::Array(array) => {
                    let elem = &array.elem;
                    match &array.len {
                        syn::Expr::Lit(syn::ExprLit {
                            lit: syn::Lit::Int(int),
                            ..
                        }) => {
                            let size = int.base10_parse::<usize>().unwrap();
                            quote! {
                                (#size * <#elem>::size_with(#ctx))
                            }
                        }
                        _ => panic!("SizeWith derive has bad array constexpr"),
                    }
                }
                _ => {
                    quote! {
                        <#ty>::size_with(#ctx)
                    }
                }
            }
        })
        .collect();

    let gl = &generics.lt_token;
    let gp = &generics.params;
    let gg = &generics.gt_token;
    let gn = gp.iter().map(|param: &syn::GenericParam| match param {
        syn::GenericParam::Type(t) => {
            let ident = &t.ident;
            quote! { #ident }
        }
        p => quote! { #p },
    });
    let gn = quote! { #gl #( #gn ),* #gg };
    let gw = if !gp.is_empty() {
        let gi = gp
            .iter()
            .filter_map(|param: &syn::GenericParam| match param {
                syn::GenericParam::Type(t) => {
                    let ident = &t.ident;
                    Some(quote! {
                        #ident : ::scroll::ctx::SizeWith<::scroll::Endian>
                    })
                }
                syn::GenericParam::Lifetime(_) => None,
                p => Some(quote! { #p }),
            });
        quote! { where #( #gi ),* }
    } else {
        quote! {}
    };

    quote! {
        impl #gl #gp #gg ::scroll::ctx::SizeWith<::scroll::Endian> for #name #gn #gw {
            #[inline]
            fn size_with(ctx: &::scroll::Endian) -> usize {
                0 #(+ #items)*
            }
        }
    }
}

fn impl_size_with(ast: &syn::DeriveInput) -> proc_macro2::TokenStream {
    let name = &ast.ident;
    let generics = &ast.generics;
    match &ast.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => size_with(name, &fields.named, generics),
            syn::Fields::Unnamed(fields) => size_with(name, &fields.unnamed, generics),
            _ => {
                panic!("SizeWith can not be derived for unit structs")
            }
        },
        _ => panic!("SizeWith can only be derived for structs"),
    }
}

#[proc_macro_derive(SizeWith, attributes(scroll))]
pub fn derive_sizewith(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    let generated = impl_size_with(&ast);
    generated.into()
}

fn impl_cread_struct(
    name: &syn::Ident,
    fields: &syn::punctuated::Punctuated<syn::Field, syn::Token![,]>,
    generics: &syn::Generics,
) -> proc_macro2::TokenStream {
    let items: Vec<_> = fields.iter().enumerate().map(|(i, f)| {
        let ident = &f.ident.as_ref().map(|i|quote!{#i}).unwrap_or({let t = proc_macro2::Literal::usize_unsuffixed(i); quote!{#t}});
        let ty = &f.ty;
        let mut noctx = false;
        let custom_ctx = custom_ctx(f, &mut noctx);
        let default_ctx =
            syn::Ident::new("ctx", proc_macro2::Span::call_site()).into_token_stream();
        let ctx = custom_ctx.unwrap_or(default_ctx);
        match ty {
            syn::Type::Reference(_) => {
                panic!("IOread cannot be derived for references, because SizeWith cannot be derived for references")
            }
            syn::Type::Array(array) => {
                let arrty = &array.elem;
                match &array.len {
                    syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(int), ..}) => {
                        let size = int.base10_parse::<usize>().unwrap();
                        let incr = quote! { ::scroll::export::mem::size_of::<#arrty>() };
                        quote! {
                            #ident: {
                                let mut __tmp: #ty = [0u8.into(); #size];
                                for i in 0..__tmp.len() {
                                    __tmp[i] = src.cread_with(*offset, #ctx);
                                    *offset += #incr;
                                }
                                __tmp
                            }
                        }
                    },
                    _ => panic!("IOread derive with bad array constexpr")
                }
            },
            _ => {
                let size = quote! { ::scroll::export::mem::size_of::<#ty>() };
                quote! {
                    #ident: { let res = src.cread_with::<#ty>(*offset, #ctx); *offset += #size; res }
                }
            }
        }
    }).collect();

    let gl = &generics.lt_token;
    let gp = &generics.params;
    let gg = &generics.gt_token;
    let gn = gp.iter().map(|param: &syn::GenericParam| match param {
        syn::GenericParam::Type(t) => {
            let ident = &t.ident;
            quote! { #ident }
        }
        p => quote! { #p },
    });
    let gn = quote! { #gl #( #gn ),* #gg };
    let gw = if !gp.is_empty() {
        let gi = gp.iter().map(|param: &syn::GenericParam| match param {
            syn::GenericParam::Type(t) => {
                let ident = &t.ident;
                quote! {
                    #ident : ::scroll::ctx::FromCtx<::scroll::Endian> + ::std::convert::From<u8> + ::std::marker::Copy
                }
            },
            p => quote! { #p }
        });
        quote! { where #( #gi ),* , }
    } else {
        quote! {}
    };

    quote! {
        impl #gl #gp #gg ::scroll::ctx::FromCtx<::scroll::Endian> for #name #gn #gw {
            #[inline]
            fn from_ctx(src: &[u8], ctx: ::scroll::Endian) -> Self {
                use ::scroll::Cread;
                let offset = &mut 0;
                let data = Self { #(#items,)* };
                data
            }
        }
    }
}

fn impl_from_ctx(ast: &syn::DeriveInput) -> proc_macro2::TokenStream {
    let name = &ast.ident;
    let generics = &ast.generics;
    match &ast.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => impl_cread_struct(name, &fields.named, generics),
            syn::Fields::Unnamed(fields) => impl_cread_struct(name, &fields.unnamed, generics),
            _ => {
                panic!("IOread can not be derived for unit structs")
            }
        },
        _ => panic!("IOread can only be derived for structs"),
    }
}

#[proc_macro_derive(IOread, attributes(scroll))]
pub fn derive_ioread(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    let generated = impl_from_ctx(&ast);
    generated.into()
}

fn impl_into_ctx(
    name: &syn::Ident,
    fields: &syn::punctuated::Punctuated<syn::Field, syn::Token![,]>,
    generics: &syn::Generics,
) -> proc_macro2::TokenStream {
    let items: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, f)| {
            let ident = &f.ident.as_ref().map(|i| quote! {#i}).unwrap_or({
                let t = proc_macro2::Literal::usize_unsuffixed(i);
                quote! {#t}
            });
            let ty = &f.ty;
            let mut noctx = false;
            let size = quote! { ::scroll::export::mem::size_of::<#ty>() };
            let custom_ctx = custom_ctx(f, &mut noctx);
            let default_ctx =
                syn::Ident::new("ctx", proc_macro2::Span::call_site()).into_token_stream();
            let ctx = custom_ctx.unwrap_or(default_ctx);
            match ty {
                syn::Type::Reference(_) => {
                    panic!("IOwrite cannot be derived for references, because SizeWith cannot be derived for references")
                }
                syn::Type::Array(array) => {
                    let arrty = &array.elem;
                    quote! {
                        let size = ::scroll::export::mem::size_of::<#arrty>();
                        for i in 0..self.#ident.len() {
                            dst.cwrite_with(self.#ident[i], *offset, #ctx);
                            *offset += size;
                        }
                    }
                }
                _ => {
                    quote! {
                        dst.cwrite_with(self.#ident, *offset, #ctx);
                        *offset += #size;
                    }
                }
            }
        })
        .collect();

    let gl = &generics.lt_token;
    let gp = &generics.params;
    let gg = &generics.gt_token;
    let gn = gp.iter().map(|param: &syn::GenericParam| match param {
        syn::GenericParam::Type(t) => {
            let ident = &t.ident;
            quote! { #ident }
        }
        p => quote! { #p },
    });
    let gw = if !gp.is_empty() {
        let gi = gp.iter().map(|param: &syn::GenericParam| match param {
            syn::GenericParam::Type(t) => {
                let ident = &t.ident;
                quote! {
                    #ident : ::scroll::ctx::IntoCtx<::scroll::Endian> + ::std::marker::Copy
                }
            }
            p => quote! { #p },
        });
        quote! { where #( #gi ),* }
    } else {
        quote! {}
    };
    let gn = quote! { #gl #( #gn ),* #gg };

    quote! {
        impl<'a, #gp > ::scroll::ctx::IntoCtx<::scroll::Endian> for &'a #name #gn #gw {
            #[inline]
            fn into_ctx(self, dst: &mut [u8], ctx: ::scroll::Endian) {
                use ::scroll::Cwrite;
                let offset = &mut 0;
                #(#items;)*;
            }
        }

        impl #gl #gp #gg ::scroll::ctx::IntoCtx<::scroll::Endian> for #name #gn #gw {
            #[inline]
            fn into_ctx(self, dst: &mut [u8], ctx: ::scroll::Endian) {
                (&self).into_ctx(dst, ctx)
            }
        }
    }
}

fn impl_iowrite(ast: &syn::DeriveInput) -> proc_macro2::TokenStream {
    let name = &ast.ident;
    let generics = &ast.generics;
    match &ast.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => impl_into_ctx(name, &fields.named, generics),
            syn::Fields::Unnamed(fields) => impl_into_ctx(name, &fields.unnamed, generics),
            _ => {
                panic!("IOwrite can not be derived for unit structs")
            }
        },
        _ => panic!("IOwrite can only be derived for structs"),
    }
}

#[proc_macro_derive(IOwrite, attributes(scroll))]
pub fn derive_iowrite(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    let generated = impl_iowrite(&ast);
    generated.into()
}
