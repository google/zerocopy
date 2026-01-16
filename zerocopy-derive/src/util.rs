// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
    parse_quote, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Error, Expr, ExprLit, Field,
    Ident, ImplGenerics, Index, Lit, Meta, Path, Type, TypeGenerics, Variant, Visibility,
    WhereClause,
};

pub(crate) struct Ctx {
    pub(crate) ast: DeriveInput,
    pub(crate) zerocopy_crate: Path,
}

impl Ctx {
    /// Attempt to extract a crate path from the provided attributes. Defaults to
    /// `::zerocopy` if not found.
    pub(crate) fn try_from_derive_input(ast: DeriveInput) -> Result<Self, Error> {
        let mut path = parse_quote!(::zerocopy);

        for attr in &ast.attrs {
            if let Meta::List(ref meta_list) = attr.meta {
                if meta_list.path.is_ident("zerocopy") {
                    attr.parse_nested_meta(|meta| {
                        if meta.path.is_ident("crate") {
                            let expr = meta.value().and_then(|value| value.parse());
                            if let Ok(Expr::Lit(ExprLit { lit: Lit::Str(lit), .. })) = expr {
                                if let Ok(path_lit) = lit.parse() {
                                    path = path_lit;
                                    return Ok(());
                                }
                            }

                            return Err(Error::new(
                                Span::call_site(),
                                "`crate` attribute requires a path as the value",
                            ));
                        }

                        Err(Error::new(
                            Span::call_site(),
                            format!(
                                "unknown attribute encountered: {}",
                                meta.path.into_token_stream()
                            ),
                        ))
                    })?;
                }
            }
        }

        Ok(Self { ast, zerocopy_crate: path })
    }

    pub(crate) fn with_input(&self, input: &DeriveInput) -> Self {
        Self { ast: input.clone(), zerocopy_crate: self.zerocopy_crate.clone() }
    }
}

pub(crate) struct ImplBlockBuilder<'a> {
    impl_generics: ImplGenerics<'a>,

    trait_name: Path,
    trait_generics: Option<TypeGenerics<'a>>,

    self_name: Ident,
    self_generics: TypeGenerics<'a>,

    where_clause: Option<&'a WhereClause>,

    ctx: &'a Ctx,
}

impl<'a> ImplBlockBuilder<'a> {
    pub(crate) fn from_derive_input(
        ctx: &'a Ctx,
        input: &'a DeriveInput,
        trait_name: Path,
    ) -> ImplBlockBuilder<'a> {
        let (impl_generics, self_generics, where_clause) = input.generics.split_for_impl();

        ImplBlockBuilder {
            impl_generics,
            trait_name,
            trait_generics: None,
            self_name: input.ident.clone(),
            self_generics,
            where_clause,
            ctx,
        }
    }

    pub(crate) fn build(self) -> TokenStream {
        let ImplBlockBuilder {
            impl_generics,
            trait_name,
            trait_generics,
            self_name,
            self_generics,
            where_clause,
            ctx,
        } = self;

        let zerocopy_crate = &ctx.zerocopy_crate;

        quote! {
            unsafe impl #impl_generics #trait_name #trait_generics for #self_name #self_generics #where_clause {
                fn only_derive_is_allowed_to_implement_this_trait() where Self: #zerocopy_crate::util::macro_util::core_reexport::marker::Sized {}
            }
        }
    }
}

pub(crate) trait DataExt {
    /// Extracts the names and types of all fields. For enums, extracts the
    /// names and types of fields from each variant. For tuple structs, the
    /// names are the indices used to index into the struct (ie, `0`, `1`, etc).
    ///
    /// FIXME: Extracting field names for enums doesn't really make sense. Types
    /// makes sense because we don't care about where they live - we just care
    /// about transitive ownership. But for field names, we'd only use them when
    /// generating is_bit_valid, which cares about where they live.
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)>;

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)>;

    fn tag(&self) -> Option<Ident>;
}

impl DataExt for Data {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        match self {
            Data::Struct(strc) => strc.fields(),
            Data::Enum(enm) => enm.fields(),
            Data::Union(un) => un.fields(),
        }
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        match self {
            Data::Struct(strc) => strc.variants(),
            Data::Enum(enm) => enm.variants(),
            Data::Union(un) => un.variants(),
        }
    }

    fn tag(&self) -> Option<Ident> {
        match self {
            Data::Struct(strc) => strc.tag(),
            Data::Enum(enm) => enm.tag(),
            Data::Union(un) => un.tag(),
        }
    }
}

impl DataExt for DataStruct {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        map_fields(&self.fields)
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        vec![(None, self.fields())]
    }

    fn tag(&self) -> Option<Ident> {
        None
    }
}

impl DataExt for DataEnum {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        map_fields(self.variants.iter().flat_map(|var| &var.fields))
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        self.variants.iter().map(|var| (Some(var), map_fields(&var.fields))).collect()
    }

    fn tag(&self) -> Option<Ident> {
        Some(Ident::new("___ZerocopyTag", Span::call_site()))
    }
}

impl DataExt for DataUnion {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        map_fields(&self.fields.named)
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        vec![(None, self.fields())]
    }

    fn tag(&self) -> Option<Ident> {
        None
    }
}

fn map_fields<'a>(
    fields: impl 'a + IntoIterator<Item = &'a Field>,
) -> Vec<(&'a Visibility, TokenStream, &'a Type)> {
    fields
        .into_iter()
        .enumerate()
        .map(|(idx, f)| {
            (
                &f.vis,
                f.ident
                    .as_ref()
                    .map(ToTokens::to_token_stream)
                    .unwrap_or_else(|| Index::from(idx).to_token_stream()),
                &f.ty,
            )
        })
        .collect()
}

pub(crate) fn to_ident_str(t: &impl ToString) -> String {
    let s = t.to_string();
    if let Some(stripped) = s.strip_prefix("r#") {
        stripped.to_string()
    } else {
        s
    }
}
