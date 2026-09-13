// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use proc_macro2::Span;
use syn::{
    punctuated::Punctuated, spanned::Spanned as _, Attribute, Data, DeriveInput, Error, Expr,
    Field, Meta, Token,
};

use crate::util::path_is_ident;

/// Parses field invariants in attribute order.
pub(crate) fn parse(attrs: &[Attribute]) -> Result<Vec<Expr>, Error> {
    let mut invariants = Vec::new();
    for attr in attrs.iter().filter(|attr| path_is_ident(attr.path(), "zerocopy")) {
        let options = attr.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)?;
        for option in options {
            if !path_is_ident(option.path(), "invariant") {
                return Err(Error::new_spanned(option, "expected `invariant(...)`"));
            }
            match option {
                Meta::List(list) => invariants.push(list.parse_args::<Expr>()?),
                other => return Err(Error::new_spanned(other, "expected `invariant(...)`")),
            }
        }
    }
    Ok(invariants)
}

/// Validates invariant syntax and placement, returning the first invariant's
/// span so derives which cannot honor invariants can reject them.
pub(crate) fn validate(ast: &DeriveInput) -> Result<Option<Span>, Error> {
    let fields: Vec<&Field> = match &ast.data {
        Data::Struct(data) => data.fields.iter().collect(),
        Data::Enum(data) => {
            for variant in &data.variants {
                if let Some(invariant) = parse(&variant.attrs)?.first() {
                    return Err(Error::new(
                        invariant.span(),
                        "invariants are only supported on named fields",
                    ));
                }
            }
            data.variants.iter().flat_map(|variant| &variant.fields).collect()
        }
        Data::Union(data) => data.fields.named.iter().collect(),
    };
    let mut first = None;
    for field in fields {
        if let Some(invariant) = parse(&field.attrs)?.first() {
            if field.ident.is_none() {
                return Err(Error::new(
                    invariant.span(),
                    "invariants are only supported on named fields",
                ));
            }
            first.get_or_insert(invariant.span());
        }
    }
    Ok(first)
}
