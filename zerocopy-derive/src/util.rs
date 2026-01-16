// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use proc_macro2::Span;
use quote::ToTokens as _;
use syn::{parse_quote, DeriveInput, Error, Expr, ExprLit, Lit, Meta, Path};

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
