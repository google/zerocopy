// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Inert, syntax-checking Anneal specification attributes.
//!
//! These macros never change the code they annotate: specifications have no
//! runtime meaning. They exist so that a crate which opts in can write
//! `#[anneal::spec(...)]` directly and get clause syntax errors from `rustc`.
//! Crates such as `zerocopy` that must not take a dependency instead write
//! `#[cfg_attr(anneal, anneal::spec(...))]`, which `rustc` strips unexpanded
//! when `cfg(anneal)` is unset, or keep specifications in companion files
//! read only by `anneal-spec-lower`.
//!
//! Type checking needs the whole specification unit (helpers, other items),
//! so it happens in `anneal-spec-lower`, not here.

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;

fn error(d: anneal_spec_lower::Diagnostic) -> TokenStream {
    let msg = format!("{d}");
    let span = d.span;
    quote::quote_spanned!(span=> ::core::compile_error!(#msg);).into()
}

/// `#[anneal::spec(requires(..), ensures(|ret| ..), total, ..)]`
#[proc_macro_attribute]
pub fn spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = proc_macro2::TokenStream::from(attr);
    let item2 = proc_macro2::TokenStream::from(item.clone());
    if let Err(d) = anneal_spec_lower::parse::check_clause_syntax(attr, Span::call_site()) {
        let err = proc_macro2::TokenStream::from(error(d));
        return quote!(#err #item2).into();
    }
    item
}

/// `#[anneal::pure]`: marks a total, side-effect-free specification helper.
#[proc_macro_attribute]
pub fn pure(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        let d = anneal_spec_lower::Diagnostic::new(
            "E_ANNEAL_SPEC_SYNTAX",
            Span::call_site(),
            "`anneal::pure` takes no arguments",
        );
        let err = proc_macro2::TokenStream::from(error(d));
        let item2 = proc_macro2::TokenStream::from(item);
        return quote!(#err #item2).into();
    }
    item
}

/// `#[anneal::vacuous_ok(reason = "...")]`: waives the non-vacuity check.
#[proc_macro_attribute]
pub fn vacuous_ok(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = proc_macro2::TokenStream::from(attr);
    let ok = syn::parse2::<syn::MetaNameValue>(attr).ok().is_some_and(|nv| {
        nv.path.is_ident("reason")
            && matches!(&nv.value, syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. })
                if !s.value().trim().is_empty())
    });
    if !ok {
        let d = anneal_spec_lower::Diagnostic::new(
            "E_ANNEAL_VACUOUS_OK_REASON",
            Span::call_site(),
            "`vacuous_ok` requires a non-empty `reason = \"...\"`",
        );
        let err = proc_macro2::TokenStream::from(error(d));
        let item2 = proc_macro2::TokenStream::from(item);
        return quote!(#err #item2).into();
    }
    item
}

/// `anneal::external_spec! { impl Trait for Ty { #[spec(..)] fn f(..); } }`
///
/// Expands to nothing after checking syntax.
#[proc_macro]
pub fn external_spec(input: TokenStream) -> TokenStream {
    match anneal_spec_lower::parse::check_external_syntax(input.into()) {
        Ok(()) => TokenStream::new(),
        Err(d) => error(d),
    }
}
