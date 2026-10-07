// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Internal generators for Kani contract proofs; see the crate's README.

use std::collections::BTreeMap;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as Tokens;
use quote::{format_ident, quote};
use syn::{
    fold::Fold,
    parenthesized,
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::Punctuated,
    Attribute, Expr, FnArg, GenericParam, Ident, ItemFn, ItemImpl, Meta, Path, Signature, Token,
    Type,
};

#[derive(Default)]
struct Options {
    target: Option<Path>,
    method: bool,
    requires: Vec<Expr>,
    ensures: Vec<Expr>,
    verified_stubs: Vec<Path>,
    instances: Vec<Instance>,
    solver: Option<Ident>,
    unwind: Option<syn::LitInt>,
}

#[derive(Clone)]
struct Instance {
    name: Ident,
    types: BTreeMap<String, Type>,
}

impl Parse for Instance {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name = input.parse()?;
        let inner;
        parenthesized!(inner in input);
        let mut types = BTreeMap::new();
        while !inner.is_empty() {
            let ident: Ident = inner.parse()?;
            inner.parse::<Token![=]>()?;
            let ty = inner.parse()?;
            if types.insert(ident.to_string(), ty).is_some() {
                return Err(syn::Error::new_spanned(ident, "duplicate type binding"));
            }
            if !inner.is_empty() {
                inner.parse::<Token![,]>()?;
            }
        }
        Ok(Self { name, types })
    }
}

impl Parse for Options {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut opts = Self::default();
        while !input.is_empty() {
            let key: Ident = input.parse()?;
            match key.to_string().as_str() {
                "method" => opts.method = true,
                "requires" | "ensures" => {
                    let inner;
                    parenthesized!(inner in input);
                    let expr: Expr = inner.parse()?;
                    if key == "requires" {
                        opts.requires.push(expr);
                    } else {
                        opts.ensures.push(expr);
                    }
                }
                "stub_verified" => {
                    let inner;
                    parenthesized!(inner in input);
                    let path: Path = inner.parse()?;
                    if !inner.is_empty() {
                        return Err(inner.error("expected one verified dependency path"));
                    }
                    opts.verified_stubs.push(path);
                }
                "instances" => {
                    let inner;
                    parenthesized!(inner in input);
                    if !opts.instances.is_empty() {
                        return Err(syn::Error::new_spanned(key, "duplicate instances"));
                    }
                    opts.instances = Punctuated::<Instance, Token![,]>::parse_terminated(&inner)?
                        .into_iter()
                        .collect();
                }
                "target" => {
                    input.parse::<Token![=]>()?;
                    if opts.target.replace(input.parse()?).is_some() {
                        return Err(syn::Error::new_spanned(key, "duplicate target"));
                    }
                }
                "solver" => {
                    input.parse::<Token![=]>()?;
                    opts.solver = Some(input.parse()?);
                }
                "unwind" => {
                    input.parse::<Token![=]>()?;
                    opts.unwind = Some(input.parse()?);
                }
                _ => return Err(syn::Error::new_spanned(key, "unsupported contract option")),
            }
            if !input.is_empty() {
                input.parse::<Token![,]>()?;
            }
        }
        Ok(opts)
    }
}

struct Substitute {
    types: BTreeMap<String, Type>,
    self_ty: Option<Type>,
}
impl Fold for Substitute {
    fn fold_type(&mut self, ty: Type) -> Type {
        if let Type::Path(ref p) = ty {
            if p.qself.is_none() && p.path.segments.len() == 1 {
                let id = p.path.segments[0].ident.to_string();
                if id == "Self" {
                    if let Some(ref t) = self.self_ty {
                        return t.clone();
                    }
                }
                if let Some(t) = self.types.get(&id) {
                    return t.clone();
                }
            }
        }
        syn::fold::fold_type(self, ty)
    }
}

fn type_params(generics: &syn::Generics) -> syn::Result<Vec<Ident>> {
    generics
        .params
        .iter()
        .map(|p| match p {
            GenericParam::Type(t) => Ok(t.ident.clone()),
            _ => Err(syn::Error::new_spanned(p, "lifetime and const parameters are not supported")),
        })
        .collect()
}

fn instances(opts: &Options, params: &[Ident]) -> syn::Result<Vec<Instance>> {
    if params.is_empty() && opts.instances.is_empty() {
        return Ok(vec![Instance { name: format_ident!("all"), types: BTreeMap::new() }]);
    }
    if opts.instances.is_empty() {
        return Err(syn::Error::new_spanned(
            &params[0],
            "generic contracts require explicit instances",
        ));
    }
    let expected: Vec<String> = params.iter().map(ToString::to_string).collect();
    let mut names = std::collections::BTreeSet::new();
    for instance in &opts.instances {
        if !names.insert(instance.name.to_string()) {
            return Err(syn::Error::new_spanned(&instance.name, "duplicate instance name"));
        }
        if instance.types.len() != expected.len()
            || expected.iter().any(|p| !instance.types.contains_key(p))
        {
            return Err(syn::Error::new_spanned(
                &instance.name,
                "each instance must bind exactly the declared type parameters",
            ));
        }
    }
    Ok(opts.instances.clone())
}

fn reject_attributes(attrs: &[Attribute]) -> syn::Result<()> {
    for attr in attrs {
        // Also reject spellings nested inside cfg_attr. The compiled inventory
        // checker is authoritative when another macro introduces an attribute.
        let text = quote!(#attr).to_string().replace(' ', "");
        if ["stub", "stub_verified", "should_panic", "recursion", "requires", "ensures", "modifies"]
            .iter()
            .any(|name| text.contains(&format!("kani::{}", name)))
        {
            return Err(syn::Error::new_spanned(
                attr,
                "use only generated contract attributes; substitutions and recursion are forbidden",
            ));
        }
    }
    Ok(())
}

fn attach(attrs: &mut Vec<Attribute>, opts: &Options) -> syn::Result<()> {
    reject_attributes(attrs)?;
    if opts.ensures.is_empty() {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "a contract needs at least one ensures clause",
        ));
    }
    for expr in &opts.requires {
        attrs.push(parse_quote!(#[kani::requires(#expr)]));
    }
    for expr in &opts.ensures {
        attrs.push(parse_quote!(#[kani::ensures(#expr)]));
    }
    Ok(())
}

fn harness(
    sig: &Signature,
    target: &Path,
    name: Ident,
    mut subst: Substitute,
    opts: &Options,
    attrs: &[Attribute],
) -> syn::Result<Tokens> {
    if sig.asyncness.is_some() || sig.variadic.is_some() || sig.abi.is_some() {
        return Err(syn::Error::new_spanned(
            sig,
            "async, variadic and foreign functions are unsupported",
        ));
    }
    let mut lets = Vec::new();
    let mut args = Vec::new();
    for (i, arg) in sig.inputs.iter().enumerate() {
        let var = format_ident!("__arg_{}", i);
        let ty = match arg {
            FnArg::Receiver(r) => {
                if r.colon_token.is_some() || r.mutability.is_some() {
                    return Err(syn::Error::new_spanned(
                        r,
                        "only self and &self receivers are supported",
                    ));
                }
                subst.fold_type(parse_quote!(Self))
            }
            FnArg::Typed(a) => subst.fold_type((*a.ty).clone()),
        };
        let borrowed = matches!(arg, FnArg::Receiver(r) if r.reference.is_some());
        let (owned, borrow) = match ty {
            Type::Reference(r) if r.mutability.is_none() => (*r.elem, true),
            Type::Reference(_) | Type::Ptr(_) | Type::Slice(_) | Type::TraitObject(_) => {
                return Err(syn::Error::new_spanned(
                    arg,
                    "mutable references, pointers and unsized arguments are unsupported",
                ))
            }
            t => (t, borrowed),
        };
        if matches!(owned, Type::Slice(_) | Type::TraitObject(_) | Type::ImplTrait(_)) {
            return Err(syn::Error::new_spanned(
                arg,
                "unbounded or opaque input domains are unsupported",
            ));
        }
        lets.push(quote!(let #var: #owned = ::kani::any::<#owned>();));
        args.push(if borrow { quote!(&#var) } else { quote!(#var) });
    }
    let params = type_params(&sig.generics)?;
    let types: Vec<Type> = params.iter().map(|p| subst.types[&p.to_string()].clone()).collect();
    let mut target = target.clone();
    if !types.is_empty() {
        target.segments.last_mut().unwrap().arguments =
            syn::PathArguments::AngleBracketed(parse_quote!(::<#(#types),*>));
    }
    let dependencies: Vec<Path> = opts
        .verified_stubs
        .iter()
        .map(|path| {
            let mut path = subst.fold_path(path.clone());
            if path.segments.first().is_some_and(|s| s.ident == "Self") {
                if let Some(Type::Path(owner)) = &subst.self_ty {
                    let mut concrete = owner.path.clone();
                    for segment in path.segments.iter().skip(1) {
                        concrete.segments.push(segment.clone());
                    }
                    path = concrete;
                }
            }
            for segment in &mut path.segments {
                if let syn::PathArguments::AngleBracketed(ref mut args) = segment.arguments {
                    args.colon2_token = Some(Token![::](proc_macro2::Span::call_site()));
                }
            }
            path
        })
        .collect();
    let call = quote!(#target(#(#args),*));
    let call = if sig.unsafety.is_some() { quote!(unsafe { #call }) } else { call };
    let solver = opts.solver.as_ref().map(|s| quote!(#[kani::solver(#s)]));
    let unwind = opts.unwind.as_ref().map(|n| quote!(#[kani::unwind(#n)]));
    let cfg = attrs.iter().filter(|a| a.path().is_ident("cfg"));
    Ok(quote! {
        #(#cfg)*
        #[cfg(kani)]
        #[allow(non_snake_case)]
        #[kani::proof_for_contract(#target)]
        #(#[kani::stub_verified(#dependencies)])*
        #solver
        #unwind
        fn #name() { #(#lets)* let _ = #call; }
    })
}

fn expand_fn(opts: Options, mut f: ItemFn) -> syn::Result<Tokens> {
    let target = match opts.target.clone() {
        Some(target) => target,
        None if opts.method => {
            return Err(syn::Error::new_spanned(
                &f.sig.ident,
                "individual methods require target = ConcreteOwner::method; use contracts on the impl to infer it",
            ));
        }
        None => {
            let name = &f.sig.ident;
            parse_quote!(#name)
        }
    };
    if !opts.method && (target.leading_colon.is_some() || target.segments.len() != 1) {
        return Err(syn::Error::new_spanned(
            &target,
            "free-function targets are inferred; qualified targets could prove another function",
        ));
    }
    if target.segments.last().map(|s| &s.ident) != Some(&f.sig.ident) {
        return Err(syn::Error::new_spanned(&target, "target must name the annotated function"));
    }
    let has_receiver = f.sig.inputs.iter().any(|a| matches!(a, FnArg::Receiver(_)));
    if has_receiver && !opts.method {
        return Err(syn::Error::new_spanned(&f.sig, "methods require the method option"));
    }
    let params = type_params(&f.sig.generics)?;
    let cases = instances(&opts, &params)?;
    let mut proofs = Vec::new();
    for case in cases {
        let name = format_ident!("__kani_contract_{}_{}", f.sig.ident, case.name);
        proofs.push(harness(
            &f.sig,
            &target,
            name,
            Substitute { types: case.types, self_ty: None },
            &opts,
            &f.attrs,
        )?);
    }
    let proof_items = if opts.method {
        let mut owner = target.clone();
        owner.segments.pop();
        owner.segments.pop_punct();
        if owner.segments.is_empty() {
            return Err(syn::Error::new_spanned(
                &target,
                "method target needs its concrete owner type",
            ));
        }
        // This Rust type check prevents a method macro in a generic impl from
        // silently generating an undiscovered generic proof. Self must equal
        // the concrete owner named by the target, even for static methods.
        let witness = format_ident!("__kani_contract_owner_{}", f.sig.ident);
        quote! {
            #[cfg(kani)]
            #[allow(non_upper_case_globals)]
            const #witness: fn() -> ::core::cell::Cell<Self> = {
                // A nested item cannot capture an impl's generic parameters or
                // Self. Cell is invariant, also preventing lifetime coercions.
                fn concrete_owner() -> ::core::cell::Cell<#owner> {
                    ::core::cell::Cell::new(::kani::any::<#owner>())
                }
                concrete_owner
            };
            #(#proofs)*
        }
    } else {
        // Keep proofs in the function's lexical scope: importing super from a
        // generated module would resolve a block-local function's name in the
        // enclosing module instead. An empty module still rejects accidentally
        // using the free-function macro on static methods inside an impl.
        let scope = format_ident!("__kani_contract_scope_{}", f.sig.ident);
        quote! { #[cfg(kani)] mod #scope {} #(#proofs)* }
    };
    attach(&mut f.attrs, &opts)?;
    Ok(quote!(#f #proof_items))
}

fn take_contract(attrs: &mut Vec<Attribute>) -> syn::Result<Option<Options>> {
    let mut found = None;
    let mut retained = Vec::new();
    for attr in attrs.drain(..) {
        let mut meta = attr.meta.clone();
        if attr.path().is_ident("cfg_attr") {
            let items = attr.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)?;
            if items.len() == 2 && items[0].path().is_ident("kani") {
                meta = items[1].clone();
            }
        }
        if meta.path().is_ident("contract") {
            if found.is_some() {
                return Err(syn::Error::new_spanned(attr, "duplicate contract"));
            }
            match meta {
                Meta::List(m) => found = Some(syn::parse2(m.tokens)?),
                _ => return Err(syn::Error::new_spanned(attr, "expected contract clauses")),
            }
        } else {
            retained.push(attr);
        }
    }
    *attrs = retained;
    Ok(found)
}

fn expand_impl(opts: Options, mut item: ItemImpl) -> syn::Result<Tokens> {
    if item.trait_.is_some() {
        return Err(syn::Error::new_spanned(item, "trait impls are unsupported"));
    }
    if opts.target.is_some()
        || opts.method
        || !opts.requires.is_empty()
        || !opts.ensures.is_empty()
        || !opts.verified_stubs.is_empty()
        || opts.solver.is_some()
        || opts.unwind.is_some()
    {
        return Err(syn::Error::new_spanned(item, "impl options may contain only instances"));
    }
    let params = type_params(&item.generics)?;
    let cases = instances(&opts, &params)?;
    let mut proofs = Vec::new();
    for member in &mut item.items {
        if let syn::ImplItem::Fn(f) = member {
            if let Some(contract) = take_contract(&mut f.attrs)? {
                if contract.target.is_some() {
                    return Err(syn::Error::new_spanned(
                        &f.sig.ident,
                        "impl contracts infer their target",
                    ));
                }
                let own_params = type_params(&f.sig.generics)?;
                let own_cases = instances(&contract, &own_params)?;
                for case in &cases {
                    for own in &own_cases {
                        let mut types = case.types.clone();
                        types.extend(own.types.clone());
                        let self_ty = Substitute { types: types.clone(), self_ty: None }
                            .fold_type((*item.self_ty).clone());
                        let method = &f.sig.ident;
                        // Kani resolves Type::method paths, rather than UFCS paths.
                        let mut target: Path = match &self_ty {
                            Type::Path(t) if t.qself.is_none() => t.path.clone(),
                            _ => {
                                return Err(syn::Error::new_spanned(
                                    &self_ty,
                                    "impl self type must be a path",
                                ))
                            }
                        };
                        for segment in &mut target.segments {
                            if let syn::PathArguments::AngleBracketed(ref mut args) =
                                segment.arguments
                            {
                                args.colon2_token =
                                    Some(Token![::](proc_macro2::Span::call_site()));
                            }
                        }
                        target.segments.push(parse_quote!(#method));
                        let type_name = target.segments.first().unwrap().ident.clone();
                        let name = format_ident!(
                            "__kani_contract_{}_{}_{}_{}",
                            type_name,
                            method,
                            case.name,
                            own.name
                        );
                        let proof = harness(
                            &f.sig,
                            &target,
                            name,
                            Substitute { types, self_ty: Some(self_ty) },
                            &contract,
                            &f.attrs,
                        )?;
                        let cfg = item.attrs.iter().filter(|a| a.path().is_ident("cfg"));
                        proofs.push(quote!(#(#cfg)* #proof));
                    }
                }
                attach(&mut f.attrs, &contract)?;
            }
        }
    }
    Ok(quote!(#item #(#proofs)*))
}

/// Generate a sibling proof for a free function or an associated proof function
/// for a method in a concrete inherent impl. Free-function targets are inferred;
/// individual method targets name their concrete owner.
pub(crate) fn contract(args: TokenStream, item: TokenStream) -> TokenStream {
    let result =
        syn::parse(args).and_then(|opts| syn::parse(item).and_then(|f| expand_fn(opts, f)));
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}

/// Generate non-generic sibling proofs for contracted methods in an inherent
/// impl. Generic impls require explicit `instances(label(T = ConcreteType))`.
pub(crate) fn contracts(args: TokenStream, item: TokenStream) -> TokenStream {
    let result =
        syn::parse(args).and_then(|opts| syn::parse(item).and_then(|i| expand_impl(opts, i)));
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn function(options: Tokens, item: Tokens) -> syn::Result<Tokens> {
        expand_fn(syn::parse2(options)?, syn::parse2(item)?)
    }
    fn implementation(options: Tokens, item: Tokens) -> syn::Result<Tokens> {
        expand_impl(syn::parse2(options)?, syn::parse2(item)?)
    }

    #[test]
    fn arguments_are_unmodified_and_independent() {
        let expanded = function(
            quote!(target = add, requires(x < 10), ensures(|r| *r == x + y)),
            quote!(
                fn add(x: u8, y: u16) -> u16 {
                    x as u16 + y
                }
            ),
        )
        .unwrap();
        let file: syn::File = syn::parse2(expanded).unwrap();
        assert_eq!(file.items.len(), 3);
        let module = match &file.items[1] {
            syn::Item::Mod(m) => m,
            _ => panic!(),
        };
        assert!(module.content.as_ref().unwrap().1.is_empty());
        let proof = match &file.items[2] {
            syn::Item::Fn(f) => f,
            _ => panic!(),
        };
        assert!(proof.sig.inputs.is_empty());
        let body = quote!(#proof).to_string();
        assert_eq!(body.matches(":: kani :: any").count(), 2);
        assert!(!body.contains("assume"));
        assert!(body.contains("add (__arg_0 , __arg_1)"));
    }

    #[test]
    fn concrete_methods_generate_associated_proofs() {
        let out = function(
            quote!(method, target = Example::f, ensures(|r| *r)),
            quote!(
                fn f(&self) -> bool {
                    true
                }
            ),
        )
        .unwrap();
        let block: ItemImpl = syn::parse2(quote!(impl Example { #out })).unwrap();
        assert_eq!(block.items.len(), 3);
    }

    #[test]
    fn generic_impl_proofs_are_outside_and_fully_instantiated() {
        let out = implementation(
            quote!(instances(byte(E = u8), word(E = u16))),
            quote! {
                impl<E> Example<E> {
                    #[cfg_attr(kani, contract(ensures(|r| *r == core::mem::size_of::<E>())))]
                    fn f(&self) -> usize { core::mem::size_of::<E>() }
                }
            },
        )
        .unwrap();
        let file: syn::File = syn::parse2(out).unwrap();
        assert_eq!(file.items.len(), 3);
        for item in &file.items[1..] {
            let f = match item {
                syn::Item::Fn(f) => f,
                _ => panic!(),
            };
            assert!(f.sig.generics.params.is_empty());
            let body = quote!(#f).to_string();
            assert!(!body.contains("Self"));
            assert!(!body.contains("< E >"));
        }
    }

    #[test]
    fn generic_function_instances_are_explicit() {
        let out = function(
            quote!(instances(unit(T = ()), byte(T = u8)), ensures(|r| *r > 0)),
            quote!(
                fn f<T>() -> usize {
                    1
                }
            ),
        )
        .unwrap();
        let file: syn::File = syn::parse2(out).unwrap();
        assert_eq!(file.items.len(), 4);
        let proofs = &file.items[2..];
        for (item, argument) in proofs.iter().zip(["()", "u8"]) {
            let proof = match item {
                syn::Item::Fn(f) => f,
                _ => panic!(),
            };
            assert!(proof.sig.generics.params.is_empty());
            let body = quote!(#proof).to_string();
            assert!(body.contains(&format!("f :: < {} >", argument)));
        }
        assert!(function(
            quote!(target = f, ensures(|r| *r > 0)),
            quote!(
                fn f<T>() -> usize {
                    1
                }
            )
        )
        .is_err());
    }

    #[test]
    fn incomplete_extra_and_duplicate_instances_are_rejected() {
        for opts in [
            quote!(instances(a(T = u8))),
            quote!(instances(a(T = u8, U = u8, V = u8))),
            quote!(instances(a(T = u8, U = u8), a(T = u16, U = u16))),
        ] {
            assert!(implementation(
                opts,
                quote!(
                    impl<T, U> Example<T, U> {}
                )
            )
            .is_err());
        }
    }

    #[test]
    fn unsupported_domains_are_rejected() {
        for item in [
            quote!(
                fn f(x: &[u8]) {}
            ),
            quote!(
                fn f(x: &mut u8) {}
            ),
            quote!(
                fn f(x: *const u8) {}
            ),
            quote!(
                fn f(x: impl Copy) {}
            ),
            quote!(
                async fn f(x: u8) {}
            ),
            quote!(
                fn f<'a>(x: &'a u8) {}
            ),
            quote!(
                fn f<const N: usize>() {}
            ),
        ] {
            assert!(function(quote!(target = f, ensures(|_| true)), item).is_err());
        }
    }

    #[test]
    fn substituted_and_recursive_proofs_are_rejected() {
        for attr in [
            quote!(#[kani::stub_verified(g)]),
            quote!(#[cfg_attr(kani, kani::stub(f, g))]),
            quote!(#[kani::should_panic]),
            quote!(#[kani::recursion]),
        ] {
            assert!(
                function(quote!(target = f, ensures(|_| true)), quote!(#attr fn f() {})).is_err()
            );
        }
    }

    #[test]
    fn trait_impls_are_rejected() {
        assert!(implementation(quote!(), quote!(impl Trait for Example {})).is_err());
    }

    #[test]
    fn immutable_arguments_have_arbitrary_owned_storage() {
        let out = function(
            quote!(target = f, ensures(|r| *r > 0)),
            quote!(
                fn f(x: &u8) -> u8 {
                    *x
                }
            ),
        )
        .unwrap()
        .to_string();
        assert!(out.contains(":: kani :: any :: < u8 >"));
        assert!(out.contains("f (& __arg_0)"));
    }

    #[test]
    fn multiple_clauses_and_bounds_are_retained() {
        let out = function(
            quote!(
                target = f,
                requires(x > 0),
                requires(x < 100),
                ensures(|r| *r > 0),
                solver = kissat,
                unwind = 9
            ),
            quote!(
                fn f(x: u8) -> u8 {
                    x
                }
            ),
        )
        .unwrap()
        .to_string();
        assert_eq!(out.matches("kani :: requires").count(), 2);
        assert!(out.contains("kani :: unwind (9)"));
        assert!(out.contains("kani :: solver (kissat)"));
    }

    #[test]
    fn missing_postcondition_and_method_owner_are_errors() {
        assert!(function(
            quote!(target = f),
            quote!(
                fn f() {}
            )
        )
        .is_err());
        assert!(function(
            quote!(method, ensures(|_| true)),
            quote!(
                fn f(&self) {}
            )
        )
        .is_err());
    }

    #[test]
    fn free_function_target_is_inferred() {
        let out = function(
            quote!(ensures(|r| *r == x)),
            quote!(
                fn f(x: u8) -> u8 {
                    x
                }
            ),
        )
        .unwrap()
        .to_string();
        assert!(out.contains("proof_for_contract (f)"));
        assert!(out.contains("f (__arg_0)"));
        assert!(function(
            quote!(target = other_module::f, ensures(|_| true)),
            quote!(
                fn f() {}
            )
        )
        .is_err());
        assert!(function(
            quote!(target = other, ensures(|_| true)),
            quote!(
                fn f() {}
            )
        )
        .is_err());
    }
    #[test]
    fn verified_dependencies_are_attached_only_to_the_proof() {
        let out = function(
            quote!(ensures(|_| true), stub_verified(helper), stub_verified(other::<u16>)),
            quote!(
                fn f(x: u8) -> u8 {
                    helper(x)
                }
            ),
        )
        .unwrap();
        let file: syn::File = syn::parse2(out).unwrap();
        let item = match &file.items[0] {
            syn::Item::Fn(f) => f,
            _ => panic!(),
        };
        assert!(!item
            .attrs
            .iter()
            .any(|a| a.path().segments.last().unwrap().ident == "stub_verified"));
        let proof = match &file.items[2] {
            syn::Item::Fn(f) => f,
            _ => panic!(),
        };
        let proof = quote!(#proof).to_string();
        assert!(proof.contains("kani :: stub_verified (helper)"));
        assert!(proof.contains("kani :: stub_verified (other :: < u16 >)"));
        for invalid in [quote!(stub(helper)), quote!(stub_verified()), quote!(stub_verified(a, b))]
        {
            assert!(function(
                quote!(ensures(|_| true), #invalid),
                quote!(
                    fn f() {}
                )
            )
            .is_err());
        }
    }

    #[test]
    fn generic_dependencies_resolve_self_and_concrete_types() {
        let out = implementation(
            quote!(instances(byte(T = u8))),
            quote!(impl<T> Example<T> {
                #[contract(ensures(|_| true), stub_verified(Self::helper), stub_verified(other::<T>))]
                fn f(x: T) -> T { x }
            }),
        ).unwrap().to_string();
        assert!(out.contains("kani :: stub_verified (Example :: < u8 > :: helper)"));
        assert!(out.contains("kani :: stub_verified (other :: < u8 >)"));
        assert!(implementation(quote!(stub_verified(helper)), quote!(impl Example {}),).is_err());
    }
}
