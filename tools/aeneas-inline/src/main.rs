// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Preserve Rust comments and associate annotations with parsed function braces.

use std::{fs, io};

use proc_macro2::LineColumn;
use serde_json::{json, Value};
use syn::visit::{self, Visit};

struct Functions<'a> {
    source: &'a str,
    modules: Vec<String>,
    unsupported: usize,
    impl_type: Option<String>,
    impl_generics: Vec<String>,
    inherent: bool,
    functions: Vec<Value>,
    implementations: Vec<Value>,
}

impl Functions<'_> {
    fn offset(&self, pos: LineColumn) -> usize {
        let start =
            self.source.split_inclusive('\n').take(pos.line - 1).map(str::len).sum::<usize>();
        start
            + self.source[start..]
                .char_indices()
                .nth(pos.column)
                .map_or(self.source[start..].len(), |(byte, _)| byte)
    }

    fn function(&mut self, sig: &syn::Signature, block: &syn::Block, method: bool) {
        let open = self.offset(block.brace_token.span.open().start());
        assert_eq!(&self.source[open..open + 1], "{", "Invalid function brace span");
        let mut path = self.modules.clone();
        path.push(sig.ident.to_string());
        let mut supported = self.unsupported == 0;
        let mut inputs = Vec::new();
        for input in &sig.inputs {
            match input {
                syn::FnArg::Receiver(_) => inputs.push("self".to_string()),
                syn::FnArg::Typed(input) => match input.pat.as_ref() {
                    syn::Pat::Ident(pattern)
                        if pattern.by_ref.is_none() && pattern.subpat.is_none() =>
                    {
                        inputs.push(pattern.ident.to_string());
                    }
                    _ => supported = false,
                },
            }
        }
        let mut generics = if method { self.impl_generics.clone() } else { Vec::new() };
        for parameter in &sig.generics.params {
            match parameter {
                syn::GenericParam::Type(parameter) => generics.push(parameter.ident.to_string()),
                syn::GenericParam::Lifetime(_) => {}
                syn::GenericParam::Const(_) => supported = false,
            }
        }
        self.functions.push(json!({
            "path": path.join("::"), "open": open,
            "close": self.offset(block.brace_token.span.close().end()),
            "supported": supported, "inputs": inputs, "generics": generics,
            "method": method, "impl_type": self.impl_type, "inherent": self.inherent,
        }));
    }
}

impl<'ast> Visit<'ast> for Functions<'_> {
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        self.modules.push(item.ident.to_string());
        visit::visit_item_mod(self, item);
        self.modules.pop();
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.function(&item.sig, &item.block, false);
        // Never attribute nested functions to the enclosing function or method.
        self.unsupported += 1;
        visit::visit_item_fn(self, item);
        self.unsupported -= 1;
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let previous_type = self.impl_type.clone();
        let previous_inherent = self.inherent;
        let previous_generics = self.impl_generics.clone();
        self.impl_generics = item.generics.type_params().map(|p| p.ident.to_string()).collect();
        self.impl_type = match item.self_ty.as_ref() {
            syn::Type::Path(path) => path.path.segments.last().map(|s| s.ident.to_string()),
            _ => None,
        };
        self.inherent = item.trait_.is_none();
        // A local named Self may apply the impl's own type parameters.
        // Specializations, qualified Self and trait impls still fail closed.
        let ident = match item.self_ty.as_ref() {
            syn::Type::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
                let segment = &path.path.segments[0];
                let supported = match &segment.arguments {
                    syn::PathArguments::None => true,
                    syn::PathArguments::AngleBracketed(args) => args.args.iter().all(|arg| {
                        let syn::GenericArgument::Type(syn::Type::Path(arg)) = arg else {
                            return false;
                        };
                        arg.qself.is_none()
                            && arg.path.get_ident().is_some_and(|ident| {
                                item.generics.type_params().any(|param| param.ident == *ident)
                            })
                    }),
                    _ => false,
                };
                supported.then_some(&segment.ident)
            }
            _ => None,
        };
        let ident = ident.filter(|_| item.trait_.is_none() && self.unsupported == 0);
        let macros: Vec<_> = item
            .items
            .iter()
            .filter_map(|item| match item {
                syn::ImplItem::Macro(item) => Some(
                    item.mac
                        .path
                        .segments
                        .iter()
                        .map(|s| s.ident.to_string())
                        .collect::<Vec<_>>()
                        .join("::"),
                ),
                _ => None,
            })
            .collect();
        // Record impls and direct macro invocations before cfg filtering. An
        // empty or macro-only impl must not disappear from closed coverage.
        self.implementations.push(json!({
            "type": self.impl_type, "inherent": self.inherent,
            "supported": ident.is_some(), "macros": macros, "modules": self.modules,
        }));
        if let Some(ident) = ident {
            self.modules.push(ident.to_string());
            visit::visit_item_impl(self, item);
            self.modules.pop();
        } else {
            self.unsupported += 1;
            visit::visit_item_impl(self, item);
            self.unsupported -= 1;
        }
        self.impl_type = previous_type;
        self.inherent = previous_inherent;
        self.impl_generics = previous_generics;
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.function(&item.sig, &item.block, true);
        self.unsupported += 1;
        visit::visit_impl_item_fn(self, item);
        self.unsupported -= 1;
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        self.unsupported += 1;
        visit::visit_item_trait(self, item);
        self.unsupported -= 1;
    }
}

fn inspect(source: &str) -> Result<Value, syn::Error> {
    let mut offset = 0;
    let mut comments = Vec::new();
    for token in rustc_lexer::tokenize(source) {
        match token.kind {
            rustc_lexer::TokenKind::LineComment | rustc_lexer::TokenKind::BlockComment { .. } => {
                comments.push(json!({"start": offset, "end": offset + token.len}));
            }
            _ => {}
        }
        offset += token.len;
    }
    let syntax = syn::parse_file(source)?;
    let mut visitor = Functions {
        source,
        modules: Vec::new(),
        unsupported: 0,
        impl_type: None,
        impl_generics: Vec::new(),
        inherent: false,
        functions: Vec::new(),
        implementations: Vec::new(),
    };
    visitor.visit_file(&syntax);
    Ok(json!({"comments": comments, "functions": visitor.functions,
              "implementations": visitor.implementations}))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let paths: Vec<String> = serde_json::from_reader(io::stdin())?;
    let mut result = serde_json::Map::new();
    for path in paths {
        let source = fs::read_to_string(&path)?;
        let inspected = inspect(&source).map_err(|error| format!("{path}: {error}"))?;
        result.insert(path, inspected);
    }
    serde_json::to_writer(io::stdout(), &result)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_real_comments_but_not_raw_string_contents() {
        let source =
            "fn f() { // real\n let x = r###\"// fake /* fake */\"###; /* outer /* inner */ */ }";
        let value = inspect(source).unwrap();
        assert_eq!(value["comments"].as_array().unwrap().len(), 2);
        assert_eq!(value["functions"][0]["path"], "f");
    }

    #[test]
    fn tracks_unicode_spans_modules_and_nested_functions_before_cfg_filtering() {
        let source = "const 雪: u8 = 0; mod m { #[cfg(any())] fn f() { fn inner() {} } }";
        let value = inspect(source).unwrap();
        let functions = value["functions"].as_array().unwrap();
        assert_eq!(functions[0]["path"], "m::f");
        assert_eq!(functions[0]["supported"], true);
        assert_eq!(functions[1]["supported"], false);
        let open = functions[0]["open"].as_u64().unwrap() as usize;
        assert!(source[open..].starts_with("{ fn inner()"));
    }

    #[test]
    fn resolves_simple_inherent_methods_and_rejects_other_impl_forms() {
        for (implementation, supported) in [
            ("impl S", true),
            ("impl<T> S<T>", true),
            ("impl S<u8>", false),
            ("impl Trait for S", false),
            ("impl m::S", false),
        ] {
            let source =
                format!("mod m {{ {implementation} {{ fn f() {{ fn nested() {{}} }} }} }}");
            let value = inspect(&source).unwrap();
            assert_eq!(value["functions"][0]["supported"], supported);
            assert_eq!(value["functions"][1]["supported"], false);
            if supported {
                assert_eq!(value["functions"][0]["path"], "m::S::f");
            }
        }
        let value = inspect("impl S { fn f<T>() {} }").unwrap();
        assert_eq!(value["functions"][0]["supported"], true);
    }

    #[test]
    fn preserves_input_order_and_impl_generics_and_rejects_patterns() {
        let value = inspect("impl<E> S<E> { fn f<T>(&self, mut x: T, y: E) {} }").unwrap();
        assert_eq!(value["functions"][0]["generics"], json!(["E", "T"]));
        assert_eq!(value["functions"][0]["inputs"], json!(["self", "x", "y"]));
        assert_eq!(value["functions"][0]["supported"], true);
        for source in ["fn f((x, y): (u8, u8)) {}", "fn f(_: u8) {}", "fn f<const N: usize>() {}"] {
            assert_eq!(inspect(source).unwrap()["functions"][0]["supported"], false);
        }
    }

    #[test]
    fn records_empty_and_macro_only_impls_before_cfg_filtering() {
        let value = inspect(
            "impl S {} #[cfg(any())] impl m::S { #[cfg(any())] methods!(); } \
             impl Trait for S { methods!(); } fn f() { unrelated!(); }",
        )
        .unwrap();
        let implementations = value["implementations"].as_array().unwrap();
        assert_eq!(implementations.len(), 3);
        assert_eq!(implementations[0]["type"], "S");
        assert_eq!(implementations[0]["supported"], true);
        assert_eq!(implementations[0]["macros"], json!([]));
        assert_eq!(implementations[1]["type"], "S");
        assert_eq!(implementations[1]["inherent"], true);
        assert_eq!(implementations[1]["supported"], false);
        assert_eq!(implementations[1]["macros"], json!(["methods"]));
        assert_eq!(implementations[2]["inherent"], false);
        let nested = inspect("mod m { impl S { fn f() {} } }").unwrap();
        assert_eq!(nested["implementations"][0]["modules"], json!(["m"]));
        assert_eq!(nested["functions"][0]["path"], "m::S::f");
    }
}
