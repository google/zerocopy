// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Report source ownership without compiling or expanding Rust.
//!
//! `syn` associates literal outer documentation with functions and nominal types.
//! The lexer independently reports every real comment, including comments that
//! have no supported owner. Python compares these reports so an orphaned fence
//! cannot disappear, while a fence inside a Rust string remains ordinary data.
//! All offsets refer to the exact source returned in the same JSON report. We
//! inspect inactive cfg branches too: coverage must not depend on the host cfg.

use std::{fs, io};

use proc_macro2::LineColumn;
use serde_json::{json, Value};
use syn::{
    spanned::Spanned,
    visit::{self, Visit},
};

struct Functions<'a> {
    source: &'a str,
    modules: Vec<String>,
    // Count enclosing contexts that cannot own supported contracts. A counter
    // preserves the outer restriction when a nested visitor enters and leaves.
    unsupported: usize,
    impl_type: Option<String>,
    impl_generics: Vec<String>,
    inherent: bool,
    functions: Vec<Value>,
    implementations: Vec<Value>,
    types: Vec<Value>,
    attributes: Vec<Value>,
}

impl Functions<'_> {
    // Span columns count characters; the editing protocol needs byte offsets.
    // Keep that conversion here so every reported range has the same meaning.
    fn offset(&self, pos: LineColumn) -> usize {
        let start =
            self.source.split_inclusive('\n').take(pos.line - 1).map(str::len).sum::<usize>();
        start
            + self.source[start..]
                .char_indices()
                .nth(pos.column)
                .map_or(self.source[start..].len(), |(byte, _)| byte)
    }

    fn docs(&self, attrs: &[syn::Attribute]) -> Vec<Value> {
        // Return decoded literal text and the physical attribute range together.
        // Computed docs are audited separately; expanding them would erase their
        // source ownership and could depend on cfg or external files.
        attrs
            .iter()
            .filter_map(|attr| {
                if !attr.path().is_ident("doc") || !matches!(attr.style, syn::AttrStyle::Outer) {
                    return None;
                }
                let syn::Meta::NameValue(meta) = &attr.meta else {
                    return None;
                };
                let syn::Expr::Lit(expr) = &meta.value else {
                    return None;
                };
                let syn::Lit::Str(text) = &expr.lit else {
                    return None;
                };
                Some(json!({"start": self.offset(attr.span().start()),
                        "end": self.offset(attr.span().end()), "text": text.value(),
                        "line": attr.span().start().line}))
            })
            .collect()
    }

    fn nominal(
        &mut self,
        ident: &syn::Ident,
        generics: &syn::Generics,
        attrs: &[syn::Attribute],
        span: proc_macro2::Span,
        kind: &str,
        fields: Value,
    ) {
        // Preserve source parameter order, even for parameters unused by fields.
        // Field admission is structural: an authored decoder cannot make a
        // borrowed or otherwise unsupported raw carrier acceptable here.
        let mut path = self.modules.clone();
        path.push(ident.to_string());
        let supported = self.unsupported == 0
            && generics.const_params().next().is_none()
            && generics.type_params().all(|p| p.bounds.is_empty())
            && generics.where_clause.is_none()
            && !has_borrowed_fields(&fields);
        let (computed_docs, include_str_docs) = doc_flags(attrs);
        self.types.push(json!({"path": path.join("::"), "kind": kind,
            "start": self.offset(ident.span().start()), "close": self.offset(span.end()),
            "supported": supported, "generics": generics.type_params().map(|p| p.ident.to_string()).collect::<Vec<_>>(),
            "inputs": [], "docs": self.docs(attrs), "computed_docs": computed_docs,
            "include_str_docs": include_str_docs, "fields": fields}));
    }

    fn function(
        &mut self,
        sig: &syn::Signature,
        block: &syn::Block,
        attrs: &[syn::Attribute],
        method: bool,
    ) {
        // The report identifies the original function and original argument
        // names. Python later checks this order against extraction before Lean
        // can construct the application used by the generated proposition.
        let open = self.offset(block.brace_token.span.open().start());
        assert_eq!(&self.source[open..open + 1], "{", "Invalid function brace span");
        let mut path = self.modules.clone();
        path.push(sig.ident.to_string());
        let mut supported = self.unsupported == 0;
        let mut inputs = Vec::new();
        for input in &sig.inputs {
            match input {
                syn::FnArg::Receiver(receiver) => {
                    inputs.push("self".to_string());
                    supported &= receiver.reference.is_none() || receiver.mutability.is_none();
                }
                syn::FnArg::Typed(input) => {
                    supported &= !unsupported_borrow(&input.ty, true);
                    match input.pat.as_ref() {
                        syn::Pat::Ident(pattern)
                            if pattern.by_ref.is_none() && pattern.subpat.is_none() =>
                        {
                            inputs.push(pattern.ident.to_string());
                        }
                        _ => supported = false,
                    }
                }
            }
        }
        if let syn::ReturnType::Type(_, ty) = &sig.output {
            supported &= !unsupported_borrow(ty, false);
        }
        supported &= sig.generics.where_clause.is_none();
        let mut generics = if method { self.impl_generics.clone() } else { Vec::new() };
        for parameter in &sig.generics.params {
            match parameter {
                syn::GenericParam::Type(parameter) => {
                    generics.push(parameter.ident.to_string());
                    supported &= parameter.bounds.is_empty();
                }
                syn::GenericParam::Lifetime(_) => {}
                syn::GenericParam::Const(_) => supported = false,
            }
        }
        let (computed_docs, include_str_docs) = doc_flags(attrs);
        self.functions.push(json!({
            "path": path.join("::"), "kind": "function", "open": open,
            "start": self.offset(sig.fn_token.span.start()), "docs": self.docs(attrs),
            "computed_docs": computed_docs, "include_str_docs": include_str_docs,
            "close": self.offset(block.brace_token.span.close().end()),
            "supported": supported, "inputs": inputs, "generics": generics,
            "method": method, "impl_type": self.impl_type, "inherent": self.inherent,
        }));
    }
}

// Literal source docs own annotations. Other computed docs remain ordinary
// Rust documentation unless that owner also carries an annotation. Direct
// include_str! is detected without expanding any documentation macro.
fn doc_flags(attrs: &[syn::Attribute]) -> (bool, bool) {
    fn flags(meta: &syn::Meta) -> (bool, bool) {
        match meta {
            syn::Meta::NameValue(value) if value.path.is_ident("doc") => {
                struct Includes(bool);
                impl<'ast> Visit<'ast> for Includes {
                    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
                        self.0 |=
                            mac.path.segments.last().is_some_and(|p| p.ident == "include_str")
                                || tokens_include_str(mac.tokens.clone());
                    }
                }
                let mut includes = Includes(false);
                includes.visit_expr(&value.value);
                (
                    !matches!(&value.value, syn::Expr::Lit(expr) if matches!(expr.lit, syn::Lit::Str(_))),
                    includes.0,
                )
            }
            syn::Meta::List(list) if list.path.is_ident("cfg_attr") => {
                use syn::parse::Parser as _;
                let parser =
                    syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated;
                match parser.parse2(list.tokens.clone()) {
                    Ok(entries) => entries
                        .iter()
                        .skip(1)
                        .map(flags)
                        .fold((false, false), |a, b| (a.0 || b.0, a.1 || b.1)),
                    Err(_) => (
                        mentions_doc(list.tokens.clone()),
                        mentions_doc(list.tokens.clone())
                            && tokens_include_str(list.tokens.clone()),
                    ),
                }
            }
            _ => (false, false),
        }
    }
    attrs.iter().map(|attr| flags(&attr.meta)).fold((false, false), |a, b| (a.0 || b.0, a.1 || b.1))
}

fn tokens_include_str(tokens: proc_macro2::TokenStream) -> bool {
    // Macros hide syntax from syn's expression visitor, so inspect their token
    // groups too. Require an actual invocation, not the word in a literal.
    use proc_macro2::TokenTree;
    let tokens: Vec<_> = tokens.into_iter().collect();
    tokens.windows(3).any(|window| {
        matches!(window,
        [TokenTree::Ident(name), TokenTree::Punct(bang), TokenTree::Group(_)]
            if name == "include_str" && bang.as_char() == '!')
    }) || tokens.iter().any(|token| match token {
        TokenTree::Group(group) => tokens_include_str(group.stream()),
        _ => false,
    })
}

fn mentions_doc(tokens: proc_macro2::TokenStream) -> bool {
    // This conservative fallback handles conditional docs that cannot be parsed
    // as ordinary metadata. Python must still see their literal fragments.
    tokens.into_iter().any(|token| match token {
        proc_macro2::TokenTree::Ident(ident) => ident == "doc",
        proc_macro2::TokenTree::Group(group) => mentions_doc(group.stream()),
        _ => false,
    })
}

fn token_strings(tokens: proc_macro2::TokenStream, output: &mut Vec<String>) {
    // Collect literal fragments without evaluating the surrounding macro. This
    // supports the reserved-fence audit but never authorizes a computed fence.
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Literal(literal) => {
                if let Ok(text) = syn::parse_str::<syn::LitStr>(&literal.to_string()) {
                    output.push(text.value());
                }
            }
            proc_macro2::TokenTree::Group(group) => token_strings(group.stream(), output),
            _ => {}
        }
    }
}

fn doc_fragments(meta: &syn::Meta) -> Vec<String> {
    // Token groups and parsed metadata represent different attribute spellings.
    // Both contribute strings to the audit, not to the owner-doc payload.
    struct Strings(Vec<String>);
    impl<'ast> Visit<'ast> for Strings {
        fn visit_lit_str(&mut self, text: &'ast syn::LitStr) {
            self.0.push(text.value());
        }
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            token_strings(mac.tokens.clone(), &mut self.0);
        }
    }
    let mut strings = Strings(Vec::new());
    if let syn::Meta::List(list) = meta {
        token_strings(list.tokens.clone(), &mut strings.0);
    } else {
        strings.visit_meta(meta);
    }
    strings.0
}

// Shared input references are supported, but mutable inputs need backward borrow
// reconstruction. Outputs and nominal fields cannot retain any reference. One
// traversal enforces both policies, including references nested in containers.
// Function pointers remain unsupported under either policy.
fn unsupported_borrow(ty: &syn::Type, allow_shared: bool) -> bool {
    struct Borrow {
        found: bool,
        allow_shared: bool,
    }
    impl<'ast> Visit<'ast> for Borrow {
        fn visit_type_reference(&mut self, ty: &'ast syn::TypeReference) {
            self.found |= !self.allow_shared || ty.mutability.is_some();
            visit::visit_type_reference(self, ty);
        }
        fn visit_type_bare_fn(&mut self, _: &'ast syn::TypeBareFn) {
            self.found = true;
        }
    }
    let mut visitor = Borrow { found: false, allow_shared };
    visitor.visit_type(ty);
    visitor.found
}

fn has_borrowed_fields(fields: &Value) -> bool {
    // Struct fields and enum variants share the report's recursive container
    // shape. A borrowed field in any variant makes the nominal owner unsupported.
    match fields {
        Value::Array(values) => values.iter().any(has_borrowed_fields),
        Value::Object(values) => {
            values.get("borrowed") == Some(&Value::Bool(true))
                || values.values().any(has_borrowed_fields)
        }
        _ => false,
    }
}

fn fields(fields: &syn::Fields) -> Value {
    // Tuple positions are names too; preserve their order rather than inventing
    // source identifiers that could disagree with the extracted carrier.
    json!(fields
        .iter()
        .enumerate()
        .map(|(index, field)| {
            json!({"name": field.ident.as_ref().map_or(index.to_string(), ToString::to_string),
               "borrowed": unsupported_borrow(&field.ty, false)})
        })
        .collect::<Vec<_>>())
}

impl<'ast> Visit<'ast> for Functions<'_> {
    fn visit_attribute(&mut self, attr: &'ast syn::Attribute) {
        // Include every doc spelling, even forms that cannot be evaluated by syn.
        // Python rejects reserved fences in conditional/computed doc forms.
        let conditional_doc = match &attr.meta {
            syn::Meta::List(list) if attr.path().is_ident("cfg_attr") => {
                mentions_doc(list.tokens.clone())
            }
            _ => false,
        };
        if attr.path().is_ident("doc") || conditional_doc {
            let start = self.offset(attr.span().start());
            let end = self.offset(attr.span().end());
            self.attributes.push(json!({"start": start, "end": end,
                "outer": matches!(attr.style, syn::AttrStyle::Outer),
                "doc": attr.path().is_ident("doc"), "fragments": doc_fragments(&attr.meta)}));
        }
        visit::visit_attribute(self, attr);
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.nominal(
            &item.ident,
            &item.generics,
            &item.attrs,
            item.span(),
            "struct",
            fields(&item.fields),
        );
        visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        let variants = item.variants.iter().map(|variant| {
            json!({"name": variant.ident.to_string(), "fields": fields(&variant.fields)})
        }).collect::<Vec<_>>();
        self.nominal(
            &item.ident,
            &item.generics,
            &item.attrs,
            item.span(),
            "enum",
            json!(variants),
        );
        visit::visit_item_enum(self, item);
    }

    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        self.modules.push(item.ident.to_string());
        visit::visit_item_mod(self, item);
        self.modules.pop();
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.function(&item.sig, &item.block, &item.attrs, false);
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
        let ident = ident.filter(|_| {
            item.trait_.is_none()
                && self.unsupported == 0
                && item.generics.const_params().next().is_none()
                && item.generics.type_params().all(|p| p.bounds.is_empty())
                && item.generics.where_clause.is_none()
        });
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
        self.function(&item.sig, &item.block, &item.attrs, true);
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
    // Keep comment discovery independent of AST ownership. A source string that
    // only resembles a comment must never enter this roster, while a real
    // orphaned comment must remain visible even when the AST has no valid owner.
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
        types: Vec::new(),
        attributes: Vec::new(),
    };
    visitor.visit_file(&syntax);
    Ok(json!({"source": source, "comments": comments, "functions": visitor.functions,
              "implementations": visitor.implementations, "types": visitor.types,
              "attributes": visitor.attributes}))
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
        let value = inspect("impl<E> S<E> { fn f<T>(self, mut x: T, y: E) {} }").unwrap();
        assert_eq!(value["functions"][0]["generics"], json!(["E", "T"]));
        assert_eq!(value["functions"][0]["inputs"], json!(["self", "x", "y"]));
        assert_eq!(value["functions"][0]["supported"], true);
        for source in [
            "fn f((x, y): (u8, u8)) {}",
            "fn f(_: u8) {}",
            "fn f<const N: usize>() {}",
            "fn f(x: &mut u8) {}",
            "fn f() -> &'static u8 {}",
            "impl S { fn f(&mut self) {} }",
        ] {
            assert_eq!(inspect(source).unwrap()["functions"][0]["supported"], false);
        }
    }

    #[test]
    fn borrow_policy_distinguishes_shared_inputs_from_outputs_and_fields() {
        for (ty, input_supported) in [
            ("u8", true),
            ("Option<&'static u8>", true),
            ("(&'static u8, Option<&'static mut u8>)", false),
            ("&'static &'static mut u8", false),
            ("Option<fn(u8) -> u8>", false),
        ] {
            let parsed: syn::Type = syn::parse_str(ty).unwrap();
            assert_eq!(unsupported_borrow(&parsed, true), !input_supported, "{ty}");
            assert_eq!(unsupported_borrow(&parsed, false), ty != "u8", "{ty}");
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
    #[test]
    fn owns_outer_literal_doc_attributes_and_preserves_nominal_metadata() {
        let source = "/// ```aeneas\n/// spec f_spec\n///   ensures r => True\n/// ```\n#[allow(unused)] fn f<T>(x: T) {}\n#[doc = \"```aeneas\\nmodel SValue := Fields\\ndecode self => self\\n```\"] struct S<T>(T); enum E { A, B(S<u8>) }";
        let value = inspect(source).unwrap();
        assert_eq!(value["functions"][0]["docs"].as_array().unwrap().len(), 4);
        assert_eq!(value["functions"][0]["docs"][0]["text"], " ```aeneas");
        assert_eq!(value["types"][0]["kind"], "struct");
        assert_eq!(value["types"][0]["generics"], json!(["T"]));
        assert_eq!(value["types"][0]["fields"][0]["name"], "0");
        assert_eq!(value["types"][1]["kind"], "enum");
        assert_eq!(value["types"][1]["fields"][1]["name"], "B");
        assert_eq!(value["attributes"].as_array().unwrap().len(), 5);
    }

    #[test]
    fn distinguishes_computed_docs_from_visible_include_str_invocations() {
        let source = "#[doc = condVersionLink!(\"version\", \"link\")] fn f() {} \
            #[cfg_attr(any(), doc = condVersionLink!(\"version\", \"link\"))] struct S; \
            #[doc = concat!(\"ordinary\", std::include_str!(\"contract.md\"))] fn g() {} \
            #[cfg_attr(any(), cfg_attr(all(), doc = wrapper!(::std::include_str!(\"contract.md\"))))] enum E { A }";
        let value = inspect(source).unwrap();
        assert_eq!(value["functions"][0]["computed_docs"], true);
        assert_eq!(value["functions"][0]["include_str_docs"], false);
        assert_eq!(value["types"][0]["computed_docs"], true);
        assert_eq!(value["types"][0]["include_str_docs"], false);
        assert_eq!(value["functions"][1]["include_str_docs"], true);
        assert_eq!(value["types"][1]["include_str_docs"], true);
        let value = inspect("#[doc = \"include_str!(not an invocation)\"] fn f() {}").unwrap();
        assert_eq!(value["functions"][0]["computed_docs"], false);
        assert_eq!(value["functions"][0]["include_str_docs"], false);
    }
}
