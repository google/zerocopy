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
    functions: Vec<Value>,
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
}

impl<'ast> Visit<'ast> for Functions<'_> {
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        self.modules.push(item.ident.to_string());
        visit::visit_item_mod(self, item);
        self.modules.pop();
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        let open = self.offset(item.block.brace_token.span.open().start());
        assert_eq!(&self.source[open..open + 1], "{", "Invalid function brace span");
        let mut path = self.modules.clone();
        path.push(item.sig.ident.to_string());
        self.functions.push(json!({
            "path": path.join("::"), "open": open,
            "close": self.offset(item.block.brace_token.span.close().end()),
            "supported": self.unsupported == 0,
        }));
        // Nested functions, impls, traits and macros need an explicit extension
        // to identity resolution; never silently attribute them to a free fn.
        self.unsupported += 1;
        visit::visit_item_fn(self, item);
        self.unsupported -= 1;
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        self.unsupported += 1;
        visit::visit_item_impl(self, item);
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
    let mut visitor =
        Functions { source, modules: Vec::new(), unsupported: 0, functions: Vec::new() };
    visitor.visit_file(&syntax);
    Ok(json!({"comments": comments, "functions": visitor.functions}))
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
}
