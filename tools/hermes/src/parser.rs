// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use anyhow::{Result, bail};
use syn::{
    Attribute, ItemFn, parse_file,
    visit::{self, Visit},
};

/// Represents a function parsed from the source code, including its signature and attached specs.
#[derive(Debug, Clone)]
pub struct ParsedFunction {
    pub fn_name: String,
    pub generics: syn::Generics,
    pub spec: Option<String>,
    pub proof: Option<String>,
}

pub struct ExtractedBlocks {
    pub functions: Vec<ParsedFunction>,
}

struct SpecVisitor {
    functions: Vec<ParsedFunction>,
    errors: Vec<anyhow::Error>,
}

impl SpecVisitor {
    fn new() -> Self {
        Self { functions: Vec::new(), errors: Vec::new() }
    }

    fn check_attrs_for_misplaced_spec(&mut self, attrs: &[Attribute], item_kind: &str) {
        for attr in attrs {
            if let Some(doc_str) = parse_doc_attr(attr) {
                if doc_str.trim_start().starts_with("@") {
                    self.errors.push(anyhow::anyhow!(
                        "Found `///@` spec usage on a {}, but it is only allowed on functions.",
                        item_kind
                    ));
                }
            }
        }
    }
}

impl<'ast> Visit<'ast> for SpecVisitor {
    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        let fn_name = node.sig.ident.to_string();
        let mut spec_lines = Vec::new();
        let mut proof_lines = Vec::new();
        let mut current_mode = None; // None, Some("spec"), Some("proof")

        for attr in &node.attrs {
            if let Some(doc_str) = parse_doc_attr(attr) {
                let trimmed = doc_str.trim();
                // Check for ///@ marker (doc comment starting with @)
                if trimmed.starts_with('@') {
                    // Check if it's a new block start
                    if let Some(content) = trimmed.strip_prefix("@ lean spec") {
                        current_mode = Some("spec");
                        spec_lines.push(content.to_string());
                    } else if let Some(content) = trimmed.strip_prefix("@ lean model") {
                        current_mode = Some("spec"); // Treat model as spec
                        spec_lines.push(content.to_string());
                    } else if let Some(content) = trimmed.strip_prefix("@ proof") {
                        current_mode = Some("proof");
                        proof_lines.push(content.to_string());
                    } else {
                        // Continuation line
                        match current_mode {
                            Some("spec") => {
                                // strip leading @ and space?
                                // User types `///@ ...` -> extracted `@ ...`
                                // If we just extract `@`, we get ` ...`
                                // The user might put `///@   ...`.
                                // If I strip `@`, I get `   ...`.
                                // I should probably strip the leading `@` and one optional space?
                                // `trimmed` starts with `@`.
                                let content = &trimmed[1..];
                                spec_lines.push(content.to_string());
                            }
                            Some("proof") => {
                                let content = &trimmed[1..];
                                proof_lines.push(content.to_string());
                            }
                            None => {
                                // Orphaned @ line? or maybe not meant for us?
                                self.errors.push(anyhow::anyhow!("Found `///@` line without preceding `lean spec` or `proof` on function '{}'", fn_name));
                            }
                            _ => {} // Should not be possible with current_mode logic
                        }
                    }
                }
            }
        }

        let spec = if !spec_lines.is_empty() {
            let full_spec = spec_lines.join("\n");
            let trimmed_spec = full_spec.trim();
            // Strip function name from the beginning of the spec
            if let Some(rest) = trimmed_spec.strip_prefix(fn_name.as_str()) {
                Some(rest.trim().to_string())
            } else {
                Some(trimmed_spec.to_string())
            }
        } else {
            None
        };

        let proof = if !proof_lines.is_empty() { Some(proof_lines.join("\n")) } else { None };

        if spec.is_some() || proof.is_some() {
            self.functions.push(ParsedFunction {
                fn_name,
                generics: node.sig.generics.clone(),
                spec,
                proof,
            });
        }

        // Continue visiting children
        visit::visit_item_fn(self, node);
    }

    fn visit_item_struct(&mut self, node: &'ast syn::ItemStruct) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "struct");
        visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &'ast syn::ItemEnum) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "enum");
        visit::visit_item_enum(self, node);
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "module");
        visit::visit_item_mod(self, node);
    }

    fn visit_item_const(&mut self, node: &'ast syn::ItemConst) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "const");
        visit::visit_item_const(self, node);
    }

    // Catch-all for other items with attributes?
    // Ideally we'd cover all items, but these are the most common places users might mistakenly put docs.
    // Let's also cover TypeAlias and Trait

    fn visit_item_type(&mut self, node: &'ast syn::ItemType) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "type alias");
        visit::visit_item_type(self, node);
    }

    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "trait");
        visit::visit_item_trait(self, node);
    }
}

fn parse_doc_attr(attr: &Attribute) -> Option<String> {
    if !attr.path().is_ident("doc") {
        return None;
    }

    // syn 2.0: doc = "..." is a NameValue meta
    match &attr.meta {
        syn::Meta::NameValue(nv) => match &nv.value {
            syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }) => Some(s.value()),
            _ => None,
        },
        _ => None,
    }
}

pub fn extract_blocks(content: &str) -> Result<ExtractedBlocks> {
    let ast = parse_file(content)?;
    let mut visitor = SpecVisitor::new();
    visitor.visit_file(&ast);

    if !visitor.errors.is_empty() {
        // Return the first error for now, or bundle them
        let msg = visitor.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n");
        bail!("Spec extraction failed:\n{}", msg);
    }

    Ok(ExtractedBlocks { functions: visitor.functions })
}
