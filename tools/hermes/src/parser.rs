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

// ... (imports remain)

/// Represents a function parsed from the source code, including its signature and attached specs.
#[derive(Debug, Clone)]
pub struct ParsedFunction {
    pub sig: syn::Signature,
    pub spec: Option<String>,
    pub proof: Option<String>,
    pub is_model: bool,
}

/// Represents a struct parsed from the source code, including its invariant.
#[derive(Debug, Clone)]
pub struct ParsedStruct {
    pub ident: syn::Ident,
    pub generics: syn::Generics,
    pub invariant: Option<String>,
}

pub struct ExtractedBlocks {
    pub functions: Vec<ParsedFunction>,
    pub structs: Vec<ParsedStruct>,
}

struct SpecVisitor {
    functions: Vec<ParsedFunction>,
    structs: Vec<ParsedStruct>,
    errors: Vec<anyhow::Error>,
}

impl SpecVisitor {
    fn new() -> Self {
        Self { functions: Vec::new(), structs: Vec::new(), errors: Vec::new() }
    }

    fn check_attrs_for_misplaced_spec(&mut self, attrs: &[Attribute], item_kind: &str) {
        for _line in crate::docs::iter_hermes_lines(attrs) {
            // We already filtered for is_hermes_directive
            // But we specifically check if it *starts* with @ and we error if it's misplaced
            // iter_hermes_lines ensures it filters for lines starting with @.
            // So every line here is a spec usage.
            self.errors.push(anyhow::anyhow!(
                "Found `///@` spec usage on a {}, but it is only allowed on functions or structs.",
                item_kind
            ));
        }
    }
}

impl<'ast> Visit<'ast> for SpecVisitor {
    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        let mut spec_lines = Vec::new();
        let mut proof_lines = Vec::new();
        let mut current_mode = None; // None, Some("spec"), Some("proof")
        let mut is_model = false;

        for trimmed in crate::docs::iter_hermes_lines(&node.attrs) {
            // Check if it's a new block start
            if let Some(content) = crate::docs::parse_hermes_tag(&trimmed, "lean spec") {
                current_mode = Some("spec");
                spec_lines.push(content.to_string());
            } else if let Some(content) = crate::docs::parse_hermes_tag(&trimmed, "lean model") {
                current_mode = Some("spec");
                is_model = true;
                spec_lines.push(content.to_string());
            } else if let Some(content) = crate::docs::parse_hermes_tag(&trimmed, "proof") {
                current_mode = Some("proof");
                proof_lines.push(content.to_string());
            } else {
                // Continuation line
                match current_mode {
                    Some("spec") | Some("proof") => {
                        // For continuation, we might want to just take the whole line after `@`?
                        // Or does the current logic assume `@` is just a marker?
                        // Original: `let content = &trimmed[1..];`
                        // We can use `parse_hermes_tag(trimmed, "")` maybe? No, that expects space.
                        // Let's simplify:
                        let content = trimmed[1..].trim();
                        if current_mode == Some("spec") {
                            spec_lines.push(content.to_string());
                        } else {
                            proof_lines.push(content.to_string());
                        }
                    }
                    None => {
                        self.errors.push(anyhow::anyhow!("Found `///@` line without preceding `lean spec` or `proof` on function '{}'", node.sig.ident));
                    }
                    _ => {}
                }
            }
        }

        let spec = if !spec_lines.is_empty() {
            Some(spec_lines.join("\n").trim().to_string())
        } else {
            None
        };

        let proof = if !proof_lines.is_empty() { Some(proof_lines.join("\n")) } else { None };

        if spec.is_some() || proof.is_some() {
            self.functions.push(ParsedFunction { sig: node.sig.clone(), spec, proof, is_model });
        }

        // Continue visiting children (though heavily nested functions are rare/unsupported for specs usually)
        visit::visit_item_fn(self, node);
    }

    fn visit_item_struct(&mut self, node: &'ast syn::ItemStruct) {
        let mut invariant_lines = Vec::new();
        let mut current_mode = None; // None, Some("invariant")

        for trimmed in crate::docs::iter_hermes_lines(&node.attrs) {
            if let Some(content) = crate::docs::parse_hermes_tag(&trimmed, "lean invariant") {
                current_mode = Some("invariant");
                let mut content = content;
                // Ignore if it's just the struct name or empty
                // referencing node.ident
                if node.ident == content {
                    content = "";
                }

                // Strip "is_valid self :=" or "is_valid :="
                if let Some(rest) = content.strip_prefix("is_valid") {
                    let rest = rest.trim();
                    if let Some(rest) = rest.strip_prefix("self") {
                        let rest = rest.trim();
                        if let Some(rest) = rest.strip_prefix(":=") {
                            content = rest.trim();
                        }
                    } else if let Some(rest) = rest.strip_prefix(":=") {
                        content = rest.trim();
                    }
                }

                if !content.is_empty() {
                    invariant_lines.push(content.to_string());
                }
            } else {
                match current_mode {
                    Some("invariant") => {
                        let content = trimmed[1..].trim();
                        invariant_lines.push(content.to_string());
                    }
                    None => {
                        self.errors.push(anyhow::anyhow!(
                            "Found `///@` line without preceding `lean invariant` on struct '{}'",
                            node.ident
                        ));
                    }
                    _ => {}
                }
            }
        }

        let invariant = if !invariant_lines.is_empty() {
            let mut full_inv = invariant_lines.join("\n").trim().to_string();
            // Strip "is_valid self :=" or "is_valid :="
            if let Some(rest) = full_inv.strip_prefix("is_valid") {
                let rest = rest.trim();
                if let Some(rest) = rest.strip_prefix("self") {
                    let rest = rest.trim();
                    if let Some(rest) = rest.strip_prefix(":=") {
                        full_inv = rest.trim().to_string();
                    }
                } else if let Some(rest) = rest.strip_prefix(":=") {
                    full_inv = rest.trim().to_string();
                }
            }
            Some(full_inv)
        } else {
            None
        };

        // We always collect structs now because we need to generate Verifiable instances for ALL structs
        // Ensure we don't add duplicate structs if for some reason we visit twice (unlikely but safe)
        // Checking by ident is enough for this context
        if !self.structs.iter().any(|s| s.ident == node.ident) {
            self.structs.push(ParsedStruct {
                ident: node.ident.clone(),
                generics: node.generics.clone(),
                invariant,
            });
        }

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

    fn visit_item_type(&mut self, node: &'ast syn::ItemType) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "type alias");
        visit::visit_item_type(self, node);
    }

    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "trait");
        visit::visit_item_trait(self, node);
    }
}

pub fn extract_blocks(content: &str) -> Result<ExtractedBlocks> {
    let ast = parse_file(content)?;
    let mut visitor = SpecVisitor::new();
    visitor.visit_file(&ast);

    if !visitor.errors.is_empty() {
        let msg = visitor.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n");
        bail!("Spec extraction failed:\n{}", msg);
    }

    Ok(ExtractedBlocks { functions: visitor.functions, structs: visitor.structs })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_add_mod() {
        let content = r#"///@ lean spec add_mod (x y : Usize)
///@ requires _h_safe : x.val + y.val < 100
///@ ensures |ret| ret.val = (x.val + y.val) % Usize.size
///@ proof
///@   simp [add]
fn add(x: usize, y: usize) -> usize {
    x.wrapping_add(y)
}
"#;
        let res = parse_file(content);
        if let Err(e) = &res {
            println!("Error: {}", e);
        }
        assert!(res.is_ok());
    }
}
