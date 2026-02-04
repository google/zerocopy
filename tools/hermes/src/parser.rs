// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// extract_blocks is defined in this file, so no need to import from docs.
use anyhow::{Context, Result, anyhow};
use syn::{
    Attribute, Generics, ItemFn, ItemMod, ItemStruct, Signature, parse_file,
    visit::{self, Visit},
};

/// Represents a function extracted from the Rust source that requires verification or modeling.
#[derive(Debug, Clone)]
pub struct ParsedFunction {
    /// The function's signature (name, arguments, return type).
    pub sig: Signature,
    /// The raw content of the `///@ lean spec` block.
    pub spec: Option<String>,
    /// The raw content of the `///@ proof` block.
    pub proof: Option<String>,
    /// Whether this function is marked as a model (`///@ lean model`).
    pub is_model: bool,
    /// The hierarchy of modules containing this function (e.g. `["outer", "inner"]`).
    pub path: Vec<String>,
}

/// Represents a struct extracted from the Rust source that requires a `Verifiable` instance.
#[derive(Debug, Clone)]
pub struct ParsedStruct {
    /// The struct's name (identifier).
    pub ident: syn::Ident,
    /// The struct's generics (lifetime, type, const parameters).
    pub generics: Generics,
    /// The raw content of the `///@ lean invariant` block (optional).
    pub invariant: Option<String>,
    /// The hierarchy of modules containing this struct.
    pub path: Vec<String>,
}

/// A container for all artifacts extracted from a single source string.
#[derive(Debug, Default)]
pub struct ExtractedBlocks {
    pub functions: Vec<ParsedFunction>,
    pub structs: Vec<ParsedStruct>,
}

/// Visits the Rust AST to find functions and structs annotated with Hermes directives.
///
/// This visitor implements `syn::visit::Visit`, allowing it to traverse the syntax tree
/// and collect relevant items while maintaining track of the current module path.
struct SpecVisitor {
    functions: Vec<ParsedFunction>,
    structs: Vec<ParsedStruct>,
    errors: Vec<anyhow::Error>,
    /// Stack of module names representing the current scope.
    current_path: Vec<String>,
}

impl SpecVisitor {
    fn new() -> Self {
        Self {
            functions: Vec::new(),
            structs: Vec::new(),
            errors: Vec::new(),
            current_path: Vec::new(),
        }
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
                match current_mode {
                    Some("spec") => spec_lines.push(trimmed[1..].trim().to_string()),
                    Some("proof") => proof_lines.push(trimmed[1..].trim().to_string()),
                    None => self.errors.push(anyhow::anyhow!("Found `///@` line without preceding `lean spec` or `proof` on function '{}'", node.sig.ident)),
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
            self.functions.push(ParsedFunction {
                sig: node.sig.clone(),
                spec,
                proof,
                is_model,
                path: self.current_path.clone(),
            });
        }

        visit::visit_item_fn(self, node);
    }

    // ... (structs don't need path? actually they might if we generate instances. But for now focusing on functions/FunsExternal)

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "module");
        self.current_path.push(node.ident.to_string());
        visit::visit_item_mod(self, node);
        self.current_path.pop();
    }
    // ...

    fn visit_item_struct(&mut self, node: &'ast ItemStruct) {
        let mut invariant = None;

        for trimmed in crate::docs::iter_hermes_lines(&node.attrs) {
            if let Some(content) = crate::docs::parse_hermes_tag(&trimmed, "lean invariant") {
                let mut content = content;
                // Ignore if it's just the struct name (heuristic for empty default?)
                if node.ident == content {
                    continue;
                }

                // Strip "is_valid self :=" or "is_valid :="
                // This handles common patterns users might write in the doc comment
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
                    invariant = Some(content.to_string());
                    // We assume only one invariant block for now or take the last?
                    // Or we could join them? Hermes usually expects one block.
                    // Let's just break after finding one for simplicity or join if multiline logic needed?
                    // But `iter_hermes_lines` yields *lines*.
                    // If the user writes:
                    // ///@ lean invariant
                    // ///@   x > 0
                    // ///@   y > 0
                    // We need to capture subsequent lines.
                    // The `parse_hermes_tag` only handles match on the SAME line or activation.
                }
            } else if invariant.is_some() {
                // Append continuation lines if we are in invariant mode?
                // But `iter_hermes_lines` loop doesn't maintain state easily across iterations if we don't track it.
                // We need `current_mode` state tracking like in `visit_item_fn`.
            }
        }

        // Re-implementing state tracking correctly:
        let mut invariant_lines = Vec::new();
        let mut in_invariant = false;

        for trimmed in crate::docs::iter_hermes_lines(&node.attrs) {
            if let Some(content) = crate::docs::parse_hermes_tag(&trimmed, "lean invariant") {
                in_invariant = true;
                if !content.is_empty() && content != node.ident.to_string() {
                    // Clean up content
                    let mut c = content;
                    if let Some(rest) = c.strip_prefix("is_valid") {
                        let rest = rest.trim();
                        if let Some(rest) = rest.strip_prefix("self") {
                            let rest = rest.trim();
                            if let Some(rest) = rest.strip_prefix(":=") {
                                c = rest.trim();
                            }
                        } else if let Some(rest) = rest.strip_prefix(":=") {
                            c = rest.trim();
                        }
                    }
                    if !c.is_empty() {
                        invariant_lines.push(c.to_string());
                    }
                }
            } else if in_invariant {
                // Continuation line
                invariant_lines.push(trimmed[1..].trim().to_string());
            }
        }

        let invariant =
            if !invariant_lines.is_empty() { Some(invariant_lines.join("\n")) } else { None };

        if let Some(inv) = invariant {
            self.structs.push(ParsedStruct {
                ident: node.ident.clone(),
                generics: node.generics.clone(),
                invariant: Some(inv),
                path: self.current_path.clone(),
            });
        }

        visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &'ast syn::ItemEnum) {
        self.check_attrs_for_misplaced_spec(&node.attrs, "enum");
        visit::visit_item_enum(self, node);
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

/// Parses the source code string and extracts all Hermes-annotated items.
///
/// # Returns
/// An `ExtractedBlocks` struct containing all found functions and structs,
/// or an error if parsing failed.
pub fn extract_blocks(source: &str) -> Result<ExtractedBlocks> {
    let syn_file = syn::parse_file(source).context("Failed to parse Rust source")?;
    let mut visitor = SpecVisitor::new();
    visitor.visit_file(&syn_file);

    if !visitor.errors.is_empty() {
        // For now, return the first error.
        return Err(anyhow!("Errors encountered during parsing: {:?}", visitor.errors));
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
