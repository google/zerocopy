// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    fs,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use quote::quote;
use syn::{Attribute, Expr, ExprBlock, ItemFn, parse_quote, visit_mut::VisitMut};
use walkdir::WalkDir;

pub fn create_shadow_crate(
    original_root: &Path,
    source_file: Option<&Path>,
) -> Result<(PathBuf, Option<PathBuf>, Vec<String>)> {
    // 1. Destination: target/hermes_shadow
    let shadow_root = original_root.join("target").join("hermes_shadow");
    if shadow_root.exists() {
        fs::remove_dir_all(&shadow_root)?;
    }
    fs::create_dir_all(&shadow_root)?;

    // 2. Recursive Copy (only if not a single-file script, OR generally?)
    // If it's a script, original_root might be unrelated.
    // However, if we preserve behaviour, we might want to copy cargo lock etc?

    // Copy Cargo.toml
    let cargo_toml = original_root.join("Cargo.toml");
    if cargo_toml.exists() {
        fs::copy(&cargo_toml, shadow_root.join("Cargo.toml"))
            .context("Failed to copy Cargo.toml")?;
    }

    // Copy Cargo.lock if exists
    let cargo_lock = original_root.join("Cargo.lock");
    if cargo_lock.exists() {
        fs::copy(&cargo_lock, shadow_root.join("Cargo.lock")).ok();
    }

    // Copy src/ recursively
    let src_path = original_root.join("src");
    if src_path.exists() {
        let dest_src = shadow_root.join("src");
        fs::create_dir_all(&dest_src)?;

        for entry in WalkDir::new(&src_path) {
            let entry = entry?;
            let relative = entry.path().strip_prefix(&src_path)?;
            let dest_path = dest_src.join(relative);

            if entry.file_type().is_dir() {
                fs::create_dir_all(&dest_path)?;
            } else if entry.file_type().is_file() {
                fs::copy(entry.path(), &dest_path)?;
            }
        }
    }

    // 3. Inject Shadow Std
    let shim_path = shadow_root.join("src").join("hermes_std.rs");
    if let Some(parent) = shim_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&shim_path, SHIM_CONTENT).context("Failed to write shadow std shim")?;

    // 4. Sanitization
    let mut models = sanitize_crate(&shadow_root)?;

    // 5. Handle Single Source File (Write it now so we can inject prelude)
    let shadow_source_file = if let Some(source) = source_file {
        let file_name = source.file_name().context("Invalid source file name")?;
        // Move to src/ so it can see __hermes_std.rs as a sibling module
        let dest_path = shadow_root.join("src").join(file_name);
        if let Some(parent) = dest_path.parent() {
            fs::create_dir_all(parent)?;
        }
        // Sanitize and write
        let file_models = process_file_content(source, &dest_path)?;
        models.extend(file_models);
        Some(dest_path)
    } else {
        None
    };

    // 6. Inject Prelude into Crate Roots
    let mut roots = Vec::new();
    if let Some(dest_path) = &shadow_source_file {
        roots.push(dest_path.clone());
    } else {
        // Standard crate structure
        let lib_rs = shadow_root.join("src").join("lib.rs");
        if lib_rs.exists() {
            roots.push(lib_rs);
        }
        let main_rs = shadow_root.join("src").join("main.rs");
        if main_rs.exists() {
            roots.push(main_rs);
        }
    }

    for root in roots {
        inject_prelude(&root)?;
    }

    // Return
    Ok((shadow_root, shadow_source_file, models))
}

const SHIM_CONTENT: &str = include_str!("include/__hermes_std.rs");

fn inject_prelude(path: &Path) -> Result<()> {
    if !path.exists() {
        return Ok(());
    }
    let content = fs::read_to_string(path)?;

    if content.contains("#![no_implicit_prelude]") {
        return Ok(());
    }

    let mut ast = syn::parse_file(&content)?;

    // 1. Disable the built-in Rust prelude (Inner Attribute)
    ast.attrs.push(parse_quote!(#![no_implicit_prelude]));

    // 2. Prepare Injection Items
    let prelude_items: Vec<syn::Item> = vec![
        // mod hermes_std;
        parse_quote!(
            mod hermes_std;
        ),
        // use crate::hermes_std as std;
        parse_quote!(
            #[allow(unused_imports)]
            use crate::hermes_std as std;
        ),
        // use crate::hermes_std as core;
        parse_quote!(
            #[allow(unused_imports)]
            use crate::hermes_std as core;
        ),
        // use std::prelude::rust_2021::*;
        parse_quote!(
            #[allow(unused_imports)]
            use std::prelude::rust_2021::*;
        ),
        // mod charon { pub use charon_macros::opaque; }
        // We need `charon_macros` to exist or be faked.
        // Actually, since we rewrite the crate, we can just define a dummy `opaque` attribute logic?
        // Rustc allows custom attributes if they are mapped to a tool or via `register_tool` (nightly).
        // For stable, we might need a dummy macro or just `allow` it?
        // But `#[charon::opaque]` looks like a path attribute.
        // Let's define: `pub mod charon { pub use crate::hermes_std::opaque; }`
        // and in `hermes_std` define `pub use ...`?
        // Simpler: define `mod charon` right here which exports a dummy `opaque` attribute macro?
        // Attributes must be macros.
    ];
    // 3. Insert at the beginning of items (AFTER inner attributes)
    ast.items.splice(0..0, prelude_items);

    let new_content = quote!(#ast).to_string();
    fs::write(path, new_content)?;
    Ok(())
}

fn process_file_content(src: &Path, dest: &Path) -> Result<Vec<String>> {
    let content = fs::read_to_string(src)?;
    let mut ast = syn::parse_file(&content)?;

    let mut visitor = ShadowVisitor::new();
    visitor.visit_file_mut(&mut ast);

    let new_content = quote!(#ast).to_string();
    fs::write(dest, new_content)?;
    Ok(visitor.models)
}

fn sanitize_crate(root: &Path) -> Result<Vec<String>> {
    let src_dir = root.join("src");
    let mut all_models = Vec::new();
    if !src_dir.exists() {
        return Ok(all_models);
    }

    for entry in WalkDir::new(&src_dir) {
        let entry = entry?;
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "rs") {
            let relative = entry.path().strip_prefix(&src_dir)?;
            // Map file path to module path (simplistic: foo/bar.rs -> foo::bar)
            // Note: ShadowVisitor tracks `current_path` relative to the file.
            // We need to prepend the module path derived from file structure?
            // Wait, ShadowVisitor `current_path` is empty at file root.
            // But if we are processing `src/foo/bar.rs`, the functions in it are in `foo::bar`.
            // `ShadowVisitor` doesn't know this external context unless we tell it.
            // OR we fix up the returned models.
            // `visitor.models` will contain e.g. `my_func` or `inner::my_func`.
            // We need to prepend `foo::bar`.

            // Logic for module path:
            let components: Vec<_> = relative
                .with_extension("")
                .iter()
                .map(|s| s.to_string_lossy().into_owned())
                .collect();
            // If filename is `mod.rs` or `lib.rs` or `main.rs`, handle accordingly.
            let mut mod_path = Vec::new();
            for (i, comp) in components.iter().enumerate() {
                if i == components.len() - 1 && (comp == "mod" || comp == "lib" || comp == "main") {
                    continue;
                }
                mod_path.push(comp.clone());
            }

            let file_models = process_file(entry.path())?;
            for m in file_models {
                let full =
                    if mod_path.is_empty() { m } else { format!("{}::{}", mod_path.join("::"), m) };
                all_models.push(full);
            }
        }
    }
    Ok(all_models)
}

fn process_file(path: &Path) -> Result<Vec<String>> {
    let content = fs::read_to_string(path)?;
    let mut ast = syn::parse_file(&content)?;

    let mut visitor = ShadowVisitor::new();
    visitor.visit_file_mut(&mut ast);

    let new_content = quote!(#ast).to_string();
    fs::write(path, new_content)?;
    Ok(visitor.models)
}

struct ShadowVisitor {
    current_path: Vec<String>,
    models: Vec<String>,
}

impl ShadowVisitor {
    fn new() -> Self {
        Self { current_path: Vec::new(), models: Vec::new() }
    }
}

impl VisitMut for ShadowVisitor {
    fn visit_item_mod_mut(&mut self, i: &mut syn::ItemMod) {
        self.current_path.push(i.ident.to_string());
        syn::visit_mut::visit_item_mod_mut(self, i);
        self.current_path.pop();
    }

    fn visit_item_fn_mut(&mut self, node: &mut ItemFn) {
        let (is_model, _model_requires) = parse_model_specs(&node.attrs);

        if is_model {
             // Collect model name
             let mut full_path = self.current_path.clone();
             full_path.push(node.sig.ident.to_string());
             self.models.push(full_path.join("::"));

             // Case A: Model Strategy
             // 1. Remove unsafe (if present)
             node.sig.unsafety = None;

             // 2. Replace body with loop {} (Diverge)
             let body_content = quote! {
                 {
                     loop {}
                 }
             };

             let block: syn::Block = syn::parse2(body_content).expect("Failed to parse loop body");
             *node.block = block;

             // Append #[allow(unused_variables)] if not present
             let has_allow_unused = node.attrs.iter().any(|attr| {
                 if attr.path().is_ident("allow") {
                     if let syn::Meta::List(list) = &attr.meta {
                         return list.tokens.to_string().contains("unused_variables");
                     }
                 }
                 false
             });

             if !has_allow_unused {
                 node.attrs.push(parse_quote!(#[allow(unused_variables)]));
             }
             return; 
        }

        // Pre-existing logic for unwrapping unsafe functions that are NOT models
        if node.sig.unsafety.is_some() {
             // Case B: Unwrap Strategy
             // 1. Remove unsafe
             node.sig.unsafety = None;

             // 2. Recurse into body to unwrap internal unsafe blocks
             syn::visit_mut::visit_item_fn_mut(self, node);
        } else {
             // Safe function not model: just recurse
             syn::visit_mut::visit_item_fn_mut(self, node);
        }
    }

    fn visit_expr_mut(&mut self, node: &mut Expr) {
        if let Expr::Unsafe(expr_unsafe) = node {
            // Transform `unsafe { ... }` into `{ ... }`
            // We preserve attributes and the inner block
            let new_expr = Expr::Block(ExprBlock {
                attrs: expr_unsafe.attrs.clone(),
                label: None,
                block: expr_unsafe.block.clone(),
            });
            *node = new_expr;

            // Recurse into the new block (in case there are nested unsafe blocks)
            self.visit_expr_mut(node);
        } else {
            syn::visit_mut::visit_expr_mut(self, node);
        }
    }
}

fn parse_model_specs(attrs: &[Attribute]) -> (bool, Vec<String>) {
    let mut is_model = false;
    let mut requires = Vec::new();

    // Debugging loop
    /*
    for attr in attrs {
         if attr.path().is_ident("doc") {
             println!("Found doc attr: {:?}", attr);
         }
    }
    */

    for trimmed in crate::docs::iter_hermes_lines(attrs) {
        if let Some(_content) = crate::docs::parse_hermes_tag(&trimmed, "lean model") {
            is_model = true;
        }

        if let Some(content) = crate::docs::parse_hermes_tag(&trimmed, "requires") {
            // Strip binder name if present (e.g. "h : x > 0" -> "x > 0")
            let condition =
                if let Some((_, expr)) = content.split_once(':') { expr.trim() } else { content };
            requires.push(condition.to_string());
        }
    }
    (is_model, requires)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use super::*;

    fn transform(code: &str) -> String {
        let mut ast = syn::parse_file(code).expect("Failed to parse input");
        let mut visitor = ShadowVisitor::new();
        visitor.visit_file_mut(&mut ast);
        quote!(#ast).to_string()
    }

    fn assert_normalized_eq(actual: &str, expected: &str) {
        let actual_norm: String = actual.chars().filter(|c| !c.is_whitespace()).collect();
        let expected_norm: String = expected.chars().filter(|c| !c.is_whitespace()).collect();
        assert_eq!(
            actual_norm, expected_norm,
            "\nExpected(norm): {}\nActual(norm):   {}\n\nOriginal Actual:\n{}",
            expected_norm, actual_norm, actual
        );
    }

    // Category 1: Leaf Node (Model Strategy)

    #[test]
    fn test_leaf_node_basic() {
        let input = r#"
            ///@ lean model foo
            ///@ ensures |ret| ret = 42
            #[allow(unused_variables)]
            fn foo() -> i32 {
                unsafe { 0 }
            }
        "#;
        let expected = r#"
            #[doc = "@ lean model foo"]
            #[doc = "@ ensures |ret| ret = 42"]
            #[allow(unused_variables)]
            fn foo() -> i32 {
                loop {}
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_leaf_node_preconditions() {
        let input = r#"
            ///@ lean model safe_div(a b : u32)
            ///@ requires b > 0
            #[allow(unused_variables)]
            fn safe_div(a: u32, b: u32) -> u32 {
                unsafe { a / b }
            }
        "#;
        let expected = r#"
            #[doc = "@ lean model safe_div(a b : u32)"]
            #[doc = "@ requires b > 0"]
            #[allow(unused_variables)]
            fn safe_div(a: u32, b: u32) -> u32 {
                loop {}
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_raw_pointer_signatures() {
        let input = r#"
            ///@ lean model read(ptr : Type) ...
            #[allow(unused_variables)]
            fn read(ptr: *const u32) -> u32 {
                unsafe { *ptr }
            }
        "#;
        // Signature should keep *const u32
        let expected = r#"
            #[doc = "@ lean model read(ptr : Type) ..."]
            #[allow(unused_variables)]
            fn read(ptr: *const u32) -> u32 {
                loop {}
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    // Category 2: Intermediate Node (Unwrap Strategy)

    #[test]
    fn test_structural_unwrap() {
        let input = r#"
            unsafe fn wrapper() {
                unsafe { foo() }
            }
        "#;
        // Note: visitor transforms `unsafe { block }` -> `{ block }`
        let expected = r#"
            fn wrapper() {
                { foo() }
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_block_scoping() {
        let input = r#"
            fn main() {
                let x = 1;
                unsafe {
                    let x = 2;
                    use_val(x);
                }
                use_val(x);
            }
        "#;
        let expected = r#"
            fn main() {
                let x = 1;
                {
                    let x = 2;
                    use_val(x);
                }
                use_val(x);
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_expr_unsafe_block() {
        let input = r#"
            fn main() {
                let y = unsafe {
                    let z = 10;
                    z * 2
                };
            }
        "#;
        let expected = r#"
            fn main() {
                let y = {
                    let z = 10;
                    z * 2
                };
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    // Category 3: Complex Rust Features

    #[test]
    fn test_generics_preserved() {
        let input = r#"
            ///@ lean model ...
            #[allow(unused_variables)]
            fn cast<T: Copy>(x: *const T) -> T {
                unsafe { *x }
            }
        "#;
        let expected = r#"
            #[doc = "@ lean model ..."]
            #[allow(unused_variables)]
            fn cast <T: Copy> (x: *const T) -> T {
                loop {}
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_unsafe_trait_impl() {
        let input = r#"
            unsafe impl GlobalAlloc for MyAllocator { }
        "#;
        // Visitor is structural on Fn and Expr, usually ignores ItemImpl unless recurse
        // We only implemented visit_item_fn_mut and visit_expr_mut
        // Default visit_item_impl_mut recurses.
        // It shouldn't change `unsafe impl`.
        let expected = input;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_nested_unsafe() {
        let input = r#"
            fn nesting() {
                unsafe {
                    let ptr = 0 as *const i32;
                    unsafe { *ptr }
                }
            }
        "#;
        let expected = r#"
            fn nesting() {
                {
                    let ptr = 0 as *const i32;
                    { *ptr }
                }
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    // Category 4: Verification Logic (Proof Tests)

    #[test]
    fn test_verification_logic_positive() {
        let input = r#"
            ///@ lean model foo
            ///@ requires x > 0
            #[allow(unused_variables)]
            fn foo(x: i32) {
                unsafe {}
            }
        "#;
        let expected = r#"
            #[doc = "@ lean model foo"]
            #[doc = "@ requires x > 0"]
            #[allow(unused_variables)]
            fn foo(x: i32) {
                loop {}
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_verification_logic_negative() {
        // Obsolete test for Panic Shim logic.
        // We just ensure we generate the loop.
        let input = r#"
            ///@ lean model foo
            ///@ requires x > 0
            #[allow(unused_variables)]
            fn foo(x: i32) {
                unsafe {}
            }
        "#;
        let expected = r#"
            #[doc = "@ lean model foo"]
            #[doc = "@ requires x > 0"]
            #[allow(unused_variables)]
            fn foo(x: i32) {
                loop {}
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_wrong_precondition_trap() {
        let input = r#"
            ///@ lean model foo
            ///@ requires x == 10
            #[allow(unused_variables)]
            fn foo(x: i32) {
               unsafe {}
            }
        "#;
        let expected = r#"
            #[doc = "@ lean model foo"]
            #[doc = "@ requires x == 10"]
            #[allow(unused_variables)]
            fn foo(x: i32) {
                loop {}
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    // Category 5: Syntactic Edge Cases

    #[test]
    fn test_attributes_preserved() {
        let input = r#"
            fn main() {
                #[allow(unused_unsafe)]
                unsafe { }
            }
        "#;
        let expected = r#"
             fn main() {
                #[allow(unused_unsafe)]
                { }
            }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_doc_comments_preserved() {
        let input = r#"
            /// Doc comment
            unsafe fn foo() { }
        "#;
        // Unwrap strategy - quote expands doc comments to attributes
        let expected = r#"
            #[doc = " Doc comment"]
            fn foo() { }
        "#;
        assert_normalized_eq(&transform(input), expected);
    }

    #[test]
    fn test_macro_invoking_unsafe() {
        let input = r#"
            fn main() {
                my_unsafe_macro!();
            }
        "#;
        // Should be untouched
        assert_normalized_eq(&transform(input), input);
    }
}
