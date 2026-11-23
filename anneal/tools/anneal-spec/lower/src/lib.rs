// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Lowers Rust-syntax Anneal specifications to `Spec.lean`.
//!
//! The surface language attaches to Rust code in two forms that share one
//! grammar: inert inline attributes (`#[cfg_attr(anneal, anneal::spec(...))]`)
//! and out-of-tree companion files (`anneal::external_spec! { ... }`). Both
//! lower deterministically to a declarative `Spec.lean` built on
//! `Trusted.MirSemantics.Contract` (`FnContract`, `ContractSpecs`), which
//! `cargo-anneal`'s `spec-preflight` and target audit then check like any
//! hand-written specification. Nothing here is trusted: a lowering bug can
//! only produce a `Spec.lean` that reviewers read and the auditor checks.

pub mod ast;
pub mod check;
pub mod diag;
mod emit;
pub mod parse;

use std::collections::BTreeMap;

pub use diag::{Diagnostic, SourceMap, SrcSpan};
pub use emit::Lowered;

/// One Rust input file.
pub struct Source {
    /// The path recorded in diagnostics and `spec_span_map.json`.
    pub label: String,
    pub text: String,
    /// The module path of the file within its crate (empty for the crate
    /// root or for companion files that only contain `external_spec!`).
    pub module: Vec<String>,
}

/// A diagnostic and the index of the [`Source`] it refers to.
pub struct LowerError {
    pub file: usize,
    pub diag: Diagnostic,
}

impl LowerError {
    pub fn render(&self, sources: &[Source]) -> String {
        let src = &sources[self.file];
        self.diag.render(&src.label, &SourceMap::new(&src.text))
    }
}

/// Derives a module path from a source path relative to the crate's `src/`
/// directory, following Rust's file layout (`a/b.rs` and `a/b/mod.rs` are
/// `a::b`; `lib.rs` and `main.rs` are the root).
pub fn module_path(rel: &str) -> Vec<String> {
    let rel = rel.strip_suffix(".rs").unwrap_or(rel);
    let mut parts: Vec<String> =
        rel.split('/').filter(|p| !p.is_empty()).map(String::from).collect();
    if parts.len() == 1 && (parts[0] == "lib" || parts[0] == "main") {
        parts.clear();
    }
    if parts.last().is_some_and(|p| p == "mod") {
        parts.pop();
    }
    parts
}

/// Parses, checks, and lowers `sources` into one specification unit.
pub fn lower(sources: &[Source]) -> Result<Lowered, Vec<LowerError>> {
    let mut errors = Vec::new();
    let mut fns = Vec::new();
    let mut helpers = Vec::new();
    for (i, src) in sources.iter().enumerate() {
        let file = match syn::parse_file(&src.text) {
            Ok(f) => f,
            Err(e) => {
                errors.push(LowerError { file: i, diag: e.into() });
                continue;
            }
        };
        let mut c = parse::Collected::default();
        if let Err(d) = parse::collect_items(&file.items, &src.module, &mut c) {
            errors.push(LowerError { file: i, diag: d });
            continue;
        }
        let stream: proc_macro2::TokenStream = src.text.parse().expect("parsed by syn above");
        for (span, code) in parse::ignored_anneal_paths(stream, &c.handled) {
            let diag = if code == "E_ANNEAL_UNSUPPORTED_IMPORT" {
                Diagnostic::new(code, span, "importing or renaming `anneal` is not supported")
                    .help("write attributes with their full `anneal::` path")
            } else {
                Diagnostic::new(
                    code,
                    span,
                    "this `anneal::` item is not in a position `anneal-spec-lower` reads",
                )
                .help(
                    "write `#[anneal::...]` or `#[cfg_attr(anneal, anneal::...)]` on a free \
                     function or impl method, and `anneal::external_spec!` at module level",
                )
            };
            errors.push(LowerError { file: i, diag });
        }
        fns.extend(c.fns.into_iter().map(|mut f| {
            f.file = i;
            f
        }));
        helpers.extend(c.helpers.into_iter().map(|mut h| {
            h.file = i;
            h
        }));
    }
    if !errors.is_empty() {
        return Err(errors);
    }

    // Helper signatures, duplicate names, and a call-graph order that puts
    // every helper after the helpers it calls.
    let mut sigs = BTreeMap::new();
    for h in &helpers {
        if sigs.contains_key(&h.name) {
            errors.push(LowerError {
                file: h.file,
                diag: Diagnostic::new(
                    "E_ANNEAL_DUPLICATE_HELPER",
                    h.span,
                    format!("`#[anneal::pure]` helper `{}` is defined twice", h.name),
                ),
            });
            continue;
        }
        sigs.insert(
            h.name.clone(),
            check::HelperSig {
                lean_name: check::helper_lean_name(&h.name),
                params: h.params.iter().map(|p| p.ty).collect(),
                ret: h.ret,
            },
        );
    }
    helpers.sort_by(|a, b| a.name.cmp(&b.name));
    let order = match helper_order(&helpers) {
        Ok(o) => o,
        Err(e) => {
            errors.push(e);
            return Err(errors);
        }
    };
    let runtime = check::Uses::default();
    let mut helper_bodies = Vec::new();
    for idx in order {
        let h = &helpers[idx];
        match check::lower_helper(h, &sigs, &runtime) {
            Ok(body) => helper_bodies.push((h, body)),
            Err(d) => errors.push(LowerError { file: h.file, diag: d }),
        }
    }

    fns.sort_by(|a, b| a.path.cmp(&b.path));
    for w in fns.windows(2) {
        if w[0].path == w[1].path {
            errors.push(LowerError {
                file: w[1].file,
                diag: Diagnostic::new(
                    "E_ANNEAL_DUPLICATE_TARGET",
                    w[1].sig_span,
                    format!("`{}` is specified more than once", w[1].path),
                ),
            });
        }
    }
    if fns.is_empty() {
        errors.push(LowerError {
            file: 0,
            diag: Diagnostic::new(
                "E_ANNEAL_EMPTY_UNIT",
                proc_macro2::Span::call_site(),
                "no `anneal::spec` items were found",
            ),
        });
    }
    let mut lowered_fns = Vec::new();
    for f in &fns {
        match check::lower_fn(f, &sigs, &runtime) {
            Ok(l) => lowered_fns.push((f, l)),
            Err(ds) => errors.extend(ds.into_iter().map(|d| LowerError { file: f.file, diag: d })),
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(emit::emit(sources, &helper_bodies, &lowered_fns, &runtime))
}

fn helper_order(helpers: &[ast::PureFn]) -> Result<Vec<usize>, LowerError> {
    let index: BTreeMap<&str, usize> =
        helpers.iter().enumerate().map(|(i, h)| (h.name.as_str(), i)).collect();
    // 0 = unvisited, 1 = on the current path, 2 = done.
    let mut state = vec![0u8; helpers.len()];
    let mut order = Vec::new();
    fn visit(
        i: usize,
        helpers: &[ast::PureFn],
        index: &BTreeMap<&str, usize>,
        state: &mut [u8],
        order: &mut Vec<usize>,
    ) -> Result<(), LowerError> {
        match state[i] {
            2 => return Ok(()),
            1 => {
                return Err(LowerError {
                    file: helpers[i].file,
                    diag: Diagnostic::new(
                        "E_ANNEAL_PURE_RECURSION",
                        helpers[i].span,
                        format!("`#[anneal::pure]` helper `{}` is recursive", helpers[i].name),
                    )
                    .help("profile v1 helpers must not call themselves, directly or indirectly"),
                })
            }
            _ => {}
        }
        state[i] = 1;
        let mut calls = Vec::new();
        check::calls_in(&helpers[i].body, &mut calls);
        calls.sort();
        calls.dedup();
        for c in calls {
            if let Some(&j) = index.get(c.as_str()) {
                visit(j, helpers, index, state, order)?;
            }
        }
        state[i] = 2;
        order.push(i);
        Ok(())
    }
    for i in 0..helpers.len() {
        visit(i, helpers, &index, &mut state, &mut order)?;
    }
    Ok(order)
}
