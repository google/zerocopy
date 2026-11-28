// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Lowers Rust-syntax Anneal specifications to `Spec.lean` and
//! `spec-closure.golden`.
//!
//! The surface language attaches to Rust code in two forms that share one
//! grammar: inert inline attributes (`#[cfg_attr(anneal, anneal::spec(...))]`)
//! and out-of-tree companion files (`anneal::external_spec! { ... }`). Both
//! lower deterministically to a declarative `Spec.lean` built on
//! `Trusted.Framework.MirEnvelopeSpec`, accompanied by `spec-closure.golden`,
//! which `cargo-anneal`'s `spec-preflight` and target audit check like any
//! hand-written specification. Nothing here is trusted: a lowering bug can
//! only produce a `Spec.lean` that reviewers read and the auditor checks.

pub mod ast;
pub mod check;
pub mod closure;
pub mod diag;
mod emit;
pub mod parse;

use std::collections::{BTreeMap, BTreeSet};

pub use closure::{CapturedBodySummary, CapturedProgramSummary, Scope};
pub use diag::{Diagnostic, SourceMap, SrcSpan};
pub use emit::Lowered;
use proc_macro2::Span;

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

/// The layout of the lowering's output.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Format {
    /// `Spec.lean` in namespace `Spec`, plus `spec_span_map.json` and
    /// `spec-closure.golden`.
    #[default]
    V1,
    /// One span-free Lean module, `Specs/<crate>/<claim>.lean`, in namespace
    /// `Specs.<crate>.<claim>`, plus `spec-closure.golden`. It records no Rust
    /// source positions, so edits elsewhere in the Rust file leave it
    /// unchanged.
    V2Module,
}

/// Which items to lower and how to write them.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Lower only these items (`rust-path-v1` paths without the scheme).
    pub targets: Vec<String>,
    /// Lower only the items whose claim ([`ast::SpecFn::claim_id`]) is this.
    pub claim: Option<String>,
    pub format: Format,
    /// The crate component of the `Format::V2Module` namespace.
    pub crate_slug: Option<String>,
    /// Verification scope recorded in `MirEnvelopeSpec.gaps` (defaults to
    /// [`Scope::Unit`]; must match `capture.scope` when `capture` is `Some`).
    pub scope: Scope,
    /// Optional `capture.json` summary used to synthesize default UB-freedom
    /// entries for unannotated safe callees and reject unannotated `unsafe`
    /// callees.
    pub capture: Option<CapturedProgramSummary>,
}

impl Options {
    fn selecting(&self) -> bool {
        !self.targets.is_empty() || self.claim.is_some()
    }

    /// Checks that the options are consistent, returning the Lean namespace
    /// the output is written in.
    pub fn validate(&self) -> Result<String, String> {
        self.validate_names().map(|(ns, _)| ns)
    }

    fn validate_names(&self) -> Result<(String, String), String> {
        if let Some(cap) = &self.capture {
            if !matches!(cap.mir_profile_version, 1 | 2) {
                return Err(format!(
                    "unsupported capture `mir_profile_version` {} (expected 1 or 2)",
                    cap.mir_profile_version
                ));
            }
            if cap.scope != self.scope {
                return Err(format!(
                    "`Options::scope` ({:?}) conflicts with capture JSON scope ({:?})",
                    self.scope, cap.scope
                ));
            }
        }
        match self.format {
            Format::V1 if self.crate_slug.is_some() => {
                Err("`--crate-slug` needs `--format v2-module`".into())
            }
            Format::V1 => {
                let ns = check::SPEC_NAMESPACE.to_string();
                Ok((ns.clone(), ns))
            }
            Format::V2Module => {
                let (Some(slug), Some(claim)) = (&self.crate_slug, &self.claim) else {
                    return Err("`--format v2-module` needs `--crate-slug` and `--claim`".into());
                };
                for (what, id) in [("crate slug", slug), ("claim", claim)] {
                    if !parse::is_claim_ident(id) {
                        return Err(format!(
                            "`{}` is not a valid {what} for `--format v2-module`: use 1 to 64 \
                             ASCII letters, digits, and `_`, starting with a letter, other than \
                             a reserved Lean or Anneal name (give the item an explicit \
                             `claim = \"...\"` if its derived claim is not valid)",
                            id.escape_debug()
                        ));
                    }
                }
                // Escaped in syntax so that the generated Lean parses whatever
                // keywords are declared, paired with the un-escaped Lean
                // module identifier used in `request.json` and `Name.toString`.
                Ok((
                    format!("{}.«{slug}».«{claim}»", check::SPECS_ROOT),
                    format!("{}.{slug}.{claim}", check::SPECS_ROOT),
                ))
            }
        }
    }
}

/// One specified item, as reported by [`list_targets`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetInfo {
    /// The item's `rust-path-v1` path, without the scheme.
    pub target: String,
    /// The claim the item belongs to.
    pub claim: String,
    /// The index of the [`Source`] that specifies it.
    pub file: usize,
    /// Whether it is specified in `anneal::external_spec!` (rather than by
    /// an inline attribute).
    pub external: bool,
}

/// Parses, checks, and lowers `sources` into one specification unit.
pub fn lower(sources: &[Source]) -> Result<Lowered, Vec<LowerError>> {
    lower_with(sources, &Options::default())
}

/// Lists every item `sources` specify, sorted by path; `sources` may specify
/// no items at all.
///
/// The sources are parsed and their items collected as [`lower`] would, with
/// the same file-level checks, duplicate-target check, and claim-collision
/// check, but clauses are not type-checked: that happens when the unit that
/// owns an item lowers it, with that unit's own helpers.
pub fn list_targets(sources: &[Source]) -> Result<Vec<TargetInfo>, Vec<LowerError>> {
    let (fns, _) = collect(sources)?;
    Ok(fns
        .iter()
        .map(|f| TargetInfo {
            target: f.path.clone(),
            claim: f.claim_id(),
            file: f.file,
            external: f.external,
        })
        .collect())
}

fn resolve_unannotated_callees(
    fns: &[(&ast::SpecFn, check::LoweredFn)],
    opts: &Options,
) -> Result<(Scope, Vec<CapturedBodySummary>), Vec<LowerError>> {
    let Some(cap) = &opts.capture else {
        return Ok((opts.scope, Vec::new()));
    };
    let annotated_ids: BTreeSet<String> =
        fns.iter().map(|(f, _)| format!("rust-path-v1::{}", f.path)).collect();
    let mut errors = Vec::new();
    let mut safe_callees = Vec::new();
    for body in &cap.bodies {
        if annotated_ids.contains(&body.identity) {
            continue;
        }
        if body.is_unsafe {
            let short = body.identity.strip_prefix("rust-path-v1::").unwrap_or(&body.identity);
            errors.push(LowerError {
                file: 0,
                diag: Diagnostic::new(
                    "E_ANNEAL_UNANNOTATED_UNSAFE_CALLEE",
                    Span::call_site(),
                    format!(
                        "captured `unsafe` body `{short}` has no `anneal::spec` contract; \
                         `unsafe` callees cannot receive an implicit contract"
                    ),
                )
                .help("add an explicit `#[cfg_attr(anneal, anneal::spec(...))]` or `external_spec!` entry"),
            });
        } else {
            safe_callees.push(body.clone());
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok((cap.scope, safe_callees))
}

/// Parses, checks, and lowers the items of `sources` that `opts` selects.
///
/// Every item is checked, selected or not, so a selection never hides an
/// error. When selecting, only the `#[anneal::pure]` helpers the selected
/// items reach are emitted; without a selection the output is exactly
/// [`lower`]'s.
pub fn lower_with(sources: &[Source], opts: &Options) -> Result<Lowered, Vec<LowerError>> {
    let (namespace, lean_module) = opts.validate_names().map_err(|msg| {
        vec![LowerError {
            file: 0,
            diag: Diagnostic::new("E_ANNEAL_INVALID_OPTIONS", Span::call_site(), msg),
        }]
    })?;
    let a = analyze(sources, &namespace)?;
    if a.fns.is_empty() {
        return Err(vec![LowerError {
            file: 0,
            diag: Diagnostic::new(
                "E_ANNEAL_EMPTY_UNIT",
                Span::call_site(),
                "no `anneal::spec` items were found",
            ),
        }]);
    }
    let module_path = match (&opts.format, &opts.crate_slug, &opts.claim) {
        (Format::V2Module, Some(slug), Some(claim)) => {
            Some(format!("{}/{slug}/{claim}.lean", check::SPECS_ROOT))
        }
        _ => None,
    };
    if !opts.selecting() {
        let helpers: Vec<_> =
            a.helper_bodies.iter().map(|(i, b)| (&a.helpers[*i], b.clone())).collect();
        let fns: Vec<_> = a.fns.iter().zip(a.lowered_fns).collect();
        let (eff_scope, safe_callees) = resolve_unannotated_callees(&fns, opts)?;
        return Ok(emit::emit(
            sources,
            &helpers,
            &fns,
            &safe_callees,
            opts.capture.as_ref(),
            eff_scope,
            &a.runtime,
            &namespace,
            &lean_module,
            module_path,
        ));
    }

    let selected = select(&a.fns, opts)?;
    // The helpers the selected items reach, directly or through other
    // helpers.
    let index: BTreeMap<&str, usize> =
        a.helpers.iter().enumerate().map(|(i, h)| (h.name.as_str(), i)).collect();
    let mut pending = Vec::new();
    for f in &selected {
        for c in &f.clauses {
            // Exhaustive, so that a new clause carrying an expression cannot
            // silently drop the helpers it calls.
            match &c.clause {
                ast::Clause::Requires(e)
                | ast::Clause::SafetyRequires(e)
                | ast::Clause::MaxSteps(e)
                | ast::Clause::Ensures { body: e, .. } => check::calls_in(e, &mut pending),
                ast::Clause::Effect(_)
                | ast::Clause::Target(_)
                | ast::Clause::Claim(_)
                | ast::Clause::Instantiate(_) => {}
            }
        }
    }
    let mut reached = vec![false; a.helpers.len()];
    while let Some(name) = pending.pop() {
        if let Some(&i) = index.get(name.as_str()) {
            if !std::mem::replace(&mut reached[i], true) {
                check::calls_in(&a.helpers[i].body, &mut pending);
            }
        }
    }
    // Lower the selection again with fresh `Uses`, so the runtime
    // definitions emitted are exactly the ones the selection references.
    let mut errors = Vec::new();
    let runtime = check::Uses::default();
    let mut helper_bodies = Vec::new();
    for &i in a.order.iter().filter(|&&i| reached[i]) {
        let h = &a.helpers[i];
        match check::lower_helper(h, &a.sigs, &runtime) {
            Ok(body) => helper_bodies.push((h, body)),
            Err(d) => errors.push(LowerError { file: h.file, diag: d }),
        }
    }
    let mut lowered_fns = Vec::new();
    for f in selected {
        match check::lower_fn(f, &a.sigs, &runtime) {
            Ok(l) => lowered_fns.push((f, l)),
            Err(ds) => errors.extend(ds.into_iter().map(|d| LowerError { file: f.file, diag: d })),
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let (eff_scope, safe_callees) = resolve_unannotated_callees(&lowered_fns, opts)?;
    Ok(emit::emit(
        sources,
        &helper_bodies,
        &lowered_fns,
        &safe_callees,
        opts.capture.as_ref(),
        eff_scope,
        &runtime,
        &namespace,
        &lean_module,
        module_path,
    ))
}

/// The items `opts` selects from `fns`, in `fns`' order.
fn select<'a>(
    fns: &'a [ast::SpecFn],
    opts: &Options,
) -> Result<Vec<&'a ast::SpecFn>, Vec<LowerError>> {
    let err = |code: &'static str, msg: String| LowerError {
        file: 0,
        diag: Diagnostic::new(code, Span::call_site(), msg),
    };
    let mut errors = Vec::new();
    for t in &opts.targets {
        match fns.iter().find(|f| &f.path == t) {
            None => errors.push(err("E_ANNEAL_UNKNOWN_TARGET", format!("no item specifies `{t}`"))),
            Some(f) => {
                if let Some(c) = opts.claim.as_ref().filter(|c| **c != f.claim_id()) {
                    errors.push(err(
                        "E_ANNEAL_UNKNOWN_TARGET",
                        format!("`{t}` belongs to claim `{}`, not `{c}`", f.claim_id()),
                    ));
                }
            }
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let selected: Vec<_> = fns
        .iter()
        .filter(|f| opts.targets.is_empty() || opts.targets.contains(&f.path))
        .filter(|f| opts.claim.as_ref().is_none_or(|c| *c == f.claim_id()))
        .collect();
    if selected.is_empty() {
        let c = opts.claim.as_deref().unwrap_or_default();
        return Err(vec![err("E_ANNEAL_EMPTY_CLAIM", format!("no item belongs to claim `{c}`"))]);
    }
    Ok(selected)
}

/// Every item and helper of a set of sources, checked and lowered.
struct Analysis {
    /// Sorted by name.
    helpers: Vec<ast::PureFn>,
    /// Indices into `helpers`, each after the helpers it calls.
    order: Vec<usize>,
    sigs: BTreeMap<String, check::HelperSig>,
    /// `(index into helpers, body)` in `order`.
    helper_bodies: Vec<(usize, String)>,
    /// Sorted by path.
    fns: Vec<ast::SpecFn>,
    /// Parallel to `fns`.
    lowered_fns: Vec<check::LoweredFn>,
    runtime: check::Uses,
}

/// Parses `sources` and collects their items (sorted by path) and helpers,
/// rejecting file-level misuse, duplicate targets, and colliding claims.
fn collect(sources: &[Source]) -> Result<(Vec<ast::SpecFn>, Vec<ast::PureFn>), Vec<LowerError>> {
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
        let stream: proc_macro2::TokenStream = src.text.parse().expect("parsed by syn above");
        for span in parse::cfg_anneal_misuse(stream.clone()) {
            let diag = Diagnostic::new(
                "E_ANNEAL_BARE_OR_COMPOUND_CFG",
                span,
                "the `anneal` cfg may only enable `anneal::` specification attributes, and the \
                 identifier `anneal` is reserved for that use",
            )
            .help(
                "write `#[cfg_attr(anneal, anneal::spec(..))]`, `#[cfg_attr(anneal, \
                 anneal::pure)]`, or `#[cfg_attr(anneal, anneal::vacuous_ok(..))]`; code that \
                 is compiled only under `anneal` would make the specified crate differ from \
                 the built one",
            );
            errors.push(LowerError { file: i, diag });
        }
        let mut c = parse::Collected::default();
        if let Err(d) = parse::collect_items(&file.items, &src.module, &mut c) {
            errors.push(LowerError { file: i, diag: d });
            continue;
        }
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
    if !errors.is_empty() {
        return Err(errors);
    }
    // A derived claim names one item, so it may not coincide with another
    // item's derived claim (`a::b` and `a__b`) or with an explicit claim.
    let mut claims: BTreeMap<String, (Vec<&ast::SpecFn>, bool)> = BTreeMap::new();
    for f in &fns {
        let entry = claims.entry(f.claim_id()).or_default();
        if f.claim.is_some() {
            entry.1 = true;
        } else {
            entry.0.push(f);
        }
    }
    for (claim, (derived, explicit)) in &claims {
        if derived.len() + usize::from(*explicit) > 1 {
            for f in derived {
                errors.push(LowerError {
                    file: f.file,
                    diag: Diagnostic::new(
                        "E_ANNEAL_CLAIM_COLLISION",
                        f.sig_span,
                        format!(
                            "the claim `{claim}` derived from `{}` is also the claim of another \
                             item",
                            f.path
                        ),
                    )
                    .help("give the item an explicit `claim = \"...\"`"),
                });
            }
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok((fns, helpers))
}

/// Parses and checks every item of `sources`, lowering helper references
/// into `namespace`.
fn analyze(sources: &[Source], namespace: &str) -> Result<Analysis, Vec<LowerError>> {
    let (fns, mut helpers) = collect(sources)?;
    let mut errors = Vec::new();

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
                lean_name: check::helper_lean_name(namespace, &h.name),
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
    for &idx in &order {
        let h = &helpers[idx];
        match check::lower_helper(h, &sigs, &runtime) {
            Ok(body) => helper_bodies.push((idx, body)),
            Err(d) => errors.push(LowerError { file: h.file, diag: d }),
        }
    }

    let mut lowered_fns = Vec::new();
    for f in &fns {
        match check::lower_fn(f, &sigs, &runtime) {
            Ok(l) => lowered_fns.push(l),
            Err(ds) => errors.extend(ds.into_iter().map(|d| LowerError { file: f.file, diag: d })),
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Analysis { helpers, order, sigs, helper_bodies, fns, lowered_fns, runtime })
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
