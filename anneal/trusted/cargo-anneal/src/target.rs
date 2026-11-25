// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact-root acceptance for an external, source-authenticated proof workspace.
//!
//! The trusted runner owns Model, Capture, Specification, and Expected inputs.
//! Only Proof sources and the submitted theorem name come from the proof
//! producer. This API does not establish that a caller's chosen model or
//! specification matches human intent. It authenticates those choices and
//! checks their separation from the unreviewed proof implementation.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs, io,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use serde_json::json;

use crate::{
    sandbox::set_mode,
    stage::Checker,
    toolchain::{
        AdmittedToolchain, Failure, ImportEdge, Json, PreflightResult, TOOLCHAIN,
        collect_pinned_sysroot_module_artifacts, compute_unpinned_foundation_closure,
        default_compile_workers, hash_unpinned_sysroot_module, is_allowed_pinned_library_module,
        is_allowed_unpinned_sysroot_module, is_lean_ident, is_sha256_hex, sha256_bytes,
        sha256_file, sha256_file_deref, stage_regular_file, topo_sort_modules,
        validate_pinned_library_graph,
    },
};

/// Module root namespaces reserved for the Lean toolchain and inspector in both
/// pinned and unpinned modes.
///
/// Reserving these roots prevents authored target modules from claiming names
/// such as `Init.System.IO`, `Lean.Elab`, or `TrustedBoundary` that would
/// shadow sysroot or inspector modules in exported `LEAN_PATH` directories.
const RESERVED_TOOLCHAIN_MODULE_ROOTS: &[&str] =
    &["Init", "Std", "Lean", "Lake", "TrustedBoundary"];

/// Return whether `module` belongs to a reserved toolchain or inspector root.
fn is_reserved_toolchain_module(module: &str) -> bool {
    let root_pkg = module.split('.').next().unwrap_or("");
    RESERVED_TOOLCHAIN_MODULE_ROOTS.contains(&root_pkg)
}

/// The authority of a source module in a target verification request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum TargetRole {
    /// Installed primitive semantics and the canonical verification roots.
    Model,
    /// Reviewed mathematical specifications and their authored helpers.
    Specification,
    /// Runner-generated, closed captured program data.
    Capture,
    /// Runner-generated expected proposition, independent of proof sources.
    Expected,
    /// Authored proofs, checked theory, tactics, and other proof libraries.
    Proof,
}

impl TargetRole {
    /// Proofs may depend on reviewed inputs, but the reverse direction would
    /// let an unreviewed helper redefine the claim. Check this relation before
    /// elaboration and again over actual compiled declaration edges: an import
    /// graph alone cannot establish every dependency's origin. Changes must
    /// preserve both enforcement points.
    pub fn allows(self, other: Self) -> bool {
        match self {
            Self::Model => other == Self::Model,
            Self::Capture => matches!(other, Self::Model | Self::Capture),
            Self::Specification => matches!(other, Self::Model | Self::Specification),
            Self::Expected => other != Self::Proof,
            Self::Proof => true,
        }
    }
}

/// Represents a read-only source input, authenticated before private staging.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TargetModule {
    /// Names the module in the ASCII dotted-name protocol of
    /// [`TargetAuditRequest`].
    pub module: String,
    /// Names the host path used only for source admission and private staging.
    /// The inspector receives compiled artifacts, not this original path.
    pub source: PathBuf,
    /// Holds the hex SHA-256 digest that the source bytes must match both
    /// before staging and again after elaboration.
    pub expected_sha256: String,
    /// Assigns the module's authority; see [`TargetRole::allows`].
    pub role: TargetRole,
}

/// Independently established subject identities reported with acceptance.
///
/// The runner must compute these from the actual configured request, capture,
/// and reviewed manifests. Lean definitional equality cannot authenticate
/// metadata that the mathematical proposition does not inspect.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TargetBindings {
    /// Holds the hex SHA-256 digest of the configured verification request.
    pub request_sha256: String,
    /// Holds the hex SHA-256 digest of the captured program data.
    pub capture_sha256: String,
    /// Holds the hex SHA-256 digest of the installed model manifest.
    pub model_manifest_sha256: String,
    /// Holds the hex SHA-256 digest of the reviewed specification manifest.
    pub specification_manifest_sha256: String,
}

/// Trusted-runner request for an exact, closed target theorem.
///
/// Expected must name a runner-generated definition of type Prop. The caller
/// must obtain Model hashes from its installed package and Specification hashes
/// from its reviewed request, rather than accepting either from proof code.
/// Adjacent caller `.olean` files are never loaded; every listed source is
/// copied into a fresh private stage and compiled against explicit artifacts.
///
/// Module and selected declaration labels currently use nonempty dot-separated
/// components, each starting with an ASCII letter and continuing with ASCII
/// letters, digits, or underscores. This is a bounded wire protocol, not Lean's
/// identifier grammar. Helpers in the authored Lean source can use ordinary
/// Unicode and apostrophe identifiers; expose an ASCII root alias to select
/// such a proof. General Lean surface syntax and escaped-name transport remain
/// outside this protocol. Frontends that generate Lean source have their own
/// source-rendering obligations; accepting a name as data does not quote it.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TargetAuditRequest {
    /// Lists every source module with its expected digest and role.
    pub modules: Vec<TargetModule>,
    /// Names the `Proof` module that defines `theorem_name`.
    pub theorem_module: String,
    /// Names the submitted theorem, whose type must be definitionally equal to
    /// the canonical root application.
    pub theorem_name: String,
    /// Names the `Expected` module that defines `expected_declaration`.
    pub expected_module: String,
    /// Names the runner-generated `Prop` definition of the expected claim.
    pub expected_declaration: String,
    /// Fixed model root, independent of parsing the Expected source.
    pub canonical_root: String,
    /// Exact runner-generated subject declaration.
    pub subject_declaration: String,
    /// Exact reviewed specification declaration.
    pub specification_declaration: String,
    /// When `true`, Phase 2 of `"target-audit"` admits `sorryAx` strictly on
    /// outgoing edges from `TargetRole::Proof` declarations outside the
    /// Phase 1 claim/specification closure, reporting them in
    /// `"sorryDeclarations"`. Phase 1 always enforces the strict 3-axiom
    /// ceiling.
    #[serde(default)]
    pub allow_sorry_in_proof: bool,
    /// Holds the subject identities reported with acceptance.
    pub bindings: TargetBindings,
}

// Module routing and selected declaration labels deliberately share the
// documented protocol above. Do not mistake this bounded profile for Lean's
// general naming rules or apply it to helper declarations inside source files.
fn target_name_valid(name: &str) -> bool {
    !name.is_empty() && name.split('.').all(is_lean_ident)
}

/// Return whether `module` belongs to the bundled `Anneal` theory namespace
/// (`Anneal` or `Anneal.*`), which authored proof modules are forbidden from
/// naming via `reserved_proof_module`.
pub(crate) fn is_bundled_theory_module(module: &str) -> bool {
    module == "Anneal" || module.starts_with("Anneal.")
}

/// Foundation modules that bundled `Anneal.*` `module`-system theory files may
/// open via `import all` (mirroring `TrustedBoundary.allowedTheoryImportAllModules`).
const ALLOWED_THEORY_IMPORT_ALL_MODULES: &[&str] = &["Init.Data.Nat.Bitwise.Basic"];

/// Compute the deterministic BFS set of target modules to retain for
/// compilation and auditing.
///
/// Every non-bundled-theory module (`Model`, `Capture`, `Specification`,
/// `Expected`, and authored `Proof` modules, plus `request.theorem_module`)
/// seeds the traversal. Bundled `Anneal.*` `Proof` modules are retained only
/// when reachable via parsed `imports` edges from those seeds, preserving
/// role-violation checks such as `Specification -> Anneal.*` while skipping
/// compilation and provenance of unused bundled theory libraries.
fn reachable_target_modules(
    request: &TargetAuditRequest,
    imports: &BTreeMap<String, Vec<ImportEdge>>,
) -> BTreeSet<String> {
    let staged_names: BTreeSet<&str> = request.modules.iter().map(|m| m.module.as_str()).collect();
    let mut retained = BTreeSet::new();
    let mut queue = VecDeque::new();
    for module in &request.modules {
        let is_seed = module.role != TargetRole::Proof
            || !is_bundled_theory_module(&module.module)
            || module.module == request.theorem_module;
        if is_seed && retained.insert(module.module.clone()) {
            queue.push_back(module.module.clone());
        }
    }
    while let Some(current) = queue.pop_front() {
        if let Some(edges) = imports.get(&current) {
            for edge in edges {
                if staged_names.contains(edge.module.as_str())
                    && retained.insert(edge.module.clone())
                {
                    queue.push_back(edge.module.clone());
                }
            }
        }
    }
    retained
}

/// Inspector data excludes original host paths: Lean uses compiled artifacts
/// and authority labels after Rust has authenticated and staged the sources.
/// Keep the hashes and bindings unchanged, but do not make a native source path
/// pass through JSON text encoding merely to audit its compiled declarations.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct InspectorTargetAuditRequest<'a> {
    modules: Vec<InspectorTargetModule<'a>>,
    theorem_module: &'a str,
    theorem_name: &'a str,
    expected_module: &'a str,
    expected_declaration: &'a str,
    canonical_root: &'a str,
    subject_declaration: &'a str,
    specification_declaration: &'a str,
    allow_sorry_in_proof: bool,
    bindings: &'a TargetBindings,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct InspectorTargetModule<'a> {
    module: &'a str,
    expected_sha256: &'a str,
    role: TargetRole,
    is_module: bool,
}

impl<'a> InspectorTargetAuditRequest<'a> {
    fn from_request_and_modes(
        request: &'a TargetAuditRequest,
        is_modules: &BTreeMap<String, bool>,
    ) -> Result<Self, Failure> {
        let mut modules = Vec::with_capacity(request.modules.len());
        for module in &request.modules {
            let is_module = is_modules.get(&module.module).copied().ok_or_else(|| {
                Failure::operational(
                    "target-audit",
                    format!("missing isModule expectation for {}", module.module),
                )
            })?;
            modules.push(InspectorTargetModule {
                module: &module.module,
                expected_sha256: &module.expected_sha256,
                role: module.role,
                is_module,
            });
        }
        Ok(Self {
            modules,
            theorem_module: &request.theorem_module,
            theorem_name: &request.theorem_name,
            expected_module: &request.expected_module,
            expected_declaration: &request.expected_declaration,
            canonical_root: &request.canonical_root,
            subject_declaration: &request.subject_declaration,
            specification_declaration: &request.specification_declaration,
            allow_sorry_in_proof: request.allow_sorry_in_proof,
            bindings: &request.bindings,
        })
    }
}

impl Checker {
    /// Discover source imports via `"headers"` mode without elaborating
    /// commands.
    #[doc(hidden)]
    pub fn inspect_headers(&mut self, sources: &[(String, PathBuf)]) -> Result<Json, Failure> {
        let req = {
            let adm = self.admitted()?;
            json!({
                "mode": "headers",
                "sysroot": adm.prefix.to_string_lossy(),
                "foundation": adm.foundation_modules(),
                "sources": sources,
            })
        };
        self.invoke_inspector("headers", &req)
    }

    /// Run batched fail-closed `"spec-preflight"` across
    /// `TargetRole::Specification` sources against the authenticated `Init` +
    /// `Std` parser environment (zero target `.olean`s loaded).
    #[doc(hidden)]
    pub fn inspect_spec_preflight(
        &mut self,
        sources: &[(String, PathBuf)],
    ) -> Result<Json, Failure> {
        self.inspect_spec_preflight_with_closures(sources, None, None)
    }

    fn inspect_spec_preflight_with_closures(
        &mut self,
        sources: &[(String, PathBuf)],
        allowed_foundation: Option<&BTreeSet<String>>,
        allowed_libraries: Option<&BTreeSet<String>>,
    ) -> Result<Json, Failure> {
        let req = {
            let adm = self.admitted()?;
            let lib_set = allowed_libraries.unwrap_or(&adm.library_modules);
            let in_fnd = |m: &String| {
                adm.foundation_graph.contains_key(m)
                    && allowed_foundation.is_none_or(|fnd_set| fnd_set.contains(m))
            };
            let in_lib = |m: &String| lib_set.contains(m) && adm.library_modules.contains(m);
            let arts_arr: Vec<Json> = adm
                .artifacts
                .iter()
                .filter(|(k, _)| in_fnd(k) || in_lib(k))
                .map(|(k, parts)| json!([k, parts.to_wire()]))
                .collect();
            let foundation: Vec<&str> =
                adm.foundation_graph.keys().filter(|m| in_fnd(m)).map(String::as_str).collect();
            let libraries: Vec<&str> = lib_set
                .iter()
                .filter(|m| adm.library_modules.contains(*m))
                .map(String::as_str)
                .collect();
            let graph: BTreeMap<&str, &[ImportEdge]> = adm
                .graph
                .iter()
                .filter(|(k, _)| in_fnd(k) || in_lib(k))
                .map(|(k, v)| (k.as_str(), v.as_slice()))
                .collect();
            json!({
                "mode": "spec-preflight",
                "sysroot": adm.prefix.to_string_lossy(),
                "artifacts": arts_arr,
                "foundation": foundation,
                "libraries": libraries,
                "graph": graph,
                "sources": sources,
            })
        };
        self.invoke_inspector("spec-preflight", &req)
    }
}

/// Closed set of foundation axioms permitted in any `"target-audit"` report
/// (outside `--allow-sorry-in-proof`, which additionally permits `"sorryAx"`).
pub(crate) const ALLOWED_TARGET_FOUNDATION_AXIOMS: &[&str] =
    &["Classical.choice", "Quot.sound", "propext"];

/// Single declaration-to-module entry in a `"target-audit"` logical closure.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TargetClosureEntry {
    name: String,
    module: String,
}

/// Single advisory anti-vacuity warning emitted by `"target-audit"`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TargetSpecWarning {
    code: String,
    declaration: String,
    message: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    body: Option<String>,
}

/// Closed set of anti-vacuity lint warning codes emitted by `"target-audit"`.
const VALID_SPEC_WARNING_CODES: &[&str] =
    &["unsatisfiable_safety", "trivial_property", "unused_spec_binding"];

/// Strict typed schema for the `"result"` payload emitted by `"target-audit"`.
///
/// Deserializing directly into this `#[serde(deny_unknown_fields)]` struct and
/// validating every field against the authenticated [`TargetAuditRequest`] and
/// admitted import graph prevents a malformed, truncated, or tampered audit
/// payload from being accepted by `cargo-anneal`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TargetAuditReport {
    theorem: String,
    canonical_root: String,
    subject: String,
    specification: String,
    graph: BTreeMap<String, Vec<ImportEdge>>,
    expected: String,
    axioms: Vec<String>,
    sorry_declarations: Vec<String>,
    replay: bool,
    exact_type: bool,
    replayed_declarations: u64,
    checked_alternate_proofs: u64,
    subject_closure: Vec<TargetClosureEntry>,
    model_closure: Vec<TargetClosureEntry>,
    specification_closure: Vec<TargetClosureEntry>,
    #[serde(default)]
    spec_warnings: Vec<TargetSpecWarning>,
}

/// Validate every invariant of a deserialized [`TargetAuditReport`] against
/// `request` and the admitted module import graph `expected_graph`.
fn validate_target_audit_report(
    report: &TargetAuditReport,
    request: &TargetAuditRequest,
    expected_graph: &BTreeMap<String, Vec<ImportEdge>>,
) -> Result<(), Failure> {
    if report.theorem != request.theorem_name {
        return Err(Failure::operational(
            "target-audit",
            format!(
                "target-audit theorem mismatch: expected {}, got {}",
                request.theorem_name, report.theorem
            ),
        ));
    }
    if report.expected != request.expected_declaration {
        return Err(Failure::operational(
            "target-audit",
            format!(
                "target-audit expected declaration mismatch: expected {}, got {}",
                request.expected_declaration, report.expected
            ),
        ));
    }
    if report.canonical_root != request.canonical_root {
        return Err(Failure::operational(
            "target-audit",
            format!(
                "target-audit canonicalRoot mismatch: expected {}, got {}",
                request.canonical_root, report.canonical_root
            ),
        ));
    }
    if report.subject != request.subject_declaration {
        return Err(Failure::operational(
            "target-audit",
            format!(
                "target-audit subject mismatch: expected {}, got {}",
                request.subject_declaration, report.subject
            ),
        ));
    }
    if report.specification != request.specification_declaration {
        return Err(Failure::operational(
            "target-audit",
            format!(
                "target-audit specification mismatch: expected {}, got {}",
                request.specification_declaration, report.specification
            ),
        ));
    }
    if !report.replay || !report.exact_type {
        return Err(Failure::operational(
            "target-audit",
            format!(
                "target-audit did not certify replay and exactType (replay={}, exactType={})",
                report.replay, report.exact_type
            ),
        ));
    }
    if report.replayed_declarations == 0 {
        return Err(Failure::operational(
            "target-audit",
            "target-audit reported zero replayed declarations",
        ));
    }
    if &report.graph != expected_graph {
        return Err(Failure::operational(
            "target-audit",
            "target-audit reported import graph differing from admitted DAG",
        ));
    }
    for (label, closure) in [
        ("subjectClosure", &report.subject_closure),
        ("modelClosure", &report.model_closure),
        ("specificationClosure", &report.specification_closure),
    ] {
        if closure.is_empty() {
            return Err(Failure::operational(
                "target-audit",
                format!("target-audit reported empty {label}"),
            ));
        }
        for entry in closure {
            if entry.name.is_empty() || entry.module.is_empty() {
                return Err(Failure::operational(
                    "target-audit",
                    format!("target-audit reported malformed entry in {label}"),
                ));
            }
        }
    }
    let mut seen_axioms = BTreeSet::new();
    let mut uses_sorry_ax = false;
    for ax in &report.axioms {
        if !seen_axioms.insert(ax.as_str()) {
            return Err(Failure::operational(
                "target-audit",
                format!("target-audit reported duplicate axiom {ax}"),
            ));
        }
        if ax == "sorryAx" {
            if !request.allow_sorry_in_proof {
                return Err(Failure::operational(
                    "target-audit",
                    "target-audit reported sorryAx without allow_sorry_in_proof",
                ));
            }
            uses_sorry_ax = true;
        } else if !ALLOWED_TARGET_FOUNDATION_AXIOMS.contains(&ax.as_str()) {
            return Err(Failure::operational(
                "target-audit",
                format!("target-audit reported axiom outside closed allowlist: {ax}"),
            ));
        }
    }
    if report.sorry_declarations.iter().any(String::is_empty) {
        return Err(Failure::operational(
            "target-audit",
            "target-audit reported empty declaration name in sorryDeclarations",
        ));
    }
    if request.allow_sorry_in_proof {
        if uses_sorry_ax != !report.sorry_declarations.is_empty() {
            return Err(Failure::operational(
                "target-audit",
                "target-audit mismatch between sorryAx axiom and sorryDeclarations",
            ));
        }
    } else if !report.sorry_declarations.is_empty() {
        return Err(Failure::operational(
            "target-audit",
            "target-audit reported non-empty sorryDeclarations without allow_sorry_in_proof",
        ));
    }
    for warning in &report.spec_warnings {
        if !VALID_SPEC_WARNING_CODES.contains(&warning.code.as_str()) {
            return Err(Failure::operational(
                "target-audit",
                format!("target-audit reported unknown specWarnings code `{}`", warning.code),
            ));
        }
        if warning.declaration.is_empty() || warning.message.is_empty() {
            return Err(Failure::operational(
                "target-audit",
                "target-audit reported malformed specWarnings entry with empty declaration/message",
            ));
        }
        if warning.body.as_deref().is_some_and(str::is_empty) {
            return Err(Failure::operational(
                "target-audit",
                "target-audit reported malformed specWarnings entry with empty body label",
            ));
        }
    }
    Ok(())
}

/// Run `"target-export"` (isolated proof-artifact export) followed by
/// `"target-audit"` (verdict-producing replay with zero `Proof` `.olean`s
/// mounted or imported) and validate the strict [`TargetAuditReport`] schema.
impl Checker {
    /// Run `"target-audit"` mode over compiled target artifacts, deriving
    /// `isModule` expectations from the target source headers on disk.
    #[doc(hidden)]
    pub fn inspect_target(&mut self, request: &TargetAuditRequest) -> Result<Json, Failure> {
        let mut is_modules = BTreeMap::new();
        for module in &request.modules {
            let source = fs::read(&module.source).map_err(|e| {
                Failure::operational(
                    "target-audit",
                    format!("cannot read target source {}: {e}", module.source.display()),
                )
            })?;
            is_modules.insert(
                module.module.clone(),
                crate::stage::source_starts_with_module_keyword(&source),
            );
        }
        self.inspect_target_with_modes(request, &is_modules)
    }

    /// Run `"target-audit"` mode over compiled target artifacts with explicit
    /// per-module `isModule` expectations.
    #[doc(hidden)]
    pub fn inspect_target_with_modes(
        &mut self,
        request: &TargetAuditRequest,
        is_modules: &BTreeMap<String, bool>,
    ) -> Result<Json, Failure> {
        let proof_modules: BTreeSet<&str> = request
            .modules
            .iter()
            .filter(|m| m.role == TargetRole::Proof)
            .map(|m| m.module.as_str())
            .collect();
        let inspector_target =
            InspectorTargetAuditRequest::from_request_and_modes(request, is_modules)?;
        let (export_req, expected_graph) = {
            let adm = self.admitted()?;
            let arts_arr: Vec<Json> =
                adm.artifacts.iter().map(|(k, parts)| json!([k, parts.to_wire()])).collect();
            let libraries: Vec<&str> = adm.library_modules.iter().map(String::as_str).collect();
            (
                json!({
                    "mode": "target-export",
                    "sysroot": adm.prefix.to_string_lossy(),
                    "artifacts": arts_arr,
                    "foundation": adm.foundation_modules(),
                    "libraries": libraries,
                    "graph": &adm.graph,
                    "axioms": &adm.axioms,
                    "target": &inspector_target,
                }),
                adm.graph.clone(),
            )
        };
        // Step 1: Run `"target-export"` in its own isolated ExecSeal child
        // process with no write access to `"target-audit"`'s verdict file.
        // Map operational/policy errors back to the `"target-audit"` phase so
        // callers see a unified audit failure surface.
        let proof_export = self
            .invoke_inspector("target-export", &export_req)
            .map_err(|e| Failure::new(e.code, "target-audit", e.message))?;

        let export_run_id = self.next_counter();
        let proof_export_host = self.stage.join(format!("proof-export-{export_run_id:03}.json"));
        let export_bytes = serde_json::to_vec(&proof_export).map_err(|e| {
            Failure::operational("target-audit", format!("cannot serialize proof export: {e}"))
        })?;
        fs::write(&proof_export_host, export_bytes).map_err(|e| {
            Failure::operational(
                "target-audit",
                format!("cannot write {}: {e}", proof_export_host.display()),
            )
        })?;
        set_mode(&proof_export_host, 0o444)?;

        // Step 2: Run `"target-audit"` with ZERO `Proof` `.olean` artifacts in
        // either `artifacts` or its sandbox mount namespace.
        let audit_req = {
            let adm = self.admitted()?;
            let non_proof_arts: Vec<Json> = adm
                .artifacts
                .iter()
                .filter(|(k, _)| !proof_modules.contains(k.as_str()))
                .map(|(k, parts)| json!([k, parts.to_wire()]))
                .collect();
            let libraries: Vec<&str> = adm.library_modules.iter().map(String::as_str).collect();
            json!({
                "mode": "target-audit",
                "sysroot": adm.prefix.to_string_lossy(),
                "artifacts": non_proof_arts,
                "foundation": adm.foundation_modules(),
                "libraries": libraries,
                "graph": &adm.graph,
                "axioms": &adm.axioms,
                "proofExportPath": proof_export_host.to_string_lossy(),
                "target": &inspector_target,
            })
        };
        let typed_res: Result<TargetAuditReport, Failure> =
            self.invoke_inspector_typed("target-audit", &audit_req);
        let _ = set_mode(&proof_export_host, 0o600);
        let _ = fs::remove_file(&proof_export_host);
        let report = typed_res?;
        validate_target_audit_report(&report, request, &expected_graph)?;
        serde_json::to_value(&report).map_err(|e| {
            Failure::operational("target-audit", format!("cannot encode validated report: {e}"))
        })
    }
}

impl Checker {

    /// Authenticate the requested installed-library import closure.
    ///
    /// Library hashes pin their 4-tree sysroot contents without admitting their
    /// declarations as axioms. The inspector replays every logically reached
    /// declaration onto the foundation environment, verifies the 4-tree
    /// `library-lock.json` sysroot digests, resolves requested `Init.*`/`Std.*`
    /// imports dynamically via `"resolve-imports"`, and admits their transitive
    /// sysroot `.olean` artifacts and edges.
    pub(crate) fn admit_libraries(
        &mut self,
        roots: impl IntoIterator<Item = String>,
    ) -> Result<(), Failure> {
        let adm = self.admitted()?;
        let Some(lock) = adm.library_lock.clone() else {
            return Ok(());
        };
        let prefix = adm.prefix.clone();
        let foundation = adm.foundation_graph.clone();
        let already_admitted = adm.library_modules.clone();
        let mut resolve_roots = BTreeSet::new();
        for module in roots {
            if foundation.contains_key(&module) || already_admitted.contains(&module) {
                continue;
            }
            if !is_allowed_pinned_library_module(&module) {
                if module.starts_with("Init.") || module.starts_with("Std.") {
                    return Err(Failure::operational("library-lock", "invalid module record"));
                }
                continue;
            }
            let olean_path =
                prefix.join("lib/lean").join(format!("{}.olean", module.replace('.', "/")));
            match fs::symlink_metadata(&olean_path) {
                Ok(meta) => {
                    if meta.file_type().is_symlink() || !meta.file_type().is_file() {
                        continue;
                    }
                    resolve_roots.insert(module);
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => {
                    return Err(Failure::operational(
                        "library-lock",
                        format!("cannot inspect {}: {e}", olean_path.display()),
                    ));
                }
            }
        }
        if resolve_roots.is_empty() {
            return Ok(());
        }
        lock.verify_prefix(&prefix, "library-lock")?;
        let roots_vec: Vec<String> = resolve_roots.into_iter().collect();
        let resolved_graph = self.resolve_sysroot_imports(&roots_vec)?;
        validate_pinned_library_graph(&resolved_graph)?;
        for module in &roots_vec {
            if !resolved_graph.contains_key(module) {
                return Err(Failure::operational(
                    "resolve-imports",
                    format!("resolve-imports omitted requested root {module}"),
                ));
            }
        }
        for (module, edges) in &resolved_graph {
            if let Some(expected_edges) = foundation.get(module)
                && expected_edges != edges
            {
                return Err(Failure::operational(
                    "library-lock",
                    format!("resolved foundation import edges changed for {module}"),
                ));
            }
        }
        let mut reachable = BTreeSet::new();
        let mut queue: VecDeque<String> = roots_vec.iter().cloned().collect();
        while let Some(module) = queue.pop_front() {
            if !reachable.insert(module.clone()) {
                continue;
            }
            if let Some(edges) = resolved_graph.get(&module) {
                for edge in edges {
                    if !reachable.contains(&edge.module) {
                        queue.push_back(edge.module.clone());
                    }
                }
            }
        }
        for (module, edges) in resolved_graph {
            if foundation.contains_key(&module)
                || !reachable.contains(&module)
                || self.admitted()?.library_modules.contains(&module)
            {
                continue;
            }
            let artifacts = collect_pinned_sysroot_module_artifacts(&prefix, &module, "library")?;
            let adm = self.admitted_mut()?;
            adm.artifacts.insert(module.clone(), artifacts);
            adm.graph.insert(module.clone(), edges);
            adm.library_modules.insert(module);
        }
        Ok(())
    }

    /// Invoke `"resolve-imports"` mode on `TrustedBoundary.lean` with the
    /// admitted Lean sysroot and requested module roots.
    #[doc(hidden)]
    pub fn resolve_sysroot_imports(
        &mut self,
        modules: &[String],
    ) -> Result<BTreeMap<String, Vec<ImportEdge>>, Failure> {
        let req = {
            let adm = self.admitted()?;
            json!({
                "mode": "resolve-imports",
                "sysroot": adm.prefix.to_string_lossy(),
                "modules": modules,
            })
        };
        let mut resp = self.invoke_inspector("resolve-imports", &req)?;
        let graph_val = resp.as_object_mut().and_then(|o| o.remove("graph")).ok_or_else(|| {
            Failure::operational("resolve-imports", "missing graph in resolve-imports response")
        })?;
        serde_json::from_value(graph_val)
            .map_err(|e| Failure::operational("resolve-imports", format!("invalid graph: {e}")))
    }

    /// Discover, guard, and hash the unpinned `Init`/`Std` sysroot import
    /// closure via `"resolve-imports"`, partitioning the `{Init.Prelude,
    /// Init.Core}` closure into `foundation_graph` and all remaining sysroot
    /// modules into `library_modules`.
    pub(crate) fn admit_unpinned_sysroot(
        &mut self,
        requested_imports: impl IntoIterator<Item = String>,
    ) -> Result<(), Failure> {
        let prefix = self.admitted()?.prefix.clone();
        let mut resolve_roots =
            BTreeSet::from(["Init.Prelude".to_string(), "Init.Core".to_string()]);
        for module in requested_imports {
            if !is_allowed_unpinned_sysroot_module(&module) {
                return Err(Failure::policy(
                    "target-import",
                    format!(
                        "unsupported import {module}; unpinned mode permits only Init and Std sysroot imports"
                    ),
                ));
            }
            let olean_path =
                prefix.join("lib/lean").join(format!("{}.olean", module.replace('.', "/")));
            match fs::metadata(&olean_path) {
                Ok(meta) if meta.is_file() => {}
                Ok(_) => {
                    return Err(Failure::policy(
                        "target-import",
                        format!("unsupported import {module}; expected compiled .olean file"),
                    ));
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => {
                    return Err(Failure::policy(
                        "target-import",
                        format!("unsupported import {module}; missing sysroot module"),
                    ));
                }
                Err(e) => {
                    return Err(Failure::operational(
                        "sysroot",
                        format!("cannot inspect {}: {e}", olean_path.display()),
                    ));
                }
            }
            resolve_roots.insert(module);
        }
        let roots: Vec<String> = resolve_roots.into_iter().collect();
        let resolved_graph = self.resolve_sysroot_imports(&roots)?;
        let foundation_set = compute_unpinned_foundation_closure(&resolved_graph)?;

        // Replace any prior unpinned sysroot admission wholesale so repeated
        // calls on the same `Checker` keep foundation and library sets disjoint
        // with no stale modules from earlier targets.
        {
            let adm = self.admitted_mut()?;
            adm.foundation_graph.clear();
            adm.library_modules.clear();
            adm.graph.clear();
            adm.artifacts.clear();
            adm.unpinned_records.clear();
        }
        for (module, edges) in resolved_graph {
            let unpinned = hash_unpinned_sysroot_module(&prefix, &module, "sysroot")?;
            let adm = self.admitted_mut()?;
            adm.artifacts.insert(module.clone(), unpinned.artifacts.clone());
            adm.unpinned_records.insert(module.clone(), unpinned);
            adm.graph.insert(module.clone(), edges.clone());
            if foundation_set.contains(&module) {
                adm.foundation_graph.insert(module, edges);
            } else {
                adm.library_modules.insert(module);
            }
        }
        Ok(())
    }

    /// Check an exact target root using freshly compiled, authenticated
    /// sources.
    ///
    /// Arbitrary target elaborators may execute code under the experimental
    /// intact-host assumption. Repository source admission remains separate and
    /// retains its closed syntax policy. Reported frontend/source and policy
    /// rejections use code 1; malformed protocols, native failures, resource or
    /// kernel reports, and unavailable locked artifacts use code 2. A rejection
    /// alone does not establish that the requested proposition is false.
    pub fn run_target(&mut self, request: &TargetAuditRequest) -> Result<Json, Failure> {
        self.reset_stage()?;
        self.tool_admission()?;
        for digest in [
            &request.bindings.request_sha256,
            &request.bindings.capture_sha256,
            &request.bindings.model_manifest_sha256,
            &request.bindings.specification_manifest_sha256,
        ] {
            if !is_sha256_hex(digest) {
                return Err(Failure::policy("target-input", "invalid subject binding digest"));
            }
        }
        for name in [
            &request.theorem_module,
            &request.theorem_name,
            &request.expected_module,
            &request.expected_declaration,
            &request.canonical_root,
            &request.subject_declaration,
            &request.specification_declaration,
        ] {
            if !target_name_valid(name) {
                return Err(Failure::policy(
                    "target-input",
                    format!("target name is outside the ASCII dotted-name protocol: {name}"),
                ));
            }
        }
        // Authenticate each source before using its claimed role or name.
        // Compiling adjacent caller artifacts would bypass this ownership
        // partition even when their import names looked correct.
        //
        // One role and staged path belong to each source. Reject overlap with
        // locked modules so callers cannot replace foundation or library data.
        let mut staged = BTreeMap::new();
        let mut roles = BTreeMap::new();
        for module in &request.modules {
            let adm = self.admitted()?;
            let root_pkg = module.module.split('.').next().unwrap_or("");
            let collides_with_sysroot = is_reserved_toolchain_module(&module.module)
                || if adm.unpinned {
                    adm.sysroot_package_roots.contains(root_pkg)
                } else {
                    adm.foundation_graph.contains_key(&module.module)
                };
            if !target_name_valid(&module.module)
                || roles.contains_key(&module.module)
                || collides_with_sysroot
            {
                return Err(Failure::policy(
                    "target-input",
                    format!("duplicate, reserved or invalid module {}", module.module),
                ));
            }
            if !is_sha256_hex(&module.expected_sha256) {
                return Err(Failure::policy("target-input", "invalid source digest"));
            }
            let dest =
                self.stage.join("ro").join(format!("{}.lean", module.module.replace('.', "/")));
            stage_regular_file(&module.source, &dest, "target-input")?;
            if !sha256_file(&dest, "target-input")?.eq_ignore_ascii_case(&module.expected_sha256) {
                return Err(Failure::policy(
                    "target-input",
                    format!("source digest differs for {}", module.module),
                ));
            }
            set_mode(&dest, 0o444)?;
            staged.insert(module.module.clone(), dest);
            roles.insert(module.module.clone(), module.role);
        }
        if roles.get(&request.theorem_module) != Some(&TargetRole::Proof)
            || roles.get(&request.expected_module) != Some(&TargetRole::Expected)
            || !roles.values().any(|r| *r == TargetRole::Model)
            || !roles.values().any(|r| *r == TargetRole::Capture)
            || !roles.values().any(|r| *r == TargetRole::Specification)
        {
            return Err(Failure::policy(
                "target-input",
                "missing or incorrect target authority roles",
            ));
        }
        // Read imports before elaboration to establish the complete module
        // graph and reject missing or forbidden dependencies. This is an
        // early structural check; compiled dependency checks remain needed
        // because elaborators can introduce references not visible here.
        let header_sources: Vec<(String, PathBuf)> =
            staged.iter().map(|(n, p)| (n.clone(), p.clone())).collect();
        let headers: PreflightResult =
            serde_json::from_value(self.inspect_headers(&header_sources)?)
                .map_err(|e| Failure::operational("headers", e.to_string()))?;
        let mut imports = BTreeMap::new();
        let mut is_module = BTreeMap::new();
        for header in headers.headers {
            if !staged.contains_key(&header.module) || imports.contains_key(&header.module) {
                return Err(Failure::policy("headers", "duplicate or foreign source header"));
            }
            is_module.insert(header.module.clone(), header.is_module);
            imports.insert(header.module, header.imports);
        }
        if imports.len() != staged.len() {
            return Err(Failure::policy("headers", "incomplete target source header inventory"));
        }
        // Retain every non-bundled target module plus only those bundled
        // `Anneal.*` theory modules reachable from them via parsed imports.
        let retained = reachable_target_modules(request, &imports);
        imports.retain(|module, _| retained.contains(module));
        is_module.retain(|module, _| retained.contains(module));
        roles.retain(|module, _| retained.contains(module));
        staged.retain(|module, _| retained.contains(module));
        let filtered_request = TargetAuditRequest {
            modules: request
                .modules
                .iter()
                .filter(|m| retained.contains(&m.module))
                .cloned()
                .collect(),
            theorem_module: request.theorem_module.clone(),
            theorem_name: request.theorem_name.clone(),
            expected_module: request.expected_module.clone(),
            expected_declaration: request.expected_declaration.clone(),
            canonical_root: request.canonical_root.clone(),
            subject_declaration: request.subject_declaration.clone(),
            specification_declaration: request.specification_declaration.clone(),
            allow_sorry_in_proof: request.allow_sorry_in_proof,
            bindings: request.bindings.clone(),
        };
        if self.admitted()?.unpinned {
            let external_imports: Vec<String> = imports
                .values()
                .flatten()
                .filter(|e| !roles.contains_key(&e.module))
                .map(|e| e.module.clone())
                .collect();
            self.admit_unpinned_sysroot(external_imports)?;
        } else {
            self.admit_libraries(imports.values().flatten().map(|e| e.module.clone()))?;
        }
        for (module, edges) in &imports {
            let mod_is_module = is_module.get(module).copied().unwrap_or(false);
            let allow_theory_import_all = mod_is_module
                && roles[module] == TargetRole::Proof
                && is_bundled_theory_module(module);
            let has_non_meta_init = edges.iter().any(|e| e.module == "Init" && !e.is_meta);
            for edge in edges {
                if edge.import_all
                    && !(allow_theory_import_all
                        && ALLOWED_THEORY_IMPORT_ALL_MODULES.contains(&edge.module.as_str()))
                {
                    return Err(Failure::policy(
                        "target-import",
                        format!("import modifiers are unsupported in {module}"),
                    ));
                }
                if !edge.is_exported && !mod_is_module {
                    return Err(Failure::policy(
                        "target-import",
                        format!("import modifiers are unsupported in {module}"),
                    ));
                }
                if edge.is_meta && !(edge.module == "Init" && has_non_meta_init) {
                    return Err(Failure::policy(
                        "target-import",
                        format!("meta import {} is unsupported in {module}", edge.module),
                    ));
                }
                if let Some(dep) = roles.get(&edge.module) {
                    if !roles[module].allows(*dep) {
                        return Err(Failure::policy(
                            "target-role",
                            format!("{} cannot import {}", module, edge.module),
                        ));
                    }
                } else if !self.admitted()?.artifacts.contains_key(&edge.module) {
                    return Err(Failure::policy(
                        "target-import",
                        format!(
                            "unsupported import {} in {}; use explicit prelude and supported checked math imports",
                            edge.module, module
                        ),
                    ));
                }
            }
        }
        let order =
            topo_sort_modules(staged.keys().cloned().collect(), &imports, "target import cycle")?;
        // Run fail-closed `"spec-preflight"` across retained
        // `TargetRole::Specification` modules, grouping strictly by each
        // specification module's own transitive `(foundation_graph,
        // library_modules)` import closure so neither unimported `Init.*`
        // foundation extensions nor proof/sibling library imports can leak
        // parser syntax or priorities into a specification's preflight AST.
        let spec_sources: Vec<(String, PathBuf)> = staged
            .iter()
            .filter(|(m, _)| roles.get(*m) == Some(&TargetRole::Specification))
            .map(|(m, p)| (m.clone(), p.clone()))
            .collect();
        if spec_sources.is_empty() {
            let empty_fnd = BTreeSet::new();
            let empty_libs = BTreeSet::new();
            let spec_pf = self.inspect_spec_preflight_with_closures(
                &[],
                Some(&empty_fnd),
                Some(&empty_libs),
            )?;
            if spec_pf.get("checked").and_then(Json::as_array).is_none() {
                return Err(Failure::operational(
                    "spec-preflight",
                    "missing checked specification inventory",
                ));
            }
        } else {
            type ClosureKey = (BTreeSet<String>, BTreeSet<String>);
            let spec_groups: BTreeMap<ClosureKey, Vec<(String, PathBuf)>> = {
                let adm = self.admitted()?;
                let mut groups: BTreeMap<ClosureKey, Vec<(String, PathBuf)>> = BTreeMap::new();
                for (spec_mod, spec_path) in &spec_sources {
                    let mut visited_mods: BTreeSet<String> = BTreeSet::new();
                    let mut fnd: BTreeSet<String> = BTreeSet::new();
                    let mut libs: BTreeSet<String> = BTreeSet::new();
                    let mut queue: VecDeque<String> = VecDeque::from([spec_mod.clone()]);
                    while let Some(curr) = queue.pop_front() {
                        if !visited_mods.insert(curr.clone()) {
                            continue;
                        }
                        if adm.foundation_graph.contains_key(&curr) {
                            fnd.insert(curr.clone());
                        } else if adm.library_modules.contains(&curr) {
                            libs.insert(curr.clone());
                        }
                        let edges = imports
                            .get(&curr)
                            .map(Vec::as_slice)
                            .or_else(|| adm.graph.get(&curr).map(Vec::as_slice));
                        if let Some(edges) = edges {
                            for edge in edges {
                                if !visited_mods.contains(&edge.module) {
                                    queue.push_back(edge.module.clone());
                                }
                            }
                        }
                    }
                    groups
                        .entry((fnd, libs))
                        .or_default()
                        .push((spec_mod.clone(), spec_path.clone()));
                }
                groups
            };
            let mut checked_specs: BTreeSet<String> = BTreeSet::new();
            for ((group_fnd, group_libs), group_sources) in &spec_groups {
                let spec_pf = self.inspect_spec_preflight_with_closures(
                    group_sources,
                    Some(group_fnd),
                    Some(group_libs),
                )?;
                let group_checked: BTreeSet<&str> = spec_pf
                    .get("checked")
                    .and_then(Json::as_array)
                    .ok_or_else(|| {
                        Failure::operational(
                            "spec-preflight",
                            "missing checked specification inventory",
                        )
                    })?
                    .iter()
                    .filter_map(Json::as_str)
                    .collect();
                if group_checked.len() != group_sources.len()
                    || !group_sources.iter().all(|(m, _)| group_checked.contains(m.as_str()))
                {
                    return Err(Failure::operational(
                        "spec-preflight",
                        "incomplete specification preflight inventory",
                    ));
                }
                checked_specs.extend(group_checked.into_iter().map(str::to_owned));
            }
            if checked_specs.len() != spec_sources.len()
                || !spec_sources.iter().all(|(m, _)| checked_specs.contains(m.as_str()))
            {
                return Err(Failure::operational(
                    "spec-preflight",
                    "incomplete specification preflight inventory",
                ));
            }
        }
        // Compilation consumes authenticated private copies and explicit
        // imported artifacts across the verified module DAG inside `ExecSeal`.
        self.compiled_roles = roles.clone();
        self.compile_lean_modules_parallel(
            &order,
            &staged,
            &imports,
            &is_module,
            "lib",
            false,
            true,
            default_compile_workers(4),
        )?;
        // Re-hash `stage/control/TrustedBoundary.lean`,
        // `stage/control/TrustedBoundary.olean`, every staged source snapshot
        // in `stage/ro/`, and every Door-1-promoted `.olean` in `stage/lib/`
        // immediately before `"target-audit"` (`ArtifactLedger`).
        let ledger_sources: Vec<(PathBuf, &str)> = filtered_request
            .modules
            .iter()
            .map(|m| (staged[&m.module].clone(), m.expected_sha256.as_str()))
            .collect();
        self.verify_artifact_ledger(&ledger_sources)?;
        // Compilation success alone does not establish the exact theorem
        // type, permitted assumptions, or compiled source roles. Acceptance
        // is a separate inspection of the produced kernel declarations.
        let mut report = self.inspect_target_with_modes(&filtered_request, &is_module)?;
        let mut provenance = Vec::new();
        for module in &filtered_request.modules {
            let artifacts = &self.admitted()?.artifacts[&module.module];
            let paths = artifacts.to_wire();
            let hashes: Result<Vec<_>, Failure> = paths
                .iter()
                .flat_map(|parts| parts.iter())
                .map(|p| Ok(json!({"sha256": sha256_file(Path::new(p), "target-artifact")?})))
                .collect();
            provenance.push(json!({"module": module.module, "role": module.role,
                "sourceSha256": module.expected_sha256, "artifacts": hashes?}));
        }
        let obj = report
            .as_object_mut()
            .ok_or_else(|| Failure::operational("target-audit", "non-object inspector result"))?;
        // Report modules determining the subject, model, or specification,
        // including installed libraries used only by captured program data.
        // The logical closures exclude proof-only helpers; the source inventory
        // above separately identifies every retained target source.
        let mut identities = serde_json::Map::new();
        for key in ["subjectClosure", "modelClosure", "specificationClosure"] {
            if let Some(rows) = obj.get(key).and_then(Json::as_array) {
                for row in rows {
                    let Some(module) = row.get("module").and_then(Json::as_str) else {
                        return Err(Failure::operational(
                            "target-audit",
                            "missing closure provenance",
                        ));
                    };
                    if identities.contains_key(module) {
                        continue;
                    }
                    let adm = self.admitted()?;
                    let (source_sha, hashes) = if let Some(source) =
                        filtered_request.modules.iter().find(|m| m.module == module)
                    {
                        (
                            Json::String(source.expected_sha256.clone()),
                            hash_admitted_module_artifacts(adm, module)?,
                        )
                    } else if adm.unpinned {
                        let admitted = adm.unpinned_records.get(module).ok_or_else(|| {
                            Failure::operational(
                                "target-provenance",
                                format!("missing admitted unpinned record for {module}"),
                            )
                        })?;
                        let current =
                            hash_unpinned_sysroot_module(&adm.prefix, module, "target-provenance")?;
                        if current.source_sha256 != admitted.source_sha256
                            || current.part_hashes != admitted.part_hashes
                        {
                            return Err(Failure::policy(
                                "target-provenance",
                                format!("unpinned sysroot module {module} changed during run"),
                            ));
                        }
                        let hashes = admitted
                            .part_hashes
                            .iter()
                            .map(|(part, sha)| json!({ "part": part, "sha256": sha }))
                            .collect();
                        (Json::from(admitted.source_sha256.clone()), hashes)
                    } else {
                        let source_sha = sha256_file(
                            &adm.prefix
                                .join("src/lean")
                                .join(format!("{}.lean", module.replace('.', "/"))),
                            "target-provenance",
                        )?;
                        (Json::String(source_sha), hash_admitted_module_artifacts(adm, module)?)
                    };
                    identities.insert(
                        module.into(),
                        json!({"sourceSha256": source_sha, "artifacts": hashes}),
                    );
                }
            }
        }
        obj.insert("moduleIdentities".into(), Json::Object(identities));
        obj.insert(
            "bindings".into(),
            serde_json::to_value(&request.bindings)
                .map_err(|e| Failure::operational("target-audit", e.to_string()))?,
        );
        obj.insert("sources".into(), json!(provenance));
        let adm = self.admitted()?;
        obj.insert("toolchain".into(), json!(adm.version));
        if adm.unpinned {
            let current_lean_sha = sha256_file_deref(&adm.exec_lean, "target-provenance")
                .map_err(|e| Failure::operational("target-provenance", e.message))?;
            let Some(admitted_lean_sha) = adm.lean_binary_sha256.as_deref() else {
                return Err(Failure::operational(
                    "target-provenance",
                    "missing admitted unpinned Lean binary digest",
                ));
            };
            if !current_lean_sha.eq_ignore_ascii_case(admitted_lean_sha) {
                return Err(Failure::operational(
                    "target-provenance",
                    "unpinned Lean executable changed during run",
                ));
            }
            let sysroot_modules_sha256 = unpinned_sysroot_modules_sha256(adm)?;
            obj.insert(
                "unpinnedLean".into(),
                json!({
                    "expectedToolchain": TOOLCHAIN,
                    "observedVersion": adm.version,
                    "leanBinarySha256": admitted_lean_sha,
                    "foundationModules": adm.foundation_modules(),
                    "sysrootModulesSha256": sysroot_modules_sha256,
                    "admittedSysrootModuleCount": adm.unpinned_records.len(),
                }),
            );
        }
        Ok(report)
    }
}

fn unpinned_sysroot_modules_sha256(adm: &AdmittedToolchain) -> Result<String, Failure> {
    #[derive(Serialize)]
    #[serde(rename_all = "camelCase")]
    struct ModuleRecord<'a> {
        module: &'a str,
        parts: BTreeMap<&'a str, &'a str>,
        source_sha256: Option<&'a str>,
    }

    let entries: Vec<ModuleRecord<'_>> = adm
        .unpinned_records
        .iter()
        .map(|(module, rec)| {
            let parts =
                rec.part_hashes.iter().map(|(part, sha)| (part.as_str(), sha.as_str())).collect();
            ModuleRecord {
                module: module.as_str(),
                parts,
                source_sha256: rec.source_sha256.as_deref(),
            }
        })
        .collect();
    let bytes = serde_json::to_vec(&entries)
        .map_err(|e| Failure::operational("target-provenance", e.to_string()))?;
    Ok(sha256_bytes(&bytes))
}

fn hash_admitted_module_artifacts(
    adm: &AdmittedToolchain,
    module: &str,
) -> Result<Vec<Json>, Failure> {
    let artifacts = adm
        .artifacts
        .get(module)
        .ok_or_else(|| Failure::operational("target-provenance", "missing closure artifact"))?;
    artifacts
        .to_wire()
        .iter()
        .flat_map(|p| p.iter())
        .map(|p| {
            Ok(json!({
                "part": Path::new(p).file_name().and_then(|s| s.to_str()),
                "sha256": sha256_file(Path::new(p), "target-provenance")?
            }))
        })
        .collect()
}

// Exercise locked-module admission without a Lean installation. The synthetic
// toolchain's `lean` is a shell script whose digest its own foundation lock
// pins. The script answers only the version and prefix queries of tool
// admission, so each tested refusal must occur before any inspector or
// compiler request; reaching one fails with status 3.
#[cfg(all(test, unix))]
mod admission_tests {
    use std::{fs, os::unix::fs::symlink};

    use serde_json::json;

    use super::*;
    use crate::toolchain::{LibraryLock, TOOLCHAIN, compute_sysroot_manifest_sha256_for_test};

    const VERSION: &str = "Lean (version 4.34.1, synthetic admission fixture)";
    const FOUNDATION: &str = "Init.Prelude";
    const LIBRARY: &str = "Init.Data.BitVec.Basic";
    const LIBRARY_USER: &str = "Init.Data.BitVec.Lemmas";
    const STD_LIBRARY: &str = "Std.Data.TreeMap";

    fn edge(module: &str) -> Json {
        json!({"module": module, "importAll": false, "isExported": true, "isMeta": false})
    }

    /// Install `module`'s source and `.olean` under `prefix` and return a lock
    /// record that also requires its other companion parts to be absent.
    fn install(prefix: &Path, module: &str) -> Json {
        let relative = module.replace('.', "/");
        let source = prefix.join("src/lean").join(format!("{relative}.lean"));
        let olean = prefix.join("lib/lean").join(format!("{relative}.olean"));
        for (path, part) in [(&source, "source"), (&olean, "olean")] {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, format!("{module} {part}\n")).unwrap();
        }
        json!({
            "sourceSha256": sha256_file(&source, "fixture").unwrap(),
            "parts": {
                "olean": sha256_file(&olean, "fixture").unwrap(),
                "olean.server": null,
                "olean.private": null,
                "ir.sig": null,
                "ir": null,
            },
        })
    }

    /// A bundle root, Lean prefix, and `lean` script that pass
    /// `Checker::tool_admission`.
    struct Toolchain {
        _dir: tempfile::TempDir,
        base: PathBuf,
        root: PathBuf,
        prefix: PathBuf,
        lean: PathBuf,
        sysroot_manifest_sha256: String,
    }

    impl Toolchain {
        fn new() -> Self {
            let dir = tempfile::tempdir().unwrap();
            let base = fs::canonicalize(dir.path()).unwrap();
            let root = base.join("bundle");
            let prefix = base.join("prefix");
            let lean = base.join("lean");
            let resolve_graph_path = base.join("resolve-graph.json");
            let default_graph = json!({
                "ok": true,
                "result": {
                    "graph": {
                        FOUNDATION: [],
                        LIBRARY: [edge(FOUNDATION)],
                        LIBRARY_USER: [edge(LIBRARY)],
                        STD_LIBRARY: [edge(LIBRARY)],
                    }
                }
            });
            fs::write(&resolve_graph_path, default_graph.to_string()).unwrap();
            // Simulate compiling the inspector through Door 1 so `"headers"`
            // reaches `TrustedBoundaryEntry.lean` (`exit 3`), while
            // `"resolve-imports"` returns the staged `resolve-graph.json`.
            let marker = base.join("headers-ran.marker");
            fs::write(
                &lean,
                format!(
                    r#"#!/bin/sh
case "$1" in
    --version) printf '%s\n' '{VERSION}'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
while [ "$#" -gt 1 ]; do
    case "$1:$2" in
        -o:*/out/TrustedBoundary.olean|-o:*/inspector-compile-*/TrustedBoundary.olean)
            printf 'olean\002synthetic\n' > "$2"
            exit 0
            ;;
        --run:*/TrustedBoundaryEntry.lean)
            if [ "$#" -ge 4 ] && grep -q '"resolve-imports"' "$3"; then
                cat '{}' > "$4"
                exit 0
            fi
            printf 'ran\n' >> '{}'
            exit 3
            ;;
    esac
    shift
done
exit 4
"#,
                    prefix.display(),
                    resolve_graph_path.display(),
                    marker.display()
                ),
            )
            .unwrap();
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();
            }
            let records: BTreeMap<_, _> = [FOUNDATION, LIBRARY, LIBRARY_USER, STD_LIBRARY]
                .into_iter()
                .map(|module| (module, install(&prefix, module)))
                .collect();
            for dir_rel in ["lib/lean/Init", "lib/lean/Std", "lib/lean/Lean", "src/lean/Init", "src/lean/Std"] {
                fs::create_dir_all(prefix.join(dir_rel)).unwrap();
            }
            fs::write(prefix.join("lib/lean/Lean/Replay.olean"), b"synthetic lean replay\n")
                .unwrap();
            let sysroot_manifest_sha256 =
                compute_sysroot_manifest_sha256_for_test(&prefix.join("lib/lean"));
            let foundation_lock = json!({
                "schema": 1,
                "toolchain": TOOLCHAIN,
                "distributions": {VERSION: sha256_file(&lean, "fixture").unwrap()},
                "modules": {FOUNDATION: records[FOUNDATION]},
                "graph": {FOUNDATION: []},
                "axioms": [],
            });
            for (relative, contents) in [
                ("trusted/audit/TrustedBoundary.lean", "-- Never run.\n".to_owned()),
                ("trusted/lean/lean-toolchain", format!("{TOOLCHAIN}\n")),
                ("trusted/lean/foundation-lock.json", foundation_lock.to_string()),
            ] {
                let path = root.join(relative);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(path, contents).unwrap();
            }
            Self { _dir: dir, base, root, prefix, lean, sysroot_manifest_sha256 }
        }

        /// Return the canonical 4-line recursive sysroot tree digest lock.
        fn library_lock(&self) -> String {
            LibraryLock::compute_for_prefix(&self.prefix, "fixture")
                .expect("test sysroot trees should hash cleanly")
                .render()
        }

        fn write_library_lock(&self, lock: &str) {
            let path = self.root.join("trusted/audit/library-lock.json");
            fs::write(path, lock).unwrap();
        }

        fn checker(&self) -> Checker {
            let mut checker =
                Checker::new_with_env(&self.root, Some(self.lean.as_path()), []).unwrap();
            checker.set_expected_sysroot_manifest_sha256_for_test(&self.sysroot_manifest_sha256);
            checker.set_sandbox_mode(crate::SandboxMode::Unsandboxed);
            checker
        }

        /// Return a request whose five sources pass target input admission.
        fn request(&self) -> TargetAuditRequest {
            let mut modules = Vec::new();
            for (module, role) in [
                ("Model", TargetRole::Model),
                ("Captured", TargetRole::Capture),
                ("Spec", TargetRole::Specification),
                ("Expected", TargetRole::Expected),
                ("Proof", TargetRole::Proof),
            ] {
                let source = self.base.join(format!("{module}.lean"));
                fs::write(&source, format!("-- {module}\n")).unwrap();
                modules.push(TargetModule {
                    module: module.to_owned(),
                    expected_sha256: sha256_file(&source, "fixture").unwrap(),
                    source,
                    role,
                });
            }
            let digest = modules[0].expected_sha256.clone();
            TargetAuditRequest {
                modules,
                theorem_module: "Proof".to_owned(),
                theorem_name: "Proof.verify".to_owned(),
                expected_module: "Expected".to_owned(),
                expected_declaration: "Expected.claim".to_owned(),
                canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
                subject_declaration: "Captured.program".to_owned(),
                specification_declaration: "Spec.specs".to_owned(),
                allow_sorry_in_proof: false,
                bindings: TargetBindings {
                    request_sha256: digest.clone(),
                    capture_sha256: digest.clone(),
                    model_manifest_sha256: digest.clone(),
                    specification_manifest_sha256: digest,
                },
            }
        }
    }

    /// Admit the library import closure of `root` with a fresh checker.
    fn admit(toolchain: &Toolchain, root: &str) -> Result<(), Failure> {
        let mut checker = toolchain.checker();
        checker.tool_admission()?;
        checker.admit_libraries([root.to_owned()])
    }

    /// Tool admission validates the 4-line sysroot lock against all four
    /// `Init`/`Std` directory trees before any target input.
    #[test]
    fn tool_admission_rejects_invalid_library_catalogs() {
        let toolchain = Toolchain::new();
        // Controls: an absent catalog and the valid 4-line lock both pass, so
        // each refusal below follows from its single change.
        assert!(toolchain.checker().tool_admission().unwrap().library_lock.is_none());
        let valid = toolchain.library_lock();
        let expected_lock = LibraryLock::parse(&valid).unwrap();
        toolchain.write_library_lock(&valid);
        let mut checker = toolchain.checker();
        let admitted = checker.tool_admission().unwrap();
        assert_eq!(admitted.library_lock.as_ref(), Some(&expected_lock));
        assert!(admitted.library_modules.is_empty());

        let valid_lines: Vec<&str> = valid.lines().collect();
        assert_eq!(valid_lines.len(), 4);
        let missing_line = format!("{}\n", valid_lines[..3].join("\n"));
        let duplicate_line = format!("{}\n{}", valid, valid_lines[0]);
        let unknown_label = format!(
            "{}\n{}  lean/lib/lean/Lean/**\n",
            valid_lines[..3].join("\n"),
            "0".repeat(64)
        );
        let bad_hex = format!(
            "{}  lean/lib/lean/Init/**\n{}\n",
            "z".repeat(64),
            valid_lines[1..].join("\n")
        );
        let extra_line = format!("{valid}{}  lean/lib/lean/Extra/**\n", "a".repeat(64));
        let legacy_json = "{\"schema\":1}\n".to_owned();
        let crlf_lock = valid.replace('\n', "\r\n");

        for (case, lock) in [
            ("empty", String::new()),
            ("missing line", missing_line),
            ("duplicate line", duplicate_line),
            ("unknown label", unknown_label),
            ("bad hex", bad_hex),
            ("extra line", extra_line),
            ("legacy json", legacy_json),
            ("crlf", crlf_lock),
        ] {
            toolchain.write_library_lock(&lock);
            assert_eq!(
                toolchain.checker().tool_admission().unwrap_err(),
                Failure::operational("library-lock", "invalid checked-library catalog"),
                "{case}"
            );
        }

        // Mismatching tree digest (corrupted digest on valid tree) fails
        // closed.
        let mismatched = format!(
            "{}  lean/lib/lean/Init/**\n{}\n",
            "f".repeat(64),
            valid_lines[1..].join("\n")
        );
        toolchain.write_library_lock(&mismatched);
        let mismatch_err = toolchain.checker().tool_admission().unwrap_err();
        assert_eq!((mismatch_err.code, mismatch_err.phase.as_str()), (2, "library-lock"));
        assert!(
            mismatch_err.message.contains("sysroot tree lean/lib/lean/Init/** SHA-256 mismatch"),
            "{mismatch_err}"
        );

        // The catalog must be the bundle's own regular file.
        let linked = toolchain.base.join("linked-library-lock.json");
        fs::write(&linked, &valid).unwrap();
        let path = toolchain.root.join("trusted/audit/library-lock.json");
        fs::remove_file(&path).unwrap();
        std::os::unix::fs::symlink(&linked, &path).unwrap();
        let failure = toolchain.checker().tool_admission().unwrap_err();
        assert_eq!((failure.code, failure.phase.as_str()), (1, "library-lock"), "{failure}");
        assert!(failure.message.starts_with("expected a regular file: "), "{failure}");
    }

    /// A target source cannot take the name of a locked foundation or reserved
    /// toolchain module root
    /// (`Init`, `Std`, `Lean`, `Lake`, `TrustedBoundary`).
    #[test]
    fn run_target_rejects_modules_named_like_locked_modules() {
        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        let request = toolchain.request();
        // Control: without a locked name, the request passes every input
        // check and reaches the inspector, which the script refuses.
        let failure = toolchain.checker().run_target(&request).unwrap_err();
        assert_eq!((failure.code, failure.phase.as_str()), (2, "headers"), "{failure}");
        assert!(failure.message.starts_with("Lean exited Some(3)"), "{failure}");
        assert!(toolchain.base.join("headers-ran.marker").is_file());
        for module in [
            FOUNDATION,
            LIBRARY,
            STD_LIBRARY,
            "Init",
            "Init.System.IO",
            "Std",
            "Std.Data.Custom",
            "Lean",
            "Lean.Elab",
            "Lake",
            "Lake.DSL",
            "TrustedBoundary",
            "TrustedBoundary.Extra",
        ] {
            let mut shadowing = request.clone();
            shadowing.modules.push(TargetModule {
                module: module.to_owned(),
                // The name is refused before this path is read.
                source: toolchain.base.join("missing.lean"),
                expected_sha256: request.bindings.request_sha256.clone(),
                role: TargetRole::Proof,
            });
            assert_eq!(
                toolchain.checker().run_target(&shadowing).unwrap_err(),
                Failure::policy(
                    "target-input",
                    format!("duplicate, reserved or invalid module {module}")
                )
            );
        }
    }

    /// Library 4-tree digests are verified on tool admission and re-checked
    /// against TOCTOU mutations when `admit_libraries` resolves
    /// `Init.*`/`Std.*` closures.
    #[test]
    fn admit_libraries_rejects_changed_artifacts_in_the_import_closure() {
        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        // Control: unchanged trees admit `Init.*` and `Std.*` closures.
        let mut checker = toolchain.checker();
        checker.tool_admission().unwrap();
        checker.admit_libraries([STD_LIBRARY.to_owned()]).unwrap();
        let admitted = checker.admitted().unwrap();
        assert_eq!(
            admitted.library_modules,
            BTreeSet::from([LIBRARY.to_owned(), STD_LIBRARY.to_owned()])
        );
        assert!(admitted.artifacts.contains_key(LIBRARY));
        assert!(admitted.artifacts.contains_key(STD_LIBRARY));

        // Prepare a second admitted checker before mutating disk bytes so we
        // also exercise post-admission `admit_libraries` enforcement without
        // cache hits from the control run's `library_modules`.
        let mut toctou_checker = toolchain.checker();
        toctou_checker.tool_admission().unwrap();

        let olean = toolchain.prefix.join("lib/lean/Init/Data/BitVec/Basic.olean");
        fs::write(&olean, b"changed library artifact").unwrap();
        // A fresh checker rejects the altered sysroot `.olean` manifest in
        // `tool_admission` before library resolution begins.
        for root in [LIBRARY, LIBRARY_USER] {
            let err = admit(&toolchain, root).unwrap_err();
            assert_eq!((err.code, err.phase.as_str()), (1, "toolchain"), "{err}");
            assert!(
                err.message.contains("sysroot Init/Std/Lean .olean manifest SHA-256 mismatch"),
                "{root}: {err}"
            );
        }
        // The pre-admitted checker still catches the post-admission TOCTOU
        // artifact swap in `admit_libraries`.
        for root in [LIBRARY, LIBRARY_USER] {
            let err = toctou_checker.admit_libraries([root.to_owned()]).unwrap_err();
            assert_eq!((err.code, err.phase.as_str()), (2, "library-lock"), "{err}");
            assert!(
                err.message.contains("sysroot tree lean/lib/lean/Init/** SHA-256 mismatch"),
                "{root}: {err}"
            );
        }
    }

    /// Tampering with, removing, or symlinking sysroot `{Std,Lean}` `.olean`
    /// files outside `foundation-lock.json` and `library-lock.json` must reject
    /// during pinned `tool_admission` before any inspector invocation runs.
    #[test]
    fn tool_admission_rejects_tampered_lean_sysroot_before_inspector_runs() {
        let toolchain = Toolchain::new();
        let request = toolchain.request();
        let replay_olean = toolchain.prefix.join("lib/lean/Lean/Replay.olean");

        fs::write(&replay_olean, b"tampered lean replay\n").unwrap();
        let mut checker = toolchain.checker();
        let err = checker.run_target(&request).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "toolchain"), "{err}");
        assert!(
            err.message.contains("sysroot Init/Std/Lean .olean manifest SHA-256 mismatch"),
            "{err}"
        );
        assert!(!checker.execution_began());

        fs::remove_file(&replay_olean).unwrap();
        let mut checker = toolchain.checker();
        let err = checker.run_target(&request).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "toolchain"), "{err}");
        assert!(
            err.message.contains("sysroot Init/Std/Lean .olean manifest SHA-256 mismatch"),
            "{err}"
        );
        assert!(!checker.execution_began());

        let toolchain = Toolchain::new();
        let target = toolchain.prefix.join("lib/lean/Lean/Replay.olean");
        symlink(&target, toolchain.prefix.join("lib/lean/Std/Link.olean")).unwrap();
        let mut checker = toolchain.checker();
        let err = checker.run_target(&request).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "toolchain"), "{err}");
        assert!(err.message.contains("symlink forbidden in sysroot"), "{err}");
        assert!(!checker.execution_began());
    }

    /// Each reached sysroot tree also binds `.lean` sources, forbids extra
    /// unpinned files (such as `.ir` additions) inside the trees, rejects
    /// disallowed transitive sysroot imports, and rejects invalid names.
    #[test]
    fn admit_libraries_rejects_changed_sources_extra_parts_and_invalid_names() {
        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        let source = toolchain.prefix.join("src/lean/Init/Data/BitVec/Basic.lean");
        fs::write(&source, b"changed library source").unwrap();
        let err = admit(&toolchain, LIBRARY_USER).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (2, "library-lock"), "{err}");
        assert!(
            err.message.contains("sysroot tree lean/src/lean/Init/** SHA-256 mismatch"),
            "{err}"
        );

        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        let ir = toolchain.prefix.join("lib/lean/Init/Data/BitVec/Basic.ir");
        fs::write(&ir, b"unlocked companion part").unwrap();
        let err = admit(&toolchain, LIBRARY).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (2, "library-lock"), "{err}");
        assert!(
            err.message.contains("sysroot tree lean/lib/lean/Init/** SHA-256 mismatch"),
            "{err}"
        );

        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        assert_eq!(
            admit(&toolchain, "Init.Data.7Bad"),
            Err(Failure::operational("library-lock", "invalid module record"))
        );

        // Disallowed transitive imports (`Init`, `Std`, or `Lean.*`) returned
        // by `"resolve-imports"` fail closed in
        // `validate_pinned_library_graph`.
        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        fs::write(
            toolchain.base.join("resolve-graph.json"),
            json!({
                "ok": true,
                "result": {
                    "graph": {
                        LIBRARY: [edge("Init")],
                        "Init": [],
                    }
                }
            })
            .to_string(),
        )
        .unwrap();
        let err = admit(&toolchain, LIBRARY).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "sysroot"), "{err}");
        assert!(err.message.contains("only Init.* and Std.* are permitted"), "{err}");
    }
}

#[cfg(all(test, unix))]
mod unpinned_admission_tests {
    use std::{
        fs,
        os::unix::fs::{PermissionsExt, symlink},
    };

    use serde_json::json;

    use super::*;
    use crate::toolchain::{UNPINNED_FOUNDATION_MODULES, default_lean_path};

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn installed_lean() -> PathBuf {
        std::env::var_os("ANNEAL_LEAN")
            .filter(|v| !v.is_empty())
            .map(PathBuf::from)
            .unwrap_or_else(default_lean_path)
    }

    pub(super) fn write_target_request(
        dir: &Path,
        modules: Vec<(&str, TargetRole, &str)>,
    ) -> TargetAuditRequest {
        let mut req_modules = Vec::new();
        for (name, role, src) in modules {
            let path = dir.join(format!("{name}.lean"));
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, src).unwrap();
            req_modules.push(TargetModule {
                module: name.to_owned(),
                source: path,
                expected_sha256: sha256_file(&dir.join(format!("{name}.lean")), "fixture").unwrap(),
                role,
            });
        }
        let digest = req_modules[0].expected_sha256.clone();
        TargetAuditRequest {
            modules: req_modules,
            theorem_module: "Proof".to_owned(),
            theorem_name: "Proof.verify".to_owned(),
            expected_module: "Expected".to_owned(),
            expected_declaration: "Expected.claim".to_owned(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
            subject_declaration: "Captured.program".to_owned(),
            specification_declaration: "Spec.specs".to_owned(),
            allow_sorry_in_proof: false,
            bindings: TargetBindings {
                request_sha256: digest.clone(),
                capture_sha256: digest.clone(),
                model_manifest_sha256: digest.clone(),
                specification_manifest_sha256: digest,
            },
        }
    }

    pub(super) fn minimal_request(
        dir: &Path,
        proof_extra_import: Option<&str>,
    ) -> TargetAuditRequest {
        let extra = proof_extra_import.map(|m| format!("import {m}\n")).unwrap_or_default();
        write_target_request(
            dir,
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Data.BitVec.Basic\nnamespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\nimport Init.Data.Nat.Gcd\n\
                     def Captured.program : BitVec 8 := BitVec.ofNat 8 (Nat.gcd 0 7)\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    &format!(
                        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n{extra}\
                         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n"
                    ),
                ),
            ],
        )
    }

    #[test]
    fn unpinned_reserves_sysroot_roots_before_staging_and_allows_anneal_mir_wp() {
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let root = base.join("bundle");
        let prefix = base.join("sysroot");
        let ext = base.join("ext");
        fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();
        fs::create_dir_all(ext.join("LeanDir")).unwrap();
        fs::write(ext.join("Lake.olean"), b"lake").unwrap();
        symlink(ext.join("LeanDir"), prefix.join("lib/lean/Lean")).unwrap();
        symlink(ext.join("Lake.olean"), prefix.join("lib/lean/Lake.olean")).unwrap();
        fs::write(prefix.join("lib/lean/Std.olean"), b"std").unwrap();

        let marker = base.join("unpinned-headers-ran.marker");
        let lean = base.join("lean");
        fs::write(
            &lean,
            format!(
                r#"#!/bin/sh
case "$1" in
    --version) printf 'Lean 4.35\n'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
while [ "$#" -gt 1 ]; do
    case "$1:$2" in
        -o:*/out/TrustedBoundary.olean|-o:*/inspector-compile-*/TrustedBoundary.olean)
            printf 'olean\002synthetic\n' > "$2"
            exit 0
            ;;
        --run:*/TrustedBoundaryEntry.lean)
            printf 'ran\n' >> '{}'
            exit 3
            ;;
    esac
    shift
done
exit 4
"#,
                prefix.display(),
                marker.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

        let inspector = root.join("trusted/audit/TrustedBoundary.lean");
        fs::create_dir_all(inspector.parent().unwrap()).unwrap();
        fs::write(&inspector, "-- stub\n").unwrap();

        let mut req = minimal_request(&base.join("inputs"), None);
        // Bundled Anneal.MirWp (TargetRole::Proof) must NOT be rejected by
        // run_target's sysroot reservation check.
        let wp_src = base.join("inputs/Anneal/MirWp.lean");
        fs::create_dir_all(wp_src.parent().unwrap()).unwrap();
        fs::write(&wp_src, "prelude\n").unwrap();
        req.modules.push(TargetModule {
            module: "Anneal.MirWp".to_owned(),
            expected_sha256: sha256_file(&wp_src, "fixture").unwrap(),
            source: wp_src,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        checker.set_allow_unpinned_lean(true);
        checker.set_sandbox_mode(crate::SandboxMode::Unsandboxed);
        // Control: passes staging and reaches inspector (`Lean exited
        // Some(3)`).
        let control = checker.run_target(&req).unwrap_err();
        assert_eq!((control.code, control.phase.as_str()), (2, "headers"), "{control}");
        assert!(control.message.starts_with("Lean exited Some(3)"), "{control}");
        assert!(marker.is_file());

        for colliding in ["Init.Shadow", "Std.Shadow", "Lean.Shadow", "Lake", "Lake.Shadow"] {
            let mut bad = req.clone();
            bad.modules.push(TargetModule {
                module: colliding.to_owned(),
                // Refused before staging touches this path.
                source: base.join("does-not-exist.lean"),
                expected_sha256: req.bindings.request_sha256.clone(),
                role: TargetRole::Proof,
            });
            let err = checker.run_target(&bad).unwrap_err();
            assert_eq!(
                err,
                Failure::policy(
                    "target-input",
                    format!("duplicate, reserved or invalid module {colliding}")
                )
            );
        }
    }

    #[test]
    fn live_resolve_imports_round_trip_and_init_std_guard() {
        let lean = installed_lean();
        let mut checker = Checker::new(&repo_root(), Some(&lean)).unwrap();
        checker.set_allow_unpinned_lean(true);
        checker.tool_admission().unwrap();

        let roots_a = vec!["Init.Data.BitVec.Basic".to_string(), "Std.Data.HashMap".to_string()];
        let roots_b = vec!["Std.Data.HashMap".to_string(), "Init.Data.BitVec.Basic".to_string()];
        let graph_a = checker.resolve_sysroot_imports(&roots_a).unwrap();
        let graph_b = checker.resolve_sysroot_imports(&roots_b).unwrap();
        assert_eq!(graph_a, graph_b);
        assert!(graph_a.contains_key("Std.Data.HashMap"));
        assert!(graph_a.contains_key("Init.Data.BitVec.Basic"));

        let foundation = compute_unpinned_foundation_closure(&graph_a).unwrap();
        let expected_foundation: BTreeSet<String> =
            UNPINNED_FOUNDATION_MODULES.iter().map(|s| (*s).to_string()).collect();
        assert_eq!(foundation, expected_foundation);
    }

    #[test]
    fn live_unpinned_run_target_rejects_lean_lake_and_records_null_source_sha() {
        let real_lean = fs::canonicalize(installed_lean()).unwrap();
        let real_prefix_out =
            std::process::Command::new(&real_lean).arg("--print-prefix").output().unwrap();
        assert!(real_prefix_out.status.success());
        let real_prefix = PathBuf::from(String::from_utf8(real_prefix_out.stdout).unwrap().trim());

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        // Synthetic sysroot with symlinked lib/lean and NO src/lean directory.
        let syn_prefix = base.join("sysroot");
        fs::create_dir_all(syn_prefix.join("lib")).unwrap();
        symlink(real_prefix.join("lib/lean"), syn_prefix.join("lib/lean")).unwrap();

        let wrapper_lean = base.join("lean");
        fs::write(
            &wrapper_lean,
            format!(
                "#!/bin/sh\nif [ \"$1\" = \"--print-prefix\" ]; then\n  \
                 /bin/echo '{}'\n  exit 0\nfi\nexec '{}' \"$@\"\n",
                syn_prefix.display(),
                real_lean.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&wrapper_lean, fs::Permissions::from_mode(0o755)).unwrap();

        let mut checker = Checker::new(&repo_root(), Some(&wrapper_lean)).unwrap();
        checker.set_allow_unpinned_lean(true);
        checker.set_sandbox_mode(crate::SandboxMode::Unsandboxed);

        // Reject Lean.* and Lake.* imports at `"headers"` before compilation,
        // and verify `admit_unpinned_sysroot` independently enforces the same
        // Init/Std-only boundary as defense-in-depth.
        for forbidden in ["Lean.Elab", "Lake.Build"] {
            let bad_req = minimal_request(&base.join(format!("bad-{forbidden}")), Some(forbidden));
            let err = checker.run_target(&bad_req).unwrap_err();
            assert_eq!(err.code, 1, "{forbidden}: {err}");
            assert_eq!(err.phase, "headers", "{forbidden}: {err}");
            assert!(err.message.contains("disallowed sysroot import"), "{forbidden}: {err}");
            let adm_err = checker.admit_unpinned_sysroot([forbidden.to_owned()]).unwrap_err();
            assert_eq!(adm_err.code, 1, "{forbidden}: {adm_err}");
            assert_eq!(adm_err.phase, "target-import", "{forbidden}: {adm_err}");
            assert!(adm_err.message.contains("only Init and Std"), "{forbidden}: {adm_err}");
        }

        // Valid unpinned run with absent src/lean produces null sourceSha256 on
        // sysroot library modules while hashing all binary parts and keeping
        // non-null sourceSha256 on authored/model/capture/expected/proof.
        let good_req = minimal_request(&base.join("good"), None);
        let report = checker.run_target(&good_req).unwrap();
        assert_eq!(report["replay"], json!(true));
        assert_eq!(report["exactType"], json!(true));

        let identities = report["moduleIdentities"].as_object().unwrap();
        let nat_gcd = &identities["Init.Data.Nat.Gcd"];
        assert_eq!(nat_gcd["sourceSha256"], Json::Null);
        assert!(
            nat_gcd["artifacts"]
                .as_array()
                .unwrap()
                .iter()
                .any(|a| a["part"] == "Gcd.olean" && a["sha256"].as_str().unwrap().len() == 64),
            "{nat_gcd}"
        );
        for target_mod in ["Model", "Captured", "Spec"] {
            assert!(
                identities[target_mod]["sourceSha256"].as_str().is_some_and(is_sha256_hex),
                "{target_mod}: {}",
                identities[target_mod]
            );
        }
    }

    #[test]
    fn live_unpinned_wrapper_launcher_rechecks_resolved_exec_lean_consistently() {
        let real_lean = fs::canonicalize(installed_lean()).unwrap();
        let real_lean_sha = sha256_file_deref(&real_lean, "test").unwrap();
        let real_prefix = real_lean.parent().unwrap().parent().unwrap();

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        // Opaque wrapper launcher outside `<prefix>/bin/lean` with a host-write
        // sentinel proving it never runs unsandboxed under `ExecSeal`.
        let wrapper_sentinel = base.join("wrapper-ran");
        let wrapper_lean = base.join("lean-wrapper");
        fs::write(
            &wrapper_lean,
            format!(
                "#!/bin/sh\n: > '{}'\nexec '{}' \"$@\"\n",
                wrapper_sentinel.display(),
                real_lean.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&wrapper_lean, fs::Permissions::from_mode(0o755)).unwrap();
        let wrapper_sha = sha256_file_deref(&wrapper_lean, "test").unwrap();
        assert_ne!(
            wrapper_sha, real_lean_sha,
            "wrapper launcher must have a distinct digest from prefix/bin/lean"
        );

        // 1. Under `PreferBwrapOrLandlock`, an opaque wrapper outside a Lean
        //    sysroot must fail closed BEFORE spawning any child process.
        let mut contained_wrapper = Checker::new(&repo_root(), Some(&wrapper_lean)).unwrap();
        contained_wrapper.set_allow_unpinned_lean(true);
        contained_wrapper.set_sandbox_mode(crate::SandboxMode::PreferBwrapOrLandlock);
        let contained_req = minimal_request(&base.join("req-wrapper-contained"), None);
        let contained_err = contained_wrapper.run_target(&contained_req).unwrap_err();
        assert_eq!(contained_err.code, 2, "{contained_err}");
        assert_eq!(contained_err.phase, "toolchain", "{contained_err}");
        assert!(
            !wrapper_sentinel.exists(),
            "opaque wrapper launcher must never execute on the host under ExecSeal"
        );

        // 2. Static `elan`-layout proxy (`<elan_home>/bin/lean` +
        //    `settings.toml` `default_toolchain`) resolves
        //    `<elan_home>/toolchains/<tc>/bin/lean` statically without
        //    executing the proxy binary and runs all probes inside `ExecSeal`.
        let elan_home = base.join("elan-home");
        let elan_sentinel = base.join("elan-proxy-ran");
        let elan_proxy = elan_home.join("bin/lean");
        fs::create_dir_all(elan_proxy.parent().unwrap()).unwrap();
        fs::write(&elan_proxy, format!("#!/bin/sh\n: > '{}'\nexit 99\n", elan_sentinel.display()))
            .unwrap();
        fs::set_permissions(&elan_proxy, fs::Permissions::from_mode(0o755)).unwrap();
        fs::write(
            elan_home.join("settings.toml"),
            "default_toolchain = \"leanprover/lean4:v4.34.1\" # comment\n\
             [overrides]\n\"/ignored\" = \"other\"\n",
        )
        .unwrap();
        let elan_tc = elan_home.join("toolchains/leanprover--lean4---v4.34.1");
        fs::create_dir_all(elan_tc.join("bin")).unwrap();
        symlink(&real_lean, elan_tc.join("bin/lean")).unwrap();
        symlink(real_prefix.join("lib"), elan_tc.join("lib")).unwrap();

        let mut elan_checker = Checker::new(&repo_root(), Some(&elan_proxy)).unwrap();
        elan_checker.set_allow_unpinned_lean(true);
        elan_checker.set_sandbox_mode(crate::SandboxMode::PreferBwrapOrLandlock);
        let elan_req = minimal_request(&base.join("req-elan-contained"), None);
        let elan_report = elan_checker.run_target(&elan_req).unwrap();
        assert_eq!(elan_report["replay"], json!(true));
        assert_eq!(elan_report["exactType"], json!(true));
        assert_eq!(
            elan_report["unpinnedLean"]["leanBinarySha256"].as_str(),
            Some(real_lean_sha.as_str())
        );
        assert_ne!(
            elan_checker.active_sandbox(),
            Some(crate::ActiveSandbox::None),
            "elan-resolved unpinned run must use active ExecSeal containment"
        );
        assert!(!elan_sentinel.exists(), "elan proxy binary must never execute under ExecSeal");

        // 3. Under explicit `SandboxMode::Unsandboxed` (tainted receipt with
        //    `elaboration_sandbox: "none"`), the opaque wrapper succeeds and
        //    records `exec_lean`'s digest; switching back to contained mode on
        //    the same `Checker` invalidates the unsandboxed admission.
        let mut unsandboxed = Checker::new(&repo_root(), Some(&wrapper_lean)).unwrap();
        unsandboxed.set_allow_unpinned_lean(true);
        unsandboxed.set_sandbox_mode(crate::SandboxMode::Unsandboxed);
        let unsandboxed_req = minimal_request(&base.join("req-wrapper-unsandboxed"), None);
        let report = unsandboxed.run_target(&unsandboxed_req).unwrap();
        assert!(wrapper_sentinel.exists());
        assert_eq!(report["replay"], json!(true));
        assert_eq!(report["exactType"], json!(true));
        assert_eq!(
            report["unpinnedLean"]["leanBinarySha256"].as_str(),
            Some(real_lean_sha.as_str()),
            "unpinnedLean.leanBinarySha256 must match resolved exec_lean"
        );

        fs::remove_file(&wrapper_sentinel).unwrap();
        unsandboxed.set_sandbox_mode(crate::SandboxMode::PreferBwrapOrLandlock);
        let recheck_err = unsandboxed.tool_admission().unwrap_err();
        assert_eq!(recheck_err.code, 2, "{recheck_err}");
        assert_eq!(recheck_err.phase, "toolchain", "{recheck_err}");
        assert!(
            !wrapper_sentinel.exists(),
            "mode switch to ExecSeal must clear cached unsandboxed admission"
        );
    }

    fn nat_shadow_false_proof_request(
        dir: &Path,
        prim: &str,
        lhs_a: u64,
        lhs_b: u64,
        kernel_result: u64,
    ) -> TargetAuditRequest {
        write_target_request(
            dir,
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Prelude\nimport Init.Core\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\ndef Spec.specs (_ : Nat) : Prop := False\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    &format!(
                        "prelude\nimport Expected\n\
                         def Nat.{prim} (_ _ : Nat) : Nat := 0\n\
                         theorem h_kernel : Nat.{prim} {lhs_a} {lhs_b} = {kernel_result} := rfl\n\
                         theorem h_delta (x y : Nat) : Nat.{prim} x y = 0 := rfl\n\
                         theorem Proof.verify : Expected.claim :=\n  \
                         Nat.noConfusion ((h_delta {lhs_a} {lhs_b}).symm.trans h_kernel)\n"
                    ),
                ),
            ],
        )
    }

    #[test]
    fn live_pinned_target_audit_rejects_nat_gcd_shadowing() {
        let lean = installed_lean();
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();

        // Pinned mode: `Init.Data.Nat.Gcd` is outside `foundation-lock.json`;
        // without the reserved-kernel-namespace guard, `def Nat.gcd` would
        // compile a zero-axiom proof of `False`.
        let mut pinned = Checker::new(&repo_root(), Some(&lean)).unwrap();
        let gcd_req = nat_shadow_false_proof_request(&base.join("pinned-gcd"), "gcd", 6, 4, 2);
        let pinned_err = pinned.run_target(&gcd_req).unwrap_err();
        assert_eq!(pinned_err.code, 1, "{pinned_err}");
        assert!(pinned_err.message.contains("reserved kernel namespace Nat"), "{pinned_err}");
    }

    #[test]
    fn live_unpinned_target_audit_rejects_nat_shadowing_and_allows_eq_def() {
        let lean = installed_lean();
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();

        // Unpinned mode: `Init.Data.Nat.Bitwise.Basic` is outside the 6-module
        // foundation closure; `def Nat.land` must be rejected.
        let mut unpinned = Checker::new(&repo_root(), Some(&lean)).unwrap();
        unpinned.set_allow_unpinned_lean(true);
        let land_req = nat_shadow_false_proof_request(&base.join("unpinned-land"), "land", 1, 1, 1);
        let unpinned_err = unpinned.run_target(&land_req).unwrap_err();
        assert_eq!(unpinned_err.code, 1, "{unpinned_err}");
        assert!(unpinned_err.message.contains("reserved kernel namespace Nat"), "{unpinned_err}");

        // Even a `theorem Nat.land`, fabricated `theorem Nat.fake.eq_def`,
        // newly reserved `Int8.*`, or non-model `Trusted.*` (public or
        // private) declaration must be rejected.
        for (label, extra_decl, expected_substr) in [
            (
                "thm-land",
                "theorem Nat.land (_ _ : Nat) : True := trivial",
                "reserved kernel namespace Nat",
            ),
            (
                "fake-eq-def",
                "theorem Nat.fake.eq_def : True := trivial",
                "reserved kernel namespace Nat",
            ),
            ("int8-reserved", "def Int8.fake : Nat := 0", "reserved kernel namespace Int8"),
            ("trusted-pub", "def Trusted.fake : Nat := 0", "in Trusted namespace"),
            ("trusted-priv", "private def Trusted.privFake : Nat := 0", "in Trusted namespace"),
            ("trusted-thm-fake", "theorem Trusted.fake : True := trivial", "in Trusted namespace"),
            (
                "trusted-eq-spoof",
                "theorem Trusted.MirSemantics.UnitTheorem.spoof : True := trivial",
                "in Trusted namespace",
            ),
            (
                "trusted-priv-thm",
                "private theorem Trusted.privThm : True := trivial",
                "in Trusted namespace",
            ),
            (
                "trusted-def-sub",
                "def Trusted.MirSemantics.UnitTheorem.spoof : Nat := 0",
                "in Trusted namespace",
            ),
        ] {
            let req = write_target_request(
                &base.join(label),
                vec![
                    (
                        "Model",
                        TargetRole::Model,
                        "prelude\nimport Init.Prelude\nimport Init.Core\n\
                         namespace Trusted.MirSemantics\n\
                         structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                         def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                    ),
                    (
                        "Captured",
                        TargetRole::Capture,
                        "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                    ),
                    (
                        "Spec",
                        TargetRole::Specification,
                        "prelude\nimport Model\ndef Spec.specs (_ : Nat) : Prop := True\n",
                    ),
                    (
                        "Expected",
                        TargetRole::Expected,
                        "prelude\nimport Captured\nimport Spec\n\
                         def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                         (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                    ),
                    (
                        "Proof",
                        TargetRole::Proof,
                        &format!(
                            "prelude\nimport Expected\n{extra_decl}\n\
                             theorem Proof.verify : Expected.claim := trivial\n"
                        ),
                    ),
                ],
            );
            let err = unpinned.run_target(&req).unwrap_err();
            assert_eq!(err.code, 1, "{label}: {err}");
            assert!(
                err.message.contains(expected_substr),
                "{label}: expected {expected_substr:?} in {err}"
            );
        }

        // Legitimate Lean-synthesized equational theorems attached to an
        // existing sysroot definition (`Nat.bitwise.eq_def` from
        // `unfold Nat.bitwise`) or an imported `.model` definition
        // (`Trusted.MirSemantics.isZero.eq_1` from `simp`) must succeed and
        // replay cleanly in both unpinned and pinned modes.
        let eq_def_req = write_target_request(
            &base.join("unfold-bitwise-and-model"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Prelude\nimport Init.Core\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n\
                     def isZero : Nat → Bool\n  | 0 => true\n  | _ => false\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\ndef Spec.specs (_ : Nat) : Prop := True\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Init.Data.Nat.Bitwise.Basic\n\
                     private theorem bw_zero : Nat.bitwise and 0 0 = 0 := by\n  \
                     unfold Nat.bitwise\n  rfl\n\
                     private theorem is_zero_zero : Trusted.MirSemantics.isZero 0 = true := by\n  \
                     simp [Trusted.MirSemantics.isZero]\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     have _ := bw_zero\n  have _ := is_zero_zero\n  exact trivial\n",
                ),
            ],
        );
        let report = unpinned.run_target(&eq_def_req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let mut pinned = Checker::new(&repo_root(), Some(&lean)).unwrap();
        let pinned_report = pinned.run_target(&eq_def_req).unwrap();
        assert_eq!(pinned_report["replay"], Json::Bool(true));
        assert_eq!(pinned_report["exactType"], Json::Bool(true));
    }

    fn copy_dir_filtered(src: &Path, dst: &Path, olean_only: bool) {
        for entry in walkdir::WalkDir::new(src).follow_links(false) {
            let entry = entry.unwrap();
            let rel = entry.path().strip_prefix(src).unwrap();
            let out = dst.join(rel);
            let ft = entry.file_type();
            if ft.is_dir() {
                fs::create_dir_all(&out).unwrap();
            } else if ft.is_file() {
                let keep = !olean_only
                    || crate::toolchain::OLEAN_PARTS
                        .iter()
                        .any(|ext| out.to_string_lossy().ends_with(&format!(".{ext}")));
                if keep {
                    fs::hard_link(entry.path(), &out)
                        .or_else(|_| fs::copy(entry.path(), &out).map(|_| ()))
                        .unwrap();
                }
            }
        }
    }

    /// Real-sysroot negative test: keep the pinned `bin/lean` executable and
    /// all `foundation-lock.json` (`Init.*`) artifacts intact, confirm
    /// untampered admission passes `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`,
    /// then corrupt `Lean/Replay.olean` and assert pinned `tool_admission`
    /// rejects with policy exit code `1` and phase `"toolchain"` before
    /// `TrustedBoundary.lean` runs (`execution_began == false`).
    #[test]
    fn tool_admission_rejects_tampered_real_lean_sysroot_before_inspector_runs() {
        let real_lean = fs::canonicalize(installed_lean()).unwrap();
        let real_prefix_out =
            std::process::Command::new(&real_lean).arg("--print-prefix").output().unwrap();
        assert!(real_prefix_out.status.success());
        let real_prefix = PathBuf::from(String::from_utf8(real_prefix_out.stdout).unwrap().trim());

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let syn_prefix = base.join("sysroot");
        let copied_lean = syn_prefix.join("bin/lean");
        fs::create_dir_all(copied_lean.parent().unwrap()).unwrap();
        fs::copy(&real_lean, &copied_lean).unwrap();
        fs::set_permissions(&copied_lean, fs::Permissions::from_mode(0o755)).unwrap();

        for src_sub in ["src/lean/Init", "src/lean/Std"] {
            copy_dir_filtered(&real_prefix.join(src_sub), &syn_prefix.join(src_sub), false);
        }
        let dst_lib_lean = syn_prefix.join("lib/lean");
        fs::create_dir_all(&dst_lib_lean).unwrap();
        // Copy Lean's shared libraries in `<prefix>/lib` so sandboxed
        // `tool_admission` (which executes `--version`/`--print-prefix` inside
        // ExecSeal) can resolve `DT_RUNPATH` without escaping symlinks.
        for entry in fs::read_dir(real_prefix.join("lib")).unwrap() {
            let entry = entry.unwrap();
            let src_path = entry.path();
            if entry.file_type().unwrap().is_file() {
                let dst_path = syn_prefix.join("lib").join(entry.file_name());
                fs::hard_link(&src_path, &dst_path)
                    .or_else(|_| fs::copy(&src_path, &dst_path).map(|_| ()))
                    .unwrap();
            }
        }
        for entry in fs::read_dir(real_prefix.join("lib/lean")).unwrap() {
            let entry = entry.unwrap();
            let name = entry.file_name();
            let name_str = name.to_string_lossy();
            let src_path = entry.path();
            let dst_path = dst_lib_lean.join(&name);
            let ft = fs::symlink_metadata(&src_path).unwrap().file_type();
            if matches!(name_str.as_ref(), "Init" | "Std" | "Lean") {
                copy_dir_filtered(&src_path, &dst_path, name_str == "Lean");
            } else if ["Init.", "Std.", "Lean."].iter().any(|p| name_str.starts_with(p)) {
                if ft.is_file() {
                    fs::copy(&src_path, &dst_path).unwrap();
                }
            } else if ft.is_file() {
                fs::hard_link(&src_path, &dst_path)
                    .or_else(|_| fs::copy(&src_path, &dst_path).map(|_| ()))
                    .unwrap();
            }
        }

        // Control: untampered copy passes full pinned admission against
        // `LOCKED_LEAN_SHA256`, `foundation-lock.json`, and
        // `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`.
        let mut control = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        control.tool_admission().unwrap();
        assert!(!control.execution_began());

        // Attack: corrupt `Lean/Replay.olean` while keeping `bin/lean` and
        // all `Init.*` artifacts untouched (unlink first so hardlinks never
        // mutate the real sysroot).
        let replay_olean = dst_lib_lean.join("Lean/Replay.olean");
        assert!(replay_olean.is_file(), "missing {}", replay_olean.display());
        fs::remove_file(&replay_olean).unwrap();
        fs::write(&replay_olean, b"tampered lean replay\n").unwrap();

        let req = minimal_request(&base.join("req"), None);
        let mut tampered_target = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err = tampered_target.run_target(&req).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "toolchain"), "{err}");
        assert!(
            err.message.contains("sysroot Init/Std/Lean .olean manifest SHA-256 mismatch"),
            "{err}"
        );
        assert!(!tampered_target.execution_began());

        let mut tampered_adm = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err_adm = tampered_adm.tool_admission().unwrap_err();
        assert_eq!((err_adm.code, err_adm.phase.as_str()), (1, "toolchain"), "{err_adm}");
        assert!(
            err_adm.message.contains("sysroot Init/Std/Lean .olean manifest SHA-256 mismatch"),
            "{err_adm}"
        );
        assert!(!tampered_adm.execution_began());
    }

    /// Regression test for unauthenticated Lean runtime shared libraries:
    /// replacing a `lib/lean/*.so` file, deleting a required runtime shared
    /// library, or dropping an extra `.so` under `lib/` or `bin/` while keeping
    /// `bin/lean` and `Init`/`Std`/`Lean` `.olean`s pinned must fail closed
    /// before `SandboxRuntime::probe` or any child `lean` process executes.
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn tool_admission_rejects_tampered_or_injected_lean_runtime_shared_lib() {
        let real_lean = fs::canonicalize(installed_lean()).unwrap();
        let real_prefix_out =
            std::process::Command::new(&real_lean).arg("--print-prefix").output().unwrap();
        assert!(real_prefix_out.status.success());
        let real_prefix = PathBuf::from(String::from_utf8(real_prefix_out.stdout).unwrap().trim());

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let syn_prefix = base.join("sysroot");
        let copied_lean = syn_prefix.join("bin/lean");
        fs::create_dir_all(copied_lean.parent().unwrap()).unwrap();
        fs::copy(&real_lean, &copied_lean).unwrap();
        fs::set_permissions(&copied_lean, fs::Permissions::from_mode(0o755)).unwrap();

        copy_dir_filtered(
            &real_prefix.join("src/lean/Init"),
            &syn_prefix.join("src/lean/Init"),
            false,
        );
        copy_dir_filtered(
            &real_prefix.join("src/lean/Std"),
            &syn_prefix.join("src/lean/Std"),
            false,
        );
        let dst_lib_lean = syn_prefix.join("lib/lean");
        fs::create_dir_all(&dst_lib_lean).unwrap();
        for entry in fs::read_dir(real_prefix.join("lib")).unwrap() {
            let entry = entry.unwrap();
            let src_path = entry.path();
            if entry.file_type().unwrap().is_file() {
                let dst_path = syn_prefix.join("lib").join(entry.file_name());
                fs::hard_link(&src_path, &dst_path)
                    .or_else(|_| fs::copy(&src_path, &dst_path).map(|_| ()))
                    .unwrap();
            }
        }
        for entry in fs::read_dir(real_prefix.join("lib/lean")).unwrap() {
            let entry = entry.unwrap();
            let name = entry.file_name();
            let name_str = name.to_string_lossy();
            let src_path = entry.path();
            let dst_path = dst_lib_lean.join(&name);
            let ft = fs::symlink_metadata(&src_path).unwrap().file_type();
            if matches!(name_str.as_ref(), "Init" | "Std" | "Lean") {
                copy_dir_filtered(&src_path, &dst_path, name_str == "Lean");
            } else if ["Init.", "Std.", "Lean."].iter().any(|p| name_str.starts_with(p)) {
                if ft.is_file() {
                    fs::copy(&src_path, &dst_path).unwrap();
                }
            } else if ft.is_file() {
                fs::hard_link(&src_path, &dst_path)
                    .or_else(|_| fs::copy(&src_path, &dst_path).map(|_| ()))
                    .unwrap();
            }
        }

        // Control: untampered copy passes full pinned admission.
        let mut control = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        control.tool_admission().unwrap();
        assert!(!control.execution_began());

        // 1. Tampering with `lib/lean/libInit_shared.so` fails pre-probe.
        let init_shared = dst_lib_lean.join("libInit_shared.so");
        let real_init_shared = real_prefix.join("lib/lean/libInit_shared.so");
        fs::remove_file(&init_shared).unwrap();
        fs::write(&init_shared, b"tampered runtime shared library\n").unwrap();

        let req = minimal_request(&base.join("req"), None);
        let mut tampered_target = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err = tampered_target.run_target(&req).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (2, "toolchain"), "{err}");
        assert!(
            err.message.contains(
                "Lean runtime shared library SHA-256 mismatch for lib/lean/libInit_shared.so"
            ),
            "{err}"
        );
        assert!(!tampered_target.execution_began());

        // 2. Removing a required runtime DSO fails closed.
        fs::remove_file(&init_shared).unwrap();
        let mut missing_adm = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err_missing = missing_adm.tool_admission().unwrap_err();
        assert_eq!(
            (err_missing.code, err_missing.phase.as_str()),
            (2, "toolchain"),
            "{err_missing}"
        );
        assert!(
            err_missing.message.contains(
                "missing required Lean runtime shared library: lib/lean/libInit_shared.so"
            ),
            "{err_missing}"
        );
        assert!(!missing_adm.execution_began());

        // Restore `libInit_shared.so`, then inject an unlisted `lib/libc.so.6`.
        fs::hard_link(&real_init_shared, &init_shared)
            .or_else(|_| fs::copy(&real_init_shared, &init_shared).map(|_| ()))
            .unwrap();
        let injected_libc = syn_prefix.join("lib/libc.so.6");
        fs::write(&injected_libc, b"unlisted shadow libc\n").unwrap();
        let mut injected_adm = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err_inj = injected_adm.tool_admission().unwrap_err();
        assert_eq!((err_inj.code, err_inj.phase.as_str()), (2, "toolchain"), "{err_inj}");
        assert!(
            err_inj
                .message
                .contains("unexpected runtime shared library in Lean sysroot: lib/libc.so.6"),
            "{err_inj}"
        );
        assert!(!injected_adm.execution_began());

        // Remove `lib/libc.so.6`, then inject an unlisted `.so` into `bin/`.
        fs::remove_file(&injected_libc).unwrap();
        let injected_bin = syn_prefix.join("bin/rogue.so");
        fs::write(&injected_bin, b"unlisted bin shared library\n").unwrap();
        let mut bin_adm = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err_bin = bin_adm.tool_admission().unwrap_err();
        assert_eq!((err_bin.code, err_bin.phase.as_str()), (2, "toolchain"), "{err_bin}");
        assert!(
            err_bin
                .message
                .contains("unexpected runtime shared library in Lean sysroot: bin/rogue.so"),
            "{err_bin}"
        );
        assert!(!bin_adm.execution_began());

        // Remove `bin/rogue.so`, then point `lib/libLLVM.so` at a tampered
        // symlink target and confirm symlinked DSO substitution fails closed.
        fs::remove_file(&injected_bin).unwrap();
        let outside_so = base.join("outside.so");
        fs::write(&outside_so, b"tampered symlinked libLLVM\n").unwrap();
        let llvm_link = syn_prefix.join("lib/libLLVM.so");
        std::os::unix::fs::symlink(&outside_so, &llvm_link).unwrap();
        let mut sym_adm = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err_sym = sym_adm.tool_admission().unwrap_err();
        assert_eq!((err_sym.code, err_sym.phase.as_str()), (2, "toolchain"), "{err_sym}");
        assert!(
            err_sym
                .message
                .contains("Lean runtime shared library SHA-256 mismatch for lib/libLLVM.so"),
            "{err_sym}"
        );
        assert!(!sym_adm.execution_began());

        // Remove `lib/libLLVM.so`, then inject a symlinked directory under
        // `lib/` (`lib/rogue_dir`) and confirm directory-symlink guard fires.
        fs::remove_file(&llvm_link).unwrap();
        let rogue_target = base.join("rogue_target");
        fs::create_dir_all(&rogue_target).unwrap();
        let rogue_dir = syn_prefix.join("lib/rogue_dir");
        std::os::unix::fs::symlink(&rogue_target, &rogue_dir).unwrap();
        let mut dir_adm = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        let err_dir = dir_adm.tool_admission().unwrap_err();
        assert_eq!((err_dir.code, err_dir.phase.as_str()), (2, "toolchain"), "{err_dir}");
        assert!(
            err_dir
                .message
                .contains("unexpected symlinked directory in Lean sysroot: lib/rogue_dir"),
            "{err_dir}"
        );
        assert!(!dir_adm.execution_began());

        // Remove `lib/rogue_dir`, verify Unsandboxed pre-version guard on a
        // tampered DSO, and verify prefix-split symlinked `bin/lean`.
        fs::remove_file(&rogue_dir).unwrap();
        fs::remove_file(&init_shared).unwrap();
        fs::write(&init_shared, b"tampered runtime shared library\n").unwrap();
        let mut unsandboxed_adm = Checker::new(&repo_root(), Some(&copied_lean)).unwrap();
        unsandboxed_adm.set_sandbox_mode(crate::SandboxMode::Unsandboxed);
        let err_unsand = unsandboxed_adm.tool_admission().unwrap_err();
        assert_eq!(
            (err_unsand.code, err_unsand.phase.as_str()),
            (2, "toolchain"),
            "{err_unsand}"
        );
        assert!(
            err_unsand.message.contains(
                "Lean runtime shared library SHA-256 mismatch for lib/lean/libInit_shared.so"
            ),
            "{err_unsand}"
        );
        assert!(!unsandboxed_adm.execution_began());

        // Symlinked `bin/lean` check: `<split_prefix>/bin/lean` symlinks to
        // `copied_lean` (whose sibling `lib/lean/libInit_shared.so` is
        // tampered); Unsandboxed admission must follow the symlink and reject
        // the canonical executable's `$ORIGIN/..` DSOs before `--version`.
        let split_prefix = base.join("split-prefix");
        fs::create_dir_all(split_prefix.join("bin")).unwrap();
        std::os::unix::fs::symlink(&copied_lean, split_prefix.join("bin/lean")).unwrap();
        let mut split_adm =
            Checker::new(&repo_root(), Some(&split_prefix.join("bin/lean"))).unwrap();
        split_adm.set_sandbox_mode(crate::SandboxMode::Unsandboxed);
        let err_split = split_adm.tool_admission().unwrap_err();
        assert_eq!((err_split.code, err_split.phase.as_str()), (2, "toolchain"), "{err_split}");
        assert!(
            err_split.message.contains(
                "Lean runtime shared library SHA-256 mismatch for lib/lean/libInit_shared.so"
            ),
            "{err_split}"
        );
        assert!(!split_adm.execution_began());

        // Non-`bin/` parent check: placing the pinned `x86_64` Linux binary at
        // `<dir>/notbin/lean` next to a tampered `libInit_shared.so` must fail
        // closed before `--version` rather than skipping `$ORIGIN/..` checks.
        let notbin_root = base.join("notbin-sysroot");
        let notbin_lean = notbin_root.join("notbin/lean");
        fs::create_dir_all(notbin_lean.parent().unwrap()).unwrap();
        fs::create_dir_all(notbin_root.join("lib/lean")).unwrap();
        fs::copy(&real_lean, &notbin_lean).unwrap();
        fs::set_permissions(&notbin_lean, fs::Permissions::from_mode(0o755)).unwrap();
        fs::write(
            notbin_root.join("lib/lean/libInit_shared.so"),
            b"tampered runtime shared library\n",
        )
        .unwrap();
        let mut notbin_adm = Checker::new(&repo_root(), Some(&notbin_lean)).unwrap();
        notbin_adm.set_sandbox_mode(crate::SandboxMode::Unsandboxed);
        let err_notbin = notbin_adm.tool_admission().unwrap_err();
        assert_eq!(
            (err_notbin.code, err_notbin.phase.as_str()),
            (2, "toolchain"),
            "{err_notbin}"
        );
        assert!(
            err_notbin.message.contains("must reside under <prefix>/bin/"),
            "{err_notbin}"
        );
        assert!(!notbin_adm.execution_began());
    }

    #[test]
    fn live_spec_preflight_isolates_per_specification_library_closures() {
        let lean = installed_lean();
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();

        // `0#8` (`n#w` BitVec literal syntax) is registered by
        // `Init.Data.BitVec.Basic` (`library-lock.json`), not `Init.Prelude`.
        // `SpecWithBv` imports `Init.Data.BitVec.Basic`, whereas `SpecBare`
        // imports only `Model` (`prelude`). Preflight must check `SpecBare`
        // strictly against its own import closure and reject `0#8` at
        // `"spec-preflight"` rather than leaking `SpecWithBv`'s parser syntax.
        let bad_req = write_target_request(
            &base.join("isolated-closures-bad"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Prelude\nnamespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "SpecWithBv",
                    TargetRole::Specification,
                    "prelude\nimport Model\nimport Init.Data.BitVec.Basic\n\
                     def SpecWithBv.ok : Prop := (0#8) = (0#8)\n",
                ),
                (
                    "SpecBare",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def SpecBare.specs (_ : Nat) : Prop := (0#8) = (0#8)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport SpecWithBv\nimport SpecBare\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program SpecBare.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := rfl\n",
                ),
            ],
        );
        let mut checker = Checker::new(&repo_root(), Some(&lean)).unwrap();
        let err = checker.run_target(&bad_req).unwrap_err();
        assert_eq!(err.code, 1, "expected policy rejection: {err}");
        assert_eq!(err.phase, "spec-preflight", "expected spec-preflight rejection: {err}");
        assert!(
            err.message.contains("SpecBare"),
            "expected SpecBare parse failure in spec-preflight, got: {err}"
        );

        // Foundation-closure isolation: infix `=` is registered by
        // `Init.Notation` (part of `foundation_graph`), not `Init.Prelude`.
        // Even when `Proof` imports `Init.Notation`, `SpecFoundBad` (`prelude`,
        // importing only `Model` -> `Init.Prelude`) must be preflighted strictly
        // against its own `{"Init.Prelude"}` foundation closure and rejected at
        // `"spec-preflight"` rather than elaborating under `Init.Notation`.
        let bad_fnd_req = write_target_request(
            &base.join("isolated-fnd-closures-bad"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Prelude\nnamespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "SpecFoundBad",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def SpecFoundBad.specs (n : Nat) : Prop := n = n\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport SpecFoundBad\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program SpecFoundBad.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Init.Notation\nimport Expected\n\
                     theorem Proof.verify : Expected.claim := rfl\n",
                ),
            ],
        );
        let mut fnd_checker = Checker::new(&repo_root(), Some(&lean)).unwrap();
        let fnd_err = fnd_checker.run_target(&bad_fnd_req).unwrap_err();
        assert_eq!(fnd_err.code, 1, "expected policy rejection: {fnd_err}");
        assert_eq!(
            fnd_err.phase, "spec-preflight",
            "expected spec-preflight rejection before compilation: {fnd_err}"
        );
        assert!(
            fnd_err.message.contains("SpecFoundBad"),
            "expected SpecFoundBad parse failure in spec-preflight, got: {fnd_err}"
        );

        // Control: when `Spec` uses only `Init.Prelude` syntax (`Eq n n`) while
        // `SpecWithBv` uses `0#8`, both distinct closure groups pass preflight
        // and full verification succeeds.
        let good_req = write_target_request(
            &base.join("isolated-closures-good"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Prelude\nnamespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "SpecWithBv",
                    TargetRole::Specification,
                    "prelude\nimport Model\nimport Init.Data.BitVec.Basic\n\
                     def SpecWithBv.ok : Prop := (0#8) = (0#8)\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (n : Nat) : Prop := Eq n n\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport SpecWithBv\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := rfl\n",
                ),
            ],
        );
        let mut ok_checker = Checker::new(&repo_root(), Some(&lean)).unwrap();
        let report = ok_checker.run_target(&good_req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
    }
}

#[cfg(all(test, unix))]
mod tests {
    use std::{ffi::OsStr, fs};

    use super::{
        unpinned_admission_tests::{minimal_request, write_target_request},
        *,
    };
    use crate::toolchain::LOCKED_LEAN_SHA256;

    mod embedded {
        include!(concat!(env!("OUT_DIR"), "/bundled_resources.rs"));

        pub fn entries() -> &'static [(&'static str, &'static str)] {
            let _ = CORRESPONDENCE_PROVENANCE_JSON;
            BUNDLE
        }
    }

    struct EmbeddedBundle {
        root: PathBuf,
        model_modules: Vec<TargetModule>,
        theory_modules: Vec<TargetModule>,
    }

    impl EmbeddedBundle {
        /// Materialize `cargo-anneal`'s embedded trusted and theory bundles
        /// into `root` just as `verify.rs` does, so `target::tests` runs
        /// without reaching outside the package (including from an unpacked
        /// `cargo package` tarball).
        fn materialize(root: &Path) -> Self {
            let mut model_modules = Vec::new();
            let mut theory_modules = Vec::new();
            for &(relative, text) in embedded::entries() {
                assert!(
                    !relative.starts_with("theory/"),
                    "trusted bundle must not contain theory source: {relative}"
                );
                let path = root.join(relative);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(&path, text.as_bytes()).unwrap();
                let sha = sha256_file(&path, "fixture").unwrap();
                if let Some(rest) =
                    relative.strip_prefix("trusted/lean/").and_then(|s| s.strip_suffix(".lean"))
                {
                    model_modules.push(TargetModule {
                        module: rest.replace('/', "."),
                        source: path,
                        expected_sha256: sha,
                        role: TargetRole::Model,
                    });
                }
            }
            let bundled_theory =
                crate::bundle::embedded_theory_bundle().expect("embedded theory bundle");
            for entry in bundled_theory.modules {
                let path = root.join(&entry.path);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(&path, entry.content.as_bytes()).unwrap();
                let rest = entry
                    .path
                    .strip_prefix("theory/")
                    .and_then(|s| s.strip_suffix(".lean"))
                    .expect("validated theory bundle path");
                theory_modules.push(TargetModule {
                    module: rest.replace('/', "."),
                    source: path,
                    expected_sha256: entry.sha256,
                    role: TargetRole::Proof,
                });
            }
            Self { root: root.to_path_buf(), model_modules, theory_modules }
        }

        fn attach(&self, req: &mut TargetAuditRequest, include_model: bool) {
            if include_model {
                req.modules.extend(self.model_modules.iter().cloned());
            }
            req.modules.extend(self.theory_modules.iter().cloned());
        }

        /// Assert that `sources`, `compiled_lib_dir`, and optional `export_dir`
        /// retain every module in `expected_retained` and prune every other
        /// bundled `Anneal.*` theory module (plus `extra_unimported`), without
        /// hardcoding the global theory inventory in each test.
        fn assert_exact_theory_retention(
            &self,
            sources: &BTreeSet<&str>,
            compiled_lib_dir: &Path,
            export_dir: Option<&Path>,
            expected_retained: &[&str],
            extra_unimported: &[&str],
        ) {
            let expected: BTreeSet<&str> = expected_retained.iter().copied().collect();
            for module in &expected {
                assert!(sources.contains(module), "missing {module} in {sources:?}");
                let rel_olean = format!("{}.olean", module.replace('.', "/"));
                assert!(
                    compiled_lib_dir.join(&rel_olean).is_file(),
                    "missing compiled {rel_olean}"
                );
                if let Some(dir) = export_dir {
                    assert!(dir.join(&rel_olean).is_file(), "missing exported {rel_olean}");
                }
            }
            for module in self
                .theory_modules
                .iter()
                .map(|m| m.module.as_str())
                .chain(extra_unimported.iter().copied())
            {
                if expected.contains(module) {
                    continue;
                }
                assert!(
                    !sources.contains(module),
                    "unexpected unimported theory module {module} in {sources:?}"
                );
                let rel_olean = format!("{}.olean", module.replace('.', "/"));
                assert!(
                    !compiled_lib_dir.join(&rel_olean).exists(),
                    "unexpected compiled {rel_olean}"
                );
                if let Some(dir) = export_dir {
                    assert!(!dir.join(&rel_olean).exists(), "unexpected exported {rel_olean}");
                }
            }
        }
    }

    /// Resolve an explicitly configured, pinned Lean 4.34.1 binary from
    /// `(ANNEAL_LEAN, ANNEAL_TEST_INSTALL_ROOT)`.
    ///
    /// Returns `None` when neither variable is set (or both are empty),
    /// skipping live Lean tests without probing ambient `$HOME/.elan` or
    /// `$XDG_CACHE_HOME` installs. Panics when either variable is configured to
    /// a missing path or a binary whose SHA-256 differs from
    /// [`LOCKED_LEAN_SHA256`], so toolchain-equipped CI jobs cannot silently
    /// skip live tests.
    fn explicit_verified_lean_from(
        anneal_lean: Option<&OsStr>,
        install_root: Option<&OsStr>,
    ) -> Option<PathBuf> {
        let (source, path) = if let Some(lean) = anneal_lean.filter(|v| !v.is_empty()) {
            ("ANNEAL_LEAN", PathBuf::from(lean))
        } else {
            let root = install_root.filter(|v| !v.is_empty())?;
            ("ANNEAL_TEST_INSTALL_ROOT", Path::new(root).join("lean/bin/lean"))
        };
        assert!(
            path.is_file(),
            "{source} does not point to a Lean binary file: {}",
            path.display()
        );
        let digest = sha256_file(&path, "test")
            .unwrap_or_else(|err| panic!("{source} failed to hash {}: {err}", path.display()));
        assert!(
            LOCKED_LEAN_SHA256.contains(&digest.as_str()),
            "{source} Lean binary {} has unpinned SHA-256 {digest}",
            path.display()
        );
        Some(path)
    }

    fn explicit_verified_lean() -> Option<PathBuf> {
        explicit_verified_lean_from(
            std::env::var_os("ANNEAL_LEAN").as_deref(),
            std::env::var_os("ANNEAL_TEST_INSTALL_ROOT").as_deref(),
        )
    }

    #[test]
    fn demand_driven_theory_bfs_prunes_unused_and_preserves_role_edges() {
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let mut req = minimal_request(&base.join("bfs"), None);
        for extra in ["Anneal.Extra", "Anneal.MirWp", "Anneal.Helper"] {
            let path = base.join("bfs").join(format!("{extra}.lean"));
            fs::write(&path, "prelude\n").unwrap();
            req.modules.push(TargetModule {
                module: extra.to_owned(),
                expected_sha256: sha256_file(&path, "fixture").unwrap(),
                source: path,
                role: TargetRole::Proof,
            });
        }
        let mk_edge = |m: &str| ImportEdge {
            module: m.to_owned(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        };
        let mut imports: BTreeMap<String, Vec<ImportEdge>> = BTreeMap::from([
            ("Model".to_owned(), vec![]),
            ("Captured".to_owned(), vec![mk_edge("Model")]),
            ("Spec".to_owned(), vec![mk_edge("Model")]),
            ("Expected".to_owned(), vec![mk_edge("Captured"), mk_edge("Spec")]),
            ("Proof".to_owned(), vec![mk_edge("Expected")]),
            ("Anneal.Extra".to_owned(), vec![]),
            ("Anneal.MirWp".to_owned(), vec![mk_edge("Model")]),
            ("Anneal.Helper".to_owned(), vec![mk_edge("Anneal.Extra")]),
        ]);

        // 1. None of the bundled `Anneal.*` modules are imported.
        let retained_none = reachable_target_modules(&req, &imports);
        assert!(!retained_none.contains("Anneal.Extra"));
        assert!(!retained_none.contains("Anneal.MirWp"));
        assert!(!retained_none.contains("Anneal.Helper"));
        for seed in ["Model", "Captured", "Spec", "Expected", "Proof"] {
            assert!(retained_none.contains(seed), "missing seed {seed}");
        }

        // 2. Transitive `Proof -> Anneal.Helper -> Anneal.Extra` retains both
        //    reachable theory modules while still pruning `Anneal.MirWp`.
        imports.get_mut("Proof").unwrap().push(mk_edge("Anneal.Helper"));
        let retained_trans = reachable_target_modules(&req, &imports);
        assert!(retained_trans.contains("Anneal.Helper"));
        assert!(retained_trans.contains("Anneal.Extra"));
        assert!(!retained_trans.contains("Anneal.MirWp"));

        // 3. A forbidden `Spec -> Anneal.MirWp` edge retains `Anneal.MirWp` so
        //    the downstream `TargetRole::allows` check still rejects it.
        imports.get_mut("Spec").unwrap().push(mk_edge("Anneal.MirWp"));
        let retained_spec = reachable_target_modules(&req, &imports);
        assert!(retained_spec.contains("Anneal.MirWp"));

        // 4. Setting `theorem_module` to a bundled `Anneal.*` module keeps it
        //    as a seed even with no incoming import edges.
        imports.get_mut("Proof").unwrap().retain(|e| e.module != "Anneal.Helper");
        req.theorem_module = "Anneal.Extra".to_owned();
        let retained_thm = reachable_target_modules(&req, &imports);
        assert!(retained_thm.contains("Anneal.Extra"));
        assert!(!retained_thm.contains("Anneal.Helper"));
    }

    fn parse_lean_header_imports_for_test(source: &str) -> Vec<ImportEdge> {
        let bytes = source.as_bytes();
        let mut pos = 0usize;
        let mut edges = Vec::new();
        let mut expecting_import_target = false;
        let mut import_all = false;
        let mut is_exported = false;
        let mut is_meta = false;
        while pos < bytes.len() {
            while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
                pos += 1;
            }
            if pos >= bytes.len() {
                break;
            }
            if bytes[pos..].starts_with(b"--") {
                while pos < bytes.len() && bytes[pos] != b'\n' {
                    pos += 1;
                }
                continue;
            }
            if bytes[pos..].starts_with(b"/-") {
                pos += 2;
                let mut depth = 1usize;
                while pos < bytes.len() && depth > 0 {
                    if bytes[pos..].starts_with(b"/-") {
                        depth += 1;
                        pos += 2;
                    } else if bytes[pos..].starts_with(b"-/") {
                        depth -= 1;
                        pos += 2;
                    } else {
                        pos += 1;
                    }
                }
                continue;
            }
            let start = pos;
            while pos < bytes.len()
                && !bytes[pos].is_ascii_whitespace()
                && !bytes[pos..].starts_with(b"--")
                && !bytes[pos..].starts_with(b"/-")
            {
                pos += 1;
            }
            let token = &source[start..pos];
            if expecting_import_target {
                if token == "all" {
                    import_all = true;
                    continue;
                }
                edges.push(ImportEdge {
                    module: token.to_string(),
                    import_all,
                    is_exported,
                    is_meta,
                });
                expecting_import_target = false;
                import_all = false;
                is_exported = false;
                is_meta = false;
            } else {
                match token {
                    "module" | "prelude" => {}
                    "public" => is_exported = true,
                    "meta" => is_meta = true,
                    "import" => expecting_import_target = true,
                    _ => break,
                }
            }
        }
        edges
    }

    #[test]
    fn reachable_target_modules_prunes_domain_umbrellas_on_demand() {
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        let mut base_imports: BTreeMap<String, Vec<ImportEdge>> = BTreeMap::new();
        for tm in bundle.model_modules.iter().chain(bundle.theory_modules.iter()) {
            let src = fs::read_to_string(&tm.source).unwrap();
            base_imports.insert(tm.module.clone(), parse_lean_header_imports_for_test(&src));
        }

        let mk_edge = |m: &str| ImportEdge {
            module: m.to_owned(),
            import_all: false,
            is_exported: false,
            is_meta: false,
        };

        // 1. `import Anneal.Scalar` retains strictly the 8 constructive scalar/
        //    bitvector/byte/chunking/linear-arith `Anneal.*` modules and prunes
        //    all `MirWp*`, `LoopInv`, `Wp`, `ClassicalEm`, `BitTrieLrat`,
        //    `PTree`, `SpineForce`, and `Firewall` modules.
        let mut scalar_req = minimal_request(&base.join("scalar-req"), None);
        bundle.attach(&mut scalar_req, true);
        let mut scalar_imports = base_imports.clone();
        scalar_imports.insert("Model".into(), vec![]);
        scalar_imports.insert("Captured".into(), vec![mk_edge("Model")]);
        scalar_imports.insert("Spec".into(), vec![mk_edge("Model")]);
        scalar_imports.insert("Expected".into(), vec![mk_edge("Captured"), mk_edge("Spec")]);
        scalar_imports.insert("Proof".into(), vec![mk_edge("Expected"), mk_edge("Anneal.Scalar")]);

        let scalar_retained = reachable_target_modules(&scalar_req, &scalar_imports);
        assert!(!scalar_retained.contains("Anneal"));
        let scalar_anneal: BTreeSet<&str> = scalar_retained
            .iter()
            .filter(|m| m.starts_with("Anneal."))
            .map(String::as_str)
            .collect();
        let expected_scalar_anneal = BTreeSet::from([
            "Anneal.BitVec",
            "Anneal.BitVecArith",
            "Anneal.InitLemmas",
            "Anneal.LeBytes",
            "Anneal.LinearArith",
            "Anneal.ListChunks",
            "Anneal.NatBitwise",
            "Anneal.Scalar",
        ]);
        assert_eq!(scalar_anneal.len(), 8);
        assert_eq!(scalar_anneal, expected_scalar_anneal);
        for pruned in [
            "Anneal.Wp",
            "Anneal.MirWp",
            "Anneal.MirWp.Core",
            "Anneal.MirWp.Scalars",
            "Anneal.MirWp.Execution",
            "Anneal.MirWp.Reflection",
            "Anneal.LoopInv",
            "Anneal.ClassicalEm",
            "Anneal.BitTrieLrat",
            "Anneal.PTree",
            "Anneal.SpineForce",
            "Anneal.Firewall",
        ] {
            assert!(!scalar_retained.contains(pruned), "expected {pruned} to be pruned");
        }

        // 2. `import Anneal.Wp` retains strictly the 8 MIR WP + loop-invariant
        //    `Anneal.*` modules and prunes unused `Scalar`, `BitVec*`,
        //    `InitLemmas`, `LeBytes`, `ListChunks`, `LinearArith`,
        //    `BitTrieLrat`, `PTree`, `SpineForce`, `ClassicalEm`, and
        //    `Firewall`.
        let mut wp_req = minimal_request(&base.join("wp-req"), None);
        bundle.attach(&mut wp_req, true);
        let mut wp_imports = base_imports;
        wp_imports.insert("Model".into(), vec![]);
        wp_imports.insert("Captured".into(), vec![mk_edge("Model")]);
        wp_imports.insert("Spec".into(), vec![mk_edge("Model")]);
        wp_imports.insert("Expected".into(), vec![mk_edge("Captured"), mk_edge("Spec")]);
        wp_imports.insert("Proof".into(), vec![mk_edge("Expected"), mk_edge("Anneal.Wp")]);

        let wp_retained = reachable_target_modules(&wp_req, &wp_imports);
        assert!(!wp_retained.contains("Anneal"));
        let wp_anneal: BTreeSet<&str> =
            wp_retained.iter().filter(|m| m.starts_with("Anneal.")).map(String::as_str).collect();
        let expected_wp_anneal = BTreeSet::from([
            "Anneal.LoopInv",
            "Anneal.MirWp",
            "Anneal.MirWp.Core",
            "Anneal.MirWp.Execution",
            "Anneal.MirWp.Reflection",
            "Anneal.MirWp.Scalars",
            "Anneal.NatBitwise",
            "Anneal.Wp",
        ]);
        assert_eq!(wp_anneal.len(), 8);
        assert_eq!(wp_anneal, expected_wp_anneal);
        for pruned in [
            "Anneal.Scalar",
            "Anneal.BitVec",
            "Anneal.BitVecArith",
            "Anneal.InitLemmas",
            "Anneal.LeBytes",
            "Anneal.ListChunks",
            "Anneal.LinearArith",
            "Anneal.BitTrieLrat",
            "Anneal.PTree",
            "Anneal.SpineForce",
            "Anneal.ClassicalEm",
            "Anneal.Firewall",
        ] {
            assert!(!wp_retained.contains(pruned), "expected {pruned} to be pruned");
        }
    }

    #[test]
    fn explicit_verified_lean_gates_and_fails_closed() {
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let empty = OsStr::new("");

        assert_eq!(explicit_verified_lean_from(None, None), None);
        assert_eq!(explicit_verified_lean_from(Some(empty), Some(empty)), None);

        let panic_message = |anneal_lean: Option<&OsStr>, install_root: Option<&OsStr>| {
            let err =
                std::panic::catch_unwind(|| explicit_verified_lean_from(anneal_lean, install_root))
                    .expect_err("expected fail-closed panic");
            err.downcast_ref::<String>()
                .cloned()
                .or_else(|| err.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .expect("string panic payload")
        };

        let missing_lean = base.join("missing-lean");
        let msg = panic_message(Some(missing_lean.as_os_str()), None);
        assert!(msg.contains("ANNEAL_LEAN"), "{msg}");
        assert!(msg.contains("Lean binary file"), "{msg}");

        let missing_root = base.join("missing-root");
        let msg = panic_message(Some(empty), Some(missing_root.as_os_str()));
        assert!(msg.contains("ANNEAL_TEST_INSTALL_ROOT"), "{msg}");
        assert!(msg.contains("Lean binary file"), "{msg}");

        let bogus_lean = base.join("bogus-lean");
        fs::write(&bogus_lean, b"not lean").unwrap();
        let msg = panic_message(Some(bogus_lean.as_os_str()), Some(missing_root.as_os_str()));
        assert!(msg.contains("ANNEAL_LEAN"), "{msg}");
        assert!(msg.contains("unpinned SHA-256"), "{msg}");

        let bogus_root = base.join("bogus-root");
        let bogus_root_lean = bogus_root.join("lean/bin/lean");
        fs::create_dir_all(bogus_root_lean.parent().unwrap()).unwrap();
        fs::write(&bogus_root_lean, b"not lean").unwrap();
        let msg = panic_message(None, Some(bogus_root.as_os_str()));
        assert!(msg.contains("ANNEAL_TEST_INSTALL_ROOT"), "{msg}");
        assert!(msg.contains("unpinned SHA-256"), "{msg}");
    }

    #[test]
    fn live_demand_driven_bundled_theory_pruning() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let attach_mir_wp_and_unused = |req: &mut TargetAuditRequest, include_model: bool| {
            bundle.attach(req, include_model);
            req.modules.push(TargetModule {
                module: "Anneal.Unused".to_owned(),
                source: unused_path.clone(),
                expected_sha256: unused_sha.clone(),
                role: TargetRole::Proof,
            });
        };

        // 1. When `Proof` does NOT import `Anneal.MirWp` or `Anneal.Unused`,
        //    neither is compiled nor listed in provenance (`sources`).
        let mut req_unimported = minimal_request(&base.join("unimported"), None);
        attach_mir_wp_and_unused(&mut req_unimported, false);
        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report_unimported = checker.run_target(&req_unimported).unwrap();
        assert_eq!(report_unimported["replay"], Json::Bool(true));
        assert_eq!(report_unimported["exactType"], Json::Bool(true));
        let sources_unimported: BTreeSet<&str> = report_unimported["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let export_unimported = base.join("export-unimported");
        assert!(checker.export_target_oleans(&export_unimported).unwrap());
        bundle.assert_exact_theory_retention(
            &sources_unimported,
            &checker.stage.join("lib"),
            Some(&export_unimported),
            &[],
            &["Anneal.Unused"],
        );

        // 2. When `Proof` imports `Anneal.MirWp`, `Anneal.MirWp` and its
        //    transitive submodules ARE compiled and verified within the
        //    3-axiom ceiling, while unimported `Anneal.Unused` remains
        //    uncompiled and omitted.
        let mut req_with_mir_wp = write_target_request(
            &base.join("with-mir-wp"),
            vec![
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Captured.body0 : Trusted.MirAst.Body :=\n  \
                     { argumentCount := 0, isUnsafe := false, locals := [.unit],\n    \
                       basicBlocks := [{ statements := [], terminator := .return_ }],\n    \
                       identity := _root_.String.ofList [(_root_.Char.ofNat 97)] }\n\
                     def Captured.program : Trusted.MirAst.Program :=\n  \
                     { pointerWidthBits := 64, mirProfileVersion := 1, bodies := [Captured.body0], scope := .unit }\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Spec.specs : Trusted.MirSemantics.Specs where\n  \
                     safety := fun _ _ => True\n  \
                     property := fun _ => True\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.MirWp\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩\n  \
                     intro id selected h\n  \
                     cases id with\n  \
                     | zero =>\n    \
                       cases h\n    \
                       refine Anneal.MirWp.bodyVerified_of_safe rfl rfl (fun args hv _ => ?_)\n    \
                       cases args with\n    \
                       | nil => exact (Anneal.MirWp.run_initial_success (body := Captured.body0) (fuel := 4) (args := []) (value := .unit) rfl).1\n    \
                       | cons _ _ => cases hv\n  \
                     | succ n => cases n <;> cases h\n",
                ),
            ],
        );
        attach_mir_wp_and_unused(&mut req_with_mir_wp, true);
        let report_with_mir_wp = checker.run_target(&req_with_mir_wp).unwrap();
        assert_eq!(report_with_mir_wp["replay"], Json::Bool(true));
        assert_eq!(report_with_mir_wp["exactType"], Json::Bool(true));
        let sources_with_mir_wp: BTreeSet<&str> = report_with_mir_wp["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> = report_with_mir_wp["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| a.as_str().unwrap())
            .collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_with_mir_wp = base.join("export-with-mir-wp");
        assert!(checker.export_target_oleans(&export_with_mir_wp).unwrap());
        bundle.assert_exact_theory_retention(
            &sources_with_mir_wp,
            &checker.stage.join("lib"),
            Some(&export_with_mir_wp),
            &[
                "Anneal.MirWp",
                "Anneal.MirWp.Core",
                "Anneal.MirWp.Execution",
                "Anneal.MirWp.Reflection",
                "Anneal.MirWp.Scalars",
                "Anneal.NatBitwise",
            ],
            &["Anneal.Unused", "Anneal.MirWp.Canaries"],
        );

        // 3. Role isolation remains intact: `Specification -> Anneal.MirWp`
        //    is retained by BFS and rejected by `TargetRole::allows`.
        let mut req_bad_spec = write_target_request(
            &base.join("bad-spec"),
            vec![
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Captured.body0 : Trusted.MirAst.Body :=\n  \
                     { argumentCount := 0, isUnsafe := false, locals := [.unit],\n    \
                       basicBlocks := [{ statements := [], terminator := .return_ }],\n    \
                       identity := _root_.String.ofList [(_root_.Char.ofNat 97)] }\n\
                     def Captured.program : Trusted.MirAst.Program :=\n  \
                     { pointerWidthBits := 64, mirProfileVersion := 1, bodies := [Captured.body0], scope := .unit }\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Trusted.MirSemantics\nimport Anneal.MirWp\n\
                     def Spec.specs : Trusted.MirSemantics.Specs where\n  \
                     safety := fun _ _ => True\n  \
                     property := fun _ => True\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := trivial\n",
                ),
            ],
        );
        attach_mir_wp_and_unused(&mut req_bad_spec, true);
        let err = checker.run_target(&req_bad_spec).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert_eq!(err.phase, "target-role", "{err}");
        assert!(err.message.contains("Spec cannot import Anneal.MirWp"), "{err}");
    }

    #[test]
    fn live_demand_driven_anneal_bitvec_pruning_and_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let attach_bundled_theory = |req: &mut TargetAuditRequest, include_model: bool| {
            bundle.attach(req, include_model);
            req.modules.push(TargetModule {
                module: "Anneal.Unused".to_owned(),
                source: unused_path.clone(),
                expected_sha256: unused_sha.clone(),
                role: TargetRole::Proof,
            });
        };

        // 1. When `Proof` does NOT import `Anneal.BitVec` (or `Anneal.Unused`),
        //    neither is compiled nor listed in provenance (`sources`).
        let mut req_no_bv = minimal_request(&base.join("no-bv"), None);
        attach_bundled_theory(&mut req_no_bv, false);
        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report_no_bv = checker.run_target(&req_no_bv).unwrap();
        assert_eq!(report_no_bv["replay"], Json::Bool(true));
        assert_eq!(report_no_bv["exactType"], Json::Bool(true));
        let sources_no_bv: BTreeSet<&str> = report_no_bv["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let export_no_bv = base.join("export-no-bv");
        assert!(checker.export_target_oleans(&export_no_bv).unwrap());
        bundle.assert_exact_theory_retention(
            &sources_no_bv,
            &checker.stage.join("lib"),
            Some(&export_no_bv),
            &[],
            &["Anneal.Unused"],
        );

        // 2. When `Proof` imports `Anneal.BitVec`, it IS compiled and verified
        //    using `disjoint_or_injective`, `tnum_and_sound`, and
        //    `common_prefix_of_bounds` within the 3-axiom ceiling, while
        //    unimported `Anneal.Unused` remains uncompiled and omitted.
        let mut req_with_bv = write_target_request(
            &base.join("with-bv"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Data.BitVec.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 64\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (w : Nat) : Prop :=\n  \
                     (∀ (mask a1 b1 a2 b2 : BitVec w),\n    \
                       a1 &&& mask = 0#w → a2 &&& mask = 0#w →\n    \
                       b1 &&& ~~~mask = 0#w → b2 &&& ~~~mask = 0#w →\n    \
                       a1 ||| b1 = a2 ||| b2 → a1 = a2 ∧ b1 = b2) ∧\n  \
                     (∀ (m1 m2 x y v1 v2 : BitVec w),\n    \
                       x &&& ~~~m1 = v1 &&& ~~~m1 → y &&& ~~~m2 = v2 &&& ~~~m2 →\n    \
                       (x &&& y) &&& ~~~(((m1 &&& m2) ||| (m1 &&& v2) ||| (v1 &&& m2))) =\n    \
                       (v1 &&& v2) &&& ~~~(((m1 &&& m2) ||| (m1 &&& v2) ||| (v1 &&& m2)))) ∧\n  \
                     (∀ (k : Nat) (umin x umax : BitVec w),\n    \
                       umin ≤ x → x ≤ umax →\n    \
                       (umin ^^^ umax) &&& ~~~(BitVec.ofNat w (2 ^ k - 1)) = 0#w →\n    \
                       (x ^^^ umin) &&& ~~~(BitVec.ofNat w (2 ^ k - 1)) = 0#w)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.BitVec\n\
                     theorem Proof.verify : Expected.claim :=\n  \
                     ⟨fun _ _ _ _ _ ha1 ha2 hb1 hb2 hor =>\n    \
                       Anneal.BitVec.disjoint_or_injective ha1 ha2 hb1 hb2 hor,\n   \
                      fun _ _ _ _ _ _ h1 h2 =>\n    \
                       Anneal.BitVec.tnum_and_sound h1 h2,\n   \
                      fun _ _ _ _ hlo hhi hpref =>\n    \
                       Anneal.BitVec.common_prefix_of_bounds hlo hhi hpref⟩\n",
                ),
            ],
        );
        attach_bundled_theory(&mut req_with_bv, false);
        let report_with_bv = checker.run_target(&req_with_bv).unwrap();
        assert_eq!(report_with_bv["replay"], Json::Bool(true));
        assert_eq!(report_with_bv["exactType"], Json::Bool(true));
        let sources_with_bv: BTreeSet<&str> = report_with_bv["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> = report_with_bv["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| a.as_str().unwrap())
            .collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_with_bv = base.join("export-with-bv");
        assert!(checker.export_target_oleans(&export_with_bv).unwrap());
        bundle.assert_exact_theory_retention(
            &sources_with_bv,
            &checker.stage.join("lib"),
            Some(&export_with_bv),
            &["Anneal.NatBitwise", "Anneal.BitVec"],
            &["Anneal.Unused"],
        );

        // 3. Role isolation remains intact: `Specification -> Anneal.BitVec`
        //    is retained by BFS and rejected by `TargetRole::allows`.
        let mut req_bad_spec = write_target_request(
            &base.join("bad-spec"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Prelude\nimport Init.Core\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\nimport Anneal.BitVec\n\
                     def Spec.specs (_ : Nat) : Prop := True\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := trivial\n",
                ),
            ],
        );
        attach_bundled_theory(&mut req_bad_spec, false);
        let err = checker.run_target(&req_bad_spec).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert_eq!(err.phase, "target-role", "{err}");
        assert!(err.message.contains("Spec cannot import Anneal.BitVec"), "{err}");

        // 4. Importing both `Anneal.MirWp` and `Anneal.BitVec` together in one
        //    `Proof` replays cleanly with no duplicate declarations.
        let mut req_both = write_target_request(
            &base.join("both-mirwp-bitvec"),
            vec![
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Captured.body0 : Trusted.MirAst.Body :=\n  \
                     { argumentCount := 0, isUnsafe := false, locals := [.unit],\n    \
                       basicBlocks := [{ statements := [], terminator := .return_ }],\n    \
                       identity := _root_.String.ofList [(_root_.Char.ofNat 97)] }\n\
                     def Captured.program : Trusted.MirAst.Program :=\n  \
                     { pointerWidthBits := 64, mirProfileVersion := 1, bodies := [Captured.body0], scope := .unit }\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Init.Data.BitVec.Basic\nimport Trusted.MirSemantics\n\
                     def Spec.specs : Trusted.MirSemantics.Specs where\n  \
                     safety := fun _ _ => True\n  \
                     property := fun _ =>\n    \
                     (∀ (mask a1 b1 a2 b2 : BitVec 8),\n      \
                       a1 &&& mask = 0#8 → a2 &&& mask = 0#8 →\n      \
                       b1 &&& ~~~mask = 0#8 → b2 &&& ~~~mask = 0#8 →\n      \
                       a1 ||| b1 = a2 ||| b2 → a1 = a2 ∧ b1 = b2)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.MirWp\nimport Anneal.BitVec\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩\n  \
                     · intro id selected h\n    \
                       cases id with\n    \
                       | zero =>\n      \
                         cases h\n      \
                         refine Anneal.MirWp.bodyVerified_of_safe rfl rfl (fun args hv _ => ?_)\n      \
                         cases args with\n      \
                         | nil => exact (Anneal.MirWp.run_initial_success (body := Captured.body0) (fuel := 4) (args := []) (value := .unit) rfl).1\n      \
                         | cons _ _ => cases hv\n    \
                       | succ n => cases n <;> cases h\n  \
                     · exact fun _ _ _ _ _ ha1 ha2 hb1 hb2 hor =>\n      \
                       Anneal.BitVec.disjoint_or_injective ha1 ha2 hb1 hb2 hor\n",
                ),
            ],
        );
        attach_bundled_theory(&mut req_both, true);
        let report_both = checker.run_target(&req_both).unwrap();
        assert_eq!(report_both["replay"], Json::Bool(true));
        assert_eq!(report_both["exactType"], Json::Bool(true));
        let sources_both: BTreeSet<&str> = report_both["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        bundle.assert_exact_theory_retention(
            &sources_both,
            &checker.stage.join("lib"),
            None,
            &[
                "Anneal.NatBitwise",
                "Anneal.BitVec",
                "Anneal.MirWp",
                "Anneal.MirWp.Core",
                "Anneal.MirWp.Execution",
                "Anneal.MirWp.Reflection",
                "Anneal.MirWp.Scalars",
            ],
            &["Anneal.Unused", "Anneal.MirWp.Canaries"],
        );
    }

    #[test]
    fn live_demand_driven_lebytes_and_listchunks_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        let mut req = write_target_request(
            &base.join("lebytes-listchunks"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Data.BitVec.Basic\nimport Init.Data.List.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 4\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (k : Nat) : Prop :=\n  \
                     (∀ (a1 a2 : BitVec 32) (b1 b2 : BitVec 64),\n    \
                       [BitVec.ofNat 8 a1.toNat, BitVec.ofNat 8 (a1.toNat / 2 ^ 8),\n     \
                        BitVec.ofNat 8 (a1.toNat / 2 ^ 16), BitVec.ofNat 8 (a1.toNat / 2 ^ 24)] ++\n    \
                       [BitVec.ofNat 8 b1.toNat, BitVec.ofNat 8 (b1.toNat / 2 ^ 8),\n     \
                        BitVec.ofNat 8 (b1.toNat / 2 ^ 16), BitVec.ofNat 8 (b1.toNat / 2 ^ 24),\n     \
                        BitVec.ofNat 8 (b1.toNat / 2 ^ 32), BitVec.ofNat 8 (b1.toNat / 2 ^ 40),\n     \
                        BitVec.ofNat 8 (b1.toNat / 2 ^ 48), BitVec.ofNat 8 (b1.toNat / 2 ^ 56)] =\n    \
                       [BitVec.ofNat 8 a2.toNat, BitVec.ofNat 8 (a2.toNat / 2 ^ 8),\n     \
                        BitVec.ofNat 8 (a2.toNat / 2 ^ 16), BitVec.ofNat 8 (a2.toNat / 2 ^ 24)] ++\n    \
                       [BitVec.ofNat 8 b2.toNat, BitVec.ofNat 8 (b2.toNat / 2 ^ 8),\n     \
                        BitVec.ofNat 8 (b2.toNat / 2 ^ 16), BitVec.ofNat 8 (b2.toNat / 2 ^ 24),\n     \
                        BitVec.ofNat 8 (b2.toNat / 2 ^ 32), BitVec.ofNat 8 (b2.toNat / 2 ^ 40),\n     \
                        BitVec.ofNat 8 (b2.toNat / 2 ^ 48), BitVec.ofNat 8 (b2.toNat / 2 ^ 56)] →\n    \
                       a1 = a2 ∧ b1 = b2) ∧\n  \
                     (∀ (n : Nat), 1 < n → 1 < k → (n + k - 1) / k < n)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.LeBytes\nimport Anneal.ListChunks\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     constructor\n  \
                     · intro a1 a2 b1 b2 h\n    \
                       rw [← Anneal.LeBytes.toLeBytes_u32_eq a1, ← Anneal.LeBytes.toLeBytes_u64_eq b1,\n        \
                           ← Anneal.LeBytes.toLeBytes_u32_eq a2, ← Anneal.LeBytes.toLeBytes_u64_eq b2] at h\n    \
                       exact Anneal.LeBytes.toLeBytes_append_injective h\n  \
                     · intro n hn hk\n    \
                       have hk0 : 0 < Captured.program := by decide\n    \
                       dsimp only [Expected.claim, Trusted.MirSemantics.UnitTheorem, Spec.specs] at hk ⊢\n    \
                       rw [← Anneal.ListChunks.divCeil_eq_add_sub_div hk0]\n    \
                       exact Anneal.ListChunks.divCeil_lt_self hn hk\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            None,
            &["Anneal.LeBytes", "Anneal.ListChunks"],
            &[],
        );
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
    }

    #[test]
    fn live_demand_driven_bitvec_arith_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-bv-arith"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Data.BitVec.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 64\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (w : Nat) : Prop :=\n  \
                     (∀ (m1 m2 x1 x2 v1 v2 : BitVec w),\n    \
                       x1 &&& ~~~m1 = v1 &&& ~~~m1 →\n    \
                       x2 &&& ~~~m2 = v2 &&& ~~~m2 →\n    \
                       v1 &&& m1 = 0#w →\n    \
                       v2 &&& m2 = 0#w →\n    \
                       let sm := m1 + m2\n    \
                       let sv := v1 + v2\n    \
                       let mu := ((sm + sv) ^^^ sv) ||| (m1 ||| m2)\n    \
                       (x1 + x2) &&& ~~~mu = (sv &&& ~~~mu) &&& ~~~mu) ∧\n  \
                     (∃ f : BitVec 64 → BitVec 64,\n    \
                       (∀ x, f (f x) = x) ∧\n    \
                       (∀ x y, f x = f y → x = y) ∧\n    \
                       (∀ (x : BitVec 64) (i : Nat), i < 64 →\n      \
                         (f x).getLsbD i = x.getLsbD (i % 8 + 8 * (7 - i / 8)))) ∧\n  \
                     (∀ (umin x umax : BitVec w) (kmin k kmax : Nat),\n    \
                       umin ≤ x → x ≤ umax → kmin ≤ k → k ≤ kmax →\n    \
                       umin >>> kmax ≤ x >>> k ∧ x >>> k ≤ umax >>> kmin)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.BitVecArith\n\
                     theorem Proof.verify : Expected.claim :=\n  \
                     ⟨fun _ _ _ _ _ _ h1 h2 hc1 hc2 =>\n    \
                       Anneal.BitVecArith.tnum_add_sound h1 h2 hc1 hc2,\n   \
                      ⟨Anneal.BitVecArith.bswap64,\n    \
                       Anneal.BitVecArith.bswap64_bswap64,\n    \
                       fun _ _ h => Anneal.BitVecArith.bswap64_injective h,\n    \
                       fun x i hi => by\n      \
                         change Anneal.BitVec.getLsbD (Anneal.BitVecArith.bswapBytes 8 x) i =\n        \
                           Anneal.BitVec.getLsbD x (Nat.mod i 8 + 8 * (8 - 1 - Nat.div i 8))\n      \
                         rw [Anneal.BitVecArith.getLsbD_bswapBytes, decide_eq_true hi,\n        \
                           Bool.true_and]⟩,\n   \
                      fun _ _ _ _ _ _ hlo hhi hklo hkhi =>\n    \
                       Anneal.BitVecArith.range_ushr_sound hlo hhi hklo hkhi⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-bv-arith");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.NatBitwise", "Anneal.BitVec", "Anneal.BitVecArith"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn live_demand_driven_loopinv_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-loopinv"),
            vec![
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Captured.u32Ty : Trusted.MirAst.MirTy := .int .i32 false\n\
                     def Captured.body0 : Trusted.MirAst.Body :=\n  \
                     { argumentCount := 1, isUnsafe := false,\n    \
                       locals := [Captured.u32Ty, Captured.u32Ty],\n    \
                       basicBlocks := [\n      \
                         { statements := [.assign ⟨0, []⟩ (.use (.constant ⟨Captured.u32Ty, .scalar (BitVec.ofNat 128 0)⟩))],\n        \
                           terminator := .goto 1 },\n      \
                         { statements := [],\n        \
                           terminator := .switchInt (.copy ⟨1, []⟩) { branches := [(BitVec.ofNat 128 0, 3)], otherwise := 2 } },\n      \
                         { statements := [\n            \
                             .assign ⟨1, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (.constant ⟨Captured.u32Ty, .scalar (BitVec.ofNat 128 1)⟩)),\n            \
                             .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.constant ⟨Captured.u32Ty, .scalar (BitVec.ofNat 128 1)⟩))],\n        \
                           terminator := .goto 1 },\n      \
                         { statements := [], terminator := .return_ }],\n    \
                       identity := \"count_down\" }\n\
                     def Captured.program : Trusted.MirAst.Program :=\n  \
                     { pointerWidthBits := 64, mirProfileVersion := 1, bodies := [Captured.body0], scope := .unit }\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Spec.specs : Trusted.MirSemantics.Specs where\n  \
                     safety := fun _ _ => True\n  \
                     property := fun prog =>\n    \
                     ∀ (n : Nat), n < Nat.pow 2 32 →\n      \
                       Trusted.MirSemantics.WellFormed prog\n        \
                         { args := [.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩] } ∧\n      \
                       Trusted.MirSemantics.Behavior prog\n        \
                         { args := [.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩] }\n        \
                         (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩, ⟨[]⟩⟩)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.LoopInv\n\
                     private theorem check_arg_u32 (v : Trusted.MirSemantics.Val)\n  \
                       (h : Trusted.MirSemantics.checkVal v Captured.u32Ty = true) :\n  \
                       ∃ n, n < Nat.pow 2 32 ∧ v = .scalar ⟨.i32, false, BitVec.ofNat 128 n⟩ := by\n  \
                       let ⟨bits, hv, hTrunc⟩ := Anneal.MirWp.checkVal_int_iff.mp h\n  \
                       have hlt : bits.toNat < Nat.pow 2 32 := by\n    \
                         have h1 : bits.toNat = (Trusted.MirSemantics.truncateBits .i32 bits).toNat :=\n      \
                           congrArg BitVec.toNat hTrunc.symm\n    \
                         rw [h1, Anneal.MirWp.toNat_truncateBits]\n    \
                         exact Nat.mod_lt bits.toNat (Anneal.MirWp.intWidth_modulus_pos .i32)\n  \
                       exact ⟨bits.toNat, hlt,\n    \
                         hv.trans (congrArg (fun x => Trusted.MirSemantics.Val.scalar ⟨.i32, false, x⟩)\n      \
                           (congrArg BitVec.ofFin (Fin.eq_of_val_eq (Nat.mod_eq_of_lt bits.isLt))).symm)⟩\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩\n  \
                     · intro id selected h\n    \
                       cases id with\n    \
                       | zero =>\n      \
                         cases h\n      \
                         refine ⟨rfl, rfl, fun args hv _ => ?_⟩\n      \
                         change Trusted.MirSemantics.checkArgsMatch args [Captured.u32Ty] = true at hv\n      \
                         cases args with\n      \
                         | nil => cases hv\n      \
                         | cons v rest =>\n        \
                           cases rest with\n        \
                           | cons _ _ =>\n          \
                             change (Trusted.MirSemantics.checkVal v Captured.u32Ty && false) = true at hv\n          \
                             rw [Bool.and_false] at hv; cases hv\n        \
                           | nil =>\n          \
                             change (Trusted.MirSemantics.checkVal v Captured.u32Ty && true) = true at hv\n          \
                             rw [Bool.and_true] at hv\n          \
                             let ⟨n, hn, hvEq⟩ := check_arg_u32 v hv\n          \
                             rw [hvEq]\n          \
                             exact (Anneal.LoopInv.countDown_returns n hn).1\n    \
                       | succ n => cases n <;> cases h\n  \
                     · exact fun n hn => Anneal.LoopInv.countDown_returns n hn\n",
                ),
            ],
        );
        bundle.attach(&mut req, true);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-loopinv");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &[
                "Anneal.LoopInv",
                "Anneal.MirWp",
                "Anneal.MirWp.Core",
                "Anneal.MirWp.Execution",
                "Anneal.MirWp.Reflection",
                "Anneal.MirWp.Scalars",
                "Anneal.NatBitwise",
            ],
            &["Anneal.Unused", "Anneal.MirWp.Canaries"],
        );
    }

    #[test]
    fn live_demand_driven_spineforce_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-spineforce"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.NotationExtra\nimport Init.Data.Nat.Basic\n\
                     import Init.Data.List.Basic\nnamespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 3\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (depth : Nat) : Prop :=\n  \
                     (∀ (xs : List Nat), ∃ (f : List Nat → Nat), f xs = xs.length) ∧\n  \
                     (∀ (n : Nat), ∃ (g : Nat → Nat), g n = n + 1) ∧\n  \
                     (∃ m : Nat, 0 < m ∧ m = 9) ∧\n  \
                     (∀ i : Nat, i < depth → i < 10)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.SpineForce\n\
                     theorem Proof.verify : Expected.claim :=\n  \
                     ⟨fun xs => ⟨fun ys => Anneal.SpineForce.forceList ys List.length,\n    \
                       Anneal.SpineForce.forceList_eq xs List.length⟩,\n   \
                      fun n => ⟨fun m => Anneal.SpineForce.withStrictNat m (fun x => x + 1),\n    \
                       Anneal.SpineForce.withStrictNat_eq n (fun x => x + 1)⟩,\n   \
                      ⟨Anneal.SpineForce.runPow2 Captured.program (fun x => x + 1) 1,\n    \
                       Anneal.SpineForce.runPow2_preserves (fun x => 0 < x) (fun x => x + 1)\n      \
                         (fun _ hx => Nat.lt_trans hx (Nat.lt_succ_self _)) Captured.program 1\n      \
                         (Nat.lt_succ_self 0),\n    rfl⟩,\n   \
                      Anneal.SpineForce.checkRange_sound (fun i => decide (i < 10))\n    \
                        (fun _ h => of_decide_eq_true h) Captured.program rfl⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-spineforce");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.SpineForce"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn live_demand_driven_ptree_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-ptree"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.NotationExtra\nimport Init.Data.Nat.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 10\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (base : Nat) : Prop :=\n  \
                     (∀ (k1 k2 : Nat), k1 ≠ k2 →\n    \
                       ∃ (read1 read2 : Nat → Option Nat),\n      \
                         (∀ q, read1 q = read2 q) ∧\n      \
                         read1 k1 = some base ∧\n      \
                         read1 k2 = some (base + 20) ∧\n      \
                         (∀ q, q ≠ k1 → q ≠ k2 → read1 q = none)) ∧\n  \
                     (∃ (r1 r2 u : Nat → Option Nat),\n    \
                       (∀ k, r1 k = none ∨ r2 k = none) ∧\n    \
                       (∀ k, (match r1 k with | some x => some x | none => r2 k) = u k) ∧\n    \
                       u 1 = some base ∧ u 2 = some (base + 20) ∧\n    \
                       r1 1 = some base ∧ r2 2 = some (base + 20))\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.PTree\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     constructor\n  \
                     · intro k1 k2 hNe\n    \
                       let p1 := Anneal.PTree.natToPos k1\n    \
                       let p2 := Anneal.PTree.natToPos k2\n    \
                       have hp : p1 ≠ p2 := fun h => hNe (Anneal.PTree.natToPos_inj h)\n    \
                       let t1 := (Anneal.PTree.PTree.empty.set p1 Captured.program).set p2 \
                         (Captured.program + 20)\n    \
                       let t2 := (Anneal.PTree.PTree.empty.set p2 (Captured.program + 20)).set p1 \
                         Captured.program\n    \
                       have hComm : t1 = t2 := Anneal.PTree.ptree_set_set_comm \
                         Anneal.PTree.PTree.empty Captured.program (Captured.program + 20) hp\n    \
                       refine ⟨fun q => t1.get (Anneal.PTree.natToPos q), \
                         fun q => t2.get (Anneal.PTree.natToPos q), ?_, ?_, ?_, ?_⟩\n    \
                       · intro q\n      \
                         exact congrArg (fun m => Anneal.PTree.PTree.get m (Anneal.PTree.natToPos q)) \
                           hComm\n    \
                       · dsimp only [t1]\n      \
                         rw [Anneal.PTree.ptree_get_set_other _ _ _ _ hp.symm, \
                           Anneal.PTree.ptree_get_set_same]\n    \
                       · exact Anneal.PTree.ptree_get_set_same _ _ _\n    \
                       · intro q hq1 hq2\n      \
                         have hqp1 : p1 ≠ Anneal.PTree.natToPos q :=\n        \
                           fun h => hq1 (Anneal.PTree.natToPos_inj h).symm\n      \
                         have hqp2 : p2 ≠ Anneal.PTree.natToPos q :=\n        \
                           fun h => hq2 (Anneal.PTree.natToPos_inj h).symm\n      \
                         dsimp only [t1]\n      \
                         rw [Anneal.PTree.ptree_get_set_other _ _ _ _ hqp2, \
                           Anneal.PTree.ptree_get_set_other _ _ _ _ hqp1]\n      \
                         exact Anneal.PTree.ptree_get_empty _\n  \
                     · let goal := (Anneal.PTree.PTree.empty.set (Anneal.PTree.natToPos 1) \
                         Captured.program).set (Anneal.PTree.natToPos 2) (Captured.program + 20)\n    \
                       let req := Anneal.PTree.PTree.empty.set (Anneal.PTree.natToPos 1) \
                         Captured.program\n    \
                       let rem := Anneal.PTree.PTree.empty.set (Anneal.PTree.natToPos 2) \
                         (Captured.program + 20)\n    \
                       have hDiff : Anneal.PTree.PTree.diffWith Nat.beq goal req = some rem := rfl\n    \
                       let ⟨hDisj, hUnion⟩ :=\n      \
                         Anneal.PTree.ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true hDiff\n    \
                       refine ⟨fun k => req.get (Anneal.PTree.natToPos k), \
                         fun k => rem.get (Anneal.PTree.natToPos k), \
                         fun k => goal.get (Anneal.PTree.natToPos k), ?_, ?_, rfl, rfl, rfl, rfl⟩\n    \
                       · intro k\n      \
                         exact hDisj (Anneal.PTree.natToPos k)\n    \
                       · intro k\n      \
                         dsimp only\n      \
                         rw [← hUnion, Anneal.PTree.ptree_get_union]\n      \
                         cases Anneal.PTree.PTree.get req (Anneal.PTree.natToPos k) <;> rfl\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-ptree");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.PTree"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn live_demand_driven_bit_trie_lrat_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-bit-trie-lrat"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.NotationExtra\nimport Init.Data.Nat.Basic\n\
                     import Init.Data.List.Basic\nnamespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 6\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.diamondCnfSat (σ : Nat → Bool) : Bool :=\n  \
                     ((σ 0 || false) &&\n   \
                      (((!σ 0) || (σ 1 || (σ 2 || false))) &&\n    \
                       (((!σ 1) || (σ 3 || false)) &&\n     \
                        (((!σ 2) || (σ 3 || false)) &&\n      \
                         (((!σ 3) || false) && true)))))\n\
                     def Spec.unitPairSat (σ : Nat → Bool) : Bool :=\n  \
                     ((σ 1 || false) && (((!σ 1) || false) && true))\n\
                     def Spec.specs (depth : Nat) : Prop :=\n  \
                     depth = 6 ∧\n  \
                     (∀ (σ : Nat → Bool), Spec.diamondCnfSat σ = false) ∧\n  \
                     (∀ (σ : Nat → Bool), Spec.unitPairSat σ = false)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.BitTrieLrat\n\
                     private abbrev bOr := Anneal.BitTrieLrat.boolOr\n\
                     private abbrev bAnd := Anneal.BitTrieLrat.boolAnd\n\
                     private abbrev bBeq := Anneal.BitTrieLrat.boolBeq\n\
                     private def unitCnf : List Anneal.BitTrieLrat.Clause :=\n  \
                     [[Anneal.BitTrieLrat.mkLit 1 true], [Anneal.BitTrieLrat.mkLit 1 false]]\n\
                     private theorem boolBeq_true (b : Bool) :\n  \
                     bBeq b true = b := by cases b <;> rfl\n\
                     private theorem boolBeq_false (b : Bool) :\n  \
                     bBeq b false = !b := by cases b <;> rfl\n\
                     private theorem boolOr_eq (a b : Bool) :\n  \
                     bOr a b = (a || b) := by cases a <;> cases b <;> rfl\n\
                     private theorem boolAnd_eq (a b : Bool) :\n  \
                     bAnd a b = (a && b) := by cases a <;> cases b <;> rfl\n\
                     private theorem diamond_eval_eq (σ : Nat → Bool) :\n  \
                     Anneal.BitTrieLrat.evalCnf σ Anneal.BitTrieLrat.sampleUnsatCnf =\n    \
                     Spec.diamondCnfSat σ := by\n  \
                     change bAnd (bOr (bBeq (σ 0) true) false)\n    \
                     (bAnd (bOr (bBeq (σ 0) false) (bOr (bBeq (σ 1) true)\n      \
                     (bOr (bBeq (σ 2) true) false)))\n    \
                     (bAnd (bOr (bBeq (σ 1) false) (bOr (bBeq (σ 3) true) false))\n    \
                     (bAnd (bOr (bBeq (σ 2) false) (bOr (bBeq (σ 3) true) false))\n    \
                     (bAnd (bOr (bBeq (σ 3) false) false) true)))) = Spec.diamondCnfSat σ\n  \
                     simp only [boolBeq_true, boolBeq_false, boolOr_eq,\n    \
                     boolAnd_eq, Spec.diamondCnfSat]\n\
                     private theorem unit_eval_eq (σ : Nat → Bool) :\n  \
                     Anneal.BitTrieLrat.evalCnf σ unitCnf = Spec.unitPairSat σ := by\n  \
                     change bAnd (bOr (bBeq (σ 1) true) false)\n    \
                     (bAnd (bOr (bBeq (σ 1) false) false) true) = Spec.unitPairSat σ\n  \
                     simp only [boolBeq_true, boolBeq_false, boolOr_eq,\n    \
                     boolAnd_eq, Spec.unitPairSat]\n\
                     theorem Proof.verify : Expected.claim :=\n  \
                     ⟨rfl,\n   \
                      fun σ => (diamond_eval_eq σ).symm.trans\n     \
                        (Anneal.BitTrieLrat.checkRupProof_sound Captured.program\n       \
                          Anneal.BitTrieLrat.sampleUnsatCnf\n       \
                          Anneal.BitTrieLrat.sampleUnsatSteps rfl σ),\n   \
                      fun σ => (unit_eval_eq σ).symm.trans\n     \
                        (Anneal.BitTrieLrat.checkRupProof_sound Captured.program\n       \
                          unitCnf [.addRup 2 [] [0, 1]] rfl σ)⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-bit-trie-lrat");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.BitTrieLrat"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn live_demand_driven_linear_arith_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-linear-arith"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Data.Int.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (_ : Nat) : Prop :=\n  \
                     (∀ i n : Nat, 2 * i + 1 ≤ 2 * n → i < n) ∧\n  \
                     (∀ i n : Nat, 2 * i ≤ 2 * n + 1 → 2 * n + 1 ≤ 2 * i → False) ∧\n  \
                     (∀ (x y : Int),\n    \
                       Int.sub (Int.mul (Int.negOfNat 2) x) y ≤ Int.ofNat 5 →\n    \
                       Int.negOfNat 3 ≤ Int.neg y →\n    \
                       Int.negOfNat 4 ≤ x) ∧\n  \
                     (∀ x : Nat, 0 ≤ x)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.LinearArith\n\
                     theorem Proof.verify : Expected.claim :=\n  \
                     ⟨Anneal.LinearArith.parity_stride_lt,\n   \
                      Anneal.LinearArith.parity_cut_req_false,\n   \
                      Anneal.LinearArith.int_sub_neg_mul_lower_bound,\n   \
                      Anneal.LinearArith.nat_var_nonneg_no_hyps⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-linear-arith");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.LinearArith"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn live_omitted_program_scope_fails_elaboration() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Omitting `scope` from `Trusted.MirAst.Program` must fail Lean
        // elaboration at capture compilation time rather than defaulting to
        // `.unit` (`Trusted.MirSemantics` negative canaries already reject an
        // explicit `scope := .unit` under `CrateTheorem`).
        let mut req_missing = write_target_request(
            &base.join("missing-scope"),
            vec![
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Captured.program : Trusted.MirAst.Program :=\n  \
                     { pointerWidthBits := 64, mirProfileVersion := 1, bodies := [] }\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Trusted.MirSemantics\n\
                     def Spec.specs : Trusted.MirSemantics.Specs := {}\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.CrateTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\n\
                     theorem Proof.verify : Expected.claim := by exact False.elim sorry\n",
                ),
            ],
        );
        bundle.attach(&mut req_missing, true);
        let mut checker_missing = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let err_missing = checker_missing.run_target(&req_missing).unwrap_err();
        assert_eq!(err_missing.code, 1, "expected elaboration failure: {err_missing}");
        assert_eq!(err_missing.phase, "compile-Captured", "{err_missing}");
        assert!(err_missing.message.contains("Fields missing: `scope`"), "{err_missing}");
    }

    #[test]
    fn live_demand_driven_init_lemmas_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-init-lemmas"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Data.Nat.Div.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (_ : Nat) : Prop :=\n  \
                     (∀ (a b : Bool), (a && b) = true → a = true ∧ b = true) ∧\n  \
                     (∀ n : Nat, 0 < Nat.pow 2 n) ∧\n  \
                     (∀ m n : Nat, Nat.div n 2 = Nat.div m 2 → Nat.mod n 2 = Nat.mod m 2 → n = m)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.InitLemmas\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     have _ := Anneal.InitLemmas.canary_list_ops_edge\n  \
                     exact ⟨fun _ _ h => ⟨Anneal.InitLemmas.bool_and_left h,\n    \
                       Anneal.InitLemmas.bool_and_right h⟩,\n    \
                       Anneal.InitLemmas.nat_two_pow_pos,\n    \
                       fun m n hd hm => Anneal.InitLemmas.div2_mod2_inj m n hd hm⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-init-lemmas");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.InitLemmas"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn live_demand_driven_classical_em_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-classical-em"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.NotationExtra\nimport Init.Data.Nat.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 1\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (_ : Nat) : Prop :=\n  \
                     (∀ p : Prop, p ∨ ¬ p) ∧\n  \
                     (∀ p : Prop, ¬ ¬ p → p) ∧\n  \
                     (∀ (P : Nat → Prop), (∃ x : Nat, P x) → ∃ x : Nat, P x)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.ClassicalEm\n\
                     theorem Proof.verify : Expected.claim := by\n  \
                     have _ := Anneal.ClassicalEm.canary_chooseExists_false_rejected\n  \
                     exact ⟨Anneal.ClassicalEm.prop_em,\n    \
                       fun _ hnn => Anneal.ClassicalEm.of_not_not hnn,\n    \
                       fun _ h => ⟨Anneal.ClassicalEm.chooseExists h,\n      \
                         Anneal.ClassicalEm.chooseExists_spec h⟩⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-classical-em");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.ClassicalEm"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn target_audit_report_schema_rejects_unknown_fields_mismatches_and_unapproved_axioms() {
        let valid_graph: BTreeMap<String, Vec<ImportEdge>> =
            BTreeMap::from([("Init.Prelude".to_string(), Vec::new())]);
        let request = TargetAuditRequest {
            modules: Vec::new(),
            theorem_module: "Proof".to_string(),
            theorem_name: "Proof.verify".to_string(),
            expected_module: "Expected".to_string(),
            expected_declaration: "Expected.claim".to_string(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".to_string(),
            subject_declaration: "Captured.program".to_string(),
            specification_declaration: "Spec.specs".to_string(),
            allow_sorry_in_proof: false,
            bindings: TargetBindings {
                request_sha256: "0".repeat(64),
                capture_sha256: "0".repeat(64),
                model_manifest_sha256: "0".repeat(64),
                specification_manifest_sha256: "0".repeat(64),
            },
        };
        let valid_json = json!({
            "theorem": "Proof.verify",
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "subject": "Captured.program",
            "specification": "Spec.specs",
            "graph": { "Init.Prelude": [] },
            "expected": "Expected.claim",
            "axioms": ["propext"],
            "sorryDeclarations": [],
            "replay": true,
            "exactType": true,
            "replayedDeclarations": 12,
            "checkedAlternateProofs": 0,
            "subjectClosure": [{"name": "Captured.program", "module": "Captured"}],
            "modelClosure": [{"name": "Trusted.MirSemantics.UnitTheorem", "module": "Trusted.MirSemantics"}],
            "specificationClosure": [{"name": "Spec.specs", "module": "Spec"}],
        });
        let valid: TargetAuditReport = serde_json::from_value(valid_json.clone()).unwrap();
        validate_target_audit_report(&valid, &request, &valid_graph).unwrap();

        // Unknown fields must fail closed under `deny_unknown_fields`.
        let mut with_extra = valid_json.clone();
        with_extra.as_object_mut().unwrap().insert("extraField".into(), json!(true));
        assert!(serde_json::from_value::<TargetAuditReport>(with_extra).is_err());

        // Missing fields must fail deserialization.
        let mut missing_replay = valid_json.clone();
        missing_replay.as_object_mut().unwrap().remove("replay");
        assert!(serde_json::from_value::<TargetAuditReport>(missing_replay).is_err());

        // Semantic mismatches must fail closed.
        for (label, mutate) in [
            ("wrong theorem", Box::new(|r: &mut TargetAuditReport| r.theorem = "Other.thm".into()) as Box<dyn FnOnce(&mut TargetAuditReport)>),
            ("wrong expected", Box::new(|r: &mut TargetAuditReport| r.expected = "Other.claim".into())),
            ("wrong canonicalRoot", Box::new(|r: &mut TargetAuditReport| r.canonical_root = "Other.root".into())),
            ("wrong subject", Box::new(|r: &mut TargetAuditReport| r.subject = "Other.prog".into())),
            ("wrong specification", Box::new(|r: &mut TargetAuditReport| r.specification = "Other.spec".into())),
            ("replay false", Box::new(|r: &mut TargetAuditReport| r.replay = false)),
            ("exactType false", Box::new(|r: &mut TargetAuditReport| r.exact_type = false)),
            ("zero replayed", Box::new(|r: &mut TargetAuditReport| r.replayed_declarations = 0)),
            ("empty subjectClosure", Box::new(|r: &mut TargetAuditReport| r.subject_closure.clear())),
            ("empty modelClosure", Box::new(|r: &mut TargetAuditReport| r.model_closure.clear())),
            ("empty specificationClosure", Box::new(|r: &mut TargetAuditReport| r.specification_closure.clear())),
            ("unapproved axiom", Box::new(|r: &mut TargetAuditReport| r.axioms.push("Lean.ofReduceBool".into()))),
            ("sorryAx disallowed", Box::new(|r: &mut TargetAuditReport| r.axioms.push("sorryAx".into()))),
            ("duplicate axiom", Box::new(|r: &mut TargetAuditReport| r.axioms.push("propext".into()))),
            ("graph mismatch", Box::new(|r: &mut TargetAuditReport| { r.graph.clear(); })),
        ] {
            let mut bad = valid.clone();
            mutate(&mut bad);
            assert!(
                validate_target_audit_report(&bad, &request, &valid_graph).is_err(),
                "expected validation failure for {label}"
            );
        }

        // `allow_sorry_in_proof` permits `sorryAx` iff `sorryDeclarations` is non-empty.
        let mut sorry_req = request.clone();
        sorry_req.allow_sorry_in_proof = true;
        let mut sorry_rep = valid.clone();
        sorry_rep.axioms.push("sorryAx".into());
        assert!(validate_target_audit_report(&sorry_rep, &sorry_req, &valid_graph).is_err());
        sorry_rep.sorry_declarations.push("Proof.hole".into());
        validate_target_audit_report(&sorry_rep, &sorry_req, &valid_graph).unwrap();

        let mut valid_with_warnings = valid.clone();
        valid_with_warnings.spec_warnings = vec![TargetSpecWarning {
            code: "trivial_property".into(),
            declaration: "Spec.specs".into(),
            message: "Specs.property reduces to True".into(),
            body: None,
        }];
        validate_target_audit_report(&valid_with_warnings, &request, &valid_graph).unwrap();

        for (label, mutator) in [
            (
                "unknown spec warning code",
                Box::new(|r: &mut TargetAuditReport| {
                    r.spec_warnings.push(TargetSpecWarning {
                        code: "bogus_code".into(),
                        declaration: "Spec.specs".into(),
                        message: "bad".into(),
                        body: None,
                    });
                }) as Box<dyn FnOnce(&mut TargetAuditReport)>,
            ),
            (
                "empty warning declaration",
                Box::new(|r: &mut TargetAuditReport| {
                    r.spec_warnings.push(TargetSpecWarning {
                        code: "trivial_property".into(),
                        declaration: String::new(),
                        message: "bad".into(),
                        body: None,
                    });
                }),
            ),
            (
                "empty warning message",
                Box::new(|r: &mut TargetAuditReport| {
                    r.spec_warnings.push(TargetSpecWarning {
                        code: "trivial_property".into(),
                        declaration: "Spec.specs".into(),
                        message: String::new(),
                        body: None,
                    });
                }),
            ),
            (
                "empty warning body",
                Box::new(|r: &mut TargetAuditReport| {
                    r.spec_warnings.push(TargetSpecWarning {
                        code: "unsatisfiable_safety".into(),
                        declaration: "Spec.specs".into(),
                        message: "bad".into(),
                        body: Some(String::new()),
                    });
                }),
            ),
        ] {
            let mut bad = valid.clone();
            mutator(&mut bad);
            assert!(
                validate_target_audit_report(&bad, &request, &valid_graph).is_err(),
                "expected spec_warnings rejection for {label}"
            );
        }
    }

    #[test]
    fn live_demand_driven_firewall_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-firewall"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Core\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (n : Nat) : Prop :=\n  \
                     (n = 0 → n = 0 ∧ n = 0) ∧ (n = 0 → n = 0)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.Firewall\n\
                     theorem Proof.verify : Expected.claim :=\n  \
                     let stepPred : Nat → Nat → Prop := fun stage x =>\n    \
                       match stage with\n    \
                       | 0 => x = 0\n    \
                       | _ + 1 => x = 0 ∧ True\n  \
                     ⟨fun hn =>\n    \
                       let h0 := Anneal.Firewall.wrap 0 hn\n    \
                       let h4 := Anneal.Firewall.trans_tag 0 4 h0\n    \
                       let hm := Anneal.Firewall.map 4 \
                         (fun h : Captured.program = 0 => h) h4\n    \
                       Anneal.Firewall.unwrap (Anneal.Firewall.map2 4 And.intro hm h4),\n   \
                      fun hn =>\n    \
                       let hs1 : Anneal.Firewall.IndexedCut stepPred 1 Captured.program :=\n      \
                         Anneal.Firewall.seal_cut ⟨hn, True.intro⟩\n    \
                       let hs0 : Anneal.Firewall.IndexedCut stepPred 0 Captured.program :=\n      \
                         Anneal.Firewall.step_cut (cutAt := stepPred)\n        \
                         (stage1 := 0) (stage2 := 1) (st1 := Captured.program)\n        \
                         (st2 := Captured.program) (fun h => h.1) hs1\n    \
                       let _opened := Anneal.Firewall.open_cut hs0\n    \
                       Anneal.Firewall.canary_irreducible_indexed_cut\n      \
                         (Anneal.Firewall.finish_cut (cutAt := stepPred) (stage := 0)\n        \
                           (st := Captured.program) (fun h => h) hs0)⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        let export_dir = base.join("export-with-firewall");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &["Anneal.Firewall"],
            &["Anneal.Unused"],
        );
    }

    #[test]
    fn live_demand_driven_scalar_umbrella_three_axiom_proof() {
        let Some(lean) = explicit_verified_lean() else {
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let bundle = EmbeddedBundle::materialize(&base.join("bundle"));

        // Unused bundled theory module with a deliberate elaboration error in
        // its body (valid header only): proving it is pruned means it is never
        // compiled.
        let unused_path = base.join("Anneal_Unused.lean");
        fs::write(
            &unused_path,
            "prelude\nimport Init.Prelude\ndef Anneal.Unused.broken : Nat := \"not_a_nat\"\n",
        )
        .unwrap();
        let unused_sha = sha256_file(&unused_path, "fixture").unwrap();

        let mut req = write_target_request(
            &base.join("with-scalar-umbrella"),
            vec![
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Data.BitVec.BasicAux\nimport Init.Data.Nat.Div.Basic\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n",
                ),
                (
                    "Captured",
                    TargetRole::Capture,
                    "prelude\nimport Model\ndef Captured.program : Nat := 8\n",
                ),
                (
                    "Spec",
                    TargetRole::Specification,
                    "prelude\nimport Model\n\
                     def Spec.specs (w : Nat) : Prop :=\n  \
                     0 < Nat.pow 2 w ∧\n  \
                     (∀ i n : Nat, 2 * i + 1 ≤ 2 * n → i < n) ∧\n  \
                     (∀ a b : BitVec 32, a.toNat = b.toNat → a = b)\n",
                ),
                (
                    "Expected",
                    TargetRole::Expected,
                    "prelude\nimport Captured\nimport Spec\n\
                     def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                     (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
                ),
                (
                    "Proof",
                    TargetRole::Proof,
                    "prelude\nimport Expected\nimport Anneal.Scalar\n\
                     theorem Proof.verify : Expected.claim :=\n  \
                     have _ := @Anneal.BitVecArith.bswap32_injective\n  \
                     have _ := @Anneal.LeBytes.toLeBytes_injective\n  \
                     have _ := @Anneal.ListChunks.divCeil_pos\n  \
                     have _ := @Anneal.NatBitwise.land_lt_two_pow\n  \
                     ⟨Anneal.InitLemmas.nat_two_pow_pos Captured.program,\n   \
                      Anneal.LinearArith.parity_stride_lt,\n   \
                      fun _ _ h => Anneal.BitVec.eq_of_toNat_eq h⟩\n",
                ),
            ],
        );
        bundle.attach(&mut req, false);
        req.modules.push(TargetModule {
            module: "Anneal.Unused".to_owned(),
            source: unused_path,
            expected_sha256: unused_sha,
            role: TargetRole::Proof,
        });

        let mut checker = Checker::new(&bundle.root, Some(&lean)).unwrap();
        let report = checker.run_target(&req).unwrap();
        assert_eq!(report["replay"], Json::Bool(true));
        assert_eq!(report["exactType"], Json::Bool(true));
        let sources: BTreeSet<&str> = report["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["module"].as_str().unwrap())
            .collect();
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        let constructive_axioms: BTreeSet<&str> = BTreeSet::from(["Quot.sound", "propext"]);
        assert!(
            used_axioms.is_subset(&constructive_axioms),
            "expected constructive axioms subset of [\"Quot.sound\", \"propext\"] (no Classical.choice), got {used_axioms:?}"
        );
        assert!(!used_axioms.contains("Classical.choice"));
        let export_dir = base.join("export-with-scalar-umbrella");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        bundle.assert_exact_theory_retention(
            &sources,
            &checker.stage.join("lib"),
            Some(&export_dir),
            &[
                "Anneal.BitVec",
                "Anneal.BitVecArith",
                "Anneal.InitLemmas",
                "Anneal.LeBytes",
                "Anneal.LinearArith",
                "Anneal.ListChunks",
                "Anneal.NatBitwise",
                "Anneal.Scalar",
            ],
            &["Anneal.Unused"],
        );
    }
}
