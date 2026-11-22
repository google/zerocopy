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
    stage::Checker,
    toolchain::{
        AdmittedToolchain, Failure, ImportEdge, Json, PreflightResult, TOOLCHAIN,
        compute_unpinned_foundation_closure, default_compile_workers,
        hash_unpinned_sysroot_module, is_allowed_unpinned_sysroot_module, is_lean_ident,
        is_sha256_hex, sha256_bytes, sha256_file, sha256_file_deref, stage_regular_file,
        topo_sort_modules, verify_installed_module_record,
    },
};

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
fn is_bundled_theory_module(module: &str) -> bool {
    module == "Anneal" || module.starts_with("Anneal.")
}

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
    bindings: &'a TargetBindings,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct InspectorTargetModule<'a> {
    module: &'a str,
    expected_sha256: &'a str,
    role: TargetRole,
}

impl<'a> From<&'a TargetAuditRequest> for InspectorTargetAuditRequest<'a> {
    fn from(request: &'a TargetAuditRequest) -> Self {
        Self {
            modules: request
                .modules
                .iter()
                .map(|module| InspectorTargetModule {
                    module: &module.module,
                    expected_sha256: &module.expected_sha256,
                    role: module.role,
                })
                .collect(),
            theorem_module: &request.theorem_module,
            theorem_name: &request.theorem_name,
            expected_module: &request.expected_module,
            expected_declaration: &request.expected_declaration,
            canonical_root: &request.canonical_root,
            subject_declaration: &request.subject_declaration,
            specification_declaration: &request.specification_declaration,
            bindings: &request.bindings,
        }
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

    /// Run `"target-audit"` mode over compiled target artifacts.
    #[doc(hidden)]
    pub fn inspect_target(&mut self, request: &TargetAuditRequest) -> Result<Json, Failure> {
        let req = {
            let adm = self.admitted()?;
            let arts_arr: Vec<Json> =
                adm.artifacts.iter().map(|(k, parts)| json!([k, parts.to_wire()])).collect();
            let libraries: Vec<&str> = adm.library_modules.iter().map(String::as_str).collect();
            json!({
                "mode": "target-audit",
                "sysroot": adm.prefix.to_string_lossy(),
                "artifacts": arts_arr,
                "foundation": adm.foundation_modules(),
                "libraries": libraries,
                "graph": &adm.graph,
                "axioms": &adm.axioms,
                "target": InspectorTargetAuditRequest::from(request),
            })
        };
        self.invoke_inspector("target-audit", &req)
    }

    /// Authenticate the requested installed-library import closure.
    ///
    /// Library hashes pin their bytes but do not admit their declarations as
    /// axioms. The inspector replays every logically reached declaration into
    /// the original foundation environment. A library can import only another
    /// locked library or the original foundation, never target source modules.
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
        let mut pending: Vec<String> = roots.into_iter().collect();
        let mut needed = BTreeSet::new();
        while let Some(module) = pending.pop() {
            if foundation.contains_key(&module)
                || !lock.modules.contains_key(&module)
                || !needed.insert(module.clone())
            {
                continue;
            }
            pending.extend(lock.graph[&module].iter().map(|e| e.module.clone()));
        }
        for module in needed {
            if self.admitted()?.library_modules.contains(&module) {
                continue;
            }
            if !target_name_valid(&module) {
                return Err(Failure::operational("library-lock", "invalid module record"));
            }
            let record = &lock.modules[&module];
            let artifacts = verify_installed_module_record(&prefix, &module, record, "library")?;
            let adm = self.admitted_mut()?;
            adm.artifacts.insert(module.clone(), artifacts);
            adm.graph.insert(module.clone(), lock.graph[&module].clone());
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
            let collides_with_sysroot = if adm.unpinned {
                let root_pkg = module.module.split('.').next().unwrap_or("");
                adm.sysroot_package_roots.contains(root_pkg)
            } else {
                adm.foundation_graph.contains_key(&module.module)
                    || adm
                        .library_lock
                        .as_ref()
                        .is_some_and(|l| l.modules.contains_key(&module.module))
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
            let dest = self
                .stage
                .join("target-src")
                .join(format!("{}.lean", module.module.replace('.', "/")));
            stage_regular_file(&module.source, &dest, "target-input")?;
            if !sha256_file(&dest, "target-input")?.eq_ignore_ascii_case(&module.expected_sha256) {
                return Err(Failure::policy(
                    "target-input",
                    format!("source digest differs for {}", module.module),
                ));
            }
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
        for header in headers.headers {
            if !staged.contains_key(&header.module) || imports.contains_key(&header.module) {
                return Err(Failure::policy("headers", "duplicate or foreign source header"));
            }
            imports.insert(header.module, header.imports);
        }
        if imports.len() != staged.len() {
            return Err(Failure::policy("headers", "incomplete target source header inventory"));
        }
        // Retain every non-bundled target module plus only those bundled
        // `Anneal.*` theory modules reachable from them via parsed imports.
        let retained = reachable_target_modules(request, &imports);
        imports.retain(|module, _| retained.contains(module));
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
            for edge in edges {
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
        // Compilation consumes authenticated private copies and explicit
        // imported artifacts across the verified module DAG. Target
        // elaboration remains under the intact-host assumption; this path does
        // not relax repository syntax admission.
        self.compile_lean_modules_parallel(
            &order,
            &staged,
            &imports,
            "target-lib",
            false,
            true,
            default_compile_workers(4),
        )?;
        // Authenticate the staged bytes again after elaboration. This catches
        // accidental source changes; hostile host mutation remains excluded.
        for module in &filtered_request.modules {
            if !sha256_file(&staged[&module.module], "target-input")?
                .eq_ignore_ascii_case(&module.expected_sha256)
            {
                return Err(Failure::policy(
                    "target-input",
                    "staged source changed during elaboration",
                ));
            }
        }
        // Compilation success alone does not establish the exact theorem
        // type, permitted assumptions, or compiled source roles. Acceptance
        // is a separate inspection of the produced kernel declarations.
        let mut report = self.inspect_target(&filtered_request)?;
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
            let current_lean_sha = sha256_file_deref(self.lean_path(), "target-provenance")
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
    use std::fs;

    use serde_json::json;

    use super::*;
    use crate::toolchain::TOOLCHAIN;

    const VERSION: &str = "Lean (version 4.34.1, synthetic admission fixture)";
    const FOUNDATION: &str = "Init.Prelude";
    const LIBRARY: &str = "Init.Data.BitVec.Basic";
    const LIBRARY_USER: &str = "Init.Data.BitVec.Lemmas";

    fn edge(module: &str) -> Json {
        json!({"module": module, "importAll": false, "isExported": true, "isMeta": false})
    }

    /// Return a copy of `value` with `change` applied.
    fn changed(value: &Json, change: impl FnOnce(&mut Json)) -> Json {
        let mut value = value.clone();
        change(&mut value);
        value
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
        records: BTreeMap<&'static str, Json>,
    }

    impl Toolchain {
        fn new() -> Self {
            let dir = tempfile::tempdir().unwrap();
            let base = fs::canonicalize(dir.path()).unwrap();
            let root = base.join("bundle");
            let prefix = base.join("prefix");
            let lean = base.join("lean");
            // Simulate compiling the inspector so a valid request reaches
            // its header invocation. Status 3 makes that invocation visible.
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
        -o:*/inspector-lib/TrustedBoundary.olean) : > "$2"; exit ;;
    esac
    shift
done
exit 3
"#,
                    prefix.display()
                ),
            )
            .unwrap();
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();
            }
            let records: BTreeMap<_, _> = [FOUNDATION, LIBRARY, LIBRARY_USER]
                .into_iter()
                .map(|module| (module, install(&prefix, module)))
                .collect();
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
            Self { _dir: dir, base, root, prefix, lean, records }
        }

        /// Return a valid catalog in which `LIBRARY_USER` imports `LIBRARY`.
        fn library_lock(&self) -> Json {
            json!({
                "schema": 1,
                "toolchain": TOOLCHAIN,
                "modules": {
                    LIBRARY: self.records[LIBRARY],
                    LIBRARY_USER: self.records[LIBRARY_USER],
                },
                "graph": {
                    LIBRARY: [edge(FOUNDATION)],
                    LIBRARY_USER: [edge(LIBRARY)],
                },
            })
        }

        fn write_library_lock(&self, lock: &Json) {
            let path = self.root.join("trusted/audit/library-lock.json");
            fs::write(path, lock.to_string()).unwrap();
        }

        fn checker(&self) -> Checker {
            Checker::new_with_env(&self.root, Some(self.lean.as_path()), []).unwrap()
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

    /// Tool admission validates the whole library catalog before any target
    /// input. Library digests wait until an import reaches the library.
    #[test]
    fn tool_admission_rejects_invalid_library_catalogs() {
        let toolchain = Toolchain::new();
        // Controls: an absent catalog and the valid catalog both pass, so
        // each refusal below follows from its single change.
        assert!(toolchain.checker().tool_admission().unwrap().library_lock.is_none());
        let valid = toolchain.library_lock();
        toolchain.write_library_lock(&valid);
        let mut checker = toolchain.checker();
        let admitted = checker.tool_admission().unwrap();
        assert_eq!(admitted.library_lock.as_ref().map(|lock| lock.modules.len()), Some(2));
        assert!(admitted.library_modules.is_empty());

        for (case, lock) in [
            ("schema", changed(&valid, |lock| lock["schema"] = json!(2))),
            (
                "toolchain",
                changed(&valid, |lock| {
                    lock["toolchain"] = json!("leanprover/lean4:v4.34.0");
                }),
            ),
            (
                "graph inventory",
                changed(&valid, |lock| {
                    let graph = lock["graph"].as_object_mut().unwrap();
                    assert!(graph.remove(LIBRARY_USER).is_some());
                }),
            ),
            (
                "foundation overlap",
                changed(&valid, |lock| {
                    lock["modules"][FOUNDATION] = toolchain.records[FOUNDATION].clone();
                    lock["graph"][FOUNDATION] = json!([]);
                }),
            ),
            (
                "unlocked import",
                changed(&valid, |lock| {
                    lock["graph"][LIBRARY_USER] = json!([edge("Init.Missing")]);
                }),
            ),
        ] {
            toolchain.write_library_lock(&lock);
            assert_eq!(
                toolchain.checker().tool_admission().unwrap_err(),
                Failure::operational("library-lock", "invalid checked-library catalog"),
                "{case}"
            );
        }

        for (lock, message) in [
            (
                changed(&valid, |lock| {
                    let parts = lock["modules"][LIBRARY]["parts"].as_object_mut().unwrap();
                    assert!(parts.remove("ir").is_some());
                }),
                format!("incomplete artifact-part policy for {LIBRARY}"),
            ),
            (
                changed(&valid, |lock| {
                    lock["modules"][LIBRARY]["parts"]["ir"] = json!("not a digest");
                }),
                format!("invalid part digest in {LIBRARY}"),
            ),
        ] {
            toolchain.write_library_lock(&lock);
            assert_eq!(
                toolchain.checker().tool_admission().unwrap_err(),
                Failure::operational("library-lock", message)
            );
        }

        toolchain.write_library_lock(&changed(&valid, |lock| lock["unexpected"] = json!(true)));
        let failure = toolchain.checker().tool_admission().unwrap_err();
        assert_eq!((failure.code, failure.phase.as_str()), (2, "library-lock"), "{failure}");
        assert!(failure.message.contains("unknown field `unexpected`"), "{failure}");

        // The catalog must be the bundle's own regular file.
        let linked = toolchain.base.join("linked-library-lock.json");
        fs::write(&linked, valid.to_string()).unwrap();
        let path = toolchain.root.join("trusted/audit/library-lock.json");
        fs::remove_file(&path).unwrap();
        std::os::unix::fs::symlink(&linked, &path).unwrap();
        let failure = toolchain.checker().tool_admission().unwrap_err();
        assert_eq!((failure.code, failure.phase.as_str()), (1, "library-lock"), "{failure}");
        assert!(failure.message.starts_with("expected a regular file: "), "{failure}");
    }

    /// A target source cannot take the name of a locked foundation or library
    /// module, whose authenticated artifacts it would otherwise replace.
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
        for module in [FOUNDATION, LIBRARY] {
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

    /// Library digests are checked when a target import reaches the library.
    /// Tool admission still accepts the catalog after an artifact changes.
    #[test]
    fn admit_libraries_rejects_changed_artifacts_in_the_import_closure() {
        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        // Control: unchanged bytes admit the root and the library it imports.
        let mut checker = toolchain.checker();
        checker.tool_admission().unwrap();
        checker.admit_libraries([LIBRARY_USER.to_owned()]).unwrap();
        let admitted = checker.admitted().unwrap();
        assert_eq!(
            admitted.library_modules,
            BTreeSet::from([LIBRARY.to_owned(), LIBRARY_USER.to_owned()])
        );
        assert!(admitted.artifacts.contains_key(LIBRARY));

        let olean = toolchain.prefix.join("lib/lean/Init/Data/BitVec/Basic.olean");
        fs::write(&olean, b"changed library artifact").unwrap();
        let expected = Failure::operational(
            "library",
            format!(
                "library artifact SHA-256 mismatch for Init/Data/BitVec/Basic.olean: \
                 expected {}, got {}",
                toolchain.records[LIBRARY]["parts"]["olean"].as_str().unwrap(),
                sha256_file(&olean, "fixture").unwrap()
            ),
        );
        // Both the library and a library that imports it reach the change.
        for root in [LIBRARY, LIBRARY_USER] {
            assert_eq!(admit(&toolchain, root), Err(expected.clone()), "{root}");
        }
    }

    /// Each reached record also binds its source bytes and the absence of
    /// companion parts locked as absent, and its name must fit the target
    /// module-name protocol.
    #[test]
    fn admit_libraries_rejects_changed_sources_extra_parts_and_invalid_names() {
        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        let source = toolchain.prefix.join("src/lean/Init/Data/BitVec/Basic.lean");
        fs::write(&source, b"changed library source").unwrap();
        assert_eq!(
            admit(&toolchain, LIBRARY_USER),
            Err(Failure::operational(
                "library",
                format!(
                    "library source SHA-256 mismatch for {LIBRARY}: expected {}, got {}",
                    toolchain.records[LIBRARY]["sourceSha256"].as_str().unwrap(),
                    sha256_file(&source, "fixture").unwrap()
                )
            ))
        );

        let toolchain = Toolchain::new();
        toolchain.write_library_lock(&toolchain.library_lock());
        let ir = toolchain.prefix.join("lib/lean/Init/Data/BitVec/Basic.ir");
        fs::write(&ir, b"unlocked companion part").unwrap();
        assert_eq!(
            admit(&toolchain, LIBRARY),
            Err(Failure::operational(
                "library",
                "unexpected companion part: Init/Data/BitVec/Basic.ir"
            ))
        );

        // The catalog accepts this record, but admission refuses its name
        // before reading any of its files.
        let toolchain = Toolchain::new();
        let invalid = "Init.Data.7Bad";
        toolchain.write_library_lock(&changed(&toolchain.library_lock(), |lock| {
            lock["modules"][invalid] = toolchain.records[LIBRARY].clone();
            lock["graph"][invalid] = json!([]);
            lock["graph"][LIBRARY_USER] = json!([edge(LIBRARY), edge(invalid)]);
        }));
        assert_eq!(
            admit(&toolchain, LIBRARY_USER),
            Err(Failure::operational("library-lock", "invalid module record"))
        );
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
        -o:*/inspector-lib/TrustedBoundary.olean) : > "$2"; exit ;;
    esac
    shift
done
exit 3
"#,
                prefix.display()
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
        // Control: passes staging and reaches inspector (`Lean exited
        // Some(3)`).
        let control = checker.run_target(&req).unwrap_err();
        assert_eq!((control.code, control.phase.as_str()), (2, "headers"), "{control}");

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

        // Reject Lean.* and Lake.* imports before compilation.
        for forbidden in ["Lean.Elab", "Lake.Build"] {
            let bad_req = minimal_request(&base.join(format!("bad-{forbidden}")), Some(forbidden));
            let err = checker.run_target(&bad_req).unwrap_err();
            assert_eq!(err.code, 1, "{forbidden}: {err}");
            assert_eq!(err.phase, "target-import", "{forbidden}: {err}");
            assert!(err.message.contains("only Init and Std"), "{forbidden}: {err}");
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
        include!("bundled_resources.rs");

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
        /// Materialize `cargo-anneal`'s embedded bundle into `root` just as
        /// `verify.rs` does, so `target::tests` runs without reaching outside
        /// the package (including from an unpacked `cargo package` tarball).
        fn materialize(root: &Path) -> Self {
            let mut model_modules = Vec::new();
            let mut theory_modules = Vec::new();
            for &(relative, text) in embedded::entries() {
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
                } else if let Some(rest) =
                    relative.strip_prefix("theory/").and_then(|s| s.strip_suffix(".lean"))
                {
                    theory_modules.push(TargetModule {
                        module: rest.replace('/', "."),
                        source: path,
                        expected_sha256: sha,
                        role: TargetRole::Proof,
                    });
                }
            }
            Self { root: root.to_path_buf(), model_modules, theory_modules }
        }

        fn attach(&self, req: &mut TargetAuditRequest, include_model: bool) {
            if include_model {
                req.modules.extend(self.model_modules.iter().cloned());
            }
            req.modules.extend(self.theory_modules.iter().cloned());
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
        assert!(!sources_unimported.contains("Anneal.MirWp"), "{sources_unimported:?}");
        assert!(!sources_unimported.contains("Anneal.MirWp.Core"), "{sources_unimported:?}");
        assert!(!sources_unimported.contains("Anneal.Unused"), "{sources_unimported:?}");
        assert!(!checker.stage.join("target-lib/Anneal/MirWp.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_unimported = base.join("export-unimported");
        assert!(checker.export_target_oleans(&export_unimported).unwrap());
        assert!(!export_unimported.join("Anneal/MirWp.olean").exists());
        assert!(!export_unimported.join("Anneal/Unused.olean").exists());

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
        for expected in [
            "Anneal.MirWp",
            "Anneal.MirWp.Core",
            "Anneal.MirWp.Execution",
            "Anneal.MirWp.Reflection",
            "Anneal.MirWp.Scalars",
            "Anneal.MirWp.Canaries",
        ] {
            assert!(
                sources_with_mir_wp.contains(expected),
                "missing {expected} in {sources_with_mir_wp:?}"
            );
        }
        assert!(!sources_with_mir_wp.contains("Anneal.Unused"), "{sources_with_mir_wp:?}");
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> = report_with_mir_wp["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| a.as_str().unwrap())
            .collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        assert!(checker.stage.join("target-lib/Anneal/MirWp.olean").is_file());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_with_mir_wp = base.join("export-with-mir-wp");
        assert!(checker.export_target_oleans(&export_with_mir_wp).unwrap());
        assert!(export_with_mir_wp.join("Anneal/MirWp.olean").is_file());
        assert!(!export_with_mir_wp.join("Anneal/Unused.olean").exists());

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
        assert!(!sources_no_bv.contains("Anneal.NatBitwise"), "{sources_no_bv:?}");
        assert!(!sources_no_bv.contains("Anneal.BitVec"), "{sources_no_bv:?}");
        assert!(!sources_no_bv.contains("Anneal.Unused"), "{sources_no_bv:?}");
        assert!(!checker.stage.join("target-lib/Anneal/NatBitwise.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/BitVec.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_no_bv = base.join("export-no-bv");
        assert!(checker.export_target_oleans(&export_no_bv).unwrap());
        assert!(!export_no_bv.join("Anneal/NatBitwise.olean").exists());
        assert!(!export_no_bv.join("Anneal/BitVec.olean").exists());
        assert!(!export_no_bv.join("Anneal/Unused.olean").exists());

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
        assert!(sources_with_bv.contains("Anneal.NatBitwise"), "{sources_with_bv:?}");
        assert!(sources_with_bv.contains("Anneal.BitVec"), "{sources_with_bv:?}");
        assert!(!sources_with_bv.contains("Anneal.Unused"), "{sources_with_bv:?}");
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> = report_with_bv["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| a.as_str().unwrap())
            .collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        assert!(checker.stage.join("target-lib/Anneal/NatBitwise.olean").is_file());
        assert!(checker.stage.join("target-lib/Anneal/BitVec.olean").is_file());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_with_bv = base.join("export-with-bv");
        assert!(checker.export_target_oleans(&export_with_bv).unwrap());
        assert!(export_with_bv.join("Anneal/NatBitwise.olean").is_file());
        assert!(export_with_bv.join("Anneal/BitVec.olean").is_file());
        assert!(!export_with_bv.join("Anneal/Unused.olean").exists());

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
        assert!(sources_both.contains("Anneal.NatBitwise"), "{sources_both:?}");
        assert!(sources_both.contains("Anneal.MirWp"), "{sources_both:?}");
        assert!(sources_both.contains("Anneal.BitVec"), "{sources_both:?}");
        assert!(!sources_both.contains("Anneal.BitVecArith"), "{sources_both:?}");
        assert!(!sources_both.contains("Anneal.LeBytes"), "{sources_both:?}");
        assert!(!sources_both.contains("Anneal.ListChunks"), "{sources_both:?}");
        assert!(!sources_both.contains("Anneal.Unused"), "{sources_both:?}");
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
        assert!(sources.contains("Anneal.LeBytes"), "{sources:?}");
        assert!(sources.contains("Anneal.ListChunks"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVec"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVecArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.NatBitwise"), "{sources:?}");
        assert!(!sources.contains("Anneal.MirWp"), "{sources:?}");
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
        assert!(sources.contains("Anneal.NatBitwise"), "{sources:?}");
        assert!(sources.contains("Anneal.BitVec"), "{sources:?}");
        assert!(sources.contains("Anneal.BitVecArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.LeBytes"), "{sources:?}");
        assert!(!sources.contains("Anneal.ListChunks"), "{sources:?}");
        assert!(!sources.contains("Anneal.LinearArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.MirWp"), "{sources:?}");
        assert!(!sources.contains("Anneal.Unused"), "{sources:?}");
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        assert!(checker.stage.join("target-lib/Anneal/NatBitwise.olean").is_file());
        assert!(checker.stage.join("target-lib/Anneal/BitVec.olean").is_file());
        assert!(checker.stage.join("target-lib/Anneal/BitVecArith.olean").is_file());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_dir = base.join("export-with-bv-arith");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        assert!(export_dir.join("Anneal/NatBitwise.olean").is_file());
        assert!(export_dir.join("Anneal/BitVec.olean").is_file());
        assert!(export_dir.join("Anneal/BitVecArith.olean").is_file());
        assert!(!export_dir.join("Anneal/Unused.olean").exists());
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
        assert!(sources.contains("Anneal.MirWp"), "{sources:?}");
        assert!(sources.contains("Anneal.NatBitwise"), "{sources:?}");
        assert!(sources.contains("Anneal.LoopInv"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVec"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVecArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.LeBytes"), "{sources:?}");
        assert!(!sources.contains("Anneal.ListChunks"), "{sources:?}");
        assert!(!sources.contains("Anneal.SpineForce"), "{sources:?}");
        assert!(!sources.contains("Anneal.PTree"), "{sources:?}");
        assert!(!sources.contains("Anneal.LinearArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.Unused"), "{sources:?}");
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        assert!(checker.stage.join("target-lib/Anneal/MirWp.olean").is_file());
        assert!(checker.stage.join("target-lib/Anneal/NatBitwise.olean").is_file());
        assert!(checker.stage.join("target-lib/Anneal/LoopInv.olean").is_file());
        assert!(!checker.stage.join("target-lib/Anneal/BitVec.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/BitVecArith.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/SpineForce.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/PTree.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/LinearArith.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_dir = base.join("export-with-loopinv");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        assert!(export_dir.join("Anneal/MirWp.olean").is_file());
        assert!(export_dir.join("Anneal/NatBitwise.olean").is_file());
        assert!(export_dir.join("Anneal/LoopInv.olean").is_file());
        assert!(!export_dir.join("Anneal/BitVec.olean").exists());
        assert!(!export_dir.join("Anneal/BitVecArith.olean").exists());
        assert!(!export_dir.join("Anneal/SpineForce.olean").exists());
        assert!(!export_dir.join("Anneal/PTree.olean").exists());
        assert!(!export_dir.join("Anneal/LinearArith.olean").exists());
        assert!(!export_dir.join("Anneal/Unused.olean").exists());
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
        assert!(sources.contains("Anneal.SpineForce"), "{sources:?}");
        assert!(!sources.contains("Anneal.PTree"), "{sources:?}");
        assert!(!sources.contains("Anneal.LinearArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.MirWp"), "{sources:?}");
        assert!(!sources.contains("Anneal.LoopInv"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVec"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVecArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.LeBytes"), "{sources:?}");
        assert!(!sources.contains("Anneal.ListChunks"), "{sources:?}");
        assert!(!sources.contains("Anneal.Unused"), "{sources:?}");
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        assert!(checker.stage.join("target-lib/Anneal/SpineForce.olean").is_file());
        assert!(!checker.stage.join("target-lib/Anneal/PTree.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/LinearArith.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/MirWp.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/LoopInv.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/BitVec.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_dir = base.join("export-with-spineforce");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        assert!(export_dir.join("Anneal/SpineForce.olean").is_file());
        assert!(!export_dir.join("Anneal/PTree.olean").exists());
        assert!(!export_dir.join("Anneal/LinearArith.olean").exists());
        assert!(!export_dir.join("Anneal/MirWp.olean").exists());
        assert!(!export_dir.join("Anneal/LoopInv.olean").exists());
        assert!(!export_dir.join("Anneal/BitVec.olean").exists());
        assert!(!export_dir.join("Anneal/Unused.olean").exists());
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
        assert!(sources.contains("Anneal.PTree"), "{sources:?}");
        assert!(!sources.contains("Anneal.SpineForce"), "{sources:?}");
        assert!(!sources.contains("Anneal.LinearArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.MirWp"), "{sources:?}");
        assert!(!sources.contains("Anneal.LoopInv"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVec"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVecArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.LeBytes"), "{sources:?}");
        assert!(!sources.contains("Anneal.ListChunks"), "{sources:?}");
        assert!(!sources.contains("Anneal.Unused"), "{sources:?}");
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        assert!(checker.stage.join("target-lib/Anneal/PTree.olean").is_file());
        assert!(!checker.stage.join("target-lib/Anneal/SpineForce.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/LinearArith.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/MirWp.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/LoopInv.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/BitVec.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_dir = base.join("export-with-ptree");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        assert!(export_dir.join("Anneal/PTree.olean").is_file());
        assert!(!export_dir.join("Anneal/SpineForce.olean").exists());
        assert!(!export_dir.join("Anneal/LinearArith.olean").exists());
        assert!(!export_dir.join("Anneal/MirWp.olean").exists());
        assert!(!export_dir.join("Anneal/LoopInv.olean").exists());
        assert!(!export_dir.join("Anneal/BitVec.olean").exists());
        assert!(!export_dir.join("Anneal/Unused.olean").exists());
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
        assert!(sources.contains("Anneal.LinearArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.LoopInv"), "{sources:?}");
        assert!(!sources.contains("Anneal.MirWp"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVec"), "{sources:?}");
        assert!(!sources.contains("Anneal.BitVecArith"), "{sources:?}");
        assert!(!sources.contains("Anneal.LeBytes"), "{sources:?}");
        assert!(!sources.contains("Anneal.ListChunks"), "{sources:?}");
        assert!(!sources.contains("Anneal.NatBitwise"), "{sources:?}");
        assert!(!sources.contains("Anneal.SpineForce"), "{sources:?}");
        assert!(!sources.contains("Anneal.PTree"), "{sources:?}");
        assert!(!sources.contains("Anneal.Unused"), "{sources:?}");
        let allowed_axioms: BTreeSet<&str> =
            BTreeSet::from(["Classical.choice", "Quot.sound", "propext"]);
        let used_axioms: BTreeSet<&str> =
            report["axioms"].as_array().unwrap().iter().map(|a| a.as_str().unwrap()).collect();
        assert!(used_axioms.is_subset(&allowed_axioms), "unexpected axioms: {used_axioms:?}");
        assert!(checker.stage.join("target-lib/Anneal/LinearArith.olean").is_file());
        assert!(!checker.stage.join("target-lib/Anneal/PTree.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/SpineForce.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/LoopInv.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/MirWp.olean").exists());
        assert!(!checker.stage.join("target-lib/Anneal/Unused.olean").exists());
        let export_dir = base.join("export-with-linear-arith");
        assert!(checker.export_target_oleans(&export_dir).unwrap());
        assert!(export_dir.join("Anneal/LinearArith.olean").is_file());
        assert!(!export_dir.join("Anneal/PTree.olean").exists());
        assert!(!export_dir.join("Anneal/SpineForce.olean").exists());
        assert!(!export_dir.join("Anneal/LoopInv.olean").exists());
        assert!(!export_dir.join("Anneal/MirWp.olean").exists());
        assert!(!export_dir.join("Anneal/Unused.olean").exists());
    }
}
