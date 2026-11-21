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

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::json;

use crate::stage::Checker;
use crate::toolchain::{
    Failure, Json, PreflightResult, default_compile_workers, is_lean_ident, is_sha256_hex,
    sha256_file, stage_regular_file, topo_sort_modules, verify_installed_module_record,
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
            let arts_arr: Vec<Json> = adm
                .artifacts
                .iter()
                .map(|(k, parts)| json!([k, parts.to_wire()]))
                .collect();
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
                return Err(Failure::operational(
                    "library-lock",
                    "invalid module record",
                ));
            }
            let record = &lock.modules[&module];
            let artifacts = verify_installed_module_record(&prefix, &module, record, "library")?;
            let adm = self.admitted_mut()?;
            adm.artifacts.insert(module.clone(), artifacts);
            adm.graph
                .insert(module.clone(), lock.graph[&module].clone());
            adm.library_modules.insert(module);
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
                return Err(Failure::policy(
                    "target-input",
                    "invalid subject binding digest",
                ));
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
            if !target_name_valid(&module.module)
                || roles.contains_key(&module.module)
                || adm.foundation_graph.contains_key(&module.module)
                || adm
                    .library_lock
                    .as_ref()
                    .is_some_and(|l| l.modules.contains_key(&module.module))
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
                return Err(Failure::policy(
                    "headers",
                    "duplicate or foreign source header",
                ));
            }
            imports.insert(header.module, header.imports);
        }
        if imports.len() != staged.len() {
            return Err(Failure::policy(
                "headers",
                "incomplete target source header inventory",
            ));
        }
        self.admit_libraries(imports.values().flatten().map(|e| e.module.clone()))?;
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
        let order = topo_sort_modules(
            staged.keys().cloned().collect(),
            &imports,
            "target import cycle",
        )?;
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
        for module in &request.modules {
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
        let mut report = self.inspect_target(request)?;
        let mut provenance = Vec::new();
        for module in &request.modules {
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
        // above separately identifies every request source, even unused ones.
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
                    let source_sha =
                        if let Some(source) = request.modules.iter().find(|m| m.module == module) {
                            source.expected_sha256.clone()
                        } else {
                            sha256_file(
                                &adm.prefix
                                    .join("src/lean")
                                    .join(format!("{}.lean", module.replace('.', "/"))),
                                "target-provenance",
                            )?
                        };
                    let artifacts = adm.artifacts.get(module).ok_or_else(|| {
                        Failure::operational("target-provenance", "missing closure artifact")
                    })?;
                    let paths = artifacts.to_wire();
                    let hashes: Result<Vec<_>, Failure> = paths
                        .iter()
                        .flat_map(|p| p.iter())
                        .map(|p| {
                            Ok(json!({
                                "part": Path::new(p).file_name().and_then(|s| s.to_str()),
                                "sha256": sha256_file(Path::new(p), "target-provenance")?
                            }))
                        })
                        .collect();
                    identities.insert(
                        module.into(),
                        json!({"sourceSha256": source_sha, "artifacts": hashes?}),
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
        obj.insert("toolchain".into(), json!(self.admitted()?.version));
        Ok(report)
    }
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
                (
                    "trusted/audit/TrustedBoundary.lean",
                    "-- Never run.\n".to_owned(),
                ),
                ("trusted/lean/lean-toolchain", format!("{TOOLCHAIN}\n")),
                (
                    "trusted/lean/foundation-lock.json",
                    foundation_lock.to_string(),
                ),
            ] {
                let path = root.join(relative);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(path, contents).unwrap();
            }
            Self {
                _dir: dir,
                base,
                root,
                prefix,
                lean,
                records,
            }
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
        assert!(
            toolchain
                .checker()
                .tool_admission()
                .unwrap()
                .library_lock
                .is_none()
        );
        let valid = toolchain.library_lock();
        toolchain.write_library_lock(&valid);
        let mut checker = toolchain.checker();
        let admitted = checker.tool_admission().unwrap();
        assert_eq!(
            admitted
                .library_lock
                .as_ref()
                .map(|lock| lock.modules.len()),
            Some(2)
        );
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
        assert_eq!(
            (failure.code, failure.phase.as_str()),
            (2, "library-lock"),
            "{failure}"
        );
        assert!(
            failure.message.contains("unknown field `unexpected`"),
            "{failure}"
        );

        // The catalog must be the bundle's own regular file.
        let linked = toolchain.base.join("linked-library-lock.json");
        fs::write(&linked, valid.to_string()).unwrap();
        let path = toolchain.root.join("trusted/audit/library-lock.json");
        fs::remove_file(&path).unwrap();
        std::os::unix::fs::symlink(&linked, &path).unwrap();
        let failure = toolchain.checker().tool_admission().unwrap_err();
        assert_eq!(
            (failure.code, failure.phase.as_str()),
            (1, "library-lock"),
            "{failure}"
        );
        assert!(
            failure.message.starts_with("expected a regular file: "),
            "{failure}"
        );
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
        assert_eq!(
            (failure.code, failure.phase.as_str()),
            (2, "headers"),
            "{failure}"
        );
        assert!(
            failure.message.starts_with("Lean exited Some(3)"),
            "{failure}"
        );
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

        let olean = toolchain
            .prefix
            .join("lib/lean/Init/Data/BitVec/Basic.olean");
        fs::write(&olean, b"changed library artifact").unwrap();
        let expected = Failure::operational(
            "library",
            format!(
                "library artifact SHA-256 mismatch for Init/Data/BitVec/Basic.olean: \
                 expected {}, got {}",
                toolchain.records[LIBRARY]["parts"]["olean"]
                    .as_str()
                    .unwrap(),
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
        let source = toolchain
            .prefix
            .join("src/lean/Init/Data/BitVec/Basic.lean");
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
            Err(Failure::operational(
                "library-lock",
                "invalid module record"
            ))
        );
    }
}
