// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Implements repository Pass 1 (`trusted/lean/` + `theory/`) and Pass 2
//! (`vendor/lean-miri/` + `trusted/correspondence/` + `correspondence/`)
//! boundary auditing atop `cargo_anneal`'s Lean toolchain and staging
//! substrate.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use serde_json::json;
use walkdir::WalkDir;

use cargo_anneal::{
    AdmittedToolchain, Failure, ImportEdge, Json, OLEAN_PARTS, PARTS, PreflightResult,
    TargetAuditRequest, is_lean_ident, regular, sha256_file, stage_regular_file, topo_sort_modules,
};

use crate::cargo_boundary::check_checkout_cargo_hygiene;
use crate::miri_pin::{
    MiriClosureEntry, ensure_miri_cache_outside_checkout, prepare_nosymlink_cache_path,
    remove_cache_file, verify_sysroot_foundation, verify_upstream_pin, write_cache_file,
};

/// Enumerates the subsystem candidate-trusted feature identifiers recognized by
/// Anneal.
///
/// Must stay in sync with `TrustedBoundary.validCandidateFeatures` in
/// `trusted/audit/TrustedBoundary.lean`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CandidateFeature {
    Refinement,
    StepResult,
    Memory,
    MirAst,
    MirSemantics,
    RustcCapture,
}

impl CandidateFeature {
    /// Parse a candidate feature identifier string.
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "refinement" => Some(Self::Refinement),
            "step_result" => Some(Self::StepResult),
            "memory" => Some(Self::Memory),
            "mir_ast" => Some(Self::MirAst),
            "mir_semantics" => Some(Self::MirSemantics),
            "rustc_capture" => Some(Self::RustcCapture),
            _ => None,
        }
    }

    /// Return the canonical identifier string for this candidate feature.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Refinement => "refinement",
            Self::StepResult => "step_result",
            Self::Memory => "memory",
            Self::MirAst => "mir_ast",
            Self::MirSemantics => "mir_semantics",
            Self::RustcCapture => "rustc_capture",
        }
    }
}

/// Represents the module-level trust tier declared by a `Trusted` module via
/// `-- anneal-trust-tier: <tier>`.
///
/// Making `TrustTier` a sum type over [`CandidateFeature`] ensures that an
/// invalid or misspelled tier cannot be represented.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustTier {
    /// Marks a human-audited, permanently trusted TCB module (`vetted`).
    Vetted,
    /// Marks an alpha TCB module gated behind an explicit candidate feature
    /// opt-in (`candidate:<feature>`).
    Candidate(CandidateFeature),
}

impl TrustTier {
    /// Parse `"vetted"` or `"candidate:<feature>"`.
    pub fn parse(raw: &str) -> Option<Self> {
        if raw == "vetted" {
            Some(Self::Vetted)
        } else {
            let feat = raw.strip_prefix("candidate:")?;
            Some(Self::Candidate(CandidateFeature::parse(feat)?))
        }
    }

    /// Render the canonical wire string (`"vetted"` or
    /// `"candidate:<feature>"`).
    pub fn render(self) -> String {
        match self {
            Self::Vetted => "vetted".to_string(),
            Self::Candidate(f) => format!("candidate:{}", f.as_str()),
        }
    }
}

/// Represents a typed request sent to `TrustedBoundary.lean`.
///
/// Repository syntax admission, Pass 2 correspondence inspection, and target
/// theorem acceptance remain distinct modes. Target sources cannot opt
/// repository modules out of their closed syntax policy, and checked libraries
/// never join the replay foundation or repository audits.
#[derive(Debug, Clone)]
pub enum InspectorRequest {
    /// Discovers source imports without elaborating source commands.
    Headers { sources: Vec<(String, PathBuf)> },
    /// Inspects an exact external theorem against acceptance-owned inputs.
    TargetAudit { request: TargetAuditRequest },
    /// Parses `(module_name, staged_path)` pairs (`"preflight"`) against the
    /// authenticated foundation parser environment without elaborating the
    /// source commands being inspected.
    Preflight { sources: Vec<(String, PathBuf)> },
    /// Parses Pass 2 `(module_name, staged_path)` pairs
    /// (`"correspondence-preflight"`) against the authenticated Pass 2 compile
    /// parser environment (`foundation`, Pass 1 `trusted`/`theory`, and pinned
    /// `vendor_miri` with `loadExts := true`) before compiling any Pass 2
    /// module.
    CorrespondencePreflight {
        search_path: Vec<PathBuf>,
        trusted: Vec<String>,
        theory: Vec<String>,
        vendor_miri: Vec<String>,
        module_tiers: BTreeMap<String, TrustTier>,
        sources: Vec<(String, PathBuf)>,
    },
    /// Loads compiled Pass 1 `.olean`s (`"audit"`) with `loadExts := false`,
    /// verifies module-level trust tiers and namespace hygiene, and replays all
    /// non-foundation constants through the Lean kernel.
    Audit {
        trusted: Vec<String>,
        theory: Vec<String>,
        module_tiers: BTreeMap<String, TrustTier>,
    },
    /// Loads Pass 2 correspondence and `lean-miri` closure `.olean`s
    /// (`"correspondence-audit"`) with `loadExts := false`, verifies
    /// `CorrOrigin` import/edge isolation and `.vendorMiri` purity,
    /// kernel-replays every non-`isPartial` `.vendorMiri` declaration onto the
    /// authenticated sysroot base on every run (cold compile and cache hit
    /// alike), kernel-replays all correspondence declarations onto that
    /// replayed vendor kernel environment, and verifies constant-cone purity,
    /// all 41 correspondence/wiring/canary claims, and reference-evaluator
    /// independence.
    CorrespondenceAudit {
        search_path: Vec<PathBuf>,
        trusted: Vec<String>,
        corr_trusted: Vec<String>,
        theory: Vec<String>,
        corr_theory: Vec<String>,
        vendor_miri: Vec<String>,
        module_tiers: BTreeMap<String, TrustTier>,
    },
}

/// Scan a Lean directory tree (`trusted/lean` with `"Trusted"` or `theory`
/// with `"Anneal"`), rejecting symlinks, non-`.lean` files, and compiled
/// artifacts in the source tree and returning the map from dot-separated module
/// name to `.lean` path.
pub fn scan_lean_tree(
    root: &Path,
    umbrella_prefix: &str,
) -> Result<BTreeMap<String, PathBuf>, Failure> {
    scan_lean_tree_opts(root, umbrella_prefix, true)
}

/// Scan a Lean directory tree (`root`) under `umbrella_prefix`, optionally
/// requiring a root `<umbrella_prefix>.lean` umbrella file.
fn scan_lean_tree_opts(
    root: &Path,
    umbrella_prefix: &str,
    require_umbrella: bool,
) -> Result<BTreeMap<String, PathBuf>, Failure> {
    let meta = fs::symlink_metadata(root).map_err(|_| {
        Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        )
    })?;
    if meta.file_type().is_symlink() || !meta.file_type().is_dir() {
        return Err(Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        ));
    }

    let mut modules = BTreeMap::new();
    for entry in WalkDir::new(root)
        .follow_links(false)
        .sort_by_file_name()
        .into_iter()
        .skip(1)
    {
        let entry = entry.map_err(|e| {
            Failure::new(
                2,
                "snapshot",
                format!("cannot read {}: {e}", root.display()),
            )
        })?;
        let path = entry.path().to_path_buf();
        if entry.file_type().is_symlink() {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("unexpected symlink in source tree: {}", path.display()),
            ));
        }
        if entry.file_type().is_dir() {
            continue;
        }
        regular(&path, "snapshot")?;

        let rel_path = path.strip_prefix(root).unwrap();
        let relative = rel_path.to_string_lossy().replace('\\', "/");
        if PARTS
            .iter()
            .any(|part| relative.ends_with(&format!(".{part}")))
            || relative.ends_with(".ilean")
        {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("compiled artifact in source root: {relative}"),
            ));
        }

        if let Some(stem) = relative.strip_suffix(".lean") {
            let components: Vec<&str> = stem.split('/').collect();
            if components.first().copied() != Some(umbrella_prefix)
                || !components.iter().copied().all(is_lean_ident)
            {
                return Err(Failure::new(
                    1,
                    "snapshot",
                    format!("unmappable Lean source: {relative}"),
                ));
            }
            let module = components.join(".");
            if modules.insert(module.clone(), path).is_some() {
                return Err(Failure::new(
                    1,
                    "snapshot",
                    format!("duplicate module: {module}"),
                ));
            }
        } else if !(require_umbrella
            && umbrella_prefix == "Trusted"
            && (relative == "lean-toolchain" || relative == "foundation-lock.json"))
        {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("unexpected non-Lean file in source tree: {relative}"),
            ));
        }
    }

    if require_umbrella
        && (umbrella_prefix == "Trusted" || !modules.is_empty())
        && !modules.contains_key(umbrella_prefix)
    {
        return Err(Failure::new(
            1,
            "snapshot",
            format!("missing {umbrella_prefix}.lean umbrella"),
        ));
    }
    Ok(modules)
}

/// Holds validated repository source headers, topological build orders, and
/// module-level trust tiers from [`Checker::preflight_and_order_modules`].
struct OrderedPreflight {
    imports: BTreeMap<String, Vec<ImportEdge>>,
    module_tiers: BTreeMap<String, TrustTier>,
    trusted_order: Vec<String>,
    theory_order: Vec<String>,
}

/// Audits repository trust boundaries across Pass 1 and Pass 2 while wrapping
/// [`cargo_anneal::Checker`] with synchronized stage and cache lifecycles.
pub struct Checker {
    inner: cargo_anneal::Checker,
    modules: BTreeMap<String, PathBuf>,
    theory_modules: BTreeMap<String, PathBuf>,
    sysroot_foundation: Option<(PathBuf, Vec<String>)>,
    require_correspondence: bool,
    miri_cache_dir: Option<PathBuf>,
    require_mir_wp: bool,
}

impl Checker {
    /// Create a new repository [`Checker`] with `require_mir_wp = true` by
    /// default and optional `ANNEAL_MIRI_CACHE_DIR` discovery.
    pub fn new(checkout: &Path, lean: Option<&Path>) -> io::Result<Self> {
        let inner = cargo_anneal::Checker::new(checkout, lean)?;
        let miri_cache_dir = env::var_os("ANNEAL_MIRI_CACHE_DIR")
            .filter(|v| !v.is_empty())
            .map(PathBuf::from);
        Ok(Self {
            inner,
            modules: BTreeMap::new(),
            theory_modules: BTreeMap::new(),
            sysroot_foundation: None,
            require_correspondence: false,
            miri_cache_dir,
            require_mir_wp: true,
        })
    }

    /// Create a new repository [`Checker`] using a closed environment allowlist
    /// (`require_mir_wp = true` by default).
    pub fn new_with_env<I>(checkout: &Path, lean: Option<&Path>, ambient_env: I) -> io::Result<Self>
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let inner = cargo_anneal::Checker::new_with_env(checkout, lean, ambient_env)?;
        Ok(Self {
            inner,
            modules: BTreeMap::new(),
            theory_modules: BTreeMap::new(),
            sysroot_foundation: None,
            require_correspondence: false,
            miri_cache_dir: None,
            require_mir_wp: true,
        })
    }

    /// Return the path to the private `0o700` staging directory.
    pub fn stage(&self) -> &Path {
        self.inner.stage()
    }

    /// Return `true` if Lean compilation has started on the current stage.
    pub fn execution_began(&self) -> bool {
        self.inner.execution_began()
    }

    /// Return the sanitized child-process environment allowlist.
    pub fn environment(&self) -> &BTreeMap<String, String> {
        self.inner.environment()
    }

    /// Return the staged Pass 1 `Trusted.*` module map.
    pub fn modules(&self) -> &BTreeMap<String, PathBuf> {
        &self.modules
    }

    /// Return the staged Pass 1 `Anneal.*` (`theory/`) module map.
    pub fn theory_modules(&self) -> &BTreeMap<String, PathBuf> {
        &self.theory_modules
    }

    /// Return a shared reference to the [`AdmittedToolchain`], if admitted.
    pub fn admitted(&self) -> Result<&AdmittedToolchain, Failure> {
        self.inner.admitted()
    }

    /// Return a mutable reference to the [`AdmittedToolchain`], if admitted.
    pub fn admitted_mut(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        self.inner.admitted_mut()
    }

    /// Wipe and recreate the private `0o700` staging directory while clearing
    /// all staged repository module maps and cached sysroot digests.
    pub fn reset_stage(&mut self) -> Result<(), Failure> {
        self.modules.clear();
        self.theory_modules.clear();
        self.sysroot_foundation = None;
        self.inner.reset_stage()
    }

    /// Authenticate the Lean 4.34.1 binary and `foundation-lock.json` artifacts
    /// after invalidating any cached sysroot-foundation state.
    pub fn tool_admission(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        self.sysroot_foundation = None;
        self.inner.tool_admission()
    }

    /// Run external target verification via
    /// [`cargo_anneal::Checker::run_target`] after clearing repository-stage
    /// maps and cached sysroot state.
    pub fn run_target(&mut self, request: &TargetAuditRequest) -> Result<Json, Failure> {
        self.modules.clear();
        self.theory_modules.clear();
        self.sysroot_foundation = None;
        self.inner.run_target(request)
    }

    /// Execute `lean` inside the private stage with the sanitized environment.
    pub fn process(&mut self, label: &str, arguments: &[String]) -> Result<String, Failure> {
        self.inner.process(label, arguments)
    }

    /// Execute `lean` inside the private stage with an optional hermetic
    /// `LEAN_PATH` override.
    pub fn process_with_path(
        &mut self,
        label: &str,
        arguments: &[String],
        lean_path: Option<&OsStr>,
    ) -> Result<String, Failure> {
        self.inner.process_with_path(label, arguments, lean_path)
    }

    /// Write a `<module>.setup.json` descriptor for `lean --setup`.
    pub fn write_setup_json(
        &self,
        module: &str,
        imports: &[ImportEdge],
    ) -> Result<PathBuf, Failure> {
        self.inner.write_setup_json(module, imports)
    }

    /// Configure whether Pass 2 (`vendor/lean-miri/`,
    /// `trusted/correspondence/`, and `correspondence/`) is mandatory even if
    /// those directories are absent.
    pub fn set_require_correspondence(&mut self, require: bool) {
        self.require_correspondence = require;
    }

    /// Configure an optional cache directory for verified `Miri.*` `.olean`
    /// artifacts (`execution_machine_closure` in `UPSTREAM_PIN.json`).
    pub fn set_miri_cache_dir(&mut self, cache_dir: Option<PathBuf>) {
        self.miri_cache_dir = cache_dir;
    }

    /// Configure whether the Pass 1 `"audit"` inspector unconditionally
    /// requires `Trusted.MirAst`, `Trusted.MirSemantics`, and `Anneal.MirWp`
    /// to be present, and whether checkout hygiene verifies
    /// `bundled_resources.rs` parity (defaults to `true`; only disabled in
    /// minimal synthetic unit test fixtures; even when `false`, the `"audit"`
    /// check still runs if any MIR or `PureLift` module is loaded).
    pub fn set_require_mir_wp(&mut self, require: bool) {
        self.require_mir_wp = require;
    }

    /// Authenticate the toolchain sysroot `{Init,Std,Lean}*` `.olean` manifest
    /// against `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256` and cache its module
    /// list for Pass 2 inspection.
    pub fn ensure_sysroot_foundation(&mut self) -> Result<&[String], Failure> {
        let (prefix, foundation_graph) = {
            let adm = self.inner.admitted()?;
            (adm.prefix.clone(), adm.foundation_graph.clone())
        };
        let needs_verify = match &self.sysroot_foundation {
            Some((cached_prefix, _)) => *cached_prefix != prefix,
            None => true,
        };
        if needs_verify {
            let modules = verify_sysroot_foundation(&prefix, &foundation_graph)?;
            self.sysroot_foundation = Some((prefix, modules));
        }
        Ok(self.sysroot_foundation.as_ref().unwrap().1.as_slice())
    }

    #[doc(hidden)]
    pub fn set_sysroot_foundation_for_test(&mut self, modules: Vec<String>) -> Result<(), Failure> {
        let prefix = self.inner.admitted()?.prefix.clone();
        self.sysroot_foundation = Some((prefix, modules));
        Ok(())
    }

    /// Invoke `TrustedBoundary.lean` with a typed [`InspectorRequest`].
    pub fn inspect(&mut self, request: InspectorRequest) -> Result<Json, Failure> {
        match request {
            InspectorRequest::Headers { sources } => self.inner.inspect_headers(&sources),
            InspectorRequest::TargetAudit { request } => self.inner.inspect_target(&request),
            InspectorRequest::Preflight { sources } => {
                let req = {
                    let adm = self.inner.admitted()?;
                    let arts_arr: Vec<Json> = adm
                        .artifacts
                        .iter()
                        .map(|(k, parts)| json!([k, parts.to_wire()]))
                        .collect();
                    let src_pairs: Vec<(&str, std::borrow::Cow<'_, str>)> = sources
                        .iter()
                        .map(|(m, p)| (m.as_str(), p.to_string_lossy()))
                        .collect();
                    json!({
                        "mode": "preflight",
                        "sysroot": adm.prefix.to_string_lossy(),
                        "artifacts": arts_arr,
                        "foundation": adm.foundation_modules(),
                        "graph": &adm.foundation_graph,
                        "axioms": &adm.axioms,
                        "sources": src_pairs,
                    })
                };
                self.inner.invoke_inspector("preflight", &req)
            }
            InspectorRequest::CorrespondencePreflight {
                search_path,
                trusted,
                theory,
                vendor_miri,
                module_tiers,
                sources,
            } => {
                self.ensure_sysroot_foundation()?;
                self.inspect_correspondence_preflight_sandboxed(
                    &search_path,
                    &trusted,
                    &theory,
                    &vendor_miri,
                    &module_tiers,
                    &sources,
                )
            }
            InspectorRequest::Audit {
                trusted,
                theory,
                module_tiers,
            } => {
                let req = {
                    let adm = self.inner.admitted()?;
                    let arts_arr: Vec<Json> = adm
                        .artifacts
                        .iter()
                        .map(|(k, parts)| json!([k, parts.to_wire()]))
                        .collect();
                    let tiers: Vec<(&str, String)> = module_tiers
                        .iter()
                        .map(|(m, t)| (m.as_str(), t.render()))
                        .collect();
                    json!({
                        "mode": "audit",
                        "sysroot": adm.prefix.to_string_lossy(),
                        "artifacts": arts_arr,
                        "foundation": adm.foundation_modules(),
                        "graph": &adm.graph,
                        "axioms": &adm.axioms,
                        "trusted": trusted,
                        "theory": theory,
                        "moduleTiers": tiers,
                        "requireMirWp": self.require_mir_wp,
                    })
                };
                self.inner.invoke_inspector("audit", &req)
            }
            InspectorRequest::CorrespondenceAudit {
                search_path,
                trusted,
                corr_trusted,
                theory,
                corr_theory,
                vendor_miri,
                module_tiers,
            } => {
                self.ensure_sysroot_foundation()?;
                let req = {
                    let adm = self.inner.admitted()?;
                    let sysroot_foundation = self
                        .sysroot_foundation
                        .as_ref()
                        .map_or(&[][..], |(_, mods)| mods.as_slice());
                    let sp: Vec<std::borrow::Cow<'_, str>> =
                        search_path.iter().map(|p| p.to_string_lossy()).collect();
                    let tiers: Vec<(&str, String)> = module_tiers
                        .iter()
                        .map(|(m, t)| (m.as_str(), t.render()))
                        .collect();
                    let has_vendor_miri = !vendor_miri.is_empty();
                    let has_correspondence = !corr_trusted.is_empty() || !corr_theory.is_empty();
                    (
                        json!({
                            "mode": "correspondence-audit",
                            "sysroot": adm.prefix.to_string_lossy(),
                            "searchPath": sp,
                            "foundation": adm.foundation_modules(),
                            "sysrootFoundation": sysroot_foundation,
                            "axioms": &adm.axioms,
                            "trusted": trusted,
                            "corrTrusted": corr_trusted,
                            "theory": theory,
                            "corrTheory": corr_theory,
                            "vendorMiri": vendor_miri,
                            "moduleTiers": tiers,
                        }),
                        has_vendor_miri,
                        has_correspondence,
                    )
                };
                let (req, has_vendor_miri, has_correspondence) = req;
                let report = self.inner.invoke_inspector("correspondence-audit", &req)?;
                let Some(obj) = report.as_object() else {
                    return Err(Failure::operational(
                        "correspondence-audit",
                        "expected JSON object from correspondence audit",
                    ));
                };
                validate_correspondence_report(obj, has_vendor_miri, has_correspondence)?;
                Ok(report)
            }
        }
    }

    fn scan_and_stage_tree_opts(
        &self,
        root: &Path,
        umbrella_prefix: &str,
        stage_subdir: &str,
        require_umbrella: bool,
    ) -> Result<BTreeMap<String, PathBuf>, Failure> {
        scan_lean_tree_opts(root, umbrella_prefix, require_umbrella)?
            .into_iter()
            .map(|(mod_name, raw_path)| {
                let staged_path = self
                    .inner
                    .stage()
                    .join(stage_subdir)
                    .join(format!("{}.lean", mod_name.replace('.', "/")));
                stage_regular_file(&raw_path, &staged_path, "snapshot")?;
                Ok((mod_name, staged_path))
            })
            .collect()
    }

    /// Run preflight, tier extraction, import-boundary validation, and
    /// topological ordering for Pass 1 (`trusted/lean` + `theory`) and Pass 2
    /// (`trusted/correspondence` + `correspondence`).
    #[allow(clippy::too_many_arguments)]
    fn preflight_and_order_modules(
        &mut self,
        trusted_map: &BTreeMap<String, PathBuf>,
        theory_map: &BTreeMap<String, PathBuf>,
        base_tiers: &BTreeMap<String, TrustTier>,
        extra_trusted_allowed: &BTreeSet<String>,
        extra_theory_allowed: &BTreeSet<String>,
        inventory_err: &str,
        trusted_cycle_msg: &str,
        theory_cycle_msg: &str,
    ) -> Result<OrderedPreflight, Failure> {
        let sources: Vec<(String, PathBuf)> = trusted_map
            .iter()
            .chain(theory_map.iter())
            .map(|(n, p)| (n.clone(), p.clone()))
            .collect();
        let pf_res: PreflightResult =
            serde_json::from_value(self.inspect(InspectorRequest::Preflight { sources })?)
                .map_err(|_| Failure::operational("preflight", inventory_err))?;

        let mut imports: BTreeMap<String, Vec<ImportEdge>> = BTreeMap::new();
        let mut module_tiers = base_tiers.clone();
        {
            let adm = self.inner.admitted()?;
            for h in pf_res.headers {
                let mod_name = h.module;
                let is_trusted = trusted_map.contains_key(&mod_name);
                if is_trusted {
                    let raw_tier = h.trust_tier.ok_or_else(|| {
                        Failure::policy(
                            "preflight",
                            format!("missing trust tier for Trusted module {mod_name}"),
                        )
                    })?;
                    let tier = TrustTier::parse(&raw_tier).ok_or_else(|| {
                        Failure::policy(
                            "preflight",
                            format!("invalid trust tier {raw_tier} for Trusted module {mod_name}"),
                        )
                    })?;
                    module_tiers.insert(mod_name.clone(), tier);
                }
                for edge in &h.imports {
                    let imp_mod = edge.module.as_str();
                    let allowed = if is_trusted {
                        adm.foundation_graph.contains_key(imp_mod)
                            || trusted_map.contains_key(imp_mod)
                            || extra_trusted_allowed.contains(imp_mod)
                    } else {
                        adm.foundation_graph.contains_key(imp_mod)
                            || trusted_map.contains_key(imp_mod)
                            || theory_map.contains_key(imp_mod)
                            || extra_trusted_allowed.contains(imp_mod)
                            || extra_theory_allowed.contains(imp_mod)
                    };
                    if !allowed {
                        return Err(Failure::policy(
                            "preflight",
                            format!("foreign/missing import {imp_mod} in {mod_name}"),
                        ));
                    }
                }
                imports.insert(mod_name, h.imports);
            }
        }

        let expected_count = trusted_map.len() + theory_map.len();
        if imports.len() != expected_count
            || !trusted_map.keys().all(|m| imports.contains_key(m))
            || !theory_map.keys().all(|m| imports.contains_key(m))
        {
            return Err(Failure::operational("preflight", inventory_err));
        }

        let trusted_order = topo_sort_modules(
            trusted_map.keys().cloned().collect(),
            &imports,
            trusted_cycle_msg,
        )?;
        let theory_order = topo_sort_modules(
            theory_map.keys().cloned().collect(),
            &imports,
            theory_cycle_msg,
        )?;

        Ok(OrderedPreflight {
            imports,
            module_tiers,
            trusted_order,
            theory_order,
        })
    }

    /// Run the complete repository boundary check (Cargo hygiene, Pass 1
    /// `trusted/lean/` + `theory/`, and Pass 2 correspondence when present or
    /// required).
    pub fn run(&mut self) -> Result<Json, Failure> {
        let root = self.inner.root().to_path_buf();
        if let Some(cache_dir) = &self.miri_cache_dir {
            ensure_miri_cache_outside_checkout(&root, cache_dir)?;
        }
        check_checkout_cargo_hygiene(&root, self.require_mir_wp)?;
        self.reset_stage()?;

        // Scan and stage repository trees before `tool_admission` so missing
        // source directories or umbrellas fail in phase `"snapshot"`
        // (`code == 1`) before probing the external `--lean` binary
        // (`cli_environment.rs`).
        let source = root.join("trusted/lean");
        let theory_dir = root.join("theory");
        self.modules = self.scan_and_stage_tree_opts(&source, "Trusted", "src/trusted", true)?;
        self.theory_modules = if fs::symlink_metadata(&theory_dir).is_ok() {
            self.scan_and_stage_tree_opts(&theory_dir, "Anneal", "src/theory", false)?
        } else {
            BTreeMap::new()
        };
        if !self.theory_modules.is_empty() && !self.theory_modules.contains_key("Anneal") {
            return Err(Failure::new(1, "snapshot", "missing Anneal.lean umbrella"));
        }

        self.tool_admission()?;

        let modules_snap = self.modules.clone();
        let theory_snap = self.theory_modules.clone();
        let preflight = self.preflight_and_order_modules(
            &modules_snap,
            &theory_snap,
            &BTreeMap::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            "incomplete source-header inventory",
            "Trusted import cycle",
            "Theory import cycle",
        )?;

        for module in &preflight.trusted_order {
            let edge_list = preflight.imports[module].clone();
            let staged_src_path = self.modules[module].clone();
            self.inner.mark_execution_began();
            self.inner.compile_lean_module(
                module,
                &staged_src_path,
                edge_list,
                "lib",
                false,
                false,
            )?;
        }

        for module in &preflight.theory_order {
            let edge_list = preflight.imports[module].clone();
            let staged_src_path = self.theory_modules[module].clone();
            self.inner.mark_execution_began();
            self.inner.compile_lean_module(
                module,
                &staged_src_path,
                edge_list,
                "theory-lib",
                true,
                false,
            )?;
        }

        let audit_req = InspectorRequest::Audit {
            trusted: self.modules.keys().cloned().collect(),
            theory: self.theory_modules.keys().cloned().collect(),
            module_tiers: preflight.module_tiers.clone(),
        };
        let mut report = self.inspect(audit_req)?;
        let version = self.inner.admitted()?.version.clone();
        {
            let rep_obj = report.as_object_mut().unwrap();
            rep_obj.insert("toolchain".to_string(), json!(version));
            rep_obj.insert(
                "guarantee".to_string(),
                json!(
                    "kernel dependency closure, module-origin separation, and Cargo DAG boundary"
                ),
            );
        }

        if let Some(corr_report) = self.run_correspondence(&preflight.module_tiers)?
            && let (Some(rep_obj), Some(corr_obj)) =
                (report.as_object_mut(), corr_report.as_object())
        {
            for (k, v) in corr_obj {
                rep_obj.insert(k.clone(), v.clone());
            }
        }

        Ok(report)
    }

    /// Execute Pass 2 (`"correspondence-audit"`) when
    /// `self.require_correspondence` is set or any of `vendor/lean-miri`,
    /// `trusted/correspondence`, or `correspondence` exists under the root.
    fn run_correspondence(
        &mut self,
        base_tiers: &BTreeMap<String, TrustTier>,
    ) -> Result<Option<Json>, Failure> {
        let root = self.inner.root().to_path_buf();
        let vendor_dir = root.join("vendor/lean-miri");
        let corr_trusted_dir = root.join("trusted/correspondence");
        let corr_theory_dir = root.join("correspondence");

        let vendor_exists = fs::symlink_metadata(&vendor_dir).is_ok();
        let corr_trusted_exists = fs::symlink_metadata(&corr_trusted_dir).is_ok();
        let corr_theory_exists = fs::symlink_metadata(&corr_theory_dir).is_ok();

        if !self.require_correspondence
            && !vendor_exists
            && !corr_trusted_exists
            && !corr_theory_exists
        {
            return Ok(None);
        }
        if !vendor_exists || !corr_trusted_exists || !corr_theory_exists {
            return Err(Failure::policy(
                "correspondence",
                "missing required correspondence directories (vendor/lean-miri, trusted/correspondence, correspondence)",
            ));
        }

        let pin = verify_upstream_pin(&vendor_dir)?;
        let expected_sources = pin.expected_source_digests();
        let corr_report = self.run_correspondence_with_closure(
            base_tiers,
            &vendor_dir,
            &pin.commit,
            &pin.execution_machine_closure,
            &expected_sources,
        )?;
        Ok(Some(corr_report))
    }

    /// Execute Pass 2 staging, foundation `"preflight"`, sysroot
    /// authentication, vendor Miri staging, Pass 2 compile-environment
    /// `"correspondence-preflight"`, Pass 2 compilation, and
    /// `"correspondence-audit"` for an authenticated vendor Miri closure.
    ///
    /// Production callers enter strictly via [`Checker::run`], which
    /// authenticates `vendor/lean-miri/UPSTREAM_PIN.json` with
    /// [`verify_upstream_pin`] before invoking this method.
    pub fn run_correspondence_with_closure(
        &mut self,
        base_tiers: &BTreeMap<String, TrustTier>,
        vendor_dir: &Path,
        miri_commit: &str,
        closure_entries: &[MiriClosureEntry],
        expected_sources: &BTreeMap<String, String>,
    ) -> Result<Json, Failure> {
        let root = self.inner.root().to_path_buf();
        let corr_trusted_dir = root.join("trusted/correspondence");
        let corr_theory_dir = root.join("correspondence");

        let corr_trusted_modules =
            self.scan_and_stage_tree_opts(&corr_trusted_dir, "Trusted", "src/corr-trusted", false)?;
        if !corr_trusted_modules.contains_key("Trusted.Correspondence") {
            return Err(Failure::policy(
                "snapshot",
                "missing Trusted/Correspondence.lean umbrella in trusted/correspondence",
            ));
        }

        let corr_theory_modules =
            self.scan_and_stage_tree_opts(&corr_theory_dir, "Anneal", "src/corr-theory", false)?;
        if !corr_theory_modules.contains_key("Anneal.MirCorrespondenceProof") {
            return Err(Failure::policy(
                "snapshot",
                "missing Anneal/MirCorrespondenceProof.lean in correspondence",
            ));
        }

        // Run Phase 1 (`"preflight"`) over `trusted/correspondence/` and
        // `correspondence/` before compiling any Pass 2 module.
        let extra_trusted_allowed: BTreeSet<String> = self
            .modules
            .keys()
            .cloned()
            .chain(closure_entries.iter().map(|e| e.module.clone()))
            .collect();
        let extra_theory_allowed: BTreeSet<String> = self.theory_modules.keys().cloned().collect();
        let preflight = self.preflight_and_order_modules(
            &corr_trusted_modules,
            &corr_theory_modules,
            base_tiers,
            &extra_trusted_allowed,
            &extra_theory_allowed,
            "incomplete correspondence header inventory",
            "Trusted correspondence import cycle",
            "Correspondence proof import cycle",
        )?;

        // Authenticate the toolchain sysroot `.olean` manifest before compiling
        // any vendored or correspondence module against `Init`/`Std`/`Lean`.
        self.ensure_sysroot_foundation()?;

        let miri_lib =
            self.verify_and_stage_miri_entries(vendor_dir, closure_entries, expected_sources)?;

        // Compile `Trusted.Correspondence.*` into `lib/` and
        // `Anneal.MirCorrespondenceProof.*` into `theory-lib/` inside
        // per-module OS-level `bwrap` sandboxes. For `Trusted` modules,
        // `corr_theory_lib` is neither mounted nor in `LEAN_PATH`, so they
        // cannot resolve compiled `theory/` or `correspondence/` modules even
        // if an import slipped past preflight.
        let stage = self.inner.stage().to_path_buf();
        let corr_trusted_lib = stage.join("lib");
        let corr_theory_lib = stage.join("theory-lib");
        fs::create_dir_all(&corr_trusted_lib)
            .map_err(|e| Failure::operational("compile", e.to_string()))?;
        fs::create_dir_all(&corr_theory_lib)
            .map_err(|e| Failure::operational("compile", e.to_string()))?;
        let search_dirs = vec![
            corr_trusted_lib.clone(),
            corr_theory_lib.clone(),
            miri_lib.clone(),
        ];

        // Re-parse every Pass 2 source under the Pass 2 union compile parser
        // environment (`foundation` + Pass 1 `trusted`/`theory` + pinned
        // `vendor/lean-miri` with `loadExts := true`) inside an isolated
        // `bwrap` sandbox before compiling any Pass 2 module, rejecting
        // unscoped `Miri.*`/`Lean.*`/`Std.*` syntax (such as `throwError` and
        // `m!`) and any `namespace`, namespaced declaration, or candidate
        // `open` resolution (resisting unimported decoy namespaces) targeting
        // a namespace with scoped `ScopedEnvExtension` entries.
        let corr_preflight_sources: Vec<(String, PathBuf)> = corr_trusted_modules
            .iter()
            .chain(corr_theory_modules.iter())
            .map(|(n, p)| (n.clone(), p.clone()))
            .collect();
        let corr_pf_req = InspectorRequest::CorrespondencePreflight {
            search_path: search_dirs.clone(),
            trusted: self.modules.keys().cloned().collect(),
            theory: self.theory_modules.keys().cloned().collect(),
            vendor_miri: closure_entries.iter().map(|e| e.module.clone()).collect(),
            module_tiers: base_tiers.clone(),
            sources: corr_preflight_sources.clone(),
        };
        let corr_pf_res: PreflightResult = serde_json::from_value(self.inspect(corr_pf_req)?)
            .map_err(|_| {
                Failure::operational(
                    "correspondence-preflight",
                    "incomplete correspondence compile-environment preflight result",
                )
            })?;
        if corr_pf_res.headers.len() != corr_preflight_sources.len() {
            return Err(Failure::operational(
                "correspondence-preflight",
                "incomplete correspondence compile-environment preflight inventory",
            ));
        }

        let corr_trusted_src_root = stage.join("src/corr-trusted");
        for module in &preflight.trusted_order {
            let staged_src = &corr_trusted_modules[module];
            let entry_rel = staged_src
                .strip_prefix(&corr_trusted_src_root)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
            let entry_rel_str = entry_rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/");
            // Importing the 160-module `Miri.Interpreter.ExecutionMachine`
            // closure consumes ~1.7 GiB of Lean's `-M` allocator at startup,
            // so Pass 2 uses `-M4096` rather than Pass 1's `-M2048`.
            self.sandbox_compile_pass2_module(&Pass2CompileSpec {
                module,
                src_root: &corr_trusted_src_root,
                entry_rel_path: &entry_rel_str,
                ro_libs: &[
                    (&corr_trusted_lib, "/work/lib"),
                    (&miri_lib, "/work/miri-lib"),
                ],
                sandbox_lean_path: "/work/lib:/work/miri-lib",
                out_lib_root: &corr_trusted_lib,
                warning_as_error: false,
            })?;
        }

        let corr_theory_src_root = stage.join("src/corr-theory");
        for module in &preflight.theory_order {
            let staged_src = &corr_theory_modules[module];
            let entry_rel = staged_src
                .strip_prefix(&corr_theory_src_root)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
            let entry_rel_str = entry_rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/");
            self.sandbox_compile_pass2_module(&Pass2CompileSpec {
                module,
                src_root: &corr_theory_src_root,
                entry_rel_path: &entry_rel_str,
                ro_libs: &[
                    (&corr_trusted_lib, "/work/lib"),
                    (&corr_theory_lib, "/work/theory-lib"),
                    (&miri_lib, "/work/miri-lib"),
                ],
                sandbox_lean_path: "/work/lib:/work/theory-lib:/work/miri-lib",
                out_lib_root: &corr_theory_lib,
                warning_as_error: true,
            })?;
        }

        let corr_req = InspectorRequest::CorrespondenceAudit {
            search_path: search_dirs,
            trusted: self.modules.keys().cloned().collect(),
            corr_trusted: corr_trusted_modules.keys().cloned().collect(),
            theory: self.theory_modules.keys().cloned().collect(),
            corr_theory: corr_theory_modules.keys().cloned().collect(),
            vendor_miri: closure_entries.iter().map(|e| e.module.clone()).collect(),
            module_tiers: preflight.module_tiers,
        };
        let mut corr_report = self.inspect(corr_req)?;
        if let Some(obj) = corr_report.as_object_mut() {
            validate_correspondence_report(
                obj,
                !closure_entries.is_empty(),
                !corr_trusted_modules.is_empty() || !corr_theory_modules.is_empty(),
            )?;
            obj.insert("miriCommit".to_string(), json!(miri_commit));
            obj.insert(
                "miriClosureModules".to_string(),
                json!(closure_entries.len()),
            );
        } else {
            return Err(Failure::operational(
                "correspondence-audit",
                "expected JSON object from correspondence audit",
            ));
        }
        Ok(corr_report)
    }

    /// Stage, restore from the digest-gated cache or compile synchronously,
    /// verify every staged source and output `.olean` companion digest, and
    /// write newly compiled artifacts to `self.miri_cache_dir` only after
    /// verification succeeds.
    pub fn verify_and_stage_miri_entries(
        &mut self,
        vendor_dir: &Path,
        entries: &[MiriClosureEntry],
        expected_sources: &BTreeMap<String, String>,
    ) -> Result<PathBuf, Failure> {
        if let Some(cache_dir) = &self.miri_cache_dir {
            ensure_miri_cache_outside_checkout(self.inner.root(), cache_dir)?;
        }
        let stage = self.inner.stage().to_path_buf();
        let miri_src_root = stage.join("src/vendor-miri");
        let miri_lib = stage.join("miri-lib");
        fs::create_dir_all(&miri_lib)
            .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
        for entry in entries {
            let Some(expected_src_sha) = expected_sources.get(&entry.path) else {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "missing pinned source digest for Miri closure module {}",
                        entry.path
                    ),
                ));
            };
            let src_file = vendor_dir.join(&entry.path);
            let staged_src = miri_src_root.join(&entry.path);
            let actual_src_sha = stage_regular_file(&src_file, &staged_src, "miri-pin")?;
            if !actual_src_sha.eq_ignore_ascii_case(expected_src_sha) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "staged Miri source SHA-256 mismatch for {}: expected {expected_src_sha}, got {actual_src_sha}",
                        entry.path
                    ),
                ));
            }
        }

        for entry in entries {
            let rel_stem = entry.module.replace('.', "/");
            let rel_olean = format!("{rel_stem}.olean");
            let staged_olean = miri_lib.join(&rel_olean);
            if let Some(parent) = staged_olean.parent() {
                fs::create_dir_all(parent)
                    .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
            }
            let mut cache_hit = false;
            if let Some(cache_dir) = &self.miri_cache_dir {
                let cached =
                    prepare_nosymlink_cache_path(cache_dir, &rel_olean, false, "miri-pin")?;
                let olean_matches = sha256_file(&cached, "miri-pin")
                    .is_ok_and(|h| h.eq_ignore_ascii_case(&entry.olean_sha256));
                let mut parts_match = true;
                for (part, expected_opt) in [
                    ("olean.server", entry.olean_server_sha256.as_deref()),
                    ("olean.private", entry.olean_private_sha256.as_deref()),
                ] {
                    let rel_part = format!("{rel_stem}.{part}");
                    let cached_part =
                        prepare_nosymlink_cache_path(cache_dir, &rel_part, false, "miri-pin")?;
                    let ok = match expected_opt {
                        Some(exp_sha) => sha256_file(&cached_part, "miri-pin")
                            .is_ok_and(|h| h.eq_ignore_ascii_case(exp_sha)),
                        None => fs::symlink_metadata(&cached_part).is_err(),
                    };
                    if !ok {
                        parts_match = false;
                    }
                }
                if olean_matches && parts_match {
                    stage_regular_file(&cached, &staged_olean, "miri-pin")?;
                    for (part, expected_opt) in [
                        ("olean.server", entry.olean_server_sha256.as_deref()),
                        ("olean.private", entry.olean_private_sha256.as_deref()),
                    ] {
                        if expected_opt.is_some() {
                            let rel_part = format!("{rel_stem}.{part}");
                            let cached_part = prepare_nosymlink_cache_path(
                                cache_dir, &rel_part, false, "miri-pin",
                            )?;
                            stage_regular_file(
                                &cached_part,
                                &miri_lib.join(&rel_part),
                                "miri-pin",
                            )?;
                        }
                    }
                    cache_hit = true;
                }
            }
            if cache_hit {
                let actual_olean_sha = sha256_file(&staged_olean, "miri-pin")?;
                if !actual_olean_sha.eq_ignore_ascii_case(&entry.olean_sha256) {
                    return Err(Failure::policy(
                        "miri-pin",
                        format!(
                            "compiled Miri .olean SHA-256 mismatch for {}: expected {}, got {actual_olean_sha}",
                            entry.module, entry.olean_sha256
                        ),
                    ));
                }
                for (part, expected_opt) in [
                    ("olean.server", entry.olean_server_sha256.as_deref()),
                    ("olean.private", entry.olean_private_sha256.as_deref()),
                ] {
                    let staged_part = miri_lib.join(format!("{rel_stem}.{part}"));
                    match expected_opt {
                        Some(exp_sha) => {
                            if fs::symlink_metadata(&staged_part).is_err() {
                                return Err(Failure::policy(
                                    "miri-pin",
                                    format!(
                                        "missing compiled Miri .{part} sidecar for {}",
                                        entry.module
                                    ),
                                ));
                            }
                            let actual_sha = sha256_file(&staged_part, "miri-pin")?;
                            if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                                return Err(Failure::policy(
                                    "miri-pin",
                                    format!(
                                        "compiled Miri .{part} SHA-256 mismatch for {}: expected {exp_sha}, got {actual_sha}",
                                        entry.module
                                    ),
                                ));
                            }
                        }
                        None => {
                            if fs::symlink_metadata(&staged_part).is_ok() {
                                return Err(Failure::policy(
                                    "miri-pin",
                                    format!("unexpected Miri .{part} sidecar for {}", entry.module),
                                ));
                            }
                        }
                    }
                }
                continue;
            }

            // Cold vendor elaboration runs inside an isolated per-module OS
            // sandbox whose sole host-backed writable directory is a fresh
            // owner-only temporary directory outside `self.stage`, the
            // checkout, `$HOME`, and `self.miri_cache_dir`.
            self.inner.mark_execution_began();
            let mut out_builder = tempfile::Builder::new();
            out_builder.prefix("anneal-miri-out-");
            #[cfg(unix)]
            out_builder.permissions(fs::Permissions::from_mode(0o700));
            let module_out_dir = out_builder
                .tempdir()
                .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
            let out_olean = module_out_dir.path().join(&rel_olean);
            if let Some(parent) = out_olean.parent() {
                fs::create_dir_all(parent)
                    .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
            }
            self.sandbox_compile_miri_module(
                &format!("compile-{}", entry.module),
                &miri_src_root,
                &miri_lib,
                module_out_dir.path(),
                &rel_olean,
                &entry.path,
            )?;

            let actual_olean_sha = sha256_file(&out_olean, "miri-pin")?;
            if !actual_olean_sha.eq_ignore_ascii_case(&entry.olean_sha256) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "compiled Miri .olean SHA-256 mismatch for {}: expected {}, got {actual_olean_sha}",
                        entry.module, entry.olean_sha256
                    ),
                ));
            }
            let mut expected_out_files = BTreeSet::from([rel_olean.clone()]);
            for (part, expected_opt) in [
                ("olean.server", entry.olean_server_sha256.as_deref()),
                ("olean.private", entry.olean_private_sha256.as_deref()),
            ] {
                let rel_part = format!("{rel_stem}.{part}");
                let out_part = module_out_dir.path().join(&rel_part);
                match expected_opt {
                    Some(exp_sha) => {
                        if fs::symlink_metadata(&out_part).is_err() {
                            return Err(Failure::policy(
                                "miri-pin",
                                format!(
                                    "missing compiled Miri .{part} sidecar for {}",
                                    entry.module
                                ),
                            ));
                        }
                        let actual_sha = sha256_file(&out_part, "miri-pin")?;
                        if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                            return Err(Failure::policy(
                                "miri-pin",
                                format!(
                                    "compiled Miri .{part} SHA-256 mismatch for {}: expected {exp_sha}, got {actual_sha}",
                                    entry.module
                                ),
                            ));
                        }
                        expected_out_files.insert(rel_part);
                    }
                    None => {
                        if fs::symlink_metadata(&out_part).is_ok() {
                            return Err(Failure::policy(
                                "miri-pin",
                                format!("unexpected Miri .{part} sidecar for {}", entry.module),
                            ));
                        }
                    }
                }
            }
            if entry.olean_server_sha256.is_some() || entry.olean_private_sha256.is_some() {
                expected_out_files.insert(format!("{rel_stem}.ir"));
                expected_out_files.insert(format!("{rel_stem}.ir.sig"));
            }
            verify_no_unexpected_sandbox_outputs(
                module_out_dir.path(),
                &expected_out_files,
                &rel_olean,
                &entry.module,
            )?;

            let staged_olean_sha = stage_regular_file(&out_olean, &staged_olean, "miri-pin")?;
            if !staged_olean_sha.eq_ignore_ascii_case(&entry.olean_sha256) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "staged Miri .olean SHA-256 mismatch for {}: expected {}, got {staged_olean_sha}",
                        entry.module, entry.olean_sha256
                    ),
                ));
            }
            for (part, expected_opt) in [
                ("olean.server", entry.olean_server_sha256.as_deref()),
                ("olean.private", entry.olean_private_sha256.as_deref()),
            ] {
                if let Some(exp_sha) = expected_opt {
                    let rel_part = format!("{rel_stem}.{part}");
                    let staged_part_sha = stage_regular_file(
                        &module_out_dir.path().join(&rel_part),
                        &miri_lib.join(&rel_part),
                        "miri-pin",
                    )?;
                    if !staged_part_sha.eq_ignore_ascii_case(exp_sha) {
                        return Err(Failure::policy(
                            "miri-pin",
                            format!(
                                "staged Miri .{part} SHA-256 mismatch for {}: expected {exp_sha}, got {staged_part_sha}",
                                entry.module
                            ),
                        ));
                    }
                }
            }

            if let Some(cache_dir) = &self.miri_cache_dir {
                write_cache_file(&staged_olean, cache_dir, &rel_olean, "miri-pin")?;
                for part in &OLEAN_PARTS[1..] {
                    let rel_part = format!("{rel_stem}.{part}");
                    let staged_part = miri_lib.join(&rel_part);
                    if fs::symlink_metadata(&staged_part).is_ok() {
                        write_cache_file(&staged_part, cache_dir, &rel_part, "miri-pin")?;
                    } else {
                        remove_cache_file(cache_dir, &rel_part, "miri-pin")?;
                    }
                }
            }
        }
        Ok(miri_lib)
    }

    fn inspect_correspondence_preflight_sandboxed(
        &mut self,
        search_path: &[PathBuf],
        trusted: &[String],
        theory: &[String],
        vendor_miri: &[String],
        module_tiers: &BTreeMap<String, TrustTier>,
        sources: &[(String, PathBuf)],
    ) -> Result<Json, Failure> {
        let mode = "correspondence-preflight";
        let (bwrap, lean_prefix, sandbox_lean) = self.resolve_bwrap_and_sandbox_lean(mode)?;

        let (foundation, inspector) = {
            let adm = self.inner.admitted()?;
            (adm.foundation_modules(), adm.inspector.clone())
        };
        let sysroot_foundation = self
            .sysroot_foundation
            .as_ref()
            .map_or(&[][..], |(_, mods)| mods.as_slice());

        let mut sp_binds: Vec<(PathBuf, String)> = Vec::new();
        for (i, dir) in search_path.iter().enumerate() {
            match fs::symlink_metadata(dir) {
                Ok(meta) => {
                    if meta.file_type().is_symlink() || !meta.is_dir() {
                        return Err(Failure::policy(
                            mode,
                            format!(
                                "invalid correspondence search_path entry (must be a regular directory): {}",
                                dir.display()
                            ),
                        ));
                    }
                    sp_binds.push((dir.clone(), format!("/work/sp-{i}")));
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => {
                    return Err(Failure::operational(
                        mode,
                        format!("cannot inspect search_path {}: {e}", dir.display()),
                    ));
                }
            }
        }
        let sandbox_sp: Vec<&str> = sp_binds.iter().map(|(_, dst)| dst.as_str()).collect();
        let src_binds: Vec<(PathBuf, String)> = sources
            .iter()
            .enumerate()
            .map(|(i, (_, p))| (p.clone(), format!("/work/src/s-{i}.lean")))
            .collect();
        let sandbox_sources: Vec<(&str, &str)> = sources
            .iter()
            .zip(src_binds.iter())
            .map(|((m, _), (_, dst))| (m.as_str(), dst.as_str()))
            .collect();
        let tiers: Vec<(&str, String)> = module_tiers
            .iter()
            .map(|(m, t)| (m.as_str(), t.render()))
            .collect();

        let req = json!({
            "mode": mode,
            "sysroot": "/toolchain",
            "searchPath": sandbox_sp,
            "foundation": foundation,
            "sysrootFoundation": sysroot_foundation,
            "trusted": trusted,
            "theory": theory,
            "vendorMiri": vendor_miri,
            "moduleTiers": tiers,
            "sources": sandbox_sources,
        });

        let counter = self.inner.next_counter();
        let request_path = self
            .inner
            .stage()
            .join(format!("request-{counter:03}-{mode}.json"));
        let req_bytes = serde_json::to_vec(&req)
            .map_err(|e| Failure::new(2, mode, format!("cannot serialize request: {e}")))?;
        fs::write(&request_path, req_bytes)
            .map_err(|e| Failure::new(2, mode, format!("cannot write request: {e}")))?;

        let mut out_builder = tempfile::Builder::new();
        out_builder.prefix("anneal-corr-pf-out-");
        #[cfg(unix)]
        out_builder.permissions(fs::Permissions::from_mode(0o700));
        let out_dir = out_builder
            .tempdir()
            .map_err(|e| Failure::operational(mode, e.to_string()))?;

        let args = build_bwrap_correspondence_preflight_args(
            &lean_prefix,
            &sandbox_lean,
            &inspector,
            &request_path,
            &sp_binds,
            &src_binds,
            out_dir.path(),
        );
        let output = Command::new(bwrap)
            .args(&args)
            .current_dir(out_dir.path())
            .env_clear()
            .output()
            .map_err(|e| {
                Failure::new(
                    2,
                    mode,
                    format!(
                        "could not execute bubblewrap sandbox {}: {e}",
                        bwrap.display()
                    ),
                )
            })?;

        let allowed = BTreeSet::from(["result.json".to_string()]);
        verify_no_unexpected_sandbox_outputs_for_phase(
            out_dir.path(),
            &allowed,
            None,
            mode,
            mode,
            "correspondence-preflight",
        )?;

        let result_path = out_dir.path().join("result.json");
        let result_map = parse_inspector_output(mode, &output, &result_path)?;
        Ok(Json::Object(result_map))
    }

    fn resolve_bwrap_and_sandbox_lean(
        &self,
        label: &str,
    ) -> Result<(&'static Path, PathBuf, PathBuf), Failure> {
        #[cfg(not(target_os = "linux"))]
        {
            return Err(Failure::operational(
                label,
                "Pass 2 OS-level sandboxing requires Linux bubblewrap (/usr/bin/bwrap)",
            ));
        }

        #[cfg(target_os = "linux")]
        {
            let bwrap = ["/usr/bin/bwrap", "/bin/bwrap"]
                .into_iter()
                .map(Path::new)
                .find(|p| fs::metadata(p).is_ok_and(|m| m.is_file()))
                .ok_or_else(|| {
                    Failure::operational(
                        label,
                        "Pass 2 OS-level sandboxing requires Linux bubblewrap (/usr/bin/bwrap)",
                    )
                })?;

            let lean_prefix = self.inner.admitted()?.prefix.clone();
            let lean_canon = fs::canonicalize(self.inner.lean()).map_err(|e| {
                Failure::operational(label, format!("cannot resolve Lean binary path: {e}"))
            })?;
            let lean_rel = lean_canon.strip_prefix(&lean_prefix).map_err(|_| {
                Failure::operational(
                    label,
                    format!(
                        "Lean binary {} does not reside under admitted toolchain prefix {}",
                        lean_canon.display(),
                        lean_prefix.display()
                    ),
                )
            })?;
            let sandbox_lean = Path::new("/toolchain").join(lean_rel);
            Ok((bwrap, lean_prefix, sandbox_lean))
        }
    }

    fn sandbox_compile_miri_module(
        &mut self,
        label: &str,
        miri_src_root: &Path,
        miri_lib: &Path,
        module_out_dir: &Path,
        rel_olean: &str,
        entry_rel_path: &str,
    ) -> Result<(), Failure> {
        let (bwrap, lean_prefix, sandbox_lean) = self.resolve_bwrap_and_sandbox_lean(label)?;
        let args = build_bwrap_miri_compile_args(
            &lean_prefix,
            &sandbox_lean,
            miri_src_root,
            miri_lib,
            module_out_dir,
            rel_olean,
            entry_rel_path,
        );
        let _ = self.inner.next_counter();
        let output = Command::new(bwrap)
            .args(&args)
            .current_dir(module_out_dir)
            .env_clear()
            .output()
            .map_err(|e| {
                Failure::new(
                    2,
                    label,
                    format!(
                        "could not execute bubblewrap sandbox {}: {e}",
                        bwrap.display()
                    ),
                )
            })?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let detail = if stderr.trim().is_empty() {
                stdout.trim()
            } else {
                stderr.trim()
            };
            return Err(Failure::new(
                2,
                label,
                format!("sandboxed Lean exited {:?}: {detail}", output.status.code()),
            ));
        }
        Ok(())
    }

    fn sandbox_compile_pass2_module(&mut self, spec: &Pass2CompileSpec<'_>) -> Result<(), Failure> {
        let label = format!("compile-{}", spec.module);
        let rel_olean = format!("{}.olean", spec.module.replace('.', "/"));
        let mut out_builder = tempfile::Builder::new();
        out_builder.prefix("anneal-pass2-out-");
        #[cfg(unix)]
        out_builder.permissions(fs::Permissions::from_mode(0o700));
        let module_out_dir = out_builder
            .tempdir()
            .map_err(|e| Failure::operational("compile", e.to_string()))?;
        let out_olean = module_out_dir.path().join(&rel_olean);
        if let Some(parent) = out_olean.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
        }

        let (bwrap, lean_prefix, sandbox_lean) = self.resolve_bwrap_and_sandbox_lean(&label)?;
        let args = build_bwrap_pass2_compile_args(
            &lean_prefix,
            &sandbox_lean,
            spec,
            module_out_dir.path(),
            &rel_olean,
        );
        self.inner.mark_execution_began();
        let _ = self.inner.next_counter();
        let output = Command::new(bwrap)
            .args(&args)
            .current_dir(module_out_dir.path())
            .env_clear()
            .output()
            .map_err(|e| {
                Failure::new(
                    2,
                    &label,
                    format!(
                        "could not execute bubblewrap sandbox {}: {e}",
                        bwrap.display()
                    ),
                )
            })?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let detail = if stderr.trim().is_empty() {
                stdout.trim()
            } else {
                stderr.trim()
            };
            return Err(Failure::new(
                2,
                &label,
                format!("sandboxed Lean exited {:?}: {detail}", output.status.code()),
            ));
        }

        regular(&out_olean, "compile")?;
        let expected_out_files = BTreeSet::from([rel_olean.clone()]);
        verify_no_unexpected_sandbox_outputs_for_phase(
            module_out_dir.path(),
            &expected_out_files,
            Some(&rel_olean),
            spec.module,
            "compile",
            "Pass 2",
        )?;

        let staged_olean = spec.out_lib_root.join(&rel_olean);
        stage_regular_file(&out_olean, &staged_olean, "compile")?;
        regular(&staged_olean, "compile")?;
        Ok(())
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorErrResponse {
    ok: bool,
    category: String,
    message: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorOkResponse {
    ok: bool,
    result: serde_json::Map<String, Json>,
}

struct Pass2CompileSpec<'a> {
    module: &'a str,
    src_root: &'a Path,
    entry_rel_path: &'a str,
    ro_libs: &'a [(&'a Path, &'a str)],
    sandbox_lean_path: &'a str,
    out_lib_root: &'a Path,
    warning_as_error: bool,
}

fn parse_inspector_output(
    mode: &str,
    output: &std::process::Output,
    result_path: &Path,
) -> Result<serde_json::Map<String, Json>, Failure> {
    if !output.status.success() {
        if output.status.code() == Some(1)
            && result_path.is_file()
            && let Ok(text) = fs::read_to_string(result_path)
            && let Ok(resp) = serde_json::from_str::<InspectorErrResponse>(&text)
            && !resp.ok
            && resp.category == "policy"
            && resp.message.starts_with("policy:")
        {
            return Err(Failure::new(1, mode, resp.message));
        }
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(Failure::new(
            2,
            mode,
            format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
        ));
    }

    let resp_text = fs::read_to_string(result_path)
        .map_err(|e| Failure::new(2, mode, format!("missing/malformed inspector result: {e}")))?;
    let resp: InspectorOkResponse = serde_json::from_str(&resp_text)
        .map_err(|_| Failure::new(2, mode, "unexpected inspector protocol response"))?;
    if !resp.ok {
        return Err(Failure::new(
            2,
            mode,
            "unexpected inspector protocol response",
        ));
    }
    Ok(resp.result)
}

fn bwrap_base_args(lean_prefix: &Path) -> Vec<OsString> {
    let mut args: Vec<OsString> = Vec::new();
    for flag in [
        "--unshare-all",
        "--die-with-parent",
        "--new-session",
        "--clearenv",
        "--tmpfs",
        "/",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
        "--ro-bind",
        "/usr/lib",
        "/usr/lib",
        "--ro-bind-try",
        "/usr/lib64",
        "/usr/lib64",
        "--ro-bind-try",
        "/lib",
        "/lib",
        "--ro-bind-try",
        "/lib64",
        "/lib64",
        "--ro-bind-try",
        "/etc/ld.so.cache",
        "/etc/ld.so.cache",
        "--ro-bind-try",
        "/etc/ld.so.conf",
        "/etc/ld.so.conf",
        "--ro-bind-try",
        "/etc/ld.so.conf.d",
        "/etc/ld.so.conf.d",
    ] {
        args.push(OsString::from(flag));
    }
    if lean_prefix.starts_with("/nix/store") {
        args.push(OsString::from("--ro-bind"));
        args.push(OsString::from("/nix/store"));
        args.push(OsString::from("/nix/store"));
    }
    args.push(OsString::from("--ro-bind"));
    args.push(lean_prefix.as_os_str().to_os_string());
    args.push(OsString::from("/toolchain"));
    args
}

fn push_bwrap_env_args(args: &mut Vec<OsString>, lean_path: Option<&str>) {
    for flag in [
        "--tmpfs",
        "/work/tmp",
        "--chdir",
        "/work",
        "--setenv",
        "PATH",
        "/toolchain/bin",
    ] {
        args.push(OsString::from(flag));
    }
    if let Some(lp) = lean_path {
        args.push(OsString::from("--setenv"));
        args.push(OsString::from("LEAN_PATH"));
        args.push(OsString::from(lp));
    }
    for flag in [
        "--setenv",
        "HOME",
        "/work/tmp",
        "--setenv",
        "TMPDIR",
        "/work/tmp",
        "--setenv",
        "LANG",
        "C.UTF-8",
        "--setenv",
        "LC_ALL",
        "C.UTF-8",
        "--",
    ] {
        args.push(OsString::from(flag));
    }
}

fn build_bwrap_miri_compile_args(
    lean_prefix: &Path,
    sandbox_lean: &Path,
    miri_src_root: &Path,
    miri_lib: &Path,
    module_out_dir: &Path,
    rel_olean: &str,
    entry_rel_path: &str,
) -> Vec<OsString> {
    let mut args = bwrap_base_args(lean_prefix);

    args.push(OsString::from("--ro-bind"));
    args.push(miri_src_root.as_os_str().to_os_string());
    args.push(OsString::from("/work/src/vendor-miri"));

    args.push(OsString::from("--ro-bind"));
    args.push(miri_lib.as_os_str().to_os_string());
    args.push(OsString::from("/work/miri-lib"));

    args.push(OsString::from("--bind"));
    args.push(module_out_dir.as_os_str().to_os_string());
    args.push(OsString::from("/work/out"));

    push_bwrap_env_args(&mut args, Some("/work/miri-lib"));

    args.push(sandbox_lean.as_os_str().to_os_string());
    for arg in [
        "-j1",
        "-M2048",
        "-t0",
        "-DElab.async=false",
        "-Ddebug.skipKernelTC=false",
        "-R",
        "src/vendor-miri",
        "-o",
    ] {
        args.push(OsString::from(arg));
    }
    args.push(OsString::from(format!("out/{rel_olean}")));
    args.push(OsString::from(format!("src/vendor-miri/{entry_rel_path}")));
    args
}

fn build_bwrap_correspondence_preflight_args(
    lean_prefix: &Path,
    sandbox_lean: &Path,
    inspector: &Path,
    request_path: &Path,
    sp_binds: &[(PathBuf, String)],
    src_binds: &[(PathBuf, String)],
    out_dir: &Path,
) -> Vec<OsString> {
    let mut args = bwrap_base_args(lean_prefix);

    args.push(OsString::from("--ro-bind"));
    args.push(inspector.as_os_str().to_os_string());
    args.push(OsString::from("/work/TrustedBoundary.lean"));

    args.push(OsString::from("--ro-bind"));
    args.push(request_path.as_os_str().to_os_string());
    args.push(OsString::from("/work/request.json"));

    for (host_dir, sandbox_dst) in sp_binds {
        args.push(OsString::from("--ro-bind"));
        args.push(host_dir.as_os_str().to_os_string());
        args.push(OsString::from(sandbox_dst));
    }
    for (host_src, sandbox_dst) in src_binds {
        args.push(OsString::from("--ro-bind"));
        args.push(host_src.as_os_str().to_os_string());
        args.push(OsString::from(sandbox_dst));
    }

    args.push(OsString::from("--bind"));
    args.push(out_dir.as_os_str().to_os_string());
    args.push(OsString::from("/work/out"));

    push_bwrap_env_args(&mut args, None);

    args.push(sandbox_lean.as_os_str().to_os_string());
    for arg in [
        "-j1",
        "-M8192",
        "--run",
        "/work/TrustedBoundary.lean",
        "/work/request.json",
        "/work/out/result.json",
    ] {
        args.push(OsString::from(arg));
    }
    args
}

fn build_bwrap_pass2_compile_args(
    lean_prefix: &Path,
    sandbox_lean: &Path,
    spec: &Pass2CompileSpec<'_>,
    module_out_dir: &Path,
    rel_olean: &str,
) -> Vec<OsString> {
    let mut args = bwrap_base_args(lean_prefix);

    args.push(OsString::from("--ro-bind"));
    args.push(spec.src_root.as_os_str().to_os_string());
    args.push(OsString::from("/work/src/pass2"));

    for (host_lib, sandbox_dst) in spec.ro_libs {
        args.push(OsString::from("--ro-bind"));
        args.push(host_lib.as_os_str().to_os_string());
        args.push(OsString::from(*sandbox_dst));
    }

    args.push(OsString::from("--bind"));
    args.push(module_out_dir.as_os_str().to_os_string());
    args.push(OsString::from("/work/out"));

    push_bwrap_env_args(&mut args, Some(spec.sandbox_lean_path));

    args.push(sandbox_lean.as_os_str().to_os_string());
    for arg in [
        "-j1",
        "-M4096",
        "-t0",
        "-DElab.async=false",
        "-Ddebug.skipKernelTC=false",
    ] {
        args.push(OsString::from(arg));
    }
    if spec.warning_as_error {
        args.push(OsString::from("-DwarningAsError=true"));
    }
    for arg in ["-R", "src/pass2", "-o"] {
        args.push(OsString::from(arg));
    }
    args.push(OsString::from(format!("out/{rel_olean}")));
    args.push(OsString::from(format!("src/pass2/{}", spec.entry_rel_path)));
    args
}

fn verify_no_unexpected_sandbox_outputs(
    out_root: &Path,
    expected_files: &BTreeSet<String>,
    rel_olean: &str,
    module: &str,
) -> Result<(), Failure> {
    verify_no_unexpected_sandbox_outputs_for_phase(
        out_root,
        expected_files,
        Some(rel_olean),
        module,
        "miri-pin",
        "Miri",
    )
}

fn verify_no_unexpected_sandbox_outputs_for_phase(
    out_root: &Path,
    expected_files: &BTreeSet<String>,
    allowed_dir_from_rel: Option<&str>,
    label: &str,
    phase: &str,
    kind: &str,
) -> Result<(), Failure> {
    let mut allowed_dirs = BTreeSet::new();
    let mut ancestor = allowed_dir_from_rel.and_then(|p| Path::new(p).parent());
    while let Some(dir) = ancestor {
        if dir.as_os_str().is_empty() {
            break;
        }
        let mut segs = Vec::new();
        for comp in dir.components() {
            if let Component::Normal(s) = comp
                && let Some(s) = s.to_str()
            {
                segs.push(s);
            }
        }
        if !segs.is_empty() {
            allowed_dirs.insert(segs.join("/"));
        }
        ancestor = dir.parent();
    }

    for item in WalkDir::new(out_root).follow_links(false) {
        let item = item.map_err(|e| {
            Failure::policy(
                phase,
                format!("cannot inspect sandbox output for {label}: {e}"),
            )
        })?;
        if item.path() == out_root {
            continue;
        }
        let ft = item.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!(
                    "symlink forbidden in sandboxed {kind} output for {label}: {}",
                    item.path().display()
                ),
            ));
        }
        let rel = item.path().strip_prefix(out_root).map_err(|e| {
            Failure::operational(phase, format!("invalid sandbox relative path: {e}"))
        })?;
        let mut segs = Vec::new();
        for comp in rel.components() {
            let Component::Normal(os) = comp else {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "invalid path component in sandboxed {kind} output for {label}: {}",
                        item.path().display()
                    ),
                ));
            };
            let Some(s) = os.to_str() else {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "non-UTF-8 path in sandboxed {kind} output for {label}: {}",
                        item.path().display()
                    ),
                ));
            };
            segs.push(s);
        }
        let rel_str = segs.join("/");
        if ft.is_dir() {
            if !allowed_dirs.contains(&rel_str) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unexpected directory in sandboxed {kind} output for {label}: {rel_str}"
                    ),
                ));
            }
        } else if ft.is_file() {
            if !expected_files.contains(&rel_str) {
                return Err(Failure::policy(
                    phase,
                    format!("unexpected file in sandboxed {kind} output for {label}: {rel_str}"),
                ));
            }
        } else {
            return Err(Failure::policy(
                phase,
                format!("unexpected file type in sandboxed {kind} output for {label}: {rel_str}"),
            ));
        }
    }
    Ok(())
}

/// Fail-closed validation of the `"correspondence-audit"` JSON result returned
/// by `TrustedBoundary.lean`.
///
/// Requires `miriReplay == true` and a numeric `miriReplayedDeclarations`
/// count (positive whenever `has_vendor_miri` is `true`).
///
/// Whenever `has_correspondence` is `true`, also requires
/// `correspondenceReplay == true` and positive, equal
/// `correspondenceDeclarations` and `correspondenceReplayedDeclarations`
/// counts. `TrustedBoundary.lean` counts replayed correspondence declarations
/// in the kernel environment that its repository replay returns, so a
/// regression that skips that replay reports zero and fails here.
///
/// Whenever `has_correspondence` is `false` (vendor-only mode, which replays
/// no repository declarations), rejects any report that claims a
/// correspondence replay (`correspondenceReplay == true` or a positive
/// `correspondenceReplayedDeclarations` count).
fn validate_correspondence_report(
    result: &serde_json::Map<String, Json>,
    has_vendor_miri: bool,
    has_correspondence: bool,
) -> Result<(), Failure> {
    let phase = "correspondence-audit";
    if result.get("miriReplay").and_then(Json::as_bool) != Some(true) {
        return Err(Failure::policy(
            phase,
            "correspondence audit did not confirm vendor Miri kernel replay",
        ));
    }
    let Some(replayed) = result
        .get("miriReplayedDeclarations")
        .and_then(Json::as_u64)
    else {
        return Err(Failure::operational(
            phase,
            "missing miriReplayedDeclarations in correspondence audit result",
        ));
    };
    if has_vendor_miri && replayed == 0 {
        return Err(Failure::policy(
            phase,
            "correspondence audit replayed zero vendor Miri declarations",
        ));
    }
    let corr_replay = result.get("correspondenceReplay").and_then(Json::as_bool);
    let corr_replayed = result
        .get("correspondenceReplayedDeclarations")
        .and_then(Json::as_u64);
    if !has_correspondence {
        if corr_replay == Some(true) || corr_replayed.is_some_and(|n| n > 0) {
            return Err(Failure::policy(
                phase,
                "correspondence audit reported correspondence kernel replay without correspondence modules",
            ));
        }
        return Ok(());
    }
    if corr_replay != Some(true) {
        return Err(Failure::policy(
            phase,
            "correspondence audit did not confirm correspondence kernel replay",
        ));
    }
    let Some(corr_decls) = result
        .get("correspondenceDeclarations")
        .and_then(Json::as_u64)
    else {
        return Err(Failure::operational(
            phase,
            "missing correspondenceDeclarations in correspondence audit result",
        ));
    };
    if corr_decls == 0 {
        return Err(Failure::policy(
            phase,
            "correspondence audit replayed zero correspondence declarations",
        ));
    }
    let Some(corr_replayed) = corr_replayed else {
        return Err(Failure::operational(
            phase,
            "missing correspondenceReplayedDeclarations in correspondence audit result",
        ));
    };
    if corr_replayed == 0 {
        return Err(Failure::policy(
            phase,
            "correspondence audit kernel-replayed zero correspondence declarations",
        ));
    }
    if corr_replayed != corr_decls {
        return Err(Failure::policy(
            phase,
            format!(
                "correspondence audit kernel-replayed {corr_replayed} of {corr_decls} correspondence declarations"
            ),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_correspondence_replay_fields_fail_closed() {
        let obj = |v: Json| v.as_object().unwrap().clone();

        // Missing or false `miriReplay` fails closed with policy code 1.
        let err_missing = validate_correspondence_report(
            &obj(json!({"miriReplayedDeclarations": 10})),
            true,
            false,
        )
        .unwrap_err();
        assert_eq!(err_missing.code, 1);
        let err_false = validate_correspondence_report(
            &obj(json!({"miriReplay": false, "miriReplayedDeclarations": 10})),
            true,
            false,
        )
        .unwrap_err();
        assert_eq!(err_false.code, 1);

        // Missing `miriReplayedDeclarations` fails closed (operational code 2).
        let err_no_count =
            validate_correspondence_report(&obj(json!({"miriReplay": true})), true, false)
                .unwrap_err();
        assert_eq!(err_no_count.code, 2);

        // Zero replayed vendor declarations fails closed when vendor modules
        // are present.
        let err_zero = validate_correspondence_report(
            &obj(json!({"miriReplay": true, "miriReplayedDeclarations": 0})),
            true,
            false,
        )
        .unwrap_err();
        assert_eq!(err_zero.code, 1);

        // Zero vendor declarations is permitted only when `vendor_miri` is
        // empty.
        validate_correspondence_report(
            &obj(json!({"miriReplay": true, "miriReplayedDeclarations": 0})),
            false,
            false,
        )
        .unwrap();

        // When correspondence modules are present, `correspondenceReplay` and
        // positive `correspondenceDeclarations` are also mandatory.
        let err_missing_corr = validate_correspondence_report(
            &obj(json!({"miriReplay": true, "miriReplayedDeclarations": 38728})),
            true,
            true,
        )
        .unwrap_err();
        assert_eq!(err_missing_corr.code, 1);
        let err_zero_corr = validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 38728,
                "correspondenceReplay": true,
                "correspondenceDeclarations": 0
            })),
            true,
            true,
        )
        .unwrap_err();
        assert_eq!(err_zero_corr.code, 1);
        let err_no_corr_count = validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 38728,
                "correspondenceReplay": true
            })),
            true,
            true,
        )
        .unwrap_err();
        assert_eq!(err_no_corr_count.code, 2);

        // `correspondenceReplayedDeclarations` must be present (operational
        // code 2 otherwise), positive, and equal to
        // `correspondenceDeclarations`, and `correspondenceReplay` must be
        // `true` even when both counts agree (policy code 1 otherwise).
        let err_no_corr_replayed = validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 38728,
                "correspondenceReplay": true,
                "correspondenceDeclarations": 120
            })),
            true,
            true,
        )
        .unwrap_err();
        assert_eq!(err_no_corr_replayed.code, 2);
        for corr_replayed in [0, 119, 121] {
            let err_corr_replayed = validate_correspondence_report(
                &obj(json!({
                    "miriReplay": true,
                    "miriReplayedDeclarations": 38728,
                    "correspondenceReplay": true,
                    "correspondenceDeclarations": 120,
                    "correspondenceReplayedDeclarations": corr_replayed
                })),
                true,
                true,
            )
            .unwrap_err();
            assert_eq!(
                err_corr_replayed.code, 1,
                "unexpected result for {corr_replayed} replayed declarations: {err_corr_replayed}"
            );
        }
        let err_false_corr_replay = validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 38728,
                "correspondenceReplay": false,
                "correspondenceDeclarations": 120,
                "correspondenceReplayedDeclarations": 120
            })),
            true,
            true,
        )
        .unwrap_err();
        assert_eq!(err_false_corr_replay.code, 1);

        // Positive vendor + correspondence replay counts succeed.
        validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 38728,
                "correspondenceReplay": true,
                "correspondenceDeclarations": 120,
                "correspondenceReplayedDeclarations": 120
            })),
            true,
            true,
        )
        .unwrap();

        // Vendor-only mode accepts the zero correspondence fields that
        // `TrustedBoundary.lean` reports without correspondence modules, but
        // rejects any report claiming a correspondence replay.
        validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 21,
                "correspondenceReplay": false,
                "correspondenceDeclarations": 0,
                "correspondenceReplayedDeclarations": 0
            })),
            true,
            false,
        )
        .unwrap();
        let err_vendor_only_replay = validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 21,
                "correspondenceReplay": true,
                "correspondenceDeclarations": 0,
                "correspondenceReplayedDeclarations": 0
            })),
            true,
            false,
        )
        .unwrap_err();
        assert_eq!(err_vendor_only_replay.code, 1);
        let err_vendor_only_count = validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 21,
                "correspondenceReplay": false,
                "correspondenceDeclarations": 0,
                "correspondenceReplayedDeclarations": 5
            })),
            true,
            false,
        )
        .unwrap_err();
        assert_eq!(err_vendor_only_count.code, 1);
    }

    #[test]
    fn bwrap_miri_compile_args_enforce_isolation_and_readonly_inputs() {
        let args: Vec<String> = build_bwrap_miri_compile_args(
            Path::new("/opt/lean-4.34.1"),
            Path::new("/toolchain/bin/lean"),
            Path::new("/tmp/stage/src/vendor-miri"),
            Path::new("/tmp/stage/miri-lib"),
            Path::new("/tmp/miri-out-123"),
            "Miri/Memory/Identity.olean",
            "Miri/Memory/Identity.lean",
        )
        .into_iter()
        .map(|a| a.to_string_lossy().into_owned())
        .collect();

        for required in [
            "--unshare-all",
            "--die-with-parent",
            "--new-session",
            "--clearenv",
            "--tmpfs",
            "--chdir",
        ] {
            assert!(
                args.iter().any(|a| a == required),
                "missing required sandbox flag {required}: {args:?}"
            );
        }

        let rw_binds: Vec<(&str, &str)> = args
            .windows(3)
            .filter(|w| w[0] == "--bind")
            .map(|w| (w[1].as_str(), w[2].as_str()))
            .collect();
        assert_eq!(rw_binds, vec![("/tmp/miri-out-123", "/work/out")]);

        let ro_binds: Vec<(&str, &str)> = args
            .windows(3)
            .filter(|w| w[0] == "--ro-bind")
            .map(|w| (w[1].as_str(), w[2].as_str()))
            .collect();
        assert!(ro_binds.contains(&("/opt/lean-4.34.1", "/toolchain")));
        assert!(ro_binds.contains(&("/tmp/stage/src/vendor-miri", "/work/src/vendor-miri")));
        assert!(ro_binds.contains(&("/tmp/stage/miri-lib", "/work/miri-lib")));
        assert!(
            !args.iter().any(|a| a == "/usr/bin" || a == "/bin"),
            "host shell/utility directories must not be mounted: {args:?}"
        );
    }

    #[test]
    fn bwrap_correspondence_preflight_and_pass2_compile_args_enforce_isolation() {
        let pf_args: Vec<String> = build_bwrap_correspondence_preflight_args(
            Path::new("/opt/lean-4.34.1"),
            Path::new("/toolchain/bin/lean"),
            Path::new("/tmp/stage/TrustedBoundary.lean"),
            Path::new("/tmp/stage/request-001-correspondence-preflight.json"),
            &[
                (PathBuf::from("/tmp/stage/lib"), "/work/sp-0".to_string()),
                (
                    PathBuf::from("/tmp/stage/theory-lib"),
                    "/work/sp-1".to_string(),
                ),
                (
                    PathBuf::from("/tmp/stage/miri-lib"),
                    "/work/sp-2".to_string(),
                ),
            ],
            &[(
                PathBuf::from("/tmp/stage/src/corr-trusted/Trusted/Correspondence.lean"),
                "/work/src/s-0.lean".to_string(),
            )],
            Path::new("/tmp/corr-pf-out-123"),
        )
        .into_iter()
        .map(|a| a.to_string_lossy().into_owned())
        .collect();

        for required in [
            "--unshare-all",
            "--die-with-parent",
            "--new-session",
            "--clearenv",
            "-M8192",
            "--run",
        ] {
            assert!(
                pf_args.iter().any(|a| a == required),
                "missing required sandbox flag {required}: {pf_args:?}"
            );
        }
        let pf_rw_binds: Vec<(&str, &str)> = pf_args
            .windows(3)
            .filter(|w| w[0] == "--bind")
            .map(|w| (w[1].as_str(), w[2].as_str()))
            .collect();
        assert_eq!(pf_rw_binds, vec![("/tmp/corr-pf-out-123", "/work/out")]);

        let trusted_spec = Pass2CompileSpec {
            module: "Trusted.Correspondence",
            src_root: Path::new("/tmp/stage/src/corr-trusted"),
            entry_rel_path: "Trusted/Correspondence.lean",
            ro_libs: &[
                (Path::new("/tmp/stage/lib"), "/work/lib"),
                (Path::new("/tmp/stage/miri-lib"), "/work/miri-lib"),
            ],
            sandbox_lean_path: "/work/lib:/work/miri-lib",
            out_lib_root: Path::new("/tmp/stage/lib"),
            warning_as_error: false,
        };
        let trusted_args: Vec<String> = build_bwrap_pass2_compile_args(
            Path::new("/opt/lean-4.34.1"),
            Path::new("/toolchain/bin/lean"),
            &trusted_spec,
            Path::new("/tmp/pass2-out-1"),
            "Trusted/Correspondence.olean",
        )
        .into_iter()
        .map(|a| a.to_string_lossy().into_owned())
        .collect();
        assert!(trusted_args.iter().any(|a| a == "-M4096"));
        assert!(!trusted_args.iter().any(|a| a.contains("theory-lib")));
        assert!(!trusted_args.iter().any(|a| a == "-DwarningAsError=true"));

        let theory_spec = Pass2CompileSpec {
            module: "Anneal.MirCorrespondenceProof",
            src_root: Path::new("/tmp/stage/src/corr-theory"),
            entry_rel_path: "Anneal/MirCorrespondenceProof.lean",
            ro_libs: &[
                (Path::new("/tmp/stage/lib"), "/work/lib"),
                (Path::new("/tmp/stage/theory-lib"), "/work/theory-lib"),
                (Path::new("/tmp/stage/miri-lib"), "/work/miri-lib"),
            ],
            sandbox_lean_path: "/work/lib:/work/theory-lib:/work/miri-lib",
            out_lib_root: Path::new("/tmp/stage/theory-lib"),
            warning_as_error: true,
        };
        let theory_args: Vec<String> = build_bwrap_pass2_compile_args(
            Path::new("/opt/lean-4.34.1"),
            Path::new("/toolchain/bin/lean"),
            &theory_spec,
            Path::new("/tmp/pass2-out-2"),
            "Anneal/MirCorrespondenceProof.olean",
        )
        .into_iter()
        .map(|a| a.to_string_lossy().into_owned())
        .collect();
        assert!(theory_args.iter().any(|a| a == "-DwarningAsError=true"));
        assert!(theory_args.iter().any(|a| a == "/work/theory-lib"));
    }

    #[test]
    fn sandbox_output_check_allows_only_expected_regular_files() {
        let out_dir = tempfile::Builder::new()
            .prefix("anneal-sandbox-out-unit-")
            .tempdir()
            .unwrap();
        let mod_dir = out_dir.path().join("Miri/Memory");
        fs::create_dir_all(&mod_dir).unwrap();
        fs::write(mod_dir.join("QSortProof.olean"), b"olean").unwrap();
        fs::write(mod_dir.join("QSortProof.olean.server"), b"srv").unwrap();
        fs::write(mod_dir.join("QSortProof.olean.private"), b"priv").unwrap();
        fs::write(mod_dir.join("QSortProof.ir"), b"ir").unwrap();
        fs::write(mod_dir.join("QSortProof.ir.sig"), b"irsig").unwrap();

        let non_module_expected = BTreeSet::from(["Miri/Memory/QSortProof.olean".to_string()]);
        let err_non_mod = verify_no_unexpected_sandbox_outputs(
            out_dir.path(),
            &non_module_expected,
            "Miri/Memory/QSortProof.olean",
            "Miri.Memory.QSortProof",
        )
        .unwrap_err();
        assert_eq!(err_non_mod.code, 1);

        let module_expected = BTreeSet::from([
            "Miri/Memory/QSortProof.olean".to_string(),
            "Miri/Memory/QSortProof.olean.server".to_string(),
            "Miri/Memory/QSortProof.olean.private".to_string(),
            "Miri/Memory/QSortProof.ir".to_string(),
            "Miri/Memory/QSortProof.ir.sig".to_string(),
        ]);
        verify_no_unexpected_sandbox_outputs(
            out_dir.path(),
            &module_expected,
            "Miri/Memory/QSortProof.olean",
            "Miri.Memory.QSortProof",
        )
        .unwrap();

        #[cfg(unix)]
        {
            fs::remove_file(mod_dir.join("QSortProof.ir")).unwrap();
            std::os::unix::fs::symlink(
                mod_dir.join("QSortProof.olean"),
                mod_dir.join("QSortProof.ir"),
            )
            .unwrap();
            let err_sym = verify_no_unexpected_sandbox_outputs(
                out_dir.path(),
                &module_expected,
                "Miri/Memory/QSortProof.olean",
                "Miri.Memory.QSortProof",
            )
            .unwrap_err();
            assert_eq!(err_sym.code, 1);
        }
    }
}
