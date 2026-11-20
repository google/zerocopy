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
use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde_json::json;
use walkdir::WalkDir;

use cargo_anneal::{
    AdmittedToolchain, Failure, ImportEdge, Json, OLEAN_PARTS, PARTS, PreflightResult, SandboxMode,
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
        let mut inner = cargo_anneal::Checker::new(checkout, lean)?;
        // Pass 1 (`trusted/lean/` + `theory/`) stays unchanged; Pass 2 switches
        // strictly to `SandboxMode::RequireBwrap` inside `run_correspondence`.
        inner.set_sandbox_mode(SandboxMode::Unsandboxed);
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
        let mut inner = cargo_anneal::Checker::new_with_env(checkout, lean, ambient_env)?;
        inner.set_sandbox_mode(SandboxMode::Unsandboxed);
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
        self.inner
            .set_sandbox_mode(SandboxMode::PreferBwrapOrLandlock);
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
                self.inner.set_sandbox_mode(SandboxMode::RequireBwrap);
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
                    let src_pairs: Vec<(&str, std::borrow::Cow<'_, str>)> = sources
                        .iter()
                        .map(|(m, p)| (m.as_str(), p.to_string_lossy()))
                        .collect();
                    json!({
                        "mode": "correspondence-preflight",
                        "sysroot": adm.prefix.to_string_lossy(),
                        "searchPath": sp,
                        "foundation": adm.foundation_modules(),
                        "sysrootFoundation": sysroot_foundation,
                        "trusted": trusted,
                        "theory": theory,
                        "vendorMiri": vendor_miri,
                        "moduleTiers": tiers,
                        "sources": src_pairs,
                    })
                };
                self.inner
                    .invoke_inspector("correspondence-preflight", &req)
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
        self.inner.set_sandbox_mode(SandboxMode::Unsandboxed);
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

        // Enforce Tier 1 `linux_bwrap` (`SandboxMode::RequireBwrap`) across
        // all three Pass 2 surfaces (cold `vendor/lean-miri/`,
        // `"correspondence-preflight"`, and `trusted/correspondence/` +
        // `correspondence/`, even on `--miri-cache-dir` cache hits).
        self.inner.set_sandbox_mode(SandboxMode::RequireBwrap);

        let miri_lib =
            self.verify_and_stage_miri_entries(vendor_dir, closure_entries, expected_sources)?;

        // Compile `Trusted.Correspondence.*` into `lib/` and
        // `Anneal.MirCorrespondenceProof.*` into `theory-lib/`. The `LEAN_PATH`
        // for `Trusted` modules omits `corr_theory_lib`, so they cannot resolve
        // compiled `theory/` or `correspondence/` modules even if an import
        // slipped past preflight.
        let stage = self.inner.stage().to_path_buf();
        let corr_trusted_lib = stage.join("lib");
        let corr_theory_lib = stage.join("theory-lib");
        fs::create_dir_all(&corr_trusted_lib)
            .map_err(|e| Failure::operational("compile", e.to_string()))?;
        fs::create_dir_all(&corr_theory_lib)
            .map_err(|e| Failure::operational("compile", e.to_string()))?;
        let corr_trusted_dirs = vec![corr_trusted_lib.clone(), miri_lib.clone()];
        let search_dirs = vec![corr_trusted_lib.clone(), corr_theory_lib.clone(), miri_lib];

        // Re-parse every Pass 2 source under the Pass 2 union compile parser
        // environment (`foundation` + Pass 1 `trusted`/`theory` + pinned
        // `vendor/lean-miri` with `loadExts := true`) before compiling any
        // Pass 2 module, rejecting unscoped `Miri.*`/`Lean.*`/`Std.*` syntax
        // (such as `throwError` and `m!`) and any `namespace`, namespaced
        // declaration, or candidate `open` resolution (resisting unimported
        // decoy namespaces) targeting a namespace with scoped
        // `ScopedEnvExtension` entries.
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
            let out_olean = corr_trusted_lib.join(format!("{}.olean", module.replace('.', "/")));
            self.inner.mark_execution_began();
            // Importing the 160-module `Miri.Interpreter.ExecutionMachine`
            // closure consumes ~1.7 GiB of Lean's `-M` allocator at startup,
            // so Pass 2 uses `-M4096` rather than Pass 1's `-M2048`.
            self.inner.compile_lean_module_with_root(
                module,
                &corr_trusted_src_root,
                staged_src,
                &out_olean,
                &corr_trusted_dirs,
                4096,
                false,
                &[],
                &[],
            )?;
            regular(&out_olean, "compile")?;
        }

        let corr_theory_src_root = stage.join("src/corr-theory");
        for module in &preflight.theory_order {
            let staged_src = &corr_theory_modules[module];
            let out_olean = corr_theory_lib.join(format!("{}.olean", module.replace('.', "/")));
            self.inner.mark_execution_began();
            self.inner.compile_lean_module_with_root(
                module,
                &corr_theory_src_root,
                staged_src,
                &out_olean,
                &search_dirs,
                4096,
                true,
                &[],
                &[],
            )?;
            regular(&out_olean, "compile")?;
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

        let miri_lean_dirs = vec![miri_lib.clone()];
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
            if !cache_hit {
                self.inner.mark_execution_began();
                self.inner.set_sandbox_mode(SandboxMode::RequireBwrap);
                let staged_src = miri_src_root.join(&entry.path);
                // Promote optional `.olean.server`/`.olean.private` sidecars so
                // the explicit SHA-256/presence policy below enforces the pin
                // with exit code 1, while validating and discarding Lean
                // `module` `.ir`/`.ir.sig` outputs without promoting them.
                let discarded_parts: &[&str] = if entry.olean_server_sha256.is_some()
                    || entry.olean_private_sha256.is_some()
                {
                    &["ir", "ir.sig"]
                } else {
                    &[]
                };
                self.inner.compile_lean_module_with_root(
                    &entry.module,
                    &miri_src_root,
                    &staged_src,
                    &staged_olean,
                    &miri_lean_dirs,
                    2048,
                    false,
                    &["olean.server", "olean.private"],
                    discarded_parts,
                )?;
            }
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
            if !cache_hit && let Some(cache_dir) = &self.miri_cache_dir {
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
            &obj(json!({"miriReplay": true, "miriReplayedDeclarations": 38718})),
            true,
            true,
        )
        .unwrap_err();
        assert_eq!(err_missing_corr.code, 1);
        let err_zero_corr = validate_correspondence_report(
            &obj(json!({
                "miriReplay": true,
                "miriReplayedDeclarations": 38718,
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
                "miriReplayedDeclarations": 38718,
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
                "miriReplayedDeclarations": 38718,
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
                    "miriReplayedDeclarations": 38718,
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
                "miriReplayedDeclarations": 38718,
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
                "miriReplayedDeclarations": 38718,
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
}
