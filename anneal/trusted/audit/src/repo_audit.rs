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

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::OsStr,
    fs, io,
    path::{Path, PathBuf},
    time::Duration,
};

use cargo_anneal::{
    AdmittedToolchain, Failure, ImportEdge, Json, OLEAN_PARTS, PARTS, ParallelDagPlan,
    PreflightResult, SandboxMode, TargetAuditRequest, default_compile_workers, is_lean_ident,
    regular, run_parallel_dag,
    sandbox::{SandboxRuntime, create_dir_mode},
    sha256_file, stage_regular_file, topo_sort_modules,
};
use serde_json::json;
use walkdir::WalkDir;

use crate::{
    cargo_boundary::check_checkout_cargo_hygiene,
    miri_pin::{
        MiriClosureEntry, ensure_miri_cache_outside_checkout, prepare_nosymlink_cache_path,
        remove_cache_file, verify_sysroot_foundation, verify_upstream_pin, write_cache_file,
    },
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
    /// source commands being inspected, authenticating optional staged
    /// `base_trusted_sources` (`"baseSources"`, such as Pass 1 `Trusted`
    /// modules during Pass 2 preflight) directly from disk.
    Preflight { sources: Vec<(String, PathBuf)>, base_trusted_sources: Vec<(String, PathBuf)> },
    /// Parses Pass 2 `(module_name, staged_path)` pairs
    /// (`"correspondence-preflight"`) against the authenticated Pass 2 compile
    /// parser environment (`foundation`, Pass 1 `trusted`/`theory`, and pinned
    /// `vendor_miri` with `loadExts := true`) before compiling any Pass 2
    /// module, authenticating `base_trusted_sources` (`"baseSources"`, one per
    /// staged Pass 1 `trusted` module) directly from disk.
    CorrespondencePreflight {
        search_path: Vec<PathBuf>,
        trusted: Vec<String>,
        theory: Vec<String>,
        vendor_miri: Vec<String>,
        base_trusted_sources: Vec<(String, PathBuf)>,
        sources: Vec<(String, PathBuf)>,
    },
    /// Loads compiled Pass 1 `.olean`s (`"audit"`) with `loadExts := false`,
    /// verifies module-level trust tiers and namespace hygiene, and replays all
    /// non-foundation constants through the Lean kernel.
    Audit { trusted: Vec<String>, theory: Vec<String>, module_tiers: BTreeMap<String, TrustTier> },
    /// Loads Pass 2 correspondence and `lean-miri` closure `.olean`s
    /// (`"correspondence-audit"`) with `loadExts := false`, verifies
    /// `CorrOrigin` import/edge isolation and `.vendorMiri` purity,
    /// kernel-replays every non-`isPartial` `.vendorMiri` declaration onto the
    /// authenticated sysroot base on every run (cold compile and cache hit
    /// alike), kernel-replays all correspondence declarations onto that
    /// replayed vendor kernel environment, and verifies 36-root constant-cone
    /// purity, all 37 correspondence, choice-coupled, wiring, `AllowedStep`
    /// soundness, byte-codec, and canary claims, and reference-evaluator independence
    /// (reaching all 39 live `ExecutionMachine` `Miri.*` primitives from
    /// `[evalRefStep, initRefState]` without relying on `RefAllowedStep`,
    /// checking `AllowedStep` separately on `RefAllowedStep`, requiring
    /// isolated submodule placement and zero direct/transitive disallowed
    /// `Trusted` imports in `Trusted.Correspondence.*` evaluator submodules,
    /// and restricting `Trusted` dependencies across both cones to
    /// `Trusted.MirAst*`, `Trusted.MirModel`, and `Trusted.Correspondence*`,
    /// with human review of `trusted/correspondence/` and `Trusted.MirModel`
    /// remaining the semantic boundary).
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
/// with `"Anneal"`), rejecting symlinks, non-`.lean` files (except the
/// explicit manifest files allowed for that tree), and compiled artifacts in
/// the source tree and returning the map from dot-separated module name to
/// `.lean` path. `"Trusted"` requires a root `Trusted.lean` umbrella, whereas
/// `"Anneal"` uses domain-scoped umbrellas under `theory/Anneal/`.
pub fn scan_lean_tree(
    root: &Path,
    umbrella_prefix: &str,
) -> Result<BTreeMap<String, PathBuf>, Failure> {
    let (require_umbrella, allowed_non_lean): (bool, &[&str]) = match umbrella_prefix {
        "Trusted" => (true, &["lean-toolchain", "foundation-lock.json"]),
        "Anneal" => (false, &["bundle-manifest.json"]),
        _ => (true, &[]),
    };
    scan_lean_tree_opts(root, umbrella_prefix, require_umbrella, allowed_non_lean)
}

/// Scan a Lean directory tree (`root`) under `umbrella_prefix`, optionally
/// requiring a root `<umbrella_prefix>.lean` umbrella file and permitting only
/// the relative paths listed in `allowed_non_lean` as non-`.lean` regular files.
fn scan_lean_tree_opts(
    root: &Path,
    umbrella_prefix: &str,
    require_umbrella: bool,
    allowed_non_lean: &[&str],
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
    for entry in WalkDir::new(root).follow_links(false).sort_by_file_name().into_iter().skip(1) {
        let entry = entry.map_err(|e| {
            Failure::new(2, "snapshot", format!("cannot read {}: {e}", root.display()))
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
        if PARTS.iter().any(|part| relative.ends_with(&format!(".{part}")))
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
                return Err(Failure::new(1, "snapshot", format!("duplicate module: {module}")));
            }
        } else if !allowed_non_lean.contains(&relative.as_str()) {
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
    is_module: BTreeMap<String, bool>,
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
    pass1_imports: BTreeMap<String, Vec<ImportEdge>>,
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
            pass1_imports: BTreeMap::new(),
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
            pass1_imports: BTreeMap::new(),
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
        self.pass1_imports.clear();
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
        self.pass1_imports.clear();
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
    /// requires `Trusted.MirAst`, `Trusted.MirSemantics`, `Anneal.MirWp`, and
    /// `Anneal.MirWp.Canaries` to be present, and whether checkout hygiene
    /// verifies bundled resource parity (`verify_bundled_resources`; defaults
    /// to `true`, disabled only in synthetic test fixtures, and even then
    /// `"audit"` still runs if any of those modules or `Anneal.PureLift` is
    /// loaded).
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
            InspectorRequest::Preflight { sources, base_trusted_sources } => {
                let req = {
                    let adm = self.inner.admitted()?;
                    let arts_arr: Vec<Json> = adm
                        .artifacts
                        .iter()
                        .map(|(k, parts)| json!([k, parts.to_wire()]))
                        .collect();
                    let src_pairs: Vec<(&str, std::borrow::Cow<'_, str>)> =
                        sources.iter().map(|(m, p)| (m.as_str(), p.to_string_lossy())).collect();
                    let base_pairs: Vec<(&str, std::borrow::Cow<'_, str>)> = base_trusted_sources
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
                        "baseSources": base_pairs,
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
                base_trusted_sources,
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
                    let base_pairs: Vec<(&str, std::borrow::Cow<'_, str>)> = base_trusted_sources
                        .iter()
                        .map(|(m, p)| (m.as_str(), p.to_string_lossy()))
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
                        "baseSources": base_pairs,
                        "sources": src_pairs,
                    })
                };
                self.inner
                    .invoke_inspector("correspondence-preflight", &req)
            }
            InspectorRequest::Audit { trusted, theory, module_tiers } => {
                let req = {
                    let adm = self.inner.admitted()?;
                    let arts_arr: Vec<Json> = adm
                        .artifacts
                        .iter()
                        .map(|(k, parts)| json!([k, parts.to_wire()]))
                        .collect();
                    let tiers: Vec<(&str, String)> =
                        module_tiers.iter().map(|(m, t)| (m.as_str(), t.render())).collect();
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
                    let tiers: Vec<(&str, String)> =
                        module_tiers.iter().map(|(m, t)| (m.as_str(), t.render())).collect();
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
        allowed_non_lean: &[&str],
    ) -> Result<BTreeMap<String, PathBuf>, Failure> {
        scan_lean_tree_opts(root, umbrella_prefix, require_umbrella, allowed_non_lean)?
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
        base_trusted_modules: &BTreeMap<String, PathBuf>,
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
        let base_trusted_sources: Vec<(String, PathBuf)> =
            base_trusted_modules.iter().map(|(n, p)| (n.clone(), p.clone())).collect();
        let pf_res: PreflightResult = serde_json::from_value(
            self.inspect(InspectorRequest::Preflight { sources, base_trusted_sources })?,
        )
        .map_err(|_| Failure::operational("preflight", inventory_err))?;

        let mut imports: BTreeMap<String, Vec<ImportEdge>> = BTreeMap::new();
        let mut is_module: BTreeMap<String, bool> = BTreeMap::new();
        let mut module_tiers = base_tiers.clone();
        {
            let adm = self.inner.admitted()?;
            for h in pf_res.headers {
                let mod_name = h.module;
                let mod_is_module = h.is_module;
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
                is_module.insert(mod_name.clone(), mod_is_module);
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

        {
            let adm = self.inner.admitted()?;
            check_preflight_tier_imports(
                trusted_map.keys(),
                &imports,
                &module_tiers,
                &adm.foundation_graph,
            )?;
        }

        let trusted_order =
            topo_sort_modules(trusted_map.keys().cloned().collect(), &imports, trusted_cycle_msg)?;
        let theory_order =
            topo_sort_modules(theory_map.keys().cloned().collect(), &imports, theory_cycle_msg)?;

        Ok(OrderedPreflight { imports, is_module, module_tiers, trusted_order, theory_order })
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
        // source directories or `Trusted.lean` fail in phase `"snapshot"`
        // (`code == 1`) before probing the external `--lean` binary
        // (`cli_environment.rs`).
        let source = root.join("trusted/lean");
        let theory_dir = root.join("theory");
        self.modules = self.scan_and_stage_tree_opts(
            &source,
            "Trusted",
            "src/trusted",
            true,
            &["lean-toolchain", "foundation-lock.json"],
        )?;
        self.theory_modules = if fs::symlink_metadata(&theory_dir).is_ok() {
            self.scan_and_stage_tree_opts(
                &theory_dir,
                "Anneal",
                "src/theory",
                false,
                &["bundle-manifest.json"],
            )?
        } else {
            BTreeMap::new()
        };

        self.tool_admission()?;

        let modules_snap = self.modules.clone();
        let theory_snap = self.theory_modules.clone();
        let preflight = self.preflight_and_order_modules(
            &modules_snap,
            &theory_snap,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            "incomplete source-header inventory",
            "Trusted import cycle",
            "Theory import cycle",
        )?;

        self.pass1_imports = preflight.imports.clone();
        let pass1_workers = default_compile_workers(4);
        self.inner.compile_lean_modules_parallel(
            &preflight.trusted_order,
            &self.modules,
            &preflight.imports,
            &preflight.is_module,
            "lib",
            false,
            false,
            pass1_workers,
        )?;

        self.inner.compile_lean_modules_parallel(
            &preflight.theory_order,
            &self.theory_modules,
            &preflight.imports,
            &preflight.is_module,
            "theory-lib",
            true,
            false,
            pass1_workers,
        )?;

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

        let corr_trusted_modules = self.scan_and_stage_tree_opts(
            &corr_trusted_dir,
            "Trusted",
            "src/corr-trusted",
            false,
            &[],
        )?;
        if !corr_trusted_modules.contains_key("Trusted.Correspondence") {
            return Err(Failure::policy(
                "snapshot",
                "missing Trusted/Correspondence.lean umbrella in trusted/correspondence",
            ));
        }

        let corr_theory_modules = self.scan_and_stage_tree_opts(
            &corr_theory_dir,
            "Anneal",
            "src/corr-theory",
            false,
            &[],
        )?;
        if !corr_theory_modules.contains_key("Anneal.MirCorrespondenceProof") {
            return Err(Failure::policy(
                "snapshot",
                "missing Anneal/MirCorrespondenceProof.lean in correspondence",
            ));
        }

        // Enforce unique module ownership across Pass 1 (`trusted/lean/`,
        // `theory/`), Pass 2 (`trusted/correspondence/`, `correspondence/`),
        // and pinned `vendor/lean-miri/` before preflight or staging into
        // `lib/` and `theory-lib/`. Without this guard, narrowing
        // `CorrespondenceAudit.theory` to imported Pass 1 `theory/` modules
        // would omit an unimported Pass 1 collision (such as
        // `theory/Anneal/MirCorrespondenceProof.lean`) from `baseTheory ++
        // corrTheory` while overwriting its Pass 1 `.olean` in `theory-lib/`.
        let vendor_module_names: BTreeSet<&str> =
            closure_entries.iter().map(|e| e.module.as_str()).collect();
        for module in self.modules.keys().chain(self.theory_modules.keys()) {
            if vendor_module_names.contains(module.as_str()) {
                return Err(Failure::policy(
                    "snapshot",
                    format!("overlapping module role for {module}"),
                ));
            }
        }
        for module in corr_trusted_modules.keys().chain(corr_theory_modules.keys()) {
            let collides_with_pass1 =
                self.modules.contains_key(module) || self.theory_modules.contains_key(module);
            let collides_within_pass2 = corr_trusted_modules.contains_key(module)
                && corr_theory_modules.contains_key(module);
            let collides_with_vendor = vendor_module_names.contains(module.as_str());
            if collides_with_pass1 || collides_within_pass2 || collides_with_vendor {
                return Err(Failure::policy(
                    "snapshot",
                    format!("overlapping module role for {module}"),
                ));
            }
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
        let base_trusted_modules = self.modules.clone();
        let preflight = self.preflight_and_order_modules(
            &corr_trusted_modules,
            &corr_theory_modules,
            &base_trusted_modules,
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

        // Compile `Trusted.Correspondence*` into `lib/` and
        // `Anneal.MirCorrespondence*` into `theory-lib/` inside per-module
        // `ExecSeal` (`SandboxMode::RequireBwrap`) sandboxes. For `Trusted`
        // modules, `corr_theory_lib` is neither mounted nor in `LEAN_PATH`, so
        // they cannot resolve compiled `theory/` or `correspondence/` modules
        // even if an import slipped past preflight.
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
        let corr_base_trusted_sources: Vec<(String, PathBuf)> =
            self.modules.iter().map(|(n, p)| (n.clone(), p.clone())).collect();
        let corr_pf_req = InspectorRequest::CorrespondencePreflight {
            search_path: search_dirs.clone(),
            trusted: self.modules.keys().cloned().collect(),
            theory: self.theory_modules.keys().cloned().collect(),
            vendor_miri: closure_entries.iter().map(|e| e.module.clone()).collect(),
            base_trusted_sources: corr_base_trusted_sources,
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

        // Importing the 160-module `Miri.Interpreter.ExecutionMachine`
        // closure consumes ~1.7 GiB of Lean's `-M` allocator at startup,
        // so Pass 2 uses `-M4096` rather than Pass 1's `-M2048`. Cap Pass 2
        // concurrency at 3 workers (`3 * 4 GiB = 12 GiB` ceiling) to leave
        // headroom on 16 GiB CI runners. Compile `Trusted.Correspondence*`
        // first (without mounting `theory-lib`), then
        // `Anneal.MirCorrespondence*`, each concurrently along its verified
        // import DAG inside isolated per-module `bwrap` sandboxes.
        let pass2_workers = default_compile_workers(3);
        let corr_trusted_src_root = stage.join("src/corr-trusted");
        self.compile_pass2_dag_with_root(
            &preflight.trusted_order,
            &corr_trusted_modules,
            &preflight.imports,
            &corr_trusted_src_root,
            &corr_trusted_dirs,
            &corr_trusted_lib,
            false,
            pass2_workers,
        )?;

        let corr_theory_src_root = stage.join("src/corr-theory");
        self.compile_pass2_dag_with_root(
            &preflight.theory_order,
            &corr_theory_modules,
            &preflight.imports,
            &corr_theory_src_root,
            &search_dirs,
            &corr_theory_lib,
            true,
            pass2_workers,
        )?;

        // Pass 1 `"audit"` has already replayed every `theory/` module against
        // the locked foundation. Pass 2 `"correspondence-audit"` only needs
        // the Pass 1 `theory/` modules transitively imported by
        // `correspondence/` (`corr_theory_modules`); any unexpected Pass 1
        // `theory/` module loaded by a forged `.olean` fails closed as a
        // foreign module in `classifyCorrModules`.
        let corr_audit_theory: Vec<String> =
            if !self.theory_modules.is_empty() && self.pass1_imports.is_empty() {
                self.theory_modules.keys().cloned().collect()
            } else {
                let mut needed = BTreeSet::new();
                let mut pending: Vec<String> = corr_theory_modules
                    .keys()
                    .flat_map(|m| preflight.imports[m].iter().map(|e| e.module.clone()))
                    .collect();
                while let Some(module) = pending.pop() {
                    if !self.theory_modules.contains_key(&module)
                        || !needed.insert(module.clone())
                    {
                        continue;
                    }
                    if let Some(edges) = self.pass1_imports.get(&module) {
                        for edge in edges {
                            pending.push(edge.module.clone());
                        }
                    }
                }
                needed.into_iter().collect()
            };

        let corr_req = InspectorRequest::CorrespondenceAudit {
            search_path: search_dirs,
            trusted: self.modules.keys().cloned().collect(),
            corr_trusted: corr_trusted_modules.keys().cloned().collect(),
            theory: corr_audit_theory,
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
            obj.insert("miriClosureModules".to_string(), json!(closure_entries.len()));
        } else {
            return Err(Failure::operational(
                "correspondence-audit",
                "expected JSON object from correspondence audit",
            ));
        }
        Ok(corr_report)
    }

    /// Stage, restore from the digest-gated cache or compile inside isolated
    /// per-module OS sandboxes (concurrently along the `Miri.*` import DAG
    /// when multiple modules miss the cache), verify every staged source and
    /// output `.olean` companion digest, and write newly compiled artifacts to
    /// `self.miri_cache_dir` only after verification succeeds.
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
        let mut seen_modules = BTreeSet::new();
        for entry in entries {
            if !seen_modules.insert(entry.module.as_str()) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!("duplicate Miri closure module {}", entry.module),
                ));
            }
            let Some(expected_src_sha) = expected_sources.get(&entry.path) else {
                return Err(Failure::policy(
                    "miri-pin",
                    format!("missing pinned source digest for Miri closure module {}", entry.path),
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

        let mut cold_indices: Vec<usize> = Vec::new();
        for (idx, entry) in entries.iter().enumerate() {
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
            } else {
                cold_indices.push(idx);
            }
        }

        if cold_indices.is_empty() {
            return Ok(miri_lib);
        }

        self.inner.set_sandbox_mode(SandboxMode::RequireBwrap);
        let workers = default_compile_workers(4);

        // Parse only the `module`/`prelude`/`import` headers of all
        // SHA-256-verified staged closure sources (`Parser.parseHeader` in
        // `"vendor-headers"` mode loads zero `.olean` files, runs zero
        // initializers, and elaborates zero commands) to build the complete
        // `Miri.*` dependency DAG, preserving transitive dependencies and
        // cycle checks across cached intermediate modules regardless of worker
        // count.
        let total_len = entries.len();
        let mut is_cold = vec![false; total_len];
        for &idx in &cold_indices {
            is_cold[idx] = true;
        }
        let header_sources: Vec<(String, PathBuf)> = entries
            .iter()
            .map(|entry| (entry.module.clone(), miri_src_root.join(&entry.path)))
            .collect();
        let vendor_headers_req = {
            let adm = self.inner.admitted()?;
            json!({
                "mode": "vendor-headers",
                "sysroot": adm.prefix.to_string_lossy(),
                "foundation": adm.foundation_modules(),
                "sources": header_sources,
            })
        };
        let headers_res: PreflightResult = serde_json::from_value(
            self.inner.invoke_inspector("vendor-headers", &vendor_headers_req)?,
        )
        .map_err(|e| Failure::operational("vendor-headers", e.to_string()))?;
        let idx_by_module: BTreeMap<&str, usize> = entries
            .iter()
            .enumerate()
            .map(|(idx, entry)| (entry.module.as_str(), idx))
            .collect();
        if headers_res.headers.len() != total_len {
            return Err(Failure::operational(
                "vendor-headers",
                "incomplete Miri closure header inventory",
            ));
        }

        let mut seen_headers = vec![false; total_len];
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); total_len];
        for header in headers_res.headers {
            let Some(&dst_idx) = idx_by_module.get(header.module.as_str()) else {
                return Err(Failure::policy(
                    "miri-pin",
                    format!("unexpected Miri header record for {}", header.module),
                ));
            };
            if seen_headers[dst_idx] {
                return Err(Failure::policy(
                    "miri-pin",
                    format!("duplicate Miri header record for {}", header.module),
                ));
            }
            seen_headers[dst_idx] = true;
            for edge in header.imports {
                if let Some(&src_idx) = idx_by_module.get(edge.module.as_str()) {
                    if src_idx == dst_idx {
                        return Err(Failure::policy(
                            "miri-pin",
                            format!("self-import in Miri closure module {}", header.module),
                        ));
                    }
                    dependents[src_idx].push(dst_idx);
                }
            }
        }
        let plan = ParallelDagPlan::from_indexed_edges(
            is_cold,
            dependents,
            "miri-pin",
            "import cycle in Miri closure modules",
        )?;

        let runtime = self.inner.ensure_sandbox_ready()?;
        let child_timeout = self.inner.child_timeout();
        fs::create_dir_all(stage.join("runs"))
            .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
        self.inner.mark_execution_began();
        let mut run_ids = vec![0usize; total_len];
        for &idx in &cold_indices {
            run_ids[idx] = self.inner.next_counter();
        }

        let miri_cache_dir = self.miri_cache_dir.as_deref();
        let mut staging_guard = ();
        run_parallel_dag(
            &plan,
            workers,
            "miri-compile",
            "worker panicked during Miri compilation",
            &mut staging_guard,
            |_, _| Ok(()),
            |entry_idx, ()| {
                compile_and_verify_cold_miri_entry(
                    &runtime,
                    &stage,
                    run_ids[entry_idx],
                    child_timeout,
                    &miri_src_root,
                    &miri_lib,
                    &entries[entry_idx],
                )
            },
            |_, entry_idx, module_out_dir| {
                // Stage and cache under the lock so dependents see complete
                // `.olean` files without races.
                stage_and_cache_verified_miri_entry(
                    &miri_lib,
                    miri_cache_dir,
                    module_out_dir.path(),
                    &entries[entry_idx],
                )
            },
        )?;
        Ok(miri_lib)
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_pass2_dag_with_root(
        &mut self,
        order: &[String],
        staged_sources: &BTreeMap<String, PathBuf>,
        imports: &BTreeMap<String, Vec<ImportEdge>>,
        src_root: &Path,
        lean_path_dirs: &[PathBuf],
        out_lib_root: &Path,
        warning_as_error: bool,
        max_workers: usize,
    ) -> Result<(), Failure> {
        if order.is_empty() {
            return Ok(());
        }
        for module in order {
            if !staged_sources.contains_key(module) {
                return Err(Failure::operational(
                    "compile",
                    format!("missing staged Pass 2 source for {module}"),
                ));
            }
        }
        let plan = ParallelDagPlan::from_module_order(
            order,
            imports,
            "preflight",
            "Pass 2 correspondence import cycle",
        )?;
        self.inner.set_sandbox_mode(SandboxMode::RequireBwrap);
        let runtime = self.inner.ensure_sandbox_ready()?;
        let child_timeout = self.inner.child_timeout();
        let stage = self.inner.stage().to_path_buf();
        create_dir_mode(&stage.join("runs"), 0o700)?;
        create_dir_mode(out_lib_root, 0o700)?;
        for lp in lean_path_dirs {
            create_dir_mode(lp, 0o700)?;
        }
        self.inner.mark_execution_began();
        let run_ids: Vec<usize> = (0..order.len()).map(|_| self.inner.next_counter()).collect();

        let mut staging_guard = ();
        run_parallel_dag(
            &plan,
            max_workers,
            "compile",
            "worker panicked during Pass 2 compilation",
            &mut staging_guard,
            |_, _| Ok(()),
            |idx, ()| {
                let module = &order[idx];
                let staged_src = &staged_sources[module];
                let rel_olean = format!("{}.olean", module.replace('.', "/"));
                let mut out_builder = tempfile::Builder::new();
                out_builder.prefix("anneal-pass2-out-");
                #[cfg(unix)]
                out_builder.permissions(fs::Permissions::from_mode(0o700));
                let module_out_dir = out_builder
                    .tempdir_in(stage.join("runs"))
                    .map_err(|e| Failure::operational("compile", e.to_string()))?;
                let worker_olean = module_out_dir.path().join(&rel_olean);
                if let Some(parent) = worker_olean.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|e| Failure::operational("compile", e.to_string()))?;
                }
                cargo_anneal::Checker::compile_lean_module_with_root_in_runtime(
                    &runtime,
                    &stage,
                    run_ids[idx],
                    child_timeout,
                    module,
                    src_root,
                    staged_src,
                    &worker_olean,
                    lean_path_dirs,
                    4096,
                    warning_as_error,
                    &[],
                    &[],
                )?;
                Ok((rel_olean, module_out_dir))
            },
            |_, _idx, (rel_olean, module_out_dir)| {
                // Stage under the mutex so downstream Pass 2 workers only ever
                // observe complete `.olean` files.
                let worker_olean = module_out_dir.path().join(&rel_olean);
                let staged_olean = out_lib_root.join(&rel_olean);
                if let Some(parent) = staged_olean.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|e| Failure::operational("compile", e.to_string()))?;
                }
                fs::rename(&worker_olean, &staged_olean)
                    .map_err(|e| Failure::operational("compile", e.to_string()))?;
                regular(&staged_olean, "compile")?;
                Ok(())
            },
        )
    }
}

/// Compile one cold `vendor/lean-miri` module inside an isolated per-module
/// `ExecSeal` (`SandboxMode::RequireBwrap`) sandbox and verify all `.olean`,
/// `.olean.server`, `.olean.private`, and Door 1 output invariants before
/// returning the verified temporary directory.
fn compile_and_verify_cold_miri_entry(
    runtime: &SandboxRuntime,
    stage: &Path,
    run_id: usize,
    child_timeout: Duration,
    miri_src_root: &Path,
    miri_lib: &Path,
    entry: &MiriClosureEntry,
) -> Result<tempfile::TempDir, Failure> {
    let rel_stem = entry.module.replace('.', "/");
    let rel_olean = format!("{rel_stem}.olean");

    let mut out_builder = tempfile::Builder::new();
    out_builder.prefix("anneal-miri-out-");
    #[cfg(unix)]
    out_builder.permissions(fs::Permissions::from_mode(0o700));
    let module_out_dir = out_builder
        .tempdir_in(stage.join("runs"))
        .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
    let out_olean = module_out_dir.path().join(&rel_olean);
    if let Some(parent) = out_olean.parent() {
        fs::create_dir_all(parent)
            .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
    }

    let staged_src = miri_src_root.join(&entry.path);
    // Promote optional `.olean.server`/`.olean.private` sidecars so the
    // explicit SHA-256/presence policy below enforces the pin with exit code 1,
    // while validating and discarding Lean `module` `.ir`/`.ir.sig` outputs
    // without promoting them.
    let discarded_parts: &[&str] =
        if entry.olean_server_sha256.is_some() || entry.olean_private_sha256.is_some() {
            &["ir", "ir.sig"]
        } else {
            &[]
        };
    let miri_lean_dirs = [miri_lib.to_path_buf()];
    cargo_anneal::Checker::compile_lean_module_with_root_in_runtime(
        runtime,
        stage,
        run_id,
        child_timeout,
        &entry.module,
        miri_src_root,
        &staged_src,
        &out_olean,
        &miri_lean_dirs,
        2048,
        false,
        &["olean.server", "olean.private"],
        discarded_parts,
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
    Ok(module_out_dir)
}

/// Stage a digest-verified `module_out_dir` into `miri_lib`, re-verify staged
/// digests, and populate `miri_cache_dir` when configured.
fn stage_and_cache_verified_miri_entry(
    miri_lib: &Path,
    miri_cache_dir: Option<&Path>,
    module_out_dir: &Path,
    entry: &MiriClosureEntry,
) -> Result<(), Failure> {
    let rel_stem = entry.module.replace('.', "/");
    let rel_olean = format!("{rel_stem}.olean");
    let out_olean = module_out_dir.join(&rel_olean);
    let staged_olean = miri_lib.join(&rel_olean);
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
                &module_out_dir.join(&rel_part),
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

    if let Some(cache_dir) = miri_cache_dir {
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
    let Some(replayed) = result.get("miriReplayedDeclarations").and_then(Json::as_u64) else {
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
    let corr_replayed = result.get("correspondenceReplayedDeclarations").and_then(Json::as_u64);
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
    let Some(corr_decls) = result.get("correspondenceDeclarations").and_then(Json::as_u64) else {
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

/// Enforce module-level trust-tier import isolation before compilation: a
/// `vetted` module may import `imp` if and only if `imp` belongs to
/// `foundation_graph` or another `vetted` `Trusted` module (never
/// `candidate:<feature>`, `.repo .theory`, or Pass 2 non-foundation modules
/// such as `vendor/lean-miri`).
fn check_preflight_tier_imports<'a, I>(
    trusted_modules: I,
    imports: &BTreeMap<String, Vec<ImportEdge>>,
    module_tiers: &BTreeMap<String, TrustTier>,
    foundation_graph: &BTreeMap<String, Vec<ImportEdge>>,
) -> Result<(), Failure>
where
    I: IntoIterator<Item = &'a String>,
{
    for mod_name in trusted_modules {
        if module_tiers.get(mod_name) == Some(&TrustTier::Vetted) {
            for edge in &imports[mod_name] {
                let imp_mod = edge.module.as_str();
                if !foundation_graph.contains_key(imp_mod) {
                    match module_tiers.get(imp_mod) {
                        Some(TrustTier::Vetted) => {}
                        Some(dep_tier) => {
                            return Err(Failure::policy(
                                "preflight",
                                format!(
                                    "vetted module {mod_name} cannot import {} module {imp_mod}",
                                    dep_tier.render()
                                ),
                            ));
                        }
                        None => {
                            return Err(Failure::policy(
                                "preflight",
                                format!(
                                    "vetted module {mod_name} cannot import non-foundation module {imp_mod}"
                                ),
                            ));
                        }
                    }
                }
            }
        }
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
    #[test]
    fn preflight_tier_imports_isolate_vetted_modules() {
        let mk_edge = |module: &str| ImportEdge {
            module: module.to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        };
        let foundation = BTreeMap::from([("Init.Core".to_string(), Vec::new())]);
        let tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            ("Trusted.VettedSub".to_string(), TrustTier::Vetted),
            (
                "Trusted.Cand".to_string(),
                TrustTier::Candidate(CandidateFeature::MirSemantics),
            ),
        ]);
        let mods = [
            "Trusted".to_string(),
            "Trusted.VettedSub".to_string(),
            "Trusted.Cand".to_string(),
        ];

        // Allowed: vetted imports foundation and vetted; candidate imports
        // vetted and Miri.
        let ok_imports = BTreeMap::from([
            ("Trusted".to_string(), vec![mk_edge("Init.Core"), mk_edge("Trusted.VettedSub")]),
            ("Trusted.VettedSub".to_string(), vec![mk_edge("Init.Core")]),
            (
                "Trusted.Cand".to_string(),
                vec![mk_edge("Init.Core"), mk_edge("Trusted.VettedSub"), mk_edge("Miri.Child")],
            ),
        ]);
        check_preflight_tier_imports(mods.iter(), &ok_imports, &tiers, &foundation).unwrap();

        // Rejected: vetted imports candidate.
        let mut bad_cand = ok_imports.clone();
        bad_cand.get_mut("Trusted").unwrap().push(mk_edge("Trusted.Cand"));
        let err_cand =
            check_preflight_tier_imports(mods.iter(), &bad_cand, &tiers, &foundation).unwrap_err();
        assert_eq!(err_cand.code, 1);
        assert_eq!(err_cand.phase, "preflight");
        assert!(
            err_cand.message.contains(
                "vetted module Trusted cannot import candidate:mir_semantics module Trusted.Cand"
            ),
            "unexpected error: {err_cand}"
        );

        // Rejected: vetted imports Pass 2 non-foundation module (such as
        // `vendor/lean-miri`) or `theory/` module (`Anneal.Helper`).
        let mut bad_miri = ok_imports.clone();
        bad_miri.get_mut("Trusted").unwrap().push(mk_edge("Miri.Child"));
        let err_miri =
            check_preflight_tier_imports(mods.iter(), &bad_miri, &tiers, &foundation).unwrap_err();
        assert_eq!(err_miri.code, 1);
        assert_eq!(err_miri.phase, "preflight");
        assert!(
            err_miri
                .message
                .contains("vetted module Trusted cannot import non-foundation module Miri.Child"),
            "unexpected error: {err_miri}"
        );

        let mut bad_theory = ok_imports;
        bad_theory.get_mut("Trusted").unwrap().push(mk_edge("Anneal.Helper"));
        let err_theory =
            check_preflight_tier_imports(mods.iter(), &bad_theory, &tiers, &foundation)
                .unwrap_err();
        assert_eq!(err_theory.code, 1);
        assert_eq!(err_theory.phase, "preflight");
        assert!(
            err_theory.message.contains(
                "vetted module Trusted cannot import non-foundation module Anneal.Helper"
            ),
            "unexpected error: {err_theory}"
        );
    }
}
