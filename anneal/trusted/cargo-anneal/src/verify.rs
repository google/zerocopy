// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Bind one configured compilation to its canonical Lean verification claim.
//!
//! The proof package supplies specifications and proof terms. It cannot supply
//! the source model, captured subject or expected proposition. Those inputs are
//! staged independently and passed to the compiled-environment auditor.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::{OsStr, OsString},
    fs,
    io::{ErrorKind as IoErrorKind, Write as _},
    path::{Component, Path, PathBuf},
    process::{Command, ExitCode},
    time::Instant,
};

use clap::{
    Args, Subcommand,
    builder::{OsStringValueParser, TypedValueParser as _},
    error::ErrorKind,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

#[cfg(feature = "setup")]
use crate::setup::{ToolOverrides, installed_bundle, resolve_tools};
use crate::{
    ActiveSandbox, Checker, SandboxMode, TOOLCHAIN, TargetAuditRequest, TargetBindings,
    TargetModule, TargetProgress, TargetRole, TrustTier, cargo_config, diagnostics,
    output::{
        CardRenderOptions, ColorChoice, FailureCardInput, OutputSession, ResolvedVerifyFormat,
        SanitizedInline, VerifyFormat, VerifyPhase, finish_with_writers, render_failure_card,
        render_success_card,
    },
    parse_trusted_tier_directive, read_regular_file_deref, read_regular_file_strict, sha256_bytes,
    shard::{
        CaptureShardsManifest, SHARD_PLAN_SCHEMA_VERSION, ShardArgs, ShardConfig, ShardPlan,
        compare_shard_plan, parse_and_validate_capture_shards, render_id_tree_module,
    },
    source_starts_with_module_keyword,
};

// Generated deterministically by `build.rs` into `$OUT_DIR` from canonical
// workspace sources (or from `packaged/bundled_resources.rs` in standalone
// `.crate` builds), keeping edits to `trusted/` and `correspondence/` free of
// checked-in monolith conflicts while binding the compiled binary to audited
// bytes.
include!(concat!(env!("OUT_DIR"), "/bundled_resources.rs"));

pub(crate) const EMBEDDED_BUNDLE_SOURCES: &[(&str, &str)] = BUNDLE;
pub(crate) const EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON: &str = CORRESPONDENCE_PROVENANCE_JSON;

const PINNED_CAPTURE_SCHEMA_VERSION: u32 = 5;
const PINNED_RUSTC_COMMIT: &str = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1";
const RECEIPT_SCHEMA_VERSION: u32 = 3;

/// Closed 4-element set of verification taint atoms projected onto Receipt
/// Schema v3 (`taint_reasons`), sorted lexicographically by wire spelling.
/// Variant declaration order must match lexicographical `as_str()` order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum VerificationTaint {
    SorryInProof,
    UnmodeledUnstableFeatures,
    UnpinnedLean,
    UnsandboxedElaboration,
}

impl VerificationTaint {
    const fn as_str(self) -> &'static str {
        match self {
            Self::SorryInProof => "sorry_in_proof",
            Self::UnmodeledUnstableFeatures => "unmodeled_unstable_features",
            Self::UnpinnedLean => "unpinned_lean",
            Self::UnsandboxedElaboration => "unsandboxed_elaboration",
        }
    }

    const fn warning_banner(self) -> &'static str {
        match self {
            Self::SorryInProof => {
                "WARNING: allowing `sorry` in proof modules (--allow-sorry-in-proof); \
                 verification result is TAINTED"
            }
            Self::UnmodeledUnstableFeatures => {
                "WARNING: allowing unstable rustc features whose semantics Anneal \
                 does not model (--allow-unstable-feature); verification result is \
                 TAINTED"
            }
            Self::UnpinnedLean => {
                "WARNING: running with unpinned Lean (--allow-unpinned-lean); \
                 verification result is TAINTED"
            }
            Self::UnsandboxedElaboration => {
                "WARNING: running without OS elaborator containment \
                 (--allow-unsandboxed-elaboration); verification result is TAINTED"
            }
        }
    }
}

/// Collect active taint atoms under the Uniform Flag-Driven Taint Law: every
/// `--allow-*` relaxation flag unconditionally inserts its taint atom even when
/// the relaxed condition did not occur on that run.
fn active_taints(args: &VerifyArgs) -> BTreeSet<VerificationTaint> {
    let mut taints = BTreeSet::new();
    if args.allow_sorry_in_proof {
        taints.insert(VerificationTaint::SorryInProof);
    }
    if !args.allow_unstable_feature.is_empty() {
        taints.insert(VerificationTaint::UnmodeledUnstableFeatures);
    }
    if args.allow_unpinned_lean {
        taints.insert(VerificationTaint::UnpinnedLean);
    }
    if args.allow_unsandboxed_elaboration {
        taints.insert(VerificationTaint::UnsandboxedElaboration);
    }
    taints
}

fn taint_reason_strings(taints: &BTreeSet<VerificationTaint>) -> Vec<&'static str> {
    taints.iter().map(|t| t.as_str()).collect()
}

/// Arguments of the build-neutral verification command.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize, clap::ValueEnum)]
#[serde(rename_all = "snake_case")]
enum CrateType {
    #[default]
    Lib,
    Bin,
}

impl CrateType {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Lib => "lib",
            Self::Bin => "bin",
        }
    }
}

/// Standard-library crate for capture's opt-in `--stdlib-crate` capability,
/// which admits that crate's own language items (see
/// `check_stdlib_capability` in `trusted/rustc-capture/src/capture.rs`).
/// Absent by default, so ordinary requests keep crate-local language items
/// refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, clap::ValueEnum)]
#[serde(rename_all = "snake_case")]
enum StdlibCrate {
    Core,
}

impl StdlibCrate {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Core => "core",
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize, clap::ValueEnum)]
#[serde(rename_all = "snake_case")]
enum PanicStrategy {
    #[default]
    Unwind,
    Abort,
}

impl PanicStrategy {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Unwind => "unwind",
            Self::Abort => "abort",
        }
    }
}

#[derive(Args)]
#[command(subcommand_negates_reqs = true)]
pub struct VerifyArgs {
    /// JSON compilation/proof request, with paths relative to its directory.
    #[arg(
        long,
        conflicts_with_all = [
            "manifest_path",
            "proof_dir",
            "panic",
            "overflow_checks",
            "select",
            "instantiate",
            "features",
            "all_features",
            "no_default_features",
        ]
    )]
    request: Option<PathBuf>,
    /// A library or binary crate with no required normal or build dependencies
    /// (dev-dependencies and inactive optional dependencies are ignored) for
    /// the `x86_64-unknown-linux-gnu` scalar profile.
    #[arg(long, conflicts_with = "request", requires = "proof_dir")]
    manifest_path: Option<PathBuf>,
    /// Directory containing Spec.lean and Proof.lean, for the Cargo shortcut.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    proof_dir: Option<PathBuf>,
    /// Panic strategy (`unwind` or `abort`) for the Cargo shortcut.
    #[arg(long, value_enum, requires = "manifest_path", conflicts_with = "request")]
    panic: Option<PanicStrategy>,
    /// Enable runtime integer overflow checks (`-Coverflow-checks=yes`) during
    /// capture.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    overflow_checks: bool,
    /// Select a function by its compiler path; omit to require the whole crate.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    select: Vec<String>,
    /// Instantiate a generic item with concrete arguments as JSON
    /// (`{"path":"...","args":[...]}`).
    #[arg(
        long,
        requires = "manifest_path",
        conflicts_with = "request",
        value_name = "JSON",
        value_parser = parse_instantiation_arg
    )]
    instantiate: Vec<Instantiation>,
    /// Space or comma separated list of Cargo features to activate.
    #[arg(
        long,
        short = 'F',
        value_name = "FEATURES",
        requires = "manifest_path",
        conflicts_with = "request"
    )]
    features: Vec<String>,
    /// Activate all available Cargo features of the selected package.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    all_features: bool,
    /// Do not activate the `default` Cargo feature.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    no_default_features: bool,
    /// Capture driver; defaults to the installed bundle, then a sibling. The
    /// receipt records its SHA-256, which no lock pins.
    #[cfg_attr(
        not(feature = "setup"),
        arg(
            long,
            global = true,
            help = "Capture driver; required when built without the `setup` \
                    feature. The receipt records its SHA-256, which no lock pins."
        )
    )]
    #[cfg_attr(feature = "setup", arg(long, global = true))]
    capture: Option<PathBuf>,
    /// Lean executable; defaults to the installed bundle, cached toolchain, or
    /// pinned elan installation. Its SHA-256 must match the foundation lock,
    /// which does not cover the shared libraries it loads.
    #[cfg_attr(
        not(feature = "setup"),
        arg(
            long,
            global = true,
            help = "Lean executable; required when built without the `setup` \
                    feature. Its SHA-256 must match the foundation lock, which \
                    does not cover the shared libraries it loads."
        )
    )]
    #[cfg_attr(feature = "setup", arg(long, global = true))]
    lean: Option<PathBuf>,
    /// Compiler sysroot; defaults to the installed bundle when present.
    /// Capture checks its reported rustc commit but does not hash it.
    #[cfg_attr(
        not(feature = "setup"),
        arg(
            long,
            global = true,
            help = "Compiler sysroot; required when built without the `setup` \
                    feature. Capture checks its reported rustc commit but does \
                    not hash it."
        )
    )]
    #[cfg_attr(feature = "setup", arg(long, global = true))]
    sysroot: Option<PathBuf>,
    /// New UTF-8 directory path for retained capture, sources and audit
    /// evidence.
    #[arg(long, global = true)]
    artifacts: Option<PathBuf>,
    /// Primary stdout output format (`human`, `json`, or `auto`).
    #[arg(
        long,
        global = true,
        value_enum,
        default_value_t = VerifyFormat::Human,
        value_name = "FORMAT"
    )]
    format: VerifyFormat,
    /// Atomically write the canonical Receipt Schema v3 JSON to PATH.
    ///
    /// Clears any pre-existing non-input regular file at PATH once inputs are
    /// validated so an interrupted or failed run cannot leave a stale passing
    /// receipt behind. Always check the process exit code alongside PATH.
    #[arg(long, global = true, value_name = "PATH")]
    receipt_out: Option<PathBuf>,
    /// Export compiled `.olean*` files to `<artifacts>/lean-lib/`.
    #[arg(long, global = true)]
    export_lean_lib: bool,
    /// Replace an existing `--artifacts` directory that holds only earlier
    /// `cargo-anneal` artifacts, after the new artifacts are fully copied.
    #[arg(long, global = true)]
    overwrite_artifacts: bool,
    /// Allow unpinned Lean with explicit `--lean` (taints receipt).
    #[arg(long, global = true)]
    allow_unpinned_lean: bool,
    /// Disable OS-level elaborator containment (`ExecSeal`) and run Lean
    /// unsandboxed (taints receipt).
    #[arg(long, global = true)]
    allow_unsandboxed_elaboration: bool,
    /// Allow `sorry` in proof modules only, recording `sorry_declarations`
    /// (never specifications, model, capture, or expected; taints receipt).
    #[arg(long, global = true)]
    allow_sorry_in_proof: bool,
    /// Cross-check the NDJSON proof export across a four-independent-kernel
    /// quorum (`nanoda_bin`, `con-ron`, `con-leche`, and `lean4lean --import`)
    /// directly inside `ExecSeal` on Lean `v4.35.0+`.
    #[arg(long, global = true)]
    paranoid_quorum: bool,
    /// Admit an unstable `#![feature(...)]` gate on the target crate; repeat
    /// or comma-separate for several (never wildcards). Taints the receipt
    /// even when the crate enables none of them. Compiler-internal features,
    /// `ergonomic_clones`, and `rustc_private` stay refused.
    #[arg(
        long,
        global = true,
        value_name = "FEATURE",
        value_delimiter = ',',
        value_parser = parse_unstable_feature_arg
    )]
    allow_unstable_feature: Vec<String>,
    /// Explicit Lean memory limit in MiB (`-M<MB>`; `resolve-imports` enforces
    /// a 4096 MiB floor).
    #[arg(
        long,
        global = true,
        value_name = "MB",
        value_parser = clap::value_parser!(u32).range(1..)
    )]
    lean_memory_mb: Option<u32>,
    /// Disable prebuilt and local disk `.olean` caching for bundled modules and
    /// `TrustedBoundary`.
    #[arg(long, global = true)]
    no_cache: bool,
    /// Fail closed rather than compiling `Trusted.*`, `Anneal.*`, or
    /// `TrustedBoundary` when absent from prebuilt or local `.olean` caches.
    #[arg(long, global = true, conflicts_with = "no_cache")]
    no_rebuild_bundled: bool,
    /// Sharding budget configuration for Tarjan SCC `.olean` partitioning.
    #[command(flatten)]
    shard: ShardArgs,
    /// Verify that the captured shard topology matches a checked-in
    /// `anneal-shards.json` plan before Lean verification.
    #[arg(long, global = true, value_name = "PATH")]
    verify_shard_plan: Option<PathBuf>,
    /// Direct rustc-style verification subcommand.
    #[command(subcommand)]
    command: Option<VerifySubcommand>,
}

#[derive(Subcommand)]
enum VerifySubcommand {
    /// Verify a crate from explicit rustc inputs and Lean module mappings.
    Rustc(RustcArgs),
}

#[derive(Args)]
struct RustcArgs {
    /// Crate root Rust source file.
    crate_root: PathBuf,
    /// Crate name passed to rustc capture.
    #[arg(long)]
    crate_name: String,
    /// Crate type (`lib` or `bin`) passed to rustc capture.
    #[arg(long, value_enum, default_value_t = CrateType::Lib)]
    crate_type: CrateType,
    /// Panic strategy (`unwind` or `abort`) passed to rustc capture.
    #[arg(long, value_enum, default_value_t = PanicStrategy::Unwind)]
    panic: PanicStrategy,
    /// Enable runtime integer overflow checks (`-Coverflow-checks=yes`) during
    /// capture.
    #[arg(long)]
    overflow_checks: bool,
    /// Rust edition (`2015`, `2018`, `2021`, or `2024`).
    #[arg(
        long,
        default_value = "2024",
        value_parser = ["2015", "2018", "2021", "2024"]
    )]
    edition: String,
    /// Target triple for the verification profile.
    #[arg(long, default_value = "x86_64-unknown-linux-gnu")]
    target: String,
    /// Conditional compilation `cfg` flag passed to capture.
    #[arg(long)]
    cfg: Vec<String>,
    /// Compile-time environment variable (`KEY=VALUE`) for `env!` and
    /// `option_env!`.
    #[arg(long, value_name = "KEY=VALUE", value_parser = parse_env_arg)]
    env: Vec<(String, String)>,
    /// Additional Rust source file in the crate.
    #[arg(long)]
    source_file: Vec<PathBuf>,
    /// Capture this standard-library crate (`core`) from its own sources,
    /// admitting its language items; recorded in the receipt configuration.
    #[arg(long, value_enum)]
    stdlib_crate: Option<StdlibCrate>,
    /// Reviewed specification module mapping (`<MOD>=<PATH>`).
    #[arg(
        long,
        required = true,
        value_name = "MOD=PATH",
        value_parser = OsStringValueParser::new().try_map(|v| parse_module_file_arg(&v))
    )]
    spec_file: Vec<ModuleFileArg>,
    /// Authored proof module mapping (`<MOD>=<PATH>`).
    #[arg(
        long,
        required = true,
        value_name = "MOD=PATH",
        value_parser = OsStringValueParser::new().try_map(|v| parse_module_file_arg(&v))
    )]
    proof_file: Vec<ModuleFileArg>,
    /// Specification declaration (`[MODULE:]DECL`).
    #[arg(
        long,
        default_value = "Spec:Spec.specs",
        value_name = "[MODULE:]DECL",
        value_parser = parse_decl_spec
    )]
    spec_decl: DeclSpec,
    /// Proof theorem declaration (`[MODULE:]DECL`).
    #[arg(
        long,
        default_value = "Proof:Proof.verify",
        value_name = "[MODULE:]DECL",
        value_parser = parse_decl_spec
    )]
    theorem: DeclSpec,
    /// Select a function by its compiler path; omit to require the whole crate.
    #[arg(long)]
    select: Vec<String>,
    /// Instantiate a generic item with concrete arguments as JSON
    /// (`{"path":"...","args":[...]}`).
    #[arg(long, value_name = "JSON", value_parser = parse_instantiation_arg)]
    instantiate: Vec<Instantiation>,
}

/// CLI arguments for `cargo anneal shard-plan`.
#[derive(Args)]
pub struct ShardPlanArgs {
    /// Explicit configured verification request JSON.
    #[arg(
        long,
        conflicts_with_all = [
            "manifest_path",
            "panic",
            "overflow_checks",
            "select",
            "instantiate",
            "features",
            "all_features",
            "no_default_features",
        ]
    )]
    request: Option<PathBuf>,
    /// Package manifest for Cargo discovery (without needing proof modules).
    #[arg(long, conflicts_with = "request")]
    manifest_path: Option<PathBuf>,
    /// Panic strategy for Cargo discovery (`unwind` or `abort`).
    #[arg(long, value_enum, requires = "manifest_path")]
    panic: Option<PanicStrategy>,
    /// Enable runtime integer overflow checks (`-Coverflow-checks=yes`) for
    /// Cargo discovery.
    #[arg(long, requires = "manifest_path")]
    overflow_checks: bool,
    /// Select a function path; omit to plan the whole crate.
    #[arg(long, requires = "manifest_path")]
    select: Vec<String>,
    /// Instantiate a generic item with concrete arguments as JSON
    /// (`{"path":"...","args":[...]}`).
    #[arg(
        long,
        requires = "manifest_path",
        value_name = "JSON",
        value_parser = parse_instantiation_arg
    )]
    instantiate: Vec<Instantiation>,
    /// Space or comma separated list of Cargo features to activate.
    #[arg(
        long,
        short = 'F',
        value_name = "FEATURES",
        requires = "manifest_path",
        conflicts_with = "request"
    )]
    features: Vec<String>,
    /// Activate all available Cargo features of the selected package.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    all_features: bool,
    /// Do not activate the `default` Cargo feature.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    no_default_features: bool,
    /// Write the deterministic `anneal-shards.json` plan to `PATH`.
    #[arg(long, value_name = "PATH", conflicts_with = "check")]
    write: Option<PathBuf>,
    /// Verify that the computed shard plan matches `PATH`.
    #[arg(long, value_name = "PATH", conflicts_with = "write")]
    check: Option<PathBuf>,
    /// Capture driver; defaults to the installed bundle, then a sibling.
    #[cfg_attr(
        not(feature = "setup"),
        arg(long, help = "Capture driver; required when built without the `setup` feature.")
    )]
    #[cfg_attr(feature = "setup", arg(long))]
    capture: Option<PathBuf>,
    /// Compiler sysroot; defaults to the installed bundle when present.
    #[cfg_attr(
        not(feature = "setup"),
        arg(long, help = "Compiler sysroot; required when built without the `setup` feature.")
    )]
    #[cfg_attr(feature = "setup", arg(long))]
    sysroot: Option<PathBuf>,
    /// Sharding budget configuration for Tarjan SCC partitioning.
    #[command(flatten)]
    shard: ShardArgs,
}

impl ShardPlanArgs {
    pub fn validate(&self, mut cmd: clap::Command) -> std::result::Result<(), clap::Error> {
        if self.request.is_none() && self.manifest_path.is_none() {
            return Err(cmd.error(
                ErrorKind::MissingRequiredArgument,
                "specify one of `--request <JSON>` or `--manifest-path <Cargo.toml>`",
            ));
        }
        if self.capture.is_some() != self.sysroot.is_some() {
            return Err(cmd.error(
                ErrorKind::ArgumentConflict,
                "`--capture` and `--sysroot` are ABI-paired and must be passed together",
            ));
        }
        #[cfg(not(feature = "setup"))]
        if self.capture.is_none() || self.sysroot.is_none() {
            let mut missing = Vec::new();
            if self.capture.is_none() {
                missing.push("--capture");
            }
            if self.sysroot.is_none() {
                missing.push("--sysroot");
            }
            return Err(cmd.error(
                ErrorKind::MissingRequiredArgument,
                format!(
                    "missing {}; explicit --capture and --sysroot tool paths are required \
                     when built without the `setup` feature",
                    missing.join(", ")
                ),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct ModuleFileArg {
    module: String,
    path: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DeclSpec {
    module: Option<String>,
    decl: String,
}

fn parse_module_file_arg(raw: &OsStr) -> std::result::Result<ModuleFileArg, String> {
    let bytes = raw.as_encoded_bytes();
    let Some(eq_pos) = bytes.iter().position(|&b| b == b'=') else {
        return Err("expected <MOD>=<PATH>".to_owned());
    };
    let mod_bytes = &bytes[..eq_pos];
    let path_bytes = &bytes[eq_pos + 1..];
    let Ok(module) = std::str::from_utf8(mod_bytes) else {
        return Err("Lean module name must be UTF-8".to_owned());
    };
    if module.is_empty() || !identifier(module) {
        return Err(format!("invalid Lean module identifier: {module:?}"));
    }
    if path_bytes.is_empty() {
        return Err(format!("missing file path for module {module}"));
    }
    #[cfg(unix)]
    let path = {
        use std::os::unix::ffi::OsStrExt as _;
        PathBuf::from(OsStr::from_bytes(path_bytes))
    };
    #[cfg(not(unix))]
    let path = {
        let s = std::str::from_utf8(path_bytes)
            .map_err(|_| format!("non-UTF-8 path for module {module}"))?;
        PathBuf::from(s)
    };
    Ok(ModuleFileArg { module: module.to_owned(), path })
}

/// Accept a `#![feature(...)]` gate name of the form `[a-z][a-z0-9_]*`.
fn parse_unstable_feature_arg(raw: &str) -> std::result::Result<String, String> {
    if !crate::core::identifiers::is_feature_name(raw) {
        return Err(format!("invalid feature name {raw:?}: expected [a-z][a-z0-9_]*"));
    }
    Ok(raw.to_owned())
}

/// The operator's `--allow-unstable-feature` names, sorted and deduplicated.
fn allowed_unstable_features(args: &VerifyArgs) -> Vec<&str> {
    let names: BTreeSet<&str> = args.allow_unstable_feature.iter().map(String::as_str).collect();
    names.into_iter().collect()
}

/// Unstable-feature evidence that capture recorded for a normal crate.
#[derive(Debug, Default, PartialEq, Eq)]
struct CapturedUnstableFeatures {
    observed: Vec<String>,
    incomplete_observed: Vec<String>,
}

/// Authenticate the feature lists in capture's `configuration` against the
/// operator's sorted `--allow-unstable-feature` list: capture must record
/// exactly that list, report only allowed features as enabled, and report
/// only enabled features as incomplete. Capture omits each list when empty.
fn check_captured_unstable_features(
    configuration: &Value,
    allowed: &[&str],
) -> std::result::Result<CapturedUnstableFeatures, String> {
    let list = |key: &str| -> std::result::Result<Vec<String>, String> {
        let Some(value) = configuration.get(key) else {
            return Ok(Vec::new());
        };
        let names: Option<Vec<String>> = value
            .as_array()
            .filter(|items| !items.is_empty())
            .and_then(|items| items.iter().map(|item| item.as_str().map(str::to_owned)).collect());
        match names {
            Some(names)
                if names.windows(2).all(|pair| pair[0] < pair[1])
                    && names.iter().all(|name| crate::core::identifiers::is_feature_name(name)) =>
            {
                Ok(names)
            }
            _ => Err(format!(
                "capture configuration.{key} must be a non-empty, strictly sorted array of \
                 feature names"
            )),
        }
    };
    let recorded = list("allowed_unstable_features")?;
    if !recorded.iter().map(String::as_str).eq(allowed.iter().copied()) {
        return Err(
            "capture allowed_unstable_features differs from --allow-unstable-feature".into()
        );
    }
    let observed = list("observed_unstable_features")?;
    if let Some(feature) = observed.iter().find(|feature| !allowed.contains(&feature.as_str())) {
        return Err(format!("capture observed unstable feature `{feature}` that was not allowed"));
    }
    let incomplete_observed = list("incomplete_observed_unstable_features")?;
    if let Some(feature) = incomplete_observed.iter().find(|feature| !observed.contains(feature)) {
        return Err(format!("capture reported incomplete feature `{feature}` it did not observe"));
    }
    list("stabilized_features_present")?;
    Ok(CapturedUnstableFeatures { observed, incomplete_observed })
}

fn parse_env_arg(raw: &str) -> std::result::Result<(String, String), String> {
    let Some((key, value)) = raw.split_once('=') else {
        return Err(format!("expected KEY=VALUE environment binding, got {raw:?}"));
    };
    validate_env_binding(key, value)?;
    Ok((key.to_owned(), value.to_owned()))
}

/// Validate a declared compile-time environment variable binding.
///
/// Rejects empty keys, keys containing `'='`, and NUL bytes in either key or
/// value. Forbidding `'='` in keys prevents a JSON request key such as
/// `"A=B": "C"` from smuggling a different `(key, value)` split across
/// `--env={key}={value}` when invoking `anneal-rustc-capture`.
fn validate_env_binding(key: &str, value: &str) -> std::result::Result<(), String> {
    if key.is_empty() {
        return Err("environment variable name must not be empty".to_owned());
    }
    if key.contains('=') {
        return Err(format!("environment variable name must not contain '=': {key:?}"));
    }
    if key.contains('\0') || value.contains('\0') {
        return Err("environment binding must not contain NUL bytes".to_owned());
    }
    Ok(())
}

fn parse_decl_spec(raw: &str) -> std::result::Result<DeclSpec, String> {
    if let Some((module, decl)) = raw.split_once(':') {
        if decl.contains(':') || module.is_empty() || decl.is_empty() {
            return Err(format!("invalid declaration {raw:?}; expected [MODULE:]DECL"));
        }
        if !identifier(module) {
            return Err(format!("invalid Lean module identifier: {module:?}"));
        }
        if !identifier(decl) {
            return Err(format!("invalid Lean declaration identifier: {decl:?}"));
        }
        Ok(DeclSpec { module: Some(module.to_owned()), decl: decl.to_owned() })
    } else {
        if !identifier(raw) || !raw.contains('.') {
            return Err(format!("expected a qualified Lean declaration name: {raw:?}"));
        }
        Ok(DeclSpec { module: None, decl: raw.to_owned() })
    }
}

impl VerifyArgs {
    /// Enforce mode exclusivity and host policy before `verify::main`
    /// so invalid combinations exit `2` on stderr with empty stdout.
    pub fn validate(&self, mut cmd: clap::Command) -> std::result::Result<(), clap::Error> {
        if let Some(VerifySubcommand::Rustc(rustc)) = &self.command {
            if self.request.is_some()
                || self.manifest_path.is_some()
                || self.proof_dir.is_some()
                || self.panic.is_some()
                || self.overflow_checks
                || !self.select.is_empty()
                || !self.instantiate.is_empty()
                || !self.features.is_empty()
                || self.all_features
                || self.no_default_features
            {
                return Err(cmd.error(
                    ErrorKind::ArgumentConflict,
                    "--request, --manifest-path, --proof-dir, parent --panic, parent \
                     --overflow-checks, parent --select, parent --instantiate, --features, \
                     --all-features, and --no-default-features cannot be used with the `rustc` \
                     subcommand",
                ));
            }
            if rustc.stdlib_crate.is_some() && !self.allow_unstable_feature.is_empty() {
                return Err(cmd.error(
                    ErrorKind::ArgumentConflict,
                    "--allow-unstable-feature cannot be used with --stdlib-crate",
                ));
            }
            if rustc.crate_name.is_empty() {
                return Err(cmd.error(ErrorKind::InvalidValue, "--crate-name must not be empty"));
            }
            let mut seen_modules = BTreeSet::new();
            for entry in rustc.spec_file.iter().chain(rustc.proof_file.iter()) {
                if !seen_modules.insert(entry.module.as_str()) {
                    return Err(cmd.error(
                        ErrorKind::ArgumentConflict,
                        format!(
                            "duplicate Lean module `{}` across --spec-file/--proof-file",
                            entry.module
                        ),
                    ));
                }
            }
            let mut seen_env = BTreeSet::new();
            for (key, _) in &rustc.env {
                if !seen_env.insert(key.as_str()) {
                    return Err(cmd.error(
                        ErrorKind::ArgumentConflict,
                        format!("duplicate --env binding for `{key}`"),
                    ));
                }
            }
        } else {
            if self.request.is_none() && self.manifest_path.is_none() {
                return Err(cmd.error(
                    ErrorKind::MissingRequiredArgument,
                    "specify one of `--request <JSON>`, `--manifest-path <Cargo.toml> \
                     --proof-dir <DIR>`, or `rustc <CRATE_ROOT> ...`",
                ));
            }
            if self.manifest_path.is_some() && self.proof_dir.is_none() {
                return Err(cmd.error(
                    ErrorKind::MissingRequiredArgument,
                    "`--proof-dir <DIR>` is required with `--manifest-path`",
                ));
            }
        }

        if self.export_lean_lib && self.artifacts.is_none() {
            return Err(cmd.error(
                ErrorKind::MissingRequiredArgument,
                "`--export-lean-lib` requires `--artifacts <DIR>`",
            ));
        }
        if self.overwrite_artifacts && self.artifacts.is_none() {
            return Err(cmd.error(
                ErrorKind::MissingRequiredArgument,
                "`--overwrite-artifacts` requires `--artifacts <DIR>`",
            ));
        }
        if self.capture.is_some() != self.sysroot.is_some() {
            return Err(cmd.error(
                ErrorKind::ArgumentConflict,
                "`--capture` and `--sysroot` are ABI-paired and must be passed together",
            ));
        }
        if self.allow_unpinned_lean && self.lean.is_none() {
            return Err(cmd.error(
                ErrorKind::MissingRequiredArgument,
                "`--allow-unpinned-lean` requires an explicit `--lean <BIN>` path",
            ));
        }
        if self.no_cache && self.no_rebuild_bundled {
            return Err(cmd.error(
                ErrorKind::ArgumentConflict,
                "`--no-cache` and `--no-rebuild-bundled` cannot be used together",
            ));
        }
        #[cfg(not(feature = "setup"))]
        if self.capture.is_none() || self.sysroot.is_none() || self.lean.is_none() {
            let mut missing = Vec::new();
            if self.capture.is_none() {
                missing.push("--capture");
            }
            if self.sysroot.is_none() {
                missing.push("--sysroot");
            }
            if self.lean.is_none() {
                missing.push("--lean");
            }
            return Err(cmd.error(
                ErrorKind::MissingRequiredArgument,
                format!(
                    "missing {}; explicit --capture, --sysroot, and --lean tool paths \
                     are required when built without the `setup` feature",
                    missing.join(", ")
                ),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    schema_version: u32,
    compilation: Compilation,
    scope: Scope,
    proof: Proof,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Compilation {
    source_root: PathBuf,
    crate_root: PathBuf,
    crate_name: String,
    #[serde(default)]
    crate_type: CrateType,
    #[serde(default)]
    panic: PanicStrategy,
    /// Omitted when `false` so that requests without overflow checks keep
    /// their encoding and digest.
    #[serde(default, skip_serializing_if = "is_false")]
    overflow_checks: bool,
    #[serde(default = "edition")]
    edition: String,
    #[serde(default = "target")]
    target: String,
    #[serde(default)]
    cfg: BTreeSet<String>,
    #[serde(default)]
    env: BTreeMap<String, String>,
    source_files: Vec<PathBuf>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    stdlib_crate: Option<StdlibCrate>,
}

fn edition() -> String {
    "2024".to_owned()
}

// This target belongs to the verification profile. Archive variants select
// executables for the host running Anneal; adding a host must not expand the
// semantic domain. Capture admits only this triple before compiler setup in
// `trusted/rustc-capture/src/main.rs` (`run`).
// A compatible custom sysroot can provide this target's libraries on another
// host. Keep library availability under the compiler's authority so neither a
// host ban nor a guessed standard-library inventory rejects that configuration.
fn target() -> String {
    "x86_64-unknown-linux-gnu".to_owned()
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Instantiation {
    path: String,
    args: Vec<String>,
}

fn parse_instantiation_arg(raw: &str) -> std::result::Result<Instantiation, String> {
    serde_json::from_str(raw).map_err(|err| format!("invalid `--instantiate` JSON `{raw}`: {err}"))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Scope {
    SelectedUnit {
        roots: BTreeSet<String>,
        #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
        instantiations: BTreeSet<Instantiation>,
    },
    // Empty struct variant (not unit) so `deny_unknown_fields` rejects extra
    // keys such as `roots` on `{"kind":"crate"}`.
    Crate {},
}

impl Scope {
    const fn root_theorem(&self, profile_version: u32) -> (&'static str, &'static str) {
        match (self, profile_version) {
            (Self::Crate {}, 2) => ("CrateTheoremV2", "CrateV2"),
            (Self::SelectedUnit { .. }, 2) => ("UnitTheoremV2", "CrateV2"),
            (Self::Crate {}, _) => ("CrateTheorem", "Crate"),
            (Self::SelectedUnit { .. }, _) => ("UnitTheorem", "Crate"),
        }
    }

    const fn verified_status(&self, tainted: bool) -> &'static str {
        match (self, tainted) {
            (Self::Crate {}, false) => "crate_verified",
            (Self::SelectedUnit { .. }, false) => "selected_unit_verified",
            (Self::Crate {}, true) => "tainted_crate_verified",
            (Self::SelectedUnit { .. }, true) => "tainted_selected_unit_verified",
        }
    }

    const fn shard_label(&self) -> &'static str {
        match self {
            Self::Crate {} => "crate",
            Self::SelectedUnit { .. } => "unit",
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Proof {
    source_root: PathBuf,
    #[serde(default = "spec_name")]
    specification: String,
    #[serde(default = "proof_name")]
    theorem: String,
    #[serde(default)]
    specification_module: Option<String>,
    #[serde(default)]
    theorem_module: Option<String>,
    sources: Vec<ProofSource>,
}

fn spec_name() -> String {
    "Spec.specs".to_owned()
}

fn proof_name() -> String {
    "Proof.verify".to_owned()
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofSource {
    module: String,
    path: PathBuf,
    role: AuthoredRole,
}

/// Authored inputs cannot claim ownership of the model, captured program,
/// or expected proposition. Those roles would let a proof producer replace
/// the meaning of the obligation instead of proving it.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum AuthoredRole {
    Specification,
    Proof,
}

#[derive(Clone, Serialize)]
struct SourceIdentity {
    relative_path: PathBuf,
    sha256: String,
}

#[derive(Deserialize)]
struct CaptureReceipt {
    configuration: Value,
    source_files: Vec<CapturedSourceFile>,
    census: Value,
    selected: Value,
    program: CaptureProgram,
}

#[derive(Deserialize)]
struct CaptureCompiler {
    commit: String,
}

#[derive(Deserialize)]
struct CapturedSourceFile {
    path: PathBuf,
    sha256: String,
}

fn default_profile_version() -> u32 {
    1
}

#[derive(Deserialize)]
struct CaptureProgram {
    scope: Scope,
    #[serde(default)]
    has_local_panic_handler: bool,
    #[serde(default = "default_profile_version")]
    mir_profile_version: u32,
    bodies: Vec<serde::de::IgnoredAny>,
}

#[derive(Deserialize)]
struct CaptureSchemaHeader {
    schema_version: u32,
    #[serde(default)]
    compiler: Option<CaptureCompiler>,
}

fn parse_capture_receipt(bytes: &[u8]) -> Result<CaptureReceipt> {
    let header: CaptureSchemaHeader =
        serde_json::from_slice(bytes).map_err(|e| error("tool_failed", "capture", e))?;
    // Capture schema 5 adds intra-crate `call` and pinned `sysroot_call`
    // terminators (with unwind actions) and unchecked add/sub/mul on top of
    // schema 4's `i128` widths, canonical decimal 128-bit bit patterns,
    // `char`, `Ordering`, `(T, bool)` overflow pairs,
    // unary/overflow/division/comparison ops, and `IntToInt` casts, and
    // schema 3's `program.scope`, `with_retag` flags, and source identities.
    // Check the schema version and compiler commit before strict
    // deserialization so older capture ABIs report a clear version mismatch.
    // Request schema 1 is independent.
    if header.schema_version != PINNED_CAPTURE_SCHEMA_VERSION
        || header.compiler.as_ref().map(|compiler| compiler.commit.as_str())
            != Some(PINNED_RUSTC_COMMIT)
    {
        return Err(error("tool_failed", "capture", "unexpected capture schema or compiler"));
    }
    serde_json::from_slice(bytes).map_err(|e| error("tool_failed", "capture", e))
}

#[derive(Serialize)]
struct FailureReceipt<'a> {
    schema_version: u32,
    taint_reasons: &'a [&'a str],
    #[serde(skip_serializing_if = "Option::is_none")]
    elaboration_sandbox: Option<&'a str>,
    status: &'a str,
    phase: &'a str,
    detail: &'a str,
    #[serde(skip_serializing_if = "Option::is_none")]
    hint: Option<&'a str>,
    // `None` omits the key (pre-run staging/retention failures); `Some(None)`
    // emits `"artifacts": null` when `--artifacts` was omitted on failure.
    #[serde(skip_serializing_if = "Option::is_none")]
    artifacts: Option<Option<&'a str>>,
}

#[derive(Debug)]
struct Error {
    status: &'static str,
    phase: &'static str,
    detail: String,
    elaboration_sandbox: Option<&'static str>,
    suppress_retention: bool,
    suppress_receipt_out: bool,
}

impl Error {
    const fn with_sandbox(mut self, sandbox: Option<&'static str>) -> Self {
        self.elaboration_sandbox = sandbox;
        self
    }

    const fn without_retention(mut self) -> Self {
        self.suppress_retention = true;
        self
    }

    const fn without_receipt_out(mut self) -> Self {
        self.suppress_receipt_out = true;
        self
    }
}

type Result<T> = std::result::Result<T, Error>;

fn error(status: &'static str, phase: &'static str, detail: impl ToString) -> Error {
    Error {
        status,
        phase,
        detail: detail.to_string(),
        elaboration_sandbox: None,
        suppress_retention: false,
        suppress_receipt_out: false,
    }
}

fn io(phase: &'static str, failure: std::io::Error) -> Error {
    error("tool_failed", phase, failure)
}

fn io_with_path(phase: &'static str, kind: &str, path: &Path, failure: std::io::Error) -> Error {
    error("tool_failed", phase, format!("cannot inspect {kind} {}: {failure}", path.display()))
}

fn identifier(value: &str) -> bool {
    !value.is_empty() && value.split('.').all(crate::is_lean_ident)
}

fn module_of(name: &str) -> Result<String> {
    if !identifier(name) || !name.contains('.') {
        return Err(error("unsupported", "request", "expected a qualified Lean declaration name"));
    }
    Ok(name.rsplit_once('.').unwrap().0.to_owned())
}

/// Return whether `module` names a runner-owned or toolchain-reserved module
/// or namespace.
///
/// The `Trusted` and `Anneal` namespaces hold the installed model and theory,
/// `Captured` and `Expected` are the captured subject and generated claim, and
/// `Init`, `Std`, `Lean`, `Lake`, `TrustedBoundary`, and `SpecPreflight` are
/// reserved for the Lean toolchain and inspector in both pinned and unpinned
/// modes so exported `LEAN_PATH` directories cannot shadow sysroot or
/// inspector modules.
fn reserved_proof_module(module: &str) -> bool {
    matches!(
        module.split('.').next(),
        Some(
            "Captured"
                | "Expected"
                | "Trusted"
                | "Anneal"
                | "Init"
                | "Std"
                | "Lean"
                | "Lake"
                | "TrustedBoundary"
                | "SpecPreflight"
        )
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SymlinkPolicy {
    Reject,
    DereferenceRegular,
}

fn read_input_file(
    path: &Path,
    expected_canon: Option<&Path>,
    policy: SymlinkPolicy,
    phase: &'static str,
) -> Result<(Vec<u8>, String)> {
    let res = match policy {
        SymlinkPolicy::Reject => read_regular_file_strict(path, expected_canon, phase),
        SymlinkPolicy::DereferenceRegular => read_regular_file_deref(path, phase),
    };
    res.map_err(|failure| {
        if failure.code == 1 {
            let msg = if matches!(policy, SymlinkPolicy::Reject) {
                format!("not a declared regular file: {}", path.display())
            } else {
                failure.message
            };
            error("unsupported", phase, msg)
        } else {
            error("tool_failed", phase, failure.message)
        }
    })
}

/// Require a declared regular file beneath an already canonical root.
///
/// Relative paths cannot escape the staging namespace. Canonical equality
/// also rejects symlink traversal; adjacent compiled Lean files are never read.
fn declared_file(root: &Path, relative: &Path) -> Result<PathBuf> {
    if relative.as_os_str().is_empty()
        || relative.components().any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(error("unsupported", "inputs", "input paths must be clean relative paths"));
    }
    let path = root.join(relative);
    let meta = fs::symlink_metadata(&path).map_err(|e| io("inputs", e))?;
    if !meta.is_file()
        || meta.file_type().is_symlink()
        || fs::canonicalize(&path).map_err(|e| io("inputs", e))? != path
    {
        return Err(error(
            "unsupported",
            "inputs",
            format!("not a declared regular file: {}", path.display()),
        ));
    }
    Ok(path)
}

/// Resolve a `request.json` `source_root` (relative to `base` or an absolute
/// out-of-tree path) to an existing canonical directory.
fn root(base: &Path, path: &Path) -> Result<PathBuf> {
    let joined = base.join(path);
    let canon = match fs::canonicalize(&joined) {
        Ok(canon) => canon,
        Err(e)
            if matches!(
                e.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::NotADirectory
            ) =>
        {
            return Err(error(
                "unsupported",
                "inputs",
                format!("source_root is not an existing directory: {}: {e}", joined.display()),
            ));
        }
        Err(e) => return Err(io("inputs", e)),
    };
    let meta = fs::metadata(&canon).map_err(|e| io("inputs", e))?;
    if !meta.is_dir() {
        return Err(error(
            "unsupported",
            "inputs",
            format!("source_root is not a directory: {}", canon.display()),
        ));
    }
    Ok(canon)
}

fn write(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| io("staging", e))?;
    }
    fs::write(path, bytes).map_err(|e| io("staging", e))
}

fn is_false(value: &bool) -> bool {
    !*value
}

fn encoded<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    serde_json::to_vec_pretty(value).map_err(|e| error("tool_failed", "json", e))
}

/// Reject Cargo or toolchain override files under `dir`.
///
/// Uses `symlink_metadata` (without following links) so dangling symlinks are
/// rejected; a plain `.cargo` directory is allowed when it contains no config
/// file, whereas a `.cargo` symlink, non-directory entry (`!meta.is_dir()`),
/// or any non-`NotFound` metadata error fails closed. Toolchain files are
/// always rejected. A `.cargo/config` or `.cargo/config.toml` file is admitted
/// only when [`cargo_config::check_benign_config_file`] proves that it
/// configures nothing but non-compilation tables such as `[alias]`.
fn reject_compiler_overrides(dir: &Path) -> Result<()> {
    let reject = |rel: &str, reason: &str| {
        error(
            "unsupported",
            "cargo",
            format!(
                "compiler overrides need an explicit configured compilation \
                 ({rel}: {reason}; in {})",
                dir.display()
            ),
        )
    };
    for forbidden in
        [".cargo", ".cargo/config", ".cargo/config.toml", "rust-toolchain", "rust-toolchain.toml"]
    {
        let path = dir.join(forbidden);
        match fs::symlink_metadata(&path) {
            Ok(meta) if forbidden == ".cargo" => {
                if meta.file_type().is_symlink() || !meta.is_dir() {
                    return Err(reject(forbidden, "not a regular directory"));
                }
            }
            Ok(_) if forbidden.starts_with(".cargo/") => {
                cargo_config::check_benign_config_file(&path)
                    .map_err(|reason| reject(forbidden, &reason))?;
            }
            Ok(_) => return Err(reject(forbidden, "toolchain override")),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
            Err(err) => return Err(io("cargo", err)),
        }
    }
    Ok(())
}

/// Return whether `name` is a syntactically safe Cargo feature identifier for
/// `rustc` `--cfg=feature="<name>"` emission.
///
/// Rejects empty strings, whitespace, control characters, quotes, backslashes,
/// and Cargo dependency-feature separators (`/`, `:`, `?`) so
/// `feature="{name}"` encodes a single literal string value with zero quoting
/// or `@file` ambiguity.
fn is_valid_cargo_feature_name(name: &str) -> bool {
    !name.is_empty()
        && !name.chars().any(|c| {
            c.is_control() || c.is_whitespace() || matches!(c, '"' | '\\' | '/' | ':' | '?')
        })
}

/// Resolve the active Cargo feature closure into `rustc` `feature="<name>"`
/// `cfg` entries and verify that no normal or build dependency is active.
///
/// Dev-dependencies (`kind == "dev"`) apply only to tests, examples, and
/// benchmarks, so they never enter library or binary compilation. Optional
/// normal or build dependencies (`optional == true`) are permitted when left
/// inactive and rejected fail-closed as soon as an active feature enables
/// `dep:<name>` or `<name>/<subfeature>`. Weak dependency features
/// (`<name>?/<subfeature>`) do not activate `<name>` on their own and remain
/// no-ops while `<name>` stays inactive.
fn resolve_cargo_package_cfg(
    package: &Value,
    features_arg: &[String],
    all_features: bool,
    no_default_features: bool,
) -> Result<BTreeSet<String>> {
    let pkg_name = package["name"].as_str().unwrap_or("<package>");
    let features_map = package["features"]
        .as_object()
        .ok_or_else(|| error("tool_failed", "cargo", "missing Cargo features table"))?;
    let deps_arr = package["dependencies"]
        .as_array()
        .ok_or_else(|| error("tool_failed", "cargo", "missing Cargo dependencies list"))?;

    let mut optional_deps = BTreeSet::new();
    for dep in deps_arr {
        let dep_obj = dep
            .as_object()
            .ok_or_else(|| error("tool_failed", "cargo", "malformed Cargo dependency entry"))?;
        let name = dep_obj
            .get("name")
            .and_then(Value::as_str)
            .filter(|s| !s.is_empty())
            .ok_or_else(|| error("tool_failed", "cargo", "missing Cargo dependency name"))?;
        let dep_key = match dep_obj.get("rename") {
            None | Some(Value::Null) => name,
            Some(Value::String(rename)) if !rename.is_empty() => rename.as_str(),
            _ => {
                return Err(error("tool_failed", "cargo", "malformed Cargo dependency rename"));
            }
        };
        let optional = dep_obj.get("optional").and_then(Value::as_bool).ok_or_else(|| {
            error("tool_failed", "cargo", "missing Cargo dependency optional flag")
        })?;
        match dep_obj.get("kind") {
            Some(Value::String(kind)) if kind == "dev" => {}
            None | Some(Value::Null) => {
                if !optional {
                    return Err(error(
                        "unsupported",
                        "cargo",
                        "Cargo shortcut requires a dependency-free crate; \
                         use an explicit compilation request",
                    ));
                }
                optional_deps.insert(dep_key.to_owned());
            }
            Some(Value::String(kind)) if kind == "build" => {
                if !optional {
                    return Err(error(
                        "unsupported",
                        "cargo",
                        "Cargo shortcut requires a dependency-free crate; \
                         use an explicit compilation request",
                    ));
                }
                optional_deps.insert(dep_key.to_owned());
            }
            _ => {
                return Err(error("tool_failed", "cargo", "unexpected Cargo dependency kind"));
            }
        }
    }

    for key in features_map.keys() {
        if !is_valid_cargo_feature_name(key) {
            return Err(error(
                "unsupported",
                "cargo",
                format!("unsupported Cargo feature identifier: {key:?}"),
            ));
        }
    }

    let mut requested = Vec::new();
    for raw in features_arg {
        for tok in raw.split(|c: char| c == ',' || c.is_ascii_whitespace()) {
            if tok.is_empty() {
                continue;
            }
            if tok.starts_with("dep:") || tok.contains('/') {
                return Err(error(
                    "unsupported",
                    "cargo",
                    format!(
                        "Cargo shortcut requires a dependency-free crate \
                         (cannot activate dependency feature `{tok}`); \
                         use an explicit compilation request"
                    ),
                ));
            }
            if !is_valid_cargo_feature_name(tok) || !features_map.contains_key(tok) {
                return Err(error(
                    "unsupported",
                    "cargo",
                    format!("package `{pkg_name}` does not have feature `{tok}`"),
                ));
            }
            requested.push(tok.to_owned());
        }
    }

    let mut active_features = BTreeSet::new();
    let mut queue = VecDeque::new();
    let activate = |feat: &str, active: &mut BTreeSet<String>, q: &mut VecDeque<String>| {
        if active.insert(feat.to_owned()) {
            q.push_back(feat.to_owned());
        }
    };

    if all_features {
        for key in features_map.keys() {
            activate(key, &mut active_features, &mut queue);
        }
    } else {
        if !no_default_features && features_map.contains_key("default") {
            activate("default", &mut active_features, &mut queue);
        }
        for feat in &requested {
            activate(feat, &mut active_features, &mut queue);
        }
    }

    while let Some(feat) = queue.pop_front() {
        let items = features_map
            .get(&feat)
            .and_then(Value::as_array)
            .ok_or_else(|| error("tool_failed", "cargo", "malformed Cargo feature list"))?;
        for raw_item in items {
            let item = raw_item
                .as_str()
                .ok_or_else(|| error("tool_failed", "cargo", "malformed Cargo feature entry"))?;
            if let Some(dep_key) = item.strip_prefix("dep:") {
                return Err(error(
                    "unsupported",
                    "cargo",
                    format!(
                        "Cargo shortcut requires a dependency-free crate \
                         (feature `{feat}` activates dependency `{dep_key}`); \
                         use an explicit compilation request"
                    ),
                ));
            } else if let Some((dep_key, sub_feat)) = item.split_once("?/") {
                if dep_key.is_empty() || sub_feat.is_empty() || !optional_deps.contains(dep_key) {
                    return Err(error(
                        "unsupported",
                        "cargo",
                        format!(
                            "feature `{feat}` references unknown optional dependency `{dep_key}`"
                        ),
                    ));
                }
            } else if let Some((dep_key, _)) = item.split_once('/') {
                return Err(error(
                    "unsupported",
                    "cargo",
                    format!(
                        "Cargo shortcut requires a dependency-free crate \
                         (feature `{feat}` activates dependency `{dep_key}`); \
                         use an explicit compilation request"
                    ),
                ));
            } else {
                if !features_map.contains_key(item) {
                    return Err(error(
                        "unsupported",
                        "cargo",
                        format!("feature `{feat}` enables unknown feature `{item}`"),
                    ));
                }
                activate(item, &mut active_features, &mut queue);
            }
        }
    }

    Ok(active_features.into_iter().map(|feat| format!("feature=\"{feat}\"")).collect())
}

/// Run `cargo metadata --no-deps --offline` for the package whose manifest
/// is `manifest_path`, after refusing compiler overrides in its directory.
/// Returns the canonical package root, the metadata, and the package's index
/// in `metadata["packages"]`.
fn cargo_package_metadata(manifest_path: &Path) -> Result<(PathBuf, Value, usize)> {
    let manifest = fs::canonicalize(manifest_path)
        .map_err(|e| io_with_path("cargo", "Cargo manifest", manifest_path, e))?;
    let source_root = manifest
        .parent()
        .ok_or_else(|| error("unsupported", "cargo", "manifest path has no parent directory"))?
        .to_path_buf();
    reject_compiler_overrides(&source_root)?;
    let probe_cwd = tempfile::tempdir().map_err(|e| io("cargo", e))?;
    let mut cargo = Command::new("cargo");
    cargo.current_dir(probe_cwd.path()).env_clear();
    for key in ["PATH", "HOME", "CARGO_HOME", "RUSTUP_HOME", "TMPDIR"] {
        if let Some(value) = std::env::var_os(key) {
            cargo.env(key, value);
        }
    }
    let output = cargo
        .args(["metadata", "--format-version=1", "--no-deps", "--offline", "--manifest-path"])
        .arg(&manifest)
        .output()
        .map_err(|e| io("cargo", e))?;
    if !output.status.success() {
        return Err(error("compiler_failed", "cargo", String::from_utf8_lossy(&output.stderr)));
    }
    let metadata: Value =
        serde_json::from_slice(&output.stdout).map_err(|e| error("tool_failed", "cargo", e))?;
    let package_index = metadata["packages"]
        .as_array()
        .and_then(|packages| {
            packages.iter().position(|p| p["manifest_path"].as_str() == manifest.to_str())
        })
        .ok_or_else(|| {
            error("unsupported", "cargo", "choose a package Cargo.toml, not a virtual workspace")
        })?;
    Ok((source_root, metadata, package_index))
}

/// Refuse compiler overrides in every directory from `source_root` up to the
/// workspace root that `metadata` reports.
fn reject_workspace_compiler_overrides(source_root: &Path, metadata: &Value) -> Result<()> {
    let workspace_root =
        metadata["workspace_root"].as_str().and_then(|root| fs::canonicalize(root).ok());
    for ancestor in source_root.ancestors() {
        reject_compiler_overrides(ancestor)?;
        if workspace_root.as_deref() == Some(ancestor) {
            break;
        }
    }
    Ok(())
}

/// List the manifest and the root file of every target in the Cargo package
/// at `manifest_path`, without the shortcut's other restrictions, so that
/// `--overwrite-artifacts` can refuse a destination that holds any of them
/// before it modifies that destination.
fn cargo_target_paths(manifest_path: &Path) -> Result<Vec<PathBuf>> {
    let (source_root, metadata, package_index) = cargo_package_metadata(manifest_path)?;
    reject_workspace_compiler_overrides(&source_root, &metadata)?;
    let package = &metadata["packages"][package_index];
    let mut paths = vec![manifest_path.to_path_buf()];
    for target in package["targets"]
        .as_array()
        .ok_or_else(|| error("tool_failed", "cargo", "missing Cargo targets"))?
    {
        let src_path = target["src_path"]
            .as_str()
            .ok_or_else(|| error("tool_failed", "cargo", "missing Cargo target path"))?;
        paths.push(PathBuf::from(src_path));
    }
    Ok(paths)
}

// Cargo is an input-discovery shortcut, not a second verification profile.
// Reject configurations this adapter cannot reproduce before building the
// same explicit request consumed by the build-neutral path.
#[allow(clippy::too_many_arguments)]
fn cargo_compilation(
    manifest_path: &Path,
    panic: Option<PanicStrategy>,
    overflow_checks: bool,
    select: &[String],
    instantiate: &[Instantiation],
    features: &[String],
    all_features: bool,
    no_default_features: bool,
    skip_dir: Option<&Path>,
) -> Result<(Compilation, Scope, PathBuf)> {
    let (source_root, metadata, package_index) = cargo_package_metadata(manifest_path)?;
    let package = &metadata["packages"][package_index];
    let targets = package["targets"]
        .as_array()
        .ok_or_else(|| error("tool_failed", "cargo", "missing Cargo targets"))?;
    if targets.iter().any(|t| {
        t["kind"]
            .as_array()
            .is_some_and(|ks| ks.iter().any(|k| k == "custom-build" || k == "proc-macro"))
    }) {
        return Err(error(
            "unsupported",
            "cargo",
            "build scripts and procedural macros need an explicit configured compilation",
        ));
    }
    let cfg = resolve_cargo_package_cfg(package, features, all_features, no_default_features)?;
    let mut primary_targets = targets.iter().filter_map(|t| {
        let kinds = t["kind"].as_array()?;
        if kinds.iter().any(|k| k == "bin") {
            Some((CrateType::Bin, t))
        } else if kinds.iter().any(|k| k == "lib" || k == "rlib") {
            Some((CrateType::Lib, t))
        } else {
            None
        }
    });
    let (crate_type, target_meta) = primary_targets.next().ok_or_else(|| {
        error("unsupported", "cargo", "Cargo shortcut requires a single library or binary target")
    })?;
    if primary_targets.next().is_some() {
        return Err(error(
            "unsupported",
            "cargo",
            "Cargo shortcut requires a single library or binary target; \
             use an explicit compilation request",
        ));
    }
    if crate_type == CrateType::Bin {
        match target_meta.get("required-features") {
            None | Some(Value::Null) => {}
            Some(Value::Array(reqs)) => {
                for raw_req in reqs {
                    let req = raw_req.as_str().ok_or_else(|| {
                        error("tool_failed", "cargo", "malformed Cargo required-features entry")
                    })?;
                    if !cfg.contains(&format!("feature=\"{req}\"")) {
                        let target_name = target_meta["name"].as_str().unwrap_or("<target>");
                        return Err(error(
                            "unsupported",
                            "cargo",
                            format!(
                                "target `{target_name}` requires Cargo feature `{req}`, \
                                 which is not enabled"
                            ),
                        ));
                    }
                }
            }
            Some(_) => {
                return Err(error("tool_failed", "cargo", "malformed Cargo required-features"));
            }
        }
    }
    reject_workspace_compiler_overrides(&source_root, &metadata)?;
    let crate_root = Path::new(target_meta["src_path"].as_str().unwrap_or_default())
        .strip_prefix(&source_root)
        .map_err(|_| error("unsupported", "cargo", "target root escapes package"))?
        .to_path_buf();
    let mut non_primary_target_files = BTreeSet::new();
    for other_target in targets {
        if std::ptr::eq(other_target, target_meta) {
            continue;
        }
        if let Some(src_path) = other_target["src_path"].as_str()
            && let Ok(rel) = Path::new(src_path).strip_prefix(&source_root)
            && rel != crate_root
        {
            non_primary_target_files.insert(rel.to_path_buf());
        }
    }
    // This shortcut declares a namespace of .rs files for the selected primary
    // target, excluding Cargo's top-level `tests/`, `benches/`, and `examples/`
    // multi-target trees (and explicit non-primary target entrypoints) unless
    // `crate_root` itself lives inside one. Other compiler inputs require an
    // explicit request: importing every package file would stage unrelated
    // data, proof packages, and build outputs. `skip_dir` is an existing
    // artifact directory that `--overwrite-artifacts` will replace: its
    // staged copies of earlier inputs are outputs, not sources.
    let mut source_files = Vec::new();
    for entry in
        walkdir::WalkDir::new(&source_root).follow_links(false).into_iter().filter_entry(|e| {
            if e.depth() == 0 {
                return true;
            }
            if skip_dir == Some(e.path()) {
                return false;
            }
            let name = e.file_name();
            if name.to_string_lossy().starts_with('.') || name == "target" {
                return false;
            }
            if e.depth() == 1
                && !e.file_type().is_file()
                && matches!(name.to_str(), Some("tests" | "benches" | "examples"))
                && !crate_root.starts_with(name)
            {
                return false;
            }
            true
        })
    {
        let entry = entry.map_err(|e| error("tool_failed", "cargo", e))?;
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "rs") {
            let rel = entry.path().strip_prefix(&source_root).unwrap().to_path_buf();
            if !non_primary_target_files.contains(&rel) {
                source_files.push(rel);
            }
        }
    }
    source_files.sort();
    let scope = if select.is_empty() && instantiate.is_empty() {
        Scope::Crate {}
    } else {
        Scope::SelectedUnit {
            roots: select.iter().cloned().collect(),
            instantiations: instantiate.iter().cloned().collect(),
        }
    };
    let pkg_dir = source_root.clone();
    Ok((
        Compilation {
            source_root,
            crate_root,
            crate_name: target_meta["name"].as_str().unwrap_or_default().replace('-', "_"),
            crate_type,
            panic: panic.unwrap_or_default(),
            overflow_checks,
            edition: target_meta["edition"].as_str().unwrap_or("2024").to_owned(),
            target: target(),
            cfg,
            env: BTreeMap::new(),
            source_files,
            stdlib_crate: None,
        },
        scope,
        pkg_dir,
    ))
}

fn cargo_request(args: &VerifyArgs, manifest: &Path) -> Result<(Request, PathBuf)> {
    // Main has already admitted an existing `--overwrite-artifacts`
    // destination; skip it so a rerun does not discover its own artifacts.
    let skip_dir = args
        .artifacts
        .as_deref()
        .filter(|_| args.overwrite_artifacts)
        .and_then(|destination| fs::canonicalize(destination).ok());
    let (compilation, scope, base) = cargo_compilation(
        manifest,
        args.panic,
        args.overflow_checks,
        &args.select,
        &args.instantiate,
        &args.features,
        args.all_features,
        args.no_default_features,
        skip_dir.as_deref(),
    )?;
    let proof_dir = args.proof_dir.as_ref().ok_or_else(|| {
        error("unsupported", "request", "--proof-dir is required with --manifest-path")
    })?;
    let proof_root = fs::canonicalize(proof_dir)
        .map_err(|e| io_with_path("proof", "proof directory", proof_dir, e))?;
    let mut sources = Vec::new();
    for entry in
        walkdir::WalkDir::new(&proof_root).follow_links(false).into_iter().filter_entry(|e| {
            e.depth() == 0
                || (!e.file_name().to_string_lossy().starts_with('.')
                    && skip_dir.as_deref() != Some(e.path()))
        })
    {
        let entry = entry.map_err(|e| error("tool_failed", "proof", e))?;
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "lean") {
            let path = entry.path().strip_prefix(&proof_root).unwrap().to_path_buf();
            let module =
                path.with_extension("").to_string_lossy().replace(std::path::MAIN_SEPARATOR, ".");
            sources.push(ProofSource {
                role: if module == "Spec" || module.starts_with("Spec.") {
                    AuthoredRole::Specification
                } else {
                    AuthoredRole::Proof
                },
                module,
                path,
            });
        }
    }
    sources.sort_by(|a, b| a.module.cmp(&b.module));
    Ok((
        Request {
            schema_version: 1,
            compilation,
            scope,
            proof: Proof {
                source_root: proof_root,
                specification: spec_name(),
                theorem: proof_name(),
                specification_module: None,
                theorem_module: None,
                sources,
            },
        },
        base,
    ))
}

fn load_request(args: &VerifyArgs) -> Result<(Request, PathBuf)> {
    if let Some(path) = &args.request {
        let path = fs::canonicalize(path).map_err(|e| io("request", e))?;
        let (bytes, _) = read_regular_file_deref(&path, "request")
            .map_err(|e| error("tool_failed", "request", e.message))?;
        let request: Request =
            serde_json::from_slice(&bytes).map_err(|e| error("unsupported", "request", e))?;
        Ok((request, path.parent().unwrap().to_path_buf()))
    } else {
        cargo_request(args, args.manifest_path.as_ref().unwrap())
    }
}

fn normalize_lexical(path: &Path) -> Result<(bool, Vec<OsString>)> {
    if path.as_os_str().is_empty() {
        return Err(error("unsupported", "inputs", "Rust source path must not be empty"));
    }
    let mut is_abs = false;
    let mut comps = Vec::new();
    for comp in path.components() {
        match comp {
            Component::Prefix(_) => {
                return Err(error("unsupported", "inputs", "unsupported path prefix"));
            }
            Component::RootDir => is_abs = true,
            Component::CurDir => {}
            Component::ParentDir => {
                return Err(error(
                    "unsupported",
                    "inputs",
                    format!("source path must not contain '..': {}", path.display()),
                ));
            }
            Component::Normal(part) => comps.push(part.to_os_string()),
        }
    }
    if comps.is_empty() {
        return Err(error(
            "unsupported",
            "inputs",
            format!("source path must name a file: {}", path.display()),
        ));
    }
    Ok((is_abs, comps))
}

fn stage_rustc_rust_inputs(
    rustc: &RustcArgs,
    rust_stage: &Path,
    originals: &mut Vec<(PathBuf, String)>,
) -> Result<(PathBuf, Vec<PathBuf>, Vec<SourceIdentity>)> {
    let (root_abs, root_comps) = normalize_lexical(&rustc.crate_root)?;
    let mut entries = vec![(rustc.crate_root.clone(), root_comps.clone())];
    let mut seen = BTreeSet::from([root_comps.clone()]);
    for path in &rustc.source_file {
        let (src_abs, src_comps) = normalize_lexical(path)?;
        if src_abs != root_abs {
            return Err(error(
                "unsupported",
                "inputs",
                "cannot mix relative and absolute Rust source paths",
            ));
        }
        if seen.insert(src_comps.clone()) {
            entries.push((path.clone(), src_comps));
        }
    }
    let mut common_dir: Vec<OsString> = entries[0].1[..entries[0].1.len() - 1].to_vec();
    for (_, comps) in &entries[1..] {
        let parent = &comps[..comps.len() - 1];
        let shared = common_dir.iter().zip(parent.iter()).take_while(|(a, b)| a == b).count();
        common_dir.truncate(shared);
    }
    if root_abs && common_dir.is_empty() {
        return Err(error(
            "unsupported",
            "inputs",
            "absolute Rust source paths must share a non-root common directory prefix",
        ));
    }

    let prefix_len = common_dir.len();
    let mut crate_root_rel = None;
    let mut staged = Vec::with_capacity(entries.len());
    for (idx, (orig_path, comps)) in entries.into_iter().enumerate() {
        let mut rel = PathBuf::new();
        for comp in &comps[prefix_len..] {
            rel.push(comp);
        }
        if rel.as_os_str().is_empty()
            || rel.components().any(|part| !matches!(part, Component::Normal(_)))
        {
            return Err(error(
                "unsupported",
                "inputs",
                "staged Rust path must be a clean relative path",
            ));
        }
        if idx == 0 {
            crate_root_rel = Some(rel.clone());
        }
        let (bytes, sha256) =
            read_input_file(&orig_path, None, SymlinkPolicy::DereferenceRegular, "inputs")?;
        write(&rust_stage.join(&rel), &bytes)?;
        originals.push((orig_path, sha256.clone()));
        staged.push((rel.clone(), SourceIdentity { relative_path: rel, sha256 }));
    }
    staged.sort_by(|a, b| a.0.cmp(&b.0));
    let source_files = staged.iter().map(|(rel, _)| rel.clone()).collect();
    let sources = staged.into_iter().map(|(_, id)| id).collect();
    Ok((crate_root_rel.expect("crate_root included"), source_files, sources))
}

struct StagedAuthored {
    module: String,
    source: PathBuf,
    sha256: String,
    role: AuthoredRole,
}

struct PreparedRustcRequest {
    request: Request,
    sources: Vec<SourceIdentity>,
    authored: Vec<StagedAuthored>,
}

fn prepare_rustc_request(
    rustc: &RustcArgs,
    work: &Path,
    originals: &mut Vec<(PathBuf, String)>,
) -> Result<PreparedRustcRequest> {
    let rust_stage = work.join("rust");
    fs::create_dir_all(&rust_stage).map_err(|e| io("staging", e))?;
    let (crate_root, source_files, sources) =
        stage_rustc_rust_inputs(rustc, &rust_stage, originals)?;

    let mut seen_modules = BTreeSet::new();
    let mut authored = Vec::new();
    let mut proof_sources = Vec::new();
    for (entry, role) in rustc
        .spec_file
        .iter()
        .map(|e| (e, AuthoredRole::Specification))
        .chain(rustc.proof_file.iter().map(|e| (e, AuthoredRole::Proof)))
    {
        if !identifier(&entry.module)
            || reserved_proof_module(&entry.module)
            || !seen_modules.insert(entry.module.clone())
        {
            return Err(error(
                "unsupported",
                "proof",
                "invalid, duplicate or reserved proof module",
            ));
        }
        let rel_path = PathBuf::from(format!("{}.lean", entry.module.replace('.', "/")));
        let (bytes, sha256) =
            read_input_file(&entry.path, None, SymlinkPolicy::DereferenceRegular, "proof")?;
        let staged_path = work.join("authored").join(&rel_path);
        write(&staged_path, &bytes)?;
        originals.push((entry.path.clone(), sha256.clone()));
        proof_sources.push(ProofSource {
            module: entry.module.clone(),
            path: rel_path,
            role: role.clone(),
        });
        authored.push(StagedAuthored {
            module: entry.module.clone(),
            source: staged_path,
            sha256,
            role,
        });
    }
    proof_sources.sort_by(|a, b| a.module.cmp(&b.module));
    authored.sort_by(|a, b| a.module.cmp(&b.module));

    let spec_module = match &rustc.spec_decl.module {
        Some(module) => module.clone(),
        None => module_of(&rustc.spec_decl.decl)?,
    };
    let theorem_module = match &rustc.theorem.module {
        Some(module) => module.clone(),
        None => module_of(&rustc.theorem.decl)?,
    };
    if !authored
        .iter()
        .any(|m| m.module == spec_module && matches!(m.role, AuthoredRole::Specification))
        || !authored
            .iter()
            .any(|m| m.module == theorem_module && matches!(m.role, AuthoredRole::Proof))
    {
        return Err(error(
            "unsupported",
            "proof",
            "specification and theorem must have their declared source roles",
        ));
    }

    let scope = if rustc.select.is_empty() && rustc.instantiate.is_empty() {
        Scope::Crate {}
    } else {
        Scope::SelectedUnit {
            roots: rustc.select.iter().cloned().collect(),
            instantiations: rustc.instantiate.iter().cloned().collect(),
        }
    };
    let request = Request {
        schema_version: 1,
        compilation: Compilation {
            source_root: PathBuf::from("rust"),
            crate_root,
            crate_name: rustc.crate_name.clone(),
            crate_type: rustc.crate_type,
            panic: rustc.panic,
            overflow_checks: rustc.overflow_checks,
            edition: rustc.edition.clone(),
            target: rustc.target.clone(),
            cfg: rustc.cfg.iter().cloned().collect(),
            env: rustc.env.iter().cloned().collect(),
            source_files,
            stdlib_crate: rustc.stdlib_crate,
        },
        scope,
        proof: Proof {
            source_root: PathBuf::from("authored"),
            specification: rustc.spec_decl.decl.clone(),
            theorem: rustc.theorem.decl.clone(),
            specification_module: rustc.spec_decl.module.clone(),
            theorem_module: rustc.theorem.module.clone(),
            sources: proof_sources,
        },
    };
    Ok(PreparedRustcRequest { request, sources, authored })
}

struct SelectedTools {
    capture: PathBuf,
    sysroot: Option<PathBuf>,
    lean: Option<PathBuf>,
    prebuilt_dir: Option<PathBuf>,
    // Keep the shared bundle flock held until `verify::run` finishes so a
    // concurrent `setup --local-archive` cannot swap toolchain binaries in use.
    #[cfg(feature = "setup")]
    _bundle_lease: Option<crate::setup::Bundle>,
}

fn select_tools(args: &VerifyArgs) -> Result<SelectedTools> {
    select_tools_with(args.capture.as_deref(), args.sysroot.as_deref(), args.lean.as_deref(), true)
}

fn select_tools_with(
    capture: Option<&Path>,
    sysroot: Option<&Path>,
    lean: Option<&Path>,
    require_lean: bool,
) -> Result<SelectedTools> {
    #[cfg(feature = "setup")]
    {
        let needs_discovery =
            capture.is_none() || sysroot.is_none() || (require_lean && lean.is_none());
        let installed = if needs_discovery {
            installed_bundle().map_err(|detail| error("tool_failed", "capture-tool", detail))?
        } else {
            None
        };
        let tools = resolve_tools(
            ToolOverrides {
                capture: capture.map(Path::to_path_buf),
                sysroot: sysroot.map(Path::to_path_buf),
                lean: lean.map(Path::to_path_buf),
            },
            installed.as_ref(),
            std::env::current_exe(),
        )
        .map_err(|detail| error("tool_failed", "capture-tool", detail))?;
        let prebuilt_dir = if require_lean && lean.is_none() {
            installed.as_ref().map(crate::setup::Bundle::prebuilt_dir)
        } else {
            None
        };
        Ok(SelectedTools {
            capture: tools.capture,
            sysroot: tools.sysroot,
            lean: tools.lean,
            prebuilt_dir,
            _bundle_lease: installed,
        })
    }
    #[cfg(not(feature = "setup"))]
    {
        match (capture, sysroot, lean) {
            (Some(capture), Some(sysroot), lean_opt) if !require_lean || lean_opt.is_some() => {
                Ok(SelectedTools {
                    capture: capture.to_path_buf(),
                    sysroot: Some(sysroot.to_path_buf()),
                    lean: lean_opt.map(Path::to_path_buf),
                    prebuilt_dir: None,
                })
            }
            _ => {
                let mut missing = Vec::new();
                if capture.is_none() {
                    missing.push("--capture");
                }
                if sysroot.is_none() {
                    missing.push("--sysroot");
                }
                if require_lean && lean.is_none() {
                    missing.push("--lean");
                }
                let requirement = if require_lean {
                    "explicit --capture, --sysroot, and --lean tool paths are required \
                     when built without the `setup` feature"
                } else {
                    "explicit --capture and --sysroot tool paths are required when built \
                     without the `setup` feature"
                };
                Err(error(
                    "tool_failed",
                    "capture-tool",
                    format!("missing {}; {requirement}", missing.join(", ")),
                ))
            }
        }
    }
}

/// Normalize `path` lexically to an absolute path without resolving symlinks,
/// preserving virtual symlink-forest topologies (such as `<sysroot>/bin/rustc`
/// beside `<sysroot>/lib/rustlib`).
fn normalize_lexical_absolute(path: &Path) -> std::io::Result<PathBuf> {
    use std::path::Component;

    let abs =
        if path.is_absolute() { path.to_path_buf() } else { std::env::current_dir()?.join(path) };
    let mut normalized = PathBuf::new();
    for component in abs.components() {
        match component {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                if !normalized.pop() {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidInput,
                        format!("cannot normalize parent component past root: {}", path.display()),
                    ));
                }
            }
            Component::Normal(part) => normalized.push(part),
        }
    }
    Ok(normalized)
}

#[derive(Clone, Debug)]
struct ValidatedReceiptOut {
    raw_path: PathBuf,
    display_str: String,
    canon_parent: PathBuf,
    canon_target: PathBuf,
    #[cfg(unix)]
    canon_parent_inode: (u64, u64),
    #[cfg(unix)]
    existing_inode: Option<(u64, u64)>,
}

fn receipt_parent(path: &Path) -> &Path {
    match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    }
}

#[cfg(unix)]
fn inode_key(meta: &fs::Metadata) -> (u64, u64) {
    use std::os::unix::fs::MetadataExt as _;
    (meta.dev(), meta.ino())
}

/// Resolve `path` left-to-right, canonicalizing each existing prefix before
/// applying subsequent `..` components so `<symlink>/..` resolves identically
/// to OS path lookup even when trailing components do not yet exist.
fn resolve_path_preserving_symlinks(path: &Path) -> std::io::Result<PathBuf> {
    if let Ok(canon) = fs::canonicalize(path) {
        return Ok(canon);
    }
    let mut current = if path.is_absolute() {
        PathBuf::new()
    } else {
        fs::canonicalize(std::env::current_dir()?)?
    };
    let mut existing = true;
    for comp in path.components() {
        match comp {
            Component::Prefix(p) => current.push(p.as_os_str()),
            Component::RootDir => current.push(comp.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                if existing && let Ok(canon) = fs::canonicalize(&current) {
                    current = canon;
                }
                current.pop();
                if existing {
                    if let Ok(canon) = fs::canonicalize(&current) {
                        current = canon;
                    } else {
                        existing = false;
                    }
                }
            }
            Component::Normal(part) => {
                current.push(part);
                if existing {
                    if let Ok(canon) = fs::canonicalize(&current) {
                        current = canon;
                    } else {
                        existing = false;
                    }
                }
            }
        }
    }
    Ok(current)
}

fn candidate_aliases_receipt_out(target: &ValidatedReceiptOut, candidate: &Path) -> bool {
    if let Ok(canon) = fs::canonicalize(candidate)
        && canon == target.canon_target
    {
        return true;
    }
    if let Ok(resolved) = resolve_path_preserving_symlinks(candidate)
        && resolved == target.canon_target
    {
        return true;
    }
    if let Some(name) = candidate.file_name()
        && let Ok(canon_parent) = fs::canonicalize(receipt_parent(candidate))
        && canon_parent.join(name) == target.canon_target
    {
        return true;
    }
    if let Ok(lex) = normalize_lexical_absolute(candidate)
        && lex == target.canon_target
    {
        return true;
    }
    #[cfg(unix)]
    if let Some(target_ino) = target.existing_inode
        && let Ok(meta) = fs::metadata(candidate)
        && inode_key(&meta) == target_ino
    {
        return true;
    }
    false
}

fn validate_receipt_out_pre_stage(
    args: &VerifyArgs,
    artifacts: Option<&str>,
) -> std::result::Result<Option<ValidatedReceiptOut>, String> {
    let Some(raw_path) = args.receipt_out.as_ref() else {
        return Ok(None);
    };
    let Some(display_str) = raw_path.to_str() else {
        return Err("receipt destination path must be UTF-8".to_owned());
    };
    let raw_bytes = raw_path.as_os_str().as_encoded_bytes();
    let invalid_leaf = display_str.is_empty()
        || raw_bytes.last().is_some_and(|&b| std::path::is_separator(b as char))
        || raw_bytes == b"."
        || raw_bytes == b".."
        || raw_bytes.ends_with(b"/.")
        || raw_bytes.ends_with(b"/..")
        || raw_bytes.ends_with(b"\\.")
        || raw_bytes.ends_with(b"\\..")
        || !matches!(raw_path.components().next_back(), Some(Component::Normal(_)));
    let Some(file_name) = raw_path.file_name().filter(|_| !invalid_leaf) else {
        return Err(format!("invalid receipt destination path: {}", raw_path.display()));
    };
    let parent = receipt_parent(raw_path);
    // Canonicalize the parent directory (matching `--artifacts` so paths under
    // symlinked ancestors like `TMPDIR` or macOS `/var -> private/var` work),
    // while keeping all leaf-symlink, swap, and input-aliasing checks on the
    // canonical path.
    let canon_parent = fs::canonicalize(parent).map_err(|e| {
        format!("cannot canonicalize receipt parent directory {}: {e}", parent.display())
    })?;
    let parent_meta = fs::metadata(&canon_parent).map_err(|e| {
        format!("cannot inspect receipt parent directory {}: {e}", canon_parent.display())
    })?;
    if !parent_meta.is_dir() {
        return Err(format!("receipt parent path is not a directory: {}", parent.display()));
    }
    #[cfg(unix)]
    let canon_parent_inode = inode_key(&parent_meta);
    let canon_target = canon_parent.join(file_name);

    #[cfg(unix)]
    let mut existing_inode = None;
    match fs::symlink_metadata(&canon_target) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(format!("cannot inspect receipt destination {}: {e}", raw_path.display()));
        }
        Ok(meta) => {
            if meta.file_type().is_symlink() {
                return Err(format!(
                    "receipt destination must not be a symlink: {}",
                    raw_path.display()
                ));
            }
            if !meta.file_type().is_file() {
                return Err(format!(
                    "receipt destination must be a regular file: {}",
                    raw_path.display()
                ));
            }
            #[cfg(unix)]
            {
                existing_inode = Some(inode_key(&meta));
            }
        }
    }

    if let Some(art_str) = artifacts {
        let art_path = Path::new(art_str);
        if let Ok(art_resolved) = resolve_path_preserving_symlinks(art_path)
            && (canon_target == art_resolved
                || canon_target.starts_with(&art_resolved)
                || art_resolved.starts_with(&canon_target))
        {
            return Err(format!(
                "receipt destination {} must not alias or reside inside --artifacts {}",
                raw_path.display(),
                art_path.display()
            ));
        }
    }

    let validated = ValidatedReceiptOut {
        raw_path: raw_path.clone(),
        display_str: display_str.to_owned(),
        canon_parent,
        canon_target,
        #[cfg(unix)]
        canon_parent_inode,
        #[cfg(unix)]
        existing_inode,
    };

    // Refuse overwriting Rust/Lean sources or Cargo/Lean toolchain manifests
    // anywhere on disk (including out-of-tree `source_root` targets or
    // workspace-root `Cargo.lock` when `request.json` is malformed or preflight
    // fails before `load_request`).
    let protected_file_name = matches!(
        file_name.to_str(),
        Some(
            "Cargo.toml"
                | "Cargo.lock"
                | "lakefile.toml"
                | "lean-toolchain"
                | "rust-toolchain"
                | "rust-toolchain.toml"
        )
    );
    if validated.canon_target.extension().is_some_and(|e| e == "rs" || e == "lean")
        || protected_file_name
    {
        return Err(format!(
            "receipt destination {} must not target a Rust/Lean source or toolchain manifest",
            raw_path.display()
        ));
    }

    let mut direct_inputs: Vec<PathBuf> = Vec::new();
    let mut protected_dirs: Vec<PathBuf> = Vec::new();
    if let Some(req) = args.request.as_deref() {
        direct_inputs.push(req.to_path_buf());
        // Best-effort pre-stage parse of valid `--request` files so declared
        // out-of-tree `source_root` / `source_files` / `proof.sources` cannot
        // be overwritten by an early preflight or staging failure receipt.
        // Match `load_request` by resolving relative paths against the
        // canonicalized request target's parent when `--request` is a symlink.
        if fs::metadata(req).is_ok_and(|m| m.is_file() && m.len() <= 16 * 1024 * 1024)
            && let Ok(canon_req) = fs::canonicalize(req)
            && let Ok(bytes) = fs::read(&canon_req)
            && let Ok(parsed_req) = serde_json::from_slice::<Request>(&bytes)
        {
            let req_dir = receipt_parent(&canon_req);
            check_request_inputs_receipt_out_aliasing(Some(&validated), req_dir, &parsed_req)
                .map_err(|e| e.detail)?;
        }
    }
    let effective_manifest = if let Some(mp) = args.manifest_path.as_deref() {
        Some(mp)
    } else if args.request.is_none() && !matches!(args.command, Some(VerifySubcommand::Rustc(_))) {
        Some(Path::new("Cargo.toml"))
    } else {
        None
    };
    if let Some(mp) = effective_manifest {
        direct_inputs.push(mp.to_path_buf());
    }
    if let Some(cap) = args.capture.as_deref() {
        direct_inputs.push(cap.to_path_buf());
    }
    if let Some(lean) = args.lean.as_deref() {
        direct_inputs.push(lean.to_path_buf());
    }
    if let Some(sysroot) = args.sysroot.as_deref() {
        direct_inputs.push(sysroot.to_path_buf());
        protected_dirs.push(sysroot.to_path_buf());
    }
    // Also guard auto-discovered toolchain paths and the running executable
    // before preflight/staging can emit an early failure receipt.
    if let Ok(exe) = std::env::current_exe() {
        direct_inputs.push(exe);
    }
    if let Ok(tools) = select_tools(args) {
        direct_inputs.push(tools.capture);
        if let Some(sysroot) = tools.sysroot {
            direct_inputs.push(sysroot.clone());
            protected_dirs.push(sysroot);
        }
        if let Some(lean) = tools.lean {
            direct_inputs.push(lean);
        }
        if let Some(prebuilt) = tools.prebuilt_dir {
            direct_inputs.push(prebuilt.clone());
            protected_dirs.push(prebuilt);
        }
    }
    for dir in &protected_dirs {
        if let Ok(canon_dir) = fs::canonicalize(dir)
            && canon_dir.is_dir()
            && validated.canon_target.starts_with(&canon_dir)
        {
            return Err(format!(
                "receipt destination {} must not reside inside toolchain directory {}",
                raw_path.display(),
                dir.display()
            ));
        }
    }
    if let Some(pd) = args.proof_dir.as_deref() {
        direct_inputs.push(pd.to_path_buf());
    }
    if let Some(plan) = args.verify_shard_plan.as_deref() {
        direct_inputs.push(plan.to_path_buf());
    }
    if let Some(VerifySubcommand::Rustc(rustc)) = &args.command {
        direct_inputs.push(rustc.crate_root.clone());
        for src in &rustc.source_file {
            direct_inputs.push(src.clone());
        }
        for spec in &rustc.spec_file {
            direct_inputs.push(spec.path.clone());
        }
        for proof in &rustc.proof_file {
            direct_inputs.push(proof.path.clone());
        }
    }
    for input in &direct_inputs {
        if candidate_aliases_receipt_out(&validated, input) {
            return Err(format!(
                "receipt destination {} aliases verification input {}",
                raw_path.display(),
                input.display()
            ));
        }
    }
    Ok(Some(validated))
}

fn check_receipt_out_candidate(target: &ValidatedReceiptOut, candidate: &Path) -> Result<()> {
    if candidate_aliases_receipt_out(target, candidate) {
        return Err(error(
            "tool_failed",
            "receipt-out",
            format!(
                "receipt destination {} aliases verification input {}",
                target.raw_path.display(),
                candidate.display()
            ),
        )
        .without_receipt_out()
        .without_retention());
    }
    Ok(())
}

fn check_request_inputs_receipt_out_aliasing(
    receipt_out: Option<&ValidatedReceiptOut>,
    base: &Path,
    request: &Request,
) -> Result<()> {
    let Some(target) = receipt_out else {
        return Ok(());
    };
    let resolve_dir = |raw_dir: &Path| -> PathBuf {
        root(base, raw_dir).unwrap_or_else(|_| {
            if raw_dir.is_absolute() { raw_dir.to_path_buf() } else { base.join(raw_dir) }
        })
    };
    let source_root = resolve_dir(&request.compilation.source_root);
    check_receipt_out_candidate(target, &source_root)?;
    for relative in &request.compilation.source_files {
        let candidate =
            declared_file(&source_root, relative).unwrap_or_else(|_| source_root.join(relative));
        check_receipt_out_candidate(target, &candidate)?;
    }
    let proof_root = resolve_dir(&request.proof.source_root);
    check_receipt_out_candidate(target, &proof_root)?;
    for input in &request.proof.sources {
        let candidate = declared_file(&proof_root, &input.path)
            .unwrap_or_else(|_| proof_root.join(&input.path));
        check_receipt_out_candidate(target, &candidate)?;
    }
    Ok(())
}

fn reject_receipt_out_originals_aliasing(
    receipt_out: Option<&ValidatedReceiptOut>,
    originals: &[(PathBuf, String)],
) -> Result<()> {
    let Some(target) = receipt_out else {
        return Ok(());
    };
    for (orig_path, _) in originals {
        check_receipt_out_candidate(target, orig_path)?;
    }
    Ok(())
}

fn verify_receipt_target_unchanged(
    target: &ValidatedReceiptOut,
) -> std::result::Result<(), String> {
    let parent = receipt_parent(&target.raw_path);
    let current_canon_parent = fs::canonicalize(parent).map_err(|e| {
        format!("cannot canonicalize receipt parent directory {}: {e}", parent.display())
    })?;
    if current_canon_parent != target.canon_parent {
        return Err(format!("receipt parent directory changed before write: {}", parent.display()));
    }
    #[cfg(unix)]
    {
        let current_meta = fs::metadata(&current_canon_parent).map_err(|e| {
            format!(
                "cannot inspect receipt parent directory {}: {e}",
                current_canon_parent.display()
            )
        })?;
        if inode_key(&current_meta) != target.canon_parent_inode {
            return Err(format!(
                "receipt parent directory changed before write: {}",
                parent.display()
            ));
        }
    }
    match fs::symlink_metadata(&target.canon_target) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => {
            Err(format!("cannot inspect receipt destination {}: {e}", target.raw_path.display()))
        }
        Ok(meta) => {
            if meta.file_type().is_symlink() || !meta.file_type().is_file() {
                return Err(format!(
                    "refusing to overwrite non-regular receipt destination {}",
                    target.raw_path.display()
                ));
            }
            Ok(())
        }
    }
}

/// Remove any pre-existing validated regular file at `--receipt-out` before
/// verification work starts (or when a receipt write fails) so an interrupted
/// or failed run cannot leave an earlier passing receipt behind at the same
/// path.
///
/// Re-verifies parent directory identity and (on Unix) the pre-stage regular
/// file inode so we never unlink a symlink or a file created or swapped into
/// place concurrently.
fn invalidate_stale_receipt_out(target: &ValidatedReceiptOut) -> std::result::Result<(), String> {
    verify_receipt_target_unchanged(target)?;
    match fs::symlink_metadata(&target.canon_target) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(format!(
            "cannot inspect stale receipt destination {}: {e}",
            target.raw_path.display()
        )),
        Ok(meta) => {
            if meta.file_type().is_symlink() || !meta.file_type().is_file() {
                return Err(format!(
                    "refusing to remove non-regular receipt destination {}",
                    target.raw_path.display()
                ));
            }
            #[cfg(unix)]
            match target.existing_inode {
                Some(expected_ino) if inode_key(&meta) == expected_ino => {}
                Some(_) => {
                    return Err(format!(
                        "receipt destination changed before stale-receipt cleanup: {}",
                        target.raw_path.display()
                    ));
                }
                None => {
                    return Err(format!(
                        "receipt destination appeared before stale-receipt cleanup: {}",
                        target.raw_path.display()
                    ));
                }
            }
            match fs::remove_file(&target.canon_target) {
                Ok(()) => Ok(()),
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
                Err(e) => Err(format!(
                    "cannot clear stale receipt destination {}: {e}",
                    target.raw_path.display()
                )),
            }
        }
    }
}

fn stage_receipt_out_temp(
    target: &ValidatedReceiptOut,
    json_payload: &str,
) -> std::result::Result<tempfile::NamedTempFile, String> {
    verify_receipt_target_unchanged(target)?;
    let mut builder = tempfile::Builder::new();
    builder.prefix(".anneal-receipt-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        builder.permissions(fs::Permissions::from_mode(0o600));
    }
    let mut tmp = builder.tempfile_in(&target.canon_parent).map_err(|e| {
        format!("cannot create temporary receipt in {}: {e}", target.canon_parent.display())
    })?;
    tmp.write_all(json_payload.as_bytes())
        .and_then(|()| tmp.write_all(b"\n"))
        .and_then(|()| tmp.flush())
        .map_err(|e| format!("cannot write temporary receipt: {e}"))?;
    Ok(tmp)
}

fn commit_receipt_out_temp(
    tmp: tempfile::NamedTempFile,
    target: &ValidatedReceiptOut,
) -> std::result::Result<(), String> {
    verify_receipt_target_unchanged(target)?;
    tmp.persist(&target.canon_target).map_err(|e| {
        format!("cannot atomically persist receipt to {}: {}", target.raw_path.display(), e.error)
    })?;
    Ok(())
}

fn write_receipt_out_atomic(
    target: &ValidatedReceiptOut,
    json_payload: &str,
) -> std::result::Result<(), String> {
    let tmp = stage_receipt_out_temp(target, json_payload)?;
    commit_receipt_out_temp(tmp, target)
}

fn rollback_retained_artifacts(retained: Option<&str>, mut detail: String) -> String {
    if let Some(dest) = retained
        && let Err(remove_err) = fs::remove_dir_all(dest)
    {
        detail = format!("{detail}; failed to roll back retained artifacts {dest}: {remove_err}");
    }
    detail
}

struct CaptureShardsOutcome {
    manifest: CaptureShardsManifest,
    sha256: String,
    shard_modules: Vec<(String, PathBuf, String)>,
    id_tree_source: String,
}

struct CaptureOutcome {
    capture_sha256: String,
    capture_binary_sha256: String,
    capture_canon: PathBuf,
    capture_tool_path: PathBuf,
    capture_ms: u128,
    manifest: CaptureReceipt,
    shards: Option<CaptureShardsOutcome>,
    unstable_features: CapturedUnstableFeatures,
}

fn stage_request_rust_inputs(
    compilation: &Compilation,
    base: &Path,
    rust_stage: &Path,
    symlink_policy: SymlinkPolicy,
    originals: &mut Vec<(PathBuf, String)>,
) -> Result<Vec<SourceIdentity>> {
    let source_root = root(base, &compilation.source_root)?;
    fs::create_dir_all(rust_stage).map_err(|e| io("staging", e))?;
    let mut sources = Vec::new();
    let mut paths = BTreeSet::new();
    for relative in &compilation.source_files {
        if !paths.insert(relative.clone()) {
            return Err(error("unsupported", "inputs", "duplicate source input"));
        }
        let original = declared_file(&source_root, relative)?;
        let (bytes, sha256) =
            read_input_file(&original, Some(&original), symlink_policy, "inputs")?;
        write(&rust_stage.join(relative), &bytes)?;
        originals.push((original, sha256.clone()));
        sources.push(SourceIdentity { relative_path: relative.clone(), sha256 });
    }
    if !paths.contains(&compilation.crate_root) {
        return Err(error("unsupported", "inputs", "crate_root is not a declared source"));
    }
    Ok(sources)
}

#[allow(clippy::too_many_arguments)]
fn run_capture_process(
    tools: &SelectedTools,
    compilation: &Compilation,
    scope: &Scope,
    sources: &[SourceIdentity],
    rust_stage: &Path,
    capture_dir: &Path,
    work: &Path,
    shard_config: ShardConfig,
    verify_shard_plan_staged: Option<&Path>,
    allowed_unstable_features: &[&str],
    mut write_compiler_stderr: impl FnMut(&[u8]),
) -> Result<CaptureOutcome> {
    let capture_tool_path = tools.capture.clone();
    let capture_canon = fs::canonicalize(&capture_tool_path).map_err(|e| {
        error(
            "tool_failed",
            "capture-tool",
            format!("cannot inspect {}: {e}", capture_tool_path.display()),
        )
    })?;
    let (_, capture_binary_sha256) =
        read_regular_file_strict(&capture_canon, Some(&capture_canon), "capture-tool")
            .map_err(|e| error("tool_failed", "capture-tool", e.message))?;
    // Capture reserves and publishes a new output directory itself; precreating
    // it here would violate its create-only publication contract.
    // Do not let a target crate's ambient compiler wrappers or search paths
    // enter the capture process. The only added library path below comes
    // from the operator-selected compiler installation.
    let mut command = Command::new(&capture_canon);
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .args(["capture", "--crate-root"])
        .arg(rust_stage.join(&compilation.crate_root))
        .args([
            "--crate-name",
            &compilation.crate_name,
            "--crate-type",
            compilation.crate_type.as_str(),
            "--panic",
            compilation.panic.as_str(),
            "--edition",
            &compilation.edition,
            "--target",
            &compilation.target,
            "--out-dir",
        ])
        .arg(capture_dir)
        .current_dir(rust_stage);
    if let Some(sysroot) = &tools.sysroot {
        let sysroot = normalize_lexical_absolute(sysroot).map_err(|e| io("sysroot", e))?;
        if !fs::metadata(&sysroot).map_err(|e| io("sysroot", e))?.is_dir() {
            return Err(error(
                "tool_failed",
                "sysroot",
                format!("sysroot path is not a directory: {}", sysroot.display()),
            ));
        }
        // The library search path belongs to the explicitly selected compiler
        // installation, never to a target crate's ambient environment.
        command.env("LD_LIBRARY_PATH", sysroot.join("lib"));
        command.arg("--sysroot").arg(sysroot);
    }
    match scope {
        Scope::Crate {} => {
            command.args(["--scope", "crate"]);
        }
        Scope::SelectedUnit { roots, instantiations } => {
            if roots.is_empty() && instantiations.is_empty() {
                return Err(error("unsupported", "request", "empty selected scope"));
            }
            for name in roots {
                command.arg("--select").arg(name);
            }
            for inst in instantiations {
                let encoded =
                    serde_json::to_string(inst).map_err(|e| error("unsupported", "request", e))?;
                command.arg("--instantiate").arg(encoded);
            }
        }
    }
    // Preserve each cfg as option data through capture's parser. Capture must
    // use the joined form again when rebuilding compiler argv: the pinned
    // response-file expansion gate is "arg.strip_prefix('@')", before --cfg
    // parsing. Extracting the String must not restore a standalone @file arg.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/args.rs#L14-L32
    for cfg in &compilation.cfg {
        command.arg(format!("--cfg={cfg}"));
    }
    // Pass each explicit compile-time environment binding in joined `--env=...`
    // form so keys starting with `-` stay option data and capture populates
    // `rustc`'s logical environment without inheriting ambient process env.
    for (key, value) in &compilation.env {
        command.arg(format!("--env={key}={value}"));
    }
    for source in sources {
        command.arg("--source-file").arg(rust_stage.join(&source.relative_path));
    }
    if compilation.overflow_checks {
        command.arg("--overflow-checks");
    }
    if let Some(stdlib_crate) = compilation.stdlib_crate {
        command.args(["--stdlib-crate", stdlib_crate.as_str()]);
    }
    for feature in allowed_unstable_features {
        command.arg(format!("--allow-unstable-feature={feature}"));
    }
    command
        .arg("--shard-min-bodies")
        .arg(shard_config.shard_min_bodies.to_string())
        .arg("--shard-max-bodies")
        .arg(shard_config.shard_max_bodies.to_string())
        .arg("--shard-max-ast-nodes")
        .arg(shard_config.shard_max_ast_nodes.to_string());
    if let Some(plan_path) = verify_shard_plan_staged {
        command.arg("--verify-shard-plan").arg(plan_path);
    }
    let capture_start = Instant::now();
    let output = command.output().map_err(|e| io("capture", e))?;
    write(&work.join("capture.stdout"), &output.stdout)?;
    write(&work.join("capture.stderr"), &output.stderr)?;
    if !output.status.success() {
        let envelope: Value = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
        let status = match envelope["status"].as_str() {
            Some("unsupported") => "unsupported",
            Some("compiler_failed") => "compiler_failed",
            _ => "tool_failed",
        };
        let detail = if envelope.is_object() {
            if !output.stderr.is_empty() {
                write_compiler_stderr(&output.stderr);
            }
            envelope.to_string()
        } else {
            String::from_utf8_lossy(&output.stderr).into_owned()
        };
        return Err(error(status, "capture", detail));
    }
    let capture_ms = capture_start.elapsed().as_millis();
    let capture_bytes = fs::read(capture_dir.join("capture.json")).map_err(|e| io("capture", e))?;
    let manifest = parse_capture_receipt(&capture_bytes)?;
    // Authenticate configuration and scope before compiling any authored
    // Lean. A valid theorem about another target or a narrower selection
    // cannot satisfy this request.
    if !matches!(manifest.program.mir_profile_version, 1 | 2) {
        return Err(error(
            "tool_failed",
            "capture",
            format!(
                "unsupported captured MIR profile version {}",
                manifest.program.mir_profile_version
            ),
        ));
    }
    if manifest.program.scope != *scope
        || manifest.configuration["crate_name"] != compilation.crate_name
        || manifest.configuration["crate_type"] != compilation.crate_type.as_str()
        || manifest.configuration["panic"] != compilation.panic.as_str()
        || manifest.configuration["overflow_checks"] != json!(compilation.overflow_checks)
        || manifest.configuration["target"] != compilation.target
        || manifest.configuration["edition"] != compilation.edition
        || manifest.configuration["cfg"] != json!(compilation.cfg)
        || manifest.configuration["env"] != json!(compilation.env)
        // Capture records `stdlib_crate` only when its capability is active,
        // so a capture with relaxed language-item admission never satisfies
        // a request that did not ask for it (or vice versa).
        || manifest.configuration.get("stdlib_crate").cloned()
            != compilation.stdlib_crate.map(|krate| json!(krate.as_str()))
    {
        return Err(error(
            "tool_failed",
            "capture",
            "capture differs from the requested compilation or scope",
        ));
    }
    let unstable_features =
        check_captured_unstable_features(&manifest.configuration, allowed_unstable_features)
            .map_err(|detail| error("tool_failed", "capture", detail))?;
    // Every observed compiler read must match a staged, declared input.
    // Unused declared files remain in the receipt identity; they need not
    // become compiler reads merely because the request staged them.
    let source_by_path: BTreeMap<_, _> =
        sources.iter().map(|s| (rust_stage.join(&s.relative_path), &s.sha256)).collect();
    for source in &manifest.source_files {
        let Some(expected) = source_by_path.get(&source.path) else {
            return Err(error("tool_failed", "capture", "compiler read an undeclared source"));
        };
        if &source.sha256 != *expected {
            return Err(error("tool_failed", "capture", "compiler read different source bytes"));
        }
    }
    let capture_sha256 = sha256_bytes(&capture_bytes);

    let shards_path = capture_dir.join("capture_shards.json");
    let shards = match fs::symlink_metadata(&shards_path) {
        Err(e) if e.kind() == IoErrorKind::NotFound => {
            if manifest.program.bodies.len() > shard_config.shard_min_bodies {
                return Err(error(
                    "tool_failed",
                    "capture",
                    format!(
                        "capture produced {} bodies (> --shard-min-bodies={}) without \
                         capture_shards.json",
                        manifest.program.bodies.len(),
                        shard_config.shard_min_bodies
                    ),
                ));
            }
            None
        }
        Err(e) => return Err(io("capture", e)),
        Ok(meta) => {
            if !meta.file_type().is_file() {
                return Err(error(
                    "tool_failed",
                    "capture",
                    "capture_shards.json must be a regular file",
                ));
            }
            let (shards_bytes, shards_sha256) =
                read_regular_file_strict(&shards_path, Some(&shards_path), "capture")
                    .map_err(|e| error("tool_failed", "capture", e.message))?;
            let shards_manifest = parse_and_validate_capture_shards(
                &shards_bytes,
                scope.shard_label(),
                manifest.program.bodies.len(),
            )
            .map_err(|msg| error("tool_failed", "capture", msg))?;
            if shards_manifest.total_bodies <= shard_config.shard_min_bodies {
                return Err(error(
                    "tool_failed",
                    "capture",
                    format!(
                        "capture_shards.json emitted for {} bodies (<= --shard-min-bodies={})",
                        shards_manifest.total_bodies, shard_config.shard_min_bodies
                    ),
                ));
            }
            let mut shard_modules = Vec::with_capacity(shards_manifest.shards.len());
            let mut all_identities = Vec::with_capacity(shards_manifest.total_bodies);
            for entry in &shards_manifest.shards {
                let shard_path =
                    capture_dir.join("Captured").join(format!("Shard_{:03}.lean", entry.shard_idx));
                let shard_meta = fs::symlink_metadata(&shard_path).map_err(|e| io("capture", e))?;
                if !shard_meta.file_type().is_file() {
                    return Err(error(
                        "tool_failed",
                        "capture",
                        format!("{} must be a regular file", shard_path.display()),
                    ));
                }
                let (_, actual_sha) =
                    read_regular_file_strict(&shard_path, Some(&shard_path), "capture")
                        .map_err(|e| error("tool_failed", "capture", e.message))?;
                if !actual_sha.eq_ignore_ascii_case(&entry.capture_sha256) {
                    return Err(error(
                        "tool_failed",
                        "capture",
                        format!(
                            "capture shard {} digest mismatch: expected {}, got {actual_sha}",
                            entry.capture_module, entry.capture_sha256
                        ),
                    ));
                }
                shard_modules.push((
                    entry.capture_module.clone(),
                    shard_path,
                    entry.capture_sha256.clone(),
                ));
                all_identities.extend(entry.identities.iter().cloned());
            }
            let id_tree_source = render_id_tree_module(&all_identities)
                .map_err(|msg| error("tool_failed", "capture", msg))?;
            let id_tree_actual_sha = sha256_bytes(id_tree_source.as_bytes());
            if !id_tree_actual_sha.eq_ignore_ascii_case(&shards_manifest.id_tree_sha256) {
                return Err(error(
                    "tool_failed",
                    "capture",
                    format!(
                        "generated Proof.IdTree digest {id_tree_actual_sha} disagrees with \
                         capture_shards.json id_tree_sha256 {}",
                        shards_manifest.id_tree_sha256
                    ),
                ));
            }
            Some(CaptureShardsOutcome {
                manifest: shards_manifest,
                sha256: shards_sha256,
                shard_modules,
                id_tree_source,
            })
        }
    };

    Ok(CaptureOutcome {
        capture_sha256,
        capture_binary_sha256,
        capture_canon,
        capture_tool_path,
        capture_ms,
        manifest,
        shards,
        unstable_features,
    })
}

fn run<Out: std::io::Write + Send, ErrOut: std::io::Write + Send>(
    args: &VerifyArgs,
    work: &Path,
    receipt_out: Option<&ValidatedReceiptOut>,
    session: &mut OutputSession<Out, ErrOut>,
    overwrite_inputs: &mut Vec<PathBuf>,
) -> Result<Value> {
    let start = Instant::now();
    session.report_phase(VerifyPhase::Stage);
    let mut originals = Vec::new();
    let (request, base, pre_staged_rust, pre_staged_lean, symlink_policy) =
        if let Some(VerifySubcommand::Rustc(rustc)) = &args.command {
            let prepared = prepare_rustc_request(rustc, work, &mut originals)?;
            reject_receipt_out_originals_aliasing(receipt_out, &originals)?;
            reject_overwrite_input_aliasing(
                args,
                overwrite_inputs,
                originals.iter().map(|(path, _)| path.clone()),
            )?;
            (
                prepared.request,
                work.to_path_buf(),
                Some(prepared.sources),
                Some(prepared.authored),
                SymlinkPolicy::DereferenceRegular,
            )
        } else {
            let (request, base) = load_request(args)?;
            check_request_inputs_receipt_out_aliasing(receipt_out, &base, &request)?;
            reject_overwrite_input_aliasing(
                args,
                overwrite_inputs,
                request_input_paths(&base, &request),
            )?;
            (request, base, None, None, SymlinkPolicy::Reject)
        };
    // All Rust and Lean verification inputs have passed aliasing checks above.
    // Clear any pre-existing regular file at `--receipt-out` before capture or
    // proof checking begins so a timeout, signal, panic, or later receipt-write
    // error cannot leave an older passing receipt behind on disk.
    if let Some(ro) = receipt_out {
        invalidate_stale_receipt_out(ro).map_err(|detail| {
            error("tool_failed", "receipt-out", detail).without_receipt_out().without_retention()
        })?;
    }
    if request.schema_version != 1 || request.compilation.source_files.is_empty() {
        return Err(error("unsupported", "request", "unsupported or empty compilation request"));
    }
    if request.compilation.stdlib_crate.is_some() && !args.allow_unstable_feature.is_empty() {
        return Err(error(
            "tool_failed",
            "request",
            "--allow-unstable-feature cannot be used with a stdlib_crate request",
        ));
    }
    if request.compilation.stdlib_crate.is_some()
        && !matches!(request.scope, Scope::SelectedUnit { .. })
    {
        return Err(error(
            "unsupported",
            "request",
            "--stdlib-crate requires selected scope (`--select` or `--instantiate`)",
        ));
    }
    for (key, value) in &request.compilation.env {
        validate_env_binding(key, value).map_err(|msg| error("unsupported", "request", msg))?;
    }
    if !identifier(&request.proof.specification) || !identifier(&request.proof.theorem) {
        return Err(error("unsupported", "request", "invalid Lean declaration identifier"));
    }
    let spec_module = match &request.proof.specification_module {
        Some(module) if identifier(module) => module.clone(),
        Some(_) => {
            return Err(error("unsupported", "request", "invalid specification module"));
        }
        None => module_of(&request.proof.specification)?,
    };
    let theorem_module = match &request.proof.theorem_module {
        Some(module) if identifier(module) => module.clone(),
        Some(_) => {
            return Err(error("unsupported", "request", "invalid theorem module"));
        }
        None => module_of(&request.proof.theorem)?,
    };
    let shard_config = ShardConfig::from(&args.shard);
    let expected_shard_plan = if let Some(plan_path) = &args.verify_shard_plan {
        let canon_plan = fs::canonicalize(plan_path).map_err(|e| io("shard-plan", e))?;
        let (plan_bytes, plan_sha) = read_regular_file_deref(&canon_plan, "shard-plan")
            .map_err(|e| error("tool_failed", "shard-plan", e.message))?;
        let plan: ShardPlan = serde_json::from_slice(&plan_bytes)
            .map_err(|e| error("unsupported", "shard-plan", format!("invalid shard plan: {e}")))?;
        if plan.schema_version != SHARD_PLAN_SCHEMA_VERSION {
            return Err(error(
                "unsupported",
                "shard-plan",
                format!(
                    "unsupported shard-plan schema_version {} (expected {})",
                    plan.schema_version, SHARD_PLAN_SCHEMA_VERSION
                ),
            ));
        }
        let staged_plan = work.join("expected-shard-plan.json");
        write(&staged_plan, &plan_bytes)?;
        originals.push((canon_plan, plan_sha));
        Some((plan, staged_plan))
    } else {
        None
    };
    // Selection roots, cfg entries, and env bindings use BTreeSet/BTreeMap so
    // spelling order and duplicates normalize automatically in the hashed
    // request identity.
    let request_bytes = encoded(&request)?;
    let request_sha256 = sha256_bytes(&request_bytes);
    write(&work.join("request.json"), &request_bytes)?;

    // Rust and Lean consume private snapshots, not paths they can resolve
    // back into the caller's live checkout. Record the original bytes too:
    // the final identity check must still bind the receipt to those inputs.
    let rust_stage = work.join("rust");
    let sources = if let Some(sources) = pre_staged_rust {
        sources
    } else {
        stage_request_rust_inputs(
            &request.compilation,
            &base,
            &rust_stage,
            symlink_policy,
            &mut originals,
        )?
    };
    // The invocation owns tool selection; target requests cannot name a
    // compiler executable. Adapter correctness is a stated TCB assumption.
    // Its digest identifies the selected build and detects later changes, but
    // no lock pins it. Capture checks only the commit that the Rust compiler
    // and sysroot report; neither is hashed.
    //
    // When built with `setup`, `resolve_tools` checks the user-global installed
    // bundle (resolved via `XDG_CACHE_HOME` / `HOME`) so capture, Rust sysroot,
    // and Lean stay paired, falling back to a sibling capture executable and
    // `default_lean_path` when unavailable. When built without `setup`, all
    // three tool paths must be passed explicitly.
    let tools = select_tools(args)?;
    if let Some(target) = receipt_out {
        check_receipt_out_candidate(target, &tools.capture)?;
        if let Some(sysroot) = tools.sysroot.as_deref() {
            check_receipt_out_candidate(target, sysroot)?;
        }
        if let Some(lean) = tools.lean.as_deref() {
            check_receipt_out_candidate(target, lean)?;
        }
    }
    reject_receipt_out_originals_aliasing(receipt_out, &originals)?;
    reject_overwrite_input_aliasing(
        args,
        overwrite_inputs,
        originals.iter().map(|(path, _)| path.clone()).chain(
            [
                Some(&tools.capture),
                tools.sysroot.as_ref(),
                tools.lean.as_ref(),
                tools.prebuilt_dir.as_ref(),
            ]
            .into_iter()
            .flatten()
            .cloned(),
        ),
    )?;
    session.report_phase(VerifyPhase::Capture {
        crate_name: SanitizedInline::new(&request.compilation.crate_name),
    });
    let capture_dir = work.join("capture");
    let allowed_features = allowed_unstable_features(args);
    let capture_outcome = run_capture_process(
        &tools,
        &request.compilation,
        &request.scope,
        &sources,
        &rust_stage,
        &capture_dir,
        work,
        shard_config,
        expected_shard_plan.as_ref().map(|(_, path)| path.as_path()),
        &allowed_features,
        |stderr| session.write_compiler_stderr(stderr),
    )?;
    if let Some((ref expected_plan, _)) = expected_shard_plan {
        let actual_plan = match &capture_outcome.shards {
            Some(shards) => ShardPlan::from_sharded(&shards.manifest, shard_config),
            None => ShardPlan::from_unsharded(
                request.scope.shard_label(),
                capture_outcome.manifest.program.bodies.len(),
                shard_config,
            ),
        };
        compare_shard_plan(expected_plan, &actual_plan)
            .map_err(|msg| error("tool_failed", "capture", msg))?;
    }
    let capture_sha256 = capture_outcome.capture_sha256;
    let capture_binary_sha256 = capture_outcome.capture_binary_sha256;
    let unstable_features = capture_outcome.unstable_features;
    let capture = capture_outcome.capture_canon;
    let capture_tool_path = capture_outcome.capture_tool_path;
    let capture_ms = capture_outcome.capture_ms;
    let manifest = capture_outcome.manifest;
    let shards_outcome = capture_outcome.shards;

    let bundle = work.join("anneal");
    let mut modules = Vec::new();
    let mut model_identity: Vec<(String, String)> = Vec::new();
    // Installed theory remains proof code even though it ships with the
    // model. Only primitive trusted modules may determine the canonical
    // proposition; packaging must not promote proof helpers into its TCB.
    let mut model_tiers: BTreeMap<String, TrustTier> = BTreeMap::new();
    let mut model_modules: BTreeSet<String> = BTreeSet::new();
    for (relative, text) in BUNDLE {
        let path = bundle.join(relative);
        write(&path, text.as_bytes())?;
        let file_sha256 = sha256_bytes(text.as_bytes());
        model_identity.push(((*relative).to_owned(), file_sha256.clone()));
        if let Some((module, tier)) = bundled_model_tier(relative, text)? {
            model_tiers.insert(module.clone(), tier);
            model_modules.insert(module.clone());
            modules.push(TargetModule {
                module,
                source: path,
                expected_sha256: file_sha256,
                role: TargetRole::Model,
            });
        }
    }
    let bundled_theory = crate::bundle::embedded_theory_bundle().map_err(|e| {
        error("tool_failed", "bundle", format!("corrupt embedded theory bundle: {e}"))
    })?;
    for entry in bundled_theory.modules {
        let path = bundle.join(&entry.path);
        write(&path, entry.content.as_bytes())?;
        model_identity.push((entry.path.clone(), entry.sha256.clone()));
        modules.push(TargetModule {
            module: entry
                .path
                .trim_start_matches("theory/")
                .trim_end_matches(".lean")
                .replace('/', "."),
            source: path,
            expected_sha256: entry.sha256,
            role: TargetRole::Proof,
        });
    }
    let model_manifest_sha256 = sha256_bytes(&encoded(&model_identity)?);
    if let Some(ref shards) = shards_outcome {
        for (module, path, sha256) in &shards.shard_modules {
            modules.push(TargetModule {
                module: module.clone(),
                expected_sha256: sha256.clone(),
                source: path.clone(),
                role: TargetRole::Capture,
            });
        }
    }
    let captured_lean = capture_dir.join("Captured.lean");
    let captured_bytes = fs::read(&captured_lean).map_err(|e| io("capture", e))?;
    modules.push(TargetModule {
        module: "Captured".to_owned(),
        expected_sha256: sha256_bytes(&captured_bytes),
        source: captured_lean,
        role: TargetRole::Capture,
    });
    if let Some(ref shards) = shards_outcome {
        let id_tree_path = work.join("generated/Proof/IdTree.lean");
        write(&id_tree_path, shards.id_tree_source.as_bytes())?;
        modules.push(TargetModule {
            module: "Proof.IdTree".to_owned(),
            expected_sha256: shards.manifest.id_tree_sha256.clone(),
            source: id_tree_path,
            role: TargetRole::Proof,
        });
    }

    // Module names choose destinations in the private stage. Reserve the
    // runner-owned names before writing anything so authored files cannot
    // shadow the model, captured subject, or generated expectation.
    let mut module_names: BTreeSet<_> = modules.iter().map(|m| m.module.clone()).collect();
    let mut spec_identity = Vec::new();
    if let Some(authored) = pre_staged_lean {
        for staged in authored {
            if !identifier(&staged.module)
                || reserved_proof_module(&staged.module)
                || !module_names.insert(staged.module.clone())
            {
                return Err(error(
                    "unsupported",
                    "proof",
                    "invalid, duplicate or reserved proof module",
                ));
            }
            let target_role = match staged.role {
                AuthoredRole::Specification => {
                    spec_identity.push((staged.module.clone(), staged.sha256.clone()));
                    TargetRole::Specification
                }
                AuthoredRole::Proof => TargetRole::Proof,
            };
            modules.push(TargetModule {
                module: staged.module,
                source: staged.source,
                expected_sha256: staged.sha256,
                role: target_role,
            });
        }
    } else {
        let proof_root = root(&base, &request.proof.source_root)?;
        for input in &request.proof.sources {
            if !identifier(&input.module)
                || reserved_proof_module(&input.module)
                || !module_names.insert(input.module.clone())
            {
                return Err(error(
                    "unsupported",
                    "proof",
                    "invalid, duplicate or reserved proof module",
                ));
            }
            let original = declared_file(&proof_root, &input.path)?;
            let (bytes, sha256) =
                read_input_file(&original, Some(&original), symlink_policy, "proof")?;
            originals.push((original, sha256.clone()));
            let source =
                work.join("authored").join(input.module.replace('.', "/")).with_extension("lean");
            write(&source, &bytes)?;
            let role = match input.role {
                AuthoredRole::Specification => {
                    spec_identity.push((input.module.clone(), sha256.clone()));
                    TargetRole::Specification
                }
                AuthoredRole::Proof => TargetRole::Proof,
            };
            modules.push(TargetModule {
                module: input.module.clone(),
                source,
                expected_sha256: sha256,
                role,
            });
        }
    }
    reject_receipt_out_originals_aliasing(receipt_out, &originals)?;
    reject_overwrite_input_aliasing(
        args,
        overwrite_inputs,
        originals.iter().map(|(path, _)| path.clone()),
    )?;
    let spec_entry = modules
        .iter()
        .find(|m| m.module == spec_module && matches!(m.role, TargetRole::Specification))
        .ok_or_else(|| {
            error(
                "unsupported",
                "proof",
                "specification and theorem must have their declared source roles",
            )
        })?;
    if !modules.iter().any(|m| m.module == theorem_module && matches!(m.role, TargetRole::Proof)) {
        return Err(error(
            "unsupported",
            "proof",
            "specification and theorem must have their declared source roles",
        ));
    }
    let spec_bytes = fs::read(&spec_entry.source).map_err(|e| io("spec", e))?;
    let expected_is_module = source_starts_with_module_keyword(&captured_bytes)
        && source_starts_with_module_keyword(&spec_bytes);
    // Keep the reviewed specification identity separate from ordinary
    // proof edits. The auditor also checks actual compiled dependencies,
    // so a helper that changes a specification's meaning needs its role.
    let specification_manifest_sha256 = sha256_bytes(&encoded(&spec_identity)?);
    let (root_name, crate_ctor_ty) =
        request.scope.root_theorem(manifest.program.mir_profile_version);
    // Only validated declaration identifiers enter this fixed template. The
    // authored proof package never supplies an expected proposition or model.
    let header = "-- Copyright 2026 The Fuchsia Authors\n--\n-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n-- This file may not be copied, modified, or distributed except according to\n-- those terms.\n\n";
    let expected = if expected_is_module {
        format!(
            "{header}module\nprelude\npublic import Trusted.MirSemantics\npublic import Captured\npublic import {spec_module}\n\n@[expose] public section\n\nnamespace Expected\ndef claim : Prop := _root_.Trusted.MirSemantics.{root_name} (_root_.Trusted.MirSemantics.{crate_ctor_ty}.mk _root_.Captured.program _root_.{})\nend Expected\n\nend\n",
            request.proof.specification
        )
    } else {
        format!(
            "{header}prelude\nimport Trusted.MirSemantics\nimport Captured\nimport {spec_module}\n\nnamespace Expected\ndef claim : Prop := _root_.Trusted.MirSemantics.{root_name} (_root_.Trusted.MirSemantics.{crate_ctor_ty}.mk _root_.Captured.program _root_.{})\nend Expected\n",
            request.proof.specification
        )
    };
    let expected_path = work.join("generated/Expected.lean");
    write(&expected_path, expected.as_bytes())?;
    modules.push(TargetModule {
        module: "Expected".to_owned(),
        source: expected_path,
        expected_sha256: sha256_bytes(expected.as_bytes()),
        role: TargetRole::Expected,
    });
    let audit_request = TargetAuditRequest {
        modules,
        theorem_module,
        theorem_name: request.proof.theorem.clone(),
        expected_module: "Expected".to_owned(),
        expected_declaration: "Expected.claim".to_owned(),
        canonical_root: format!("Trusted.MirSemantics.{root_name}"),
        subject_declaration: "Captured.program".to_owned(),
        specification_declaration: request.proof.specification.clone(),
        allow_sorry_in_proof: args.allow_sorry_in_proof,
        bindings: TargetBindings {
            request_sha256: request_sha256.clone(),
            capture_sha256: capture_sha256.clone(),
            model_manifest_sha256: model_manifest_sha256.clone(),
            specification_manifest_sha256: specification_manifest_sha256.clone(),
        },
    };
    write(&work.join("audit-request.json"), &encoded(&audit_request)?)?;
    let proof_start = Instant::now();
    // Authored elaboration is not acceptance. The inspector must replay
    // the exact closed root and enforce origin roles before a receipt can
    // report verification success. Operational failures stay distinct from
    // a successfully executed checker rejecting a proof.
    let mut checker = Checker::new(&bundle, tools.lean.as_deref()).map_err(|e| io("audit", e))?;
    checker.set_allow_unpinned_lean(args.allow_unpinned_lean);
    checker.set_sandbox_mode(if args.allow_unsandboxed_elaboration {
        SandboxMode::Unsandboxed
    } else {
        SandboxMode::PreferBwrapOrLandlock
    });
    checker.set_lean_memory_limit_mb(args.lean_memory_mb);
    checker.set_use_olean_cache(!args.no_cache);
    checker.set_no_rebuild_bundled(args.no_rebuild_bundled);
    checker.set_prebuilt_olean_dir(tools.prebuilt_dir);
    checker.set_paranoid_quorum(args.paranoid_quorum);
    let audit_result = checker.run_target_with_progress(&audit_request, |ev| {
        let phase = match ev {
            TargetProgress::Toolchain => VerifyPhase::Toolchain,
            TargetProgress::SpecPreflight { module_count } => {
                VerifyPhase::SpecPreflight { module_count }
            }
            TargetProgress::Elaborate { done, total, cached } => {
                VerifyPhase::Elaborate { done, total, cached }
            }
            TargetProgress::Audit => VerifyPhase::Audit,
        };
        session.report_phase(phase);
    });
    let active_sandbox_opt = checker.active_sandbox();
    let sandbox_label = active_sandbox_opt.map(ActiveSandbox::as_str);
    let audit = match audit_result {
        Ok(audit) => audit,
        Err(e) => {
            return Err(handle_failed_target_audit(
                &checker,
                work,
                args.export_lean_lib,
                sandbox_label,
                e,
            ));
        }
    };
    let Some(active_sandbox) = active_sandbox_opt else {
        return Err(error("tool_failed", "sandbox", "sandbox selection did not complete"));
    };
    if (active_sandbox == ActiveSandbox::None) != args.allow_unsandboxed_elaboration {
        return Err(error(
            "tool_failed",
            "sandbox",
            format!(
                "active sandbox ({}) contradicts --allow-unsandboxed-elaboration={}",
                active_sandbox.as_str(),
                args.allow_unsandboxed_elaboration,
            ),
        )
        .with_sandbox(Some(active_sandbox.as_str())));
    }
    let proof_ms = proof_start.elapsed().as_millis();
    // Snapshot identity is checked again at the accepting boundary. Logical
    // type equality cannot authenticate unused source or configuration hashes.
    for (path, expected) in &originals {
        let (_, actual_sha) = read_input_file(path, Some(path), symlink_policy, "binding")
            .map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?;
        if actual_sha != *expected {
            return Err(error("tool_failed", "binding", "an input changed during verification")
                .with_sandbox(Some(active_sandbox.as_str())));
        }
    }
    let current_capture_canon = fs::canonicalize(&capture_tool_path).map_err(|e| {
        error(
            "tool_failed",
            "binding",
            format!("cannot inspect {}: {e}", capture_tool_path.display()),
        )
        .with_sandbox(Some(active_sandbox.as_str()))
    })?;
    let (_, current_capture_sha) =
        read_regular_file_strict(&current_capture_canon, Some(&current_capture_canon), "binding")
            .map_err(|e| {
            error("tool_failed", "binding", e.message).with_sandbox(Some(active_sandbox.as_str()))
        })?;
    if current_capture_sha != capture_binary_sha256 || current_capture_canon != capture {
        return Err(error(
            "tool_failed",
            "binding",
            "capture executable changed during verification",
        )
        .with_sandbox(Some(active_sandbox.as_str())));
    }
    let candidate_features =
        validate_and_extract_candidate_features(&audit, &model_tiers, &model_modules)
            .map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?;
    let experimental = !candidate_features.is_empty();
    let taints = active_taints(args);
    let taint_reasons = taint_reason_strings(&taints);
    let status = request.scope.verified_status(!taints.is_empty());
    let profile_v2 = manifest.program.mir_profile_version == 2;
    let correspondence_provenance: Value = if args.allow_unpinned_lean {
        json!({
            "applicable": false,
            "reason": format!(
                "unpinned Lean toolchain; bundled Pass 2 correspondence provenance \
                 applies only to pinned {TOOLCHAIN}"
            ),
        })
    } else if profile_v2 {
        // Pass 2 relates only the Profile v1 rules (`initState`/`evalStep`)
        // to `lean-miri`; `Trusted.Correspondence` maps Profile v2-only
        // constructors to fail-closed sentinels, so it certifies nothing
        // about `initStateV2`/`evalStepV2`.
        json!({
            "applicable": false,
            "reason": "bundled Pass 2 correspondence covers Profile v1 semantics \
                       only; Profile v2 execution rules are not certified \
                       against lean-miri",
        })
    } else {
        serde_json::from_str(CORRESPONDENCE_PROVENANCE_JSON).map_err(|e| {
            error(
                "tool_failed",
                "bundle",
                format!("corrupt bundled correspondence provenance: {e}"),
            )
            .with_sandbox(Some(active_sandbox.as_str()))
        })?
    };
    let adm = checker.admitted().map_err(|e| {
        error("tool_failed", "toolchain", e.message).with_sandbox(Some(active_sandbox.as_str()))
    })?;
    let runtime_libs_verified = adm.runtime_libs_verified;
    let has_ndjson_comparator = adm.ndjson_tools.is_some();
    let toolchain_identity = if args.allow_unpinned_lean {
        let mut recorded = vec![
            "capture executable as capture_binary_sha256",
            "unpinned Lean executable and admitted Init/Std sysroot modules in unpinned_lean and audit.unpinnedLean",
        ];
        if has_ndjson_comparator {
            recorded.push(
                "NDJSON comparator and kernel binaries (leanexportSha256, nanodaBinSha256, conRonSha256, and quorum digests when enabled) in audit",
            );
        }
        json!({
            "sha256_locked": [],
            "sha256_recorded": recorded,
            "unhashed": [
                "Lean shared libraries, identified by lean --version",
                "Lean sysroot modules outside the admitted Init/Std closure",
                "Rust compiler and sysroot, identified by their reported commit",
            ],
        })
    } else if runtime_libs_verified {
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "Lean runtime shared libraries in LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean/.ir artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules",
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Rust compiler and sysroot, identified by their reported commit",
            ],
        })
    } else {
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean/.ir artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules",
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Lean shared libraries, identified by lean --version",
                "Rust compiler and sysroot, identified by their reported commit",
            ],
        })
    };
    let lean_assumption = if has_ndjson_comparator {
        // Name the kernels that actually accepted the export: `con-ron` is
        // skipped for `sorryAx` proofs, and `--paranoid-quorum` adds two.
        let kernels: Vec<&str> = audit
            .get("kernelsPassed")
            .and_then(Value::as_array)
            .map(|a| a.iter().filter_map(Value::as_str).collect())
            .unwrap_or_default();
        format!(
            "unpinned Lean exporter, Rust NDJSON comparator, and independent external \
             kernels ({})",
            kernels.join(" / ")
        )
    } else if args.allow_unpinned_lean {
        "unpinned Lean kernel and dynamically discovered Init/Std foundation".to_owned()
    } else {
        "Lean kernel and admitted foundation".to_owned()
    };
    // These assumptions delimit the result, including development builds
    // selected by the operator. Identity hashes make the subject and tool
    // choice reviewable; they do not prove the trusted adapter correct.
    //
    // `toolchain_identity` separates toolchain files whose SHA-256 digests
    // verification compares with the bundled locks from the capture
    // executable, whose digest is only recorded, and from components that
    // verification does not hash. At most a version that the toolchain
    // reports about itself identifies an unhashed component, so its integrity
    // rests on the uncompromised execution environment assumed by
    // THREAT_MODEL.md section 2.1.
    // `ValidEntryArgsV2` quantifies only over entry queries whose reference
    // arguments satisfy `refsValidInMemList` (live, in-bounds, aligned, and
    // initialized pointees that decode to valid values) and are pairwise
    // disjoint when mutable, for safe and `unsafe` functions alike. Rust's
    // language validity invariant is weaker for references passed to an
    // `unsafe fn`, so the receipt states this narrowing explicitly.
    let semantics_assumption = if profile_v2 {
        "experimental Profile v2 MIR semantics: caller memory, single-level \
         references and raw pointers, little-endian byte order, and no \
         aliasing model (Stacked or Tree Borrows); bodies mixing reference \
         and raw-pointer locals are refused, reference validity and \
         mutable-reference disjointness are checked at entry and return, \
         and raw-pointer arguments are assumed to carry provenance that \
         permits the accesses made through them; every reference argument, \
         including those of unsafe functions, is assumed to be non-null and \
         aligned, to lie in bounds of a live allocation whenever it carries \
         provenance (even for zero-sized and empty pointees), to point into \
         a mutable allocation if it is a mutable reference with provenance, \
         to point to initialized bytes that decode to a valid value of the \
         pointee type (a Rust validity rule the Rust Reference calls \
         debated), and to be disjoint from every other mutable reference \
         argument, so results say nothing about calls that pass references \
         to uninitialized, invalid, or dangling memory"
    } else {
        "experimental pointer-free MIR semantics"
    };
    let mut assumptions: Vec<&str> = vec!["faithful pinned compiler capture"];
    // Without a candidate-tier module, the pointer-free semantics carries no
    // `experimental` assumption. Profile v2's entry-validity narrowing bounds
    // what results mean whatever the tier, so it is always recorded.
    if profile_v2 || experimental {
        assumptions.push(semantics_assumption);
    }
    assumptions.push(&lean_assumption);
    assumptions.push("intact compiler and verification environment");
    if !allowed_features.is_empty() {
        assumptions.push(crate::core::inspect::schema::UNSTABLE_FEATURES_ASSUMPTION);
    }
    if request.compilation.panic == PanicStrategy::Abort
        && !manifest.program.has_local_panic_handler
    {
        assumptions.push(
            "--panic abort models failed non-optional safe assertions as .aborted, \
             meaning control entered the panic runtime and never returns to the caller; \
             panic hooks and handlers (including downstream #![no_std] binary \
             #[panic_handler]s) are unverified and may abort or diverge, and only \
             caller-memory effects before the panic are modeled",
        );
    }
    if active_sandbox == ActiveSandbox::LinuxLandlockSeccomp {
        assumptions.push(
            "Tier 2 Landlock + seccomp containment shares host mount and PID namespaces \
             (metadata/symlink existence probing remains visible to the elaborator)",
        );
    }
    let mut deferred: Vec<&str> = Vec::new();
    if active_sandbox == ActiveSandbox::None {
        deferred.push("hostile Lean elaborator effects");
    }
    deferred.push("complete review-surface reporting");
    deferred.push("source-to-deployed-binary correspondence");
    // The NDJSON comparator route does not run `TrustedBoundary.lean`'s
    // anti-vacuity specification lint, so the receipt omits `spec_warnings`
    // and defers the lint instead of reporting an empty (clean-looking) list.
    let ndjson_route = audit.get("auditMode").and_then(Value::as_str) == Some("ndjson_comparator");
    if ndjson_route {
        deferred.push("anti-vacuity specification lint (not run by the NDJSON comparator)");
        // Proof `.olean`s never load outside the sandboxed exporter on this
        // route, so compiler-override attributes on Proof declarations (which
        // cannot change kernel reduction) go uninspected.
        deferred.push(
            "compiler-override attributes on Proof-module declarations (not inspected by the NDJSON comparator)",
        );
    }
    let mut result = json!({
        "schema_version": RECEIPT_SCHEMA_VERSION,
        "status": status,
        "taint_reasons": taint_reasons,
        "elaboration_sandbox": active_sandbox.as_str(),
        "experimental": experimental,
        "candidate_features": candidate_features,
        "request_sha256": request_sha256,
        "capture_sha256": capture_sha256,
        "capture_binary_sha256": capture_binary_sha256,
        "toolchain_identity": toolchain_identity,
        "model_manifest_sha256": model_manifest_sha256,
        "specification_manifest_sha256": specification_manifest_sha256,
        "correspondence_provenance": correspondence_provenance,
        "scope": request.scope, "selected": manifest.selected,
        "census": manifest.census, "sources": sources,
        "configuration": manifest.configuration, "audit": audit,
        "timing_ms": {
            "capture": capture_ms,
            "proof_and_audit": proof_ms,
            "total": start.elapsed().as_millis(),
        },
        "assumptions": assumptions,
        "deferred": deferred
    });
    if args.allow_unpinned_lean {
        let Some(unpinned_lean) = audit.get("unpinnedLean").and_then(Value::as_object) else {
            return Err(error(
                "tool_failed",
                "audit",
                "missing audit.unpinnedLean metadata for unpinned Lean run",
            )
            .with_sandbox(Some(active_sandbox.as_str())));
        };
        let required_field = |key: &str| -> Result<Value> {
            unpinned_lean.get(key).cloned().ok_or_else(|| {
                error(
                    "tool_failed",
                    "audit",
                    format!("missing audit.unpinnedLean.{key} metadata for unpinned Lean run"),
                )
                .with_sandbox(Some(active_sandbox.as_str()))
            })
        };
        result.as_object_mut().unwrap().insert(
            "unpinned_lean".into(),
            json!({
                "expected_toolchain": required_field("expectedToolchain")?,
                "observed_version": required_field("observedVersion")?,
                "lean_binary_sha256": required_field("leanBinarySha256")?,
                "foundation_modules": required_field("foundationModules")?,
                "sysroot_modules_sha256": required_field("sysrootModulesSha256")?,
                "admitted_sysroot_module_count": required_field("admittedSysrootModuleCount")?,
            }),
        );
    }
    if !allowed_features.is_empty() {
        result.as_object_mut().unwrap().insert(
            "unstable_features".into(),
            json!({
                "allowed": allowed_features,
                "observed": unstable_features.observed,
                "incomplete_observed": unstable_features.incomplete_observed,
            }),
        );
    }
    if let Some(sorry_decls) = validate_sorry_declarations(&audit, args.allow_sorry_in_proof)
        .map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?
    {
        result
            .as_object_mut()
            .unwrap()
            .insert("sorry_declarations".into(), Value::Array(sorry_decls));
    }
    if !ndjson_route {
        let spec_warnings = extract_spec_warnings(&audit)
            .map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?;
        result.as_object_mut().unwrap().insert("spec_warnings".into(), Value::Array(spec_warnings));
    }
    if let Some(ref shards) = shards_outcome {
        let obj = result.as_object_mut().unwrap();
        obj.insert("capture_shards_sha256".into(), json!(shards.sha256));
        obj.insert("shards".into(), json!(shards.manifest));
    }
    let result_bytes =
        encoded(&result).map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?;
    finalize_passing_artifacts(work, &result_bytes, args.export_lean_lib, |dest| {
        checker.export_target_oleans_gated(dest, true)
    })
    .map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?;
    Ok(result)
}

/// Write `result.json` before promoting `lean-lib` on a passing run so a
/// `result.json` write failure can never leave a promoted `lean-lib` behind,
/// and remove `result.json` if `lean-lib` export subsequently fails so
/// `tool_failed` leaves neither a success receipt nor a `lean-lib`.
fn finalize_passing_artifacts(
    work: &Path,
    result_bytes: &[u8],
    export_lean_lib: bool,
    export: impl FnOnce(&Path) -> std::result::Result<bool, crate::Failure>,
) -> Result<()> {
    let result_path = work.join("result.json");
    if let Err(mut write_err) = write(&result_path, result_bytes) {
        if fs::symlink_metadata(&result_path).is_ok_and(|m| m.is_file())
            && let Err(unlink_err) = fs::remove_file(&result_path)
        {
            write_err.detail = format!(
                "{}; failed to remove partial {}: {unlink_err}",
                write_err.detail,
                result_path.display()
            );
            write_err = write_err.without_retention();
        }
        return Err(write_err);
    }
    if export_lean_lib {
        // Export authored Proof `.olean`s only after every post-audit
        // integrity, binding, provenance, and taint guard has succeeded.
        if let Err(export_err) = export(&work.join("lean-lib")) {
            return match fs::remove_file(&result_path) {
                Ok(()) => Err(error("tool_failed", "export-lean-lib", export_err.message)),
                Err(unlink_err) => Err(error(
                    "tool_failed",
                    "export-lean-lib",
                    format!(
                        "{}; failed to roll back {}: {unlink_err}",
                        export_err.message,
                        result_path.display()
                    ),
                )
                .without_retention()),
            };
        }
    }
    Ok(())
}

/// Return the bundled `trusted/lean/` model module that `relative` names,
/// with its declared trust tier, or `None` for any other bundle file.
fn bundled_model_tier(relative: &str, text: &str) -> Result<Option<(String, TrustTier)>> {
    if !(relative.ends_with(".lean") && relative.starts_with("trusted/lean/")) {
        return Ok(None);
    }
    let module =
        relative.trim_start_matches("trusted/lean/").trim_end_matches(".lean").replace('/', ".");
    let tier = parse_trusted_tier_directive(&module, text, "bundle")
        .map_err(|e| error("tool_failed", "bundle", e.message))?;
    Ok(Some((module, tier)))
}

/// Apply `verify`'s audit-metadata acceptance checks to a
/// `Checker::run_target` report over the bundled model, as `run` does after
/// the proof phase: `audit.graph` trust tiers (`vetted -/-> candidate:*`),
/// `candidate:*` extraction from `audit.modelClosure`, and the
/// `replay`/`exactType`, axiom, `sorryDeclarations`, and closure checks
/// without `--allow-sorry-in-proof`. Returns the reached `candidate:*`
/// features, or the `status/phase: detail` of the rejection.
#[doc(hidden)]
pub fn check_bundled_model_audit(audit: &Value) -> std::result::Result<Vec<&'static str>, String> {
    let describe = |e: Error| format!("{}/{}: {}", e.status, e.phase, e.detail);
    let mut model_tiers: BTreeMap<String, TrustTier> = BTreeMap::new();
    for (relative, text) in BUNDLE {
        if let Some((module, tier)) = bundled_model_tier(relative, text).map_err(describe)? {
            model_tiers.insert(module, tier);
        }
    }
    let model_modules: BTreeSet<String> = model_tiers.keys().cloned().collect();
    let features = validate_and_extract_candidate_features(audit, &model_tiers, &model_modules)
        .map_err(describe)?;
    validate_sorry_declarations(audit, false).map_err(describe)?;
    Ok(features)
}

/// Validate that bundled `Model` modules respect `vetted -/-> candidate:*`
/// in `audit.graph` and extract the sorted set of `candidate:<feature>` flags
/// reached by declarations in `audit.modelClosure`.
fn validate_and_extract_candidate_features(
    audit: &Value,
    model_tiers: &BTreeMap<String, TrustTier>,
    model_modules: &BTreeSet<String>,
) -> Result<Vec<&'static str>> {
    let graph = audit.get("graph").and_then(Value::as_object).ok_or_else(|| {
        error("tool_failed", "audit", "missing or malformed audit.graph metadata")
    })?;
    for mod_name in model_modules {
        let Some(&tier) = model_tiers.get(mod_name) else {
            return Err(error(
                "tool_failed",
                "bundle",
                format!("missing trust tier for bundled model module {mod_name}"),
            ));
        };
        if tier == TrustTier::Vetted {
            let Some(edges) = graph.get(mod_name).and_then(Value::as_array) else {
                return Err(error(
                    "tool_failed",
                    "audit",
                    format!("missing audit.graph edges for model module {mod_name}"),
                ));
            };
            for edge in edges {
                let Some(dep) = edge.get("module").and_then(Value::as_str) else {
                    return Err(error(
                        "tool_failed",
                        "audit",
                        format!("malformed audit.graph edge for {mod_name}"),
                    ));
                };
                if model_modules.contains(dep) {
                    match model_tiers.get(dep) {
                        Some(TrustTier::Vetted) => {}
                        Some(TrustTier::Candidate(feat)) => {
                            return Err(error(
                                "tool_failed",
                                "audit",
                                format!(
                                    "vetted model module {mod_name} cannot import candidate:{} module {dep}",
                                    feat.as_str()
                                ),
                            ));
                        }
                        None => {
                            return Err(error(
                                "tool_failed",
                                "bundle",
                                format!("missing trust tier for imported model module {dep}"),
                            ));
                        }
                    }
                }
            }
        }
    }
    let closure = audit
        .get("modelClosure")
        .and_then(Value::as_array)
        .ok_or_else(|| error("tool_failed", "audit", "missing audit.modelClosure metadata"))?;
    let mut reached: BTreeSet<&'static str> = BTreeSet::new();
    for entry in closure {
        let Some(module) = entry.get("module").and_then(Value::as_str) else {
            return Err(error("tool_failed", "audit", "malformed entry in audit.modelClosure"));
        };
        if model_modules.contains(module) {
            let Some(&tier) = model_tiers.get(module) else {
                return Err(error(
                    "tool_failed",
                    "bundle",
                    format!("missing trust tier for reached model module {module}"),
                ));
            };
            if let TrustTier::Candidate(feat) = tier {
                reached.insert(feat.as_str());
            }
        }
    }
    Ok(reached.into_iter().collect())
}

/// Validate `audit.sorryDeclarations`, closed `audit.axioms` allowlist,
/// `replay`/`exactType` flags, and non-empty logical closures as
/// defense-in-depth on the final verification receipt. Returns
/// `Ok(Some(decls))` when `--allow-sorry-in-proof` is active, `Ok(None)` when
/// absent on a `sorry`-free proof, and `Err(tool_failed)` on missing,
/// malformed, or inconsistent audit metadata.
fn validate_sorry_declarations(
    audit: &Value,
    allow_sorry_in_proof: bool,
) -> Result<Option<Vec<Value>>> {
    if audit.get("replay").and_then(Value::as_bool) != Some(true)
        || audit.get("exactType").and_then(Value::as_bool) != Some(true)
    {
        return Err(error(
            "tool_failed",
            "audit",
            "audit metadata must certify replay == true and exactType == true",
        ));
    }
    for closure_key in ["subjectClosure", "modelClosure", "specificationClosure"] {
        let Some(rows) = audit.get(closure_key).and_then(Value::as_array) else {
            return Err(error(
                "tool_failed",
                "audit",
                format!("missing audit.{closure_key} metadata"),
            ));
        };
        if rows.is_empty() {
            return Err(error(
                "tool_failed",
                "audit",
                format!("unexpected empty audit.{closure_key} metadata"),
            ));
        }
    }
    let Some(sorry_decls) = audit.get("sorryDeclarations").and_then(Value::as_array) else {
        return Err(error("tool_failed", "audit", "missing audit.sorryDeclarations metadata"));
    };
    if !sorry_decls.iter().all(Value::is_string) {
        return Err(error("tool_failed", "audit", "malformed audit.sorryDeclarations metadata"));
    }
    let Some(axioms) = audit.get("axioms").and_then(Value::as_array) else {
        return Err(error("tool_failed", "audit", "missing audit.axioms metadata"));
    };
    if !axioms.iter().all(Value::is_string) {
        return Err(error("tool_failed", "audit", "malformed audit.axioms metadata"));
    }
    const ALLOWED_AXIOMS: &[&str] = &["Classical.choice", "Quot.sound", "propext"];
    let mut uses_sorry_ax = false;
    for ax in axioms {
        let Some(name) = ax.as_str() else {
            return Err(error("tool_failed", "audit", "malformed audit.axioms metadata"));
        };
        if name == "sorryAx" {
            uses_sorry_ax = true;
        } else if !ALLOWED_AXIOMS.contains(&name) {
            return Err(error(
                "tool_failed",
                "audit",
                format!("unexpected axiom {name} outside closed allowlist in audit.axioms"),
            ));
        }
    }
    if allow_sorry_in_proof {
        if uses_sorry_ax != !sorry_decls.is_empty() {
            return Err(error(
                "tool_failed",
                "audit",
                "inconsistent audit metadata between audit.axioms (sorryAx) and \
                 audit.sorryDeclarations",
            ));
        }
        Ok(Some(sorry_decls.clone()))
    } else {
        if !sorry_decls.is_empty() {
            return Err(error(
                "tool_failed",
                "audit",
                "unexpected non-empty audit.sorryDeclarations without --allow-sorry-in-proof",
            ));
        }
        if uses_sorry_ax {
            return Err(error(
                "tool_failed",
                "audit",
                "unexpected sorryAx in audit.axioms without --allow-sorry-in-proof",
            ));
        }
        Ok(None)
    }
}

/// Extract and validate advisory anti-vacuity warnings from `audit.specWarnings`
/// for Receipt v3 `"spec_warnings"`.
fn extract_spec_warnings(audit: &Value) -> Result<Vec<Value>> {
    let Some(raw) = audit.get("specWarnings") else {
        return Ok(Vec::new());
    };
    let Some(items) = raw.as_array() else {
        return Err(error("tool_failed", "audit", "malformed audit.specWarnings metadata"));
    };
    let mut warnings = Vec::with_capacity(items.len());
    for item in items {
        let Some(obj) = item.as_object() else {
            return Err(error("tool_failed", "audit", "malformed audit.specWarnings entry"));
        };
        let req_str = |key: &str| -> Result<&str> {
            match obj.get(key).and_then(Value::as_str) {
                Some(s) if !s.is_empty() => Ok(s),
                _ => Err(error(
                    "tool_failed",
                    "audit",
                    format!("malformed audit.specWarnings entry field `{key}`"),
                )),
            }
        };
        let code = req_str("code")?;
        let declaration = req_str("declaration")?;
        let message = req_str("message")?;
        let mut entry = json!({
            "code": code,
            "declaration": declaration,
            "message": message,
        });
        if let Some(body_val) = obj.get("body")
            && !body_val.is_null()
        {
            let Some(body) = body_val.as_str().filter(|s| !s.is_empty()) else {
                return Err(error(
                    "tool_failed",
                    "audit",
                    "malformed audit.specWarnings entry field `body`",
                ));
            };
            entry.as_object_mut().unwrap().insert("body".into(), Value::String(body.to_owned()));
        }
        warnings.push(entry);
    }
    Ok(warnings)
}

fn verification_stage() -> std::io::Result<tempfile::TempDir> {
    // Capture canonicalizes source paths before recording its read inventory.
    // Create the stage below a canonical parent so compiler arguments and our
    // inventory keys use that same namespace, even when TMPDIR is a symlink.
    // TempDir owns the resulting physical path and still handles its cleanup.
    let parent = fs::canonicalize(std::env::temp_dir())?;
    let mut builder = tempfile::Builder::new();
    builder.prefix("anneal-verification-");
    // Snapshots contain source and diagnostics that other local users should
    // not read. Set permissions at creation instead of relying on the umask.
    // This is Unix user privacy, not isolation from same-user host access.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        builder.permissions(fs::Permissions::from_mode(0o700));
    }
    builder.tempdir_in(parent)
}

fn handle_failed_target_audit(
    checker: &Checker,
    work: &Path,
    export_lean_lib: bool,
    sandbox_label: Option<&'static str>,
    err: crate::Failure,
) -> Error {
    if export_lean_lib
        && err.code == 1
        && let Err(export_err) = checker.export_target_oleans_gated(&work.join("lean-lib"), false)
    {
        return error("tool_failed", "export-lean-lib", export_err.message)
            .with_sandbox(sandbox_label);
    }
    error(if err.code == 1 { "proof_failed" } else { "tool_failed" }, "audit", err.to_string())
        .with_sandbox(sandbox_label)
}

fn failure_exit_code(status: &str) -> u8 {
    if matches!(status, "unsupported" | "proof_failed") { 1 } else { 2 }
}

#[allow(clippy::too_many_arguments)]
fn emit_failure<Out: std::io::Write, ErrOut: std::io::Write>(
    session: &mut OutputSession<Out, ErrOut>,
    resolved_format: ResolvedVerifyFormat,
    receipt_out: Option<&ValidatedReceiptOut>,
    taint_reasons: &[&str],
    elaboration_sandbox: Option<&str>,
    status: &str,
    phase: &str,
    detail: &str,
    artifacts: Option<Option<&str>>,
    code: u8,
) -> ExitCode {
    let mut final_status = status;
    let mut final_phase = phase;
    let mut final_detail = detail.to_owned();
    let mut final_code = code;
    let mut receipt_display: Option<&str> = None;
    let mut hint = diagnostics::hint_for_failure(final_status, final_phase, &final_detail);

    let mut serialized = serde_json::to_string(&FailureReceipt {
        schema_version: RECEIPT_SCHEMA_VERSION,
        taint_reasons,
        elaboration_sandbox,
        status: final_status,
        phase: final_phase,
        detail: &final_detail,
        hint: hint.as_deref(),
        artifacts,
    })
    .expect("serializable failure receipt");

    if let Some(ro) = receipt_out {
        match write_receipt_out_atomic(ro, &serialized) {
            Ok(()) => {
                receipt_display = Some(ro.display_str.as_str());
            }
            Err(ro_err) => {
                let _ = invalidate_stale_receipt_out(ro);
                final_status = "tool_failed";
                final_phase = "receipt-out";
                final_detail = format!("{final_detail}; {ro_err}");
                final_code = 2;
                hint = diagnostics::hint_for_failure(final_status, final_phase, &final_detail);
                serialized = serde_json::to_string(&FailureReceipt {
                    schema_version: RECEIPT_SCHEMA_VERSION,
                    taint_reasons,
                    elaboration_sandbox,
                    status: final_status,
                    phase: final_phase,
                    detail: &final_detail,
                    hint: hint.as_deref(),
                    artifacts,
                })
                .expect("serializable failure receipt");
            }
        }
    }

    let primary = match resolved_format {
        ResolvedVerifyFormat::Json => format!("{serialized}\n"),
        ResolvedVerifyFormat::Human => render_failure_card(
            &FailureCardInput {
                taint_reasons,
                elaboration_sandbox,
                status: final_status,
                phase: final_phase,
                detail: &final_detail,
                hint: hint.as_deref(),
                artifacts: artifacts.flatten(),
                exit_code: final_code,
            },
            CardRenderOptions {
                ansi_color: session.stdout_style.ansi_color,
                quiet: session.quiet,
                verbose: session.verbose,
                receipt_out_path: receipt_display,
            },
        ),
    };
    finish_with_writers(session, primary.as_bytes(), final_code)
}

pub fn main(args: VerifyArgs, color: ColorChoice, quiet: bool, verbose: bool) -> ExitCode {
    let (mut session, resolved_format) = OutputSession::live(color, quiet, verbose, args.format);
    let taints = active_taints(&args);
    for taint in &taints {
        session.write_taint_banner(taint.warning_banner());
    }
    let taint_vec = taint_reason_strings(&taints);
    let taint_reasons: &[&str] = &taint_vec;
    // Receipts encode the artifact destination as JSON text. Check its exact
    // spelling before staging or retention can create evidence, so an encoding
    // failure cannot leave an export with no receipt. Carry the checked text
    // into retention and reporting; lossy conversion would change its path.
    let artifacts = match args.artifacts.as_deref() {
        Some(path) => match path.to_str() {
            Some(path) => Some(path),
            None => {
                return emit_failure(
                    &mut session,
                    resolved_format,
                    None,
                    taint_reasons,
                    None,
                    "tool_failed",
                    "retention",
                    "artifact destination path must be UTF-8",
                    None,
                    2,
                );
            }
        },
        None => None,
    };
    let receipt_out = match validate_receipt_out_pre_stage(&args, artifacts) {
        Ok(ro) => ro,
        Err(detail) => {
            return emit_failure(
                &mut session,
                resolved_format,
                None,
                taint_reasons,
                None,
                "tool_failed",
                "receipt-out",
                &detail,
                None,
                2,
            );
        }
    };
    let mut overwrite_inputs =
        if args.overwrite_artifacts { overwrite_protected_inputs(&args) } else { Vec::new() };
    // In Cargo mode, any target root (not only the selected one) could sit
    // inside an existing destination. List them before preflight so it
    // refuses such a destination before anything modifies it, and refuse to
    // overwrite at all when the targets cannot be listed.
    if args.overwrite_artifacts
        && args.request.is_none()
        && !matches!(args.command, Some(VerifySubcommand::Rustc(_)))
        && let Some(destination) = artifacts
        && fs::symlink_metadata(destination).is_ok()
    {
        let manifest = args.manifest_path.as_deref().unwrap_or(Path::new("Cargo.toml"));
        match cargo_target_paths(manifest) {
            Ok(paths) => overwrite_inputs.extend(paths),
            Err(failure) => {
                return emit_failure(
                    &mut session,
                    resolved_format,
                    receipt_out.as_ref(),
                    taint_reasons,
                    None,
                    "tool_failed",
                    "retention",
                    &format!(
                        "artifact destination {destination} cannot be overwritten: cannot list \
                         the Cargo targets it might contain: {}",
                        failure.detail
                    ),
                    None,
                    2,
                );
            }
        }
    }
    let existing = match artifacts.map(|destination| {
        preflight_artifact_destination_mode(
            destination,
            args.overwrite_artifacts,
            &overwrite_inputs,
        )
    }) {
        None | Some(Ok(None)) => None,
        Some(Ok(Some(existing))) => Some(existing),
        Some(Err(failure)) => {
            return emit_failure(
                &mut session,
                resolved_format,
                receipt_out.as_ref(),
                taint_reasons,
                None,
                failure.status,
                failure.phase,
                &failure.detail,
                None,
                2,
            );
        }
    };
    // Every preflight check passed. Before running, drop success evidence from
    // the existing directory that `--overwrite-artifacts` may replace, so no
    // outcome of this run can leave an earlier passing receipt in place.
    if let Some(existing) = existing
        && let Err(detail) = existing.invalidate(&overwrite_inputs)
    {
        return emit_failure(
            &mut session,
            resolved_format,
            receipt_out.as_ref(),
            taint_reasons,
            None,
            "tool_failed",
            "retention",
            &detail,
            None,
            2,
        );
    }
    let stage = match verification_stage() {
        Ok(stage) => stage,
        Err(failure) => {
            return emit_failure(
                &mut session,
                resolved_format,
                receipt_out.as_ref(),
                taint_reasons,
                None,
                "tool_failed",
                "staging",
                &failure.to_string(),
                None,
                2,
            );
        }
    };
    // Preserve diagnostic evidence for rejected requests as well as proved
    // ones. Export failure takes precedence over the verification result:
    // the requested evidence operation has not completed successfully.
    let outcome =
        run(&args, stage.path(), receipt_out.as_ref(), &mut session, &mut overwrite_inputs);
    session.finish_phases(outcome.is_ok());
    if let Err(failure) = &outcome
        && failure.suppress_retention
    {
        let code = failure_exit_code(failure.status);
        let ro_ref = if failure.suppress_receipt_out { None } else { receipt_out.as_ref() };
        return emit_failure(
            &mut session,
            resolved_format,
            ro_ref,
            taint_reasons,
            failure.elaboration_sandbox,
            failure.status,
            failure.phase,
            &failure.detail,
            if artifacts.is_some() { None } else { Some(None) },
            code,
        );
    }
    // Stage `--receipt-out` (`0o600` temp file in the canonical parent) before
    // retaining `--artifacts` so an unwritable receipt parent fails closed
    // without publishing passing evidence or `lean-lib/` to `--artifacts`, and
    // only rename the staged receipt into place once retention succeeds. A hard
    // crash during `retain_stage` can leave at most that private `0o600` temp
    // file behind.
    let unretained_artifacts = if artifacts.is_some() { None } else { Some(None) };
    match outcome {
        Ok(mut result) => {
            if let Some(destination) = artifacts {
                result["artifacts"] = json!(destination);
            }
            let pretty_json = serde_json::to_string_pretty(&result).unwrap();
            let staged_receipt = if let Some(ro) = receipt_out.as_ref() {
                match stage_receipt_out_temp(ro, &pretty_json) {
                    Ok(tmp) => Some(tmp),
                    Err(ro_err) => {
                        let _ = invalidate_stale_receipt_out(ro);
                        let sandbox = result.get("elaboration_sandbox").and_then(Value::as_str);
                        return emit_failure(
                            &mut session,
                            resolved_format,
                            None,
                            taint_reasons,
                            sandbox,
                            "tool_failed",
                            "receipt-out",
                            &ro_err,
                            unretained_artifacts,
                            2,
                        );
                    }
                }
            } else {
                None
            };
            // Retention is create-only unless `--overwrite-artifacts` opts in,
            // and even then it replaces only a directory that retention wrote
            // earlier, keeping it aside until the receipt is committed.
            let retained = if let Some(destination) = artifacts {
                match retain_artifacts(
                    args.overwrite_artifacts,
                    stage.path(),
                    Path::new(destination),
                    true,
                    &overwrite_inputs,
                ) {
                    Ok(guard) => Some(guard),
                    Err(failure) => {
                        drop(staged_receipt);
                        let sandbox = result.get("elaboration_sandbox").and_then(Value::as_str);
                        return emit_failure(
                            &mut session,
                            resolved_format,
                            receipt_out.as_ref(),
                            taint_reasons,
                            sandbox,
                            "tool_failed",
                            failure.phase,
                            &failure.detail,
                            None,
                            2,
                        );
                    }
                }
            } else {
                None
            };
            if let (Some(tmp), Some(ro)) = (staged_receipt, receipt_out.as_ref())
                && let Err(ro_err) = commit_receipt_out_temp(tmp, ro)
            {
                let _ = invalidate_stale_receipt_out(ro);
                let sandbox = result.get("elaboration_sandbox").and_then(Value::as_str);
                let detail = match retained {
                    Some(guard) => guard.rollback(ro_err),
                    None => ro_err,
                };
                return emit_failure(
                    &mut session,
                    resolved_format,
                    None,
                    taint_reasons,
                    sandbox,
                    "tool_failed",
                    "receipt-out",
                    &detail,
                    unretained_artifacts,
                    2,
                );
            }
            if let Some(guard) = retained {
                guard.commit();
            }
            if let Some(incomplete) =
                result.pointer("/unstable_features/incomplete_observed").and_then(Value::as_array)
            {
                for feature in incomplete.iter().filter_map(Value::as_str) {
                    session.write_taint_banner(&format!(
                        "WARNING: the crate enables `{feature}`, which rustc marks incomplete \
                         (likely unsound or crash-prone)"
                    ));
                }
            }
            if let Some(warnings) = result.get("spec_warnings").and_then(Value::as_array) {
                for warning in warnings {
                    let code = SanitizedInline::new(
                        warning.get("code").and_then(Value::as_str).unwrap_or("unknown"),
                    );
                    let decl = SanitizedInline::new(
                        warning.get("declaration").and_then(Value::as_str).unwrap_or("<unknown>"),
                    );
                    let body =
                        warning.get("body").and_then(Value::as_str).map(SanitizedInline::new);
                    let msg = SanitizedInline::new(
                        warning.get("message").and_then(Value::as_str).unwrap_or(""),
                    );
                    session.write_spec_warning(&code, &decl, body.as_ref(), &msg);
                }
            }
            let primary = match resolved_format {
                ResolvedVerifyFormat::Json => format!("{pretty_json}\n"),
                ResolvedVerifyFormat::Human => render_success_card(
                    &result,
                    CardRenderOptions {
                        ansi_color: session.stdout_style.ansi_color,
                        quiet: session.quiet,
                        verbose: session.verbose,
                        receipt_out_path: receipt_out.as_ref().map(|r| r.display_str.as_str()),
                    },
                ),
            };
            finish_with_writers(&mut session, primary.as_bytes(), 0)
        }
        Err(failure) => {
            let code = failure_exit_code(failure.status);
            let ro_ref = if failure.suppress_receipt_out { None } else { receipt_out.as_ref() };
            let hint =
                diagnostics::hint_for_failure(failure.status, failure.phase, &failure.detail);
            let serialized = serde_json::to_string(&FailureReceipt {
                schema_version: RECEIPT_SCHEMA_VERSION,
                taint_reasons,
                elaboration_sandbox: failure.elaboration_sandbox,
                status: failure.status,
                phase: failure.phase,
                detail: &failure.detail,
                hint: hint.as_deref(),
                artifacts: Some(artifacts),
            })
            .expect("serializable failure receipt");
            let staged_receipt = if let Some(ro) = ro_ref {
                match stage_receipt_out_temp(ro, &serialized) {
                    Ok(tmp) => Some(tmp),
                    Err(ro_err) => {
                        let _ = invalidate_stale_receipt_out(ro);
                        let detail = format!("{}; {ro_err}", failure.detail);
                        return emit_failure(
                            &mut session,
                            resolved_format,
                            None,
                            taint_reasons,
                            failure.elaboration_sandbox,
                            "tool_failed",
                            "receipt-out",
                            &detail,
                            unretained_artifacts,
                            2,
                        );
                    }
                }
            } else {
                None
            };
            let mut retained_guard = None;
            let retained = if let Some(destination) = artifacts {
                match retain_artifacts(
                    args.overwrite_artifacts,
                    stage.path(),
                    Path::new(destination),
                    false,
                    &overwrite_inputs,
                ) {
                    Ok(guard) => {
                        retained_guard = Some(guard);
                        Some(destination)
                    }
                    Err(ret_failure) => {
                        drop(staged_receipt);
                        return emit_failure(
                            &mut session,
                            resolved_format,
                            ro_ref,
                            taint_reasons,
                            failure.elaboration_sandbox,
                            "tool_failed",
                            ret_failure.phase,
                            &ret_failure.detail,
                            None,
                            2,
                        );
                    }
                }
            } else {
                None
            };
            if let (Some(tmp), Some(ro)) = (staged_receipt, ro_ref)
                && let Err(ro_err) = commit_receipt_out_temp(tmp, ro)
            {
                let _ = invalidate_stale_receipt_out(ro);
                let detail = format!("{}; {ro_err}", failure.detail);
                let detail = match retained_guard {
                    Some(guard) => guard.rollback(detail),
                    None => detail,
                };
                return emit_failure(
                    &mut session,
                    resolved_format,
                    None,
                    taint_reasons,
                    failure.elaboration_sandbox,
                    "tool_failed",
                    "receipt-out",
                    &detail,
                    unretained_artifacts,
                    2,
                );
            }
            if let Some(guard) = retained_guard {
                guard.commit();
            }
            let primary = match resolved_format {
                ResolvedVerifyFormat::Json => format!("{serialized}\n"),
                ResolvedVerifyFormat::Human => render_failure_card(
                    &FailureCardInput {
                        taint_reasons,
                        elaboration_sandbox: failure.elaboration_sandbox,
                        status: failure.status,
                        phase: failure.phase,
                        detail: &failure.detail,
                        hint: hint.as_deref(),
                        artifacts: retained,
                        exit_code: code,
                    },
                    CardRenderOptions {
                        ansi_color: session.stdout_style.ansi_color,
                        quiet: session.quiet,
                        verbose: session.verbose,
                        receipt_out_path: ro_ref.map(|r| r.display_str.as_str()),
                    },
                ),
            };
            finish_with_writers(&mut session, primary.as_bytes(), code)
        }
    }
}

/// Split UTF-8 `destination` into `(entry, name, parent)` after separating a
/// leading `Component::Prefix` of `prefix_len` bytes rather than using
/// `Path::parent`, which drops trailing `.` components that `mkdir` does not.
fn split_artifact_destination_with_prefix_len(
    destination: &str,
    prefix_len: usize,
    is_separator: fn(char) -> bool,
) -> (&str, &str, String) {
    let (win_prefix, rest) = destination.split_at(prefix_len);
    let trimmed_rest = rest.trim_end_matches(is_separator);
    // A trailing separator makes `lstat` follow a final symlink, which would
    // hide a dangling one that `mkdir` still refuses. Inspect the final entry
    // without trailing separators while preserving root separators and Windows
    // prefixes (`/` or `C:\`).
    let entry = if trimmed_rest.is_empty() {
        destination
    } else {
        &destination[..prefix_len + trimmed_rest.len()]
    };
    if trimmed_rest.is_empty() {
        return (entry, "", String::new());
    }
    let name_start = trimmed_rest.rfind(is_separator).map_or(0, |separator| separator + 1);
    let name = &trimmed_rest[name_start..];
    let rest_prefix = &trimmed_rest[..name_start];
    let trimmed_parent = rest_prefix.trim_end_matches(is_separator);
    let parent = if rest_prefix.is_empty() {
        if win_prefix.is_empty() { ".".to_owned() } else { format!("{win_prefix}.") }
    } else if trimmed_parent.is_empty() {
        // Every separator before the name belongs to a root directory
        // (`/`, `C:\`, `\\?\C:\`, `\\server\share\`).
        format!("{win_prefix}{}", &rest_prefix[..1])
    } else {
        format!("{win_prefix}{trimmed_parent}")
    };
    (entry, name, parent)
}

/// Reject an artifact destination that retention could not claim.
///
/// Retention claims its destination with a create-only `mkdir`, which fails
/// when any entry (including a dangling symlink) occupies the final path
/// component, when that component is `.` or `..`, or when the parent is missing
/// or not a directory. Checking those conditions before staging reports a
/// reused or mistyped path immediately, instead of after capture and Lean
/// elaboration have run for evidence that cannot be kept. Write permission on
/// the parent directory is not checked (`retain_stage` reports it), while any
/// other error inspecting the destination path (such as search permission,
/// symlink loops, or overlong names) is reported up front with the OS error.
/// The filesystem may also change before retention, so this check is advisory
/// only: `retain_stage` remains the authoritative, race-free claim and still
/// refuses to write into any path that exists by then.
///
/// `destination` is the UTF-8 spelling already checked by `main`.
#[cfg(test)]
fn preflight_artifact_destination(destination: &str) -> Result<()> {
    preflight_artifact_destination_mode(destination, false, &[]).map(|_| ())
}

/// An existing artifact directory that preflight admitted for
/// `--overwrite-artifacts`, identified so that a later step can tell whether
/// the path still names the same directory.
#[derive(Debug)]
struct ExistingArtifactDir {
    /// The destination with trailing separators stripped, so no use of it
    /// follows a final symlink.
    entry: PathBuf,
    canonical: PathBuf,
    #[cfg(unix)]
    id: (u64, u64),
}

impl ExistingArtifactDir {
    fn new(entry: &str) -> std::result::Result<Self, String> {
        let entry = PathBuf::from(entry);
        let canonical = fs::canonicalize(&entry).map_err(|e| e.to_string())?;
        #[cfg(unix)]
        let id = {
            use std::os::unix::fs::MetadataExt as _;
            let meta = fs::symlink_metadata(&entry).map_err(|e| e.to_string())?;
            (meta.dev(), meta.ino())
        };
        Ok(Self {
            entry,
            canonical,
            #[cfg(unix)]
            id,
        })
    }

    /// Re-check that `entry` is still the directory preflight admitted, then
    /// remove its success evidence with [`invalidate_success_evidence`].
    fn invalidate(&self, inputs: &[PathBuf]) -> std::result::Result<(), String> {
        let changed = || {
            format!(
                "artifact destination {} changed after it was checked; refusing to \
                 modify it",
                self.entry.display()
            )
        };
        let meta = fs::symlink_metadata(&self.entry).map_err(|_| changed())?;
        if meta.file_type().is_symlink() || !meta.is_dir() {
            return Err(changed());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            if (meta.dev(), meta.ino()) != self.id {
                return Err(changed());
            }
        }
        if fs::canonicalize(&self.entry).ok().as_deref() != Some(self.canonical.as_path()) {
            return Err(changed());
        }
        let cwd = std::env::current_dir()
            .map_err(|e| format!("cannot determine the working directory: {e}"))?;
        check_replaceable_artifacts_protecting(&self.entry, &cwd, inputs).map_err(|reason| {
            format!("artifact destination {} cannot be overwritten: {reason}", self.entry.display())
        })?;
        invalidate_success_evidence(&self.entry)
    }
}

/// Run [`preflight_artifact_destination`]'s checks, but when `overwrite` is
/// set, also admit an existing destination that [`check_replaceable_artifacts`]
/// accepts, and return it.
fn preflight_artifact_destination_mode(
    destination: &str,
    overwrite: bool,
    inputs: &[PathBuf],
) -> Result<Option<ExistingArtifactDir>> {
    use std::path::Component;

    let reject = |detail: String| Err(error("tool_failed", "retention", detail));
    if destination.is_empty() {
        return reject("artifact destination path is empty".to_owned());
    }
    let prefix_len = match Path::new(destination).components().next() {
        Some(Component::Prefix(prefix)) => prefix.as_os_str().as_encoded_bytes().len(),
        _ => 0,
    };
    let (entry, name, parent) = split_artifact_destination_with_prefix_len(
        destination,
        prefix_len,
        std::path::is_separator,
    );
    match fs::symlink_metadata(entry) {
        Ok(_) if overwrite => {
            if name.is_empty() || matches!(name, "." | "..") {
                return reject(format!(
                    "artifact destination {destination} must end in a directory name"
                ));
            }
            let checked = std::env::current_dir()
                .map_err(|e| format!("cannot determine the working directory: {e}"))
                .and_then(|cwd| {
                    check_replaceable_artifacts_protecting(Path::new(entry), &cwd, inputs)
                });
            return checked.and_then(|()| ExistingArtifactDir::new(entry)).map(Some).or_else(
                |reason| {
                    reject(format!(
                        "artifact destination {destination} cannot be overwritten: {reason}"
                    ))
                },
            );
        }
        Ok(_) => {
            return reject(format!(
                "artifact destination {destination} already exists; retention never \
                 writes into an existing path, so pass a new path (or pass \
                 --overwrite-artifacts to replace earlier artifacts)"
            ));
        }
        // `ENOTDIR` means some ancestor is not a directory; the parent check
        // below reports the immediate parent path (`is not a directory` or the
        // OS `ENOTDIR` error).
        Err(e)
            if matches!(
                e.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::NotADirectory
            ) => {}
        Err(e) => return reject(format!("artifact destination {destination}: {e}")),
    }
    if name.is_empty() || matches!(name, "." | "..") {
        return reject(format!(
            "artifact destination {destination} must end in a new directory name"
        ));
    }
    // Follow symlinks here, as `mkdir` does for every component except the
    // last: the invoker chooses the parent, and symlinked ancestors such as a
    // symlinked temporary directory are ordinary and already accepted.
    match fs::metadata(&parent) {
        Ok(metadata) if metadata.is_dir() => Ok(None),
        Ok(_) => reject(format!("artifact destination parent {parent} is not a directory")),
        Err(e) => reject(format!("artifact destination parent {parent}: {e}")),
    }
}

fn run_shard_plan(args: &ShardPlanArgs, work: &Path) -> Result<ShardPlan> {
    let (compilation, scope, base, symlink_policy) = if let Some(path) = &args.request {
        let canon = fs::canonicalize(path).map_err(|e| io("request", e))?;
        let (bytes, _) = read_regular_file_deref(&canon, "request")
            .map_err(|e| error("tool_failed", "request", e.message))?;
        let request: Request =
            serde_json::from_slice(&bytes).map_err(|e| error("unsupported", "request", e))?;
        if request.schema_version != 1 {
            return Err(error("unsupported", "request", "unsupported compilation request version"));
        }
        (
            request.compilation,
            request.scope,
            canon.parent().unwrap().to_path_buf(),
            SymlinkPolicy::Reject,
        )
    } else {
        let (compilation, scope, base) = cargo_compilation(
            args.manifest_path.as_ref().unwrap(),
            args.panic,
            args.overflow_checks,
            &args.select,
            &args.instantiate,
            &args.features,
            args.all_features,
            args.no_default_features,
            None,
        )?;
        (compilation, scope, base, SymlinkPolicy::Reject)
    };
    if compilation.source_files.is_empty() {
        return Err(error("unsupported", "request", "empty compilation source list"));
    }
    if compilation.stdlib_crate.is_some() && !matches!(scope, Scope::SelectedUnit { .. }) {
        return Err(error(
            "unsupported",
            "request",
            "--stdlib-crate requires selected scope (`--select` or `--instantiate`)",
        ));
    }
    for (key, value) in &compilation.env {
        validate_env_binding(key, value).map_err(|msg| error("unsupported", "request", msg))?;
    }
    let mut originals = Vec::new();
    let rust_stage = work.join("rust");
    let sources = stage_request_rust_inputs(
        &compilation,
        &base,
        &rust_stage,
        symlink_policy,
        &mut originals,
    )?;
    let tools = select_tools_with(args.capture.as_deref(), args.sysroot.as_deref(), None, false)?;
    let shard_config = ShardConfig::from(&args.shard);
    let capture_dir = work.join("capture");
    let outcome = run_capture_process(
        &tools,
        &compilation,
        &scope,
        &sources,
        &rust_stage,
        &capture_dir,
        work,
        shard_config,
        None,
        &[],
        |stderr| eprint!("{}", String::from_utf8_lossy(stderr)),
    )?;
    for (path, expected) in &originals {
        let (_, actual_sha) = read_input_file(path, Some(path), symlink_policy, "binding")?;
        if actual_sha != *expected {
            return Err(error("tool_failed", "binding", "an input changed during verification"));
        }
    }
    let plan = match outcome.shards {
        Some(shards) => ShardPlan::from_sharded(&shards.manifest, shard_config),
        None => ShardPlan::from_unsharded(
            scope.shard_label(),
            outcome.manifest.program.bodies.len(),
            shard_config,
        ),
    };
    if let Some(check_path) = &args.check {
        let canon = fs::canonicalize(check_path).map_err(|e| io("shard-plan", e))?;
        let (expected_bytes, _) = read_regular_file_deref(&canon, "shard-plan")
            .map_err(|e| error("tool_failed", "shard-plan", e.message))?;
        let expected: ShardPlan = serde_json::from_slice(&expected_bytes)
            .map_err(|e| error("unsupported", "shard-plan", format!("invalid shard plan: {e}")))?;
        compare_shard_plan(&expected, &plan)
            .map_err(|msg| error("unsupported", "shard-plan", msg))?;
    }
    if let Some(write_path) = &args.write {
        match fs::symlink_metadata(write_path) {
            Err(e) if e.kind() == IoErrorKind::NotFound => {}
            Err(e) => return Err(io("shard-plan", e)),
            Ok(meta) => {
                if !meta.file_type().is_file() {
                    return Err(error(
                        "tool_failed",
                        "shard-plan",
                        format!("{} exists and is not a regular file", write_path.display()),
                    ));
                }
            }
        }
        if let Some(parent) = write_path.parent()
            && !parent.as_os_str().is_empty()
        {
            fs::create_dir_all(parent).map_err(|e| io("shard-plan", e))?;
        }
        let encoded_plan =
            plan.to_pretty_json().map_err(|msg| error("tool_failed", "shard-plan", msg))?;
        let parent = match write_path.parent() {
            Some(p) if !p.as_os_str().is_empty() => p,
            _ => Path::new("."),
        };
        let mut tmp = tempfile::NamedTempFile::new_in(parent).map_err(|e| io("shard-plan", e))?;
        std::io::Write::write_all(&mut tmp, &encoded_plan).map_err(|e| io("shard-plan", e))?;
        tmp.persist(write_path).map_err(|e| io("shard-plan", e.error))?;
        eprintln!(
            "wrote shard plan ({} shards, {} bodies) to {}",
            plan.total_shards,
            plan.total_bodies,
            write_path.display()
        );
    }
    Ok(plan)
}

pub fn main_shard_plan(args: ShardPlanArgs) -> ExitCode {
    let stage = match verification_stage() {
        Ok(stage) => stage,
        Err(failure) => {
            eprintln!("shard-plan staging failed: {failure}");
            return ExitCode::from(2);
        }
    };
    match run_shard_plan(&args, stage.path()) {
        Ok(plan) => {
            println!("{}", serde_json::to_string_pretty(&plan).expect("serializable shard plan"));
            ExitCode::SUCCESS
        }
        Err(failure) => {
            eprintln!("shard-plan failed ({}): {}", failure.phase, failure.detail);
            ExitCode::from(failure_exit_code(failure.status))
        }
    }
}

/// Copy diagnostics into a destination owned by this export.
///
/// Existing destinations are never changed. A failed copy removes the newly
/// created directory; a cleanup failure identifies possibly incomplete output.
/// Callers report success only after every file has been copied.
#[cfg(test)]
fn retain(source: &Path, destination: &Path) -> Result<()> {
    retain_stage(source, destination, true)
}

fn retain_stage(source: &Path, destination: &Path, allow_success_receipt: bool) -> Result<()> {
    // Exported evidence contains the same private inputs as the stage. Set
    // the Unix mode at creation so no permissive chmod window exposes them.
    let directory = fs::DirBuilder::new();
    #[cfg(unix)]
    let directory = {
        use std::os::unix::fs::DirBuilderExt;
        let mut directory = directory;
        directory.mode(0o700);
        directory
    };
    // Acquire ownership with create-only admission before entering any
    // cleanup path. A caller's existing directory must never be deleted
    // merely because retention failed to claim its requested destination.
    directory.create(destination).map_err(|e| io("retention", e))?;
    if let Err(failure) = copy_artifacts(source, destination, allow_success_receipt) {
        // The destination belongs to this export, so a failed copy can be
        // removed without leaving a path that blocks retry. If removal
        // fails too, report possible partial output rather than claiming
        // either a complete export or a clean filesystem rollback.
        if let Err(cleanup) = fs::remove_dir_all(destination) {
            return Err(error(
                "tool_failed",
                "retention",
                format!(
                    "{}; incomplete artifacts may remain at {} (cleanup failed: {cleanup})",
                    failure.detail,
                    destination.display()
                ),
            ));
        }
        return Err(failure);
    }
    Ok(())
}

/// Names the marker file that retention writes into every artifact
/// directory it creates, so `--overwrite-artifacts` can recognize one.
const ARTIFACT_MARKER: &str = ".cargo-anneal-artifacts";

/// Holds the exact contents of [`ARTIFACT_MARKER`].
const ARTIFACT_MARKER_TEXT: &str = "cargo-anneal verification artifacts\n";

/// Names every top-level entry that an artifact directory can contain, and
/// whether that entry is a directory (`true`) or a regular file (`false`).
///
/// `--overwrite-artifacts` replaces an existing directory only when each of
/// its entries matches one of these names and kinds, so a mistyped path
/// cannot delete unrelated data. Extend this list whenever `run` stages a new
/// top-level entry.
const ARTIFACT_ENTRIES: &[(&str, bool)] = &[
    (ARTIFACT_MARKER, false),
    ("anneal", true),
    ("audit-request.json", false),
    ("authored", true),
    ("capture", true),
    ("capture.stderr", false),
    ("capture.stdout", false),
    ("expected-shard-plan.json", false),
    ("generated", true),
    ("lean-lib", true),
    ("request.json", false),
    ("result.json", false),
    ("rust", true),
];

/// Check that `path` is an artifact directory that retention may replace.
///
/// `path` must be a real directory (not a symlink) that does not contain
/// `cwd`. Each top-level entry must be a non-symlink regular file or
/// directory whose name and kind appear in [`ARTIFACT_ENTRIES`], and a
/// non-empty directory must carry the exact [`ARTIFACT_MARKER`] file. The
/// names alone are too generic (`rust`, `anneal`) to prove that retention
/// created the directory.
#[cfg(test)]
fn check_replaceable_artifacts(path: &Path, cwd: &Path) -> std::result::Result<(), String> {
    check_replaceable_artifacts_protecting(path, cwd, &[])
}

/// Resolve `path` against `cwd` and canonicalize it, or, when it does not
/// exist, its nearest existing ancestor.
fn canonical_or_existing_ancestor(path: &Path, cwd: &Path) -> Option<PathBuf> {
    let absolute = if path.is_absolute() { path.to_path_buf() } else { cwd.join(path) };
    absolute.ancestors().find_map(|candidate| fs::canonicalize(candidate).ok())
}

/// Run [`check_replaceable_artifacts`], and also refuse a directory that
/// contains (or is) any verification input in `inputs`, so replacing it can
/// never delete the caller's own request, sources, proofs, or tools.
fn check_replaceable_artifacts_protecting(
    path: &Path,
    cwd: &Path,
    inputs: &[PathBuf],
) -> std::result::Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if meta.file_type().is_symlink() {
        return Err("it is a symlink".to_owned());
    }
    if !meta.is_dir() {
        return Err("it is not a directory".to_owned());
    }
    // Replacing a directory that contains the working directory (such as
    // `.` spelled another way, or an ancestor) would delete the caller's
    // own tree. Fail closed when containment cannot be decided.
    let unverifiable = |e: std::io::Error| {
        format!("cannot verify that it does not contain the working directory: {e}")
    };
    let canonical = fs::canonicalize(path).map_err(unverifiable)?;
    let canonical_cwd = fs::canonicalize(cwd).map_err(unverifiable)?;
    if canonical_cwd.starts_with(&canonical) {
        return Err("it contains the working directory".to_owned());
    }
    for input in inputs {
        if canonical_or_existing_ancestor(input, &canonical_cwd)
            .is_some_and(|canonical_input| canonical_input.starts_with(&canonical))
        {
            return Err(format!("it contains verification input {}", input.display()));
        }
    }
    let mut empty = true;
    for entry in fs::read_dir(path).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        empty = false;
        let name = entry.file_name();
        let shown = Path::new(&name).display().to_string();
        // `DirEntry::file_type` does not follow symlinks.
        let kind = entry.file_type().map_err(|e| e.to_string())?;
        let expected_dir = name
            .to_str()
            .and_then(|name| ARTIFACT_ENTRIES.iter().find(|(known, _)| *known == name))
            .map(|(_, is_dir)| *is_dir)
            .ok_or_else(|| format!("it contains {shown}, which cargo-anneal does not produce"))?;
        let matches = if expected_dir { kind.is_dir() } else { kind.is_file() };
        if kind.is_symlink() || !matches {
            return Err(format!(
                "it contains {shown} as a {}, which cargo-anneal does not produce",
                if kind.is_symlink() { "symlink" } else { "different file type" }
            ));
        }
    }
    if !empty {
        match read_marker_no_follow(&path.join(ARTIFACT_MARKER)) {
            Ok(text) if text == ARTIFACT_MARKER_TEXT.as_bytes() => {}
            _ => {
                return Err(format!(
                    "it lacks the {ARTIFACT_MARKER} marker that cargo-anneal writes"
                ));
            }
        }
    }
    Ok(())
}

/// Read at most one byte more than [`ARTIFACT_MARKER_TEXT`] from a regular
/// marker file, refusing to follow a symlink.
fn read_marker_no_follow(path: &Path) -> std::io::Result<Vec<u8>> {
    use std::io::Read as _;
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = opts.open(path)?;
    if !file.metadata()?.is_file() {
        return Err(std::io::Error::other("marker is not a regular file"));
    }
    let mut text = Vec::new();
    file.take(ARTIFACT_MARKER_TEXT.len() as u64 + 1).read_to_end(&mut text)?;
    Ok(text)
}

/// Remove success evidence (`result.json` and `lean-lib/`) from an existing
/// artifact directory, so a failed `--overwrite-artifacts` run can never
/// leave or restore an earlier passing receipt beside new failure evidence.
/// The marker stays, so the directory remains replaceable.
fn invalidate_success_evidence(dir: &Path) -> std::result::Result<(), String> {
    let result = dir.join("result.json");
    match fs::symlink_metadata(&result) {
        Ok(meta) if meta.is_file() => fs::remove_file(&result)
            .map_err(|e| format!("cannot remove earlier {}: {e}", result.display()))?,
        Ok(_) => return Err(format!("{} is not a regular file", result.display())),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(format!("cannot inspect {}: {e}", result.display())),
    }
    let lean_lib = dir.join("lean-lib");
    match fs::symlink_metadata(&lean_lib) {
        Ok(meta) if meta.is_dir() => fs::remove_dir_all(&lean_lib)
            .map_err(|e| format!("cannot remove earlier {}: {e}", lean_lib.display()))?,
        Ok(_) => return Err(format!("{} is not a directory", lean_lib.display())),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(format!("cannot inspect {}: {e}", lean_lib.display())),
    }
    Ok(())
}

/// Collect the verification inputs named on the command line (and, best
/// effort, those a readable `--request` declares) that
/// `--overwrite-artifacts` must never delete.
fn overwrite_protected_inputs(args: &VerifyArgs) -> Vec<PathBuf> {
    let mut inputs: Vec<PathBuf> = [
        args.request.as_deref(),
        args.proof_dir.as_deref(),
        args.manifest_path.as_deref(),
        args.verify_shard_plan.as_deref(),
        args.capture.as_deref(),
        args.sysroot.as_deref(),
        args.lean.as_deref(),
    ]
    .into_iter()
    .flatten()
    .map(Path::to_path_buf)
    .collect();
    // Also protect the tools that `run` will discover rather than receive,
    // and the running executable.
    if let Ok(tools) = select_tools(args) {
        inputs.push(tools.capture);
        inputs.extend(tools.sysroot);
        inputs.extend(tools.lean);
        inputs.extend(tools.prebuilt_dir);
    }
    inputs.extend(std::env::current_exe().ok());
    if args.request.is_none()
        && args.manifest_path.is_none()
        && !matches!(args.command, Some(VerifySubcommand::Rustc(_)))
    {
        inputs.push(PathBuf::from("Cargo.toml"));
    }
    if let Some(VerifySubcommand::Rustc(rustc)) = &args.command {
        inputs.push(rustc.crate_root.clone());
        inputs.extend(rustc.source_file.iter().cloned());
        inputs.extend(rustc.spec_file.iter().map(|spec| spec.path.clone()));
        inputs.extend(rustc.proof_file.iter().map(|proof| proof.path.clone()));
    }
    // Read the request as `load_request` does: one that cannot be read or
    // parsed here fails there too, before it can name any input.
    if let Some(req) = args.request.as_deref()
        && let Ok(canon_req) = fs::canonicalize(req)
        && let Ok((bytes, _)) = read_regular_file_deref(&canon_req, "request")
        && let Ok(request) = serde_json::from_slice::<Request>(&bytes)
    {
        inputs.extend(request_input_paths(receipt_parent(&canon_req), &request));
    }
    inputs
}

/// List the source roots and declared files that `request` reads, resolved
/// against `base` the way [`load_request`] resolves them.
fn request_input_paths(base: &Path, request: &Request) -> Vec<PathBuf> {
    let resolve_dir = |raw_dir: &Path| -> PathBuf {
        root(base, raw_dir).unwrap_or_else(|_| {
            if raw_dir.is_absolute() { raw_dir.to_path_buf() } else { base.join(raw_dir) }
        })
    };
    let source_root = resolve_dir(&request.compilation.source_root);
    let proof_root = resolve_dir(&request.proof.source_root);
    let crate_root = &request.compilation.crate_root;
    let mut inputs = vec![
        source_root.clone(),
        proof_root.clone(),
        declared_file(&source_root, crate_root).unwrap_or_else(|_| source_root.join(crate_root)),
    ];
    for relative in &request.compilation.source_files {
        inputs.push(
            declared_file(&source_root, relative).unwrap_or_else(|_| source_root.join(relative)),
        );
    }
    for input in &request.proof.sources {
        inputs.push(
            declared_file(&proof_root, &input.path)
                .unwrap_or_else(|_| proof_root.join(&input.path)),
        );
    }
    inputs
}

/// Refuse, before any evidence is retained, an `--overwrite-artifacts`
/// destination that contains a verification input discovered while staging,
/// and add those inputs to `protected` so retention checks them again.
fn reject_overwrite_input_aliasing(
    args: &VerifyArgs,
    protected: &mut Vec<PathBuf>,
    inputs: impl IntoIterator<Item = PathBuf>,
) -> Result<()> {
    let Some(destination) = args.artifacts.as_deref().filter(|_| args.overwrite_artifacts) else {
        return Ok(());
    };
    let start = protected.len();
    protected.extend(inputs);
    let Ok(canonical) = fs::canonicalize(destination) else {
        // A destination that does not exist yet holds nothing to delete.
        return Ok(());
    };
    let cwd = std::env::current_dir().map_err(|e| io("retention", e))?;
    for input in &protected[start..] {
        if canonical_or_existing_ancestor(input, &cwd)
            .is_some_and(|canonical_input| canonical_input.starts_with(&canonical))
        {
            return Err(error(
                "tool_failed",
                "retention",
                format!(
                    "artifact destination {} cannot be overwritten: it contains verification \
                     input {}",
                    destination.display(),
                    input.display()
                ),
            )
            .without_retention());
        }
    }
    Ok(())
}

/// Replace an existing artifact directory at `destination` with a copy of
/// `source`, or create it as [`retain_stage`] does when it is absent.
///
/// The new artifacts are first copied into a private sibling directory. Only
/// after that copy succeeds, and `destination` is re-checked with
/// [`check_replaceable_artifacts`], is the old directory renamed aside. The
/// moved directory is checked again before the new one is renamed into place
/// and the old one removed, so a destination swapped in after the first check
/// is restored rather than deleted. Any failure before the swap leaves
/// `destination` untouched.
fn replace_stage(
    source: &Path,
    destination: &Path,
    allow_success_receipt: bool,
    inputs: &[PathBuf],
) -> Result<RetainedArtifacts> {
    use std::path::Component;

    let fail = |detail: String| error("tool_failed", "retention", detail);
    let spelled = destination
        .to_str()
        .ok_or_else(|| fail("artifact destination path must be UTF-8".to_owned()))?;
    let prefix_len = match destination.components().next() {
        Some(Component::Prefix(prefix)) => prefix.as_os_str().as_encoded_bytes().len(),
        _ => 0,
    };
    // Strip trailing separators first, so no check or rename below follows a
    // final symlink (including a dangling `link/`).
    let (entry, name, parent) =
        split_artifact_destination_with_prefix_len(spelled, prefix_len, std::path::is_separator);
    match fs::symlink_metadata(entry) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            retain_stage(source, destination, allow_success_receipt)?;
            return Ok(RetainedArtifacts {
                destination: destination.to_path_buf(),
                previous: None,
            });
        }
        Err(e) => return Err(io("retention", e)),
        Ok(_) => {}
    }
    if name.is_empty() || matches!(name, "." | "..") {
        return Err(fail(format!("artifact destination {spelled} must end in a directory name")));
    }
    let destination = Path::new(entry);
    let parent = Path::new(&parent);
    let cannot_overwrite = |reason: String| {
        fail(format!("artifact destination {spelled} cannot be overwritten: {reason}"))
    };
    let cwd = std::env::current_dir()
        .map_err(|e| cannot_overwrite(format!("cannot determine the working directory: {e}")))?;
    let mut builder = tempfile::Builder::new();
    let new_prefix = format!(".{name}.anneal-new-");
    builder.prefix(&new_prefix);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        builder.permissions(fs::Permissions::from_mode(0o700));
    }
    // Dropping `staged` on any early return removes the partial copy.
    let staged = builder.tempdir_in(parent).map_err(|e| io("retention", e))?;
    copy_artifacts(source, staged.path(), allow_success_receipt)?;
    // The destination may have changed since preflight.
    check_replaceable_artifacts_protecting(destination, &cwd, inputs).map_err(cannot_overwrite)?;
    let suffix = staged
        .path()
        .file_name()
        .and_then(OsStr::to_str)
        .and_then(|staged_name| staged_name.strip_prefix(&new_prefix))
        .ok_or_else(|| fail("unexpected staging directory name".to_owned()))?;
    let old = parent.join(format!(".{name}.anneal-old-{suffix}"));
    match fs::symlink_metadata(&old) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Ok(_) => return Err(fail(format!("{} already exists", old.display()))),
        Err(e) => return Err(io("retention", e)),
    }
    fs::rename(destination, &old).map_err(|e| io("retention", e))?;
    // Re-check what was actually moved aside before deleting anything, in
    // case the destination was swapped after the check above.
    if let Err(reason) = check_replaceable_artifacts_protecting(&old, &cwd, inputs) {
        return Err(match fs::rename(&old, destination) {
            Ok(()) => cannot_overwrite(reason),
            Err(restore) => fail(format!(
                "artifact destination {spelled} cannot be overwritten: {reason}; it \
                 remains at {} (restore failed: {restore})",
                old.display()
            )),
        });
    }
    let staged = staged.keep();
    if let Err(e) = fs::rename(&staged, destination) {
        let restored = restore_invalidated(&old, destination);
        let _ = fs::remove_dir_all(&staged);
        return Err(fail(match restored {
            Ok(()) => format!("cannot replace {spelled}: {e}"),
            Err(why) => format!(
                "cannot replace {spelled}: {e}; earlier artifacts remain at {} ({why})",
                old.display()
            ),
        }));
    }
    Ok(RetainedArtifacts { destination: destination.to_path_buf(), previous: Some(old) })
}

/// Records an artifact directory that retention just wrote.
///
/// When it replaced an earlier artifact directory, that directory waits aside
/// at `previous` until the run either commits (removing it) or rolls back
/// (restoring it), so a later failure such as a `--receipt-out` error never
/// loses the earlier artifacts.
#[derive(Debug)]
#[must_use]
struct RetainedArtifacts {
    destination: PathBuf,
    previous: Option<PathBuf>,
}

impl RetainedArtifacts {
    /// Keep the new artifacts and remove any earlier directory set aside.
    fn commit(self) {
        if let Some(old) = self.previous
            && let Err(e) = fs::remove_dir_all(&old)
        {
            eprintln!("warning: cannot remove earlier artifacts at {}: {e}", old.display());
        }
    }

    /// Remove the new artifacts and restore any earlier directory, appending
    /// any cleanup failure to `detail`.
    fn rollback(self, detail: String) -> String {
        let mut detail = rollback_retained_artifacts(self.destination.to_str(), detail);
        if let Some(old) = self.previous {
            let restored = if fs::symlink_metadata(&self.destination).is_ok() {
                Err("restore failed: new artifacts could not be removed".to_owned())
            } else {
                restore_invalidated(&old, &self.destination)
            };
            if let Err(why) = restored {
                detail = format!("{detail}; earlier artifacts remain at {} ({why})", old.display());
            }
        }
        detail
    }
}

/// Move an earlier artifact directory set aside at `old` back to
/// `destination`, but only after removing its success evidence: the run
/// failed, so it must never bring back an earlier passing receipt.
fn restore_invalidated(old: &Path, destination: &Path) -> std::result::Result<(), String> {
    invalidate_success_evidence(old).map_err(|reason| format!("invalidation failed: {reason}"))?;
    fs::rename(old, destination).map_err(|e| format!("restore failed: {e}"))
}

/// Retain `source` at `destination`: create-only by default, or through
/// [`replace_stage`] when `overwrite` is set.
fn retain_artifacts(
    overwrite: bool,
    source: &Path,
    destination: &Path,
    allow_success_receipt: bool,
    inputs: &[PathBuf],
) -> Result<RetainedArtifacts> {
    if overwrite {
        return replace_stage(source, destination, allow_success_receipt, inputs);
    }
    retain_stage(source, destination, allow_success_receipt)?;
    Ok(RetainedArtifacts { destination: destination.to_path_buf(), previous: None })
}

fn copy_artifacts(source: &Path, destination: &Path, allow_success_receipt: bool) -> Result<()> {
    for entry in walkdir::WalkDir::new(source).min_depth(1).follow_links(false) {
        let entry = entry.map_err(|e| error("tool_failed", "retention", e))?;
        let relative = entry.path().strip_prefix(source).unwrap();
        if entry.file_type().is_symlink() {
            return Err(error("tool_failed", "retention", "unexpected staging symlink"));
        }
        if !allow_success_receipt && relative == Path::new("result.json") {
            return Err(error(
                "tool_failed",
                "retention",
                "refusing to retain success receipt on failed run",
            ));
        }
        let target = destination.join(relative);
        if entry.file_type().is_dir() {
            fs::create_dir(&target).map_err(|e| io("retention", e))?;
        } else {
            fs::copy(entry.path(), target).map_err(|e| io("retention", e))?;
        }
    }
    // Mark the directory as retention's own, so a later
    // `--overwrite-artifacts` run can tell it from unrelated data.
    fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(destination.join(ARTIFACT_MARKER))
        .and_then(|mut marker| {
            use std::io::Write as _;
            marker.write_all(ARTIFACT_MARKER_TEXT.as_bytes())
        })
        .map_err(|e| io("retention", e))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn verification_directories_are_private_with_umask_022() {
        use std::os::unix::fs::{DirBuilderExt, PermissionsExt};

        const CHILD: &str = "ANNEAL_VERIFICATION_DIRECTORY_PERMISSION_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let stage = verification_stage().unwrap();
            fs::write(stage.path().join("input.rs"), b"private source bytes").unwrap();
            let parent = tempfile::tempdir().unwrap();
            let destination = parent.path().join("artifacts");
            assert!(retain(stage.path(), &destination).is_ok());
            assert_eq!(fs::read(destination.join("input.rs")).unwrap(), b"private source bytes");

            let existing = parent.path().join("existing");
            fs::DirBuilder::new().mode(0o750).create(&existing).unwrap();
            fs::write(existing.join("keep"), b"caller bytes").unwrap();
            assert!(retain(stage.path(), &existing).is_err());
            assert_eq!(fs::metadata(&existing).unwrap().permissions().mode() & 0o777, 0o750);
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller bytes");
            assert!(!existing.join("input.rs").exists());

            assert_eq!(
                (
                    fs::metadata(stage.path()).unwrap().permissions().mode() & 0o777,
                    fs::metadata(&destination).unwrap().permissions().mode() & 0o777,
                ),
                (0o700, 0o700)
            );
            return;
        }

        // Umask is process-wide. Change it only in a fresh child so this
        // regression cannot race other tests running in the parent binary.
        let output = Command::new("/bin/sh")
            .args(["-c", "umask 022; exec \"$@\"", "anneal-private-directories"])
            .arg(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "verify::tests::verification_directories_are_private_with_umask_022",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "permission probe failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        // `--exact` with a stale module path matches no test and still exits
        // successfully. Require the child to have run this probe.
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains("1 passed"), "permission probe did not run:\n{stdout}");
    }

    #[test]
    fn declaration_names_cannot_inject_lean_commands() {
        for valid in ["Spec.specs", "A.B_2.proof", "Proof.verify"] {
            assert!(identifier(valid));
        }
        for invalid in [
            "",
            ".Proof",
            "Proof..verify",
            "Proof.verify\naxiom x : False",
            "Proof.(verify)",
            "Proof.7bad",
        ] {
            assert!(!identifier(invalid));
        }
    }

    #[test]
    fn proof_modules_cannot_claim_runner_owned_names() {
        for reserved in [
            "Trusted",
            "Trusted.Foo",
            "Trusted.MirSemantics",
            "Captured",
            "Captured.Shard_000",
            "Expected",
            "Expected.Claim",
            "Anneal",
            "Anneal.Shadow",
            "Init",
            "Init.System.IO",
            "Std",
            "Std.Data.Foo",
            "Lean",
            "Lean.Elab",
            "Lake",
            "Lake.DSL",
            "TrustedBoundary",
            "TrustedBoundary.Helper",
            "SpecPreflight",
            "SpecPreflight.Helper",
        ] {
            assert!(reserved_proof_module(reserved), "{reserved}");
        }
        // A prefix within a component or a later component reserves nothing.
        for authored in [
            "Spec",
            "Proof",
            "TrustedHelper",
            "AnnealProof",
            "InitHelper",
            "LeanProof",
            "Proof.Trusted",
            "Proof.Init",
            "Spec.Expected",
        ] {
            assert!(!reserved_proof_module(authored), "{authored}");
        }
    }

    #[test]
    fn declared_inputs_reject_escape_and_symlinks() {
        let dir = tempfile::tempdir().unwrap();
        let out_of_tree = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("request.json"), "{}").unwrap();
        fs::write(dir.path().join("source.rs"), "pub fn f() {}").unwrap();
        fs::write(out_of_tree.path().join("ext.rs"), "pub fn g() {}").unwrap();

        // Missing or non-directory `source_root` values fail as `unsupported`
        // (exit 1), never `tool_failed` (exit 2).
        for bad_root in ["missing-dir", "request.json", "request.json/sub"] {
            let err = root(dir.path(), Path::new(bad_root)).unwrap_err();
            assert_eq!(err.status, "unsupported", "{bad_root}: {}", err.detail);
            assert_eq!(err.phase, "inputs", "{bad_root}: {}", err.detail);
        }

        // Relative and out-of-tree directories canonicalize cleanly while
        // `declared_file` confines every declared path strictly inside them.
        let canon_root = root(dir.path(), Path::new(".")).unwrap();
        let ext_root = root(dir.path(), out_of_tree.path()).unwrap();
        assert!(declared_file(&ext_root, Path::new("ext.rs")).is_ok());
        assert!(declared_file(&canon_root, Path::new("source.rs")).is_ok());
        assert!(declared_file(&canon_root, Path::new("../source.rs")).is_err());
        assert!(declared_file(&canon_root, Path::new("/source.rs")).is_err());
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink("source.rs", canon_root.join("alias.rs")).unwrap();
            assert!(declared_file(&canon_root, Path::new("alias.rs")).is_err());
            std::os::unix::fs::symlink(
                out_of_tree.path().join("ext.rs"),
                canon_root.join("escape.rs"),
            )
            .unwrap();
            assert!(declared_file(&canon_root, Path::new("escape.rs")).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn compiler_override_check_rejects_dangling_and_directory_symlinks() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        assert!(reject_compiler_overrides(dir.path()).is_ok());

        fs::create_dir(dir.path().join(".cargo")).unwrap();
        assert!(reject_compiler_overrides(dir.path()).is_ok());

        symlink("missing-config", dir.path().join(".cargo/config.toml")).unwrap();
        let err = reject_compiler_overrides(dir.path()).unwrap_err();
        assert!(err.detail.contains("(.cargo/config.toml: symlink;"), "{}", err.detail);
        fs::remove_file(dir.path().join(".cargo/config.toml")).unwrap();

        symlink("missing-toolchain", dir.path().join("rust-toolchain.toml")).unwrap();
        assert!(reject_compiler_overrides(dir.path()).is_err());
        fs::remove_file(dir.path().join("rust-toolchain.toml")).unwrap();

        fs::remove_dir(dir.path().join(".cargo")).unwrap();
        symlink("missing-cargo-dir", dir.path().join(".cargo")).unwrap();
        assert!(reject_compiler_overrides(dir.path()).is_err());

        // Non-NotFound metadata errors (e.g., ENOTDIR when `dir` is a regular
        // file) must also fail closed rather than looking absent.
        let not_a_dir = dir.path().join("not-a-dir");
        fs::write(&not_a_dir, b"plain file").unwrap();
        let Err(err) = reject_compiler_overrides(&not_a_dir) else {
            panic!("non-NotFound symlink_metadata error must fail closed");
        };
        assert_eq!(err.status, "tool_failed");
        assert_eq!(err.phase, "cargo");
    }

    #[test]
    fn compiler_override_check_admits_only_benign_cargo_configs() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join(".cargo")).unwrap();
        let config = dir.path().join(".cargo/config.toml");
        let legacy = dir.path().join(".cargo/config");
        for benign in [
            "[alias]\nnightly_docs = \"doc --no-deps -Zunstable-options\"\n",
            "[alias]\nb = \"build\"\n[term]\ncolor = \"never\"\n\
             [doc]\nbrowser = \"true\"\n",
        ] {
            for path in [&config, &legacy] {
                fs::write(path, benign).unwrap();
                assert!(reject_compiler_overrides(dir.path()).is_ok(), "{benign}");
                fs::remove_file(path).unwrap();
            }
        }
        for (rel, contents, reason) in [
            (".cargo/config.toml", "[build]\nrustflags = [\"-Cdebuginfo=0\"]\n", "table [build]"),
            (".cargo/config", "[build]\nrustflags = []\n", "table [build]"),
            (".cargo/config.toml", "[target.'cfg(all())']\nrustflags = []\n", "table [target]"),
            (
                ".cargo/config.toml",
                "[target.x86_64-unknown-linux-gnu]\nlinker = \"x\"\n",
                "table [target]",
            ),
            (".cargo/config.toml", "[env]\nX = \"1\"\n", "table [env]"),
            (".cargo/config.toml", "[patch.crates-io]\nx = { path = \"y\" }\n", "table [patch]"),
            (".cargo/config.toml", "[net]\noffline = true\n", "table [net]"),
            (".cargo/config.toml", "build.rustc-wrapper = \"evil\"\n", "top-level key"),
            (".cargo/config.toml", "[alias\nb = \"build\"\n", "malformed header"),
            ("rust-toolchain.toml", "[toolchain]\nchannel = \"nightly\"\n", "toolchain override"),
            ("rust-toolchain", "nightly\n", "toolchain override"),
        ] {
            let path = dir.path().join(rel);
            fs::write(&path, contents).unwrap();
            let err = reject_compiler_overrides(dir.path()).unwrap_err();
            assert_eq!(err.status, "unsupported");
            assert_eq!(err.phase, "cargo");
            assert!(
                err.detail
                    .starts_with("compiler overrides need an explicit configured compilation"),
                "{}",
                err.detail
            );
            assert!(err.detail.contains(&format!("({rel}: ")), "{}", err.detail);
            assert!(err.detail.contains(reason), "{}", err.detail);
            fs::remove_file(&path).unwrap();
        }
        assert!(reject_compiler_overrides(dir.path()).is_ok());
    }

    #[cfg(unix)]
    #[test]
    fn artifact_retention_cleans_failed_copy_and_allows_retry() {
        use std::os::unix::fs::symlink;

        let source = tempfile::tempdir().unwrap();
        fs::create_dir(source.path().join("logs")).unwrap();
        fs::write(source.path().join("logs/compiler.stderr"), b"diagnostics").unwrap();
        let outside = tempfile::tempdir().unwrap();
        let sentinel = outside.path().join("keep");
        fs::write(&sentinel, b"outside bytes").unwrap();
        let link = source.path().join("unexpected");
        symlink(&sentinel, &link).unwrap();
        let export_parent = tempfile::tempdir().unwrap();
        let destination = export_parent.path().join("artifacts");

        let Err(failure) = retain(source.path(), &destination) else {
            panic!("a staging symlink must reject retention");
        };
        assert_eq!(failure.status, "tool_failed");
        assert_eq!(failure.phase, "retention");
        assert!(!destination.exists(), "a failed export must be removed");
        assert_eq!(fs::read(&sentinel).unwrap(), b"outside bytes");

        fs::remove_file(link).unwrap();
        assert!(retain(source.path(), &destination).is_ok());
        assert_eq!(fs::read(destination.join("logs/compiler.stderr")).unwrap(), b"diagnostics");
    }

    #[test]
    fn artifact_retention_preserves_existing_empty_destination() {
        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("new"), b"new output").unwrap();
        let destination = tempfile::tempdir().unwrap();
        assert!(retain(source.path(), destination.path()).is_err());
        assert!(destination.path().is_dir());
        assert_eq!(fs::read_dir(destination.path()).unwrap().count(), 0);
    }

    #[cfg(unix)]
    #[test]
    fn artifact_retention_preserves_existing_symlink_destination() {
        use std::os::unix::fs::symlink;

        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("new"), b"new output").unwrap();
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("keep"), b"outside bytes").unwrap();
        let parent = tempfile::tempdir().unwrap();
        let destination = parent.path().join("artifacts");
        symlink(outside.path(), &destination).unwrap();
        assert!(retain(source.path(), &destination).is_err());
        assert!(fs::symlink_metadata(&destination).unwrap().is_symlink());
        assert_eq!(fs::read(outside.path().join("keep")).unwrap(), b"outside bytes");
        assert!(!outside.path().join("new").exists());
    }

    #[test]
    fn artifact_retention_never_overwrites() {
        let source = tempfile::tempdir().unwrap();
        let target = tempfile::tempdir().unwrap();
        fs::write(target.path().join("keep"), b"valuable").unwrap();
        assert!(retain(source.path(), target.path()).is_err());
        assert_eq!(fs::read(target.path().join("keep")).unwrap(), b"valuable");
    }

    /// List the entries of `dir` other than `except`, so tests can assert
    /// that replacement leaves no staging directories behind.
    fn siblings(dir: &Path, except: &str) -> Vec<String> {
        let mut names: Vec<String> = fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .filter(|name| name != except)
            .collect();
        names.sort();
        names
    }

    #[test]
    fn overwrite_artifacts_replaces_only_earlier_artifact_directories() {
        let parent = tempfile::tempdir().unwrap();
        let destination = parent.path().join("artifacts");

        // Absent destination: behaves like create-only retention.
        let first = tempfile::tempdir().unwrap();
        fs::write(first.path().join("request.json"), b"first").unwrap();
        fs::write(first.path().join("result.json"), b"{}").unwrap();
        replace_stage(first.path(), &destination, true, &[]).unwrap().commit();
        assert_eq!(fs::read(destination.join("request.json")).unwrap(), b"first");

        // Repeated runs replace the earlier artifacts wholesale, including
        // with a trailing separator, and leave no staging siblings behind.
        let second = tempfile::tempdir().unwrap();
        fs::create_dir(second.path().join("capture")).unwrap();
        fs::write(second.path().join("capture/capture.json"), b"second").unwrap();
        let spelled = PathBuf::from(format!("{}/", destination.display()));
        replace_stage(second.path(), &spelled, false, &[]).unwrap().commit();
        assert_eq!(fs::read(destination.join("capture/capture.json")).unwrap(), b"second");
        assert!(!destination.join("result.json").exists());
        assert!(siblings(parent.path(), "artifacts").is_empty());
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = fs::metadata(&destination).unwrap().permissions().mode();
            assert_eq!(mode & 0o777, 0o700);
        }

        // A failed copy (here: a success receipt on a failed run) leaves the
        // existing artifacts intact.
        let failed = tempfile::tempdir().unwrap();
        fs::write(failed.path().join("result.json"), b"{}").unwrap();
        let err = replace_stage(failed.path(), &destination, false, &[]).unwrap_err();
        assert!(err.detail.contains("success receipt"), "{}", err.detail);
        assert_eq!(fs::read(destination.join("capture/capture.json")).unwrap(), b"second");
        assert!(siblings(parent.path(), "artifacts").is_empty());

        // A directory with any foreign entry is never replaced.
        fs::write(destination.join("notes.txt"), b"mine").unwrap();
        let err = replace_stage(second.path(), &destination, true, &[]).unwrap_err();
        assert!(err.detail.contains("notes.txt"), "{}", err.detail);
        assert_eq!(fs::read(destination.join("notes.txt")).unwrap(), b"mine");
        assert!(siblings(parent.path(), "artifacts").is_empty());

        // A later failure (such as a `--receipt-out` error) rolls back to the
        // earlier artifacts, which stay aside until the run commits.
        fs::remove_file(destination.join("notes.txt")).unwrap();
        fs::write(destination.join("result.json"), b"{}").unwrap();
        fs::create_dir(destination.join("lean-lib")).unwrap();
        let third = tempfile::tempdir().unwrap();
        fs::write(third.path().join("request.json"), b"third").unwrap();
        let guard = replace_stage(third.path(), &destination, true, &[]).unwrap();
        assert_eq!(fs::read(destination.join("request.json")).unwrap(), b"third");
        assert_eq!(siblings(parent.path(), "artifacts").len(), 1);
        let detail = guard.rollback("receipt failed".to_owned());
        assert_eq!(detail, "receipt failed");
        assert_eq!(fs::read(destination.join("capture/capture.json")).unwrap(), b"second");
        assert!(!destination.join("request.json").exists());
        // The failed run never restores earlier success evidence.
        assert!(!destination.join("result.json").exists());
        assert!(!destination.join("lean-lib").exists());
        assert!(destination.join(ARTIFACT_MARKER).is_file());
        assert!(siblings(parent.path(), "artifacts").is_empty());
    }

    /// Rollback restores an earlier directory only once its success evidence
    /// is gone; if that fails, the directory stays aside.
    #[cfg(unix)]
    #[test]
    fn rollback_keeps_earlier_artifacts_aside_when_invalidation_fails() {
        let parent = tempfile::tempdir().unwrap();
        let destination = parent.path().join("artifacts");
        fs::create_dir(&destination).unwrap();
        fs::write(destination.join("request.json"), b"new").unwrap();
        let old = parent.path().join(".artifacts.anneal-old-test");
        fs::create_dir(&old).unwrap();
        fs::write(old.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        let elsewhere = parent.path().join("elsewhere.json");
        fs::write(&elsewhere, b"{}").unwrap();
        std::os::unix::fs::symlink(&elsewhere, old.join("result.json")).unwrap();

        let guard =
            RetainedArtifacts { destination: destination.clone(), previous: Some(old.clone()) };
        let detail = guard.rollback("receipt failed".to_owned());
        assert!(detail.starts_with("receipt failed; earlier artifacts remain at"), "{detail}");
        assert!(detail.contains("invalidation failed"), "{detail}");
        let missing = fs::symlink_metadata(&destination).unwrap_err();
        assert_eq!(missing.kind(), std::io::ErrorKind::NotFound);
        assert!(fs::symlink_metadata(old.join("result.json")).unwrap().is_symlink());
        assert_eq!(fs::read(&elsewhere).unwrap(), b"{}");
    }

    #[test]
    fn overwrite_artifacts_refuses_directories_holding_verification_inputs() {
        let parent = tempfile::tempdir().unwrap();
        let cwd = parent.path().join("cwd");
        fs::create_dir(&cwd).unwrap();
        let destination = parent.path().join("evidence");
        fs::create_dir_all(destination.join("rust")).unwrap();
        fs::write(destination.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        fs::write(destination.join("request.json"), b"{}").unwrap();
        fs::write(destination.join("rust/Cargo.toml"), b"[package]").unwrap();
        let outside = parent.path().join("outside.json");
        fs::write(&outside, b"{}").unwrap();

        let check =
            |inputs: &[PathBuf]| check_replaceable_artifacts_protecting(&destination, &cwd, inputs);
        assert_eq!(check(std::slice::from_ref(&outside)), Ok(()));
        for input in [
            destination.join("request.json"),
            destination.join("rust"),
            destination.join("rust/Cargo.toml"),
            destination.clone(),
            // Not yet existing, but its nearest existing ancestor is inside.
            destination.join("rust/src/lib.rs"),
            // Relative inputs resolve against the working directory.
            PathBuf::from("../evidence/request.json"),
        ] {
            let reason = check(&[outside.clone(), input.clone()]).unwrap_err();
            assert!(reason.contains("verification input"), "{input:?}: {reason}");
        }

        // `replace_stage` refuses the same inputs and leaves them in place.
        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("request.json"), b"new").unwrap();
        let err = replace_stage(source.path(), &destination, true, &[destination.join("rust")])
            .unwrap_err();
        assert!(err.detail.contains("verification input"), "{}", err.detail);
        assert_eq!(fs::read(destination.join("rust/Cargo.toml")).unwrap(), b"[package]");
    }

    #[test]
    fn invalidate_success_evidence_drops_only_receipt_and_lean_lib() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        fs::write(dir.path().join("result.json"), b"{}").unwrap();
        fs::create_dir_all(dir.path().join("lean-lib/Proof")).unwrap();
        fs::write(dir.path().join("lean-lib/Proof/A.olean"), b"x").unwrap();
        fs::write(dir.path().join("request.json"), b"{}").unwrap();
        invalidate_success_evidence(dir.path()).unwrap();
        assert!(!dir.path().join("result.json").exists());
        assert!(!dir.path().join("lean-lib").exists());
        assert!(dir.path().join("request.json").is_file());
        assert!(dir.path().join(ARTIFACT_MARKER).is_file());
        // Absent evidence is fine; an unexpected kind fails closed.
        invalidate_success_evidence(dir.path()).unwrap();
        fs::create_dir(dir.path().join("result.json")).unwrap();
        assert!(invalidate_success_evidence(dir.path()).is_err());
        assert!(dir.path().join("result.json").is_dir());
    }

    #[cfg(unix)]
    #[test]
    fn overwrite_invalidation_rechecks_the_preflighted_directory() {
        let parent = tempfile::tempdir().unwrap();
        let seed = |dir: &Path| {
            fs::create_dir_all(dir.join("lean-lib")).unwrap();
            fs::write(dir.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
            fs::write(dir.join("result.json"), b"{}").unwrap();
        };
        // A destination absent at preflight has nothing to invalidate.
        let ev = parent.path().join("ev");
        let spelled = format!("{}/", ev.display());
        assert!(preflight_artifact_destination_mode(&spelled, true, &[]).unwrap().is_none());

        // The trailing separator is stripped, and the admitted directory
        // loses only its success evidence.
        seed(&ev);
        let existing = preflight_artifact_destination_mode(&spelled, true, &[]).unwrap().unwrap();
        assert_eq!(existing.entry, ev);
        existing.invalidate(&[]).unwrap();
        assert!(!ev.join("result.json").exists());
        assert!(!ev.join("lean-lib").exists());
        assert!(ev.join(ARTIFACT_MARKER).is_file());

        // Entries added after preflight are re-checked.
        seed(&ev);
        let existing = preflight_artifact_destination_mode(&spelled, true, &[]).unwrap().unwrap();
        fs::write(ev.join("notes.txt"), b"caller notes").unwrap();
        let reason = existing.invalidate(&[]).unwrap_err();
        assert!(reason.contains("notes.txt"), "{reason}");
        assert!(ev.join("result.json").is_file());
        fs::remove_file(ev.join("notes.txt")).unwrap();

        // A symlink or a different directory swapped in after preflight is
        // refused, and neither it nor the original is modified.
        let moved = parent.path().join("moved");
        fs::rename(&ev, &moved).unwrap();
        let other = parent.path().join("other");
        seed(&other);
        std::os::unix::fs::symlink(&other, &ev).unwrap();
        let reason = existing.invalidate(&[]).unwrap_err();
        assert!(reason.contains("changed after it was checked"), "{reason}");
        fs::remove_file(&ev).unwrap();
        seed(&ev);
        let reason = existing.invalidate(&[]).unwrap_err();
        assert!(reason.contains("changed after it was checked"), "{reason}");
        for dir in [&ev, &moved, &other] {
            assert!(dir.join("result.json").is_file(), "{}", dir.display());
            assert!(dir.join("lean-lib").is_dir(), "{}", dir.display());
        }
    }

    #[cfg(unix)]
    #[test]
    fn overwrite_artifacts_refuses_symlinks_files_and_cwd_ancestors() {
        use std::os::unix::fs::symlink;

        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("request.json"), b"new").unwrap();
        let parent = tempfile::tempdir().unwrap();
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("request.json"), b"outside").unwrap();

        // A symlink to an artifact-looking directory is refused at preflight
        // and at retention, without touching its target.
        let link = parent.path().join("link");
        symlink(outside.path(), &link).unwrap();
        for spelling in [link.display().to_string(), format!("{}/", link.display())] {
            let Err(failure) = preflight_artifact_destination_mode(&spelling, true, &[]) else {
                panic!("symlink destination {spelling} must be rejected");
            };
            assert!(failure.detail.contains("symlink"), "{}", failure.detail);
            let err = replace_stage(source.path(), Path::new(&spelling), true, &[]).unwrap_err();
            assert!(err.detail.contains("symlink"), "{}", err.detail);
        }
        assert_eq!(fs::read(outside.path().join("request.json")).unwrap(), b"outside");
        assert!(fs::symlink_metadata(&link).unwrap().is_symlink());

        let file = parent.path().join("file");
        fs::write(&file, b"caller file").unwrap();
        let Err(failure) = preflight_artifact_destination_mode(file.to_str().unwrap(), true, &[])
        else {
            panic!("regular-file destination must be rejected");
        };
        assert!(failure.detail.contains("not a directory"), "{}", failure.detail);
        assert!(replace_stage(source.path(), &file, true, &[]).is_err());
        assert_eq!(fs::read(&file).unwrap(), b"caller file");

        for root_like in ["/", ".", "..", &format!("{}/.", parent.path().display())] {
            let Err(failure) = preflight_artifact_destination_mode(root_like, true, &[]) else {
                panic!("{root_like} must be rejected");
            };
            assert!(failure.detail.contains("must end in a"), "{}", failure.detail);
        }

        let empty = parent.path().join("empty");
        fs::create_dir(&empty).unwrap();
        assert!(preflight_artifact_destination_mode(empty.to_str().unwrap(), true, &[]).is_ok());
        assert!(preflight_artifact_destination_mode(empty.to_str().unwrap(), false, &[]).is_err());
        let nested = empty.join("authored");
        fs::create_dir(&nested).unwrap();
        let reason = check_replaceable_artifacts(&empty, &nested).unwrap_err();
        assert!(reason.contains("working directory"), "{reason}");
        let reason = check_replaceable_artifacts(&empty, parent.path()).unwrap_err();
        assert!(reason.contains("marker"), "{reason}");
        fs::write(empty.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        assert!(check_replaceable_artifacts(&empty, parent.path()).is_ok());
        let missing_cwd = parent.path().join("missing-cwd");
        let reason = check_replaceable_artifacts(&empty, &missing_cwd).unwrap_err();
        assert!(reason.contains("cannot verify"), "{reason}");

        // A dangling symlink spelled with a trailing separator is still
        // inspected as the link itself.
        let dangling = parent.path().join("dangling");
        symlink(parent.path().join("absent"), &dangling).unwrap();
        let spelled = PathBuf::from(format!("{}/", dangling.display()));
        let err = replace_stage(source.path(), &spelled, true, &[]).unwrap_err();
        assert!(err.detail.contains("symlink"), "{}", err.detail);
        assert!(!parent.path().join("absent").exists());
    }

    /// Every top-level entry that production code stages into the work
    /// directory must be replaceable, or `--overwrite-artifacts` would refuse
    /// directories that retention itself wrote.
    #[test]
    fn artifact_entries_cover_every_staged_top_level_entry() {
        let source = include_str!("verify.rs");
        let production = &source[..source.find("#[cfg(test)]\nmod tests").unwrap()];
        let mut staged = BTreeSet::new();
        for piece in production.split("work.join(\"").skip(1) {
            let path = &piece[..piece.find('"').unwrap()];
            staged.insert(path.split('/').next().unwrap());
        }
        assert!(staged.contains("expected-shard-plan.json"), "{staged:?}");
        for name in &staged {
            assert!(
                ARTIFACT_ENTRIES.iter().any(|(known, _)| known == name),
                "{name} is staged but missing from ARTIFACT_ENTRIES"
            );
        }

        // A retained directory holding the shard-plan snapshot is replaceable.
        let parent = tempfile::tempdir().unwrap();
        let destination = parent.path().join("artifacts");
        let first = tempfile::tempdir().unwrap();
        fs::write(first.path().join("expected-shard-plan.json"), b"first").unwrap();
        replace_stage(first.path(), &destination, false, &[]).unwrap().commit();
        let second = tempfile::tempdir().unwrap();
        fs::write(second.path().join("expected-shard-plan.json"), b"second").unwrap();
        replace_stage(second.path(), &destination, false, &[]).unwrap().commit();
        assert_eq!(fs::read(destination.join("expected-shard-plan.json")).unwrap(), b"second");
    }

    /// Directories whose entries merely reuse generic stage names (such as a
    /// checkout named `anneal` or `rust`) are never replaced; only a
    /// directory carrying the exact marker, with each entry of the expected
    /// kind, is.
    #[cfg(unix)]
    #[test]
    fn overwrite_artifacts_requires_marker_and_entry_kinds() {
        use std::os::unix::fs::symlink;

        let parent = tempfile::tempdir().unwrap();
        let cwd = parent.path();
        let check = |dir: &Path| check_replaceable_artifacts(dir, cwd);
        let make = |name: &str| {
            let dir = parent.path().join(name);
            fs::create_dir(&dir).unwrap();
            dir
        };

        let checkout = make("checkout");
        fs::create_dir(checkout.join("anneal")).unwrap();
        fs::write(checkout.join("anneal/lib.rs"), b"user source").unwrap();
        assert!(check(&checkout).unwrap_err().contains("marker"));

        let with_git = make("with-git");
        fs::create_dir(with_git.join("rust")).unwrap();
        fs::create_dir(with_git.join(".git")).unwrap();
        fs::write(with_git.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        assert!(check(&with_git).unwrap_err().contains(".git"));

        let wrong_marker = make("wrong-marker");
        fs::create_dir(wrong_marker.join("rust")).unwrap();
        fs::write(wrong_marker.join(ARTIFACT_MARKER), b"something else\n").unwrap();
        assert!(check(&wrong_marker).unwrap_err().contains("marker"));

        let linked = make("linked");
        fs::write(linked.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        symlink(parent.path().join("checkout"), linked.join("anneal")).unwrap();
        assert!(check(&linked).unwrap_err().contains("symlink"));

        let wrong_kind = make("wrong-kind");
        fs::write(wrong_kind.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        fs::create_dir(wrong_kind.join("request.json")).unwrap();
        assert!(check(&wrong_kind).unwrap_err().contains("different file type"));

        let marker_dir = make("marker-dir");
        fs::create_dir(marker_dir.join(ARTIFACT_MARKER)).unwrap();
        assert!(check(&marker_dir).is_err());

        let owned = make("owned");
        fs::write(owned.join(ARTIFACT_MARKER), ARTIFACT_MARKER_TEXT).unwrap();
        fs::create_dir(owned.join("rust")).unwrap();
        fs::write(owned.join("request.json"), b"{}").unwrap();
        assert_eq!(check(&owned), Ok(()));
        assert_eq!(check(&make("empty")), Ok(()));

        // None of the refused directories lost anything.
        assert_eq!(fs::read(checkout.join("anneal/lib.rs")).unwrap(), b"user source");
        assert!(with_git.join(".git").is_dir());

        // Retention writes the marker, so its own output is replaceable.
        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("request.json"), b"{}").unwrap();
        let retained = parent.path().join("retained");
        retain(source.path(), &retained).unwrap();
        assert_eq!(
            fs::read(retained.join(ARTIFACT_MARKER)).unwrap(),
            ARTIFACT_MARKER_TEXT.as_bytes()
        );
        assert_eq!(check(&retained), Ok(()));
    }

    /// Run the preflight on `path`, which must be UTF-8 as `main` ensures.
    fn preflight(path: &Path) -> Result<()> {
        preflight_artifact_destination(path.to_str().unwrap())
    }

    fn preflight_detail(path: &str) -> String {
        let Err(failure) = preflight_artifact_destination(path) else {
            panic!("artifact destination {path:?} must be rejected");
        };
        assert_eq!(failure.status, "tool_failed");
        assert_eq!(failure.phase, "retention");
        failure.detail
    }

    #[test]
    fn artifact_preflight_accepts_only_claimable_destinations() {
        let parent = tempfile::tempdir().unwrap();
        let fresh = parent.path().join("fresh");
        assert!(preflight(&fresh).is_ok());
        assert!(preflight_artifact_destination(&format!("{}/", fresh.display())).is_ok());
        assert!(!fresh.exists(), "preflight must not create the destination");

        let directory = parent.path().join("directory");
        fs::create_dir(&directory).unwrap();
        let file = parent.path().join("file");
        fs::write(&file, b"caller bytes").unwrap();
        for existing in [&directory, &file] {
            let shown = existing.to_str().unwrap();
            for spelling in [shown.to_owned(), format!("{shown}/")] {
                let detail = preflight_detail(&spelling);
                assert!(detail.contains("already exists"), "{detail}");
            }
        }
        assert_eq!(fs::read(&file).unwrap(), b"caller bytes");
        assert!(preflight_detail("/").contains("already exists"));

        let empty = preflight_detail("");
        assert!(empty.contains("empty"), "{empty}");

        for dots in ["missing/.", "missing/..", "missing/./"] {
            let spelling = format!("{}/{dots}", parent.path().display());
            let detail = preflight_detail(&spelling);
            assert!(detail.contains("must end in a new directory name"), "{detail}");
        }

        let missing = parent.path().join("missing");
        let detail = preflight_detail(missing.join("out").to_str().unwrap());
        let missing_err = fs::metadata(&missing).unwrap_err();
        assert_eq!(
            detail,
            format!("artifact destination parent {}: {missing_err}", missing.display())
        );

        let detail = preflight_detail(file.join("out").to_str().unwrap());
        assert_eq!(
            detail,
            format!("artifact destination parent {} is not a directory", file.display())
        );
        let sub = file.join("sub");
        let detail = preflight_detail(sub.join("out").to_str().unwrap());
        let sub_prefix = format!("artifact destination parent {}: ", sub.display());
        assert!(detail.starts_with(&sub_prefix), "{detail}");
        assert!(!missing.exists());

        // Destinations directly under filesystem root exercise root parent
        // resolution (`/`). Multiple leading slashes remain valid on Unix.
        if !Path::new("/anneal-preflight-nonexistent-root-probe").exists() {
            assert!(
                preflight_artifact_destination("/anneal-preflight-nonexistent-root-probe").is_ok()
            );
            #[cfg(unix)]
            assert!(
                preflight_artifact_destination("///anneal-preflight-nonexistent-root-probe")
                    .is_ok()
            );
        }

        // Windows drive, drive-relative, and verbatim prefixes remain intact.
        let win_sep: fn(char) -> bool = |c| c == '/' || c == '\\';
        assert_eq!(
            split_artifact_destination_with_prefix_len(r"C:\fresh", 2, win_sep),
            (r"C:\fresh", "fresh", r"C:\".to_owned())
        );
        assert_eq!(
            split_artifact_destination_with_prefix_len(r"C:\", 2, win_sep),
            (r"C:\", "", String::new())
        );
        assert_eq!(
            split_artifact_destination_with_prefix_len(r"\\?\C:\fresh", 6, win_sep),
            (r"\\?\C:\fresh", "fresh", r"\\?\C:\".to_owned())
        );
        assert_eq!(
            split_artifact_destination_with_prefix_len("C:fresh", 2, win_sep),
            ("C:fresh", "fresh", "C:.".to_owned())
        );
        assert_eq!(
            split_artifact_destination_with_prefix_len("C:.", 2, win_sep),
            ("C:.", ".", "C:.".to_owned())
        );
        assert_eq!(
            split_artifact_destination_with_prefix_len("C:..", 2, win_sep),
            ("C:..", "..", "C:.".to_owned())
        );
    }

    #[cfg(unix)]
    #[test]
    fn artifact_preflight_reports_non_notfound_symlink_metadata_errors() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let loop_a = dir.path().join("loop_a");
        let loop_b = dir.path().join("loop_b");
        symlink(&loop_b, &loop_a).unwrap();
        symlink(&loop_a, &loop_b).unwrap();
        let target = loop_a.join("out");
        let detail = preflight_detail(target.to_str().unwrap());
        let expected_prefix = format!("artifact destination {}: ", target.display());
        assert!(detail.starts_with(&expected_prefix), "{detail}");
        assert!(!detail.contains("already exists"), "{detail}");
        assert!(!detail.contains("parent "), "{detail}");
    }

    #[cfg(unix)]
    #[test]
    fn artifact_preflight_rejects_live_and_dangling_symlink_destinations() {
        use std::os::unix::fs::symlink;

        let outside = tempfile::tempdir().unwrap();
        let parent = tempfile::tempdir().unwrap();
        let live = parent.path().join("live");
        symlink(outside.path(), &live).unwrap();
        let dangling = parent.path().join("dangling");
        symlink(outside.path().join("absent"), &dangling).unwrap();
        for link in [&live, &dangling] {
            let shown = link.to_str().unwrap();
            // A trailing separator makes `lstat` follow the link; the check
            // must still see the link itself, as `mkdir` does.
            for spelling in [shown.to_owned(), format!("{shown}/")] {
                let detail = preflight_detail(&spelling);
                assert!(detail.contains("already exists"), "{detail}");
            }
            assert!(fs::symlink_metadata(link).unwrap().is_symlink());
        }
        assert!(!outside.path().join("absent").exists());

        // A symlinked parent directory is accepted, matching `mkdir`.
        assert!(preflight(&live.join("out")).is_ok());
        let detail = preflight_detail(dangling.join("out").to_str().unwrap());
        assert!(detail.starts_with("artifact destination parent "), "{detail}");
    }

    #[test]
    fn old_capture_schema_reports_version_mismatch_before_strict_deserialization() {
        for legacy in [
            br#"{"schema_version":2,"compiler":{"commit":"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"},"legacy":true}"#.as_slice(),
            br#"{"schema_version":3,"compiler":{"commit":"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"},"legacy":true}"#.as_slice(),
            br#"{"schema_version":4,"compiler":{"commit":"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"},"legacy":true}"#.as_slice(),
        ] {
            let Err(err) = parse_capture_receipt(legacy) else {
                panic!("legacy schema receipt must be rejected");
            };
            assert_eq!(err.status, "tool_failed");
            assert_eq!(err.phase, "capture");
            assert_eq!(err.detail, "unexpected capture schema or compiler");
        }

        // Schema 5 receipts carrying 128-bit decimal string constants above
        // `u64::MAX` inside `program.bodies` parse cleanly without arbitrary
        // JSON number precision.
        let schema5_u128 = br#"{
            "schema_version": 5,
            "compiler": { "commit": "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1" },
            "configuration": {},
            "source_files": [{ "path": "src/lib.rs", "sha256": "00" }],
            "census": [],
            "selected": [],
            "program": {
                "scope": { "kind": "crate" },
                "bodies": [{ "bits": "340282366920938463463374607431768211455" }]
            }
        }"#;
        assert!(parse_capture_receipt(schema5_u128).is_ok());
    }

    #[test]
    fn failure_receipt_preserves_null_or_omitted_artifacts_and_sandbox() {
        let omitted: Value = serde_json::to_value(FailureReceipt {
            schema_version: RECEIPT_SCHEMA_VERSION,
            taint_reasons: &[],
            elaboration_sandbox: None,
            status: "tool_failed",
            phase: "retention",
            detail: "bad path",
            hint: None,
            artifacts: None,
        })
        .unwrap();
        assert_eq!(omitted["schema_version"], 3);
        assert_eq!(omitted["taint_reasons"], json!([]));
        assert!(omitted.get("tainted").is_none(), "{omitted}");
        assert!(omitted.get("hint").is_none(), "{omitted}");
        assert!(omitted.get("artifacts").is_none(), "{omitted}");
        assert!(omitted.get("elaboration_sandbox").is_none(), "{omitted}");

        let explicit_null: Value = serde_json::to_value(FailureReceipt {
            schema_version: RECEIPT_SCHEMA_VERSION,
            taint_reasons: &["unpinned_lean"],
            elaboration_sandbox: None,
            status: "unsupported",
            phase: "capture",
            detail: "bad item",
            hint: Some("try --select"),
            artifacts: Some(None),
        })
        .unwrap();
        assert_eq!(explicit_null["taint_reasons"], json!(["unpinned_lean"]));
        assert!(explicit_null.get("unpinned_lean").is_none());
        assert!(explicit_null.get("elaboration_sandbox").is_none());
        assert_eq!(explicit_null["hint"], "try --select");
        assert_eq!(explicit_null.get("artifacts"), Some(&Value::Null), "{explicit_null}");

        let retained: Value = serde_json::to_value(FailureReceipt {
            schema_version: RECEIPT_SCHEMA_VERSION,
            taint_reasons: &[],
            elaboration_sandbox: Some("linux_bwrap"),
            status: "proof_failed",
            phase: "audit",
            detail: "mismatch",
            hint: None,
            artifacts: Some(Some("/tmp/evidence")),
        })
        .unwrap();
        assert_eq!(retained["artifacts"], "/tmp/evidence");
        assert_eq!(retained["elaboration_sandbox"], "linux_bwrap");
    }

    #[test]
    fn taint_monoid_projects_all_sixteen_flag_subsets_canonically() {
        let all = [
            VerificationTaint::SorryInProof,
            VerificationTaint::UnmodeledUnstableFeatures,
            VerificationTaint::UnpinnedLean,
            VerificationTaint::UnsandboxedElaboration,
        ];
        for pair in all.windows(2) {
            assert!(pair[0] < pair[1], "{pair:?}");
            assert!(pair[0].as_str() < pair[1].as_str(), "{pair:?}");
        }
        let base = VerifyArgs {
            format: VerifyFormat::Human,
            receipt_out: None,
            request: Some(PathBuf::from("request.json")),
            manifest_path: None,
            proof_dir: None,
            panic: None,
            overflow_checks: false,
            select: Vec::new(),
            instantiate: Vec::new(),
            features: Vec::new(),
            all_features: false,
            no_default_features: false,
            capture: None,
            lean: None,
            sysroot: None,
            artifacts: None,
            export_lean_lib: false,
            overwrite_artifacts: false,
            allow_unpinned_lean: false,
            allow_unsandboxed_elaboration: false,
            allow_sorry_in_proof: false,
            paranoid_quorum: false,
            allow_unstable_feature: Vec::new(),
            lean_memory_mb: None,
            no_cache: false,
            no_rebuild_bundled: false,
            shard: ShardArgs::default(),
            verify_shard_plan: None,
            command: None,
        };
        let crate_scope = Scope::Crate {};
        let unit_scope = Scope::SelectedUnit {
            roots: BTreeSet::from(["foo".to_owned()]),
            instantiations: BTreeSet::new(),
        };

        for (sorry, unstable) in [(false, false), (false, true), (true, false), (true, true)] {
            for unpinned in [false, true] {
                for unsandboxed in [false, true] {
                    let args = VerifyArgs {
                        format: VerifyFormat::Human,
                        receipt_out: None,
                        allow_sorry_in_proof: sorry,
                        allow_unstable_feature: if unstable {
                            vec!["doc_cfg".to_owned()]
                        } else {
                            Vec::new()
                        },
                        allow_unpinned_lean: unpinned,
                        allow_unsandboxed_elaboration: unsandboxed,
                        request: base.request.clone(),
                        manifest_path: None,
                        proof_dir: None,
                        panic: None,
                        overflow_checks: false,
                        select: Vec::new(),
                        instantiate: Vec::new(),
                        features: Vec::new(),
                        all_features: false,
                        no_default_features: false,
                        capture: None,
                        lean: None,
                        sysroot: None,
                        artifacts: None,
                        export_lean_lib: false,
                        paranoid_quorum: false,
                        overwrite_artifacts: false,
                        lean_memory_mb: None,
                        no_cache: false,
                        no_rebuild_bundled: false,
                        shard: ShardArgs::default(),
                        verify_shard_plan: None,
                        command: None,
                    };
                    let taints = active_taints(&args);
                    let reasons = taint_reason_strings(&taints);
                    let mut expected = Vec::new();
                    if sorry {
                        expected.push("sorry_in_proof");
                    }
                    if unstable {
                        expected.push("unmodeled_unstable_features");
                    }
                    if unpinned {
                        expected.push("unpinned_lean");
                    }
                    if unsandboxed {
                        expected.push("unsandboxed_elaboration");
                    }
                    assert_eq!(reasons, expected);
                    let tainted = !taints.is_empty();
                    assert_eq!(
                        crate_scope.verified_status(tainted),
                        if tainted { "tainted_crate_verified" } else { "crate_verified" }
                    );
                    assert_eq!(
                        unit_scope.verified_status(tainted),
                        if tainted {
                            "tainted_selected_unit_verified"
                        } else {
                            "selected_unit_verified"
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn unstable_feature_args_are_strict_identifiers() {
        for valid in ["doc_cfg", "f16", "a", "allocator_api"] {
            assert_eq!(parse_unstable_feature_arg(valid).unwrap(), valid);
        }
        for invalid in ["", "*", "Doc_cfg", "_doc", "1abc", "doc-cfg", "doc cfg", "a,b", "a=b"] {
            assert!(parse_unstable_feature_arg(invalid).is_err(), "{invalid:?}");
        }
    }

    #[test]
    fn captured_unstable_features_must_match_operator_allowlist() {
        // Default captures omit every feature list.
        assert_eq!(
            check_captured_unstable_features(&json!({"crate_name": "x"}), &[]).unwrap(),
            CapturedUnstableFeatures::default()
        );
        // A stabilized-only crate stays untainted and needs no allowlist.
        assert!(
            check_captured_unstable_features(
                &json!({"stabilized_features_present": ["doc_alias"]}),
                &[]
            )
            .is_ok()
        );
        let allowed = ["allocator_api", "generic_const_exprs"];
        let full = json!({
            "allowed_unstable_features": allowed,
            "observed_unstable_features": ["generic_const_exprs"],
            "incomplete_observed_unstable_features": ["generic_const_exprs"],
        });
        assert_eq!(
            check_captured_unstable_features(&full, &allowed).unwrap(),
            CapturedUnstableFeatures {
                observed: vec!["generic_const_exprs".to_owned()],
                incomplete_observed: vec!["generic_const_exprs".to_owned()],
            }
        );
        // Flag present but no feature enabled by the crate.
        let unused = json!({"allowed_unstable_features": ["doc_cfg"]});
        assert_eq!(
            check_captured_unstable_features(&unused, &["doc_cfg"]).unwrap(),
            CapturedUnstableFeatures::default()
        );

        for (configuration, allowed) in [
            // Capture ignored or widened the operator's allowlist.
            (json!({}), &["doc_cfg"][..]),
            (json!({"allowed_unstable_features": ["doc_cfg"]}), &[][..]),
            (json!({"allowed_unstable_features": ["doc_cfg", "f16"]}), &["doc_cfg"][..]),
            // Observed outside allowed; incomplete outside observed.
            (
                json!({
                    "allowed_unstable_features": ["doc_cfg"],
                    "observed_unstable_features": ["f16"],
                }),
                &["doc_cfg"][..],
            ),
            (
                json!({
                    "allowed_unstable_features": ["doc_cfg"],
                    "incomplete_observed_unstable_features": ["doc_cfg"],
                }),
                &["doc_cfg"][..],
            ),
            // Malformed lists: empty, unsorted, duplicated, or non-strings.
            (json!({"allowed_unstable_features": []}), &[][..]),
            (json!({"allowed_unstable_features": ["f16", "doc_cfg"]}), &["doc_cfg", "f16"][..]),
            (json!({"allowed_unstable_features": ["f16", "f16"]}), &["f16"][..]),
            (json!({"allowed_unstable_features": [1]}), &[][..]),
            (json!({"stabilized_features_present": "doc_alias"}), &[][..]),
            (json!({"stabilized_features_present": ["Doc_alias"]}), &[][..]),
            (json!({"stabilized_features_present": [""]}), &[][..]),
        ] {
            assert!(
                check_captured_unstable_features(&configuration, allowed).is_err(),
                "{configuration} with {allowed:?}"
            );
        }
    }

    #[test]
    fn validate_sorry_declarations_enforces_flag_and_axiom_consistency() {
        let base_closures = |mut obj: serde_json::Map<String, Value>| {
            obj.entry("replay").or_insert(json!(true));
            obj.entry("exactType").or_insert(json!(true));
            obj.entry("subjectClosure")
                .or_insert(json!([{"name": "Captured.program", "module": "Captured"}]));
            obj.entry("modelClosure")
                .or_insert(json!([{"name": "Trusted.MirSemantics.UnitTheorem", "module": "Trusted.MirSemantics"}]));
            obj.entry("specificationClosure")
                .or_insert(json!([{"name": "Spec.specs", "module": "Spec"}]));
            Value::Object(obj)
        };
        let with_base = |v: Value| base_closures(v.as_object().unwrap().clone());

        let clean = with_base(json!({"sorryDeclarations": [], "axioms": ["propext"]}));
        assert_eq!(validate_sorry_declarations(&clean, false).unwrap(), None);
        assert_eq!(validate_sorry_declarations(&clean, true).unwrap(), Some(Vec::new()));

        let with_sorry = with_base(json!({
            "sorryDeclarations": ["Proof.hole"],
            "axioms": ["propext", "sorryAx"],
        }));
        assert_eq!(
            validate_sorry_declarations(&with_sorry, true).unwrap(),
            Some(vec![json!("Proof.hole")])
        );
        let err = validate_sorry_declarations(&with_sorry, false).unwrap_err();
        assert_eq!(err.status, "tool_failed");
        assert_eq!(err.phase, "audit");
        assert!(err.detail.contains("sorryDeclarations"), "{}", err.detail);

        for (case, allow, expected_substr) in [
            (with_base(json!({"axioms": []})), false, "missing audit.sorryDeclarations"),
            (
                with_base(json!({"sorryDeclarations": [42], "axioms": []})),
                true,
                "malformed audit.sorryDeclarations",
            ),
            (with_base(json!({"sorryDeclarations": []})), false, "missing audit.axioms"),
            (
                with_base(json!({"sorryDeclarations": [], "axioms": [true]})),
                true,
                "malformed audit.axioms",
            ),
            (
                with_base(json!({"sorryDeclarations": [], "axioms": ["sorryAx"]})),
                false,
                "unexpected sorryAx",
            ),
            (
                with_base(json!({"sorryDeclarations": [], "axioms": ["sorryAx"]})),
                true,
                "inconsistent audit metadata",
            ),
            (
                with_base(json!({"sorryDeclarations": ["Proof.hole"], "axioms": ["propext"]})),
                true,
                "inconsistent audit metadata",
            ),
            (
                with_base(json!({"sorryDeclarations": [], "axioms": ["Lean.ofReduceBool"]})),
                false,
                "outside closed allowlist",
            ),
            (
                with_base(json!({"replay": false, "sorryDeclarations": [], "axioms": []})),
                false,
                "replay == true",
            ),
            (
                with_base(json!({"exactType": false, "sorryDeclarations": [], "axioms": []})),
                false,
                "exactType == true",
            ),
            (
                with_base(json!({"subjectClosure": [], "sorryDeclarations": [], "axioms": []})),
                false,
                "empty audit.subjectClosure",
            ),
        ] {
            let err = validate_sorry_declarations(&case, allow).unwrap_err();
            assert_eq!(err.status, "tool_failed", "{case}");
            assert_eq!(err.phase, "audit", "{case}");
            assert!(
                err.detail.contains(expected_substr),
                "{case}: expected `{expected_substr}` in `{}`",
                err.detail
            );
        }
    }

    #[test]
    fn extract_spec_warnings_validates_and_preserves_entries() {
        assert_eq!(extract_spec_warnings(&json!({})).unwrap(), Vec::<Value>::new());
        let with_warnings = json!({
            "specWarnings": [
                {
                    "code": "unsatisfiable_safety",
                    "declaration": "Spec.specs",
                    "message": "safety is False",
                    "body": "crate::f"
                },
                {
                    "code": "trivial_property",
                    "declaration": "Spec.specs",
                    "message": "property is True",
                    "body": null
                }
            ]
        });
        assert_eq!(
            extract_spec_warnings(&with_warnings).unwrap(),
            vec![
                json!({
                    "code": "unsatisfiable_safety",
                    "declaration": "Spec.specs",
                    "message": "safety is False",
                    "body": "crate::f"
                }),
                json!({
                    "code": "trivial_property",
                    "declaration": "Spec.specs",
                    "message": "property is True"
                }),
            ]
        );
        for bad in [
            json!({"specWarnings": "not-an-array"}),
            json!({"specWarnings": [123]}),
            json!({"specWarnings": [{"code": "", "declaration": "D", "message": "M"}]}),
            json!({"specWarnings": [{"code": "c", "declaration": "", "message": "M"}]}),
            json!({"specWarnings": [{"code": "c", "declaration": "D", "message": ""}]}),
            json!({"specWarnings": [{"code": "c", "declaration": "D", "message": "M", "body": ""}]}),
        ] {
            let err = extract_spec_warnings(&bad).unwrap_err();
            assert_eq!(err.status, "tool_failed");
            assert_eq!(err.phase, "audit");
        }
    }

    #[test]
    fn parse_module_file_arg_and_decl_spec_cover_edge_cases() {
        let parsed = parse_module_file_arg(OsStr::new("Contract=a/b=c/file.lean")).unwrap();
        assert_eq!(parsed.module, "Contract");
        assert_eq!(parsed.path, PathBuf::from("a/b=c/file.lean"));

        for invalid in ["NoEquals", "=path.lean", "Mod=", "7Bad=path.lean", "A..B=x"] {
            assert!(parse_module_file_arg(OsStr::new(invalid)).is_err(), "{invalid}");
        }

        assert_eq!(
            parse_decl_spec("Contract:StarnixEbpf.Contract.specs").unwrap(),
            DeclSpec {
                module: Some("Contract".to_owned()),
                decl: "StarnixEbpf.Contract.specs".to_owned(),
            }
        );
        assert_eq!(
            parse_decl_spec("Spec.specs").unwrap(),
            DeclSpec { module: None, decl: "Spec.specs".to_owned() }
        );
        for invalid in ["A:B:C", ":Decl", "Mod:", "7Bad:Decl", "Mod:7Bad", "Unqualified", "A..B"] {
            assert!(parse_decl_spec(invalid).is_err(), "{invalid}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn rustc_staging_handles_symlinks_common_prefix_roles_and_rejects_escapes() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let cas = dir.path().join("cas");
        fs::create_dir_all(&cas).unwrap();
        fs::write(cas.join("hash1.rs"), b"pub mod helper;\n").unwrap();
        fs::write(cas.join("hash2.rs"), b"pub fn id(x: u64) -> u64 { x }\n").unwrap();
        fs::write(cas.join("spec.lean"), b"-- spec\n").unwrap();
        fs::write(cas.join("proof.lean"), b"-- proof\n").unwrap();

        let runfiles = dir.path().join("runfiles/pkg/src");
        fs::create_dir_all(runfiles.join("sub")).unwrap();
        symlink(cas.join("hash1.rs"), runfiles.join("lib.rs")).unwrap();
        symlink(cas.join("hash2.rs"), runfiles.join("helper.rs")).unwrap();
        symlink(cas.join("spec.lean"), runfiles.join("SpecHelper.lean")).unwrap();
        symlink(cas.join("proof.lean"), runfiles.join("Spec.Alias.lean")).unwrap();

        let work = dir.path().join("work");
        fs::create_dir_all(&work).unwrap();
        let rustc = RustcArgs {
            crate_root: runfiles.join("./lib.rs"),
            crate_name: "sample".to_owned(),
            crate_type: CrateType::Lib,
            panic: PanicStrategy::Unwind,
            overflow_checks: false,
            edition: "2024".to_owned(),
            target: target(),
            cfg: vec!["foo".to_owned()],
            env: vec![("CARGO_PKG_VERSION".to_owned(), "0.8.64".to_owned())],
            source_file: vec![runfiles.join("lib.rs"), runfiles.join("helper.rs")],
            stdlib_crate: None,
            spec_file: vec![ModuleFileArg {
                module: "Contract".to_owned(),
                path: runfiles.join("SpecHelper.lean"),
            }],
            proof_file: vec![ModuleFileArg {
                module: "Spec.Helper".to_owned(),
                path: runfiles.join("Spec.Alias.lean"),
            }],
            spec_decl: DeclSpec {
                module: Some("Contract".to_owned()),
                decl: "Contract.specs".to_owned(),
            },
            theorem: DeclSpec {
                module: Some("Spec.Helper".to_owned()),
                decl: "Spec.Helper.verify".to_owned(),
            },
            select: Vec::new(),
            instantiate: Vec::new(),
        };
        let mut originals = Vec::new();
        let prepared = prepare_rustc_request(&rustc, &work, &mut originals).unwrap();
        let req = prepared.request;
        assert_eq!(req.compilation.source_root, Path::new("rust"));
        assert_eq!(req.compilation.crate_root, Path::new("lib.rs"));
        assert_eq!(
            req.compilation.env,
            BTreeMap::from([("CARGO_PKG_VERSION".to_owned(), "0.8.64".to_owned())])
        );
        assert_eq!(
            req.compilation.source_files,
            vec![PathBuf::from("helper.rs"), PathBuf::from("lib.rs")]
        );
        assert_eq!(req.proof.source_root, Path::new("authored"));
        assert_eq!(req.proof.sources.len(), 2);
        // Roles come strictly from --spec-file vs --proof-file, never name.
        assert_eq!(req.proof.sources[0].module, "Contract");
        assert!(matches!(req.proof.sources[0].role, AuthoredRole::Specification));
        assert_eq!(req.proof.sources[1].module, "Spec.Helper");
        assert!(matches!(req.proof.sources[1].role, AuthoredRole::Proof));
        assert_eq!(originals.len(), 4);

        // Relative paths in the same directory do not fail root collapse.
        let rel_work = dir.path().join("rel-work");
        fs::create_dir_all(&rel_work).unwrap();
        let rel_stage = rel_work.join("rust");
        fs::create_dir_all(&rel_stage).unwrap();
        let rel_rustc = RustcArgs {
            crate_root: PathBuf::from("./a/lib.rs"),
            source_file: vec![PathBuf::from("a/helper.rs")],
            ..RustcArgs {
                crate_root: runfiles.join("lib.rs"),
                crate_name: "sample".to_owned(),
                crate_type: CrateType::Lib,
                panic: PanicStrategy::Unwind,
                overflow_checks: false,
                edition: "2024".to_owned(),
                target: target(),
                cfg: Vec::new(),
                env: Vec::new(),
                source_file: Vec::new(),
                stdlib_crate: None,
                spec_file: Vec::new(),
                proof_file: Vec::new(),
                spec_decl: DeclSpec { module: None, decl: "Spec.specs".to_owned() },
                theorem: DeclSpec { module: None, decl: "Proof.verify".to_owned() },
                select: Vec::new(),
                instantiate: Vec::new(),
            }
        };
        assert_eq!(
            normalize_lexical(Path::new("./lib.rs")).unwrap().1,
            vec![OsString::from("lib.rs")]
        );
        assert!(normalize_lexical(Path::new("../lib.rs")).is_err());
        assert!(normalize_lexical(Path::new("a/../b.rs")).is_err());
        assert!(normalize_lexical(Path::new("")).is_err());

        // Mixed relative and absolute paths fail.
        let mut bad_mixed = RustcArgs {
            crate_root: PathBuf::from("lib.rs"),
            source_file: vec![runfiles.join("helper.rs")],
            ..rel_rustc
        };
        let mut orig2 = Vec::new();
        assert!(stage_rustc_rust_inputs(&bad_mixed, &rel_stage, &mut orig2).is_err());

        // Root collapse on disjoint absolute paths fails.
        bad_mixed.crate_root = PathBuf::from("/foo/lib.rs");
        bad_mixed.source_file = vec![PathBuf::from("/bar/helper.rs")];
        assert!(stage_rustc_rust_inputs(&bad_mixed, &rel_stage, &mut orig2).is_err());
    }

    #[test]
    fn scope_deserialization_rejects_extra_fields_on_crate_and_selected_unit() {
        assert_eq!(serde_json::from_str::<Scope>(r#"{"kind":"crate"}"#).unwrap(), Scope::Crate {});
        assert_eq!(serde_json::to_string(&Scope::Crate {}).unwrap(), r#"{"kind":"crate"}"#);
        assert_eq!(
            serde_json::from_str::<Scope>(r#"{"kind":"selected_unit","roots":["a","b","a"]}"#)
                .unwrap(),
            Scope::SelectedUnit {
                roots: BTreeSet::from(["a".to_owned(), "b".to_owned()]),
                instantiations: BTreeSet::new(),
            }
        );
        assert_eq!(
            serde_json::from_str::<Scope>(
                r#"{"kind":"selected_unit","roots":[],"instantiations":[{"path":"foo","args":["usize"]}]}"#
            )
            .unwrap(),
            Scope::SelectedUnit {
                roots: BTreeSet::new(),
                instantiations: BTreeSet::from([Instantiation {
                    path: "foo".to_owned(),
                    args: vec!["usize".to_owned()],
                }]),
            }
        );
        for invalid in [
            r#"{"kind":"crate","roots":["a"]}"#,
            r#"{"kind":"crate","roots":null}"#,
            r#"{"kind":"crate","instantiations":[]}"#,
            r#"{"kind":"crate","extra":1}"#,
            r#"{"kind":"selected_unit"}"#,
            r#"{"kind":"selected_unit","roots":null}"#,
            r#"{"kind":"selected_unit","roots":["a"],"extra":1}"#,
            r#"{"kind":"selected_unit","roots":[],"instantiations":[{"path":"foo","args":[],"extra":1}]}"#,
            r#"{"kind":"other"}"#,
        ] {
            assert!(
                serde_json::from_str::<Scope>(invalid).is_err(),
                "expected invalid scope JSON to fail: {invalid}"
            );
        }
    }

    #[test]
    fn bundled_correspondence_provenance_is_well_formed() {
        let provenance: Value = serde_json::from_str(CORRESPONDENCE_PROVENANCE_JSON)
            .expect("bundled correspondence provenance must be valid JSON");
        assert_eq!(provenance["schema_version"], 1);
        assert_eq!(provenance["upstream_repository"], "https://github.com/proofs-rs/lean-miri.git");
        assert_eq!(provenance["upstream_commit"], "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a");
        assert_eq!(
            provenance["sysroot_foundation_manifest_sha256"],
            crate::LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256
        );
        assert_eq!(provenance["upstream_pin_sha256"].as_str().unwrap().len(), 64);
        assert_eq!(provenance["correspondence_adapters"].as_object().unwrap().len(), 7);
        assert_eq!(provenance["patched_files"].as_array().unwrap().len(), 13);
        assert_eq!(provenance["correspondence_proofs"].as_object().unwrap().len(), 19);
        assert_eq!(provenance["trusted_lean"].as_object().unwrap().len(), 24);
    }

    #[cfg(not(feature = "setup"))]
    #[test]
    fn select_tools_requires_explicit_paths_without_setup_feature() {
        let base = VerifyArgs {
            format: VerifyFormat::Human,
            receipt_out: None,
            request: Some(PathBuf::from("request.json")),
            manifest_path: None,
            proof_dir: None,
            panic: None,
            overflow_checks: false,
            select: Vec::new(),
            instantiate: Vec::new(),
            features: Vec::new(),
            all_features: false,
            no_default_features: false,
            capture: None,
            lean: None,
            sysroot: None,
            artifacts: None,
            export_lean_lib: false,
            overwrite_artifacts: false,
            allow_unpinned_lean: false,
            allow_unsandboxed_elaboration: false,
            allow_sorry_in_proof: false,
            paranoid_quorum: false,
            allow_unstable_feature: Vec::new(),
            lean_memory_mb: None,
            no_cache: false,
            no_rebuild_bundled: false,
            shard: ShardArgs::default(),
            verify_shard_plan: None,
            command: None,
        };

        let cases = [
            (None, None, None, &["--capture", "--sysroot", "--lean"][..]),
            (Some(PathBuf::from("/tool/capture")), None, None, &["--sysroot", "--lean"][..]),
            (
                Some(PathBuf::from("/tool/capture")),
                Some(PathBuf::from("/tool/sysroot")),
                None,
                &["--lean"][..],
            ),
            (
                None,
                Some(PathBuf::from("/tool/sysroot")),
                Some(PathBuf::from("/tool/lean")),
                &["--capture"][..],
            ),
        ];

        for (capture, sysroot, lean, expected_missing) in cases {
            let args = VerifyArgs {
                format: VerifyFormat::Human,
                receipt_out: None,
                capture,
                sysroot,
                lean,
                request: base.request.clone(),
                manifest_path: None,
                proof_dir: None,
                panic: None,
                overflow_checks: false,
                select: Vec::new(),
                instantiate: Vec::new(),
                features: Vec::new(),
                all_features: false,
                no_default_features: false,
                artifacts: None,
                export_lean_lib: false,
                overwrite_artifacts: false,
                allow_unpinned_lean: false,
                allow_unsandboxed_elaboration: false,
                allow_sorry_in_proof: false,
                paranoid_quorum: false,
                allow_unstable_feature: Vec::new(),
                lean_memory_mb: None,
                no_cache: false,
                no_rebuild_bundled: false,
                shard: ShardArgs::default(),
                verify_shard_plan: None,
                command: None,
            };
            let err = select_tools(&args).err().expect("missing tools must fail");
            assert_eq!(err.status, "tool_failed");
            assert_eq!(err.phase, "capture-tool");
            assert!(
                err.detail.contains("explicit") && err.detail.contains("setup"),
                "{}",
                err.detail
            );
            for flag in expected_missing {
                assert!(err.detail.contains(flag), "{flag}: {}", err.detail);
            }
        }

        let complete = VerifyArgs {
            capture: Some(PathBuf::from("/tool/capture")),
            sysroot: Some(PathBuf::from("/tool/sysroot")),
            lean: Some(PathBuf::from("/tool/lean")),
            ..base
        };
        let selected = select_tools(&complete)
            .unwrap_or_else(|e| panic!("all explicit paths must succeed: {}", e.detail));
        assert_eq!(selected.capture, PathBuf::from("/tool/capture"));
        assert_eq!(selected.sysroot, Some(PathBuf::from("/tool/sysroot")));
        assert_eq!(selected.lean, Some(PathBuf::from("/tool/lean")));
    }

    #[test]
    fn rustc_mode_sorts_authored_modules_regardless_of_flag_order() {
        let project = tempfile::tempdir().unwrap();
        let lib = project.path().join("lib.rs");
        let spec_a = project.path().join("A.lean");
        let spec_b = project.path().join("B.lean");
        let proof = project.path().join("Proof.lean");
        fs::write(&lib, b"pub fn zero() -> u64 { 0 }\n").unwrap();
        fs::write(&spec_a, b"-- spec A\n").unwrap();
        fs::write(&spec_b, b"-- spec B\n").unwrap();
        fs::write(&proof, b"-- proof\n").unwrap();

        let make_args = |spec_files: Vec<ModuleFileArg>| RustcArgs {
            crate_root: lib.clone(),
            crate_name: "sample".to_owned(),
            crate_type: CrateType::Lib,
            panic: PanicStrategy::Unwind,
            overflow_checks: false,
            edition: "2024".to_owned(),
            target: "x86_64-unknown-linux-gnu".to_owned(),
            cfg: Vec::new(),
            env: Vec::new(),
            source_file: Vec::new(),
            stdlib_crate: None,
            spec_file: spec_files,
            proof_file: vec![ModuleFileArg { module: "Proof".to_owned(), path: proof.clone() }],
            spec_decl: DeclSpec {
                module: Some("SpecA".to_owned()),
                decl: "SpecA.specs".to_owned(),
            },
            theorem: DeclSpec { module: Some("Proof".to_owned()), decl: "Proof.verify".to_owned() },
            select: Vec::new(),
            instantiate: Vec::new(),
        };

        let work1 = tempfile::tempdir().unwrap();
        let mut orig1 = Vec::new();
        let p1 = prepare_rustc_request(
            &make_args(vec![
                ModuleFileArg { module: "SpecB".to_owned(), path: spec_b.clone() },
                ModuleFileArg { module: "SpecA".to_owned(), path: spec_a.clone() },
            ]),
            work1.path(),
            &mut orig1,
        )
        .unwrap();

        let work2 = tempfile::tempdir().unwrap();
        let mut orig2 = Vec::new();
        let p2 = prepare_rustc_request(
            &make_args(vec![
                ModuleFileArg { module: "SpecA".to_owned(), path: spec_a },
                ModuleFileArg { module: "SpecB".to_owned(), path: spec_b },
            ]),
            work2.path(),
            &mut orig2,
        )
        .unwrap();

        let mods1: Vec<_> = p1.authored.iter().map(|m| m.module.as_str()).collect();
        let mods2: Vec<_> = p2.authored.iter().map(|m| m.module.as_str()).collect();
        assert_eq!(mods1, vec!["Proof", "SpecA", "SpecB"]);
        assert_eq!(mods1, mods2);
        assert_eq!(encoded(&p1.request).unwrap(), encoded(&p2.request).unwrap());
    }

    #[test]
    fn proof_failed_export_lean_lib_fails_closed_on_ledger_or_fs_error() {
        let anneal_root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();

        // 1. Clean `proof_failed` (`code == 1`) with `--export-lean-lib` when
        //    no artifacts compiled yet returns `proof_failed` (exit 1).
        let checker_empty = Checker::new(anneal_root, Some(Path::new("/bin/sh"))).unwrap();
        let work_empty = tempfile::tempdir().unwrap();
        let clean_empty_err = handle_failed_target_audit(
            &checker_empty,
            work_empty.path(),
            true,
            Some("linux_bwrap"),
            crate::Failure::policy("headers", "header rejected"),
        );
        assert_eq!(clean_empty_err.status, "proof_failed");
        assert_eq!(clean_empty_err.phase, "audit");
        assert_eq!(clean_empty_err.elaboration_sandbox, Some("linux_bwrap"));
        assert_eq!(failure_exit_code(clean_empty_err.status), 1);

        // 2. Filesystem error during `--export-lean-lib` on `proof_failed`
        //    (`work/lean-lib` pre-existing as a regular file) must fail closed
        //    with `status == "tool_failed"`, `phase == "export-lean-lib"`,
        //    exit 2.
        let work_fs_err = tempfile::tempdir().unwrap();
        fs::write(work_fs_err.path().join("lean-lib"), b"blocker-file").unwrap();
        let fs_err = handle_failed_target_audit(
            &checker_empty,
            work_fs_err.path(),
            true,
            Some("linux_bwrap"),
            crate::Failure::policy("compile-Proof", "proof rejected"),
        );
        assert_eq!(fs_err.status, "tool_failed");
        assert_eq!(fs_err.phase, "export-lean-lib");
        assert_eq!(fs_err.elaboration_sandbox, Some("linux_bwrap"));
        assert_eq!(failure_exit_code(fs_err.status), 2);

        // 3. Unledgered `.olean` written directly into `stage/lib` (e.g. under
        //    `--allow-unsandboxed-elaboration`) must fail closed on both
        //    `proof_failed` and passing exports.
        let checker_unledgered = Checker::new(anneal_root, Some(Path::new("/bin/sh"))).unwrap();
        let lib_unledgered = checker_unledgered.stage().join("lib");
        fs::create_dir_all(&lib_unledgered).unwrap();
        fs::write(lib_unledgered.join("Rogue.olean"), b"rogue-bytes").unwrap();
        let work_unledgered = tempfile::tempdir().unwrap();
        let unledgered_err = handle_failed_target_audit(
            &checker_unledgered,
            work_unledgered.path(),
            true,
            Some("none"),
            crate::Failure::policy("compile-Proof", "proof rejected"),
        );
        assert_eq!(unledgered_err.status, "tool_failed");
        assert_eq!(unledgered_err.phase, "export-lean-lib");
        assert!(
            unledgered_err.detail.contains("unledgered artifact"),
            "unexpected detail: {}",
            unledgered_err.detail
        );
        assert_eq!(failure_exit_code(unledgered_err.status), 2);
        assert!(!work_unledgered.path().join("lean-lib").exists());

        let work_unledgered_pass = tempfile::tempdir().unwrap();
        let pass_unledgered_err = finalize_passing_artifacts(
            work_unledgered_pass.path(),
            b"{\"status\":\"verified\"}\n",
            true,
            |dest| checker_unledgered.export_target_oleans_gated(dest, true),
        )
        .unwrap_err();
        assert_eq!(pass_unledgered_err.status, "tool_failed");
        assert_eq!(pass_unledgered_err.phase, "export-lean-lib");
        assert!(!work_unledgered_pass.path().join("result.json").exists());
        assert!(!work_unledgered_pass.path().join("lean-lib").exists());

        // 4. Real `olean_ledger` export and tampering check on `proof_failed`:
        //    compile a valid `Spec` and a broken `Proof` via `Checker::run_target`
        //    (producing `Err(e)` with `e.code == 1` and `Spec.olean` recorded in
        //    `olean_ledger`), verify clean `proof_failed` exports `Spec.olean`
        //    while gating `Proof.olean`, then tamper `stage/lib/Spec.olean` and
        //    verify `handle_failed_target_audit` escalates to `tool_failed` /
        //    exit 2.
        let lean_bin = crate::default_lean_path();
        if lean_bin.is_file() {
            let src_dir = tempfile::tempdir().unwrap();
            let sources = [
                (
                    "Model",
                    TargetRole::Model,
                    "prelude\nimport Init.Prelude\nimport Init.Core\n\
                     namespace Trusted.MirSemantics\n\
                     structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                     def UnitTheorem (c : Crate) : Prop := c.specs c.program\n\
                     end Trusted.MirSemantics\n",
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
                    "prelude\nimport Expected\n\
                     theorem Proof.verify : Expected.claim := True.intro\n",
                ),
            ];
            let modules: Vec<TargetModule> = sources
                .iter()
                .map(|(name, role, text)| {
                    let path = src_dir.path().join(format!("{name}.lean"));
                    fs::write(&path, text.as_bytes()).unwrap();
                    TargetModule {
                        module: (*name).to_owned(),
                        source: path,
                        expected_sha256: sha256_bytes(text.as_bytes()),
                        role: *role,
                    }
                })
                .collect();

            let mut checker_ledger = Checker::new(anneal_root, Some(&lean_bin)).unwrap();
            let req = TargetAuditRequest {
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
                    request_sha256: "0".repeat(64),
                    capture_sha256: "0".repeat(64),
                    model_manifest_sha256: "0".repeat(64),
                    specification_manifest_sha256: "0".repeat(64),
                },
            };
            let run_err = checker_ledger.run_target(&req).unwrap_err();
            assert_eq!(run_err.code, 1, "expected policy failure, got: {run_err}");

            let promoted_spec = checker_ledger.stage().join("lib/Spec.olean");
            assert!(promoted_spec.is_file(), "expected Spec.olean after {run_err}");

            let work_ok = tempfile::tempdir().unwrap();
            let clean_err = handle_failed_target_audit(
                &checker_ledger,
                work_ok.path(),
                true,
                Some("linux_bwrap"),
                crate::Failure::policy("compile-Proof", "proof rejected"),
            );
            assert_eq!(clean_err.status, "proof_failed");
            assert_eq!(clean_err.phase, "audit");
            assert_eq!(failure_exit_code(clean_err.status), 1);
            assert!(work_ok.path().join("lean-lib/Spec.olean").is_file());
            assert!(!work_ok.path().join("lean-lib/Proof.olean").exists());

            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(&promoted_spec, fs::Permissions::from_mode(0o600)).unwrap();
            }
            fs::write(&promoted_spec, b"tampered-spec-olean").unwrap();

            let work_ledger = tempfile::tempdir().unwrap();
            let ledger_err = handle_failed_target_audit(
                &checker_ledger,
                work_ledger.path(),
                true,
                Some("linux_bwrap"),
                run_err,
            );
            assert_eq!(ledger_err.status, "tool_failed");
            assert_eq!(ledger_err.phase, "export-lean-lib");
            assert!(
                ledger_err.detail.contains("changed before export"),
                "unexpected detail: {}",
                ledger_err.detail
            );
            assert_eq!(failure_exit_code(ledger_err.status), 2);
            assert!(
                !work_ledger.path().join("lean-lib").exists(),
                "tool_failed ledger mismatch must not leave a partial lean-lib"
            );
        }
    }

    #[test]
    fn finalize_passing_artifacts_keeps_result_and_lean_lib_atomic_on_tool_failed() {
        // 1. If `result.json` cannot be written, `export` is never invoked and
        //    no `lean-lib` directory is created.
        let work_write_fail = tempfile::tempdir().unwrap();
        fs::create_dir(work_write_fail.path().join("result.json")).unwrap();
        let mut export_called = false;
        let err = finalize_passing_artifacts(
            work_write_fail.path(),
            b"{\"status\":\"verified\"}\n",
            true,
            |_| {
                export_called = true;
                Ok(true)
            },
        )
        .unwrap_err();
        assert_eq!(err.status, "tool_failed");
        assert_eq!(err.phase, "staging");
        assert!(!export_called, "export must not run when writing result.json fails");
        assert!(
            !work_write_fail.path().join("lean-lib").exists(),
            "tool_failed must never leave a promoted lean-lib"
        );

        // 2. If `export` fails after `result.json` was written, `result.json`
        //    is rolled back so `tool_failed` leaves neither a success receipt
        //    nor a `lean-lib`.
        let work_export_fail = tempfile::tempdir().unwrap();
        let err = finalize_passing_artifacts(
            work_export_fail.path(),
            b"{\"status\":\"verified\"}\n",
            true,
            |_| Err(crate::Failure::operational("export-lean-lib", "simulated ENOSPC")),
        )
        .unwrap_err();
        assert_eq!(err.status, "tool_failed");
        assert_eq!(err.phase, "export-lean-lib");
        assert!(err.detail.contains("simulated ENOSPC"), "{}", err.detail);
        assert!(
            !work_export_fail.path().join("result.json").exists(),
            "failed export must remove pre-written success result.json"
        );
        assert!(
            !work_export_fail.path().join("lean-lib").exists(),
            "failed export must not leave lean-lib behind"
        );

        // 3. When both succeed, both `result.json` and `lean-lib` are present.
        let work_ok = tempfile::tempdir().unwrap();
        finalize_passing_artifacts(work_ok.path(), b"{\"status\":\"verified\"}\n", true, |dest| {
            fs::create_dir_all(dest).unwrap();
            fs::write(dest.join("Proof.olean"), b"ok").unwrap();
            Ok(true)
        })
        .unwrap();
        assert_eq!(
            fs::read(work_ok.path().join("result.json")).unwrap(),
            b"{\"status\":\"verified\"}\n"
        );
        assert!(work_ok.path().join("lean-lib/Proof.olean").is_file());

        // 4. If `export` fails and rolling back `result.json` also fails (for
        //    example when the staging directory becomes read-only), the error
        //    marks `suppress_retention` and `retain_stage(..., false)` refuses
        //    to publish the stale success receipt.
        #[cfg(unix)]
        if unsafe { libc::geteuid() } != 0 {
            use std::os::unix::fs::PermissionsExt;
            let work_ro = tempfile::tempdir().unwrap();
            let ro_path = work_ro.path().to_path_buf();
            let err =
                finalize_passing_artifacts(&ro_path, b"{\"status\":\"verified\"}\n", true, |_| {
                    fs::set_permissions(&ro_path, fs::Permissions::from_mode(0o500)).unwrap();
                    Err(crate::Failure::operational("export-lean-lib", "simulated EROFS"))
                })
                .unwrap_err();
            fs::set_permissions(&ro_path, fs::Permissions::from_mode(0o700)).unwrap();
            assert_eq!(err.status, "tool_failed");
            assert_eq!(err.phase, "export-lean-lib");
            assert!(err.suppress_retention);
            assert!(
                err.detail.contains("failed to roll back"),
                "unexpected detail: {}",
                err.detail
            );
            let retain_parent = tempfile::tempdir().unwrap();
            let retain_dest = retain_parent.path().join("retained");
            let retain_err = retain_stage(&ro_path, &retain_dest, false).unwrap_err();
            assert_eq!(retain_err.phase, "retention");
            assert!(!retain_dest.exists(), "failed retention must never publish stale result.json");
        }
    }

    #[cfg(unix)]
    #[test]
    fn normalize_lexical_absolute_preserves_symlinked_sysroot_topology() {
        let dir = tempfile::tempdir().unwrap();
        let target = dir.path().join("cas-tree");
        fs::create_dir_all(&target).unwrap();
        let link = dir.path().join("logical-sysroot");
        std::os::unix::fs::symlink(&target, &link).unwrap();

        let messy = link.join("subdir/..");
        let normalized = normalize_lexical_absolute(&messy).unwrap();
        assert_eq!(normalized, link);
        assert_ne!(normalized, fs::canonicalize(&link).unwrap());
    }

    #[test]
    fn env_binding_validation_blocks_empty_keys_equals_smuggling_and_nul() {
        assert_eq!(
            parse_env_arg("CARGO_PKG_VERSION=0.8.64").unwrap(),
            ("CARGO_PKG_VERSION".to_owned(), "0.8.64".to_owned())
        );
        assert_eq!(parse_env_arg("NESTED=a=b").unwrap(), ("NESTED".to_owned(), "a=b".to_owned()));
        assert_eq!(parse_env_arg("EMPTY=").unwrap(), ("EMPTY".to_owned(), String::new()));

        assert!(parse_env_arg("NO_EQUALS").is_err());
        assert!(parse_env_arg("=val").is_err());
        assert!(validate_env_binding("", "val").is_err());
        // JSON request objects could otherwise smuggle `--env=A=B=C` via key
        // `"A=B"`.
        assert!(validate_env_binding("A=B", "C").is_err());
        assert!(validate_env_binding("A\0B", "C").is_err());
        assert!(validate_env_binding("A", "B\0C").is_err());
    }

    #[test]
    fn compilation_request_env_normalizes_order_and_changes_request_digest() {
        let req_a: Request = serde_json::from_value(json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "env": { "Z": "2", "A": "1" },
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "selected_unit", "roots": ["f"] },
            "proof": { "source_root": ".", "sources": [] }
        }))
        .unwrap();
        let req_a_reordered: Request = serde_json::from_value(json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "env": { "A": "1", "Z": "2" },
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "selected_unit", "roots": ["f"] },
            "proof": { "source_root": ".", "sources": [] }
        }))
        .unwrap();
        let req_b: Request = serde_json::from_value(json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "env": { "A": "1", "Z": "3" },
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "selected_unit", "roots": ["f"] },
            "proof": { "source_root": ".", "sources": [] }
        }))
        .unwrap();

        let digest_a = sha256_bytes(&encoded(&req_a).unwrap());
        let digest_a_reordered = sha256_bytes(&encoded(&req_a_reordered).unwrap());
        let digest_b = sha256_bytes(&encoded(&req_b).unwrap());
        assert_eq!(digest_a, digest_a_reordered);
        assert_ne!(digest_a, digest_b);
    }

    #[test]
    fn compilation_crate_type_and_panic_default_to_lib_unwind_and_accept_bin_abort() {
        let defaulted: Request = serde_json::from_value(json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "crate" },
            "proof": { "source_root": ".", "sources": [] }
        }))
        .unwrap();
        assert_eq!(defaulted.compilation.crate_type, CrateType::Lib);
        assert_eq!(defaulted.compilation.panic, PanicStrategy::Unwind);

        let bin_abort: Request = serde_json::from_value(json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "main.rs",
                "crate_name": "demo_bin",
                "crate_type": "bin",
                "panic": "abort",
                "source_files": ["main.rs"]
            },
            "scope": { "kind": "selected_unit", "roots": ["guarded_exit"] },
            "proof": { "source_root": ".", "sources": [] }
        }))
        .unwrap();
        assert_eq!(bin_abort.compilation.crate_type, CrateType::Bin);
        assert_eq!(bin_abort.compilation.panic, PanicStrategy::Abort);
        assert_ne!(encoded(&defaulted).unwrap(), encoded(&bin_abort).unwrap());

        // `overflow_checks` defaults to `false`, which is left out of the
        // encoding so existing request digests are unchanged.
        assert!(!defaulted.compilation.overflow_checks);
        let defaulted_json = String::from_utf8(encoded(&defaulted).unwrap()).unwrap();
        assert!(!defaulted_json.contains("overflow_checks"), "{defaulted_json}");
        let mut checked = defaulted.clone();
        checked.compilation.overflow_checks = true;
        let checked_json = String::from_utf8(encoded(&checked).unwrap()).unwrap();
        assert!(checked_json.contains("\"overflow_checks\": true"), "{checked_json}");
        let decoded: Request = serde_json::from_str(&checked_json).unwrap();
        assert!(decoded.compilation.overflow_checks);
    }

    #[test]
    fn resolve_cargo_package_cfg_handles_features_and_rejects_active_dependencies() {
        let pkg = json!({
            "name": "ext_crate",
            "features": {
                "default": ["std"],
                "std": ["alloc"],
                "alloc": [],
                "i128": [],
                "weak_log": ["log?/kv"],
                "logging": ["dep:log"],
                "strong_core": ["core/default"]
            },
            "dependencies": [
                {
                    "name": "quickcheck",
                    "rename": null,
                    "kind": "dev",
                    "optional": false
                },
                {
                    "name": "log",
                    "rename": null,
                    "kind": null,
                    "optional": true
                },
                {
                    "name": "rustc-std-workspace-core",
                    "rename": "core",
                    "kind": null,
                    "optional": true
                }
            ]
        });

        // Default run activates `default` -> `std` -> `alloc`, ignoring dev
        // and unactivated optional dependencies.
        let default_cfg = resolve_cargo_package_cfg(&pkg, &[], false, false).unwrap();
        assert_eq!(
            default_cfg,
            BTreeSet::from([
                "feature=\"alloc\"".to_owned(),
                "feature=\"default\"".to_owned(),
                "feature=\"std\"".to_owned(),
            ])
        );

        // `--no-default-features` leaves `cfg` empty.
        let bare_cfg = resolve_cargo_package_cfg(&pkg, &[], false, true).unwrap();
        assert!(bare_cfg.is_empty());

        // Comma- and space-separated `--features` with weak `log?/kv` leave
        // optional `log` unactivated, emitting sorted `feature="..."` cfgs.
        let custom_cfg = resolve_cargo_package_cfg(
            &pkg,
            &["i128, alloc".to_owned(), "weak_log".to_owned()],
            false,
            true,
        )
        .unwrap();
        assert_eq!(
            custom_cfg,
            BTreeSet::from([
                "feature=\"alloc\"".to_owned(),
                "feature=\"i128\"".to_owned(),
                "feature=\"weak_log\"".to_owned(),
            ])
        );

        // Activating `dep:log` or `core/default` (directly or via
        // `--all-features`) fails closed as `unsupported` in phase `cargo`.
        for (feats, all_feats, expected_substr) in [
            (vec!["logging".to_owned()], false, "activates dependency `log`"),
            (vec!["strong_core".to_owned()], false, "activates dependency `core`"),
            (Vec::new(), true, "activates dependency"),
            (vec!["dep:log".to_owned()], false, "cannot activate dependency feature"),
            (vec!["log/kv".to_owned()], false, "cannot activate dependency feature"),
            (vec!["unknown".to_owned()], false, "does not have feature `unknown`"),
            (vec!["unknown".to_owned()], true, "does not have feature `unknown`"),
        ] {
            let err = resolve_cargo_package_cfg(&pkg, &feats, all_feats, true).unwrap_err();
            assert_eq!(err.status, "unsupported");
            assert_eq!(err.phase, "cargo");
            assert!(
                err.detail.contains(expected_substr),
                "expected `{expected_substr}` in `{}`",
                err.detail
            );
        }

        // `--all-features` passes when no feature enables an optional dep.
        let pure_pkg = json!({
            "name": "pure_crate",
            "features": {
                "default": ["std"],
                "std": [],
                "i128": []
            },
            "dependencies": [
                { "name": "rand", "rename": null, "kind": "dev", "optional": false }
            ]
        });
        let all_cfg = resolve_cargo_package_cfg(&pure_pkg, &[], true, false).unwrap();
        assert_eq!(
            all_cfg,
            BTreeSet::from([
                "feature=\"default\"".to_owned(),
                "feature=\"i128\"".to_owned(),
                "feature=\"std\"".to_owned(),
            ])
        );

        // Required normal or build dependencies fail closed even under
        // `--no-default-features`.
        for kind in [Value::Null, json!("build")] {
            let dep_pkg = json!({
                "name": "with_dep",
                "features": {},
                "dependencies": [
                    { "name": "dep", "rename": null, "kind": kind, "optional": false }
                ]
            });
            let err = resolve_cargo_package_cfg(&dep_pkg, &[], false, true).unwrap_err();
            assert_eq!(err.status, "unsupported");
            assert_eq!(err.phase, "cargo");
            assert!(err.detail.contains("dependency-free crate"), "{}", err.detail);
        }

        // Unsafe characters in manifest feature keys fail closed.
        let unsafe_feat_pkg = json!({
            "name": "bad_feat",
            "features": { "bad\"quote": [] },
            "dependencies": []
        });
        let err = resolve_cargo_package_cfg(&unsafe_feat_pkg, &[], false, true).unwrap_err();
        assert_eq!(err.status, "unsupported");
        assert_eq!(err.phase, "cargo");
    }

    #[test]
    fn validate_and_extract_candidate_features_enforces_tier_policy_and_closure() {
        use crate::CandidateFeature;

        let model_modules = BTreeSet::from([
            "Trusted".to_owned(),
            "Trusted.MirAst".to_owned(),
            "Trusted.MirSemantics".to_owned(),
            "Trusted.Memory".to_owned(),
            "Trusted.Refinement".to_owned(),
            "Trusted.Unused".to_owned(),
        ]);
        let model_tiers = BTreeMap::from([
            ("Trusted".to_owned(), TrustTier::Vetted),
            ("Trusted.MirAst".to_owned(), TrustTier::Candidate(CandidateFeature::MirAst)),
            (
                "Trusted.MirSemantics".to_owned(),
                TrustTier::Candidate(CandidateFeature::MirSemantics),
            ),
            ("Trusted.Memory".to_owned(), TrustTier::Candidate(CandidateFeature::Memory)),
            ("Trusted.Refinement".to_owned(), TrustTier::Candidate(CandidateFeature::Refinement)),
            ("Trusted.Unused".to_owned(), TrustTier::Candidate(CandidateFeature::StepResult)),
        ]);

        // Only candidate features reached by `modelClosure` appear, sorted
        // lexicographically (`"memory"` before `"refinement"`, despite enum
        // declaration order), ignoring unreached candidate modules (`Unused`).
        let valid_audit = json!({
            "graph": {
                "Trusted": [{"module": "Init.Prelude", "isMeta": false, "isExported": true}],
                "Trusted.MirAst": [{"module": "Trusted", "isMeta": false, "isExported": true}],
                "Trusted.MirSemantics": [
                    {"module": "Trusted.MirAst", "isMeta": false, "isExported": true}
                ],
                "Trusted.Memory": [],
                "Trusted.Refinement": [],
                "Trusted.Unused": []
            },
            "modelClosure": [
                {"name": "Trusted.Refinement.step", "module": "Trusted.Refinement"},
                {"name": "Trusted.MirSemantics.UnitTheorem", "module": "Trusted.MirSemantics"},
                {"name": "Trusted.MirAst.Fn", "module": "Trusted.MirAst"},
                {"name": "Trusted.Memory.read", "module": "Trusted.Memory"},
                {"name": "Captured.program", "module": "Captured"},
                {"name": "Trusted.ok", "module": "Trusted"}
            ]
        });
        assert_eq!(
            validate_and_extract_candidate_features(&valid_audit, &model_tiers, &model_modules)
                .unwrap(),
            vec!["memory", "mir_ast", "mir_semantics", "refinement"]
        );

        // Vetted-only closure yields an empty candidate feature list.
        let vetted_only = json!({
            "graph": {
                "Trusted": [],
                "Trusted.MirAst": [],
                "Trusted.MirSemantics": [],
                "Trusted.Memory": []
            },
            "modelClosure": [{"name": "Trusted.ok", "module": "Trusted"}]
        });
        assert!(
            validate_and_extract_candidate_features(&vetted_only, &model_tiers, &model_modules)
                .unwrap()
                .is_empty()
        );

        // Vetted importing a candidate module must fail closed.
        let vetted_imports_candidate = json!({
            "graph": {
                "Trusted": [{"module": "Trusted.MirAst", "isMeta": false, "isExported": true}],
                "Trusted.MirAst": [],
                "Trusted.MirSemantics": [],
                "Trusted.Memory": []
            },
            "modelClosure": [{"name": "Trusted.ok", "module": "Trusted"}]
        });
        let err = validate_and_extract_candidate_features(
            &vetted_imports_candidate,
            &model_tiers,
            &model_modules,
        )
        .unwrap_err();
        assert_eq!(err.status, "tool_failed");
        assert!(err.detail.contains("cannot import candidate:mir_ast"), "{}", err.detail);
    }

    #[cfg(unix)]
    #[test]
    fn write_receipt_out_atomic_rejects_swapped_parent_directory() {
        let root = tempfile::tempdir().unwrap();
        let dir_a = root.path().join("dir-a");
        let dir_b = root.path().join("dir-b");
        let dir_old = root.path().join("dir-a-old");
        fs::create_dir(&dir_a).unwrap();
        fs::create_dir(&dir_b).unwrap();

        let receipt_path = dir_a.join("receipt.json");
        let args = VerifyArgs {
            command: None,
            request: None,
            manifest_path: None,
            proof_dir: None,
            panic: None,
            overflow_checks: false,
            select: Vec::new(),
            instantiate: Vec::new(),
            features: Vec::new(),
            all_features: false,
            no_default_features: false,
            artifacts: None,
            receipt_out: Some(receipt_path.clone()),
            format: crate::output::VerifyFormat::Json,
            capture: None,
            sysroot: None,
            lean: None,
            no_cache: false,
            no_rebuild_bundled: false,
            export_lean_lib: false,
            overwrite_artifacts: false,
            lean_memory_mb: None,
            allow_unsandboxed_elaboration: false,
            allow_sorry_in_proof: false,
            allow_unstable_feature: Vec::new(),
            allow_unpinned_lean: false,
            paranoid_quorum: false,
            shard: ShardArgs::default(),
            verify_shard_plan: None,
        };
        let validated = validate_receipt_out_pre_stage(&args, None).unwrap().unwrap();

        // Swap `dir-a` with another real directory (`dir-b`) before persisting.
        fs::rename(&dir_a, &dir_old).unwrap();
        fs::rename(&dir_b, &dir_a).unwrap();

        let err = write_receipt_out_atomic(&validated, "{}").unwrap_err();
        assert!(err.contains("changed before write"), "unexpected error: {err}");
        assert!(!dir_a.join("receipt.json").exists());
        assert!(!dir_old.join("receipt.json").exists());

        // `rollback_retained_artifacts` deletes a newly created retained
        // directory so a post-retention receipt commit failure leaves no
        // orphaned passing evidence on disk.
        let retained_dir = root.path().join("retained-ev");
        fs::create_dir(&retained_dir).unwrap();
        fs::write(retained_dir.join("result.json"), b"{}").unwrap();
        let detail =
            rollback_retained_artifacts(retained_dir.to_str(), "receipt persist failed".to_owned());
        assert_eq!(detail, "receipt persist failed");
        assert!(!retained_dir.exists());

        // Late `check_receipt_out_candidate` aliasing rejections must suppress
        // both receipt-out writes and `--artifacts` retention for both
        // non-existent and existing candidate paths.
        let alias_err =
            check_receipt_out_candidate(&validated, &validated.canon_target).unwrap_err();
        assert_eq!(alias_err.status, "tool_failed");
        assert_eq!(alias_err.phase, "receipt-out");
        assert!(alias_err.suppress_receipt_out);
        assert!(alias_err.suppress_retention);

        let existing_file = root.path().join("existing-input.json");
        fs::write(&existing_file, b"{}").unwrap();
        let existing_args = VerifyArgs { receipt_out: Some(existing_file.clone()), ..args };
        let existing_validated =
            validate_receipt_out_pre_stage(&existing_args, None).unwrap().unwrap();
        let existing_err =
            check_receipt_out_candidate(&existing_validated, &existing_file).unwrap_err();
        assert_eq!(existing_err.status, "tool_failed");
        assert_eq!(existing_err.phase, "receipt-out");
        assert!(existing_err.suppress_receipt_out);
        assert!(existing_err.suppress_retention);
    }
}
