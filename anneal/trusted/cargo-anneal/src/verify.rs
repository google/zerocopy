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
    collections::{BTreeMap, BTreeSet},
    ffi::{OsStr, OsString},
    fs,
    path::{Component, Path, PathBuf},
    process::{Command, ExitCode},
    time::Instant,
};

use cargo_anneal::{
    ActiveSandbox, Checker, SandboxMode, TOOLCHAIN, TargetAuditRequest, TargetBindings,
    TargetModule, TargetRole, read_regular_file_deref, read_regular_file_strict, sha256_bytes,
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

// Generated resources keep installed and packaged builds independent of the
// source checkout. The explicit regeneration check binds these bytes to the
// canonical audited sources without running a build hook.
include!("bundled_resources.rs");

const PINNED_CAPTURE_SCHEMA_VERSION: u32 = 4;
const PINNED_RUSTC_COMMIT: &str = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1";
const RECEIPT_SCHEMA_VERSION: u32 = 3;

/// Closed 3-element set of verification taint atoms projected onto Receipt
/// Schema v3 (`taint_reasons`), sorted lexicographically by wire spelling.
/// Variant declaration order must match lexicographical `as_str()` order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum VerificationTaint {
    SorryInProof,
    UnpinnedLean,
    UnsandboxedElaboration,
}

impl VerificationTaint {
    const fn as_str(self) -> &'static str {
        match self {
            Self::SorryInProof => "sorry_in_proof",
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
    #[arg(long, conflicts_with_all = ["manifest_path", "proof_dir", "panic", "select"])]
    request: Option<PathBuf>,
    /// A feature-free library or binary crate for the x86_64-unknown-linux-gnu scalar profile.
    #[arg(long, conflicts_with = "request", requires = "proof_dir")]
    manifest_path: Option<PathBuf>,
    /// Directory containing Spec.lean and Proof.lean, for the Cargo shortcut.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    proof_dir: Option<PathBuf>,
    /// Panic strategy (`unwind` or `abort`) for the Cargo shortcut.
    #[arg(long, value_enum, requires = "manifest_path", conflicts_with = "request")]
    panic: Option<PanicStrategy>,
    /// Select a function by its compiler path; omit to require the whole crate.
    #[arg(long, requires = "manifest_path", conflicts_with = "request")]
    select: Vec<String>,
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
    /// Export compiled `.olean*` files to `<artifacts>/lean-lib/`.
    #[arg(long, global = true)]
    export_lean_lib: bool,
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
                || !self.select.is_empty()
            {
                return Err(cmd.error(
                    ErrorKind::ArgumentConflict,
                    "--request, --manifest-path, --proof-dir, parent --panic, and parent \
                     --select cannot be used with the `rustc` subcommand",
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
    #[serde(default = "edition")]
    edition: String,
    #[serde(default = "target")]
    target: String,
    #[serde(default)]
    cfg: BTreeSet<String>,
    #[serde(default)]
    env: BTreeMap<String, String>,
    source_files: Vec<PathBuf>,
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Scope {
    SelectedUnit { roots: BTreeSet<String> },
    // Empty struct variant (not unit) so `deny_unknown_fields` rejects extra
    // keys such as `roots` on `{"kind":"crate"}`.
    Crate {},
}

impl Scope {
    const fn root_theorem(&self) -> &'static str {
        match self {
            Self::Crate {} => "CrateTheorem",
            Self::SelectedUnit { .. } => "UnitTheorem",
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

#[derive(Deserialize)]
struct CaptureProgram {
    scope: Scope,
    #[serde(rename = "bodies")]
    _bodies: serde::de::IgnoredAny,
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
    // Capture schema 4 widens integer widths to `i128`, encodes 128-bit bit
    // patterns as canonical decimal strings, and adds `char`, `Ordering`,
    // `(T, bool)` overflow pairs, unary/overflow/division/comparison ops, and
    // `IntToInt` casts on top of schema 3's `program.scope`, `with_retag`
    // flags, and source identities. Check the schema version and compiler
    // commit before strict deserialization so older capture ABIs report a clear
    // version mismatch. Request schema 1 is independent.
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
}

type Result<T> = std::result::Result<T, Error>;

fn error(status: &'static str, phase: &'static str, detail: impl ToString) -> Error {
    Error {
        status,
        phase,
        detail: detail.to_string(),
        elaboration_sandbox: None,
        suppress_retention: false,
    }
}

fn io(phase: &'static str, failure: std::io::Error) -> Error {
    error("tool_failed", phase, failure)
}

fn identifier(value: &str) -> bool {
    !value.is_empty() && value.split('.').all(cargo_anneal::is_lean_ident)
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
    matches!(module, "Expected" | "Captured")
        || matches!(
            module.split('.').next(),
            Some(
                "Trusted"
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

fn encoded<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    serde_json::to_vec_pretty(value).map_err(|e| error("tool_failed", "json", e))
}

/// Reject Cargo or toolchain override files under `dir`.
///
/// Uses `symlink_metadata` (without following links) so dangling symlinks are
/// rejected; a plain `.cargo` directory is allowed when it contains no config
/// file, whereas a `.cargo` symlink, non-directory entry (`!meta.is_dir()`),
/// or any non-`NotFound` metadata error fails closed.
fn reject_compiler_overrides(dir: &Path) -> Result<()> {
    for forbidden in
        [".cargo", ".cargo/config", ".cargo/config.toml", "rust-toolchain", "rust-toolchain.toml"]
    {
        match fs::symlink_metadata(dir.join(forbidden)) {
            Ok(meta) if forbidden != ".cargo" || !meta.is_dir() => {
                return Err(error(
                    "unsupported",
                    "cargo",
                    "compiler overrides need an explicit configured compilation",
                ));
            }
            Ok(_) => {}
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
            Err(err) => return Err(io("cargo", err)),
        }
    }
    Ok(())
}

// Cargo is an input-discovery shortcut, not a second verification profile.
// Reject configurations this adapter cannot reproduce before building the
// same explicit request consumed by the build-neutral path.
fn cargo_request(args: &VerifyArgs, manifest: &Path) -> Result<(Request, PathBuf)> {
    let manifest = fs::canonicalize(manifest).map_err(|e| io("cargo", e))?;
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
    let package = metadata["packages"]
        .as_array()
        .and_then(|packages| {
            packages.iter().find(|p| p["manifest_path"].as_str() == manifest.to_str())
        })
        .ok_or_else(|| {
            error("unsupported", "cargo", "choose a package Cargo.toml, not a virtual workspace")
        })?;
    if package["features"].as_object().is_none_or(|features| !features.is_empty()) {
        return Err(error(
            "unsupported",
            "cargo",
            "Cargo features require an explicit configured compilation request",
        ));
    }
    if package["dependencies"].as_array().is_none_or(|deps| !deps.is_empty()) {
        return Err(error(
            "unsupported",
            "cargo",
            "Cargo shortcut requires a dependency-free crate; use an explicit compilation request",
        ));
    }
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
    let mut primary_targets = targets.iter().filter_map(|t| {
        let kinds = t["kind"].as_array()?;
        if kinds.iter().any(|k| k == "bin") {
            Some((CrateType::Bin, t))
        } else if kinds.iter().any(|k| k == "lib") {
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
    let workspace_root =
        metadata["workspace_root"].as_str().and_then(|root| fs::canonicalize(root).ok());
    for ancestor in source_root.ancestors() {
        reject_compiler_overrides(ancestor)?;
        if workspace_root.as_deref() == Some(ancestor) {
            break;
        }
    }
    let crate_root = Path::new(target_meta["src_path"].as_str().unwrap_or_default())
        .strip_prefix(&source_root)
        .map_err(|_| error("unsupported", "cargo", "target root escapes package"))?
        .to_path_buf();
    // This shortcut declares a namespace of .rs files. Other compiler inputs
    // require an explicit request: importing every package file would also
    // stage unrelated data, proof packages and build outputs.
    let mut source_files = Vec::new();
    for entry in
        walkdir::WalkDir::new(&source_root).follow_links(false).into_iter().filter_entry(|e| {
            e.depth() == 0
                || (!e.file_name().to_string_lossy().starts_with('.') && e.file_name() != "target")
        })
    {
        let entry = entry.map_err(|e| error("tool_failed", "cargo", e))?;
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "rs") {
            source_files.push(entry.path().strip_prefix(&source_root).unwrap().to_path_buf());
        }
    }
    source_files.sort();
    let proof_root = fs::canonicalize(args.proof_dir.as_ref().ok_or_else(|| {
        error("unsupported", "request", "--proof-dir is required with --manifest-path")
    })?)
    .map_err(|e| io("proof", e))?;
    let mut sources = Vec::new();
    for entry in walkdir::WalkDir::new(&proof_root)
        .follow_links(false)
        .into_iter()
        .filter_entry(|e| e.depth() == 0 || !e.file_name().to_string_lossy().starts_with('.'))
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
    let scope = if args.select.is_empty() {
        Scope::Crate {}
    } else {
        Scope::SelectedUnit { roots: args.select.iter().cloned().collect() }
    };
    Ok((
        Request {
            schema_version: 1,
            compilation: Compilation {
                source_root,
                crate_root,
                crate_name: target_meta["name"].as_str().unwrap_or_default().replace('-', "_"),
                crate_type,
                panic: args.panic.unwrap_or_default(),
                edition: target_meta["edition"].as_str().unwrap_or("2024").to_owned(),
                target: target(),
                cfg: BTreeSet::new(),
                env: BTreeMap::new(),
                source_files,
            },
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
        manifest.parent().unwrap().to_path_buf(),
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

    let scope = if rustc.select.is_empty() {
        Scope::Crate {}
    } else {
        Scope::SelectedUnit { roots: rustc.select.iter().cloned().collect() }
    };
    let request = Request {
        schema_version: 1,
        compilation: Compilation {
            source_root: PathBuf::from("rust"),
            crate_root,
            crate_name: rustc.crate_name.clone(),
            crate_type: rustc.crate_type,
            panic: rustc.panic,
            edition: rustc.edition.clone(),
            target: rustc.target.clone(),
            cfg: rustc.cfg.iter().cloned().collect(),
            env: rustc.env.iter().cloned().collect(),
            source_files,
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
    #[cfg(feature = "setup")]
    {
        let needs_discovery =
            args.capture.is_none() || args.sysroot.is_none() || args.lean.is_none();
        let installed = if needs_discovery {
            installed_bundle().map_err(|detail| error("tool_failed", "capture-tool", detail))?
        } else {
            None
        };
        let tools = resolve_tools(
            ToolOverrides {
                capture: args.capture.clone(),
                sysroot: args.sysroot.clone(),
                lean: args.lean.clone(),
            },
            installed.as_ref(),
            std::env::current_exe(),
        )
        .map_err(|detail| error("tool_failed", "capture-tool", detail))?;
        let prebuilt_dir = if args.lean.is_none() {
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
        match (&args.capture, &args.sysroot, &args.lean) {
            (Some(capture), Some(sysroot), Some(lean)) => Ok(SelectedTools {
                capture: capture.clone(),
                sysroot: Some(sysroot.clone()),
                lean: Some(lean.clone()),
                prebuilt_dir: None,
            }),
            _ => {
                let mut missing = Vec::new();
                if args.capture.is_none() {
                    missing.push("--capture");
                }
                if args.sysroot.is_none() {
                    missing.push("--sysroot");
                }
                if args.lean.is_none() {
                    missing.push("--lean");
                }
                Err(error(
                    "tool_failed",
                    "capture-tool",
                    format!(
                        "missing {}; explicit --capture, --sysroot, and --lean tool paths are \
                         required when built without the `setup` feature",
                        missing.join(", ")
                    ),
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

    let abs = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()?.join(path)
    };
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

fn run(args: &VerifyArgs, work: &Path) -> Result<Value> {
    let start = Instant::now();
    let mut originals = Vec::new();
    let (request, base, pre_staged_rust, pre_staged_lean, symlink_policy) =
        if let Some(VerifySubcommand::Rustc(rustc)) = &args.command {
            let prepared = prepare_rustc_request(rustc, work, &mut originals)?;
            (
                prepared.request,
                work.to_path_buf(),
                Some(prepared.sources),
                Some(prepared.authored),
                SymlinkPolicy::DereferenceRegular,
            )
        } else {
            let (request, base) = load_request(args)?;
            (request, base, None, None, SymlinkPolicy::Reject)
        };
    if request.schema_version != 1 || request.compilation.source_files.is_empty() {
        return Err(error("unsupported", "request", "unsupported or empty compilation request"));
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
        let source_root = root(&base, &request.compilation.source_root)?;
        fs::create_dir_all(&rust_stage).map_err(|e| io("staging", e))?;
        let mut sources = Vec::new();
        let mut paths = BTreeSet::new();
        for relative in &request.compilation.source_files {
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
        if !paths.contains(&request.compilation.crate_root) {
            return Err(error("unsupported", "inputs", "crate_root is not a declared source"));
        }
        sources
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
    let capture_tool_path = tools.capture.clone();
    let capture = fs::canonicalize(&capture_tool_path).map_err(|e| {
        error(
            "tool_failed",
            "capture-tool",
            format!("cannot inspect {}: {e}", capture_tool_path.display()),
        )
    })?;
    let (_, capture_binary_sha256) =
        read_regular_file_strict(&capture, Some(&capture), "capture-tool")
            .map_err(|e| error("tool_failed", "capture-tool", e.message))?;
    let capture_dir = work.join("capture");
    // Capture reserves and publishes a new output directory itself; precreating
    // it here would violate its create-only publication contract.
    // Do not let a target crate's ambient compiler wrappers or search paths
    // enter the capture process. The only added library path below comes
    // from the operator-selected compiler installation.
    let mut command = Command::new(&capture);
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .args(["capture", "--crate-root"])
        .arg(rust_stage.join(&request.compilation.crate_root))
        .args([
            "--crate-name",
            &request.compilation.crate_name,
            "--crate-type",
            request.compilation.crate_type.as_str(),
            "--panic",
            request.compilation.panic.as_str(),
            "--edition",
            &request.compilation.edition,
            "--target",
            &request.compilation.target,
            "--out-dir",
        ])
        .arg(&capture_dir)
        .current_dir(&rust_stage);
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
    match &request.scope {
        Scope::Crate {} => {
            command.args(["--scope", "crate"]);
        }
        Scope::SelectedUnit { roots } => {
            if roots.is_empty() {
                return Err(error("unsupported", "request", "empty selected scope"));
            }
            for name in roots {
                command.arg("--select").arg(name);
            }
        }
    }
    // Preserve each cfg as option data through capture's parser. Capture must
    // use the joined form again when rebuilding compiler argv: the pinned
    // response-file expansion gate is "arg.strip_prefix('@')", before --cfg
    // parsing. Extracting the String must not restore a standalone @file arg.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/args.rs#L14-L32
    for cfg in &request.compilation.cfg {
        command.arg(format!("--cfg={cfg}"));
    }
    // Pass each explicit compile-time environment binding in joined `--env=...`
    // form so keys starting with `-` stay option data and capture populates
    // `rustc`'s logical environment without inheriting ambient process env.
    for (key, value) in &request.compilation.env {
        command.arg(format!("--env={key}={value}"));
    }
    for source in &sources {
        command.arg("--source-file").arg(rust_stage.join(&source.relative_path));
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
                eprint!("{}", String::from_utf8_lossy(&output.stderr));
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
    if manifest.program.scope != request.scope
        || manifest.configuration["crate_name"] != request.compilation.crate_name
        || manifest.configuration["crate_type"] != request.compilation.crate_type.as_str()
        || manifest.configuration["panic"] != request.compilation.panic.as_str()
        || manifest.configuration["target"] != request.compilation.target
        || manifest.configuration["edition"] != request.compilation.edition
        || manifest.configuration["cfg"] != json!(request.compilation.cfg)
        || manifest.configuration["env"] != json!(request.compilation.env)
    {
        return Err(error(
            "tool_failed",
            "capture",
            "capture differs from the requested compilation or scope",
        ));
    }
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

    let bundle = work.join("anneal");
    let mut modules = Vec::new();
    let mut model_identity: Vec<(String, String)> = Vec::new();
    // Installed theory remains proof code even though it ships with the
    // model. Only primitive trusted modules may determine the canonical
    // proposition; packaging must not promote proof helpers into its TCB.
    for (relative, text) in BUNDLE {
        let path = bundle.join(relative);
        write(&path, text.as_bytes())?;
        let file_sha256 = sha256_bytes(text.as_bytes());
        model_identity.push(((*relative).to_owned(), file_sha256.clone()));
        if relative.ends_with(".lean") && relative.starts_with("trusted/lean/") {
            modules.push(TargetModule {
                module: relative
                    .trim_start_matches("trusted/lean/")
                    .trim_end_matches(".lean")
                    .replace('/', "."),
                source: path,
                expected_sha256: file_sha256,
                role: TargetRole::Model,
            });
        }
    }
    let bundled_theory = cargo_anneal::bundle::embedded_theory_bundle().map_err(|e| {
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
    let captured_lean = capture_dir.join("Captured.lean");
    modules.push(TargetModule {
        module: "Captured".to_owned(),
        expected_sha256: sha256_bytes(&fs::read(&captured_lean).map_err(|e| io("capture", e))?),
        source: captured_lean,
        role: TargetRole::Capture,
    });

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
    if !modules
        .iter()
        .any(|m| m.module == spec_module && matches!(m.role, TargetRole::Specification))
        || !modules
            .iter()
            .any(|m| m.module == theorem_module && matches!(m.role, TargetRole::Proof))
    {
        return Err(error(
            "unsupported",
            "proof",
            "specification and theorem must have their declared source roles",
        ));
    }
    // Keep the reviewed specification identity separate from ordinary
    // proof edits. The auditor also checks actual compiled dependencies,
    // so a helper that changes a specification's meaning needs its role.
    let specification_manifest_sha256 = sha256_bytes(&encoded(&spec_identity)?);
    let root_name = request.scope.root_theorem();
    // Only validated declaration identifiers enter this fixed template. The
    // authored proof package never supplies an expected proposition or model.
    let header = "-- Copyright 2026 The Fuchsia Authors\n--\n-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n-- This file may not be copied, modified, or distributed except according to\n-- those terms.\n\n";
    let expected = format!(
        "{header}prelude\nimport Trusted.MirSemantics\nimport Captured\nimport {spec_module}\n\nnamespace Expected\ndef claim : Prop := _root_.Trusted.MirSemantics.{root_name} (_root_.Trusted.MirSemantics.Crate.mk _root_.Captured.program _root_.{})\nend Expected\n",
        request.proof.specification
    );
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
    let audit_result = checker.run_target(&audit_request);
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
    let taints = active_taints(args);
    let taint_reasons = taint_reason_strings(&taints);
    let status = request.scope.verified_status(!taints.is_empty());
    let correspondence_provenance: Value = if args.allow_unpinned_lean {
        json!({
            "applicable": false,
            "reason": format!(
                "unpinned Lean toolchain; bundled Pass 2 correspondence provenance \
                 applies only to pinned {TOOLCHAIN}"
            ),
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
    let runtime_libs_verified = checker
        .admitted()
        .map_err(|e| {
            error("tool_failed", "toolchain", e.message).with_sandbox(Some(active_sandbox.as_str()))
        })?
        .runtime_libs_verified;
    let toolchain_identity = if args.allow_unpinned_lean {
        json!({
            "sha256_locked": [],
            "sha256_recorded": [
                "capture executable as capture_binary_sha256",
                "unpinned Lean executable and admitted Init/Std sysroot modules in unpinned_lean and audit.unpinnedLean",
            ],
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
                "Lean sysroot Init/Std/Lean .olean artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules",
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Lean sysroot .ir/.ir.sig companions outside the locks",
                "Rust compiler and sysroot, identified by their reported commit",
            ],
        })
    } else {
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules",
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Lean shared libraries, identified by lean --version",
                "Lean sysroot .ir/.ir.sig companions outside the locks",
                "Rust compiler and sysroot, identified by their reported commit",
            ],
        })
    };
    let lean_assumption = if args.allow_unpinned_lean {
        "unpinned Lean kernel and dynamically discovered Init/Std foundation"
    } else {
        "Lean kernel and admitted foundation"
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
    let mut assumptions: Vec<&str> = vec![
        "faithful pinned compiler capture",
        "experimental pointer-free MIR semantics",
        lean_assumption,
        "intact compiler and verification environment",
    ];
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
    let mut result = json!({
        "schema_version": RECEIPT_SCHEMA_VERSION,
        "status": status,
        "taint_reasons": taint_reasons,
        "elaboration_sandbox": active_sandbox.as_str(),
        "experimental": true,
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
    if let Some(sorry_decls) = validate_sorry_declarations(&audit, args.allow_sorry_in_proof)
        .map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?
    {
        result
            .as_object_mut()
            .unwrap()
            .insert("sorry_declarations".into(), Value::Array(sorry_decls));
    }
    let spec_warnings =
        extract_spec_warnings(&audit).map_err(|e| e.with_sandbox(Some(active_sandbox.as_str())))?;
    result
        .as_object_mut()
        .unwrap()
        .insert("spec_warnings".into(), Value::Array(spec_warnings));
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
    export: impl FnOnce(&Path) -> std::result::Result<bool, cargo_anneal::Failure>,
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
            entry
                .as_object_mut()
                .unwrap()
                .insert("body".into(), Value::String(body.to_owned()));
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
    err: cargo_anneal::Failure,
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

fn emit_failure(
    taint_reasons: &[&str],
    elaboration_sandbox: Option<&str>,
    status: &str,
    phase: &str,
    detail: &str,
    artifacts: Option<Option<&str>>,
    code: u8,
) -> ExitCode {
    let receipt = FailureReceipt {
        schema_version: RECEIPT_SCHEMA_VERSION,
        taint_reasons,
        elaboration_sandbox,
        status,
        phase,
        detail,
        artifacts,
    };
    println!("{}", serde_json::to_string(&receipt).expect("serializable failure receipt"));
    ExitCode::from(code)
}

pub fn main(args: VerifyArgs) -> ExitCode {
    let taints = active_taints(&args);
    for taint in &taints {
        eprintln!("{}", taint.warning_banner());
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
    let stage = match verification_stage() {
        Ok(stage) => stage,
        Err(failure) => {
            return emit_failure(
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
    let outcome = run(&args, stage.path());
    if let Err(failure) = &outcome
        && failure.suppress_retention
    {
        let code = failure_exit_code(failure.status);
        return emit_failure(
            taint_reasons,
            failure.elaboration_sandbox,
            failure.status,
            failure.phase,
            &failure.detail,
            if artifacts.is_some() { None } else { Some(None) },
            code,
        );
    }
    // Retention is create-only. A caller cannot accidentally overwrite a proof
    // package or an earlier verification receipt by choosing an existing path.
    let retained = if let Some(destination) = artifacts {
        match retain_stage(stage.path(), Path::new(destination), outcome.is_ok()) {
            Ok(()) => Some(destination),
            Err(failure) => {
                let sandbox = match &outcome {
                    Err(err) => err.elaboration_sandbox,
                    Ok(res) => res.get("elaboration_sandbox").and_then(Value::as_str),
                };
                return emit_failure(
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
    match outcome {
        Ok(mut result) => {
            if let Some(path) = retained {
                result["artifacts"] = json!(path);
            }
            if let Some(warnings) = result.get("spec_warnings").and_then(Value::as_array) {
                for warning in warnings {
                    let code = warning.get("code").and_then(Value::as_str).unwrap_or("unknown");
                    let decl =
                        warning.get("declaration").and_then(Value::as_str).unwrap_or("<unknown>");
                    let msg = warning.get("message").and_then(Value::as_str).unwrap_or("");
                    match warning.get("body").and_then(Value::as_str) {
                        Some(body) => {
                            eprintln!("WARNING [anti-vacuity: {code}] {decl} (body `{body}`): {msg}");
                        }
                        None => eprintln!("WARNING [anti-vacuity: {code}] {decl}: {msg}"),
                    }
                }
            }
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
            ExitCode::SUCCESS
        }
        Err(failure) => {
            let code = failure_exit_code(failure.status);
            emit_failure(
                taint_reasons,
                failure.elaboration_sandbox,
                failure.status,
                failure.phase,
                &failure.detail,
                Some(retained),
                code,
            )
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
    Ok(())
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
            "Expected",
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
        assert!(reject_compiler_overrides(dir.path()).is_err());
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

    #[test]
    fn old_capture_schema_reports_version_mismatch_before_strict_deserialization() {
        for legacy in [
            br#"{"schema_version":2,"compiler":{"commit":"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"},"legacy":true}"#.as_slice(),
            br#"{"schema_version":3,"compiler":{"commit":"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"},"legacy":true}"#.as_slice(),
        ] {
            let Err(err) = parse_capture_receipt(legacy) else {
                panic!("legacy schema receipt must be rejected");
            };
            assert_eq!(err.status, "tool_failed");
            assert_eq!(err.phase, "capture");
            assert_eq!(err.detail, "unexpected capture schema or compiler");
        }

        // Schema 4 receipts carrying 128-bit decimal string constants above
        // `u64::MAX` inside `program.bodies` parse cleanly without arbitrary
        // JSON number precision.
        let schema4_u128 = br#"{
            "schema_version": 4,
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
        assert!(parse_capture_receipt(schema4_u128).is_ok());
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
            artifacts: None,
        })
        .unwrap();
        assert_eq!(omitted["schema_version"], 3);
        assert_eq!(omitted["taint_reasons"], json!([]));
        assert!(omitted.get("tainted").is_none(), "{omitted}");
        assert!(omitted.get("artifacts").is_none(), "{omitted}");
        assert!(omitted.get("elaboration_sandbox").is_none(), "{omitted}");

        let explicit_null: Value = serde_json::to_value(FailureReceipt {
            schema_version: RECEIPT_SCHEMA_VERSION,
            taint_reasons: &["unpinned_lean"],
            elaboration_sandbox: None,
            status: "unsupported",
            phase: "capture",
            detail: "bad item",
            artifacts: Some(None),
        })
        .unwrap();
        assert_eq!(explicit_null["taint_reasons"], json!(["unpinned_lean"]));
        assert!(explicit_null.get("unpinned_lean").is_none());
        assert!(explicit_null.get("elaboration_sandbox").is_none());
        assert_eq!(explicit_null.get("artifacts"), Some(&Value::Null), "{explicit_null}");

        let retained: Value = serde_json::to_value(FailureReceipt {
            schema_version: RECEIPT_SCHEMA_VERSION,
            taint_reasons: &[],
            elaboration_sandbox: Some("linux_bwrap"),
            status: "proof_failed",
            phase: "audit",
            detail: "mismatch",
            artifacts: Some(Some("/tmp/evidence")),
        })
        .unwrap();
        assert_eq!(retained["artifacts"], "/tmp/evidence");
        assert_eq!(retained["elaboration_sandbox"], "linux_bwrap");
    }

    #[test]
    fn taint_monoid_projects_all_eight_flag_subsets_canonically() {
        let all = [
            VerificationTaint::SorryInProof,
            VerificationTaint::UnpinnedLean,
            VerificationTaint::UnsandboxedElaboration,
        ];
        for pair in all.windows(2) {
            assert!(pair[0] < pair[1], "{pair:?}");
            assert!(pair[0].as_str() < pair[1].as_str(), "{pair:?}");
        }
        let base = VerifyArgs {
            request: Some(PathBuf::from("request.json")),
            manifest_path: None,
            proof_dir: None,
            panic: None,
            select: Vec::new(),
            capture: None,
            lean: None,
            sysroot: None,
            artifacts: None,
            export_lean_lib: false,
            allow_unpinned_lean: false,
            allow_unsandboxed_elaboration: false,
            allow_sorry_in_proof: false,
            paranoid_quorum: false,
            lean_memory_mb: None,
            no_cache: false,
            no_rebuild_bundled: false,
            command: None,
        };
        let crate_scope = Scope::Crate {};
        let unit_scope = Scope::SelectedUnit { roots: BTreeSet::from(["foo".to_owned()]) };

        for sorry in [false, true] {
            for unpinned in [false, true] {
                for unsandboxed in [false, true] {
                    let args = VerifyArgs {
                        allow_sorry_in_proof: sorry,
                        allow_unpinned_lean: unpinned,
                        allow_unsandboxed_elaboration: unsandboxed,
                        request: base.request.clone(),
                        manifest_path: None,
                        proof_dir: None,
                        panic: None,
                        select: Vec::new(),
                        capture: None,
                        lean: None,
                        sysroot: None,
                        artifacts: None,
                        export_lean_lib: false,
                        paranoid_quorum: false,
                        lean_memory_mb: None,
                        no_cache: false,
                        no_rebuild_bundled: false,
                        command: None,
                    };
                    let taints = active_taints(&args);
                    let reasons = taint_reason_strings(&taints);
                    let mut expected = Vec::new();
                    if sorry {
                        expected.push("sorry_in_proof");
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
            edition: "2024".to_owned(),
            target: target(),
            cfg: vec!["foo".to_owned()],
            env: vec![("CARGO_PKG_VERSION".to_owned(), "0.8.64".to_owned())],
            source_file: vec![runfiles.join("lib.rs"), runfiles.join("helper.rs")],
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
                edition: "2024".to_owned(),
                target: target(),
                cfg: Vec::new(),
                env: Vec::new(),
                source_file: Vec::new(),
                spec_file: Vec::new(),
                proof_file: Vec::new(),
                spec_decl: DeclSpec { module: None, decl: "Spec.specs".to_owned() },
                theorem: DeclSpec { module: None, decl: "Proof.verify".to_owned() },
                select: Vec::new(),
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
            Scope::SelectedUnit { roots: BTreeSet::from(["a".to_owned(), "b".to_owned()]) }
        );
        for invalid in [
            r#"{"kind":"crate","roots":["a"]}"#,
            r#"{"kind":"crate","roots":null}"#,
            r#"{"kind":"crate","extra":1}"#,
            r#"{"kind":"selected_unit"}"#,
            r#"{"kind":"selected_unit","roots":null}"#,
            r#"{"kind":"selected_unit","roots":["a"],"extra":1}"#,
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
            cargo_anneal::LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256
        );
        assert_eq!(provenance["upstream_pin_sha256"].as_str().unwrap().len(), 64);
        assert_eq!(provenance["correspondence_adapters"].as_object().unwrap().len(), 7);
        assert_eq!(provenance["patched_files"].as_array().unwrap().len(), 13);
        assert_eq!(provenance["correspondence_proofs"].as_object().unwrap().len(), 16);
        assert_eq!(provenance["trusted_lean"].as_object().unwrap().len(), 21);
    }

    #[cfg(not(feature = "setup"))]
    #[test]
    fn select_tools_requires_explicit_paths_without_setup_feature() {
        let base = VerifyArgs {
            request: Some(PathBuf::from("request.json")),
            manifest_path: None,
            proof_dir: None,
            panic: None,
            select: Vec::new(),
            capture: None,
            lean: None,
            sysroot: None,
            artifacts: None,
            export_lean_lib: false,
            allow_unpinned_lean: false,
            allow_unsandboxed_elaboration: false,
            allow_sorry_in_proof: false,
            paranoid_quorum: false,
            lean_memory_mb: None,
            no_cache: false,
            no_rebuild_bundled: false,
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
                capture,
                sysroot,
                lean,
                request: base.request.clone(),
                manifest_path: None,
                proof_dir: None,
                panic: None,
                select: Vec::new(),
                artifacts: None,
                export_lean_lib: false,
                allow_unpinned_lean: false,
                allow_unsandboxed_elaboration: false,
                allow_sorry_in_proof: false,
                paranoid_quorum: false,
                lean_memory_mb: None,
                no_cache: false,
                no_rebuild_bundled: false,
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
            edition: "2024".to_owned(),
            target: "x86_64-unknown-linux-gnu".to_owned(),
            cfg: Vec::new(),
            env: Vec::new(),
            source_file: Vec::new(),
            spec_file: spec_files,
            proof_file: vec![ModuleFileArg { module: "Proof".to_owned(), path: proof.clone() }],
            spec_decl: DeclSpec {
                module: Some("SpecA".to_owned()),
                decl: "SpecA.specs".to_owned(),
            },
            theorem: DeclSpec { module: Some("Proof".to_owned()), decl: "Proof.verify".to_owned() },
            select: Vec::new(),
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
            cargo_anneal::Failure::policy("headers", "header rejected"),
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
            cargo_anneal::Failure::policy("compile-Proof", "proof rejected"),
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
            cargo_anneal::Failure::policy("compile-Proof", "proof rejected"),
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
        let lean_bin = cargo_anneal::default_lean_path();
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
                cargo_anneal::Failure::policy("compile-Proof", "proof rejected"),
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
            |_| Err(cargo_anneal::Failure::operational("export-lean-lib", "simulated ENOSPC")),
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
                    Err(cargo_anneal::Failure::operational("export-lean-lib", "simulated EROFS"))
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
        assert_eq!(
            parse_env_arg("NESTED=a=b").unwrap(),
            ("NESTED".to_owned(), "a=b".to_owned())
        );
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
    }
}
