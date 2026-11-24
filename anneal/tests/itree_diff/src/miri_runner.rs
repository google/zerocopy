// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Miri execution authority discovering `miri` from the active compiler sysroot
//! or explicit environment overrides (never silently skewing toolchains), with
//! offline file-locked `cargo miri setup` sysroot caching and anchored UB
//! diagnostic parsing.

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::{OsStr, OsString},
    fmt,
    fs::{self, File},
    io::{self, Read},
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

use anneal_testkit::{Invocation, ProcessOutcome, Termination};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    outcome::{AuthorityRunResult, CallerFrameLaw, TerminalOutcome, sha256_hex},
    rustc_runner::{
        DYLIB_PATH_ENV_VAR, atomic_write_file, build_child_path,
        canonicalize_preserving_rustup_proxy_with_suffix, exe_name, exe_name_for_suffix,
        forward_env_keys_with_env, forward_platform_temp_and_profile_env_with_env,
        is_rustup_executable_name, is_rustup_proxy_executable, join_dylib_path,
        parse_and_validate_host_target_triple, resolve_candidate_exe_with_suffix,
        resolve_explicit_or_path_exe_with_suffix, resolve_rustup_env_for_sysroot_with_env,
        resolve_verified_backing_sysroot_with_suffix, run_probe_supervised,
        run_probe_supervised_with_timeout, run_supervised_with_prefix,
        sysroots_equivalent_with_suffix,
    },
    spec::{
        TraceTestCase, parse_pre_abort_stdout_with_expected_args, parse_pre_entry_slots_stdout,
        parse_trace_json_stdout_with_expected_args, render_standalone_rust_harness,
    },
    trace_observer::{ObservableSpine, PRE_ABORT_JSON_PREFIX, PRE_ENTRY_JSON_PREFIX},
};

const MIRI_SETUP_TIMEOUT_SECS: u64 = 300;
const MIRI_RUN_TIMEOUT_SECS: u64 = 120;
const MIRI_SYSROOT_IDENTITY_SCHEMA: u32 = 4;
const MIRI_BUILT_ARTIFACTS_SCHEMA: u32 = 1;
const MIRI_BUILT_ARTIFACTS_FILE: &str = ".anneal-itree-miri-artifacts.json";
const STREAM_HASH_BUF_BYTES: usize = 64 * 1024;
const MAX_TREE_HASH_WORKERS: usize = 8;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct MiriBuiltArtifactsManifest {
    schema_version: u32,
    composite_sha256: String,
    target: String,
    file_count: usize,
    tree_sha256: String,
}

/// Structured content-addressed identity for a cached Miri target sysroot,
/// binding `rustc -vV` (and its resolved `host:` target triple), `rustc`
/// binary and host library SHA-256 digests, `miri --version --verbose`, `miri`,
/// `cargo`, and `cargo-miri` binary SHA-256 digests, and a complete recursive
/// SHA-256 digest of all `rust-src` files under `lib/rustlib/src/rust`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MiriSysrootIdentity {
    pub schema_version: u32,
    pub target: String,
    pub rustc_vv: String,
    pub rustc_bin_sha256: String,
    pub rustc_host_libs_sha256: String,
    pub miri_version_verbose: String,
    pub miri_bin_sha256: String,
    pub cargo_bin_sha256: Option<String>,
    pub cargo_miri_bin_sha256: Option<String>,
    pub rust_src_sha256: String,
    pub composite_sha256: String,
}

impl MiriSysrootIdentity {
    /// Compute the composite Miri sysroot cache identity from `rust_sysroot`,
    /// `miri_bin`, and optional `cargo_bin`. Fails closed when `rustc`, `miri`,
    /// `cargo` (when provided), host sysroot libraries, or `rust-src` inputs
    /// are missing or unreadable, or when `rustc -vV` reports an unsupported
    /// target architecture.
    pub fn compute(
        rust_sysroot: &Path,
        miri_bin: &Path,
        cargo_bin: Option<&Path>,
    ) -> Result<Self, String> {
        Self::compute_with_suffix(rust_sysroot, miri_bin, cargo_bin, env::consts::EXE_SUFFIX)
    }

    /// Suffix-parameterized variant of [`Self::compute`] so unit tests can
    /// exercise Windows `.exe` executable discovery on Unix hosts.
    pub fn compute_with_suffix(
        rust_sysroot: &Path,
        miri_bin: &Path,
        cargo_bin: Option<&Path>,
        exe_suffix: &str,
    ) -> Result<Self, String> {
        let dylib_path = join_dylib_path(&rust_sysroot.join("lib"));
        let rustc_exe = exe_name_for_suffix("rustc", exe_suffix);
        let rustc_bin = rust_sysroot.join("bin").join(&rustc_exe);
        let rustc_vv = run_version_cmd(&rustc_bin, &["-vV"], &dylib_path)?;
        let target = parse_and_validate_host_target_triple(&rustc_vv)?;
        let backing_sysroot =
            resolve_verified_backing_sysroot_with_suffix(rust_sysroot, exe_suffix)?;
        let rustc_bin_sha256 = match backing_sysroot
            .as_ref()
            .map(|b| b.join("bin").join(&rustc_exe))
            .filter(|p| p.is_file())
        {
            Some(backing_rustc) => sha256_file_pair(&rustc_bin, &backing_rustc)?,
            None => sha256_file(&rustc_bin)?,
        };
        let rustc_host_libs_sha256 =
            compute_rustc_host_libs_digest(rust_sysroot, backing_sysroot.as_deref())?;
        let miri_version_verbose =
            run_version_cmd(miri_bin, &["--version", "--verbose"], &dylib_path)?;
        let miri_bin_sha256 = sha256_file(miri_bin)?;
        let cargo_bin_sha256 = match cargo_bin {
            Some(cb) => Some(sha256_file(cb)?),
            None => None,
        };
        let cargo_miri_bin_sha256 = match resolve_cargo_miri_binary_with_suffix(
            rust_sysroot,
            miri_bin,
            cargo_bin,
            exe_suffix,
        ) {
            Some(cm) => Some(sha256_file(&cm)?),
            None => None,
        };
        let rust_src_sha256 = compute_rust_src_digest(rust_sysroot, backing_sysroot.as_deref())?;
        let composite_sha256 = compute_composite_miri_sha256(
            MIRI_SYSROOT_IDENTITY_SCHEMA,
            &target,
            &rustc_vv,
            &rustc_bin_sha256,
            &rustc_host_libs_sha256,
            &miri_version_verbose,
            &miri_bin_sha256,
            cargo_bin_sha256.as_deref(),
            cargo_miri_bin_sha256.as_deref(),
            &rust_src_sha256,
        );
        Ok(Self {
            schema_version: MIRI_SYSROOT_IDENTITY_SCHEMA,
            target,
            rustc_vv,
            rustc_bin_sha256,
            rustc_host_libs_sha256,
            miri_version_verbose,
            miri_bin_sha256,
            cargo_bin_sha256,
            cargo_miri_bin_sha256,
            rust_src_sha256,
            composite_sha256,
        })
    }

    /// 32-hex-character (128-bit) prefix used in cache directory and lockfile
    /// names.
    pub fn cache_dir_tag(&self) -> &str {
        &self.composite_sha256[..32]
    }

    /// Persist this structured identity into `ready_stamp` atomically as pretty
    /// JSON.
    pub fn write_ready_stamp(&self, ready_stamp: &Path) -> Result<(), String> {
        let mut json = serde_json::to_string_pretty(self)
            .map_err(|e| format!("serialize Miri ready stamp: {e}"))?;
        json.push('\n');
        atomic_write_file(ready_stamp, json.as_bytes())
    }

    /// Hash every built regular file under `<sysroot_dir>/lib/rustlib` and
    /// atomically persist `.anneal-itree-miri-artifacts.json` bound to `self`.
    pub fn write_built_artifacts_manifest(&self, sysroot_dir: &Path) -> Result<(), String> {
        let (file_count, tree_sha256) =
            compute_built_miri_sysroot_digest(sysroot_dir, &self.target)?;
        let manifest = MiriBuiltArtifactsManifest {
            schema_version: MIRI_BUILT_ARTIFACTS_SCHEMA,
            composite_sha256: self.composite_sha256.clone(),
            target: self.target.clone(),
            file_count,
            tree_sha256,
        };
        let mut json = serde_json::to_string_pretty(&manifest)
            .map_err(|e| format!("serialize Miri artifacts manifest: {e}"))?;
        json.push('\n');
        atomic_write_file(&sysroot_dir.join(MIRI_BUILT_ARTIFACTS_FILE), json.as_bytes())
    }

    /// Verify `.anneal-itree-miri-artifacts.json` matches `self` and every
    /// regular built file under `<sysroot_dir>/lib/rustlib` matches its digest.
    pub fn validate_built_artifacts_manifest(&self, sysroot_dir: &Path) -> bool {
        let stamp_path = sysroot_dir.join(MIRI_BUILT_ARTIFACTS_FILE);
        let Ok(sym) = fs::symlink_metadata(&stamp_path) else {
            return false;
        };
        if !sym.file_type().is_file() {
            return false;
        }
        let Ok(raw) = fs::read_to_string(&stamp_path) else {
            return false;
        };
        let Ok(stored) = serde_json::from_str::<MiriBuiltArtifactsManifest>(&raw) else {
            return false;
        };
        if stored.schema_version != MIRI_BUILT_ARTIFACTS_SCHEMA
            || stored.composite_sha256 != self.composite_sha256
            || stored.target != self.target
            || stored.file_count == 0
        {
            return false;
        }
        let Ok((actual_count, actual_sha)) =
            compute_built_miri_sysroot_digest(sysroot_dir, &self.target)
        else {
            return false;
        };
        actual_count == stored.file_count && actual_sha == stored.tree_sha256
    }

    /// Validate that `ready_stamp` exists, parses as [`MiriSysrootIdentity`],
    /// matches `self` on every field, and carries an internally consistent
    /// `composite_sha256`.
    pub fn validate_ready_stamp(&self, ready_stamp: &Path) -> bool {
        let Ok(raw) = fs::read_to_string(ready_stamp) else {
            return false;
        };
        let Ok(stored) = serde_json::from_str::<Self>(&raw) else {
            return false;
        };
        if stored.schema_version != MIRI_SYSROOT_IDENTITY_SCHEMA || &stored != self {
            return false;
        }
        let recomputed = compute_composite_miri_sha256(
            stored.schema_version,
            &stored.target,
            &stored.rustc_vv,
            &stored.rustc_bin_sha256,
            &stored.rustc_host_libs_sha256,
            &stored.miri_version_verbose,
            &stored.miri_bin_sha256,
            stored.cargo_bin_sha256.as_deref(),
            stored.cargo_miri_bin_sha256.as_deref(),
            &stored.rust_src_sha256,
        );
        recomputed == self.composite_sha256
    }
}

/// Result of probing the active environment for a runnable Miri authority.
#[derive(Clone, Debug)]
pub enum MiriAvailability {
    Available(MiriRunner),
    Unavailable { reason: String },
    InvalidConfig { reason: String },
}

/// Structured error returned by Miri coordinate resolution and preparation,
/// separating normal Miri absence in trimmed archives (`Unavailable`) from
/// explicit override misconfiguration or toolchain skew (`InvalidConfig`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MiriProbeError {
    Unavailable(String),
    InvalidConfig(String),
}

impl MiriProbeError {
    pub fn reason(&self) -> &str {
        match self {
            Self::Unavailable(r) | Self::InvalidConfig(r) => r,
        }
    }

    pub fn into_reason(self) -> String {
        match self {
            Self::Unavailable(r) | Self::InvalidConfig(r) => r,
        }
    }

    pub fn is_invalid_config(&self) -> bool {
        matches!(self, Self::InvalidConfig(_))
    }
}

impl fmt::Display for MiriProbeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.reason())
    }
}

impl std::error::Error for MiriProbeError {}

/// Prepared Miri binary and target sysroot coordinates.
#[derive(Clone, Debug)]
pub struct MiriRunner {
    pub label: String,
    pub target: String,
    pub miri_bin: PathBuf,
    pub cargo_bin: Option<PathBuf>,
    pub rust_sysroot: PathBuf,
    pub miri_sysroot: PathBuf,
}

impl MiriRunner {
    /// Probe for Miri without silent compiler version skew:
    /// 1. Disabled immediately when `ANNEAL_ITREE_DISABLE_MIRI=1`.
    /// 2. Explicit `ANNEAL_ITREE_MIRI_BIN`, `ANNEAL_ITREE_MIRI_TOOLCHAIN`,
    ///    `ANNEAL_ITREE_MIRI_CARGO`, or `ANNEAL_ITREE_MIRI_SYSROOT` override
    ///    when set by the caller (always failing closed as `InvalidConfig` on
    ///    invalid paths or compiler sysroot skew against `active_sysroot`).
    /// 3. `<active_sysroot>/bin/miri` from the resolved Anneal Rust sysroot
    ///    (returning `Unavailable` only when Miri is absent, and failing closed
    ///    as `InvalidConfig` whenever a discovered Miri cannot be prepared).
    pub fn probe(cache_root: &Path, active_sysroot: Option<&Path>) -> MiriAvailability {
        Self::probe_with_env(cache_root, active_sysroot, |k| env::var_os(k))
    }

    /// Deterministic environment-injected variant of [`Self::probe`].
    pub fn probe_with_env(
        cache_root: &Path,
        active_sysroot: Option<&Path>,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> MiriAvailability {
        match Self::prepare_with_env(cache_root, active_sysroot, get_env) {
            Ok(runner) => MiriAvailability::Available(runner),
            Err(MiriProbeError::Unavailable(reason)) => MiriAvailability::Unavailable { reason },
            Err(MiriProbeError::InvalidConfig(reason)) => {
                MiriAvailability::InvalidConfig { reason }
            }
        }
    }

    /// Resolve Miri and prepare or reuse its target sysroot.
    pub fn prepare(cache_root: &Path, active_sysroot: Option<&Path>) -> Result<Self, String> {
        Self::prepare_with_env(cache_root, active_sysroot, |k| env::var_os(k))
            .map_err(MiriProbeError::into_reason)
    }

    fn prepare_with_env(
        cache_root: &Path,
        active_sysroot: Option<&Path>,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, MiriProbeError> {
        if get_env("ANNEAL_ITREE_DISABLE_MIRI").and_then(|v| v.into_string().ok()).as_deref()
            == Some("1")
        {
            return Err(MiriProbeError::Unavailable(
                "disabled via ANNEAL_ITREE_DISABLE_MIRI=1".to_string(),
            ));
        }

        let explicit_miri_sysroot =
            match get_env("ANNEAL_ITREE_MIRI_SYSROOT").filter(|v| !v.is_empty()) {
                Some(raw_override) => Some(
                    validate_explicit_miri_sysroot(Path::new(&raw_override))
                        .map_err(MiriProbeError::InvalidConfig)?,
                ),
                None => None,
            };

        let (label, rust_sysroot, miri_bin, cargo_bin) = match resolve_miri_coordinates_with_env(
            active_sysroot,
            &get_env,
        ) {
            Ok(coords) => coords,
            Err(MiriProbeError::Unavailable(reason)) if explicit_miri_sysroot.is_some() => {
                return Err(MiriProbeError::InvalidConfig(format!(
                    "ANNEAL_ITREE_MIRI_SYSROOT was set, but no Miri binary could be resolved: {reason}"
                )));
            }
            Err(err) => return Err(err),
        };

        // Once Miri coordinates have been resolved (whether via explicit
        // overrides or `<active_sysroot>/bin/miri`), any failure to compute
        // sysroot identity or build/validate the Miri sysroot fails closed as
        // `InvalidConfig` rather than silently degrading to `Unavailable`.
        let identity = MiriSysrootIdentity::compute(&rust_sysroot, &miri_bin, cargo_bin.as_deref())
            .map_err(MiriProbeError::InvalidConfig)?;

        if let Some(miri_sysroot) = explicit_miri_sysroot {
            let ready_stamp = miri_sysroot.join(".anneal-itree-miri-ready");
            if !identity.validate_ready_stamp(&ready_stamp)
                || !identity.validate_built_artifacts_manifest(&miri_sysroot)
            {
                return Err(MiriProbeError::InvalidConfig(format!(
                    "explicit ANNEAL_ITREE_MIRI_SYSROOT ({}) failed MiriSysrootIdentity or built-artifacts validation against active compiler, Miri binary, and rust-src inputs (missing or stale `.anneal-itree-miri-ready` / `{}`)",
                    miri_sysroot.display(),
                    MIRI_BUILT_ARTIFACTS_FILE,
                )));
            }
            return Ok(Self {
                label,
                target: identity.target,
                miri_bin,
                cargo_bin,
                rust_sysroot,
                miri_sysroot,
            });
        }
        let cache_tag = identity.cache_dir_tag();
        fs::create_dir_all(cache_root)
            .map_err(|e| format!("create Miri cache dir {}: {e}", cache_root.display()))
            .map_err(MiriProbeError::InvalidConfig)?;
        let target_dir = cache_root.join(format!("miri-sysroot-{cache_tag}"));
        let lock_path = cache_root.join(format!("miri-sysroot-{cache_tag}.lock"));
        let lock_file = File::options()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)
            .map_err(|e| format!("open Miri setup lock {}: {e}", lock_path.display()))
            .map_err(MiriProbeError::InvalidConfig)?;
        lock_file
            .lock()
            .map_err(|e| format!("acquire Miri setup lock {}: {e}", lock_path.display()))
            .map_err(MiriProbeError::InvalidConfig)?;

        let ready_stamp = target_dir.join(".anneal-itree-miri-ready");
        let cache_valid = target_dir.join("lib/rustlib").is_dir()
            && identity.validate_ready_stamp(&ready_stamp)
            && identity.validate_built_artifacts_manifest(&target_dir);
        if !cache_valid {
            let cargo = cargo_bin
                .clone()
                .ok_or_else(|| {
                    format!(
                        "cannot run `cargo miri setup`: missing `cargo` alongside {}",
                        rust_sysroot.display()
                    )
                })
                .map_err(MiriProbeError::InvalidConfig)?;
            build_offline_miri_sysroot(
                &rust_sysroot,
                &cargo,
                &miri_bin,
                &identity.target,
                &target_dir,
            )
            .map_err(MiriProbeError::InvalidConfig)?;
            identity
                .write_built_artifacts_manifest(&target_dir)
                .map_err(MiriProbeError::InvalidConfig)?;
            identity.write_ready_stamp(&ready_stamp).map_err(MiriProbeError::InvalidConfig)?;
        }
        drop(lock_file);

        let miri_sysroot = fs::canonicalize(&target_dir)
            .map_err(|e| format!("canonicalize Miri sysroot {}: {e}", target_dir.display()))
            .map_err(MiriProbeError::InvalidConfig)?;
        Ok(Self { label, target: identity.target, miri_bin, cargo_bin, rust_sysroot, miri_sysroot })
    }

    /// Execute one [`TraceTestCase`] under Miri with Tree Borrows enabled and
    /// `-C overflow-checks=no` matching Anneal's MIR capture profile.
    pub fn run_case(&self, case: &TraceTestCase) -> AuthorityRunResult {
        let auth_name = format!("miri({})", self.label);
        let start = Instant::now();
        let tmp = match tempfile::Builder::new().prefix("anneal-itree-miri-").tempdir() {
            Ok(d) => d,
            Err(e) => {
                return AuthorityRunResult::tool_error(
                    &auth_name,
                    format!("create Miri tempdir: {e}"),
                );
            }
        };

        let canon_tmp = match fs::canonicalize(tmp.path()) {
            Ok(p) => p,
            Err(e) => {
                return AuthorityRunResult::tool_error(
                    &auth_name,
                    format!("canonicalize Miri tempdir {}: {e}", tmp.path().display()),
                );
            }
        };
        let auth_token = generate_miri_auth_token(&canon_tmp);
        let remap_arg = format!("{}={auth_token}", canon_tmp.display());

        let harness_src = render_standalone_rust_harness(case);
        let harness_path = canon_tmp.join("harness.rs");
        if let Err(e) = fs::write(&harness_path, &harness_src) {
            return AuthorityRunResult::tool_error(
                &auth_name,
                format!("write Miri harness {}: {e}", harness_path.display()),
            );
        }

        let path_env = match build_child_path(&self.rust_sysroot.join("bin")) {
            Ok(p) => p,
            Err(detail) => return AuthorityRunResult::tool_error(&auth_name, detail),
        };
        let scratch_tmp = canon_tmp.join("tmp");
        if let Err(e) = fs::create_dir_all(&scratch_tmp) {
            return AuthorityRunResult::tool_error(
                &auth_name,
                format!("create Miri scratch temp {}: {e}", scratch_tmp.display()),
            );
        }
        let inv = build_miri_run_invocation_with_env(
            &self.miri_bin,
            &self.target,
            &remap_arg,
            &self.miri_sysroot,
            &harness_path,
            &join_dylib_path(&self.rust_sysroot.join("lib")),
            &path_env,
            Some(&scratch_tmp),
            |k| env::var_os(k),
        );

        let out = match run_supervised(&inv, &canon_tmp, MIRI_RUN_TIMEOUT_SECS) {
            Ok(o) => o,
            Err(detail) => return AuthorityRunResult::tool_error(&auth_name, detail),
        };
        let elapsed_ms = start.elapsed().as_millis() as u64;
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);

        match out.termination {
            Termination::Exited(status) => {
                #[cfg(unix)]
                let signal = {
                    use std::os::unix::process::ExitStatusExt;
                    status.signal()
                };
                #[cfg(not(unix))]
                let signal: Option<i32> = None;

                parse_miri_run_output_authenticated(
                    &auth_name,
                    status.code(),
                    signal,
                    &stdout,
                    &stderr,
                    elapsed_ms,
                    Some(case.rust_arg_exprs.len()),
                    Some(&auth_token),
                )
            }
            Termination::TimedOut(status) => AuthorityRunResult::tool_error(
                &auth_name,
                format!("Miri timed out after {MIRI_RUN_TIMEOUT_SECS}s ({status})"),
            ),
            Termination::LaunchFailed(err) => {
                AuthorityRunResult::tool_error(&auth_name, format!("spawn Miri: {err}"))
            }
        }
    }
}

/// Validate an explicit `ANNEAL_ITREE_MIRI_SYSROOT` directory, rejecting
/// symlinked root paths and missing `lib/rustlib` trees while ignoring ambient
/// `MIRI_SYSROOT`.
pub fn validate_explicit_miri_sysroot(path: &Path) -> Result<PathBuf, String> {
    let meta = fs::symlink_metadata(path)
        .map_err(|e| format!("inspect ANNEAL_ITREE_MIRI_SYSROOT {}: {e}", path.display()))?;
    if meta.file_type().is_symlink() {
        return Err(format!("ANNEAL_ITREE_MIRI_SYSROOT must not be a symlink: {}", path.display()));
    }
    if !meta.is_dir() {
        return Err(format!("ANNEAL_ITREE_MIRI_SYSROOT is not a directory: {}", path.display()));
    }
    let canon = fs::canonicalize(path)
        .map_err(|e| format!("canonicalize ANNEAL_ITREE_MIRI_SYSROOT {}: {e}", path.display()))?;
    if !canon.join("lib/rustlib").is_dir() {
        return Err(format!(
            "ANNEAL_ITREE_MIRI_SYSROOT missing `lib/rustlib`: {}",
            canon.display()
        ));
    }
    Ok(canon)
}

fn generate_miri_auth_token(canon_tmp: &Path) -> String {
    static MIRI_AUTH_COUNTER: AtomicU64 = AtomicU64::new(0);
    let seq = MIRI_AUTH_COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-auth-v1\0");
    hasher.update(std::process::id().to_le_bytes());
    hasher.update(seq.to_le_bytes());
    hasher.update(nanos.to_le_bytes());
    hasher.update(canon_tmp.to_string_lossy().as_bytes());
    let hex = sha256_hex(&hasher.finalize());
    format!("__anneal_miri_auth_{}__", &hex[..24])
}

#[derive(Deserialize)]
struct RawMiriSpan {
    #[serde(default)]
    file_name: String,
}

#[derive(Deserialize)]
struct RawMiriChild {
    #[serde(default)]
    level: String,
    #[serde(default)]
    message: String,
    #[serde(default)]
    spans: Vec<RawMiriSpan>,
}

#[derive(Deserialize)]
struct RawMiriDiagnostic {
    #[serde(rename = "$message_type", default)]
    message_type: String,
    #[serde(default)]
    level: String,
    #[serde(default)]
    message: String,
    #[serde(default)]
    spans: Vec<RawMiriSpan>,
    #[serde(default)]
    children: Vec<RawMiriChild>,
    #[serde(default)]
    rendered: Option<String>,
}

fn diagnostic_mentions_token(diag: &RawMiriDiagnostic, token: &str) -> bool {
    diag.spans.iter().any(|s| s.file_name.contains(token))
        || diag.children.iter().any(|c| {
            c.message.contains(token) || c.spans.iter().any(|s| s.file_name.contains(token))
        })
        || diag.rendered.as_deref().is_some_and(|r| r.contains(token))
}

/// Parse Miri exit status, signal, stdout, and `--error-format=json` stderr
/// into an [`AuthorityRunResult`].
pub fn parse_miri_run_output(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
) -> AuthorityRunResult {
    parse_miri_run_output_authenticated(
        auth_name, exit_code, signal, stdout, stderr, elapsed_ms, None, None,
    )
}

/// Entry-count-checked variant of [`parse_miri_run_output`].
#[allow(clippy::too_many_arguments)]
pub fn parse_miri_run_output_with_expected_args(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
) -> AuthorityRunResult {
    parse_miri_run_output_authenticated(
        auth_name,
        exit_code,
        signal,
        stdout,
        stderr,
        elapsed_ms,
        expected_entry_slots,
        None,
    )
}

/// Authenticated variant of [`parse_miri_run_output_with_expected_args`] that
/// additionally requires Miri's structured `--error-format=json` diagnostic to
/// reference the per-invocation `--remap-path-prefix` `expected_remap_token`
/// (which interpreted guest code under Miri isolation cannot observe or forge).
#[allow(clippy::too_many_arguments)]
pub fn parse_miri_run_output_authenticated(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
    expected_remap_token: Option<&str>,
) -> AuthorityRunResult {
    let exited_zero = exit_code == Some(0) && signal.is_none();

    // Require Miri's nonzero exit code (without a fatal signal crash) AND an
    // authenticated `--error-format=json` Miri compiler diagnostic (carrying
    // Miri's UB help child, the companion `aborting due to ...` compiler
    // summary, and `expected_remap_token` when provided) so subject `eprintln!`
    // + `std::process::exit(1)` can never spoof Undefined Behavior.
    if !exited_zero
        && exit_code.is_some()
        && signal.is_none()
        && let Some(ub_line) = detect_authenticated_miri_ub_line(stderr, expected_remap_token)
    {
        let entry_mem_digest = match parse_pre_entry_slots_stdout(
            auth_name,
            stdout,
            stderr,
            expected_entry_slots,
        ) {
            Ok(Some(slots)) => Some(crate::outcome::compute_boundary_mem_digest(&slots)),
            Ok(None) if expected_entry_slots.is_some() => {
                return AuthorityRunResult::tool_error(
                    auth_name,
                    format!(
                        "{auth_name} UB output missing `{PRE_ENTRY_JSON_PREFIX}` line; stdout={stdout:?}, stderr={stderr:?}"
                    ),
                );
            }
            Ok(None) => None,
            Err(detail) => return AuthorityRunResult::tool_error(auth_name, detail),
        };
        return AuthorityRunResult {
            authority: auth_name.to_string(),
            outcome: TerminalOutcome::FaultUb { detail: ub_line },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: stderr.to_string(),
            elapsed_ms,
            post_only_mem_digest: false,
            entry_mem_digest,
        };
    }

    if exited_zero {
        return match parse_trace_json_stdout_with_expected_args(
            auth_name,
            stdout,
            stderr,
            elapsed_ms,
            expected_entry_slots,
        ) {
            Ok(res) => res,
            Err(detail) => AuthorityRunResult::tool_error(auth_name, detail),
        };
    }

    // Scheduled `std::process::abort()` inside Miri flushes
    // `ANNEAL_ITREE_PRE_ABORT:` before Miri reports abnormal termination.
    let miri_aborted_diag = detect_authenticated_miri_abort(stderr, expected_remap_token);
    if (miri_aborted_diag || signal == Some(6))
        && stdout.lines().any(|l| l.trim().starts_with(PRE_ABORT_JSON_PREFIX))
    {
        return match parse_pre_abort_stdout_with_expected_args(
            auth_name,
            stdout,
            stderr,
            elapsed_ms,
            expected_entry_slots,
        ) {
            Ok(res) => res,
            Err(detail) => AuthorityRunResult::tool_error(auth_name, detail),
        };
    }

    AuthorityRunResult::tool_error(
        auth_name,
        format!(
            "Miri failed (exit={exit_code:?}, signal={signal:?}): stdout={stdout:?}, stderr={stderr:?}"
        ),
    )
}

/// Detect Miri Undefined Behavior strictly from `--error-format=json`
/// compiler diagnostics, never accepting raw plain-text
/// `error: Undefined Behavior:` lines printed by guest code.
pub fn detect_miri_ub_line(stderr: &str) -> Option<String> {
    detect_authenticated_miri_ub_line(stderr, None)
}

fn parse_miri_json_diagnostics(stderr: &str) -> Vec<RawMiriDiagnostic> {
    let mut parsed_diags = Vec::new();
    for line in stderr.lines() {
        let trimmed = line.trim();
        let candidate = if trimmed.starts_with('{') {
            Some(trimmed)
        } else {
            // If guest code called `eprint!(...)` without a trailing newline
            // immediately before UB/abort, Miri appends its JSON diagnostic at
            // the end of that partial line.
            trimmed.find(r#"{"$message_type":"#).map(|idx| &trimmed[idx..])
        };
        if let Some(json_slice) = candidate
            && let Ok(diag) = serde_json::from_str::<RawMiriDiagnostic>(json_slice)
            && diag.message_type == "diagnostic"
        {
            parsed_diags.push(diag);
        }
    }
    parsed_diags
}

/// Token-authenticated variant of [`detect_miri_ub_line`].
pub fn detect_authenticated_miri_ub_line(
    stderr: &str,
    expected_remap_token: Option<&str>,
) -> Option<String> {
    if let Some(tok) = expected_remap_token
        && tok.trim().is_empty()
    {
        return None;
    }
    let parsed_diags = parse_miri_json_diagnostics(stderr);
    let has_compiler_abort_summary = parsed_diags
        .iter()
        .any(|d| d.level == "error" && d.message.starts_with("aborting due to "));
    if !has_compiler_abort_summary {
        return None;
    }
    for diag in &parsed_diags {
        let has_miri_ub_help = diag.children.iter().any(|c| {
            c.level == "help"
                && c.message
                    .contains("performed an invalid operation, and caused Undefined Behavior")
        });
        let token_ok = match expected_remap_token {
            Some(tok) => diagnostic_mentions_token(diag, tok),
            None => true,
        };
        if diag.level == "error"
            && diag.message.starts_with("Undefined Behavior:")
            && has_miri_ub_help
            && token_ok
        {
            return Some(format!("error: {}", diag.message.trim_end()));
        }
    }
    None
}

fn detect_authenticated_miri_abort(stderr: &str, expected_remap_token: Option<&str>) -> bool {
    let parsed_diags = parse_miri_json_diagnostics(stderr);
    let has_summary = parsed_diags
        .iter()
        .any(|d| d.level == "error" && d.message.starts_with("aborting due to "));
    if has_summary {
        for diag in &parsed_diags {
            let is_abort = diag.level == "error"
                && (diag.message.starts_with("abnormal termination:")
                    || diag.message.contains("the program aborted execution"));
            let token_ok = match expected_remap_token {
                Some(tok) => !tok.trim().is_empty() && diagnostic_mentions_token(diag, tok),
                None => true,
            };
            if is_abort && token_ok {
                return true;
            }
        }
    }
    false
}

/// Query `<miri_bin> --print sysroot` with a bounded timeout and return its
/// canonicalized compiler sysroot directory path so explicit Miri overrides
/// never silently pair with a skewed compiler or capture sysroot.
pub fn query_miri_sysroot(miri_bin: &Path) -> Result<PathBuf, String> {
    query_miri_sysroot_with_timeout(miri_bin, crate::rustc_runner::DISCOVERY_PROBE_TIMEOUT_SECS)
}

/// Timeout-parameterized variant of [`query_miri_sysroot`].
pub fn query_miri_sysroot_with_timeout(
    miri_bin: &Path,
    timeout_secs: u64,
) -> Result<PathBuf, String> {
    if !miri_bin.is_file() {
        return Err(format!("missing `miri` executable at {}", miri_bin.display()));
    }
    let dylib = miri_bin
        .parent()
        .and_then(Path::parent)
        .map(|p| p.join("lib"))
        .filter(|p| p.is_dir())
        .map(|lib_dir| join_dylib_path(&lib_dir));
    let out = run_probe_supervised_with_timeout(
        miri_bin,
        &["--print", "sysroot"],
        dylib.as_deref(),
        true,
        timeout_secs,
    )
    .map_err(|e| format!("invoke `{} --print sysroot`: {e}", miri_bin.display()))?;
    if !out.status.success() {
        return Err(format!(
            "`{} --print sysroot` failed ({}): {}",
            miri_bin.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let stdout = String::from_utf8(out.stdout)
        .map_err(|e| format!("invalid UTF-8 from `{} --print sysroot`: {e}", miri_bin.display()))?;
    let trimmed = stdout.trim();
    if trimmed.is_empty() {
        return Err(format!("`{} --print sysroot` returned empty stdout", miri_bin.display()));
    }
    fs::canonicalize(trimmed).map_err(|e| {
        format!("canonicalize sysroot `{trimmed}` reported by `{}`: {e}", miri_bin.display())
    })
}

fn resolve_miri_override_with_path_and_suffix(
    raw: &std::ffi::OsStr,
    path_var: Option<&std::ffi::OsStr>,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    let found = resolve_explicit_or_path_exe_with_suffix(raw, path_var, exe_suffix)
        .ok_or_else(|| format!("not an executable file: {}", Path::new(raw).display()))?;
    canonicalize_preserving_rustup_proxy_with_suffix(&found, None, "miri", exe_suffix)
}

fn pin_toolchain_miri_if_rustup_proxy_with_suffix(
    miri_bin: PathBuf,
    sysroot: &Path,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    canonicalize_preserving_rustup_proxy_with_suffix(&miri_bin, Some(sysroot), "miri", exe_suffix)
}

/// Resolve `(label, rust_sysroot, miri_bin, cargo_bin)` from process
/// environment variables, rejecting explicit Miri toolchain skew against
/// `active_sysroot`.
pub fn resolve_miri_coordinates(
    active_sysroot: Option<&Path>,
) -> Result<(String, PathBuf, PathBuf, Option<PathBuf>), MiriProbeError> {
    resolve_miri_coordinates_with_env(active_sysroot, |k| env::var_os(k))
}

/// Deterministic environment-injected variant of [`resolve_miri_coordinates`]
/// for unit-testing all Miri discovery and toolchain-skew branches without
/// mutating process environment variables.
pub fn resolve_miri_coordinates_with_env(
    active_sysroot: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<(String, PathBuf, PathBuf, Option<PathBuf>), MiriProbeError> {
    resolve_miri_coordinates_with_env_and_suffix(active_sysroot, get_env, env::consts::EXE_SUFFIX)
}

/// Suffix-parameterized variant of [`resolve_miri_coordinates_with_env`] so
/// unit tests can verify Windows `.exe` executable discovery on Unix hosts.
pub fn resolve_miri_coordinates_with_env_and_suffix(
    active_sysroot: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
    exe_suffix: &str,
) -> Result<(String, PathBuf, PathBuf, Option<PathBuf>), MiriProbeError> {
    let miri_exe = exe_name_for_suffix("miri", exe_suffix);
    let canon_active = active_sysroot
        .map(|p| {
            fs::canonicalize(p).map_err(|e| {
                MiriProbeError::InvalidConfig(format!(
                    "canonicalize active sysroot {}: {e}",
                    p.display()
                ))
            })
        })
        .transpose()?;

    let raw_bin = get_env("ANNEAL_ITREE_MIRI_BIN").filter(|v| !v.is_empty());
    let raw_tc = match get_env("ANNEAL_ITREE_MIRI_TOOLCHAIN") {
        Some(v) => {
            let s = v.into_string().map_err(|_| {
                MiriProbeError::InvalidConfig(
                    "ANNEAL_ITREE_MIRI_TOOLCHAIN contains invalid UTF-8".to_string(),
                )
            })?;
            let trimmed = s.trim().to_string();
            if trimmed.is_empty() { None } else { Some(trimmed) }
        }
        None => None,
    };
    if raw_bin.is_some() && raw_tc.is_some() {
        return Err(MiriProbeError::InvalidConfig(
            "conflicting Miri configuration: both ANNEAL_ITREE_MIRI_BIN and ANNEAL_ITREE_MIRI_TOOLCHAIN are set".to_string(),
        ));
    }

    // 1. Explicit `ANNEAL_ITREE_MIRI_BIN` override.
    let path_var = get_env("PATH");
    if let Some(raw_bin) = raw_bin {
        let miri_exec =
            resolve_miri_override_with_path_and_suffix(&raw_bin, path_var.as_deref(), exe_suffix)
                .map_err(|e| {
                MiriProbeError::InvalidConfig(format!("canonicalize ANNEAL_ITREE_MIRI_BIN: {e}"))
            })?;
        let miri_sr = query_miri_sysroot(&miri_exec).map_err(MiriProbeError::InvalidConfig)?;
        if let Some(exp_sr) = &canon_active
            && !sysroots_equivalent_with_suffix(exp_sr, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_BIN ({}) resolves compiler sysroot {}, which differs from active sysroot {}",
                miri_exec.display(),
                miri_sr.display(),
                exp_sr.display()
            )));
        }
        let miri_bin =
            pin_toolchain_miri_if_rustup_proxy_with_suffix(miri_exec, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?;
        let cargo_bin =
            resolve_cargo_for_sysroot_with_env_and_suffix(&miri_sr, &get_env, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?;
        return Ok(("explicit-miri-bin".to_string(), miri_sr, miri_bin, cargo_bin));
    }

    // 2. Explicit `ANNEAL_ITREE_MIRI_TOOLCHAIN` override via `rustup`.
    if let Some(tc) = raw_tc {
        let raw_sr = query_rustup_sysroot(&tc).map_err(MiriProbeError::InvalidConfig)?;
        let tc_sr = fs::canonicalize(&raw_sr).map_err(|e| {
            MiriProbeError::InvalidConfig(format!(
                "canonicalize `{tc}` sysroot {}: {e}",
                raw_sr.display()
            ))
        })?;
        let miri_cand = tc_sr.join("bin").join(&miri_exe);
        if !miri_cand.is_file() {
            return Err(MiriProbeError::InvalidConfig(format!(
                "ANNEAL_ITREE_MIRI_TOOLCHAIN `{tc}` lacks `bin/{miri_exe}` at {}",
                miri_cand.display()
            )));
        }
        let miri_bin = fs::canonicalize(&miri_cand)
            .map_err(|e| MiriProbeError::InvalidConfig(format!("canonicalize miri: {e}")))?;
        let miri_sr = query_miri_sysroot(&miri_bin).map_err(MiriProbeError::InvalidConfig)?;
        if !sysroots_equivalent_with_suffix(&tc_sr, &miri_sr, exe_suffix)
            .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: ANNEAL_ITREE_MIRI_TOOLCHAIN `{tc}` miri ({}) resolves compiler sysroot {}, which differs from toolchain sysroot {}",
                miri_bin.display(),
                miri_sr.display(),
                tc_sr.display()
            )));
        }
        if let Some(exp_sr) = &canon_active
            && !sysroots_equivalent_with_suffix(exp_sr, &tc_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_TOOLCHAIN `{tc}` resolves compiler sysroot {}, which differs from active sysroot {}",
                tc_sr.display(),
                exp_sr.display()
            )));
        }
        let cargo_bin = resolve_cargo_for_sysroot_with_env_and_suffix(&tc_sr, &get_env, exe_suffix)
            .map_err(MiriProbeError::InvalidConfig)?;
        return Ok((tc, tc_sr, miri_bin, cargo_bin));
    }

    // 3. Explicit `ANNEAL_ITREE_MIRI_CARGO` override when provided (checked
    //    before falling back to `active_sysroot` so a skewed explicit
    //    `ANNEAL_ITREE_MIRI_CARGO` is not masked by `active_sysroot/bin/miri`).
    if let Some(raw_cargo) = get_env("ANNEAL_ITREE_MIRI_CARGO").filter(|v| !v.is_empty()) {
        let found_cargo =
            resolve_explicit_or_path_exe_with_suffix(&raw_cargo, path_var.as_deref(), exe_suffix)
                .unwrap_or_else(|| PathBuf::from(&raw_cargo));
        let cargo_bin = canonicalize_preserving_rustup_proxy_with_suffix(
            &found_cargo,
            canon_active.as_deref(),
            "cargo",
            exe_suffix,
        )
        .map_err(|e| {
            MiriProbeError::InvalidConfig(format!("canonicalize ANNEAL_ITREE_MIRI_CARGO: {e}"))
        })?;
        let is_proxy = fs::canonicalize(&cargo_bin)
            .ok()
            .and_then(|c| c.file_name().map(is_rustup_executable_name))
            .unwrap_or(false);
        let sr = if is_proxy && let Some(exp_sr) = &canon_active {
            exp_sr.clone()
        } else {
            let Some(raw_sr) = cargo_bin.parent().and_then(Path::parent) else {
                return Err(MiriProbeError::InvalidConfig(format!(
                    "cannot derive sysroot parent for ANNEAL_ITREE_MIRI_CARGO at {}",
                    cargo_bin.display()
                )));
            };
            fs::canonicalize(raw_sr).map_err(|e| {
                MiriProbeError::InvalidConfig(format!(
                    "canonicalize ANNEAL_ITREE_MIRI_CARGO sysroot {}: {e}",
                    raw_sr.display()
                ))
            })?
        };
        let miri_cand = sr.join("bin").join(&miri_exe);
        if !miri_cand.is_file() {
            return Err(MiriProbeError::InvalidConfig(format!(
                "ANNEAL_ITREE_MIRI_CARGO at {} has no sibling `bin/{miri_exe}`",
                cargo_bin.display()
            )));
        }
        let miri_bin = fs::canonicalize(&miri_cand)
            .map_err(|e| MiriProbeError::InvalidConfig(format!("canonicalize miri: {e}")))?;
        let miri_sr = query_miri_sysroot(&miri_bin).map_err(MiriProbeError::InvalidConfig)?;
        if !sysroots_equivalent_with_suffix(&sr, &miri_sr, exe_suffix)
            .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: ANNEAL_ITREE_MIRI_CARGO sibling miri ({}) resolves compiler sysroot {}, which differs from cargo sysroot {}",
                miri_bin.display(),
                miri_sr.display(),
                sr.display()
            )));
        }
        if let Some(exp_sr) = &canon_active
            && !sysroots_equivalent_with_suffix(exp_sr, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_CARGO ({}) resolves compiler sysroot {}, which differs from active sysroot {}",
                cargo_bin.display(),
                miri_sr.display(),
                exp_sr.display()
            )));
        }
        return Ok(("explicit-miri-cargo".to_string(), sr, miri_bin, Some(cargo_bin)));
    }

    // 4. Active sysroot (`ANNEAL_SYSROOT` / `ANNEAL_TEST_INSTALL_ROOT/rust` /
    //    `ToolchainEnv.sysroot`) without explicit `ANNEAL_ITREE_MIRI_*`
    //    overrides — guarantees zero compiler skew with `rustc` and
    //    `anneal-rustc-capture` while allowing trimmed omnibus archives
    //    lacking `bin/miri` to run cleanly in `DegradedNoMiri` mode.
    if let Some(canon_sr) = &canon_active {
        let miri_cand = canon_sr.join("bin").join(&miri_exe);
        if miri_cand.is_file() {
            let miri_bin = fs::canonicalize(&miri_cand)
                .map_err(|e| MiriProbeError::InvalidConfig(format!("canonicalize miri: {e}")))?;
            let miri_sr = query_miri_sysroot(&miri_bin).map_err(MiriProbeError::InvalidConfig)?;
            if !sysroots_equivalent_with_suffix(canon_sr, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
            {
                return Err(MiriProbeError::InvalidConfig(format!(
                    "Miri toolchain version skew: active sysroot `bin/{miri_exe}` ({}) resolves compiler sysroot {}, which differs from active sysroot {}",
                    miri_bin.display(),
                    miri_sr.display(),
                    canon_sr.display()
                )));
            }
            let cargo_bin =
                resolve_cargo_for_sysroot_with_env_and_suffix(canon_sr, &get_env, exe_suffix)
                    .map_err(MiriProbeError::InvalidConfig)?;
            return Ok(("active-sysroot".to_string(), canon_sr.clone(), miri_bin, cargo_bin));
        }
    }

    Err(MiriProbeError::Unavailable(match active_sysroot {
        Some(sr) => format!(
            "active sysroot {} does not bundle `bin/{miri_exe}` (set ANNEAL_ITREE_MIRI_BIN or ANNEAL_ITREE_MIRI_TOOLCHAIN to opt into a matching Miri toolchain)",
            sr.display()
        ),
        None => "no Miri binary found in active sysroot or environment overrides".to_string(),
    }))
}

fn resolve_cargo_for_sysroot_with_env_and_suffix(
    sysroot: &Path,
    get_env: &impl Fn(&str) -> Option<OsString>,
    exe_suffix: &str,
) -> Result<Option<PathBuf>, String> {
    if let Some(explicit) = get_env("ANNEAL_ITREE_MIRI_CARGO").filter(|v| !v.is_empty()) {
        let path_var = get_env("PATH");
        let found =
            resolve_explicit_or_path_exe_with_suffix(&explicit, path_var.as_deref(), exe_suffix)
                .unwrap_or_else(|| PathBuf::from(&explicit));
        let raw_canon = fs::canonicalize(&found)
            .map_err(|e| format!("canonicalize ANNEAL_ITREE_MIRI_CARGO: {e}"))?;
        if !raw_canon.is_file() {
            return Err(format!("ANNEAL_ITREE_MIRI_CARGO is not a file: {}", raw_canon.display()));
        }
        let is_proxy = raw_canon.file_name().is_some_and(is_rustup_executable_name);
        if !is_proxy
            && let Some(cargo_sr) =
                raw_canon.parent().and_then(Path::parent).filter(|p| p.join("lib/rustlib").is_dir())
        {
            let canon_cargo_sr = fs::canonicalize(cargo_sr)
                .map_err(|e| format!("canonicalize ANNEAL_ITREE_MIRI_CARGO sysroot: {e}"))?;
            if !sysroots_equivalent_with_suffix(sysroot, &canon_cargo_sr, exe_suffix)? {
                return Err(format!(
                    "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_CARGO ({}) belongs to sysroot {}, which differs from Miri sysroot {}",
                    raw_canon.display(),
                    canon_cargo_sr.display(),
                    sysroot.display()
                ));
            }
        }
        let resolved = canonicalize_preserving_rustup_proxy_with_suffix(
            &found,
            Some(sysroot),
            "cargo",
            exe_suffix,
        )
        .map_err(|e| format!("resolve ANNEAL_ITREE_MIRI_CARGO: {e}"))?;
        return Ok(Some(resolved));
    }
    let cargo_exe = exe_name_for_suffix("cargo", exe_suffix);
    let bundled = sysroot.join("bin").join(&cargo_exe);
    if bundled.is_file() {
        return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
            &bundled,
            Some(sysroot),
            "cargo",
            exe_suffix,
        )
        .ok());
    }
    if let Some(env_cargo) = get_env("CARGO").filter(|v| !v.is_empty()) {
        let p = PathBuf::from(&env_cargo);
        if let Some(found) = resolve_candidate_exe_with_suffix(&p, exe_suffix) {
            return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
                &found,
                Some(sysroot),
                "cargo",
                exe_suffix,
            )
            .ok());
        }
        if p.components().count() == 1
            && let Some(path_var) = get_env("PATH")
        {
            let name_with_ext = if !exe_suffix.is_empty() && p.extension().is_none() {
                let mut raw = env_cargo;
                raw.push(exe_suffix);
                PathBuf::from(raw)
            } else {
                p
            };
            for dir in env::split_paths(&path_var) {
                let cand = dir.join(&name_with_ext);
                if cand.is_file() {
                    return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
                        &cand,
                        Some(sysroot),
                        "cargo",
                        exe_suffix,
                    )
                    .ok());
                }
            }
        }
    }
    if let Some(path_var) = get_env("PATH") {
        for dir in env::split_paths(&path_var) {
            let cand = dir.join(&cargo_exe);
            if cand.is_file() {
                return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
                    &cand,
                    Some(sysroot),
                    "cargo",
                    exe_suffix,
                )
                .ok());
            }
        }
    }
    Ok(None)
}

fn query_rustup_sysroot(toolchain: &str) -> Result<PathBuf, String> {
    let out = run_probe_supervised(
        Path::new("rustup"),
        &["run", toolchain, "rustc", "--print", "sysroot"],
        None,
        false,
    )
    .map_err(|e| format!("invoke rustup for `{toolchain}`: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "rustup toolchain `{toolchain}` unavailable: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let text = String::from_utf8(out.stdout)
        .map_err(|e| format!("invalid UTF-8 from rustup sysroot: {e}"))?;
    fs::canonicalize(text.trim()).map_err(|e| format!("canonicalize `{toolchain}` sysroot: {e}"))
}

fn run_version_cmd(
    bin: &Path,
    args: &[&str],
    dylib_search_path: &std::ffi::OsStr,
) -> Result<String, String> {
    if !bin.is_file() {
        return Err(format!("missing executable {}", bin.display()));
    }
    let out = run_probe_supervised(bin, args, Some(dylib_search_path), true)
        .map_err(|e| format!("run `{} {}`: {e}", bin.display(), args.join(" ")))?;
    if !out.status.success() {
        return Err(format!(
            "`{} {}` failed: {}",
            bin.display(),
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
    let (_, digest) = stream_sha256_file_with_buf(path, &mut buf)?;
    Ok(sha256_hex(&digest))
}

fn sha256_file_pair(primary: &Path, secondary: &Path) -> Result<String, String> {
    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
    let (len_a, sha_a) = stream_sha256_file_with_buf(primary, &mut buf)?;
    let (len_b, sha_b) = stream_sha256_file_with_buf(secondary, &mut buf)?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-rustc-wrapper-pair-v1\0");
    hasher.update(len_a.to_le_bytes());
    hasher.update(sha_a);
    hasher.update(len_b.to_le_bytes());
    hasher.update(sha_b);
    Ok(sha256_hex(&hasher.finalize()))
}

fn stream_sha256_file_with_buf(path: &Path, buf: &mut [u8]) -> Result<(u64, [u8; 32]), String> {
    let mut file = File::open(path).map_err(|e| format!("open {}: {e}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut total_bytes = 0u64;
    loop {
        match file.read(buf) {
            Ok(0) => break,
            Ok(n) => {
                hasher.update(&buf[..n]);
                total_bytes += n as u64;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(format!("read {}: {e}", path.display())),
        }
    }
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    Ok((total_bytes, out))
}

type HashedTreeEntry = (String, u64, [u8; 32]);

fn stream_hash_sorted_entries(
    entries: &[(String, PathBuf)],
) -> Result<Vec<HashedTreeEntry>, String> {
    if entries.is_empty() {
        return Ok(Vec::new());
    }
    let workers = thread::available_parallelism()
        .map(|n| n.get().clamp(1, MAX_TREE_HASH_WORKERS))
        .unwrap_or(1)
        .min(entries.len());
    if workers <= 1 {
        let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
        return entries
            .iter()
            .map(|(rel, path)| {
                let (len, sha) = stream_sha256_file_with_buf(path, &mut buf)?;
                Ok((rel.clone(), len, sha))
            })
            .collect();
    }

    let chunk_size = entries.len().div_ceil(workers);
    let chunk_results: Vec<Result<Vec<HashedTreeEntry>, String>> = thread::scope(|scope| {
        let mut handles = Vec::with_capacity(workers);
        for chunk in entries.chunks(chunk_size) {
            handles.push(scope.spawn(move || {
                let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
                let mut local = Vec::with_capacity(chunk.len());
                for (rel, path) in chunk {
                    let (len, sha) = stream_sha256_file_with_buf(path, &mut buf)?;
                    local.push((rel.clone(), len, sha));
                }
                Ok(local)
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_else(|_| Err("Miri tree hash worker panicked".to_string())))
            .collect()
    });

    let mut out = Vec::with_capacity(entries.len());
    for res in chunk_results {
        out.extend(res?);
    }
    Ok(out)
}

fn has_host_lib_extension(file_name: &str) -> bool {
    let ext = Path::new(file_name).extension().and_then(|s| s.to_str());
    matches!(ext, Some("so" | "dylib" | "dll" | "a")) || file_name.contains(".so.")
}

fn compute_rustc_host_libs_digest(
    rust_sysroot: &Path,
    backing_sysroot: Option<&Path>,
) -> Result<String, String> {
    let canon_sysroot = fs::canonicalize(rust_sysroot)
        .map_err(|e| format!("canonicalize rust sysroot {}: {e}", rust_sysroot.display()))?;
    let lib_dir = canon_sysroot.join("lib");
    if !lib_dir.is_dir() {
        return Err(format!("missing sysroot `lib` directory at {}", lib_dir.display()));
    }

    let mut sorted: BTreeMap<String, PathBuf> = BTreeMap::new();
    for entry in
        fs::read_dir(&lib_dir).map_err(|e| format!("read_dir {}: {e}", lib_dir.display()))?
    {
        let entry = entry.map_err(|e| format!("iterate {}: {e}", lib_dir.display()))?;
        let raw_name = entry.file_name();
        let name = raw_name
            .to_str()
            .ok_or_else(|| {
                format!("non-UTF-8 library name in {}: {raw_name:?}", lib_dir.display())
            })?
            .to_string();
        if !has_host_lib_extension(&name) {
            continue;
        }
        let path = entry.path();
        let sym_meta = fs::symlink_metadata(&path)
            .map_err(|e| format!("inspect host lib {}: {e}", path.display()))?;
        let resolved = if sym_meta.file_type().is_symlink() {
            let target = fs::canonicalize(&path)
                .map_err(|e| format!("resolve host lib symlink {}: {e}", path.display()))?;
            let in_backing = backing_sysroot.is_some_and(|b| target.starts_with(b));
            if !target.starts_with(&canon_sysroot) && !in_backing {
                return Err(format!(
                    "host lib symlink {} escapes sysroot {} -> {}",
                    path.display(),
                    canon_sysroot.display(),
                    target.display()
                ));
            }
            target
        } else {
            path
        };
        let meta = fs::metadata(&resolved)
            .map_err(|e| format!("stat host lib {}: {e}", resolved.display()))?;
        if meta.is_file() {
            sorted.insert(name, resolved);
        }
    }

    let entries: Vec<(String, PathBuf)> = sorted.into_iter().collect();
    let hashed = stream_hash_sorted_entries(&entries)?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-host-libs-v1\0");
    hasher.update((hashed.len() as u64).to_le_bytes());
    for (name, len, sha) in &hashed {
        update_len_prefixed(&mut hasher, name.as_bytes());
        hasher.update(len.to_le_bytes());
        hasher.update(sha);
    }
    Ok(sha256_hex(&hasher.finalize()))
}

/// Ordered search directories used both to locate and hash `cargo-miri` in
/// [`MiriSysrootIdentity`] and to construct the child `PATH` for offline Miri
/// sysroot preparation (`cargo_bin` sibling dir first, then `miri_bin` sibling
/// dir, `<rust_sysroot>/bin`, and ambient `PATH`).
pub fn miri_setup_search_dirs(
    rust_sysroot: &Path,
    miri_bin: &Path,
    cargo_bin: Option<&Path>,
    path_var: Option<&std::ffi::OsStr>,
) -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Some(dir) = cargo_bin.and_then(Path::parent).filter(|p| !p.as_os_str().is_empty()) {
        dirs.push(dir.to_path_buf());
    }
    if let Some(dir) = miri_bin.parent().filter(|p| !p.as_os_str().is_empty())
        && !dirs.iter().any(|d| d == dir)
    {
        dirs.push(dir.to_path_buf());
    }
    let sr_bin = rust_sysroot.join("bin");
    if !dirs.iter().any(|d| d == &sr_bin) {
        dirs.push(sr_bin);
    }
    if cargo_bin.is_some()
        && let Some(pv) = path_var
    {
        for dir in env::split_paths(pv) {
            if !dir.as_os_str().is_empty() && !dirs.iter().any(|d| d == &dir) {
                dirs.push(dir);
            }
        }
    }
    dirs
}

fn is_executable_file(path: &Path) -> bool {
    let Ok(meta) = fs::metadata(path) else {
        return false;
    };
    if !meta.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        meta.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// Resolve the exact `cargo-miri` executable that offline Miri sysroot setup
/// invokes and [`MiriSysrootIdentity`] hashes.
pub fn resolve_cargo_miri_binary_with_suffix(
    rust_sysroot: &Path,
    miri_bin: &Path,
    cargo_bin: Option<&Path>,
    exe_suffix: &str,
) -> Option<PathBuf> {
    resolve_cargo_miri_binary_with_path_and_suffix(
        rust_sysroot,
        miri_bin,
        cargo_bin,
        env::var_os("PATH").as_deref(),
        exe_suffix,
    )
}

/// Environment-parameterized variant of
/// [`resolve_cargo_miri_binary_with_suffix`].
pub fn resolve_cargo_miri_binary_with_path_and_suffix(
    rust_sysroot: &Path,
    miri_bin: &Path,
    cargo_bin: Option<&Path>,
    path_var: Option<&std::ffi::OsStr>,
    exe_suffix: &str,
) -> Option<PathBuf> {
    let cm_exe = exe_name_for_suffix("cargo-miri", exe_suffix);
    for dir in miri_setup_search_dirs(rust_sysroot, miri_bin, cargo_bin, path_var) {
        let cand = dir.join(&cm_exe);
        if is_executable_file(&cand) {
            return canonicalize_preserving_rustup_proxy_with_suffix(
                &cand,
                Some(rust_sysroot),
                "cargo-miri",
                exe_suffix,
            )
            .ok()
            .or(Some(cand));
        }
    }
    None
}

fn walk_rust_src_tree(
    current_dir: &Path,
    rel_prefix: &str,
    canon_root: &Path,
    backing_src_root: Option<&Path>,
    active_dirs: &mut BTreeSet<PathBuf>,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<(), String> {
    let mut dir_entries = Vec::new();
    for entry in
        fs::read_dir(current_dir).map_err(|e| format!("read_dir {}: {e}", current_dir.display()))?
    {
        let entry = entry.map_err(|e| format!("iterate {}: {e}", current_dir.display()))?;
        dir_entries.push(entry);
    }
    dir_entries.sort_by_key(|e| e.file_name());

    for entry in dir_entries {
        let raw_name = entry.file_name();
        let name = raw_name.to_str().ok_or_else(|| {
            format!("non-UTF-8 path entry in {}: {raw_name:?}", current_dir.display())
        })?;
        let path = entry.path();
        let sym_meta =
            fs::symlink_metadata(&path).map_err(|e| format!("inspect {}: {e}", path.display()))?;
        let ft = sym_meta.file_type();
        if name == ".git" && ft.is_dir() {
            continue;
        }
        let rel_path =
            if rel_prefix.is_empty() { name.to_string() } else { format!("{rel_prefix}/{name}") };

        if ft.is_symlink() {
            let target_canon = fs::canonicalize(&path)
                .map_err(|e| format!("resolve symlink {}: {e}", path.display()))?;
            let in_backing = backing_src_root.is_some_and(|b| target_canon.starts_with(b));
            if !target_canon.starts_with(canon_root) && !in_backing {
                return Err(format!(
                    "`rust-src` symlink {} escapes canonical `rust-src` root {} -> {}",
                    path.display(),
                    canon_root.display(),
                    target_canon.display()
                ));
            }
            let target_meta = fs::metadata(&target_canon)
                .map_err(|e| format!("stat symlink target {}: {e}", target_canon.display()))?;
            if target_meta.is_file() {
                out.push((rel_path, target_canon));
            } else if target_meta.is_dir() {
                if name == ".git" {
                    continue;
                }
                if !active_dirs.insert(target_canon.clone()) {
                    return Err(format!(
                        "`rust-src` symlink directory cycle at {}",
                        path.display()
                    ));
                }
                walk_rust_src_tree(
                    &target_canon,
                    &rel_path,
                    canon_root,
                    backing_src_root,
                    active_dirs,
                    out,
                )?;
                active_dirs.remove(&target_canon);
            } else {
                return Err(format!(
                    "unsupported special file symlink target {} in `rust-src` at {}",
                    target_canon.display(),
                    path.display()
                ));
            }
        } else if ft.is_dir() {
            let dir_canon = fs::canonicalize(&path)
                .map_err(|e| format!("canonicalize directory {}: {e}", path.display()))?;
            if !active_dirs.insert(dir_canon.clone()) {
                return Err(format!("`rust-src` directory cycle at {}", path.display()));
            }
            walk_rust_src_tree(&path, &rel_path, canon_root, backing_src_root, active_dirs, out)?;
            active_dirs.remove(&dir_canon);
        } else if ft.is_file() {
            out.push((rel_path, path));
        } else {
            return Err(format!("unsupported special file in `rust-src`: {}", path.display()));
        }
    }
    Ok(())
}

fn compute_rust_src_digest(
    rust_sysroot: &Path,
    backing_sysroot: Option<&Path>,
) -> Result<String, String> {
    let rust_src = rust_sysroot.join("lib/rustlib/src/rust");
    if !rust_src.is_dir() {
        return Err(format!("missing `rust-src` directory at {}", rust_src.display()));
    }
    let core_toml = rust_src.join("library/core/Cargo.toml");
    let alloc_toml = rust_src.join("library/alloc/Cargo.toml");
    if !core_toml.is_file() || !alloc_toml.is_file() {
        return Err(format!(
            "`rust-src` at {} missing required `library/core/Cargo.toml` or `library/alloc/Cargo.toml`",
            rust_src.display()
        ));
    }
    let root_lock = rust_src.join("Cargo.lock");
    let lib_lock = rust_src.join("library/Cargo.lock");
    if !root_lock.is_file() && !lib_lock.is_file() {
        return Err(format!(
            "`rust-src` at {} missing `Cargo.lock` (checked `Cargo.lock` and `library/Cargo.lock`)",
            rust_src.display()
        ));
    }

    let canon_root = fs::canonicalize(&rust_src)
        .map_err(|e| format!("canonicalize `rust-src` {}: {e}", rust_src.display()))?;
    let backing_src_root = match backing_sysroot {
        Some(b) => fs::canonicalize(b.join("lib/rustlib/src/rust")).ok(),
        None => None,
    };
    let mut active_dirs = BTreeSet::from([canon_root.clone()]);
    let mut files = Vec::new();
    walk_rust_src_tree(
        &canon_root,
        "",
        &canon_root,
        backing_src_root.as_deref(),
        &mut active_dirs,
        &mut files,
    )?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let hashed = stream_hash_sorted_entries(&files)?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-rust-src-v2\0");
    hasher.update((hashed.len() as u64).to_le_bytes());
    for (rel, byte_len, file_sha) in &hashed {
        update_len_prefixed(&mut hasher, rel.as_bytes());
        hasher.update(byte_len.to_le_bytes());
        hasher.update(file_sha);
    }
    Ok(sha256_hex(&hasher.finalize()))
}

fn update_len_prefixed(hasher: &mut Sha256, field: &[u8]) {
    hasher.update((field.len() as u64).to_le_bytes());
    hasher.update(field);
}

fn walk_regular_built_sysroot_tree(
    dir: &Path,
    prefix: &str,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<(), String> {
    let mut entries = Vec::new();
    for entry in fs::read_dir(dir).map_err(|e| format!("read_dir {}: {e}", dir.display()))? {
        let entry = entry.map_err(|e| format!("iterate {}: {e}", dir.display()))?;
        let raw = entry.file_name();
        let name = raw
            .to_str()
            .ok_or_else(|| format!("non-UTF-8 entry in {}: {raw:?}", dir.display()))?
            .to_string();
        entries.push((name, entry.path()));
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    for (name, path) in entries {
        let sym = fs::symlink_metadata(&path)
            .map_err(|e| format!("inspect built sysroot entry {}: {e}", path.display()))?;
        let ft = sym.file_type();
        let rel = if prefix.is_empty() { name } else { format!("{prefix}/{name}") };
        if ft.is_symlink() {
            return Err(format!("unexpected symlink in built Miri sysroot: {}", path.display()));
        } else if ft.is_dir() {
            walk_regular_built_sysroot_tree(&path, &rel, out)?;
        } else if ft.is_file() {
            out.push((rel, path));
        } else {
            return Err(format!(
                "unsupported special file in built Miri sysroot: {}",
                path.display()
            ));
        }
    }
    Ok(())
}

fn compute_built_miri_sysroot_digest(
    sysroot_dir: &Path,
    target: &str,
) -> Result<(usize, String), String> {
    let rustlib_dir = sysroot_dir.join("lib/rustlib");
    let rustlib_sym = fs::symlink_metadata(&rustlib_dir)
        .map_err(|e| format!("inspect Miri rustlib {}: {e}", rustlib_dir.display()))?;
    if !rustlib_sym.file_type().is_dir() {
        return Err(format!("Miri rustlib {} is not a real directory", rustlib_dir.display()));
    }
    let target_lib_prefix = format!("{target}/lib/");
    let mut files = Vec::new();
    walk_regular_built_sysroot_tree(&rustlib_dir, "", &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let hashed = stream_hash_sorted_entries(&files)?;
    let mut saw_target_crate = false;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-built-v1\0");
    hasher.update((hashed.len() as u64).to_le_bytes());
    for (rel, byte_len, file_sha) in &hashed {
        let is_compiled_lib =
            matches!(Path::new(rel).extension().and_then(|s| s.to_str()), Some("rlib" | "rmeta"));
        if is_compiled_lib && *byte_len == 0 {
            return Err(format!("empty compiled Miri sysroot artifact `{rel}`"));
        }
        if is_compiled_lib && rel.starts_with(&target_lib_prefix) {
            saw_target_crate = true;
        }
        update_len_prefixed(&mut hasher, rel.as_bytes());
        hasher.update(byte_len.to_le_bytes());
        hasher.update(file_sha);
    }
    if !saw_target_crate {
        return Err(format!(
            "built Miri sysroot at {} missing non-empty `{target_lib_prefix}*.rlib`/`.rmeta`",
            sysroot_dir.display()
        ));
    }
    Ok((hashed.len(), sha256_hex(&hasher.finalize())))
}

#[allow(clippy::too_many_arguments)]
fn compute_composite_miri_sha256(
    schema_version: u32,
    target: &str,
    rustc_vv: &str,
    rustc_bin_sha256: &str,
    rustc_host_libs_sha256: &str,
    miri_version_verbose: &str,
    miri_bin_sha256: &str,
    cargo_bin_sha256: Option<&str>,
    cargo_miri_bin_sha256: Option<&str>,
    rust_src_sha256: &str,
) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-sysroot-v4\0");
    hasher.update(schema_version.to_le_bytes());
    update_len_prefixed(&mut hasher, target.as_bytes());
    update_len_prefixed(&mut hasher, rustc_vv.as_bytes());
    update_len_prefixed(&mut hasher, rustc_bin_sha256.as_bytes());
    update_len_prefixed(&mut hasher, rustc_host_libs_sha256.as_bytes());
    update_len_prefixed(&mut hasher, miri_version_verbose.as_bytes());
    update_len_prefixed(&mut hasher, miri_bin_sha256.as_bytes());
    match cargo_bin_sha256 {
        Some(cb) => {
            hasher.update([1u8]);
            update_len_prefixed(&mut hasher, cb.as_bytes());
        }
        None => {
            hasher.update([0u8]);
        }
    }
    match cargo_miri_bin_sha256 {
        Some(cm) => {
            hasher.update([1u8]);
            update_len_prefixed(&mut hasher, cm.as_bytes());
        }
        None => {
            hasher.update([0u8]);
        }
    }
    update_len_prefixed(&mut hasher, rust_src_sha256.as_bytes());
    sha256_hex(&hasher.finalize())
}

#[derive(Serialize)]
struct ScratchCargoConfig {
    source: ScratchCargoSources,
}

#[derive(Serialize)]
struct ScratchCargoSources {
    #[serde(rename = "crates-io")]
    crates_io: ScratchCratesIoReplace,
    #[serde(rename = "vendored-sources")]
    vendored_sources: ScratchVendorDir,
}

#[derive(Serialize)]
struct ScratchCratesIoReplace {
    #[serde(rename = "replace-with")]
    replace_with: &'static str,
}

#[derive(Serialize)]
struct ScratchVendorDir {
    directory: String,
}

fn build_offline_miri_sysroot(
    rust_sysroot: &Path,
    cargo_bin: &Path,
    miri_bin: &Path,
    target_triple: &str,
    target_dir: &Path,
) -> Result<(), String> {
    let rustc = fs::canonicalize(rust_sysroot.join("bin").join(exe_name("rustc")))
        .map_err(|e| format!("canonicalize rustc: {e}"))?;
    let vendor_dir = rust_sysroot.join("lib/rustlib/src/rust/library/vendor");
    if !vendor_dir.is_dir() {
        return Err(format!("missing vendored rust-src deps at {}", vendor_dir.display()));
    }
    let canon_vendor = fs::canonicalize(&vendor_dir)
        .map_err(|e| format!("canonicalize vendored rust-src: {e}"))?;

    let parent = target_dir
        .parent()
        .ok_or_else(|| format!("target dir has no parent: {}", target_dir.display()))?;
    let staging = tempfile::Builder::new()
        .prefix("itree-miri-staging-")
        .tempdir_in(parent)
        .map_err(|e| format!("create Miri staging dir: {e}"))?;
    let scratch_cargo_home = tempfile::Builder::new()
        .prefix("itree-miri-cargo-")
        .tempdir()
        .map_err(|e| format!("create Miri CARGO_HOME: {e}"))?;
    let scratch_home = tempfile::Builder::new()
        .prefix("itree-miri-home-")
        .tempdir()
        .map_err(|e| format!("create Miri HOME: {e}"))?;
    let cfg = ScratchCargoConfig {
        source: ScratchCargoSources {
            crates_io: ScratchCratesIoReplace { replace_with: "vendored-sources" },
            vendored_sources: ScratchVendorDir {
                directory: canon_vendor.to_string_lossy().into_owned(),
            },
        },
    };
    let toml_text = toml::to_string(&cfg).map_err(|e| format!("serialize Miri config: {e}"))?;
    fs::write(scratch_cargo_home.path().join("config.toml"), toml_text)
        .map_err(|e| format!("write offline Miri Cargo config: {e}"))?;

    let scratch_tmp = scratch_home.path().join("tmp");
    fs::create_dir_all(&scratch_tmp).map_err(|e| format!("create Miri scratch tmp: {e}"))?;
    let path_var = env::var_os("PATH");
    let setup_dirs =
        miri_setup_search_dirs(rust_sysroot, miri_bin, Some(cargo_bin), path_var.as_deref());
    let joined_path = env::join_paths(&setup_dirs).map_err(|e| format!("join Miri PATH: {e}"))?;
    let cargo_miri_bin = resolve_cargo_miri_binary_with_path_and_suffix(
        rust_sysroot,
        miri_bin,
        Some(cargo_bin),
        path_var.as_deref(),
        env::consts::EXE_SUFFIX,
    )
    .ok_or_else(|| {
        format!("cannot locate `cargo-miri` executable across setup search paths {:?}", setup_dirs)
    })?;

    let inv = build_miri_setup_invocation_with_env(
        rust_sysroot,
        &rustc,
        cargo_bin,
        miri_bin,
        &cargo_miri_bin,
        target_triple,
        staging.path(),
        scratch_home.path(),
        scratch_cargo_home.path(),
        &scratch_tmp,
        &joined_path,
        |k| env::var_os(k),
    )?;

    let out = run_supervised(&inv, scratch_home.path(), MIRI_SETUP_TIMEOUT_SECS)?;
    match out.termination {
        Termination::Exited(status) if status.success() => {}
        other => {
            return Err(format!(
                "`cargo miri setup` failed ({}):\nstdout:\n{}\nstderr:\n{}",
                other.describe(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }

    if target_dir.exists() {
        fs::remove_dir_all(target_dir)
            .map_err(|e| format!("clean stale {}: {e}", target_dir.display()))?;
    }
    let staged = staging.keep();
    fs::rename(&staged, target_dir).map_err(|e| {
        let _ = fs::remove_dir_all(&staged);
        format!("promote Miri sysroot: {e}")
    })?;
    Ok(())
}

/// Build the clean-environment direct `miri` execution [`Invocation`],
/// preserving host temporary/profile/Windows OS variables and falling back to
/// `fallback_temp` if no temp variable is set.
#[allow(clippy::too_many_arguments)]
pub fn build_miri_run_invocation_with_env(
    miri_bin: &Path,
    target_triple: &str,
    remap_arg: &str,
    miri_sysroot: &Path,
    harness_path: &Path,
    dylib_path: &OsStr,
    path_env: &OsStr,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let inv = Invocation::new(
        miri_bin,
        &["--edition=2024", "--error-format=json", "--target", target_triple],
    )
    .arg("--remap-path-prefix")
    .arg(remap_arg)
    .arg("--remap-path-scope=diagnostics")
    .arg("--sysroot")
    .arg(miri_sysroot)
    .arg("-C")
    .arg("opt-level=0")
    .arg("-C")
    .arg("debug-assertions=no")
    .arg("-C")
    .arg("overflow-checks=no")
    .arg("-Zmiri-tree-borrows")
    .arg("-Zmiri-backtrace=1")
    .arg(harness_path)
    .env(DYLIB_PATH_ENV_VAR, dylib_path)
    .env("PATH", path_env);
    forward_platform_temp_and_profile_env_with_env(inv, fallback_temp, get_env)
}

/// Build the clean-environment `cargo miri setup` invocation, preserving
/// resolved `RUSTUP_HOME` / `RUSTUP_TOOLCHAIN` state (or failing closed if a
/// `rustup` proxy toolchain cannot be pinned to `rust_sysroot`).
#[allow(clippy::too_many_arguments)]
pub fn build_miri_setup_invocation_with_env(
    rust_sysroot: &Path,
    rustc: &Path,
    cargo_bin: &Path,
    miri_bin: &Path,
    cargo_miri_bin: &Path,
    target_triple: &str,
    miri_sysroot_staging: &Path,
    scratch_home: &Path,
    scratch_cargo_home: &Path,
    scratch_tmp: &Path,
    joined_path: &std::ffi::OsStr,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<Invocation, String> {
    let mut inv = Invocation::new(cargo_miri_bin, &["miri", "setup", "--target", target_triple])
        .env("CARGO", cargo_bin)
        .env("PATH", joined_path)
        .env("HOME", scratch_home)
        .env("USERPROFILE", scratch_home)
        .env("CARGO_HOME", scratch_cargo_home)
        .env("TMPDIR", scratch_tmp)
        .env("TEMP", scratch_tmp)
        .env("TMP", scratch_tmp)
        .env("RUSTC", rustc)
        .env("MIRI", miri_bin)
        .env("MIRI_SYSROOT", miri_sysroot_staging)
        .env("CARGO_NET_OFFLINE", "true")
        .env(DYLIB_PATH_ENV_VAR, join_dylib_path(&rust_sysroot.join("lib")));
    inv = forward_env_keys_with_env(inv, &["SystemRoot", "WINDIR"], &get_env);

    if is_rustup_proxy_executable(cargo_miri_bin) || is_rustup_proxy_executable(cargo_bin) {
        let (rustup_home, rustup_toolchain) =
            resolve_rustup_env_for_sysroot_with_env(rust_sysroot, get_env);
        if let Some(rh) = rustup_home {
            inv = inv.env("RUSTUP_HOME", rh);
        }
        match rustup_toolchain {
            Some(rt) => {
                inv = inv.env("RUSTUP_TOOLCHAIN", rt);
            }
            None => {
                return Err(format!(
                    "cannot pin rustup-backed `cargo-miri` setup ({}) to selected sysroot {}: sysroot is not under `toolchains/` and RUSTUP_TOOLCHAIN is unset",
                    cargo_miri_bin.display(),
                    rust_sysroot.display(),
                ));
            }
        }
    }
    Ok(inv)
}

fn run_supervised(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
) -> Result<ProcessOutcome, String> {
    run_supervised_with_prefix("anneal-itree-miri-sup-", inv, Some(work_dir), timeout_secs)
}
