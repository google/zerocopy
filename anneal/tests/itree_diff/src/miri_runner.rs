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

mod diagnostics;
mod digest;
mod discovery;
mod invocation;

pub use diagnostics::*;
pub use digest::*;
pub use discovery::*;
pub use invocation::*;

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
