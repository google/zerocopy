// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Lean 4 `Trusted.MirSemantics` trace-stepping authority (zero edits to
//! `trusted/lean/`).
//!
//! Captures Rust MIR via `anneal-rustc-capture` and runs a temporary test-only
//! Lean 4 trace driver importing `Trusted.MirSemantics` and
//! `Anneal.MirTotal.ExecTotal` in two explicit modes:
//!
//! 1. **Strict Verbatim Mode (`LeanTraceMode::StrictVerbatim`)**: Steps
//!    `evalMirStepBy (mirTyBeqAt 64)` directly (matching
//!    `Trusted.MirSemantics.evalStep` across all `MirTy` trees of nesting depth
//!    `< 64` for single bodies, `.sysrootCall`, and safe intra-crate `.call`s),
//!    logging every `switchInt` branch tag, call boundary, boundary byte
//!    snapshot, and final `TerminalOut` or `FaultKind`. Confirms external
//!    callees and unmodeled `.cleanup`/`.coreCall`/`.unwindResume` constructs
//!    conservatively fault with `.fault .unsupported`.
//! 2. **Compositional Multi-Call ITree Mode
//!    (`LeanTraceMode::CompositionalITree`)**: Uses `Anneal.MirTotal`'s
//!    computable `evalOperandToSlotComp`, `writePlaceBy`, `initLocalsLoopComp`,
//!    and `evalMirStepBy (mirTyBeqAt 64)` to step multi-call stacks (both real
//!    captured callee bodies and scheduled `EnvSchedule` `ReturnBytes`,
//!    `Unwind`, and `Abort` actions decoded against the callee return `MirTy`),
//!    recording the full `ObservableSpine` and verifying `CallerFrameLaw`
//!    across every call return and cleanup unwind.

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::{OsStr, OsString},
    fmt::Write as _,
    fs::{self, File},
    io::{self, Read},
    path::{Path, PathBuf},
    thread,
    time::Instant,
};

use anneal_testkit::{Invocation, ProcessOutcome, Termination, ToolchainEnv, ToolchainMode};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    outcome::{
        AuthorityRunResult, CallerFrameLaw, IntKind, MetamorphicStatus, OrderingVal,
        TerminalOutcome, TraceVal, compute_boundary_mem_digest, sha256_hex,
        validate_boundary_slots_for_outcome,
    },
    rustc_runner::{
        DYLIB_PATH_ENV_VAR, atomic_write_file, build_child_path,
        canonicalize_preserving_rustup_proxy_with_suffix, exe_name, exe_name_for_suffix,
        forward_platform_temp_and_profile_env_with_env, forward_standard_tool_env_with_env,
        is_rustup_proxy_executable, join_dylib_path, parse_and_validate_host_target_triple,
        query_rustc_host_target, resolve_explicit_or_path_exe_with_suffix,
        resolve_rustup_env_for_sysroot_with_env, resolve_verified_backing_sysroot_with_suffix,
        run_probe_supervised, run_supervised_with_prefix,
    },
    spec::{LeanProgramSpec, TraceTestCase},
    trace_observer::{EnvAction, EnvSchedule, ObservableEvent, ObservableSpine},
};

const CAPTURE_TIMEOUT_SECS: u64 = 120;
const CAPTURE_BUILD_TIMEOUT_SECS: u64 = 300;
const LEAN_COMPILE_TIMEOUT_SECS: u64 = 180;
const LEAN_EVAL_TIMEOUT_SECS: u64 = 180;
const LEAN_TRACE_PREFIX: &str = "ANNEAL_LEAN_ITREE_JSON:";

const LEAN_COMPILE_FLAGS: &[&str] =
    &["-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false"];

/// Execution mode for the Lean `Trusted.MirSemantics` trace driver.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LeanTraceMode {
    /// Strict verbatim `evalMirStepBy (mirTyBeqAt 64)` direct stepping.
    StrictVerbatim,
    /// Compositional multi-call ITree continuation stepping at the driver
    /// level.
    CompositionalITree,
}

impl LeanTraceMode {
    pub fn authority_name(self) -> &'static str {
        match self {
            Self::StrictVerbatim => "lean-strict-verbatim",
            Self::CompositionalITree => "lean-compositional-itree",
        }
    }

    fn lean_mode_ident(self) -> &'static str {
        match self {
            Self::StrictVerbatim => "TraceMode.strictVerbatim",
            Self::CompositionalITree => "TraceMode.compositionalITree",
        }
    }
}

/// Receipt for a full-authority metamorphic inlining duality check comparing a
/// multi-call program (`CompositionalITree` + `rustc O0/O2` + `miri`) against
/// its source-inlined single-body twin (`StrictVerbatim` + `rustc O0/O2` +
/// `miri`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetamorphicDualityReceipt {
    pub called_lean: AuthorityRunResult,
    pub inlined_lean: AuthorityRunResult,
    pub inlined_rustc_parity_ok: bool,
    pub inlined_miri_matched: Option<bool>,
    pub tool_error: Option<(String, String)>,
    pub status: MetamorphicStatus,
    pub duality_holds: bool,
    pub detail: String,
    #[serde(default)]
    pub failed_relations: Vec<String>,
    #[serde(default)]
    pub twin_outcome_summary: String,
}

#[derive(Clone, Copy)]
struct LeanDagSpec {
    module: &'static str,
    rel_tree: &'static str,
    deps: &'static [&'static str],
}

const MIR_TOTAL_DAG: &[LeanDagSpec] = &[
    LeanDagSpec { module: "Trusted", rel_tree: "trusted/lean", deps: &[] },
    LeanDagSpec { module: "Trusted.MirAst.Types", rel_tree: "trusted/lean", deps: &[] },
    LeanDagSpec {
        module: "Trusted.MirAst.Places",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst.Types"],
    },
    LeanDagSpec {
        module: "Trusted.MirAst.Rvalues",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst.Types", "Trusted.MirAst.Places"],
    },
    LeanDagSpec {
        module: "Trusted.MirAst.Statements",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst.Types", "Trusted.MirAst.Places", "Trusted.MirAst.Rvalues"],
    },
    LeanDagSpec {
        module: "Trusted.MirAst.Terminators",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst.Types", "Trusted.MirAst.Places", "Trusted.MirAst.Rvalues"],
    },
    LeanDagSpec {
        module: "Trusted.MirAst.Body",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst.Types", "Trusted.MirAst.Statements", "Trusted.MirAst.Terminators"],
    },
    LeanDagSpec {
        module: "Trusted.MirAst",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst.Types",
            "Trusted.MirAst.Places",
            "Trusted.MirAst.Rvalues",
            "Trusted.MirAst.Statements",
            "Trusted.MirAst.Terminators",
            "Trusted.MirAst.Body",
        ],
    },
    LeanDagSpec { module: "Trusted.MirModel", rel_tree: "trusted/lean", deps: &["Trusted.MirAst"] },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Ops",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst", "Trusted.MirModel"],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Enum",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst", "Trusted.MirModel", "Trusted.MirSemantics.Ops"],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Layout",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst", "Trusted.MirSemantics.Enum"],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Memory",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst", "Trusted.MirModel", "Trusted.MirSemantics.Layout"],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Bytes",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics.Ops",
            "Trusted.MirSemantics.Enum",
            "Trusted.MirSemantics.Layout",
            "Trusted.MirSemantics.Memory",
        ],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.State",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics.Enum",
            "Trusted.MirSemantics.Memory",
            "Trusted.MirSemantics.Bytes",
        ],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.CoreContracts",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics.Ops",
            "Trusted.MirSemantics.Enum",
            "Trusted.MirSemantics.Layout",
            "Trusted.MirSemantics.Memory",
            "Trusted.MirSemantics.Bytes",
        ],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Step",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics.Ops",
            "Trusted.MirSemantics.Enum",
            "Trusted.MirSemantics.Layout",
            "Trusted.MirSemantics.Memory",
            "Trusted.MirSemantics.Bytes",
            "Trusted.MirSemantics.CoreContracts",
            "Trusted.MirSemantics.State",
        ],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Boundary",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics.Enum",
            "Trusted.MirSemantics.State",
            "Trusted.MirSemantics.Step",
        ],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.CanaryFixtures",
        rel_tree: "trusted/lean",
        deps: &["Trusted.MirAst", "Trusted.MirModel", "Trusted.MirSemantics.Boundary"],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics.Contract",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics.Enum",
            "Trusted.MirSemantics.Ops",
            "Trusted.MirSemantics.State",
            "Trusted.MirSemantics.Step",
            "Trusted.MirSemantics.Boundary",
        ],
    },
    LeanDagSpec {
        module: "Trusted.MirSemantics",
        rel_tree: "trusted/lean",
        deps: &[
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics.Ops",
            "Trusted.MirSemantics.Enum",
            "Trusted.MirSemantics.Layout",
            "Trusted.MirSemantics.Memory",
            "Trusted.MirSemantics.Bytes",
            "Trusted.MirSemantics.CoreContracts",
            "Trusted.MirSemantics.State",
            "Trusted.MirSemantics.Step",
            "Trusted.MirSemantics.Boundary",
            "Trusted.MirSemantics.CanaryFixtures",
            "Trusted.MirSemantics.Contract",
        ],
    },
    LeanDagSpec {
        module: "Anneal.Framework.StepWp",
        rel_tree: "theory",
        deps: &["Trusted.MirModel"],
    },
    LeanDagSpec {
        module: "Anneal.MirWp.Core",
        rel_tree: "theory",
        deps: &["Trusted", "Trusted.MirAst", "Trusted.MirSemantics", "Anneal.Framework.StepWp"],
    },
    LeanDagSpec { module: "Anneal.NatBitwise", rel_tree: "theory", deps: &[] },
    LeanDagSpec {
        module: "Anneal.MirWp.Scalars",
        rel_tree: "theory",
        deps: &[
            "Trusted",
            "Trusted.MirAst",
            "Trusted.MirSemantics",
            "Anneal.NatBitwise",
            "Anneal.MirWp.Core",
        ],
    },
    LeanDagSpec {
        module: "Anneal.MirWp.Reflection",
        rel_tree: "theory",
        deps: &[
            "Trusted",
            "Trusted.MirAst",
            "Trusted.MirSemantics",
            "Anneal.MirWp.Core",
            "Anneal.MirWp.Scalars",
        ],
    },
    LeanDagSpec {
        module: "Anneal.MirWp.Execution",
        rel_tree: "theory",
        deps: &[
            "Trusted",
            "Trusted.MirAst",
            "Trusted.MirSemantics",
            "Anneal.MirWp.Core",
            "Anneal.MirWp.Scalars",
            "Anneal.MirWp.Reflection",
        ],
    },
    LeanDagSpec {
        module: "Anneal.MirWp",
        rel_tree: "theory",
        deps: &[
            "Trusted",
            "Trusted.MirAst",
            "Trusted.MirSemantics",
            "Anneal.MirWp.Core",
            "Anneal.MirWp.Scalars",
            "Anneal.MirWp.Reflection",
            "Anneal.MirWp.Execution",
        ],
    },
    LeanDagSpec {
        module: "Anneal.MirTotal.Ops",
        rel_tree: "theory",
        deps: &["Trusted", "Trusted.MirAst", "Trusted.MirModel", "Trusted.MirSemantics"],
    },
    LeanDagSpec {
        module: "Anneal.MirTotal.StepCore",
        rel_tree: "theory",
        deps: &[
            "Trusted",
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics",
            "Anneal.MirWp",
            "Anneal.MirTotal.Ops",
        ],
    },
    LeanDagSpec {
        module: "Anneal.MirTotal.ExecTotal",
        rel_tree: "theory",
        deps: &[
            "Trusted",
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics",
            "Anneal.MirWp",
            "Anneal.MirTotal.StepCore",
        ],
    },
];

/// Prepared Lean 4 + `anneal-rustc-capture` session with content-addressed
/// `.olean` and capture caches keyed on binary, compiler, and Lean digests.
#[derive(Clone, Debug)]
pub struct LeanTraceSession {
    pub anneal_root: PathBuf,
    pub cache_root: PathBuf,
    pub capture_bin: PathBuf,
    pub capture_bin_sha256: String,
    pub rust_sysroot: PathBuf,
    pub host_target: String,
    pub rustc_version_digest: String,
    pub lean_bin: PathBuf,
    pub lean_driver_digest: String,
    pub olean_paths: Vec<PathBuf>,
    pub dylib_search_path: OsString,
    pub child_path: OsString,
}

/// Captured artifact metadata from one `anneal-rustc-capture` invocation.
#[derive(Clone, Debug)]
pub struct CapturedArtifacts {
    pub capture_dir: PathBuf,
    pub capture_json: PathBuf,
    pub captured_lean: PathBuf,
    pub olean_dir: PathBuf,
    pub body_ids_by_fn: BTreeMap<String, usize>,
}

/// Outcome of attempting `anneal-rustc-capture` on a Rust fixture.
#[derive(Clone, Debug)]
pub enum CaptureAttempt {
    Captured(CapturedArtifacts),
    Refused { reason: String },
    ToolError { detail: String },
}

#[derive(Deserialize)]
struct CaptureStatusRaw {
    status: String,
    #[serde(default)]
    capture: Option<PathBuf>,
    #[serde(default)]
    lean: Option<PathBuf>,
    #[serde(default)]
    diagnostics: Vec<String>,
    #[serde(default)]
    unsupported: Vec<serde_json::Value>,
    #[serde(default)]
    reason: Option<String>,
    #[serde(default)]
    message: Option<String>,
}

#[derive(Deserialize)]
struct CaptureManifest {
    program: CaptureProgram,
}

#[derive(Deserialize)]
struct CaptureProgram {
    bodies: Vec<CaptureBody>,
}

#[derive(Deserialize)]
struct CaptureBody {
    identity: String,
}

impl LeanTraceSession {
    /// Resolve `lean`, `rust_sysroot`, and `anneal-rustc-capture` via
    /// `ToolchainEnv::resolve` (building `anneal-rustc-capture` into
    /// `cache_root` with the active Cargo/sysroot toolchain only when
    /// `ANNEAL_CAPTURE` / `ANNEAL_TEST_INSTALL_ROOT` is unset), compute exact
    /// binary/compiler/Lean digests for cache invalidation, and compile
    /// `Trusted.*`, `Anneal.MirTotal.*`, and `ITreeDriver.olean`.
    pub fn prepare(anneal_root: &Path, cache_root: &Path) -> Result<Self, String> {
        let tools = ToolchainEnv::resolve(ToolchainMode::WorkspaceBuild {
            cli_bin: None,
            capture_bin: None,
            auditor_bin: None,
        })?;
        let rust_sysroot = fs::canonicalize(&tools.sysroot)
            .map_err(|e| format!("canonicalize rust sysroot: {e}"))?;
        let lean_bin =
            fs::canonicalize(&tools.lean).map_err(|e| format!("canonicalize lean bin: {e}"))?;
        let dylib_search_path = join_dylib_path(&rust_sysroot.join("lib"));
        let child_path = build_child_path(&rust_sysroot.join("bin"))?;

        let sysroot_rustc = rust_sysroot.join("bin").join(exe_name("rustc"));
        let host_target = query_rustc_host_target(&sysroot_rustc, Some(&rust_sysroot))?;
        let rustc_version_digest = compute_rustc_sysroot_digest(&rust_sysroot)?;
        let capture_bin = match tools.capture {
            Some(bin) => bin,
            None => ensure_capture_binary(
                anneal_root,
                cache_root,
                &rust_sysroot,
                &rustc_version_digest,
                &child_path,
            )?,
        };
        let capture_bytes = fs::read(&capture_bin)
            .map_err(|e| format!("read capture binary {}: {e}", capture_bin.display()))?;
        let capture_bin_sha256 = sha256_hex(&capture_bytes);

        let lean_prefix = query_lean_prefix(&lean_bin)?;
        let lean_stdlib = lean_prefix.join("lib/lean");
        let (olean_paths, lean_driver_digest) =
            ensure_lean_and_driver_oleans(anneal_root, &lean_bin, &lean_stdlib, cache_root)?;

        Ok(Self {
            anneal_root: anneal_root.to_path_buf(),
            cache_root: cache_root.to_path_buf(),
            capture_bin,
            capture_bin_sha256,
            rust_sysroot,
            host_target,
            rustc_version_digest,
            lean_bin,
            lean_driver_digest,
            olean_paths,
            dylib_search_path,
            child_path,
        })
    }

    pub fn lean_path_with(&self, extra_dir: Option<&Path>) -> Result<String, String> {
        let mut entries = Vec::new();
        if let Some(dir) = extra_dir {
            entries.push(dir.to_path_buf());
        }
        entries.extend(self.olean_paths.iter().cloned());
        env::join_paths(entries)
            .map(|s| s.to_string_lossy().into_owned())
            .map_err(|e| format!("join LEAN_PATH: {e}"))
    }

    /// Invoke `anneal-rustc-capture` on `source_text` selecting `select_fns`,
    /// caching `Captured.olean` or `.captured-refused` under a key that binds
    /// `capture_bin_sha256`, `rustc_version_digest`, `lean_driver_digest`,
    /// `crate_name`, `source_text`, and `select_fns`.
    pub fn capture_rust_source(
        &self,
        _work_dir: &Path,
        crate_name: &str,
        source_text: &str,
        select_fns: &[String],
    ) -> CaptureAttempt {
        let mut sorted_fns: Vec<&str> = select_fns.iter().map(String::as_str).collect();
        sorted_fns.sort_unstable();

        let mut h = Sha256::new();
        h.update(b"anneal-itree-capture-v3\0");
        h.update(self.capture_bin_sha256.as_bytes());
        h.update(b"\0");
        h.update(self.rustc_version_digest.as_bytes());
        h.update(b"\0");
        h.update(self.lean_driver_digest.as_bytes());
        h.update(b"\0");
        h.update(crate_name.as_bytes());
        h.update(b"\0");
        h.update((source_text.len() as u64).to_le_bytes());
        h.update(source_text.as_bytes());
        for s in sorted_fns {
            h.update(b"\0");
            h.update(s.as_bytes());
        }
        let key = sha256_hex(&h.finalize())[..24].to_string();
        let cap_cache_dir = self.cache_root.join(format!("captured-{key}"));
        let cap_lock_path = self.cache_root.join(format!("captured-{key}.lock"));
        if let Err(e) = fs::create_dir_all(&self.cache_root) {
            return CaptureAttempt::ToolError { detail: format!("create cache root: {e}") };
        }
        let lock_file = match File::options()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&cap_lock_path)
        {
            Ok(f) => f,
            Err(e) => {
                return CaptureAttempt::ToolError { detail: format!("open capture lock: {e}") };
            }
        };
        if let Err(e) = lock_file.lock() {
            return CaptureAttempt::ToolError { detail: format!("lock capture cache: {e}") };
        }

        let ready_ok = cap_cache_dir.join(".captured-ok");
        let ready_refused = cap_cache_dir.join(".captured-refused");
        let out_dir = cap_cache_dir.join("capture_out");
        let olean_dir = cap_cache_dir.join("olean_out");
        let capture_json = out_dir.join("capture.json");
        let captured_lean = out_dir.join("Captured.lean");

        if validate_cached_artifact_manifest(
            &cap_cache_dir,
            &ready_ok,
            &key,
            EXPECTED_CAPTURE_CACHE_FILES,
        ) && let Ok(manifest_raw) = fs::read_to_string(&capture_json)
            && let Ok(manifest) = serde_json::from_str::<CaptureManifest>(&manifest_raw)
        {
            let mut body_ids_by_fn = BTreeMap::new();
            let mut all_ok = true;
            for sel in select_fns {
                match select_captured_body_idx(&manifest.program.bodies, sel) {
                    Ok(idx) => {
                        body_ids_by_fn.insert(sel.clone(), idx);
                    }
                    Err(_) => {
                        all_ok = false;
                        break;
                    }
                }
            }
            if all_ok {
                return CaptureAttempt::Captured(CapturedArtifacts {
                    capture_dir: out_dir,
                    capture_json,
                    captured_lean,
                    olean_dir,
                    body_ids_by_fn,
                });
            }
        }
        if let Some(reason) = read_captured_refused_stamp(&ready_refused, &key) {
            return CaptureAttempt::Refused { reason };
        }

        if let Err(detail) = reset_cache_dir(&cap_cache_dir) {
            return CaptureAttempt::ToolError { detail };
        }

        let src_path = cap_cache_dir.join(format!("{crate_name}.rs"));
        if let Err(e) = fs::write(&src_path, source_text) {
            return CaptureAttempt::ToolError {
                detail: format!("write capture source {}: {e}", src_path.display()),
            };
        }
        let cap_inv = build_capture_invocation_with_env(
            &self.capture_bin,
            &src_path,
            crate_name,
            &self.host_target,
            &out_dir,
            &self.rust_sysroot,
            &self.dylib_search_path,
            &self.child_path,
            select_fns,
            None,
            |k| env::var_os(k),
        );

        let cap_out = match run_supervised_cmd(&cap_inv, &cap_cache_dir, CAPTURE_TIMEOUT_SECS) {
            Ok(o) => o,
            Err(detail) => return CaptureAttempt::ToolError { detail },
        };
        let stdout = String::from_utf8_lossy(&cap_out.stdout);
        let stderr = String::from_utf8_lossy(&cap_out.stderr);

        let exit_code = match cap_out.termination {
            Termination::Exited(status) => status.code(),
            other => {
                return CaptureAttempt::ToolError {
                    detail: format!(
                        "anneal-rustc-capture terminated abnormally ({}): stdout={stdout:?} stderr={stderr:?}",
                        other.describe()
                    ),
                };
            }
        };

        if let Ok(parsed) = serde_json::from_str::<CaptureStatusRaw>(stdout.trim()) {
            if parsed.status == "captured" {
                if exit_code != Some(0) {
                    return CaptureAttempt::ToolError {
                        detail: format!(
                            "anneal-rustc-capture reported status='captured' with non-zero exit {exit_code:?}"
                        ),
                    };
                }
                let (Some(capture_json), Some(captured_lean)) = (parsed.capture, parsed.lean)
                else {
                    return CaptureAttempt::ToolError {
                        detail: format!("capture status 'captured' missing paths: {stdout}"),
                    };
                };
                let manifest_raw = match fs::read_to_string(&capture_json) {
                    Ok(s) => s,
                    Err(e) => {
                        return CaptureAttempt::ToolError {
                            detail: format!("read {}: {e}", capture_json.display()),
                        };
                    }
                };
                let manifest: CaptureManifest = match serde_json::from_str(&manifest_raw) {
                    Ok(m) => m,
                    Err(e) => {
                        return CaptureAttempt::ToolError {
                            detail: format!("parse {}: {e}", capture_json.display()),
                        };
                    }
                };
                let mut body_ids_by_fn = BTreeMap::new();
                for sel in select_fns {
                    match select_captured_body_idx(&manifest.program.bodies, sel) {
                        Ok(idx) => {
                            body_ids_by_fn.insert(sel.clone(), idx);
                        }
                        Err(detail) => return CaptureAttempt::ToolError { detail },
                    }
                }
                if let Err(e) = fs::create_dir_all(&olean_dir) {
                    return CaptureAttempt::ToolError {
                        detail: format!("mkdir {}: {e}", olean_dir.display()),
                    };
                }
                let lean_path = match self.lean_path_with(Some(&olean_dir)) {
                    Ok(lp) => lp,
                    Err(detail) => return CaptureAttempt::ToolError { detail },
                };
                let compile_inv = build_lean_invocation(
                    &self.lean_bin,
                    &lean_path,
                    &[
                        OsString::from("-R"),
                        out_dir.as_os_str().to_os_string(),
                        OsString::from("-o"),
                        olean_dir.join("Captured.olean").into_os_string(),
                        captured_lean.as_os_str().to_os_string(),
                    ],
                );
                let compile_res = match run_supervised_cmd(
                    &compile_inv,
                    &cap_cache_dir,
                    LEAN_COMPILE_TIMEOUT_SECS,
                ) {
                    Ok(o) => o,
                    Err(detail) => return CaptureAttempt::ToolError { detail },
                };
                match compile_res.termination {
                    Termination::Exited(s) if s.success() => {}
                    other => {
                        return CaptureAttempt::ToolError {
                            detail: format!(
                                "compile Captured.lean failed ({}): stdout={} stderr={}",
                                other.describe(),
                                String::from_utf8_lossy(&compile_res.stdout),
                                String::from_utf8_lossy(&compile_res.stderr)
                            ),
                        };
                    }
                }
                if let Err(detail) = write_cached_artifact_manifest(
                    &cap_cache_dir,
                    &ready_ok,
                    &key,
                    EXPECTED_CAPTURE_CACHE_FILES,
                ) {
                    return CaptureAttempt::ToolError { detail };
                }
                return CaptureAttempt::Captured(CapturedArtifacts {
                    capture_dir: out_dir,
                    capture_json,
                    captured_lean,
                    olean_dir,
                    body_ids_by_fn,
                });
            }

            let detail_msg = format_capture_failure_detail(&parsed, &stdout);
            if parsed.status == "unsupported" && exit_code == Some(1) {
                if let Err(detail) = write_captured_refused_stamp(&ready_refused, &key, &detail_msg)
                {
                    return CaptureAttempt::ToolError { detail };
                }
                return CaptureAttempt::Refused { reason: detail_msg };
            }
            return CaptureAttempt::ToolError {
                detail: format!(
                    "anneal-rustc-capture failed with status={} (exit={exit_code:?}): {detail_msg}",
                    parsed.status
                ),
            };
        }

        CaptureAttempt::ToolError {
            detail: format!(
                "anneal-rustc-capture failed with non-JSON output (exit={exit_code:?}): stdout={stdout:?} stderr={stderr:?}"
            ),
        }
    }

    /// Evaluate a single [`TraceTestCase`] in the requested [`LeanTraceMode`].
    pub fn run_case(
        &self,
        case: &TraceTestCase,
        mode: LeanTraceMode,
    ) -> (AuthorityRunResult, Option<CapturedArtifacts>) {
        let auth_name = mode.authority_name();
        let start = Instant::now();
        let work_dir = match tempfile::Builder::new().prefix("anneal-itree-lean-").tempdir() {
            Ok(d) => d,
            Err(e) => {
                return (
                    AuthorityRunResult::tool_error(auth_name, format!("create tempdir: {e}")),
                    None,
                );
            }
        };

        match &case.lean_program_spec {
            LeanProgramSpec::CapturedRust { crate_name, select_fn } => {
                match self.capture_rust_source(
                    work_dir.path(),
                    crate_name,
                    &case.pure_rust_source,
                    std::slice::from_ref(select_fn),
                ) {
                    CaptureAttempt::Refused { reason } => (
                        AuthorityRunResult {
                            authority: auth_name.to_string(),
                            outcome: TerminalOutcome::CaptureRefused { reason },
                            spine: ObservableSpine::default(),
                            caller_frame_law: CallerFrameLaw::all_satisfied(),
                            tool_error: None,
                            raw_diagnostics: String::new(),
                            elapsed_ms: start.elapsed().as_millis() as u64,
                            post_only_mem_digest: false,
                            entry_mem_digest: None,
                        },
                        None,
                    ),
                    CaptureAttempt::ToolError { detail } => {
                        (AuthorityRunResult::tool_error(auth_name, detail), None)
                    }
                    CaptureAttempt::Captured(artifacts) => {
                        let Some(&def_id) = artifacts.body_ids_by_fn.get(select_fn) else {
                            return (
                                AuthorityRunResult::tool_error(
                                    auth_name,
                                    format!("captured manifest missing defId for `{select_fn}`"),
                                ),
                                None,
                            );
                        };
                        let probe_src =
                            match render_probe_for_captured(case, mode, def_id, &case.env_schedule)
                            {
                                Ok(s) => s,
                                Err(detail) => {
                                    return (
                                        AuthorityRunResult::tool_error(auth_name, detail),
                                        None,
                                    );
                                }
                            };
                        let res = self.eval_probe_file(
                            work_dir.path(),
                            Some(&artifacts.olean_dir),
                            &probe_src,
                            auth_name,
                            start,
                            Some(case.lean_args.len()),
                        );
                        (res, Some(artifacts))
                    }
                }
            }
            LeanProgramSpec::MultiCallWithCapturedCallees {
                crate_name,
                captured_callees,
                caller_lean_body,
                caller_identity,
                external_callees,
            } => {
                let captured = if captured_callees.is_empty() {
                    None
                } else {
                    match self.capture_rust_source(
                        work_dir.path(),
                        crate_name,
                        &case.pure_rust_source,
                        captured_callees,
                    ) {
                        CaptureAttempt::Captured(arts) => Some(arts),
                        CaptureAttempt::Refused { reason } => {
                            return (
                                AuthorityRunResult {
                                    authority: auth_name.to_string(),
                                    outcome: TerminalOutcome::CaptureRefused { reason },
                                    spine: ObservableSpine::default(),
                                    caller_frame_law: CallerFrameLaw::all_satisfied(),
                                    tool_error: None,
                                    raw_diagnostics: String::new(),
                                    elapsed_ms: start.elapsed().as_millis() as u64,
                                    post_only_mem_digest: false,
                                    entry_mem_digest: None,
                                },
                                None,
                            );
                        }
                        CaptureAttempt::ToolError { detail } => {
                            return (AuthorityRunResult::tool_error(auth_name, detail), None);
                        }
                    }
                };
                let probe_src = match render_probe_for_multicall(
                    case,
                    mode,
                    captured.as_ref(),
                    captured_callees,
                    caller_lean_body,
                    caller_identity,
                    external_callees,
                    &case.env_schedule,
                ) {
                    Ok(s) => s,
                    Err(detail) => {
                        return (AuthorityRunResult::tool_error(auth_name, detail), None);
                    }
                };
                let extra_dir = captured.as_ref().map(|c| c.olean_dir.as_path());
                let res = self.eval_probe_file(
                    work_dir.path(),
                    extra_dir,
                    &probe_src,
                    auth_name,
                    start,
                    Some(case.lean_args.len()),
                );
                (res, captured)
            }
            LeanProgramSpec::SyntheticMirAst { program_lean_expr, external_callees } => {
                let probe_src = match render_probe_for_synthetic(
                    case,
                    mode,
                    program_lean_expr,
                    external_callees,
                    &case.env_schedule,
                ) {
                    Ok(s) => s,
                    Err(detail) => {
                        return (AuthorityRunResult::tool_error(auth_name, detail), None);
                    }
                };
                let res = self.eval_probe_file(
                    work_dir.path(),
                    None,
                    &probe_src,
                    auth_name,
                    start,
                    Some(case.lean_args.len()),
                );
                (res, None)
            }
        }
    }

    /// Evaluate an arbitrary custom Lean probe importing `ITreeDriver` (used by
    /// negative self-tests verifying `ITreeDriver`'s caller-frame corruption
    /// detector).
    pub fn run_raw_driver_probe(&self, probe_src: &str, auth_name: &str) -> AuthorityRunResult {
        let start = Instant::now();
        let work_dir = match tempfile::Builder::new().prefix("anneal-itree-raw-").tempdir() {
            Ok(d) => d,
            Err(e) => {
                return AuthorityRunResult::tool_error(auth_name, format!("create tempdir: {e}"));
            }
        };
        self.eval_probe_file(work_dir.path(), None, probe_src, auth_name, start, None)
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_probe_file(
        &self,
        work_dir: &Path,
        extra_olean_dir: Option<&Path>,
        probe_src: &str,
        auth_name: &str,
        start: Instant,
        expected_entry_slots: Option<usize>,
    ) -> AuthorityRunResult {
        let probe_path = work_dir.join("Probe.lean");
        if let Err(e) = fs::write(&probe_path, probe_src) {
            return AuthorityRunResult::tool_error(
                auth_name,
                format!("write {}: {e}", probe_path.display()),
            );
        }
        let lean_path = match self.lean_path_with(extra_olean_dir) {
            Ok(lp) => lp,
            Err(detail) => return AuthorityRunResult::tool_error(auth_name, detail),
        };
        let eval_inv = build_lean_invocation(
            &self.lean_bin,
            &lean_path,
            &[probe_path.as_os_str().to_os_string()],
        );
        let eval_out = match run_supervised_cmd(&eval_inv, work_dir, LEAN_EVAL_TIMEOUT_SECS) {
            Ok(o) => o,
            Err(detail) => return AuthorityRunResult::tool_error(auth_name, detail),
        };
        let elapsed_ms = start.elapsed().as_millis() as u64;
        let stdout = String::from_utf8_lossy(&eval_out.stdout);
        let stderr = String::from_utf8_lossy(&eval_out.stderr);
        match eval_out.termination {
            Termination::Exited(s) if s.success() => parse_lean_trace_output_with_expected_args(
                auth_name,
                &stdout,
                &stderr,
                elapsed_ms,
                expected_entry_slots,
            ),
            other => AuthorityRunResult::tool_error(
                auth_name,
                format!(
                    "Lean trace driver failed ({}):\nstdout:\n{stdout}\nstderr:\n{stderr}",
                    other.describe()
                ),
            ),
        }
    }
}

fn format_capture_failure_detail(parsed: &CaptureStatusRaw, raw_stdout: &str) -> String {
    let mut parts = Vec::new();
    if let Some(r) = parsed.reason.as_deref().filter(|s| !s.is_empty()) {
        parts.push(r.to_string());
    }
    if let Some(m) = parsed.message.as_deref().filter(|s| !s.is_empty()) {
        parts.push(m.to_string());
    }
    if !parsed.diagnostics.is_empty() {
        parts.push(parsed.diagnostics.join("; "));
    }
    if !parsed.unsupported.is_empty()
        && let Ok(u) = serde_json::to_string(&parsed.unsupported)
    {
        parts.push(format!("unsupported={u}"));
    }
    if parts.is_empty() {
        format!("status={}: {}", parsed.status, raw_stdout.trim())
    } else {
        parts.join(" | ")
    }
}

fn select_captured_body_idx(bodies: &[CaptureBody], fn_name: &str) -> Result<usize, String> {
    let prefixed = format!("rust-path-v1::{fn_name}");
    if let Some((idx, _)) =
        bodies.iter().enumerate().find(|(_, b)| b.identity == fn_name || b.identity == prefixed)
    {
        return Ok(idx);
    }
    let suffix = format!("::{fn_name}");
    let matches: Vec<usize> = bodies
        .iter()
        .enumerate()
        .filter(|(_, b)| b.identity.ends_with(&suffix))
        .map(|(i, _)| i)
        .collect();
    match matches.as_slice() {
        [idx] => Ok(*idx),
        [] => Err(format!("captured manifest missing body `{fn_name}`")),
        many => Err(format!("ambiguous captured body match for `{fn_name}`: {many:?}")),
    }
}

/// Render a Lean `Except FaultKind Val` expression so enum and nested-tuple
/// arguments fail closed (`.error .unsupported`) if `defId`, `argIdx`,
/// `tuplePath`, or `variantIdx` is invalid.
fn lean_val_except_expr(
    val: &TraceVal,
    def_id_expr: &str,
    arg_idx: usize,
    tuple_path: &[usize],
) -> Result<String, String> {
    match val {
        TraceVal::Scalar { kind, bits } => {
            Ok(format!("(Except.ok (.scalar {}))", kind.to_lean_scalar(*bits)))
        }
        TraceVal::Bool { value } => Ok(if *value {
            "(Except.ok (.bool true))".to_string()
        } else {
            "(Except.ok (.bool false))".to_string()
        }),
        TraceVal::Char { scalar } => {
            char::from_u32(*scalar).ok_or_else(|| format!("invalid char scalar {scalar}"))?;
            Ok(format!("(Except.ok (.char (Char.ofNat {scalar})))"))
        }
        TraceVal::Ordering { value } => Ok(format!("(Except.ok ({}))", value.to_lean_val())),
        TraceVal::Unit => Ok("(Except.ok (.unit))".to_string()),
        TraceVal::Enum { variant_index, .. } => {
            let path_lits: Vec<String> = tuple_path.iter().map(ToString::to_string).collect();
            Ok(format!(
                "(ITreeDriver.argEnumValPath targetProg {def_id_expr} {arg_idx} [{}] {variant_index})",
                path_lits.join(", ")
            ))
        }
        TraceVal::Tuple { fields } => {
            let mut sub_exprs = Vec::with_capacity(fields.len());
            for (field_i, f) in fields.iter().enumerate() {
                let mut sub_path = tuple_path.to_vec();
                sub_path.push(field_i);
                sub_exprs.push(lean_val_except_expr(f, def_id_expr, arg_idx, &sub_path)?);
            }
            Ok(format!("(ITreeDriver.seqTupleVals [{}])", sub_exprs.join(", ")))
        }
        TraceVal::PaddedBytes { .. } => {
            Err("PaddedBytes cannot be passed directly to value-only Lean MIR entry".to_string())
        }
    }
}

fn render_lean_schedule(schedule: &EnvSchedule) -> Result<String, String> {
    let mut entries = Vec::new();
    for (callee, q) in &schedule.per_callee {
        for act in q {
            entries.push(render_lean_env_action(Some(callee), act));
        }
    }
    for act in &schedule.global {
        entries.push(render_lean_env_action(None, act));
    }
    Ok(format!("[{}]", entries.join(", ")))
}

fn render_lean_env_action(callee: Option<&str>, action: &EnvAction) -> String {
    let callee_opt_lit = match callee {
        Some(name) => format!("(some {})", lean_str_lit(name)),
        None => "none".to_string(),
    };
    match action {
        EnvAction::ReturnBytes(bytes) => {
            let byte_lits: Vec<String> = bytes.iter().map(ToString::to_string).collect();
            format!(
                "({callee_opt_lit}, ITreeDriver.DriverEnvAction.returnBytes [{}])",
                byte_lits.join(", ")
            )
        }
        EnvAction::Unwind { message } => {
            format!(
                "({callee_opt_lit}, ITreeDriver.DriverEnvAction.unwind {})",
                lean_str_lit(message)
            )
        }
        EnvAction::Abort { reason } => {
            format!(
                "({callee_opt_lit}, ITreeDriver.DriverEnvAction.abort {})",
                lean_str_lit(reason)
            )
        }
    }
}

/// Render a valid Lean 4 string literal, escaping all control characters
/// `U+0000..=U+001F` (`\n`, `\r`, `\t`, and `\xHH` for remaining ASCII control
/// bytes) so generated `.lean` probes never embed raw control characters.
pub fn lean_str_lit(s: &str) -> String {
    let mut out = String::from("\"");
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\x{:02x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn render_probe_for_captured(
    case: &TraceTestCase,
    mode: LeanTraceMode,
    def_id: usize,
    schedule: &EnvSchedule,
) -> Result<String, String> {
    let args_rendered = case
        .lean_args
        .iter()
        .enumerate()
        .map(|(idx, v)| lean_val_except_expr(v, &def_id.to_string(), idx, &[]))
        .collect::<Result<Vec<_>, _>>()?
        .join(", ");
    let sched_rendered = render_lean_schedule(schedule)?;
    Ok(format!(
        "import Captured\n\
         import ITreeDriver\n\
         open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
         def targetProg : Program := {{ Captured.program with entryDefId := {def_id} }}\n\
         #eval IO.println (ITreeDriver.runTraceChecked targetProg {mode} {fuel} [{args_rendered}] {sched_rendered} [])\n",
        mode = mode.lean_mode_ident(),
        fuel = case.fuel,
    ))
}

#[allow(clippy::too_many_arguments)]
fn render_probe_for_multicall(
    case: &TraceTestCase,
    mode: LeanTraceMode,
    captured: Option<&CapturedArtifacts>,
    captured_callees: &[String],
    caller_lean_body: &str,
    caller_identity: &str,
    external_callees: &[String],
    schedule: &EnvSchedule,
) -> Result<String, String> {
    let mut out = String::new();
    if captured.is_some() {
        out.push_str("import Captured\n");
    }
    out.push_str("import ITreeDriver\n");
    out.push_str("open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n");

    let mut body_exprs = vec![format!(
        "{{ (({caller_lean_body}) : Body) with identity := {} }}",
        lean_str_lit(caller_identity)
    )];
    if let Some(arts) = captured {
        for callee_name in captured_callees {
            let Some(&idx) = arts.body_ids_by_fn.get(callee_name) else {
                return Err(format!("captured callees missing `{callee_name}`"));
            };
            body_exprs.push(format!(
                "(ITreeDriver.getBodyOrEmpty Captured.program {idx} {})",
                lean_str_lit(callee_name)
            ));
        }
    }

    let _ = writeln!(
        out,
        "def targetProg : Program := {{\n  bodies := [{}],\n  entryDefId := 0,\n  pointerWidthBits := 64,\n  mirProfileVersion := 1,\n  scope := .unit\n}}",
        body_exprs.join(", ")
    );

    let args_rendered = case
        .lean_args
        .iter()
        .enumerate()
        .map(|(idx, v)| lean_val_except_expr(v, "0", idx, &[]))
        .collect::<Result<Vec<_>, _>>()?
        .join(", ");
    let sched_rendered = render_lean_schedule(schedule)?;
    let ext_rendered: Vec<String> = external_callees.iter().map(|s| lean_str_lit(s)).collect();

    let _ = writeln!(
        out,
        "#eval IO.println (ITreeDriver.runTraceChecked targetProg {} {} [{}] {} [{}])",
        mode.lean_mode_ident(),
        case.fuel,
        args_rendered,
        sched_rendered,
        ext_rendered.join(", ")
    );
    Ok(out)
}

fn render_probe_for_synthetic(
    case: &TraceTestCase,
    mode: LeanTraceMode,
    program_lean_expr: &str,
    external_callees: &[String],
    schedule: &EnvSchedule,
) -> Result<String, String> {
    let args_rendered = case
        .lean_args
        .iter()
        .enumerate()
        .map(|(idx, v)| lean_val_except_expr(v, "targetProg.entryDefId", idx, &[]))
        .collect::<Result<Vec<_>, _>>()?
        .join(", ");
    let sched_rendered = render_lean_schedule(schedule)?;
    let ext_rendered: Vec<String> = external_callees.iter().map(|s| lean_str_lit(s)).collect();

    Ok(format!(
        "import ITreeDriver\n\
         open Trusted.MirAst Trusted.MirSemantics ITreeDriver\n\n\
         def targetProg : Program := {program_lean_expr}\n\
         #eval IO.println (ITreeDriver.runTraceChecked targetProg {mode} {fuel} [{args_rendered}] {sched_rendered} [{ext}])\n",
        mode = mode.lean_mode_ident(),
        fuel = case.fuel,
        ext = ext_rendered.join(", "),
    ))
}

#[derive(Deserialize)]
struct RawLeanTrace {
    outcome_kind: String,
    #[serde(default)]
    ret: Option<RawLeanVal>,
    #[serde(default)]
    detail: String,
    #[serde(default)]
    fuel: u64,
    boundary_slots: Vec<Vec<Option<u8>>>,
    caller_locals_preserved: bool,
    untouched_alloc_bytes_preserved: bool,
    padding_mask_respected: bool,
    violations: Vec<String>,
    events: Vec<RawLeanEvent>,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawLeanVal {
    Scalar {
        width: String,
        signed: bool,
        bits: String,
    },
    Bool {
        value: bool,
    },
    Char {
        scalar: u32,
    },
    Ordering {
        value: String,
    },
    Unit,
    Enum {
        variant: usize,
        discr: String,
        #[serde(default)]
        tag_bytes: Option<usize>,
    },
    Tuple {
        fields: Vec<RawLeanVal>,
    },
    Other,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawLeanEvent {
    CallEnter {
        callee: String,
        arg_bytes: Vec<Vec<Option<u8>>>,
        arg_reprs: Vec<String>,
    },
    CallReturn {
        callee: String,
        ret_bytes: Vec<Option<u8>>,
        ret_repr: String,
    },
    CallUnwind {
        callee: String,
        reason: String,
    },
    BranchTag {
        block: u32,
        discr: String,
        target: u32,
    },
    CallerFrameCheck {
        point: String,
        locals_preserved: bool,
        allocs_preserved: bool,
        preserved: bool,
    },
}

fn convert_lean_val(v: RawLeanVal) -> Result<TraceVal, String> {
    match v {
        RawLeanVal::Scalar { width, signed, bits } => {
            let kind = IntKind::from_width_signed(&width, signed)
                .ok_or_else(|| format!("unknown Lean width/signed: {width}/{signed}"))?;
            let parsed = bits
                .parse::<u128>()
                .map_err(|e| format!("parse Lean scalar bits {bits:?}: {e}"))?;
            Ok(TraceVal::Scalar { kind, bits: kind.mask_bits(parsed) })
        }
        RawLeanVal::Bool { value } => Ok(TraceVal::Bool { value }),
        RawLeanVal::Char { scalar } => Ok(TraceVal::Char { scalar }),
        RawLeanVal::Ordering { value } => {
            let ord = match value.as_str() {
                "less" => OrderingVal::Less,
                "equal" => OrderingVal::Equal,
                "greater" => OrderingVal::Greater,
                other => return Err(format!("unknown Lean ordering {other:?}")),
            };
            Ok(TraceVal::Ordering { value: ord })
        }
        RawLeanVal::Unit => Ok(TraceVal::Unit),
        RawLeanVal::Enum { variant, discr, tag_bytes } => {
            let parsed_discr = discr
                .parse::<u128>()
                .map_err(|e| format!("parse Lean enum discriminant {discr:?}: {e}"))?;
            Ok(TraceVal::Enum {
                type_name: String::new(),
                variant_name: String::new(),
                variant_index: variant,
                discriminant: parsed_discr,
                tag_bytes,
            })
        }
        RawLeanVal::Tuple { fields } => {
            let conv = fields.into_iter().map(convert_lean_val).collect::<Result<Vec<_>, _>>()?;
            Ok(TraceVal::Tuple { fields: conv })
        }
        RawLeanVal::Other => Err("unsupported Lean Val serialization".to_string()),
    }
}

/// Parse the single `ANNEAL_LEAN_ITREE_JSON:` line emitted by
/// `ITreeDriver.runTraceChecked`, rejecting both `0` and `>= 2` lines.
pub fn parse_lean_trace_output(
    auth_name: &str,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
) -> AuthorityRunResult {
    parse_lean_trace_output_with_expected_args(auth_name, stdout, stderr, elapsed_ms, None)
}

/// Entry-count-checked variant of [`parse_lean_trace_output`].
pub fn parse_lean_trace_output_with_expected_args(
    auth_name: &str,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
) -> AuthorityRunResult {
    let matches: Vec<&str> =
        stdout.lines().filter_map(|line| line.trim().strip_prefix(LEAN_TRACE_PREFIX)).collect();
    let json_str = match matches.as_slice() {
        [single] => *single,
        [] => {
            return AuthorityRunResult::tool_error(
                auth_name,
                format!(
                    "Lean output missing `{LEAN_TRACE_PREFIX}`; stdout={stdout:?}, stderr={stderr:?}"
                ),
            );
        }
        many => {
            return AuthorityRunResult::tool_error(
                auth_name,
                format!(
                    "Lean output emitted {} `{LEAN_TRACE_PREFIX}` lines (expected 1); stdout={stdout:?}",
                    many.len()
                ),
            );
        }
    };

    let parsed: RawLeanTrace = match serde_json::from_str(json_str) {
        Ok(p) => p,
        Err(e) => {
            return AuthorityRunResult::tool_error(
                auth_name,
                format!("parse Lean trace JSON: {e}; raw={json_str:?}"),
            );
        }
    };

    if parsed.outcome_kind == "unconsumed_schedule" {
        return AuthorityRunResult::tool_error(
            auth_name,
            format!("Lean unconsumed scheduled environment actions: {}", parsed.detail),
        );
    }

    let parsed_ret = if parsed.outcome_kind == "returned" {
        match parsed.ret.ok_or_else(|| "missing ret".to_string()).and_then(convert_lean_val) {
            Ok(ret) => Some(ret),
            Err(detail) => return AuthorityRunResult::tool_error(auth_name, detail),
        }
    } else {
        None
    };

    let effective_expected_entry_slots =
        if matches!(parsed.outcome_kind.as_str(), "fault_undefined" | "init_unsupported")
            && parsed.detail.starts_with("entry argument ")
        {
            Some(0)
        } else {
            expected_entry_slots
        };

    if let Err(detail) = validate_boundary_slots_for_outcome(
        auth_name,
        &parsed.outcome_kind,
        parsed_ret.as_ref(),
        effective_expected_entry_slots,
        &parsed.boundary_slots,
    ) {
        return AuthorityRunResult::tool_error(auth_name, detail);
    }

    let mem_digest = compute_boundary_mem_digest(&parsed.boundary_slots);
    let entry_mem_digest = match parsed.outcome_kind.as_str() {
        "returned" | "unwound" | "aborted" => {
            let entry_len = parsed.boundary_slots.len().saturating_sub(1);
            if expected_entry_slots.is_some() || entry_len > 0 {
                Some(compute_boundary_mem_digest(&parsed.boundary_slots[..entry_len]))
            } else {
                None
            }
        }
        "fault_undefined" => {
            if parsed.detail.starts_with("entry argument ") {
                None
            } else if expected_entry_slots.is_some() || !parsed.boundary_slots.is_empty() {
                Some(mem_digest.clone())
            } else {
                None
            }
        }
        _ => None,
    };
    let outcome = match parsed.outcome_kind.as_str() {
        "returned" => TerminalOutcome::Returned {
            ret: parsed_ret.expect("checked returned payload"),
            mem_digest,
        },
        "unwound" => TerminalOutcome::Unwound { mem_digest },
        "aborted" => TerminalOutcome::Aborted { mem_digest },
        "diverged" => TerminalOutcome::Diverged { fuel: parsed.fuel },
        "fault_undefined" => TerminalOutcome::FaultUb { detail: parsed.detail },
        "fault_unsupported" | "init_unsupported" => {
            TerminalOutcome::CaptureRefused { reason: parsed.detail }
        }
        other => {
            return AuthorityRunResult::tool_error(
                auth_name,
                format!("unknown Lean outcome_kind {other:?} (detail={:?})", parsed.detail),
            );
        }
    };

    let events = parsed
        .events
        .into_iter()
        .map(|ev| match ev {
            RawLeanEvent::CallEnter { callee, arg_bytes, arg_reprs } => {
                ObservableEvent::CallEnter { callee, arg_bytes, arg_reprs }
            }
            RawLeanEvent::CallReturn { callee, ret_bytes, ret_repr } => {
                ObservableEvent::CallReturn { callee, ret_bytes, ret_repr }
            }
            RawLeanEvent::CallUnwind { callee, reason } => {
                ObservableEvent::CallUnwind { callee, reason }
            }
            RawLeanEvent::BranchTag { block, discr, target } => {
                ObservableEvent::BranchTag { block, discr, target }
            }
            RawLeanEvent::CallerFrameCheck {
                point,
                locals_preserved,
                allocs_preserved,
                preserved,
            } => ObservableEvent::CallerFrameCheck {
                point,
                locals_preserved,
                allocs_preserved,
                preserved,
            },
        })
        .collect();

    AuthorityRunResult {
        authority: auth_name.to_string(),
        outcome,
        spine: ObservableSpine { events },
        caller_frame_law: CallerFrameLaw {
            caller_locals_preserved: parsed.caller_locals_preserved,
            untouched_alloc_bytes_preserved: parsed.untouched_alloc_bytes_preserved,
            padding_mask_respected: parsed.padding_mask_respected,
            violations: parsed.violations,
        },
        tool_error: None,
        raw_diagnostics: stderr.to_string(),
        elapsed_ms,
        post_only_mem_digest: false,
        entry_mem_digest,
    }
}

/// Test-only Lean 4 trace driver module (`ITreeDriver.lean`), compiled into the
/// content-addressed `.olean` cache directory outside `trusted/lean/`.
const ITREE_DRIVER_LEAN_SRC: &str = r#"-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.MirTotal.ExecTotal

namespace ITreeDriver

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

def tyEqDepth : MirTy → MirTy → Bool := mirTyBeqAt 64

inductive TraceMode where
  | strictVerbatim
  | compositionalITree

inductive DriverEnvAction where
  | returnBytes (bytes : List Nat)
  | unwind (msg : String)
  | abort (reason : String)

abbrev ScheduleEntry := Option String × DriverEnvAction

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def escJson (s : String) : String :=
  "\"" ++ (s.toList.foldl (fun acc c =>
    let code := c.toNat
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if Nat.beq code 8 then acc ++ "\\b"
    else if Nat.beq code 12 then acc ++ "\\f"
    else if c == '\n' then acc ++ "\\n"
    else if c == '\r' then acc ++ "\\r"
    else if c == '\t' then acc ++ "\\t"
    else if code < 32 then
      ((acc ++ "\\u00").push (hexDigit (code / 16))).push (hexDigit (code % 16))
    else acc.push c) "") ++ "\""

def widthName : IntWidth → String
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .i128 => "i128"
  | .isize => "isize"

def intByteSizeComp : IntWidth → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 | .isize => 8
  | .i128 => 16

def encodeLeBytes : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v => (v % 256) :: encodeLeBytes k (v / 256)

def decodeLeBytes : List Nat → Nat
  | [] => 0
  | b :: rest => (b % 256) + 256 * decodeLeBytes rest

def decodeScheduledBytes (ty : MirTy) (bytes : List Nat) : Except FaultKind Val :=
  if bytes.any (fun b => b >= 256) then
    .error .undefined
  else
    match ty with
    | .unit =>
      if bytes.isEmpty then .ok .unit else .error .undefined
    | .bool =>
      match bytes with
      | [0] => .ok (.bool false)
      | [1] => .ok (.bool true)
      | _ => .error .undefined
    | .char =>
      if Nat.beq bytes.length 4 then
        let raw := decodeLeBytes bytes
        if raw < 55296 || (57344 <= raw && raw <= 1114111) then
          .ok (.char (Char.ofNat raw))
        else
          .error .undefined
      else
        .error .undefined
    | .ordering =>
      match bytes with
      | [255] => .ok (.ordering .less)
      | [0] => .ok (.ordering .equal)
      | [1] => .ok (.ordering .greater)
      | _ => .error .undefined
    | .int w signed =>
      if Nat.beq bytes.length (intByteSizeComp w) then
        let raw := decodeLeBytes bytes
        .ok (.scalar ⟨w, signed, BitVec.ofNat 128 raw⟩)
      else
        .error .undefined
    | .enum ety =>
      match ety.tagRepr with
      | .zeroSized =>
        if !isZstEnumTyComp ety then
          .error .unsupported
        else if bytes.isEmpty then
          .ok (.enumVal ety 0)
        else
          .error .undefined
      | .scalar tagW tagS =>
        if !enumAdmittedComp ety then
          .error .unsupported
        else if Nat.beq bytes.length (intByteSizeComp tagW) then
          let rawBits := BitVec.ofNat 128 (decodeLeBytes bytes)
          let discrBits := tagBitsToDiscrBitsComp tagW tagS ety.discrWidth rawBits
          match findDiscrVariant?Comp discrBits ety.discriminants with
          | some vIdx => .ok (.enumVal ety vIdx)
          | none => .error .undefined
        else
          .error .undefined
    | _ => .error .unsupported

partial def encodeBoundaryValBytes : Val → List (Option Nat)
  | .scalar sv =>
    (encodeLeBytes (intByteSizeComp sv.width) sv.bits.toNat).map some
  | .bool b => [some (if b then 1 else 0)]
  | .char c => (encodeLeBytes 4 c.toNat).map some
  | .ordering .less => [some 255]
  | .ordering .equal => [some 0]
  | .ordering .greater => [some 1]
  | .unit => []
  | .enumVal ety v =>
    match ety.tagRepr with
    | .zeroSized => []
    | .scalar tagW _ =>
      match compGetElem? ety.discriminants v with
      | some d => (encodeLeBytes (intByteSizeComp tagW) d).map some
      | none => []
  | .tuple fs => (fs.map encodeBoundaryValBytes).foldl List.append []
  | .array elems => (elems.map encodeBoundaryValBytes).foldl List.append []
  | .ptr p => (encodeLeBytes 8 p.offsetBytes.toNat).map some
  | .slicePtr p len =>
    ((encodeLeBytes 8 p.offsetBytes.toNat) ++ (encodeLeBytes 8 len.toNat)).map some
  | .rangeTo endVal => (encodeLeBytes 8 endVal.toNat).map some
  | .rangeFrom startVal => (encodeLeBytes 8 startVal.toNat).map some
  | .range startVal endVal =>
    ((encodeLeBytes 8 startVal.toNat) ++ (encodeLeBytes 8 endVal.toNat)).map some
  | .optionVal none => [some 0]
  | .optionVal (some inner) => some 1 :: encodeBoundaryValBytes inner
  | .bytes bs =>
    bs.map (fun ab => match ab with | .init b _ => some b.toNat | .uninit => none)

def renderOptNatSlot (slot : List (Option Nat)) : String :=
  "[" ++ String.intercalate "," (slot.map (fun o =>
    match o with
    | some b => toString b
    | none => "null")) ++ "]"

def scalarRepr (sv : ScalarVal) : String :=
  let raw := sv.bits.toNat
  if sv.signed then
    match sv.width with
    | .i8 =>
      if raw >= 128 then "-" ++ toString (256 - raw) else toString raw
    | .i16 =>
      if raw >= 32768 then "-" ++ toString (65536 - raw) else toString raw
    | .i32 =>
      if raw >= 2147483648 then "-" ++ toString (4294967296 - raw) else toString raw
    | .i64 | .isize =>
      if raw >= 9223372036854775808 then
        "-" ++ toString (18446744073709551616 - raw)
      else toString raw
    | .i128 =>
      if raw >= 170141183460469231731687303715884105728 then
        "-" ++ toString (340282366920938463463374607431768211456 - raw)
      else toString raw
  else
    toString raw

partial def valRepr : Val → String
  | .scalar sv => scalarRepr sv
  | .bool b => if b then "true" else "false"
  | .char c => "char(" ++ toString c.toNat ++ ")"
  | .ordering .less => "Less"
  | .ordering .equal => "Equal"
  | .ordering .greater => "Greater"
  | .unit => "()"
  | .enumVal ety v =>
    match compGetElem? ety.discriminants v with
    | some d => "enum(" ++ scalarRepr ⟨ety.discrWidth, ety.discrSigned, BitVec.ofNat 128 d⟩ ++ ")"
    | none => "enum#" ++ toString v
  | .tuple fs => "(" ++ String.intercalate "," (fs.map valRepr) ++ ")"
  | .array elems => "[" ++ String.intercalate "," (elems.map valRepr) ++ "]"
  | .range startVal endVal =>
    "range(" ++ toString startVal.toNat ++ ".." ++ toString endVal.toNat ++ ")"
  | .optionVal none => "None"
  | .optionVal (some inner) => "Some(" ++ valRepr inner ++ ")"
  | _ => "<other>"

partial def valToJson : Val → String
  | .scalar sv =>
    "{\"kind\":\"scalar\",\"width\":" ++ escJson (widthName sv.width)
      ++ ",\"signed\":" ++ (if sv.signed then "true" else "false")
      ++ ",\"bits\":" ++ escJson (toString sv.bits.toNat) ++ "}"
  | .bool b =>
    "{\"kind\":\"bool\",\"value\":" ++ (if b then "true" else "false") ++ "}"
  | .char c =>
    "{\"kind\":\"char\",\"scalar\":" ++ toString c.toNat ++ "}"
  | .ordering .less => "{\"kind\":\"ordering\",\"value\":\"less\"}"
  | .ordering .equal => "{\"kind\":\"ordering\",\"value\":\"equal\"}"
  | .ordering .greater => "{\"kind\":\"ordering\",\"value\":\"greater\"}"
  | .unit => "{\"kind\":\"unit\"}"
  | .enumVal ety v =>
    let d := (compGetElem? ety.discriminants v).getD v
    let tb := match ety.tagRepr with
      | .zeroSized => 0
      | .scalar tagW _ => intByteSizeComp tagW
    "{\"kind\":\"enum\",\"variant\":" ++ toString v
      ++ ",\"discr\":" ++ escJson (toString d)
      ++ ",\"tag_bytes\":" ++ toString tb ++ "}"
  | .tuple fs =>
    "{\"kind\":\"tuple\",\"fields\":[" ++ String.intercalate "," (fs.map valToJson) ++ "]}"
  | .array _ | .range _ _ | .optionVal _ => "{\"kind\":\"other\"}"
  | _ => "{\"kind\":\"other\"}"

def resolveTuplePath : MirTy → List Nat → Option MirTy
  | ty, [] => some ty
  | .tuple fs, idx :: rest =>
    match compGetElem? fs idx with
    | some sub => resolveTuplePath sub rest
    | none => none
  | _, _ :: _ => none

def argEnumValPath (prog : Program) (defId argIdx : Nat) (path : List Nat)
    (variantIdx : Nat) : Except FaultKind Val :=
  match compGetElem? prog.bodies defId with
  | none => .error .unsupported
  | some b =>
    match compGetElem? b.locals (argIdx + 1) with
    | none => .error .unsupported
    | some rootTy =>
      match resolveTuplePath rootTy path with
      | some (.enum ety) =>
        if Nat.blt variantIdx ety.discriminants.length then
          .ok (.enumVal ety variantIdx)
        else
          .error .undefined
      | _ => .error .unsupported

def seqExceptVals : List (Except FaultKind Val) → Except FaultKind (List Val)
  | [] => .ok []
  | .error k :: _ => .error k
  | .ok v :: rest =>
    match seqExceptVals rest with
    | .ok vs => .ok (v :: vs)
    | .error k => .error k

def seqTupleVals (xs : List (Except FaultKind Val)) : Except FaultKind Val :=
  match seqExceptVals xs with
  | .ok vs => .ok (.tuple vs)
  | .error k => .error k

def getBodyOrEmpty (prog : Program) (idx : Nat) (id : String) : Body :=
  match compGetElem? prog.bodies idx with
  | some b => { b with identity := id }
  | none => { argumentCount := 0, locals := [], basicBlocks := [], identity := id }

def optNatEq : Option Nat → Option Nat → Bool
  | none, none => true
  | some a, some b => Nat.beq a b
  | _, _ => false

def allocByteEq : AllocByte → AllocByte → Bool
  | .uninit, .uninit => true
  | .init b1 p1, .init b2 p2 => (b1 == b2) && optNatEq p1 p2
  | _, _ => false

def allocByteMaskEq : AllocByte → AllocByte → Bool
  | .uninit, .uninit => true
  | .init _ _, .init _ _ => true
  | _, _ => false

def listAllEq {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => eq x y && listAllEq eq xs ys
  | _, _ => false

def intWidthEq : IntWidth → IntWidth → Bool
  | .i8, .i8 | .i16, .i16 | .i32, .i32 | .i64, .i64 | .i128, .i128 | .isize, .isize => true
  | _, _ => false

def ordEq : OrderingVal → OrderingVal → Bool
  | .less, .less | .equal, .equal | .greater, .greater => true
  | _, _ => false

partial def valEq : Val → Val → Bool
  | .scalar a, .scalar b =>
    intWidthEq a.width b.width && (a.signed == b.signed) && (a.bits == b.bits)
  | .ptr a, .ptr b =>
    optNatEq a.allocId b.allocId && (a.offsetBytes == b.offsetBytes) && intWidthEq a.width b.width
  | .slicePtr a la, .slicePtr b lb =>
    optNatEq a.allocId b.allocId && (a.offsetBytes == b.offsetBytes)
      && intWidthEq a.width b.width && (la == lb)
  | .rangeTo a, .rangeTo b => a == b
  | .rangeFrom a, .rangeFrom b => a == b
  | .range s1 e1, .range s2 e2 => (s1 == s2) && (e1 == e2)
  | .optionVal none, .optionVal none => true
  | .optionVal (some a), .optionVal (some b) => valEq a b
  | .bool a, .bool b => a == b
  | .char a, .char b => Nat.beq a.toNat b.toNat
  | .ordering a, .ordering b => ordEq a b
  | .unit, .unit => true
  | .enumVal e1 v1, .enumVal e2 v2 => enumTyBeqComp e1 e2 && Nat.beq v1 v2
  | .tuple f1, .tuple f2 => listAllEq valEq f1 f2
  | .array a1, .array a2 => listAllEq valEq a1 a2
  | .bytes b1, .bytes b2 => listAllEq allocByteEq b1 b2
  | _, _ => false

def optValEq : Option Val → Option Val → Bool
  | none, none => true
  | some a, some b => valEq a b
  | _, _ => false

def memPlaceEq (a b : MemPlace) : Bool :=
  Nat.beq a.allocId b.allocId && Nat.beq a.offset b.offset

def localSlotEq : LocalSlot → LocalSlot → Bool
  | .dead, .dead => true
  | .immediate a, .immediate b => optValEq a b
  | .indirect a, .indirect b => memPlaceEq a b
  | .partialTuple a, .partialTuple b => listAllEq optValEq a b
  | _, _ => false

def optValMaskEq : Option Val → Option Val → Bool
  | none, none => true
  | some _, some _ => true
  | _, _ => false

def isDeadSlot : LocalSlot → Bool
  | .dead => true
  | _ => false

def isDeadSlotOpt : Option LocalSlot → Bool
  | some .dead => true
  | _ => false

def isUninitImmediateOpt : Option LocalSlot → Bool
  | some (.immediate none) => true
  | _ => false

def natListContains (xs : List Nat) (target : Nat) : Bool :=
  xs.any (fun x => Nat.beq x target)

def localMaskEq : LocalSlot → LocalSlot → Bool
  | .dead, .dead => true
  | .immediate (some _), .immediate (some _) => true
  | .immediate none, .immediate none => true
  | .indirect _, .indirect _ => true
  | .partialTuple a, .partialTuple b => listAllEq optValMaskEq a b
  | _, _ => false

def localsPreservedExcept (skipIdx : Option Nat) : Nat → List LocalSlot → List LocalSlot → Bool
  | _, [], [] => true
  | idx, a :: as, b :: bs =>
    let ok :=
      match skipIdx with
      | some s => if Nat.beq idx s then true else localSlotEq a b
      | none => localSlotEq a b
    ok && localsPreservedExcept skipIdx (idx + 1) as bs
  | _, _, _ => false

/-- During unwind cleanup, only explicitly tracked cleanup-retired temporaries
(`dstLocal`, temporaries freshly spawned inside the cleanup block via
`.storageLive`, or pre-call uninitialized temporaries — never return slot `0`,
never caller arguments `1 ..= argCount`, and never caller locals holding a live
initialized value before the call) may transition to `.dead`; every other slot
must strictly satisfy `localSlotEq` and `localMaskEq`. -/
def localsPreservedAfterCleanup (retired : List Nat) :
    Nat → List LocalSlot → List LocalSlot → Bool
  | _, [], [] => true
  | idx, a :: as, b :: bs =>
    let ok :=
      if natListContains retired idx && isDeadSlot b then true
      else localSlotEq a b
    ok && localsPreservedAfterCleanup retired (idx + 1) as bs
  | _, _, _ => false

def localMaskPreservedAfterCleanup (retired : List Nat) :
    Nat → List LocalSlot → List LocalSlot → Bool
  | _, [], [] => true
  | idx, a :: as, b :: bs =>
    let ok :=
      if natListContains retired idx && isDeadSlot b then true
      else localMaskEq a b
    ok && localMaskPreservedAfterCleanup retired (idx + 1) as bs
  | _, _, _ => false

def localMaskPreservedExcept (skipIdx : Option Nat) : Nat → List LocalSlot → List LocalSlot → Bool
  | _, [], [] => true
  | idx, a :: as, b :: bs =>
    let ok :=
      match skipIdx with
      | some s =>
        if Nat.beq idx s then true
        else localMaskEq a b
      | none => localMaskEq a b
    ok && localMaskPreservedExcept skipIdx (idx + 1) as bs
  | _, _, _ => false

def allocEq (a b : Allocation) : Bool :=
  Nat.beq a.allocId b.allocId &&
    Nat.beq a.alignLog2 b.alignLog2 &&
    mutabilityBeqComp a.mutability b.mutability &&
    (a.live == b.live) &&
    listAllEq allocByteEq a.bytes b.bytes

def allocMaskEq (a b : Allocation) : Bool :=
  Nat.beq a.allocId b.allocId && listAllEq allocByteMaskEq a.bytes b.bytes

def findAllocById (id : AllocId) : List Allocation → Option Allocation
  | [] => none
  | a :: rest => if Nat.beq a.allocId id then some a else findAllocById id rest

def preExistingAllocsPreserved (before after : List Allocation) : Bool :=
  before.all (fun a =>
    match findAllocById a.allocId after with
    | some a' => allocEq a a'
    | none => false)

def preExistingAllocMasksPreserved (before after : List Allocation) : Bool :=
  before.all (fun a =>
    match findAllocById a.allocId after with
    | some a' => allocMaskEq a a'
    | none => false)

def mkBranchEvent (block : Nat) (discr : String) (target : Nat) : String :=
  "{\"kind\":\"branch_tag\",\"block\":" ++ toString block
    ++ ",\"discr\":" ++ escJson discr
    ++ ",\"target\":" ++ toString target ++ "}"

def mkCallEnterEvent (callee : String) (args : List Val) : String :=
  let ab := args.map (fun v => renderOptNatSlot (encodeBoundaryValBytes v))
  let reprs := args.map (fun v => escJson (valRepr v))
  "{\"kind\":\"call_enter\",\"callee\":" ++ escJson callee
    ++ ",\"arg_bytes\":[" ++ String.intercalate "," ab ++ "]"
    ++ ",\"arg_reprs\":[" ++ String.intercalate "," reprs ++ "]}"

def mkCallReturnEvent (callee : String) (ret : Val) : String :=
  "{\"kind\":\"call_return\",\"callee\":" ++ escJson callee
    ++ ",\"ret_bytes\":" ++ renderOptNatSlot (encodeBoundaryValBytes ret)
    ++ ",\"ret_repr\":" ++ escJson (valRepr ret) ++ "}"

def mkCallUnwindEvent (callee reason : String) : String :=
  "{\"kind\":\"call_unwind\",\"callee\":" ++ escJson callee
    ++ ",\"reason\":" ++ escJson reason ++ "}"

def mkFrameCheckEvent (point : String) (localsOk allocsOk : Bool) : String :=
  let preserved := localsOk && allocsOk
  "{\"kind\":\"caller_frame_check\",\"point\":" ++ escJson point
    ++ ",\"locals_preserved\":" ++ (if localsOk then "true" else "false")
    ++ ",\"allocs_preserved\":" ++ (if allocsOk then "true" else "false")
    ++ ",\"preserved\":" ++ (if preserved then "true" else "false") ++ "}"

def finishRawJson (outcomeKind : String) (retJson : String) (detail : String) (fuel : Nat)
    (boundarySlots : List (List (Option Nat)))
    (localsOk allocsOk padOk : Bool) (violations : List String) (eventsRev : List String) : String :=
  let evs := String.intercalate "," eventsRev.reverse
  let viols := String.intercalate "," (violations.reverse.map escJson)
  let bSlots := String.intercalate "," (boundarySlots.map renderOptNatSlot)
  "ANNEAL_LEAN_ITREE_JSON:{"
    ++ "\"outcome_kind\":" ++ escJson outcomeKind
    ++ ",\"ret\":" ++ retJson
    ++ ",\"detail\":" ++ escJson detail
    ++ ",\"fuel\":" ++ toString fuel
    ++ ",\"boundary_slots\":[" ++ bSlots ++ "]"
    ++ ",\"caller_locals_preserved\":" ++ (if localsOk then "true" else "false")
    ++ ",\"untouched_alloc_bytes_preserved\":" ++ (if allocsOk then "true" else "false")
    ++ ",\"padding_mask_respected\":" ++ (if padOk then "true" else "false")
    ++ ",\"violations\":[" ++ viols ++ "]"
    ++ ",\"events\":[" ++ evs ++ "]}"

def finishJson (outcomeKind : String) (retJson : String) (detail : String) (fuel : Nat)
    (boundarySlots : List (List (Option Nat))) (sched : List ScheduleEntry)
    (localsOk allocsOk padOk : Bool) (violations : List String) (eventsRev : List String) : String :=
  if !sched.isEmpty then
    finishRawJson "unconsumed_schedule" "null"
      ("unconsumed scheduled EnvActions remaining: " ++ toString sched.length)
      fuel boundarySlots localsOk allocsOk padOk violations eventsRev
  else
    finishRawJson outcomeKind retJson detail fuel boundarySlots localsOk allocsOk padOk violations eventsRev

def finishReturnedJson (retVal : Val) (fuel : Nat) (bSlots : List (List (Option Nat)))
    (sched : List ScheduleEntry)
    (localsOk allocsOk padOk : Bool) (viols eventsRev : List String) : String :=
  let postSlot := some 16 :: encodeBoundaryValBytes retVal
  finishJson "returned" (valToJson retVal) "" fuel (bSlots ++ [postSlot]) sched
    localsOk allocsOk padOk viols eventsRev

def finishUnwoundJson (detail : String) (fuel : Nat) (bSlots : List (List (Option Nat)))
    (sched : List ScheduleEntry)
    (localsOk allocsOk padOk : Bool) (viols eventsRev : List String) : String :=
  finishJson "unwound" "null" detail fuel (bSlots ++ [[some 32]]) sched
    localsOk allocsOk padOk viols eventsRev

def finishAbortedJson (detail : String) (fuel : Nat) (bSlots : List (List (Option Nat)))
    (sched : List ScheduleEntry)
    (localsOk allocsOk padOk : Bool) (viols eventsRev : List String) : String :=
  finishJson "aborted" "null" detail fuel (bSlots ++ [[some 48]]) sched
    localsOk allocsOk padOk viols eventsRev

def optCalleeEq : Option String → Option String → Bool
  | none, none => true
  | some a, some b => a == b
  | _, _ => false

def popTargetSchedule (target : Option String) :
    List ScheduleEntry → Option (DriverEnvAction × List ScheduleEntry)
  | [] => none
  | (k, act) :: rest =>
    if optCalleeEq k target then
      some (act, rest)
    else
      match popTargetSchedule target rest with
      | some (found, rest') => some (found, (k, act) :: rest')
      | none => none

def popSchedule (callee : String) (sched : List ScheduleEntry) :
    Option (DriverEnvAction × List ScheduleEntry) :=
  match popTargetSchedule (some callee) sched with
  | some hit => some hit
  | none => popTargetSchedule none sched

def evalCallArgs (bodyLocals : List MirTy) :
    List Operand → List LocalSlot → MemoryState →
      Except FaultKind (List Val × List LocalSlot × MemoryState)
  | [], locals, mem => .ok ([], locals, mem)
  | opnd :: rest, locals, mem =>
    match evalOperandToSlotComp bodyLocals locals mem isSupportedScalarOrUnitTyComp opnd with
    | .error k => .error k
    | .ok (_, none, _, _) => .error .undefined
    | .ok (_, some v, locals1, mem1) =>
      match evalCallArgs bodyLocals rest locals1 mem1 with
      | .error k => .error k
      | .ok (vs, locals2, mem2) => .ok (v :: vs, locals2, mem2)

def placeHasDeref (p : Place) : Bool :=
  p.projection.any (fun elem =>
    match elem with
    | .deref => true
    | _ => false)

def operandHasDeref : Operand → Bool
  | .copy p | .move p => placeHasDeref p
  | .constant _ => false

def rvalueHasDeref : Rvalue → Bool
  | .use op | .unaryOp _ op | .cast _ op _ | .useRetag op
  | .aggregateRangeTo _ op | .aggregateRangeFrom _ op
  | .repeat_ op _ _ => operandHasDeref op
  | .aggregateRange _ startOp endOp => operandHasDeref startOp || operandHasDeref endOp
  | .aggregateOption _ _ (some op) => operandHasDeref op
  | .aggregateOption _ _ none => false
  | .binaryOp _ l r => operandHasDeref l || operandHasDeref r
  | .discriminant p | .ref _ p | .addressOf _ p | .fakeAddressOf p => placeHasDeref p
  | .aggregateTuple ops | .aggregateArray _ ops => ops.any operandHasDeref
  | .aggregateEnum _ _ | .unsupported => false

def operandReadyInFrame (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (opnd : Operand) : Bool :=
  match evalOperandToSlotComp bodyLocals locals mem isSupportedScalarOrUnitTyComp opnd with
  | .ok (_, some _, _, _) => true
  | _ => false

/-- Attribute an `evalMirStepBy` `.fault .undefined` step to a specific UB
category (`entering unreachable code`, `unchecked shift overflow`, `unchecked
arithmetic overflow`, `division or remainder by zero`, `pointer or memory access
undefined`, or `uninitialized or invalid value undefined`) so differential UB
comparisons bind to the actual fault cause rather than a generic enum tag. -/
def describeUndefinedStepFault (prog : Program) (frame : FrameState) (mem : MemoryState) : String :=
  match activeFrameBodyComp prog frame with
  | none => "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
  | some body =>
    match compGetElem? body.basicBlocks frame.blockIdx with
    | none => "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
    | some bb =>
      if Nat.blt frame.stmtIdx bb.statements.length then
        match compGetElem? bb.statements frame.stmtIdx with
        | some (.assign dst rv) =>
          if placeHasDeref dst || rvalueHasDeref rv then
            "pointer or memory access undefined: Trusted.MirSemantics.FaultKind.undefined"
          else if isDeadSlotOpt (compGetElem? frame.locals dst.localId) then
            "dead local write undefined: Trusted.MirSemantics.FaultKind.undefined"
          else
            match rv with
            | .binaryOp op lhs rhs =>
              if operandReadyInFrame body.locals frame.locals mem lhs
                  && operandReadyInFrame body.locals frame.locals mem rhs then
                match op with
                | .shlUnchecked | .shrUnchecked =>
                  "unchecked shift overflow: Trusted.MirSemantics.FaultKind.undefined"
                | .addUnchecked | .subUnchecked | .mulUnchecked =>
                  "unchecked arithmetic overflow: Trusted.MirSemantics.FaultKind.undefined"
                | .div | .rem =>
                  "division or remainder by zero: Trusted.MirSemantics.FaultKind.undefined"
                | .offset =>
                  "pointer or memory access undefined: Trusted.MirSemantics.FaultKind.undefined"
                | _ =>
                  "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
              else
                "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
            | _ =>
              "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
        | _ =>
          "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
      else
        match bb.terminator with
        | .unreachable =>
          "entering unreachable code: Trusted.MirSemantics.FaultKind.undefined"
        | .assert condOp _ .misalignedPtrDeref _ _
        | .assert condOp _ .nullPtrDeref _ _ =>
          if operandReadyInFrame body.locals frame.locals mem condOp then
            "pointer dereference undefined: Trusted.MirSemantics.FaultKind.undefined"
          else
            "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
        | .coreCall coreOp argOps dstPlace targetOpt _ =>
          if targetOpt.isSome
              && isDeadSlotOpt (compGetElem? frame.locals dstPlace.localId) then
            "dead local write undefined: Trusted.MirSemantics.FaultKind.undefined"
          else
            match evalCallArgs body.locals argOps frame.locals mem with
            | .ok _ =>
              match coreOp with
              | .usizeUncheckedSub =>
                "unchecked arithmetic overflow: Trusted.MirSemantics.FaultKind.undefined"
              | .sliceGetUncheckedRangeTo | .sliceGetUncheckedRangeFrom
              | .sliceIndexRange _ _ | .sliceIndexRangeFrom _ _
              | .sliceIsEmpty _ | .sliceSplitAt _ _ | .memReplace _
              | .optionTake _ | .ptrAdd _ _ | .sliceLen | .arrayEq _ _ =>
                "pointer or memory access undefined: Trusted.MirSemantics.FaultKind.undefined"
              | .numIsMultipleOf _ _ | .numCheckedAdd _ _ | .numCheckedMul _ _
              | .numCheckedSub _ _ | .numSaturatingAdd _ _ | .numWrappingShl _ _
              | .numWrappingShr _ _ | .numLeadingZeros _ _
              | .numOverflowingAdd _ _ | .numOverflowingSub _ _
              | .cmpMin _ _ | .cmpMax _ _ | .optionIsSome _
              | .optionIsNone _ | .optionUnwrap _ | .intToLeBytes _ _
              | .panicAbort =>
                "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
            | .error _ =>
              "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
        | .call _ argOps dstPlace _ _ | .sysrootCall _ argOps dstPlace _ _ =>
          match evalCallArgs body.locals argOps frame.locals mem with
          | .ok _ =>
            if isDeadSlotOpt (compGetElem? frame.locals dstPlace.localId) then
              "dead local write undefined: Trusted.MirSemantics.FaultKind.undefined"
            else
              "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
          | .error _ =>
            "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
        | _ =>
          "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"

structure PendingCall where
  calleeName : String
  dstLocal : LocalId
  targetOpt : Option BasicBlockId
  unwindAct : UnwindAction
  preLocals : List LocalSlot
  preMemAllocs : List Allocation

structure PendingCleanup where
  calleeName : String
  unwindReason : String
  argCount : Nat
  dstLocal : LocalId
  preLocals : List LocalSlot
  preMemAllocs : List Allocation
  spawnedLocals : List LocalId
  retiredLocals : List LocalId

def stepCleanupStatement (c : PendingCleanup) (stmt : StatementKind) : PendingCleanup :=
  match stmt with
  | .storageLive loc =>
    let clearedRetired := c.retiredLocals.filter (fun x => !Nat.beq x loc)
    if Nat.blt c.argCount loc && isDeadSlotOpt (compGetElem? c.preLocals loc) then
      { c with
        spawnedLocals := loc :: c.spawnedLocals
        retiredLocals := clearedRetired }
    else
      { c with retiredLocals := clearedRetired }
  | .storageDead loc =>
    if Nat.blt c.argCount loc
        && (Nat.beq loc c.dstLocal
          || natListContains c.spawnedLocals loc
          || isUninitImmediateOpt (compGetElem? c.preLocals loc)) then
      { c with retiredLocals := loc :: c.retiredLocals }
    else
      c
  | _ => c

structure StackEntry where
  frame : FrameState
  pending : Option PendingCall
  cleanup : Option PendingCleanup
  localUnwindReason : Option String := none

def assertUnwindReason : AssertKind → String
  | .overflow _ | .overflowNeg => "assert:overflow"
  | .divByZero => "assert:div_by_zero"
  | .remByZero => "assert:rem_by_zero"
  | .boundsCheck => "assert:bounds_check"
  | _ => "assert_failed"

def frameCalleeName (prog : Program) (defId : Nat) : String :=
  match compGetElem? prog.bodies defId with
  | some cb => if cb.identity.isEmpty then "fn_" ++ toString defId else cb.identity
  | none => "ext_" ++ toString defId

inductive StrictStepPreAction where
  | none
  | externalCall (callee : String)
  | branch (fromBlk : Nat) (discr : String)
  | callEnter (callee : String) (args : List Val)
  | callReturn (callee : String) (ret : Val) (dstLocal? : Option Nat)

def inspectStrictPreAction (prog : Program) (extCallees : List String) (st : State) :
    StrictStepPreAction :=
  match st.frames with
  | [] => .none
  | frame :: callers =>
    if frame.sysrootOp?.isSome then
      .none
    else
      match activeFrameBodyComp prog frame with
      | none => .none
      | some body =>
        match compGetElem? body.basicBlocks frame.blockIdx with
        | none => .none
        | some bb =>
          if !Nat.beq frame.stmtIdx bb.statements.length then
            .none
          else
            match bb.terminator with
            | .switchInt discr _ =>
              match evalPrimitiveOperandComp body.locals frame.locals st.mem discr with
              | .ok (dv, _, _) => .branch frame.blockIdx (valRepr dv)
              | .error _ => .none
            | .call calleeId argOps _ _ _ =>
              let calleeName := frameCalleeName prog calleeId
              if extCallees.any (fun n => n == "*" || n == calleeName) then
                .externalCall calleeName
              else
                match evalCallArgs body.locals argOps frame.locals st.mem with
                | .ok (argVals, _, _) => .callEnter calleeName argVals
                | .error _ => .none
            | .return_ =>
              if callers.isEmpty then
                .none
              else
                let calleeName := frameCalleeName prog frame.defId
                let dstId? := Option.map (fun d => d.localId) frame.retDst?
                match compGetElem? frame.locals 0 with
                | some (.immediate (some rv)) => .callReturn calleeName rv dstId?
                | _ => .none
            | _ => .none

def describeUnsupportedStepFault (prog : Program) (frame : FrameState) : String :=
  match activeFrameBodyComp prog frame with
  | none => "Trusted.MirSemantics.FaultKind.unsupported"
  | some body =>
    match compGetElem? body.basicBlocks frame.blockIdx with
    | none => "Trusted.MirSemantics.FaultKind.unsupported"
    | some bb =>
      if Nat.beq frame.stmtIdx bb.statements.length then
        match bb.terminator with
        | .unsupported => "unsupported terminator: Trusted.MirSemantics.FaultKind.unsupported"
        | _ => "Trusted.MirSemantics.FaultKind.unsupported"
      else
        "Trusted.MirSemantics.FaultKind.unsupported"

structure StrictCallSnapshot where
  calleeName : String
  preLocals : List LocalSlot
  preMemAllocs : List Allocation

def applyStrictUnwindChecks (mem : MemoryState) :
    List StrictCallSnapshot → List FrameState →
    Bool → Bool → Bool → List String → List String →
    (Bool × Bool × Bool × List String × List String)
  | [], _, localsOk, allocsOk, padOk, viols, eventsRev =>
    (localsOk, allocsOk, padOk, viols, eventsRev)
  | snap :: snaps, callerF :: callersRest, localsOk, allocsOk, padOk, viols, eventsRev =>
    let lOk := localsPreservedExcept none 0 snap.preLocals callerF.locals
    let aOk := preExistingAllocsPreserved snap.preMemAllocs mem.allocations
    let mOk := localMaskPreservedExcept none 0 snap.preLocals callerF.locals
      && preExistingAllocMasksPreserved snap.preMemAllocs mem.allocations
    let localsOk' := localsOk && lOk
    let allocsOk' := allocsOk && aOk
    let padOk' := padOk && mOk
    let viols' :=
      if lOk && aOk && mOk then viols
      else ("caller frame drift during strict unwind of " ++ snap.calleeName) :: viols
    let evs' :=
      mkFrameCheckEvent (snap.calleeName ++ ":unwind") (lOk && mOk) aOk ::
      mkCallUnwindEvent snap.calleeName "unwound" :: eventsRev
    applyStrictUnwindChecks mem snaps callersRest localsOk' allocsOk' padOk' viols' evs'
  | snap :: snaps, [], _, allocsOk, padOk, viols, eventsRev =>
    let viols' := ("missing caller frame during strict unwind of " ++ snap.calleeName) :: viols
    let evs' :=
      mkFrameCheckEvent (snap.calleeName ++ ":unwind") false allocsOk ::
      mkCallUnwindEvent snap.calleeName "unwound" :: eventsRev
    applyStrictUnwindChecks mem snaps [] false allocsOk padOk viols' evs'

def strictLoop (prog : Program) (extCallees : List String) (origFuel : Nat)
    (bSlots : List (List (Option Nat))) (sched : List ScheduleEntry)
    (callStack : List StrictCallSnapshot) :
    Nat → State → Bool → Bool → Bool → List String → List String → String
  | 0, _, localsOk, allocsOk, padOk, viols, eventsRev =>
    finishJson "diverged" "null" "strict step fuel exhausted" origFuel bSlots sched
      localsOk allocsOk padOk viols eventsRev
  | fuel + 1, st, localsOk, allocsOk, padOk, viols, eventsRev =>
    match inspectStrictPreAction prog extCallees st with
    | .externalCall extName =>
      finishJson "fault_unsupported" "null"
        ("external callee unsupported in StrictVerbatim: " ++ extName)
        origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
    | preAct =>
      match evalMirStepBy tyEqDepth prog 0 st with
      | .done (.returned out) =>
        let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
        finishReturnedJson out.ret origFuel bSlots sched localsOk allocsOk padOk viols evs
      | .done (.unwound _) =>
        let (lOk, aOk, pOk, viols', evsUnw) :=
          applyStrictUnwindChecks st.mem callStack
            ((st.frames.filter (fun f => f.sysrootOp?.isNone)).drop 1)
            localsOk allocsOk padOk viols eventsRev
        let evs := mkFrameCheckEvent "root_exit" (lOk && pOk) aOk :: evsUnw
        finishUnwoundJson "unwound" origFuel bSlots sched lOk aOk pOk viols' evs
      | .done (.aborted _) =>
        let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
        finishAbortedJson "aborted" origFuel bSlots sched localsOk allocsOk padOk viols evs
      | .fault .undefined =>
        let reason :=
          match st.frames with
          | frame :: _ => describeUndefinedStepFault prog frame st.mem
          | [] => "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
        finishJson "fault_undefined" "null" reason origFuel bSlots sched
          localsOk allocsOk padOk viols eventsRev
      | .fault .unsupported =>
        let reason :=
          match st.frames with
          | frame :: _ => describeUnsupportedStepFault prog frame
          | [] => "Trusted.MirSemantics.FaultKind.unsupported"
        finishJson "fault_unsupported" "null" reason
          origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
      | .step st' =>
        match preAct with
        | .branch fromBlk dStr =>
          let evs' :=
            if Nat.beq st.frames.length st'.frames.length then
              match st'.frames with
              | nextFrame :: _ => mkBranchEvent fromBlk dStr nextFrame.blockIdx :: eventsRev
              | [] => eventsRev
            else eventsRev
          strictLoop prog extCallees origFuel bSlots sched callStack fuel st'
            localsOk allocsOk padOk viols evs'
        | .callEnter calleeName argVals =>
          let isUserCallPush : Bool :=
            Nat.beq st'.frames.length (st.frames.length + 1) &&
              match st'.frames with
              | newTop :: _ => newTop.sysrootOp?.isNone
              | [] => false
          let callStack' :=
            if isUserCallPush then
              match st'.frames with
              | _ :: callerF :: _ =>
                { calleeName := calleeName
                  preLocals := callerF.locals
                  preMemAllocs := st'.mem.allocations } :: callStack
              | _ => callStack
            else callStack
          let evs' :=
            if isUserCallPush then mkCallEnterEvent calleeName argVals :: eventsRev
            else eventsRev
          strictLoop prog extCallees origFuel bSlots sched callStack' fuel st'
            localsOk allocsOk padOk viols evs'
        | .callReturn calleeName rv dstId? =>
          if Nat.beq (st'.frames.length + 1) st.frames.length then
            let (lOk, aOk, mOk, callStack', violExtra) :=
              match callStack, st'.frames with
              | snap :: restCalls, caller' :: _ =>
                let l := localsPreservedExcept dstId? 0 snap.preLocals caller'.locals
                let a := preExistingAllocsPreserved snap.preMemAllocs st'.mem.allocations
                let m := localMaskPreservedExcept dstId? 0 snap.preLocals caller'.locals
                  && preExistingAllocMasksPreserved snap.preMemAllocs st'.mem.allocations
                (l, a, m, restCalls, none)
              | _, _ =>
                (false, false, false, callStack,
                  some ("missing strict call snapshot for " ++ calleeName))
            let viols' :=
              match violExtra with
              | some v => v :: viols
              | none =>
                if lOk && aOk && mOk then viols
                else ("caller frame drift across strict return of " ++ calleeName) :: viols
            let evs' :=
              mkFrameCheckEvent (calleeName ++ ":return") (lOk && mOk) aOk ::
              mkCallReturnEvent calleeName rv :: eventsRev
            strictLoop prog extCallees origFuel bSlots sched callStack' fuel st'
              (localsOk && lOk) (allocsOk && aOk) (padOk && mOk) viols' evs'
          else
            strictLoop prog extCallees origFuel bSlots sched callStack fuel st'
              localsOk allocsOk padOk viols eventsRev
        | .none | .externalCall _ =>
          strictLoop prog extCallees origFuel bSlots sched callStack fuel st'
            localsOk allocsOk padOk viols eventsRev

def runSysrootSteps (prog : Program) : Nat → State → StepResult State TerminalOut × State
  | 0, st => (.fault .unsupported, st)
  | fuel + 1, st =>
    match evalMirStepBy tyEqDepth prog 0 st with
    | .step st' =>
      match st'.frames with
      | [nextCaller] =>
        if nextCaller.sysrootOp?.isNone then (.step st', st)
        else runSysrootSteps prog fuel st'
      | _ => runSysrootSteps prog fuel st'
    | other => (other, st)

mutual

partial def propagateUnwind (prog : Program) (extCallees : List String) (origFuel : Nat)
    (bSlots : List (List (Option Nat))) (corruptCallerOnReturn : Bool)
    (fuel : Nat) (stack : List StackEntry) (mem : MemoryState) (callerMem : CallerMemory)
    (sched : List ScheduleEntry) (localsOk allocsOk padOk : Bool)
    (viols eventsRev : List String) (reason : String) : String :=
  match stack with
  | [] =>
    let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
    finishUnwoundJson reason origFuel bSlots sched localsOk allocsOk padOk viols evs
  | caller :: rest =>
    match caller.pending with
    | none =>
      let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
      finishUnwoundJson reason origFuel bSlots sched localsOk allocsOk padOk viols evs
    | some p =>
      let eventsWithUnwind := mkCallUnwindEvent p.calleeName reason :: eventsRev
      match p.unwindAct with
      | .cleanup blk =>
        match activeFrameBodyComp prog caller.frame with
        | none =>
          finishJson "fault_unsupported" "null" "missing caller body for cleanup" origFuel bSlots sched
            localsOk allocsOk padOk viols eventsWithUnwind
        | some callerBody =>
          -- Defer CallerFrameLaw check until after cleanup block `blk` runs.
          let resumedCaller : StackEntry := {
            frame := { caller.frame with blockIdx := blk, stmtIdx := 0 }
            pending := none
            cleanup := some {
              calleeName := p.calleeName
              unwindReason := reason
              argCount := callerBody.argumentCount
              dstLocal := p.dstLocal
              preLocals := p.preLocals
              preMemAllocs := p.preMemAllocs
              spawnedLocals := []
              retiredLocals := []
            }
          }
          compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
            (resumedCaller :: rest) mem callerMem sched localsOk allocsOk padOk viols eventsWithUnwind
      | .continue_ =>
        let lOk := localsPreservedExcept none 0 p.preLocals caller.frame.locals
        let aOk := preExistingAllocsPreserved p.preMemAllocs mem.allocations
        let mOk := localMaskPreservedExcept none 0 p.preLocals caller.frame.locals
          && preExistingAllocMasksPreserved p.preMemAllocs mem.allocations
        let localsOk' := localsOk && lOk
        let allocsOk' := allocsOk && aOk
        let padOk' := padOk && mOk
        let viols' :=
          if lOk && aOk && mOk then viols
          else ("caller frame drift during unwind of " ++ p.calleeName) :: viols
        let eventsChecked :=
          mkFrameCheckEvent (p.calleeName ++ ":unwind") (lOk && mOk) aOk
            :: eventsWithUnwind
        propagateUnwind prog extCallees origFuel bSlots corruptCallerOnReturn fuel rest mem callerMem sched
          localsOk' allocsOk' padOk' viols' eventsChecked reason
      | .terminate =>
        finishAbortedJson ("unwind_terminate:" ++ reason) origFuel bSlots sched
          localsOk allocsOk padOk viols eventsWithUnwind
      | .unreachable =>
        finishJson "fault_undefined" "null" "unwind into UnwindAction.unreachable" origFuel bSlots sched
          localsOk allocsOk padOk viols eventsWithUnwind

partial def compositionalLoop (prog : Program) (extCallees : List String) (origFuel : Nat)
    (bSlots : List (List (Option Nat))) (corruptCallerOnReturn : Bool) :
    Nat → List StackEntry → MemoryState → CallerMemory →
      List ScheduleEntry → Bool → Bool → Bool → List String → List String → String
  | 0, _, _, _, sched, localsOk, allocsOk, padOk, viols, eventsRev =>
    finishJson "diverged" "null" "compositional step fuel exhausted" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
  | _fuel + 1, [], _, _, sched, localsOk, allocsOk, padOk, viols, eventsRev =>
    finishJson "fault_unsupported" "null" "empty call stack" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
  | fuel + 1, top :: rest, mem, callerMem, sched, localsOk, allocsOk, padOk, viols, eventsRev =>
    match activeFrameBodyComp prog top.frame with
    | none =>
      finishJson "fault_unsupported" "null" "missing body defId" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
    | some body =>
      match compGetElem? body.basicBlocks top.frame.blockIdx with
      | none =>
        finishJson "fault_unsupported" "null" "missing basicBlock" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
      | some bb =>
        if Nat.blt top.frame.stmtIdx bb.statements.length then
          let cleanup' :=
            match top.cleanup, compGetElem? bb.statements top.frame.stmtIdx with
            | some c, some stmt => some (stepCleanupStatement c stmt)
            | other, _ => other
          match evalMirStepBy tyEqDepth prog 0 { frames := [top.frame], callerMem, mem } with
          | .step st' =>
            match st'.frames with
            | [f'] =>
              compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                ({ top with frame := f', cleanup := cleanup' } :: rest) st'.mem st'.callerMem sched
                localsOk allocsOk padOk viols eventsRev
            | _ =>
              finishJson "fault_unsupported" "null" "unexpected frame count" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
          | .fault .undefined =>
            finishJson "fault_undefined" "null" (describeUndefinedStepFault prog top.frame mem) origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
          | .fault .unsupported =>
            finishJson "fault_unsupported" "null" "Trusted.MirSemantics.FaultKind.unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
          | .done (.returned out) =>
            let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
            finishReturnedJson out.ret origFuel bSlots sched localsOk allocsOk padOk viols evs
          | .done (.unwound _) =>
            let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
            finishUnwoundJson "unwound" origFuel bSlots sched localsOk allocsOk padOk viols evs
          | .done (.aborted _) =>
            let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
            finishAbortedJson "aborted" origFuel bSlots sched localsOk allocsOk padOk viols evs
        else if !Nat.beq top.frame.stmtIdx bb.statements.length then
          finishJson "fault_unsupported" "null" "stmtIdx out of bounds" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
        else
          match bb.terminator with
          | .goto _ | .unreachable | .coreCall _ _ _ _ _ =>
            match evalMirStepBy tyEqDepth prog 0 { frames := [top.frame], callerMem, mem } with
            | .step st' =>
              match st'.frames with
              | [f'] =>
                compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                  ({ top with frame := f' } :: rest) st'.mem st'.callerMem sched
                  localsOk allocsOk padOk viols eventsRev
              | _ =>
                finishJson "fault_unsupported" "null" "unexpected frame count" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .fault .undefined =>
              finishJson "fault_undefined" "null" (describeUndefinedStepFault prog top.frame mem) origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .fault .unsupported =>
              finishJson "fault_unsupported" "null" "Trusted.MirSemantics.FaultKind.unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .done (.returned out) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishReturnedJson out.ret origFuel bSlots sched localsOk allocsOk padOk viols evs
            | .done (.unwound _) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishUnwoundJson "unwound" origFuel bSlots sched localsOk allocsOk padOk viols evs
            | .done (.aborted _) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishAbortedJson "aborted" origFuel bSlots sched localsOk allocsOk padOk viols evs
          | .sysrootCall _ _ dstPlace _ _ =>
            let preAllocs := mem.allocations
            match runSysrootSteps prog 16 { frames := [top.frame], callerMem, mem } with
            | (.step st', _) =>
              match st'.frames with
              | [nextCaller] =>
                let lOk := localsPreservedExcept (some dstPlace.localId) 0 top.frame.locals nextCaller.locals
                let aOk := preExistingAllocsPreserved preAllocs st'.mem.allocations
                let mOk := localMaskPreservedExcept (some dstPlace.localId) 0 top.frame.locals nextCaller.locals
                  && preExistingAllocMasksPreserved preAllocs st'.mem.allocations
                let localsOk' := localsOk && lOk
                let allocsOk' := allocsOk && aOk
                let padOk' := padOk && mOk
                let viols' :=
                  if lOk && aOk && mOk then viols
                  else "caller frame drift across sysrootCall" :: viols
                let nextEntry : StackEntry := { top with frame := nextCaller }
                compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                  (nextEntry :: rest) st'.mem st'.callerMem sched
                  localsOk' allocsOk' padOk' viols' eventsRev
              | _ =>
                finishJson "fault_unsupported" "null" "unexpected frame count after sysrootCall" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | (.fault .undefined, faultSt) =>
              let reason :=
                match faultSt.frames with
                | frame :: _ => describeUndefinedStepFault prog frame faultSt.mem
                | [] => "uninitialized or invalid value undefined: Trusted.MirSemantics.FaultKind.undefined"
              finishJson "fault_undefined" "null" reason origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | (.fault .unsupported, _) =>
              finishJson "fault_unsupported" "null" "Trusted.MirSemantics.FaultKind.unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | (.done (.returned out), _) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishReturnedJson out.ret origFuel bSlots sched localsOk allocsOk padOk viols evs
            | (.done (.unwound _), _) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishUnwoundJson "unwound" origFuel bSlots sched localsOk allocsOk padOk viols evs
            | (.done (.aborted _), _) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishAbortedJson "aborted" origFuel bSlots sched localsOk allocsOk padOk viols evs
          | .switchInt discr _ =>
            let discrStr :=
              match evalPrimitiveOperandComp body.locals top.frame.locals mem discr with
              | .ok (dv, _, _) => valRepr dv
              | .error _ => "?"
            match evalMirStepBy tyEqDepth prog 0 { frames := [top.frame], callerMem, mem } with
            | .step st' =>
              match st'.frames with
              | [f'] =>
                let evs := mkBranchEvent top.frame.blockIdx discrStr f'.blockIdx :: eventsRev
                compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                  ({ top with frame := f' } :: rest) st'.mem st'.callerMem sched
                  localsOk allocsOk padOk viols evs
              | _ =>
                finishJson "fault_unsupported" "null" "unexpected frame count" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .fault .undefined =>
              finishJson "fault_undefined" "null" (describeUndefinedStepFault prog top.frame mem) origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .fault .unsupported =>
              finishJson "fault_unsupported" "null" "Trusted.MirSemantics.FaultKind.unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .done (.returned out) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishReturnedJson out.ret origFuel bSlots sched localsOk allocsOk padOk viols evs
            | .done (.unwound _) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishUnwoundJson "unwound" origFuel bSlots sched localsOk allocsOk padOk viols evs
            | .done (.aborted _) =>
              let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
              finishAbortedJson "aborted" origFuel bSlots sched localsOk allocsOk padOk viols evs
          | .return_ =>
            match evalMirStepBy tyEqDepth prog 0 { frames := [top.frame], callerMem, mem } with
            | .done (.returned out) =>
              match rest with
              | [] =>
                let evs := mkFrameCheckEvent "root_exit" (localsOk && padOk) allocsOk :: eventsRev
                finishReturnedJson out.ret origFuel bSlots sched localsOk allocsOk padOk viols evs
              | caller :: parents =>
                match caller.pending with
                | none =>
                  finishJson "fault_unsupported" "null" "caller missing pending call metadata" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                | some p =>
                  match activeFrameBodyComp prog caller.frame with
                  | none =>
                    finishJson "fault_unsupported" "null" "missing caller body" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                  | some callerBody =>
                    match compGetElem? callerBody.locals p.dstLocal with
                    | none =>
                      finishJson "fault_unsupported" "null" "caller dstLocal out of bounds" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                    | some dstTy =>
                      match writePlaceBy tyEqDepth caller.frame.locals mem p.dstLocal dstTy out.ret with
                      | .error .undefined =>
                        finishJson "fault_undefined" "null" "call return writePlace undefined" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                      | .error .unsupported =>
                        finishJson "fault_unsupported" "null" "call return writePlace unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                      | .ok (localsWritten, memAfter) =>
                        -- Negative self-test hook: corrupt caller local 1.
                        let localsAfter :=
                          if corruptCallerOnReturn then
                            match compSetElem? localsWritten 1 (.immediate none) with
                            | some bad => bad
                            | none => localsWritten
                          else
                            localsWritten
                        let lOk := localsPreservedExcept (some p.dstLocal) 0 p.preLocals localsAfter
                        let aOk := preExistingAllocsPreserved p.preMemAllocs memAfter.allocations
                        let dstTypeOk := checkValBy tyEqDepth out.ret dstTy
                        let mOk := dstTypeOk
                          && localMaskPreservedExcept (some p.dstLocal) 0 p.preLocals localsAfter
                          && preExistingAllocMasksPreserved p.preMemAllocs memAfter.allocations
                        let localsOk' := localsOk && lOk
                        let allocsOk' := allocsOk && aOk
                        let padOk' := padOk && mOk
                        let viols' :=
                          if lOk && aOk && mOk then viols
                          else ("caller frame drift across return of " ++ p.calleeName) :: viols
                        let evs :=
                          mkFrameCheckEvent (p.calleeName ++ ":return") (lOk && mOk) aOk ::
                          mkCallReturnEvent p.calleeName out.ret :: eventsRev
                        match p.targetOpt with
                        | none =>
                          finishJson "fault_undefined" "null" "returned from diverging call" origFuel bSlots sched localsOk' allocsOk' padOk' viols' evs
                        | some tgt =>
                          let resumedCaller : StackEntry := {
                            frame := { caller.frame with blockIdx := tgt, stmtIdx := 0, locals := localsAfter }
                            pending := none
                            cleanup := caller.cleanup
                          }
                          compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                            (resumedCaller :: parents) memAfter out.callerMem sched
                            localsOk' allocsOk' padOk' viols' evs
            | .fault .undefined =>
              finishJson "fault_undefined" "null" "uninitialized or dead return slot: Trusted.MirSemantics.FaultKind.undefined" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .fault .unsupported =>
              finishJson "fault_unsupported" "null" "Trusted.MirSemantics.FaultKind.unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | _ =>
              finishJson "fault_unsupported" "null" "unexpected return step result" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
          | .call calleeId argOps dstPlace targetOpt unwindAct =>
            if !dstPlace.projection.isEmpty then
              finishJson "fault_unsupported" "null" "projected call destination unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            else
              match evalCallArgs body.locals argOps top.frame.locals mem with
              | .error .undefined =>
                finishJson "fault_undefined" "null" "call argument eval undefined" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
              | .error .unsupported =>
                finishJson "fault_unsupported" "null" "call argument eval unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
              | .ok (argVals, callerLocalsAfterArgs, memAfterArgs) =>
                match compGetElem? callerLocalsAfterArgs dstPlace.localId with
                | none =>
                  finishJson "fault_unsupported" "null" "call destination out of bounds"
                    origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                | some .dead =>
                  finishJson "fault_undefined" "null"
                    "dead local write undefined: Trusted.MirSemantics.FaultKind.undefined"
                    origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                | some (.indirect _) | some (.partialTuple _) =>
                  finishJson "fault_unsupported" "null" "unsupported call destination slot"
                    origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                | some (.immediate _) =>
                  let calleeName :=
                    match compGetElem? prog.bodies calleeId with
                    | some cb => if cb.identity.isEmpty then "fn_" ++ toString calleeId else cb.identity
                    | none => "ext_" ++ toString calleeId
                  let evsAfterEnter := mkCallEnterEvent calleeName argVals :: eventsRev
                  match popSchedule calleeName sched with
                  | some (.returnBytes rawBytes, sched') =>
                    match compGetElem? body.locals dstPlace.localId with
                    | none =>
                      finishJson "fault_unsupported" "null" "dst local missing" origFuel bSlots sched' localsOk allocsOk padOk viols evsAfterEnter
                    | some dstTy =>
                      match decodeScheduledBytes dstTy rawBytes with
                      | .error .undefined =>
                        finishJson "fault_undefined" "null" ("invalid scheduled ReturnBytes for " ++ calleeName)
                          origFuel bSlots sched' localsOk allocsOk padOk viols evsAfterEnter
                      | .error .unsupported =>
                        finishJson "fault_unsupported" "null" ("unsupported scheduled ReturnBytes type for " ++ calleeName)
                          origFuel bSlots sched' localsOk allocsOk padOk viols evsAfterEnter
                      | .ok rv =>
                        match writePlaceBy tyEqDepth callerLocalsAfterArgs memAfterArgs dstPlace.localId dstTy rv with
                        | .error .undefined =>
                          finishJson "fault_undefined" "null" "scheduled return writePlace undefined" origFuel bSlots sched' localsOk allocsOk padOk viols evsAfterEnter
                        | .error .unsupported =>
                          finishJson "fault_unsupported" "null" "scheduled return writePlace unsupported" origFuel bSlots sched' localsOk allocsOk padOk viols evsAfterEnter
                        | .ok (localsAfter, memAfter) =>
                          let lOk := localsPreservedExcept (some dstPlace.localId) 0 callerLocalsAfterArgs localsAfter
                          let aOk := preExistingAllocsPreserved memAfterArgs.allocations memAfter.allocations
                          let mOk := checkValBy tyEqDepth rv dstTy
                            && localMaskPreservedExcept (some dstPlace.localId) 0 callerLocalsAfterArgs localsAfter
                            && preExistingAllocMasksPreserved memAfterArgs.allocations memAfter.allocations
                          let localsOk' := localsOk && lOk
                          let allocsOk' := allocsOk && aOk
                          let padOk' := padOk && mOk
                          let viols' :=
                            if lOk && aOk && mOk then viols
                            else ("caller frame drift on scheduled return " ++ calleeName) :: viols
                          let evs :=
                            mkFrameCheckEvent (calleeName ++ ":return") (lOk && mOk) aOk ::
                            mkCallReturnEvent calleeName rv :: evsAfterEnter
                          match targetOpt with
                          | none =>
                            finishJson "fault_undefined" "null" "scheduled return from diverging call" origFuel bSlots sched' localsOk' allocsOk' padOk' viols' evs
                          | some tgt =>
                            let nextCaller : StackEntry := {
                              frame := { top.frame with blockIdx := tgt, stmtIdx := 0, locals := localsAfter }
                              pending := none
                              cleanup := top.cleanup
                            }
                            compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                              (nextCaller :: rest) memAfter callerMem sched' localsOk' allocsOk' padOk' viols' evs
                  | some (.unwind msg, sched') =>
                    let pendingCaller : StackEntry := {
                      frame := { top.frame with locals := callerLocalsAfterArgs }
                      pending := some {
                        calleeName := calleeName
                        dstLocal := dstPlace.localId
                        targetOpt := targetOpt
                        unwindAct := unwindAct
                        preLocals := callerLocalsAfterArgs
                        preMemAllocs := memAfterArgs.allocations
                      }
                      cleanup := top.cleanup
                    }
                    propagateUnwind prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                      (pendingCaller :: rest) memAfterArgs callerMem sched' localsOk allocsOk padOk viols evsAfterEnter msg
                  | some (.abort reason, sched') =>
                    let evs := mkCallUnwindEvent calleeName ("abort:" ++ reason) :: evsAfterEnter
                    finishAbortedJson ("abort:" ++ reason) origFuel bSlots sched' localsOk allocsOk padOk viols evs
                  | none =>
                    match compGetElem? prog.bodies calleeId with
                    | none =>
                      finishJson "fault_unsupported" "null" ("missing callee body " ++ calleeName) origFuel bSlots sched localsOk allocsOk padOk viols evsAfterEnter
                    | some calleeBody =>
                      let paramTys := (calleeBody.locals.drop 1).take calleeBody.argumentCount
                      if calleeBody.basicBlocks.isEmpty
                          || !Nat.blt calleeBody.argumentCount calleeBody.locals.length
                          || !storageAnnotationsInBoundsComp calleeBody
                          || !discriminantTypesValidBy tyEqDepth calleeBody
                          || !castTypesValidBy tyEqDepth calleeBody
                          || !calleeBody.locals.all isSupportedScalarOrUnitTyComp
                          || !checkArgsMatchBy tyEqDepth argVals paramTys then
                        finishJson "fault_unsupported" "null" ("callee body rejected by static admission: " ++ calleeName)
                          origFuel bSlots sched localsOk allocsOk padOk viols evsAfterEnter
                      else
                        let calleeFrame : FrameState := {
                          defId := calleeId
                          blockIdx := 0
                          stmtIdx := 0
                          locals := initLocalsLoopComp calleeBody argVals 0 calleeBody.locals
                        }
                        let savedCaller : StackEntry := {
                          frame := { top.frame with locals := callerLocalsAfterArgs }
                          pending := some {
                            calleeName := calleeName
                            dstLocal := dstPlace.localId
                            targetOpt := targetOpt
                            unwindAct := unwindAct
                            preLocals := callerLocalsAfterArgs
                            preMemAllocs := memAfterArgs.allocations
                          }
                          cleanup := top.cleanup
                        }
                        compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                          ({ frame := calleeFrame, pending := none, cleanup := none } :: savedCaller :: rest)
                          memAfterArgs callerMem sched localsOk allocsOk padOk viols evsAfterEnter
          | .unwindResume =>
            -- Check caller frame preservation after cleanup block statements.
            let (localsOk', allocsOk', padOk', viols', eventsAfterCleanup, resumeReason) :=
              match top.cleanup with
              | none => (localsOk, allocsOk, padOk, viols, eventsRev, top.localUnwindReason.getD "unwind_resume")
              | some c =>
                let lOk := localsPreservedAfterCleanup c.retiredLocals 0 c.preLocals top.frame.locals
                let aOk := preExistingAllocsPreserved c.preMemAllocs mem.allocations
                let mOk := localMaskPreservedAfterCleanup c.retiredLocals 0 c.preLocals top.frame.locals
                  && preExistingAllocMasksPreserved c.preMemAllocs mem.allocations
                let vNext :=
                  if lOk && aOk && mOk then viols
                  else ("caller frame drift during cleanup block of " ++ c.calleeName) :: viols
                let eNext :=
                  mkFrameCheckEvent (c.calleeName ++ ":unwind") (lOk && mOk) aOk
                    :: eventsRev
                (localsOk && lOk, allocsOk && aOk, padOk && mOk, vNext, eNext, c.unwindReason)
            propagateUnwind prog extCallees origFuel bSlots corruptCallerOnReturn fuel
              rest mem callerMem sched localsOk' allocsOk' padOk' viols' eventsAfterCleanup resumeReason
          | .assert condOp expected msgKind target unwindAct =>
            match evalPrimitiveOperandComp body.locals top.frame.locals mem condOp with
            | .error .undefined =>
              finishJson "fault_undefined" "null" "assert condition undefined" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .error .unsupported =>
              finishJson "fault_unsupported" "null" "assert condition unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .ok (.bool b, localsAfter, memAfter) =>
              match msgKind with
              | .unsupported =>
                finishJson "fault_unsupported" "null" "assert kind unsupported" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
              | .misalignedPtrDeref | .nullPtrDeref =>
                if b == expected then
                  let nextEntry : StackEntry := {
                    frame := { top.frame with blockIdx := target, stmtIdx := 0, locals := localsAfter }
                    pending := none
                    cleanup := top.cleanup
                  }
                  compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                    (nextEntry :: rest) memAfter callerMem sched localsOk allocsOk padOk viols eventsRev
                else
                  finishJson "fault_undefined" "null" "assert pointer dereference undefined" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
              | .overflow _ | .overflowNeg | .divByZero | .remByZero | .boundsCheck =>
                if b == expected then
                  let nextEntry : StackEntry := {
                    frame := { top.frame with blockIdx := target, stmtIdx := 0, locals := localsAfter }
                    pending := none
                    cleanup := top.cleanup
                    localUnwindReason := top.localUnwindReason
                  }
                  compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                    (nextEntry :: rest) memAfter callerMem sched localsOk allocsOk padOk viols eventsRev
                else
                  let assertReason := assertUnwindReason msgKind
                  match unwindAct with
                  | .cleanup blk =>
                    let nextEntry : StackEntry := {
                      frame := { top.frame with blockIdx := blk, stmtIdx := 0, locals := localsAfter }
                      pending := none
                      cleanup := top.cleanup
                      localUnwindReason := some assertReason
                    }
                    compositionalLoop prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                      (nextEntry :: rest) memAfter callerMem sched localsOk allocsOk padOk viols eventsRev
                  | .continue_ =>
                    propagateUnwind prog extCallees origFuel bSlots corruptCallerOnReturn fuel
                      rest memAfter callerMem sched localsOk allocsOk padOk viols eventsRev assertReason
                  | .terminate =>
                    finishAbortedJson "assert_terminate" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
                  | .unreachable =>
                    finishJson "fault_undefined" "null" "assert_unreachable" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
            | .ok (_, _, _) =>
              finishJson "fault_unsupported" "null" "non-bool assert condition" origFuel bSlots sched localsOk allocsOk padOk viols eventsRev
          | .unsupported =>
            finishJson "fault_unsupported" "null"
              "unsupported terminator: Trusted.MirSemantics.FaultKind.unsupported"
              origFuel bSlots sched localsOk allocsOk padOk viols eventsRev

end

def initCompositionalEntryFrame (p : Program) (args : List Val) :
    Except FaultKind (FrameState × MemoryState × CallerMemory) :=
  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then
    .error .unsupported
  else
    match compGetElem? p.bodies p.entryDefId with
    | none => .error .unsupported
    | some body =>
      if body.basicBlocks.isEmpty then .error .unsupported
      else if !Nat.blt body.argumentCount body.locals.length then .error .unsupported
      else if !storageAnnotationsInBoundsComp body then .error .unsupported
      else if !discriminantTypesValidBy tyEqDepth body then .error .unsupported
      else if !castTypesValidBy tyEqDepth body then .error .unsupported
      else if !body.locals.all isSupportedScalarOrUnitTyComp then .error .unsupported
      else
        let paramTys := (body.locals.drop 1).take body.argumentCount
        if !checkArgsMatchBy tyEqDepth args paramTys then .error .unsupported
        else
          .ok (
            {
              defId := p.entryDefId
              blockIdx := 0
              stmtIdx := 0
              locals := initLocalsLoopComp body args 0 body.locals
            },
            entryMemoryComp,
            ⟨[]⟩
          )

def runTraceCore (prog : Program) (mode : TraceMode) (fuel : Nat) (args : List Val)
    (sched : List ScheduleEntry) (extCallees : List String)
    (corruptCallerOnReturn : Bool) : String :=
  let bSlots := args.map encodeBoundaryValBytes
  match mode with
  | .strictVerbatim =>
    match initStateBy tyEqDepth prog { args := args } with
    | .error .undefined =>
      finishJson "fault_undefined" "null" "initStateBy undefined" fuel bSlots sched true true true [] []
    | .error .unsupported =>
      finishJson "init_unsupported" "null" "initStateBy unsupported" fuel bSlots sched true true true [] []
    | .ok s0 =>
      strictLoop prog extCallees fuel bSlots sched [] fuel s0 true true true [] []
  | .compositionalITree =>
    match initCompositionalEntryFrame prog args with
    | .error .undefined =>
      finishJson "fault_undefined" "null" "initStateBy undefined" fuel bSlots sched true true true [] []
    | .error .unsupported =>
      finishJson "init_unsupported" "null" "initStateBy unsupported" fuel bSlots sched true true true [] []
    | .ok (f0, mem0, callerMem0) =>
      compositionalLoop prog extCallees fuel bSlots corruptCallerOnReturn fuel
        [{ frame := f0, pending := none, cleanup := none }]
        mem0 callerMem0 sched true true true [] []

def runTraceChecked (prog : Program) (mode : TraceMode) (fuel : Nat)
    (argExprs : List (Except FaultKind Val))
    (sched : List ScheduleEntry) (extCallees : List String) : String :=
  match seqExceptVals argExprs with
  | .error .undefined =>
    finishJson "fault_undefined" "null" "entry argument bit-validity failed" fuel [] sched true true true [] []
  | .error .unsupported =>
    finishJson "init_unsupported" "null" "entry argument type unsupported" fuel [] sched true true true [] []
  | .ok args =>
    runTraceCore prog mode fuel args sched extCallees false

def runTraceCorruptCallerTest (prog : Program) (fuel : Nat) (args : List Val) : String :=
  runTraceCore prog .compositionalITree fuel args [] [] true

end ITreeDriver
"#;

/// Derive the compiler- and Cargo-keyed target directory suffix for building
/// `anneal-rustc-capture`, ensuring in-place replacements of `rustc`,
/// `librustc_driver` / host sysroot libraries, or `cargo` never reuse a stale
/// capture binary.
pub fn compute_capture_build_dir_tag(rustc_sysroot_digest: &str, cargo_bin_sha256: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-capture-target-v1\0");
    update_len_prefixed_sha256(&mut hasher, rustc_sysroot_digest.as_bytes());
    update_len_prefixed_sha256(&mut hasher, cargo_bin_sha256.as_bytes());
    let hex = sha256_hex(&hasher.finalize());
    hex[..24].to_string()
}

fn ensure_capture_binary(
    anneal_root: &Path,
    cache_root: &Path,
    rust_sysroot: &Path,
    rustc_sysroot_digest: &str,
    child_path: &std::ffi::OsStr,
) -> Result<PathBuf, String> {
    fs::create_dir_all(cache_root)
        .map_err(|e| format!("create cache dir {}: {e}", cache_root.display()))?;
    let cargo_bin = resolve_cargo_binary(rust_sysroot)?;
    let (_, cargo_sha) = stream_sha256_file(&cargo_bin)?;
    let cargo_bin_sha256 = sha256_hex(&cargo_sha);
    let build_tag = compute_capture_build_dir_tag(rustc_sysroot_digest, &cargo_bin_sha256);

    let lock_path = cache_root.join(format!("capture-build-{build_tag}.lock"));
    let lock_file = File::options()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
        .map_err(|e| format!("open capture build lock {}: {e}", lock_path.display()))?;
    lock_file
        .lock()
        .map_err(|e| format!("acquire capture build lock {}: {e}", lock_path.display()))?;

    let target_dir = cache_root.join(format!("capture-target-{build_tag}"));
    let stamp_path = target_dir.join(".anneal-capture-build-identity");
    if target_dir.exists()
        && fs::read_to_string(&stamp_path).ok().as_deref().map(str::trim) != Some(&build_tag)
    {
        fs::remove_dir_all(&target_dir)
            .map_err(|e| format!("clean stale capture target dir {}: {e}", target_dir.display()))?;
    }
    let manifest_path = anneal_root.join("Cargo.toml");
    let rustc_exe = exe_name("rustc");
    let rustc_bin = rust_sysroot.join("bin").join(&rustc_exe);
    if !rustc_bin.is_file() {
        return Err(format!(
            "cannot build `anneal-rustc-capture`: missing `bin/{rustc_exe}` under {} (set ANNEAL_CAPTURE or ANNEAL_SYSROOT)",
            rust_sysroot.display()
        ));
    }

    let inv = build_capture_cargo_invocation_with_env(
        &cargo_bin,
        &manifest_path,
        &target_dir,
        &rustc_bin,
        rust_sysroot,
        &join_dylib_path(&rust_sysroot.join("lib")),
        child_path,
        None,
        |k| env::var_os(k),
    );

    let out = run_supervised_cmd(&inv, anneal_root, CAPTURE_BUILD_TIMEOUT_SECS)?;
    match out.termination {
        Termination::Exited(s) if s.success() => {}
        other => {
            return Err(format!(
                "building anneal-rustc-capture failed ({}):\nstdout:\n{}\nstderr:\n{}",
                other.describe(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }
    fs::write(&stamp_path, format!("{build_tag}\n"))
        .map_err(|e| format!("write capture build stamp {}: {e}", stamp_path.display()))?;
    drop(lock_file);

    let bin_path = target_dir.join("debug").join(exe_name("anneal-rustc-capture"));
    fs::canonicalize(&bin_path)
        .map_err(|e| format!("canonicalize built anneal-rustc-capture {}: {e}", bin_path.display()))
}

fn resolve_cargo_binary(rust_sysroot: &Path) -> Result<PathBuf, String> {
    resolve_cargo_binary_with_env_and_suffix(
        rust_sysroot,
        |k| env::var_os(k),
        env::consts::EXE_SUFFIX,
    )
}

/// Deterministic environment- and suffix-parameterized `cargo` resolver for
/// `ensure_capture_binary`, preferring `<rust_sysroot>/bin/cargo` and
/// preserving the `cargo` leaf filename whenever `CARGO` or `PATH` resolves to
/// a `rustup` multicall proxy (`~/.cargo/bin/cargo -> rustup`).
pub fn resolve_cargo_binary_with_env_and_suffix(
    rust_sysroot: &Path,
    get_env: impl Fn(&str) -> Option<OsString>,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    let cargo_exe = exe_name_for_suffix("cargo", exe_suffix);
    let sysroot_cargo = rust_sysroot.join("bin").join(&cargo_exe);
    if sysroot_cargo.is_file() {
        return canonicalize_preserving_rustup_proxy_with_suffix(
            &sysroot_cargo,
            Some(rust_sysroot),
            "cargo",
            exe_suffix,
        );
    }
    let path_var = get_env("PATH");
    if let Some(cargo_env) = get_env("CARGO").filter(|v| !v.is_empty())
        && let Some(found) =
            resolve_explicit_or_path_exe_with_suffix(&cargo_env, path_var.as_deref(), exe_suffix)
    {
        return canonicalize_preserving_rustup_proxy_with_suffix(
            &found,
            Some(rust_sysroot),
            "cargo",
            exe_suffix,
        );
    }
    if let Some(path_var) = path_var {
        for dir in env::split_paths(&path_var) {
            let cand = dir.join(&cargo_exe);
            if cand.is_file() {
                return canonicalize_preserving_rustup_proxy_with_suffix(
                    &cand,
                    Some(rust_sysroot),
                    "cargo",
                    exe_suffix,
                );
            }
        }
    }
    Err("cannot locate `cargo` binary to build `anneal-rustc-capture`".to_string())
}

const STREAM_HASH_BUF_BYTES: usize = 64 * 1024;

/// Compute a deterministic SHA-256 capture-cache identity for `rust_sysroot`
/// using streaming 64 KiB `Sha256` reads (never buffering whole compiler or
/// library binaries on the heap), binding:
/// 1. Domain separator `"anneal-itree-rustc-sysroot-v2\0"` + canonical
///    `rust_sysroot` path,
/// 2. `<rust_sysroot>/bin/rustc` `-vV` stdout (including its validated `host:`
///    target triple) AND streaming SHA-256 of `<rust_sysroot>/bin/rustc`
///    executable bytes (failing closed if `bin/rustc` exists and cannot be
///    executed or read; recording `"no-bin-rustc\0"` only when `bin/rustc` is
///    absent),
/// 3. Sorted regular/resolved library files directly under `<rust_sysroot>/lib`
///    (`.so`, `.dylib`, `.dll`, `.a`, and versioned `.so.` shared objects such
///    as `librustc_driver-*.so` and `libLLVM*.so*`), AND
/// 4. Sorted regular/resolved target library artifacts under
///    `<rust_sysroot>/lib/rustlib/<host_target>/lib` (or all sorted
///    `lib/rustlib/*/lib` target directories when `bin/rustc` is absent) with
///    extensions `.rlib`, `.rmeta`, `.so`, `.dylib`, `.dll`, or `.a` (such as
///    `libcore*.rlib` and `libstd*.rlib`).
pub fn compute_rustc_sysroot_digest(rust_sysroot: &Path) -> Result<String, String> {
    let canon_sysroot = fs::canonicalize(rust_sysroot)
        .map_err(|e| format!("canonicalize rust sysroot {}: {e}", rust_sysroot.display()))?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-rustc-sysroot-v2\0");
    let sysroot_str = canon_sysroot.to_string_lossy();
    hasher.update((sysroot_str.len() as u64).to_le_bytes());
    hasher.update(sysroot_str.as_bytes());

    let lib_dir = canon_sysroot.join("lib");
    if !lib_dir.is_dir() {
        return Err(format!("missing sysroot `lib` directory at {}", lib_dir.display()));
    }

    let rustc_bin = canon_sysroot.join("bin").join(exe_name("rustc"));
    let resolved_host_target = match fs::symlink_metadata(&rustc_bin) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            hasher.update(b"no-bin-rustc\0");
            None
        }
        Err(e) => {
            return Err(format!("inspect {}: {e}", rustc_bin.display()));
        }
        Ok(_) => {
            let dylib = join_dylib_path(&lib_dir);
            let out = run_probe_supervised(&rustc_bin, &["-vV"], Some(&dylib), true)
                .map_err(|e| format!("run `{} -vV`: {e}", rustc_bin.display()))?;
            if !out.status.success() {
                return Err(format!(
                    "`{} -vV` failed: {}",
                    rustc_bin.display(),
                    String::from_utf8_lossy(&out.stderr)
                ));
            }
            let vv_str = String::from_utf8(out.stdout)
                .map_err(|e| format!("invalid UTF-8 from `{} -vV`: {e}", rustc_bin.display()))?;
            let host_target = parse_and_validate_host_target_triple(&vv_str)?;
            let (bin_len, bin_sha) = stream_sha256_file(&rustc_bin)?;
            hasher.update(b"bin-rustc\0");
            hasher.update((vv_str.len() as u64).to_le_bytes());
            hasher.update(vv_str.as_bytes());
            hasher.update(bin_len.to_le_bytes());
            hasher.update(bin_sha);
            if let Some(backing_sr) = resolve_verified_backing_sysroot_with_suffix(
                &canon_sysroot,
                env::consts::EXE_SUFFIX,
            )? {
                let backing_rustc = backing_sr.join("bin").join(exe_name("rustc"));
                if backing_rustc.is_file() {
                    let (b_len, b_sha) = stream_sha256_file(&backing_rustc)?;
                    hasher.update(b"bin-rustc-backing\0");
                    hasher.update(b_len.to_le_bytes());
                    hasher.update(b_sha);
                }
            }
            Some(host_target)
        }
    };

    hasher.update(b"host-lib\0");
    let host_libs = collect_and_hash_sysroot_libs(&lib_dir, false)?;
    hasher.update((host_libs.len() as u64).to_le_bytes());
    for (name, len, file_sha) in &host_libs {
        hasher.update((name.len() as u64).to_le_bytes());
        hasher.update(name.as_bytes());
        hasher.update(len.to_le_bytes());
        hasher.update(file_sha);
    }

    let target_triples = match resolved_host_target {
        Some(triple) => vec![triple],
        None => discover_rustlib_target_triples(&lib_dir.join("rustlib"))?,
    };
    if target_triples.is_empty() {
        hasher.update(b"no-target-lib\0");
    } else {
        for triple in &target_triples {
            let target_lib_dir = lib_dir.join("rustlib").join(triple).join("lib");
            match fs::symlink_metadata(&target_lib_dir) {
                Err(e) if e.kind() == io::ErrorKind::NotFound => {
                    hasher.update(b"no-target-lib\0");
                }
                Err(e) => {
                    return Err(format!("inspect {}: {e}", target_lib_dir.display()));
                }
                Ok(_) => {
                    let meta = fs::metadata(&target_lib_dir)
                        .map_err(|e| format!("stat {}: {e}", target_lib_dir.display()))?;
                    if !meta.is_dir() {
                        return Err(format!(
                            "expected directory at {}, found non-directory",
                            target_lib_dir.display()
                        ));
                    }
                    hasher.update(b"target-lib\0");
                    hasher.update((triple.len() as u64).to_le_bytes());
                    hasher.update(triple.as_bytes());
                    let target_libs = collect_and_hash_sysroot_libs(&target_lib_dir, true)?;
                    hasher.update((target_libs.len() as u64).to_le_bytes());
                    for (name, len, file_sha) in &target_libs {
                        hasher.update((name.len() as u64).to_le_bytes());
                        hasher.update(name.as_bytes());
                        hasher.update(len.to_le_bytes());
                        hasher.update(file_sha);
                    }
                }
            }
        }
    }

    Ok(sha256_hex(&hasher.finalize()))
}

fn discover_rustlib_target_triples(rustlib_dir: &Path) -> Result<Vec<String>, String> {
    let entries = match fs::read_dir(rustlib_dir) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(format!("read_dir {}: {e}", rustlib_dir.display())),
        Ok(rd) => rd,
    };
    let mut triples = Vec::new();
    for ent in entries {
        let ent = ent.map_err(|e| format!("entry in {}: {e}", rustlib_dir.display()))?;
        let name = ent.file_name().to_string_lossy().into_owned();
        if matches!(name.as_str(), "src" | "etc") {
            continue;
        }
        if ent.path().join("lib").is_dir() {
            triples.push(name);
        }
    }
    triples.sort();
    Ok(triples)
}

fn has_sysroot_lib_extension(file_name: &str, include_rust_rlibs: bool) -> bool {
    let ext = Path::new(file_name).extension().and_then(|s| s.to_str());
    let base_match =
        matches!(ext, Some("so" | "dylib" | "dll" | "a")) || file_name.contains(".so.");
    if include_rust_rlibs {
        base_match || matches!(ext, Some("rlib" | "rmeta"))
    } else {
        base_match
    }
}

fn stream_sha256_file(path: &Path) -> Result<(u64, [u8; 32]), String> {
    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
    stream_sha256_file_with_buf(path, &mut buf)
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

type HashedSysrootLib = (String, u64, [u8; 32]);

fn collect_and_hash_sysroot_libs(
    dir: &Path,
    include_rust_rlibs: bool,
) -> Result<Vec<HashedSysrootLib>, String> {
    let mut sorted: BTreeMap<String, PathBuf> = BTreeMap::new();
    for entry in fs::read_dir(dir).map_err(|e| format!("read_dir {}: {e}", dir.display()))? {
        let entry = entry.map_err(|e| format!("iterate {}: {e}", dir.display()))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if !has_sysroot_lib_extension(&name, include_rust_rlibs) {
            continue;
        }
        let path = entry.path();
        let meta =
            fs::metadata(&path).map_err(|e| format!("stat sysroot lib {}: {e}", path.display()))?;
        if meta.is_file() {
            sorted.insert(name, path);
        }
    }

    let items: Vec<(String, PathBuf)> = sorted.into_iter().collect();
    if items.is_empty() {
        return Ok(Vec::new());
    }
    let workers =
        thread::available_parallelism().map(|n| n.get().clamp(1, 4)).unwrap_or(1).min(items.len());
    if workers <= 1 {
        return items
            .into_iter()
            .map(|(name, path)| {
                let (len, sha) = stream_sha256_file(&path)?;
                Ok((name, len, sha))
            })
            .collect();
    }

    let chunk_size = items.len().div_ceil(workers);
    let chunk_results: Vec<Result<Vec<HashedSysrootLib>, String>> = thread::scope(|scope| {
        let mut handles = Vec::with_capacity(workers);
        for chunk in items.chunks(chunk_size) {
            handles.push(scope.spawn(move || {
                let mut local = Vec::with_capacity(chunk.len());
                for (name, path) in chunk {
                    let (len, sha) = stream_sha256_file(path)?;
                    local.push((name.clone(), len, sha));
                }
                Ok(local)
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_else(|_| Err("sysroot hash worker panicked".to_string())))
            .collect()
    });

    let mut out = Vec::with_capacity(items.len());
    for res in chunk_results {
        out.extend(res?);
    }
    Ok(out)
}

fn query_lean_stdout(lean_bin: &Path, arg: &str) -> Result<Vec<u8>, String> {
    let inv = apply_lean_env_with_env(Invocation::new(lean_bin, &[arg]), lean_bin, "", None, |k| {
        env::var_os(k)
    });
    let work_dir = lean_bin.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised_cmd(&inv, work_dir, 60)?;
    match out.termination {
        Termination::Exited(s) if s.success() => Ok(out.stdout),
        other => Err(format!(
            "`lean {arg}` failed ({}): {}",
            other.describe(),
            String::from_utf8_lossy(&out.stderr)
        )),
    }
}

fn query_lean_prefix(lean_bin: &Path) -> Result<PathBuf, String> {
    let stdout = query_lean_stdout(lean_bin, "--print-prefix")?;
    let text = String::from_utf8(stdout)
        .map_err(|e| format!("invalid UTF-8 from `lean --print-prefix`: {e}"))?;
    fs::canonicalize(text.trim()).map_err(|e| format!("canonicalize lean prefix: {e}"))
}

fn query_lean_version_bytes(lean_bin: &Path) -> Result<Vec<u8>, String> {
    query_lean_stdout(lean_bin, "--version")
}

const MAX_LEAN_HASH_WORKERS: usize = 8;
type HashedCanonFile = (PathBuf, (u64, [u8; 32]));

fn update_len_prefixed_sha256(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn stream_hash_lean_entries(
    entries: &[(String, PathBuf)],
) -> Result<Vec<HashedSysrootLib>, String> {
    if entries.is_empty() {
        return Ok(Vec::new());
    }
    // Deduplicate physical file reads when multiple symlinks point at the same
    // canonical library target (such as `libLLVM.so -> libLLVM.so.23.1`), while
    // preserving every logical `(rel_path, len, sha)` entry in sorted order.
    let mut unique_paths: Vec<PathBuf> = entries.iter().map(|(_, p)| p.clone()).collect();
    unique_paths.sort();
    unique_paths.dedup();

    let workers = thread::available_parallelism()
        .map(|n| n.get().clamp(1, MAX_LEAN_HASH_WORKERS))
        .unwrap_or(1)
        .min(unique_paths.len());

    let hashed_unique: BTreeMap<PathBuf, (u64, [u8; 32])> = if workers <= 1 {
        let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
        let mut map = BTreeMap::new();
        for p in unique_paths {
            let res = stream_sha256_file_with_buf(&p, &mut buf)?;
            map.insert(p, res);
        }
        map
    } else {
        let chunk_size = unique_paths.len().div_ceil(workers);
        let chunk_results: Vec<Result<Vec<HashedCanonFile>, String>> = thread::scope(|scope| {
            let mut handles = Vec::with_capacity(workers);
            for chunk in unique_paths.chunks(chunk_size) {
                handles.push(scope.spawn(move || {
                    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
                    let mut local = Vec::with_capacity(chunk.len());
                    for p in chunk {
                        let res = stream_sha256_file_with_buf(p, &mut buf)?;
                        local.push((p.clone(), res));
                    }
                    Ok(local)
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_else(|_| Err("Lean hash worker panicked".to_string())))
                .collect()
        });
        let mut map = BTreeMap::new();
        for res in chunk_results {
            for (p, digest) in res? {
                map.insert(p, digest);
            }
        }
        map
    };

    let mut out = Vec::with_capacity(entries.len());
    for (rel, p) in entries {
        let &(len, sha) = hashed_unique
            .get(p)
            .ok_or_else(|| format!("missing hashed entry for {}", p.display()))?;
        out.push((rel.clone(), len, sha));
    }
    Ok(out)
}

fn walk_lean_stdlib_tree(
    current_dir: &Path,
    rel_prefix: &str,
    canon_prefix: &Path,
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
            format!("non-UTF-8 entry in Lean stdlib {}: {raw_name:?}", current_dir.display())
        })?;
        let path = entry.path();
        let sym_meta = fs::symlink_metadata(&path)
            .map_err(|e| format!("inspect Lean stdlib entry {}: {e}", path.display()))?;
        let ft = sym_meta.file_type();
        let rel_path =
            if rel_prefix.is_empty() { name.to_string() } else { format!("{rel_prefix}/{name}") };

        if ft.is_symlink() {
            let target_canon = fs::canonicalize(&path)
                .map_err(|e| format!("resolve Lean stdlib symlink {}: {e}", path.display()))?;
            if !target_canon.starts_with(canon_prefix) {
                return Err(format!(
                    "Lean stdlib symlink {} escapes Lean prefix {} -> {}",
                    path.display(),
                    canon_prefix.display(),
                    target_canon.display()
                ));
            }
            let target_meta = fs::metadata(&target_canon).map_err(|e| {
                format!("stat Lean stdlib symlink target {}: {e}", target_canon.display())
            })?;
            if target_meta.is_file() {
                out.push((rel_path, target_canon));
            } else if target_meta.is_dir() {
                if !active_dirs.insert(target_canon.clone()) {
                    return Err(format!(
                        "Lean stdlib symlink directory cycle at {}",
                        path.display()
                    ));
                }
                walk_lean_stdlib_tree(&target_canon, &rel_path, canon_prefix, active_dirs, out)?;
                active_dirs.remove(&target_canon);
            } else {
                return Err(format!(
                    "unsupported special file symlink target {} in Lean stdlib at {}",
                    target_canon.display(),
                    path.display()
                ));
            }
        } else if ft.is_dir() {
            let dir_canon = fs::canonicalize(&path)
                .map_err(|e| format!("canonicalize Lean stdlib dir {}: {e}", path.display()))?;
            if !active_dirs.insert(dir_canon.clone()) {
                return Err(format!("Lean stdlib directory cycle at {}", path.display()));
            }
            walk_lean_stdlib_tree(&dir_canon, &rel_path, canon_prefix, active_dirs, out)?;
            active_dirs.remove(&dir_canon);
        } else if ft.is_file() {
            out.push((rel_path, path));
        } else {
            return Err(format!("unsupported special file in Lean stdlib: {}", path.display()));
        }
    }
    Ok(())
}

/// Compute a deterministic content-addressed `.olean` base cache key
/// (`"anneal-itree-lean-base-v3\0"`), binding:
/// 1. Canonical `lean_bin` path, `lean --version` stdout, and streaming 64 KiB
///    SHA-256 of the `lean_bin` executable bytes (plus `<lean_prefix>/bin/lean`
///    when distinct from `lean_bin`),
/// 2. Sorted top-level shared/static libraries (`.so`, `.so.`, `.dylib`,
///    `.dll`, `.a`) in `<lean_prefix>/lib` (skipping the `lean` stdlib
///    subdirectory itself),
/// 3. Complete deterministic recursive walk of `lean_stdlib`
///    (`<lean_prefix>/lib/lean`), rejecting symlinks escaping `<lean_prefix>`
///    and stream-hashing all regular files and intra-prefix symlink targets in
///    parallel across up to 8 worker threads using 64 KiB buffers, AND
/// 4. All `MIR_TOTAL_DAG` `.lean` source files.
pub fn compute_lean_cache_key(
    anneal_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
) -> Result<String, String> {
    let canon_lean_bin = fs::canonicalize(lean_bin)
        .map_err(|e| format!("canonicalize Lean binary {}: {e}", lean_bin.display()))?;
    if !lean_stdlib.is_dir() {
        return Err(format!("missing Lean stdlib directory at {}", lean_stdlib.display()));
    }
    let canon_stdlib = fs::canonicalize(lean_stdlib)
        .map_err(|e| format!("canonicalize Lean stdlib {}: {e}", lean_stdlib.display()))?;
    let canon_prefix = canon_stdlib
        .parent()
        .and_then(|p| {
            if p.file_name().and_then(|s| s.to_str()) == Some("lib") { p.parent() } else { Some(p) }
        })
        .unwrap_or(canon_stdlib.as_path())
        .to_path_buf();

    let lean_ver = query_lean_version_bytes(&canon_lean_bin)?;
    let (lean_bin_len, lean_bin_sha) = stream_sha256_file(&canon_lean_bin)?;

    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-lean-base-v3\0");
    update_len_prefixed_sha256(&mut hasher, canon_lean_bin.to_string_lossy().as_bytes());
    update_len_prefixed_sha256(&mut hasher, &lean_ver);
    hasher.update(lean_bin_len.to_le_bytes());
    hasher.update(lean_bin_sha);

    let prefix_bin = canon_prefix.join("bin/lean");
    if prefix_bin.is_file()
        && let Ok(canon_prefix_bin) = fs::canonicalize(&prefix_bin)
        && canon_prefix_bin != canon_lean_bin
    {
        let (p_len, p_sha) = stream_sha256_file(&canon_prefix_bin)?;
        hasher.update([1u8]);
        update_len_prefixed_sha256(&mut hasher, canon_prefix_bin.to_string_lossy().as_bytes());
        hasher.update(p_len.to_le_bytes());
        hasher.update(p_sha);
    } else {
        hasher.update([0u8]);
    }

    hasher.update(b"lean-prefix-lib\0");
    if let Some(parent_lib) = canon_stdlib.parent().filter(|p| p.is_dir()) {
        let mut top_libs: BTreeMap<String, PathBuf> = BTreeMap::new();
        for entry in fs::read_dir(parent_lib)
            .map_err(|e| format!("read_dir {}: {e}", parent_lib.display()))?
        {
            let entry = entry.map_err(|e| format!("iterate {}: {e}", parent_lib.display()))?;
            let path = entry.path();
            if path == canon_stdlib {
                continue;
            }
            let raw_name = entry.file_name();
            let name = raw_name
                .to_str()
                .ok_or_else(|| {
                    format!("non-UTF-8 library name in {}: {raw_name:?}", parent_lib.display())
                })?
                .to_string();
            if name == "lean" || !has_sysroot_lib_extension(&name, false) {
                continue;
            }
            let sym_meta = fs::symlink_metadata(&path)
                .map_err(|e| format!("inspect Lean lib {}: {e}", path.display()))?;
            let resolved = if sym_meta.file_type().is_symlink() {
                let target = fs::canonicalize(&path)
                    .map_err(|e| format!("resolve Lean lib symlink {}: {e}", path.display()))?;
                if !target.starts_with(&canon_prefix) {
                    return Err(format!(
                        "Lean lib symlink {} escapes Lean prefix {} -> {}",
                        path.display(),
                        canon_prefix.display(),
                        target.display()
                    ));
                }
                target
            } else {
                fs::canonicalize(&path)
                    .map_err(|e| format!("canonicalize Lean lib {}: {e}", path.display()))?
            };
            let meta = fs::metadata(&resolved)
                .map_err(|e| format!("stat Lean lib {}: {e}", resolved.display()))?;
            if meta.is_file() {
                top_libs.insert(name, resolved);
            }
        }
        let lib_entries: Vec<(String, PathBuf)> = top_libs.into_iter().collect();
        let hashed_libs = stream_hash_lean_entries(&lib_entries)?;
        hasher.update((hashed_libs.len() as u64).to_le_bytes());
        for (name, len, sha) in &hashed_libs {
            update_len_prefixed_sha256(&mut hasher, name.as_bytes());
            hasher.update(len.to_le_bytes());
            hasher.update(sha);
        }
    } else {
        hasher.update(0u64.to_le_bytes());
    }

    hasher.update(b"lean-stdlib-tree\0");
    let mut active_dirs = BTreeSet::from([canon_stdlib.clone()]);
    let mut stdlib_files = Vec::new();
    walk_lean_stdlib_tree(&canon_stdlib, "", &canon_prefix, &mut active_dirs, &mut stdlib_files)?;
    stdlib_files.sort_by(|a, b| a.0.cmp(&b.0));
    let hashed_stdlib = stream_hash_lean_entries(&stdlib_files)?;
    hasher.update((hashed_stdlib.len() as u64).to_le_bytes());
    for (rel, len, sha) in &hashed_stdlib {
        update_len_prefixed_sha256(&mut hasher, rel.as_bytes());
        hasher.update(len.to_le_bytes());
        hasher.update(sha);
    }

    hasher.update(b"mir-total-dag\0");
    hasher.update((MIR_TOTAL_DAG.len() as u64).to_le_bytes());
    for spec in MIR_TOTAL_DAG {
        let rel = spec.module.replace('.', "/") + ".lean";
        let path = anneal_root.join(spec.rel_tree).join(&rel);
        let bytes = fs::read(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        update_len_prefixed_sha256(&mut hasher, spec.module.as_bytes());
        update_len_prefixed_sha256(&mut hasher, &bytes);
    }
    let digest = hasher.finalize();
    let hex = sha256_hex(&digest);
    Ok(hex[..32].to_string())
}

fn compute_driver_cache_key(base_key: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-driver-v3\0");
    hasher.update(base_key.as_bytes());
    hasher.update(b"\0");
    hasher.update(ITREE_DRIVER_LEAN_SRC.as_bytes());
    let digest = hasher.finalize();
    let hex = sha256_hex(&digest);
    hex[..32].to_string()
}

const OLEAN_CACHE_MANIFEST_SCHEMA: u32 = 1;
const EXPECTED_CAPTURE_CACHE_FILES: &[&str] =
    &["capture_out/capture.json", "capture_out/Captured.lean", "olean_out/Captured.olean"];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct OleanArtifactDigest {
    byte_len: u64,
    sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct OleanCacheManifest {
    schema_version: u32,
    cache_key: String,
    artifacts: BTreeMap<String, OleanArtifactDigest>,
}

/// Return the normalized relative `.olean` paths required under the base Lean
/// cache directory for all [`MIR_TOTAL_DAG`] modules.
pub fn expected_base_olean_rel_paths() -> Vec<String> {
    MIR_TOTAL_DAG.iter().map(|spec| format!("{}.olean", spec.module.replace('.', "/"))).collect()
}

fn resolve_cache_rel_subpath(root: &Path, rel: &str) -> Option<PathBuf> {
    if rel.is_empty() || Path::new(rel).is_absolute() {
        return None;
    }
    let mut out = root.to_path_buf();
    for seg in rel.split('/') {
        if seg.is_empty() || seg == "." || seg == ".." {
            return None;
        }
        out.push(seg);
    }
    Some(out)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CapturedRefusedStamp {
    schema_version: u32,
    cache_key: String,
    reason: String,
}

fn write_captured_refused_stamp(
    ready_refused: &Path,
    cache_key: &str,
    reason: &str,
) -> Result<(), String> {
    if reason.trim().is_empty() {
        return Err("refusal reason cannot be empty when stamping `.captured-refused`".to_string());
    }
    let stamp = CapturedRefusedStamp {
        schema_version: OLEAN_CACHE_MANIFEST_SCHEMA,
        cache_key: cache_key.to_string(),
        reason: reason.to_string(),
    };
    let mut json = serde_json::to_string_pretty(&stamp)
        .map_err(|e| format!("serialize capture refusal stamp: {e}"))?;
    json.push('\n');
    atomic_write_file(ready_refused, json.as_bytes())
}

fn read_captured_refused_stamp(ready_refused: &Path, expected_key: &str) -> Option<String> {
    let sym = fs::symlink_metadata(ready_refused).ok()?;
    if !sym.file_type().is_file() {
        return None;
    }
    let raw = fs::read_to_string(ready_refused).ok()?;
    let parsed = serde_json::from_str::<CapturedRefusedStamp>(&raw).ok()?;
    if parsed.schema_version != OLEAN_CACHE_MANIFEST_SCHEMA
        || parsed.cache_key != expected_key
        || parsed.reason.trim().is_empty()
    {
        return None;
    }
    Some(parsed.reason)
}

fn reset_cache_dir(dir: &Path) -> Result<(), String> {
    if let Ok(meta) = fs::symlink_metadata(dir) {
        if meta.file_type().is_dir() {
            fs::remove_dir_all(dir)
                .map_err(|e| format!("wipe partial cache {}: {e}", dir.display()))?;
        } else if let Err(file_err) = fs::remove_file(dir) {
            // Windows directory symlinks and NTFS junctions reject
            // `remove_file` and must be removed with `remove_dir`.
            fs::remove_dir(dir).map_err(|dir_err| {
                format!(
                    "remove stale cache entry {}: {file_err}; fallback remove_dir: {dir_err}",
                    dir.display()
                )
            })?;
        }
    }
    fs::create_dir_all(dir).map_err(|e| format!("mkdir {}: {e}", dir.display()))
}

/// Hash every regular non-empty file in `expected_rel_paths` under `cache_dir`
/// and atomically write a versioned manifest into `ready_path`.
pub fn write_cached_artifact_manifest(
    cache_dir: &Path,
    ready_path: &Path,
    cache_key: &str,
    expected_rel_paths: &[&str],
) -> Result<(), String> {
    let mut artifacts = BTreeMap::new();
    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
    for &rel in expected_rel_paths {
        let path = resolve_cache_rel_subpath(cache_dir, rel)
            .ok_or_else(|| format!("invalid cache artifact relative path: {rel:?}"))?;
        let sym_meta = fs::symlink_metadata(&path)
            .map_err(|e| format!("stat cache artifact {}: {e}", path.display()))?;
        if !sym_meta.file_type().is_file() {
            return Err(format!("cache artifact {} is not a regular file", path.display()));
        }
        let (byte_len, sha) = stream_sha256_file_with_buf(&path, &mut buf)?;
        if byte_len == 0 {
            return Err(format!("cache artifact {} is empty", path.display()));
        }
        artifacts
            .insert(rel.to_string(), OleanArtifactDigest { byte_len, sha256: sha256_hex(&sha) });
    }
    let manifest = OleanCacheManifest {
        schema_version: OLEAN_CACHE_MANIFEST_SCHEMA,
        cache_key: cache_key.to_string(),
        artifacts,
    };
    let mut json = serde_json::to_string_pretty(&manifest)
        .map_err(|e| format!("serialize cache manifest: {e}"))?;
    json.push('\n');
    atomic_write_file(ready_path, json.as_bytes())
}

/// Validate `ready_path` as a JSON manifest bound to `expected_key` and verify
/// every regular non-empty artifact in `expected_rel_paths` exists under
/// `cache_dir` with matching byte length and SHA-256 digest.
pub fn validate_cached_artifact_manifest(
    cache_dir: &Path,
    ready_path: &Path,
    expected_key: &str,
    expected_rel_paths: &[&str],
) -> bool {
    let Ok(sym_ready) = fs::symlink_metadata(ready_path) else {
        return false;
    };
    if !sym_ready.file_type().is_file() {
        return false;
    }
    let Ok(raw) = fs::read_to_string(ready_path) else {
        return false;
    };
    let Ok(manifest) = serde_json::from_str::<OleanCacheManifest>(&raw) else {
        return false;
    };
    if manifest.schema_version != OLEAN_CACHE_MANIFEST_SCHEMA || manifest.cache_key != expected_key
    {
        return false;
    }
    let expected_set: BTreeSet<&str> = expected_rel_paths.iter().copied().collect();
    if manifest.artifacts.len() != expected_set.len()
        || !expected_set.iter().all(|rel| manifest.artifacts.contains_key(*rel))
    {
        return false;
    }
    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
    for (rel, expected_digest) in &manifest.artifacts {
        if expected_digest.byte_len == 0 {
            return false;
        }
        let Some(path) = resolve_cache_rel_subpath(cache_dir, rel) else {
            return false;
        };
        let Ok(sym_meta) = fs::symlink_metadata(&path) else {
            return false;
        };
        if !sym_meta.file_type().is_file() {
            return false;
        }
        let Ok((byte_len, sha)) = stream_sha256_file_with_buf(&path, &mut buf) else {
            return false;
        };
        if byte_len != expected_digest.byte_len || sha256_hex(&sha) != expected_digest.sha256 {
            return false;
        }
    }
    true
}

/// Build or validate the cached base `MIR_TOTAL_DAG` `.olean` tree and
/// `ITreeDriver.olean` directory under `cache_root`, wiping and rebuilding any
/// directory whose ready manifest or expected `.olean` digests fail validation.
pub fn ensure_lean_and_driver_oleans(
    anneal_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    cache_root: &Path,
) -> Result<(Vec<PathBuf>, String), String> {
    let base_key = compute_lean_cache_key(anneal_root, lean_bin, lean_stdlib)?;
    let driver_key = compute_driver_cache_key(&base_key);
    fs::create_dir_all(cache_root)
        .map_err(|e| format!("create cache dir {}: {e}", cache_root.display()))?;
    let out_dir = cache_root.join(format!("lean-itree-base-{base_key}"));
    let lock_path = cache_root.join(format!("lean-itree-base-{base_key}.lock"));
    let lock_file = File::options()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
        .map_err(|e| format!("open Lean olean lock {}: {e}", lock_path.display()))?;
    lock_file
        .lock()
        .map_err(|e| format!("acquire Lean olean lock {}: {e}", lock_path.display()))?;

    let ready = out_dir.join(".anneal-itree-base-ready");
    let expected_base = expected_base_olean_rel_paths();
    let expected_base_refs: Vec<&str> = expected_base.iter().map(String::as_str).collect();
    let base_search_paths = vec![out_dir.clone(), lean_stdlib.to_path_buf()];
    let lean_path = env::join_paths(&base_search_paths)
        .map_err(|e| format!("join LEAN_PATH: {e}"))?
        .to_string_lossy()
        .into_owned();

    if !validate_cached_artifact_manifest(&out_dir, &ready, &base_key, &expected_base_refs) {
        reset_cache_dir(&out_dir)?;

        let known_modules: BTreeSet<&'static str> =
            MIR_TOTAL_DAG.iter().map(|s| s.module).collect();
        let mut effective_deps: BTreeMap<&'static str, BTreeSet<String>> = BTreeMap::new();
        for spec in MIR_TOTAL_DAG {
            let mut deps_set: BTreeSet<String> =
                spec.deps.iter().map(|d| (*d).to_string()).collect();
            let rel = spec.module.replace('.', "/") + ".lean";
            let src_path = anneal_root.join(spec.rel_tree).join(rel);
            let src_text = fs::read_to_string(&src_path)
                .map_err(|e| format!("read {}: {e}", src_path.display()))?;
            for imp in parse_lean_header_imports(&src_text) {
                if known_modules.contains(imp.as_str()) && imp != spec.module {
                    deps_set.insert(imp);
                }
            }
            effective_deps.insert(spec.module, deps_set);
        }

        let mut built: BTreeSet<&'static str> = BTreeSet::new();
        let mut remaining: Vec<&LeanDagSpec> = MIR_TOTAL_DAG.iter().collect();
        let max_workers = thread::available_parallelism().map(|n| n.get().clamp(1, 4)).unwrap_or(1);

        while !remaining.is_empty() {
            let mut ready_batch = Vec::new();
            let mut next_remaining = Vec::new();
            for spec in remaining {
                let deps_ready = effective_deps
                    .get(spec.module)
                    .is_some_and(|ds| ds.iter().all(|d| built.contains(d.as_str())));
                if deps_ready {
                    ready_batch.push(spec);
                } else {
                    next_remaining.push(spec);
                }
            }
            if ready_batch.is_empty() {
                return Err("cycle in Lean build DAG".to_string());
            }

            for chunk in ready_batch.chunks(max_workers) {
                let out_dir_ref = &out_dir;
                let results: Vec<Result<&'static str, String>> = thread::scope(|scope| {
                    let mut handles = Vec::with_capacity(chunk.len());
                    for spec in chunk {
                        let lp = &lean_path;
                        handles.push(scope.spawn(move || {
                            let rel = spec.module.replace('.', "/");
                            let tree_root = anneal_root.join(spec.rel_tree);
                            let src = tree_root.join(format!("{rel}.lean"));
                            let dst = out_dir_ref.join(format!("{rel}.olean"));
                            if let Some(parent) = dst.parent() {
                                fs::create_dir_all(parent)
                                    .map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
                            }
                            let inv = build_lean_invocation(
                                lean_bin,
                                lp,
                                &[
                                    OsString::from("-R"),
                                    tree_root.as_os_str().to_os_string(),
                                    OsString::from("-o"),
                                    dst.as_os_str().to_os_string(),
                                    src.as_os_str().to_os_string(),
                                ],
                            );
                            let res =
                                run_supervised_cmd(&inv, &tree_root, LEAN_COMPILE_TIMEOUT_SECS)?;
                            match res.termination {
                                Termination::Exited(s) if s.success() => Ok(spec.module),
                                other => Err(format!(
                                    "compile {} failed ({}):\nstdout:\n{}\nstderr:\n{}",
                                    spec.module,
                                    other.describe(),
                                    String::from_utf8_lossy(&res.stdout),
                                    String::from_utf8_lossy(&res.stderr)
                                )),
                            }
                        }));
                    }
                    handles
                        .into_iter()
                        .map(|h| {
                            h.join().unwrap_or_else(|_| Err("Lean worker panicked".to_string()))
                        })
                        .collect()
                });
                for r in results {
                    built.insert(r?);
                }
            }
            remaining = next_remaining;
        }
        write_cached_artifact_manifest(&out_dir, &ready, &base_key, &expected_base_refs)?;
    }
    drop(lock_file);

    let driver_dir = cache_root.join(format!("lean-itree-driver-{driver_key}"));
    let driver_lock_path = cache_root.join(format!("lean-itree-driver-{driver_key}.lock"));
    let driver_lock = File::options()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(&driver_lock_path)
        .map_err(|e| format!("open driver olean lock {}: {e}", driver_lock_path.display()))?;
    driver_lock
        .lock()
        .map_err(|e| format!("acquire driver olean lock {}: {e}", driver_lock_path.display()))?;
    let driver_ready = driver_dir.join(".anneal-itree-driver-ready");
    let expected_driver = &["ITreeDriver.olean"];
    if !validate_cached_artifact_manifest(&driver_dir, &driver_ready, &driver_key, expected_driver)
    {
        reset_cache_dir(&driver_dir)?;
        let driver_src_dir = tempfile::Builder::new()
            .prefix("anneal-itree-driver-src-")
            .tempdir()
            .map_err(|e| format!("create driver src tempdir: {e}"))?;
        let driver_src = driver_src_dir.path().join("ITreeDriver.lean");
        fs::write(&driver_src, ITREE_DRIVER_LEAN_SRC)
            .map_err(|e| format!("write ITreeDriver.lean: {e}"))?;
        let driver_olean = driver_dir.join("ITreeDriver.olean");
        let inv = build_lean_invocation(
            lean_bin,
            &lean_path,
            &[
                OsString::from("-R"),
                driver_src_dir.path().as_os_str().to_os_string(),
                OsString::from("-o"),
                driver_olean.as_os_str().to_os_string(),
                driver_src.as_os_str().to_os_string(),
            ],
        );
        let res = run_supervised_cmd(&inv, driver_src_dir.path(), LEAN_COMPILE_TIMEOUT_SECS)?;
        match res.termination {
            Termination::Exited(s) if s.success() => {}
            other => {
                return Err(format!(
                    "compile ITreeDriver.lean failed ({}):\nstdout:\n{}\nstderr:\n{}",
                    other.describe(),
                    String::from_utf8_lossy(&res.stdout),
                    String::from_utf8_lossy(&res.stderr)
                ));
            }
        }
        write_cached_artifact_manifest(&driver_dir, &driver_ready, &driver_key, expected_driver)?;
    }
    drop(driver_lock);

    Ok((vec![driver_dir, out_dir, lean_stdlib.to_path_buf()], driver_key))
}

fn apply_lean_env_with_env(
    mut inv: Invocation,
    lean_bin: &Path,
    lean_path: &str,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    if !lean_path.is_empty() {
        inv = inv.env("LEAN_PATH", lean_path);
    }
    if let Some(dylib_env) = get_env(DYLIB_PATH_ENV_VAR).filter(|v| !v.is_empty()) {
        inv = inv.env(DYLIB_PATH_ENV_VAR, dylib_env);
    } else if let Some(lib_dir) =
        lean_bin.parent().and_then(Path::parent).map(|p| p.join("lib/lean"))
        && lib_dir.is_dir()
    {
        inv = inv.env(DYLIB_PATH_ENV_VAR, lib_dir);
    }
    forward_standard_tool_env_with_env(inv, fallback_temp, get_env)
}

/// Build the clean-environment `lean` compiler/evaluator [`Invocation`],
/// preserving platform temporary/profile/toolchain variables and falling back
/// to `fallback_temp` if no temp variable is set.
pub fn build_lean_invocation_with_env(
    lean_bin: &Path,
    lean_path: &str,
    extra_args: &[OsString],
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let mut inv = Invocation::new(lean_bin, LEAN_COMPILE_FLAGS);
    for a in extra_args {
        inv = inv.arg(a);
    }
    apply_lean_env_with_env(inv, lean_bin, lean_path, fallback_temp, get_env)
}

fn build_lean_invocation(lean_bin: &Path, lean_path: &str, extra_args: &[OsString]) -> Invocation {
    build_lean_invocation_with_env(lean_bin, lean_path, extra_args, None, |k| env::var_os(k))
}

/// Build the clean-environment `anneal-rustc-capture` [`Invocation`],
/// preserving host temporary/profile/Windows OS variables and falling back to
/// `fallback_temp` if no temp variable is set.
#[allow(clippy::too_many_arguments)]
pub fn build_capture_invocation_with_env(
    capture_bin: &Path,
    src_path: &Path,
    crate_name: &str,
    host_target: &str,
    out_dir: &Path,
    rust_sysroot: &Path,
    dylib_search_path: &OsStr,
    child_path: &OsStr,
    select_fns: &[String],
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let mut cap_inv = Invocation::new(capture_bin, &["capture"])
        .arg("--crate-root")
        .arg(src_path)
        .arg("--crate-name")
        .arg(crate_name)
        .arg("--target")
        .arg(host_target)
        .arg("--out-dir")
        .arg(out_dir)
        .arg("--sysroot")
        .arg(rust_sysroot)
        .arg("--source-file")
        .arg(src_path)
        .env(DYLIB_PATH_ENV_VAR, dylib_search_path)
        .env("PATH", child_path);
    for sel in select_fns {
        cap_inv = cap_inv.arg("--select").arg(sel);
    }
    forward_platform_temp_and_profile_env_with_env(cap_inv, fallback_temp, get_env)
}

/// Build the clean-environment Cargo invocation used to compile
/// `anneal-rustc-capture`, preserving host temporary/profile/toolchain
/// variables alongside pinned `rustup` toolchain metadata.
#[allow(clippy::too_many_arguments)]
pub fn build_capture_cargo_invocation_with_env(
    cargo_bin: &Path,
    manifest_path: &Path,
    target_dir: &Path,
    rustc_bin: &Path,
    rust_sysroot: &Path,
    dylib_search_path: &OsStr,
    child_path: &OsStr,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let mut inv = Invocation::new(cargo_bin, &["build", "--offline", "--locked"])
        .arg("--manifest-path")
        .arg(manifest_path)
        .arg("-p")
        .arg("anneal-rustc-capture")
        .arg("--bin")
        .arg("anneal-rustc-capture")
        .arg("--target-dir")
        .arg(target_dir)
        .env("RUSTC", rustc_bin)
        .env(DYLIB_PATH_ENV_VAR, dylib_search_path)
        .env("PATH", child_path);
    if is_rustup_proxy_executable(cargo_bin) {
        let (rustup_home, rustup_toolchain) =
            resolve_rustup_env_for_sysroot_with_env(rust_sysroot, &get_env);
        if let Some(rh) = rustup_home {
            inv = inv.env("RUSTUP_HOME", rh);
        }
        if let Some(rt) = rustup_toolchain {
            inv = inv.env("RUSTUP_TOOLCHAIN", rt);
        }
    }
    forward_standard_tool_env_with_env(inv, fallback_temp, get_env)
}

fn parse_lean_header_imports(src_text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in src_text.lines() {
        let trimmed = line.split("--").next().unwrap_or("").trim();
        if trimmed.is_empty() {
            continue;
        }
        let tokens: Vec<&str> = trimmed.split_whitespace().collect();
        if let Some(imp_pos) = tokens.iter().position(|t| *t == "import")
            && tokens[..imp_pos].iter().all(|t| matches!(*t, "public" | "private" | "meta"))
        {
            for &tok in &tokens[imp_pos + 1..] {
                if tok == "all" {
                    continue;
                }
                if tok.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '\'')) {
                    out.push(tok.to_string());
                }
            }
        }
    }
    out
}

fn run_supervised_cmd(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
) -> Result<ProcessOutcome, String> {
    run_supervised_with_prefix("anneal-itree-lean-sup-", inv, Some(work_dir), timeout_secs)
}
