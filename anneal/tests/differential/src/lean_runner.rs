// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Candidate-oracle runner driving `anneal-rustc-capture` and Lean 4
//! `Anneal.MirTotal.StepCore` / `ExecTotal` over captured MIR programs, plus
//! Lean kernel `WP` theorems (`wpProg_of_evalMirFuelTotal` /
//! `wpFaultProg_of_evalMirFuelTotal`) for budget-fitting single-block pass and
//! UB cases (`<= 9` MIR statements, no 128-bit scalars, `<= 16` WP fuel).

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::{OsStr, OsString},
    fmt::Write as _,
    fs::{self, File},
    io::Read as _,
    path::{Component, Path, PathBuf},
    thread,
    time::Duration,
};

use anneal_testkit::{Invocation, ProcessOutcome, ProcessSupervisor, Termination, ToolchainEnv};
use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::{
    corpus::LitmusCase,
    verdict::{Expectation, IntKind, MirValue, ObservedOutcome, OrderingKind},
};

const LEAN_CASE_PREFIX: &str = "ANNEAL_LEAN_CASE:";
const LEAN_TRACE_PREFIX: &str = "ANNEAL_LEAN_TRACE:";
const WP_TRACE_STRIDE: usize = 3;
const CAPTURE_TIMEOUT_SECS: u64 = 120;
const LEAN_PROBE_TIMEOUT_SECS: u64 = 30;
const LEAN_COMPILE_TIMEOUT_SECS: u64 = 180;
const LEAN_EVAL_TIMEOUT_SECS: u64 = 180;
const MAX_TIMEOUT_OVERRIDE_SECS: u64 = 3600;

pub(crate) const LEAN_COMPILE_FLAGS: &[&str] =
    &["-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false"];

const CANONICAL_PREBUILT_FLAGS: &[&str] =
    &["-j1", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false"];

const LEAN_ARTIFACT_EXTS: &[&str] = &["olean", "olean.server", "olean.private", "ir", "ir.sig"];
const LEAN_SYSROOT_PACKAGES: &[&str] = &["Init", "Std", "Lean"];

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
            "Trusted.MirSemantics.Ops",
            "Trusted.MirSemantics.Enum",
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

/// Prepared Lean 4 and `anneal-rustc-capture` session with `.olean` cache.
#[derive(Clone, Debug)]
pub struct LeanSession {
    pub anneal_root: PathBuf,
    pub capture_bin: PathBuf,
    pub rust_sysroot: PathBuf,
    pub lean_bin: PathBuf,
    pub olean_paths: Vec<PathBuf>,
    pub prebuilt_overlay: String,
    pub ld_library_path: String,
    pub child_path: OsString,
}

/// Captured artifact pair and per-case metadata for one source module group.
#[derive(Clone, Debug)]
pub struct CapturedModule {
    pub capture_dir: PathBuf,
    pub capture_json: PathBuf,
    pub captured_lean: PathBuf,
    pub olean_dir: PathBuf,
    pub body_ids_by_fn: BTreeMap<String, usize>,
    pub kernel_whnf_eligible_by_fn: BTreeMap<String, bool>,
    pub kernel_whnf_ub_sysroot_by_fn: BTreeMap<String, bool>,
    pub move_reinit_fns: BTreeSet<String>,
}

const MAX_KERNEL_WHNF_STMTS: usize = 9;

/// Lean probe evaluation result for a single case alongside whether a Lean
/// kernel `WP` proof theorem verified it during `Probe.lean` elaboration.
#[derive(Clone, Debug)]
pub struct LeanCaseResult {
    pub outcome: ObservedOutcome,
    pub kernel_checked: bool,
}

#[derive(Deserialize)]
struct CaptureStatusOk {
    status: String,
    capture: PathBuf,
    lean: PathBuf,
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
pub(crate) struct CaptureBlock {
    pub(crate) statements: Vec<serde_json::Value>,
    #[serde(default)]
    pub(crate) terminator: serde_json::Value,
}

fn is_single_block_kernel_whnf(body: &CaptureBody) -> bool {
    body.blocks.len() == 1 && body.blocks[0].statements.len() <= MAX_KERNEL_WHNF_STMTS
}

/// True for a 2-block `bb0 -> bb1` body whose `bb0` terminator is a returning
/// Profile v1 `sysroot_call` targeting a bounded-statement `ret` `bb1` (for
/// example `StorageDead` cleanup before returning). Faulting
/// `unchecked_{add,sub,mul}` UB proofs evaluate within Lean's default
/// `200_000` `whnf` heartbeats; passing `sysroot_call` paths remain
/// `#eval`-checked.
fn is_sysroot_ub_kernel_whnf(body: &CaptureBody) -> bool {
    if body.blocks.len() != 2 || body.blocks[0].statements.len() > MAX_KERNEL_WHNF_STMTS {
        return false;
    }
    let t0 = &body.blocks[0].terminator;
    let t1 = &body.blocks[1].terminator;
    t0.get("kind").and_then(serde_json::Value::as_str) == Some("sysroot_call")
        && t0.get("target").and_then(serde_json::Value::as_u64) == Some(1)
        && body.blocks[1].statements.len() <= MAX_KERNEL_WHNF_STMTS
        && t1.get("kind").and_then(serde_json::Value::as_str) == Some("ret")
}

#[derive(Deserialize)]
pub(crate) struct CaptureBody {
    pub(crate) identity: String,
    pub(crate) arg_count: usize,
    pub(crate) local_tys: Vec<serde_json::Value>,
    pub(crate) blocks: Vec<CaptureBlock>,
}

fn is_non_zst_captured_ty(ty: &serde_json::Value) -> bool {
    match ty.get("kind").and_then(serde_json::Value::as_str) {
        Some("bool" | "char" | "ordering" | "int" | "overflow_pair") => true,
        Some("enum") => {
            ty.get("tag_repr").and_then(|tr| tr.get("kind")).and_then(serde_json::Value::as_str)
                == Some("scalar")
        }
        _ => false,
    }
}

fn rvalue_reads_local(rvalue: &serde_json::Value, target_local: u64) -> bool {
    let op_has_local = |op: &serde_json::Value| -> bool {
        match op.get("kind").and_then(serde_json::Value::as_str) {
            Some("copy" | "move") => {
                op.get("local").and_then(serde_json::Value::as_u64) == Some(target_local)
            }
            Some("copy_place" | "move_place") => {
                op.get("place").and_then(|p| p.get("local")).and_then(serde_json::Value::as_u64)
                    == Some(target_local)
            }
            _ => false,
        }
    };
    match rvalue.get("kind").and_then(serde_json::Value::as_str) {
        Some("use" | "use_retag" | "unary" | "cast") => {
            rvalue.get("operand").is_some_and(op_has_local)
        }
        Some("binary") => {
            rvalue.get("left").is_some_and(op_has_local)
                || rvalue.get("right").is_some_and(op_has_local)
        }
        Some("discriminant") => {
            rvalue
                .get("place")
                .and_then(|p| p.get("local"))
                .or_else(|| rvalue.get("local"))
                .and_then(serde_json::Value::as_u64)
                == Some(target_local)
        }
        _ => false,
    }
}

/// Check whether `body` initializes a non-argument, non-ZST local, moves out of
/// it via `Rvalue::Use(Operand::Move)` (deinitializing it), reinitializes that
/// same local, and subsequently reads or moves from it again.
pub(crate) fn body_exercises_move_then_reinit(body: &CaptureBody) -> bool {
    'slot_loop: for (slot_idx, ty) in body.local_tys.iter().enumerate().skip(body.arg_count + 1) {
        if !is_non_zst_captured_ty(ty) {
            continue;
        }
        let slot = slot_idx as u64;
        // 0 = uninitialized, 1 = initialized, 2 = moved out, 3 = reinitialized.
        let mut stage = 0u8;
        for block in &body.blocks {
            for stmt in &block.statements {
                if stmt.get("kind").and_then(serde_json::Value::as_str) != Some("assign") {
                    continue;
                }
                let Some(dst) = stmt.get("local").and_then(serde_json::Value::as_u64) else {
                    continue;
                };
                let Some(val) = stmt.get("value") else {
                    continue;
                };
                match stage {
                    0 => {
                        if dst == slot {
                            stage = 1;
                        }
                    }
                    1 => {
                        let is_use_move = dst != slot
                            && val.get("kind").and_then(serde_json::Value::as_str) == Some("use")
                            && val
                                .get("operand")
                                .and_then(|op| op.get("kind"))
                                .and_then(serde_json::Value::as_str)
                                == Some("move")
                            && val
                                .get("operand")
                                .and_then(|op| op.get("local"))
                                .and_then(serde_json::Value::as_u64)
                                == Some(slot);
                        if is_use_move {
                            stage = 2;
                        }
                    }
                    2 => {
                        if rvalue_reads_local(val, slot) {
                            continue 'slot_loop;
                        }
                        if dst == slot {
                            stage = 3;
                        }
                    }
                    3 => {
                        if rvalue_reads_local(val, slot) {
                            return true;
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
    false
}

pub(crate) fn effective_timeout_secs(default_secs: u64) -> Result<u64, String> {
    effective_timeout_secs_from(env::var_os("ANNEAL_DIFF_TIMEOUT_SECS").as_deref(), default_secs)
}

fn effective_timeout_secs_from(
    raw_override: Option<&OsStr>,
    default_secs: u64,
) -> Result<u64, String> {
    let Some(raw) = raw_override.filter(|v| !v.is_empty()) else {
        return Ok(default_secs);
    };
    let text = raw
        .to_str()
        .ok_or_else(|| format!("ANNEAL_DIFF_TIMEOUT_SECS is not valid UTF-8: {raw:?}"))?;
    let parsed: u64 = text
        .trim()
        .parse()
        .map_err(|e| format!("invalid ANNEAL_DIFF_TIMEOUT_SECS {text:?}: {e}"))?;
    if !(1..=MAX_TIMEOUT_OVERRIDE_SECS).contains(&parsed) {
        return Err(format!(
            "ANNEAL_DIFF_TIMEOUT_SECS={parsed} out of valid range 1..={MAX_TIMEOUT_OVERRIDE_SECS}"
        ));
    }
    Ok(parsed)
}

pub(crate) fn sha256_bytes_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(hex, "{b:02x}");
    }
    hex
}

pub(crate) fn sha256_file_hex(path: &Path) -> Result<String, String> {
    let mut file =
        File::open(path).map_err(|e| format!("open {} for sha256: {e}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 64 * 1024];
    loop {
        let n =
            file.read(&mut buf).map_err(|e| format!("read {} for sha256: {e}", path.display()))?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(hex, "{b:02x}");
    }
    Ok(hex)
}

/// Reject symlinks and non-regular files BEFORE `fs::canonicalize` runs.
pub(crate) fn validate_and_canonicalize_capture_bin(raw: &Path) -> Result<PathBuf, String> {
    let meta = fs::symlink_metadata(raw)
        .map_err(|e| format!("stat capture binary {}: {e}", raw.display()))?;
    if meta.file_type().is_symlink() {
        return Err(format!("capture binary must not be a symlink: {}", raw.display()));
    }
    if !meta.is_file() {
        return Err(format!("capture binary path is not a regular file: {}", raw.display()));
    }
    fs::canonicalize(raw).map_err(|e| format!("canonicalize capture bin {}: {e}", raw.display()))
}

pub(crate) fn run_supervised_cmd(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
    context: &str,
) -> Result<ProcessOutcome, String> {
    let tmp =
        tempfile::tempdir().map_err(|e| format!("create supervisor temp dir ({context}): {e}"))?;
    let canon_root = fs::canonicalize(tmp.path())
        .map_err(|e| format!("canonicalize supervisor temp dir ({context}): {e}"))?;
    let canon_work = fs::canonicalize(work_dir)
        .map_err(|e| format!("canonicalize work dir ({context}): {e}"))?;
    let supervisor = ProcessSupervisor::new(Duration::from_secs(timeout_secs))?;
    supervisor.run(inv, &canon_work, &canon_root.join("log"), &canon_root)
}

fn default_child_path() -> OsString {
    env::var_os("PATH").unwrap_or_else(|| OsString::from("/usr/bin:/bin"))
}

pub(crate) fn apply_lean_tool_env(mut inv: Invocation, lean_bin: &Path) -> Invocation {
    if let Some(ld) = env::var_os("LD_LIBRARY_PATH").filter(|v| !v.is_empty()) {
        inv = inv.env("LD_LIBRARY_PATH", ld);
    } else if let Some(lib_dir) =
        lean_bin.parent().and_then(Path::parent).map(|p| p.join("lib/lean"))
        && lib_dir.is_dir()
    {
        inv = inv.env("LD_LIBRARY_PATH", lib_dir);
    }
    inv = inv.env("PATH", default_child_path());
    if let Some(tmp) = env::var_os("TMPDIR").filter(|v| !v.is_empty()) {
        inv = inv.env("TMPDIR", tmp);
    }
    inv
}

impl LeanSession {
    /// Resolve `anneal-rustc-capture` and Lean 4.34.1, and ensure compiled
    /// `.olean` artifacts for `Anneal.MirTotal.{Ops,StepCore,ExecTotal}` exist
    /// in `cache_root`.
    pub fn prepare(
        anneal_root: &Path,
        tools: &ToolchainEnv,
        cache_root: &Path,
    ) -> Result<Self, String> {
        let rust_sysroot = fs::canonicalize(&tools.sysroot)
            .map_err(|e| format!("canonicalize rust sysroot: {e}"))?;
        let lean_bin =
            fs::canonicalize(&tools.lean).map_err(|e| format!("canonicalize lean bin: {e}"))?;
        let ld_library_path = join_library_path(&rust_sysroot.join("lib"));
        let capture_bin = resolve_explicit_capture_bin(tools)?;

        let lean_prefix = query_lean_prefix(&lean_bin)?;
        let lean_stdlib = lean_prefix.join("lib/lean");
        let prebuilt_dir = env::var_os("ANNEAL_TEST_INSTALL_ROOT")
            .filter(|v| !v.is_empty())
            .map(|r| PathBuf::from(r).join("share/anneal/prebuilt"));

        let (olean_paths, prebuilt_overlay) = ensure_lean_dag_oleans(
            anneal_root,
            &lean_bin,
            &lean_stdlib,
            prebuilt_dir.as_deref(),
            cache_root,
        )?;

        Ok(Self {
            anneal_root: anneal_root.to_path_buf(),
            capture_bin,
            rust_sysroot,
            lean_bin,
            olean_paths,
            prebuilt_overlay,
            ld_library_path,
            child_path: default_child_path(),
        })
    }

    /// Build `LEAN_PATH` including `extra_dir` first, then DAG `.olean` dirs.
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

    /// Capture one fixture crate group, compile `Captured.lean`, evaluate all
    /// `cases` against `Anneal.MirTotal.StepCore`, and run kernel `WP`
    /// adequacy theorems on budget-fitting single-block cases and 2-block
    /// single-`sysroot_call` UB cases (`<= 9` statements in `bb0`, no 128-bit
    /// scalars, `<= 16` WP fuel).
    pub fn capture_and_evaluate_group(
        &self,
        group_dir: &Path,
        crate_name: &str,
        source_abs: &Path,
        cases: &[&LitmusCase],
    ) -> Result<(CapturedModule, BTreeMap<String, LeanCaseResult>), String> {
        let mut selected_fns: Vec<String> = Vec::new();
        for c in cases {
            if !selected_fns.contains(&c.function) {
                selected_fns.push(c.function.clone());
            }
        }

        let out_dir = group_dir.join("capture_out");
        let mut cap_inv = Invocation::new(&self.capture_bin, &["capture"])
            .arg("--crate-root")
            .arg(source_abs)
            .arg("--crate-name")
            .arg(crate_name)
            .arg("--target")
            .arg("x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&out_dir)
            .arg("--sysroot")
            .arg(&self.rust_sysroot)
            .arg("--source-file")
            .arg(source_abs)
            .env("LD_LIBRARY_PATH", &self.ld_library_path)
            .env("PATH", &self.child_path);
        if let Some(tmp) = env::var_os("TMPDIR").filter(|v| !v.is_empty()) {
            cap_inv = cap_inv.env("TMPDIR", tmp);
        }
        for f in &selected_fns {
            cap_inv = cap_inv.arg("--select").arg(f);
        }

        let cap_out = run_supervised_cmd(
            &cap_inv,
            group_dir,
            effective_timeout_secs(CAPTURE_TIMEOUT_SECS)?,
            &format!("capture {crate_name}"),
        )?;
        let cap_stdout = String::from_utf8_lossy(&cap_out.stdout);
        let cap_stderr = String::from_utf8_lossy(&cap_out.stderr);
        match cap_out.termination {
            Termination::Exited(s) if s.success() => {}
            other => {
                return Err(format!(
                    "`anneal-rustc-capture capture` failed for {crate_name} ({}):\nstdout: {cap_stdout}\nstderr: {cap_stderr}",
                    other.describe()
                ));
            }
        }

        let status_ok: CaptureStatusOk = serde_json::from_str(cap_stdout.trim()).map_err(|e| {
            format!("parse capture output JSON for {crate_name}: {e}; raw={cap_stdout:?}")
        })?;
        if status_ok.status != "captured" {
            return Err(format!(
                "unexpected capture status {:?} for {crate_name}",
                status_ok.status
            ));
        }

        let manifest_raw = fs::read_to_string(&status_ok.capture)
            .map_err(|e| format!("read {}: {e}", status_ok.capture.display()))?;
        let manifest: CaptureManifest = serde_json::from_str(&manifest_raw)
            .map_err(|e| format!("parse {}: {e}", status_ok.capture.display()))?;

        let mut body_ids_by_fn = BTreeMap::new();
        let mut kernel_whnf_eligible_by_fn = BTreeMap::new();
        let mut kernel_whnf_ub_sysroot_by_fn = BTreeMap::new();
        let mut move_reinit_fns = BTreeSet::new();
        for f in &selected_fns {
            let (idx, body) =
                select_captured_body(&manifest.program.bodies, f, &status_ok.capture)?;
            body_ids_by_fn.insert(f.clone(), idx);
            kernel_whnf_eligible_by_fn.insert(f.clone(), is_single_block_kernel_whnf(body));
            kernel_whnf_ub_sysroot_by_fn.insert(f.clone(), is_sysroot_ub_kernel_whnf(body));
            if body_exercises_move_then_reinit(body) {
                move_reinit_fns.insert(f.clone());
            }
        }

        let mod_olean_dir = group_dir.join("olean_out");
        fs::create_dir_all(&mod_olean_dir)
            .map_err(|e| format!("create {}: {e}", mod_olean_dir.display()))?;
        let lean_path = self.lean_path_with(Some(&mod_olean_dir))?;

        let compile_inv = apply_lean_tool_env(
            Invocation::new(&self.lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-R")
                .arg(&out_dir)
                .arg("-o")
                .arg(mod_olean_dir.join("Captured.olean"))
                .arg(&status_ok.lean)
                .env("LEAN_PATH", &lean_path),
            &self.lean_bin,
        );
        let compile_cap = run_supervised_cmd(
            &compile_inv,
            group_dir,
            effective_timeout_secs(LEAN_COMPILE_TIMEOUT_SECS)?,
            &format!("compile Captured.lean ({crate_name})"),
        )?;
        match compile_cap.termination {
            Termination::Exited(s) if s.success() => {}
            other => {
                return Err(format!(
                    "compiling {} failed ({}):\nstdout:\n{}\nstderr:\n{}",
                    status_ok.lean.display(),
                    other.describe(),
                    String::from_utf8_lossy(&compile_cap.stdout),
                    String::from_utf8_lossy(&compile_cap.stderr)
                ));
            }
        }

        let captured = CapturedModule {
            capture_dir: out_dir,
            capture_json: status_ok.capture,
            captured_lean: status_ok.lean,
            olean_dir: mod_olean_dir,
            body_ids_by_fn,
            kernel_whnf_eligible_by_fn,
            kernel_whnf_ub_sysroot_by_fn,
            move_reinit_fns,
        };

        let results =
            self.evaluate_captured_group(group_dir, crate_name, &lean_path, &captured, cases)?;
        Ok((captured, results))
    }

    /// Evaluate `#eval` `StepCore` outcomes for `cases` first and then verify
    /// kernel `Anneal.MirWp` `rfl` theorems in a separate `WpProbe.lean` pass
    /// over agreeing single-block cases so semantic regressions still produce
    /// structured verdicts and JSON telemetry rather than aborting elaboration.
    pub fn evaluate_captured_group(
        &self,
        group_dir: &Path,
        crate_name: &str,
        lean_path: &str,
        captured: &CapturedModule,
        cases: &[&LitmusCase],
    ) -> Result<BTreeMap<String, LeanCaseResult>, String> {
        let probe_src = generate_lean_eval_probe(captured, cases)?;
        let probe_path = group_dir.join("Probe.lean");
        fs::write(&probe_path, &probe_src)
            .map_err(|e| format!("write {}: {e}", probe_path.display()))?;

        let eval_inv = apply_lean_tool_env(
            Invocation::new(&self.lean_bin, LEAN_COMPILE_FLAGS)
                .arg(&probe_path)
                .env("LEAN_PATH", lean_path),
            &self.lean_bin,
        );
        let eval_out = run_supervised_cmd(
            &eval_inv,
            group_dir,
            effective_timeout_secs(LEAN_EVAL_TIMEOUT_SECS)?,
            &format!("eval Probe.lean ({crate_name})"),
        )?;
        let stdout = String::from_utf8_lossy(&eval_out.stdout);
        let stderr = String::from_utf8_lossy(&eval_out.stderr);
        match eval_out.termination {
            Termination::Exited(s) if s.success() => {}
            other => {
                return Err(format!(
                    "Lean probe failed for {crate_name} ({}):\nstdout:\n{stdout}\nstderr:\n{stderr}",
                    other.describe()
                ));
            }
        }

        let mut raw_outcomes = parse_lean_probe_output(&stdout, cases)?;
        let wp_traces = parse_lean_wp_traces(&stdout)?;
        let wp_candidates = select_wp_kernel_candidates(captured, cases, &raw_outcomes);
        let mut kernel_checked_ids = BTreeSet::new();
        if !wp_candidates.is_empty() {
            let mut probe_seq = 0usize;
            self.verify_kernel_wp_slice(
                group_dir,
                crate_name,
                lean_path,
                captured,
                &wp_candidates,
                &wp_traces,
                &mut probe_seq,
                &mut raw_outcomes,
                &mut kernel_checked_ids,
            )?;
        }

        let mut results = BTreeMap::new();
        for (id, outcome) in raw_outcomes {
            let kernel_checked = kernel_checked_ids.contains(&id);
            results.insert(id, LeanCaseResult { outcome, kernel_checked });
        }
        Ok(results)
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_kernel_wp_slice(
        &self,
        group_dir: &Path,
        crate_name: &str,
        lean_path: &str,
        captured: &CapturedModule,
        candidates: &[&LitmusCase],
        wp_traces: &BTreeMap<String, WpStepTrace>,
        probe_seq: &mut usize,
        raw_outcomes: &mut BTreeMap<String, ObservedOutcome>,
        kernel_checked_ids: &mut BTreeSet<String>,
    ) -> Result<(), String> {
        let wp_src = generate_lean_wp_probe_with_traces(captured, candidates, wp_traces)?;
        let seq = *probe_seq;
        *probe_seq += 1;
        let wp_path = group_dir.join(format!("WpProbe_{seq}.lean"));
        fs::write(&wp_path, &wp_src).map_err(|e| format!("write {}: {e}", wp_path.display()))?;

        let wp_inv = apply_lean_tool_env(
            Invocation::new(&self.lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-DwarningAsError=true")
                .arg(&wp_path)
                .env("LEAN_PATH", lean_path),
            &self.lean_bin,
        );
        let wp_out = run_supervised_cmd(
            &wp_inv,
            group_dir,
            effective_timeout_secs(LEAN_EVAL_TIMEOUT_SECS)?,
            &format!("check WpProbe_{seq}.lean ({crate_name})"),
        )?;
        match wp_out.termination {
            Termination::Exited(s) if s.success() => {
                for case in candidates {
                    kernel_checked_ids.insert(case.id.clone());
                }
                Ok(())
            }
            Termination::Exited(_) => {
                if candidates.len() == 1 {
                    let case = candidates[0];
                    let diag = String::from_utf8_lossy(&wp_out.stdout);
                    let err_diag = String::from_utf8_lossy(&wp_out.stderr);
                    let detail_msg =
                        if !err_diag.trim().is_empty() { err_diag.trim() } else { diag.trim() };
                    raw_outcomes.insert(
                        case.id.clone(),
                        ObservedOutcome::ToolError {
                            detail: format!(
                                "Lean kernel WP rfl theorem disagreed with #eval for {:?}: {}",
                                case.id, detail_msg
                            ),
                        },
                    );
                    return Ok(());
                }
                let mid = candidates.len() / 2;
                self.verify_kernel_wp_slice(
                    group_dir,
                    crate_name,
                    lean_path,
                    captured,
                    &candidates[..mid],
                    wp_traces,
                    probe_seq,
                    raw_outcomes,
                    kernel_checked_ids,
                )?;
                self.verify_kernel_wp_slice(
                    group_dir,
                    crate_name,
                    lean_path,
                    captured,
                    &candidates[mid..],
                    wp_traces,
                    probe_seq,
                    raw_outcomes,
                    kernel_checked_ids,
                )
            }
            other => Err(format!(
                "Lean kernel WP probe failed globally for {crate_name} ({}):\nstdout:\n{}\nstderr:\n{}",
                other.describe(),
                String::from_utf8_lossy(&wp_out.stdout),
                String::from_utf8_lossy(&wp_out.stderr)
            )),
        }
    }
}

fn select_captured_body<'a>(
    bodies: &'a [CaptureBody],
    fn_name: &str,
    capture_path: &Path,
) -> Result<(usize, &'a CaptureBody), String> {
    let prefixed = format!("rust-path-v1::{fn_name}");
    let exact: Vec<(usize, &'a CaptureBody)> = bodies
        .iter()
        .enumerate()
        .filter(|(_, b)| b.identity == fn_name || b.identity == prefixed)
        .collect();
    match exact.len() {
        1 => return Ok(exact[0]),
        n if n > 1 => {
            let ids: Vec<&str> = exact.iter().map(|(_, b)| b.identity.as_str()).collect();
            return Err(format!(
                "ambiguous exact captured body match for function {fn_name:?} in {}: {ids:?}",
                capture_path.display()
            ));
        }
        _ => {}
    }

    let suffix = format!("::{fn_name}");
    let suffix_matches: Vec<(usize, &'a CaptureBody)> =
        bodies.iter().enumerate().filter(|(_, b)| b.identity.ends_with(&suffix)).collect();
    match suffix_matches.len() {
        1 => Ok(suffix_matches[0]),
        0 => Err(format!(
            "captured program {} missing body for function {fn_name:?}",
            capture_path.display()
        )),
        _ => {
            let ids: Vec<&str> = suffix_matches.iter().map(|(_, b)| b.identity.as_str()).collect();
            Err(format!(
                "ambiguous suffix captured body match for function {fn_name:?} in {}: {ids:?}",
                capture_path.display()
            ))
        }
    }
}

fn resolve_explicit_capture_bin(tools: &ToolchainEnv) -> Result<PathBuf, String> {
    let Some(p) = &tools.capture else {
        return Err("missing `anneal-rustc-capture` binary: pass `--capture-bin` or set `ANNEAL_CAPTURE`, `ANNEAL_CLI`, or `ANNEAL_TEST_INSTALL_ROOT`".to_owned());
    };
    if !p.is_file() {
        return Err(format!("capture binary path is not a regular file: {}", p.display()));
    }
    Ok(p.clone())
}

fn query_lean_prefix(lean_bin: &Path) -> Result<PathBuf, String> {
    let inv = apply_lean_tool_env(Invocation::new(lean_bin, &["--print-prefix"]), lean_bin);
    let work_dir = lean_bin.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised_cmd(
        &inv,
        work_dir,
        effective_timeout_secs(LEAN_PROBE_TIMEOUT_SECS)?,
        "lean --print-prefix",
    )?;
    match out.termination {
        Termination::Exited(s) if s.success() => {}
        other => {
            return Err(format!(
                "`lean --print-prefix` failed ({}): {}",
                other.describe(),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }
    let text = String::from_utf8(out.stdout)
        .map_err(|e| format!("invalid UTF-8 from `lean --print-prefix`: {e}"))?;
    fs::canonicalize(text.trim()).map_err(|e| format!("canonicalize lean prefix: {e}"))
}

const PREBUILT_SCHEMA_VERSION: u32 = 2;

#[derive(Deserialize)]
struct PrebuiltManifest {
    schema_version: u32,
    entries: Vec<PrebuiltEntry>,
}

#[derive(Deserialize)]
struct PrebuiltEntry {
    kind: String,
    module: String,
    lean_sha256: String,
    #[serde(default)]
    sysroot_manifest_sha256: String,
    source_sha256: String,
    #[serde(default)]
    is_module: Option<bool>,
    #[serde(default)]
    flags: Vec<String>,
    #[serde(default)]
    imports: Vec<PrebuiltImport>,
    #[serde(default)]
    parts: Vec<PrebuiltPart>,
}

#[derive(Deserialize)]
struct PrebuiltImport {
    module: String,
    #[serde(default)]
    is_exported: Option<bool>,
    #[serde(default)]
    import_all: Option<bool>,
    #[serde(default)]
    is_meta: Option<bool>,
    #[serde(default)]
    part_sha256s: Vec<String>,
    #[serde(default)]
    transitive_sha256: String,
}

#[derive(Deserialize)]
struct PrebuiltPart {
    suffix: String,
    path: String,
    sha256: String,
}

fn feed_len_str(h: &mut Sha256, value: &str) {
    h.update((value.len() as u64).to_le_bytes());
    h.update(value.as_bytes());
}

fn compute_transitive_module_sha256(
    part_shas: &[String],
    imports: &[PrebuiltImport],
) -> Result<String, String> {
    let mut sorted_edges: Vec<(&str, bool, bool, bool, &str)> = Vec::with_capacity(imports.len());
    for imp in imports {
        let is_exported = imp
            .is_exported
            .ok_or_else(|| format!("missing is_exported on import {}", imp.module))?;
        let import_all =
            imp.import_all.ok_or_else(|| format!("missing import_all on import {}", imp.module))?;
        let is_meta =
            imp.is_meta.ok_or_else(|| format!("missing is_meta on import {}", imp.module))?;
        sorted_edges.push((
            imp.module.as_str(),
            is_exported,
            import_all,
            is_meta,
            imp.transitive_sha256.as_str(),
        ));
    }
    sorted_edges
        .sort_by(|a, b| a.0.cmp(b.0).then(a.1.cmp(&b.1)).then(a.2.cmp(&b.2)).then(a.3.cmp(&b.3)));

    let mut h = Sha256::new();
    h.update(b"anneal-olean-transitive-v1\0");
    h.update((part_shas.len() as u64).to_le_bytes());
    for sha in part_shas {
        feed_len_str(&mut h, &sha.to_ascii_lowercase());
    }
    h.update((sorted_edges.len() as u64).to_le_bytes());
    for (module, is_exported, import_all, is_meta, transitive_sha) in sorted_edges {
        feed_len_str(&mut h, module);
        h.update([u8::from(is_exported), u8::from(import_all), u8::from(is_meta)]);
        feed_len_str(&mut h, &transitive_sha.to_ascii_lowercase());
    }
    let digest = h.finalize();
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(hex, "{b:02x}");
    }
    Ok(hex)
}

fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

fn source_starts_with_module_keyword(raw: &[u8]) -> bool {
    let mut i = 0usize;
    let n = raw.len();
    while i < n {
        if raw[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if raw[i..].starts_with(b"--") {
            match raw[i..].iter().position(|&b| b == b'\n') {
                Some(pos) => i += pos + 1,
                None => i = n,
            }
            continue;
        }
        if raw[i..].starts_with(b"/-") {
            i += 2;
            let mut depth = 1usize;
            while i < n && depth > 0 {
                if raw[i..].starts_with(b"/-") {
                    depth += 1;
                    i += 2;
                } else if raw[i..].starts_with(b"-/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        break;
    }
    let Some(after) = raw.get(i..).and_then(|s| s.strip_prefix(b"module")) else {
        return false;
    };
    after.first().is_none_or(|b| b.is_ascii_whitespace())
        || after.starts_with(b"--")
        || after.starts_with(b"/-")
}

struct VerifiedPrebuiltOverlay {
    manifest_sha256: Option<String>,
    modules: BTreeMap<String, Vec<(String, PathBuf)>>,
    fallback_label: String,
}

fn resolve_safe_prebuilt_part(canon_pb_dir: &Path, rel_raw: &str) -> Result<PathBuf, String> {
    if rel_raw.is_empty() {
        return Err("empty prebuilt part path".to_owned());
    }
    let rel = Path::new(rel_raw);
    let mut cur = canon_pb_dir.to_path_buf();
    let mut saw_component = false;
    for comp in rel.components() {
        match comp {
            Component::Normal(seg) => {
                saw_component = true;
                cur.push(seg);
                let meta = fs::symlink_metadata(&cur)
                    .map_err(|e| format!("stat prebuilt part {}: {e}", cur.display()))?;
                if meta.file_type().is_symlink() {
                    return Err(format!("symlink forbidden in prebuilt path: {}", cur.display()));
                }
            }
            Component::ParentDir
            | Component::CurDir
            | Component::RootDir
            | Component::Prefix(_) => {
                return Err(format!("disallowed path component in prebuilt path {rel_raw:?}"));
            }
        }
    }
    if !saw_component {
        return Err("prebuilt part path has no segments".to_owned());
    }
    let canon = fs::canonicalize(&cur)
        .map_err(|e| format!("canonicalize prebuilt part {}: {e}", cur.display()))?;
    if !canon.starts_with(canon_pb_dir) || !canon.is_file() {
        return Err(format!("prebuilt part escapes root or is not a file: {}", canon.display()));
    }
    Ok(canon)
}

/// Compute the canonical SHA-256 manifest digest over
/// `<lean_stdlib>/{Init,Std,Lean}*` `.olean`, `.olean.server`,
/// `.olean.private`, `.ir`, and `.ir.sig` artifacts (matching `cargo-anneal`'s
/// `compute_sysroot_manifest_sha256` and `ci/prebuild_bundled_oleans.py`'s
/// `SYSROOT_MANIFEST_PARTS` framing `<rel>:<sha256>\n` so prebuilt `.olean`
/// overlays and local `#eval` DAG cache keys are bound to all active Lean
/// sysroot artifacts).
pub(crate) fn compute_lean_sysroot_manifest_sha256(lean_stdlib: &Path) -> Result<String, String> {
    let stdlib_meta = fs::symlink_metadata(lean_stdlib)
        .map_err(|e| format!("stat Lean stdlib {}: {e}", lean_stdlib.display()))?;
    if stdlib_meta.file_type().is_symlink() || !stdlib_meta.is_dir() {
        return Err(format!(
            "Lean stdlib must be a non-symlink directory: {}",
            lean_stdlib.display()
        ));
    }

    fn walk_pkg_dir(
        lib_dir: &Path,
        cur_dir: &Path,
        out: &mut Vec<(String, PathBuf)>,
    ) -> Result<(), String> {
        let mut dir_entries: Vec<_> = fs::read_dir(cur_dir)
            .map_err(|e| format!("read Lean sysroot dir {}: {e}", cur_dir.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("iterate Lean sysroot dir {}: {e}", cur_dir.display()))?;
        dir_entries.sort_by_key(|e| e.file_name());
        for entry in dir_entries {
            let path = entry.path();
            let ft = entry
                .file_type()
                .map_err(|e| format!("inspect Lean sysroot entry {}: {e}", path.display()))?;
            if ft.is_symlink() {
                return Err(format!("symlink forbidden in Lean sysroot: {}", path.display()));
            }
            if ft.is_dir() {
                walk_pkg_dir(lib_dir, &path, out)?;
                continue;
            }
            if !ft.is_file() {
                return Err(format!(
                    "unexpected non-regular entry in Lean sysroot: {}",
                    path.display()
                ));
            }
            let rel = path
                .strip_prefix(lib_dir)
                .map_err(|e| format!("strip Lean sysroot prefix {}: {e}", path.display()))?;
            let mut segs = Vec::new();
            for comp in rel.components() {
                let Component::Normal(os) = comp else {
                    return Err(format!(
                        "invalid relative component in Lean sysroot: {}",
                        path.display()
                    ));
                };
                let s = os
                    .to_str()
                    .ok_or_else(|| format!("non-UTF-8 path in Lean sysroot: {}", path.display()))?;
                segs.push(s);
            }
            let rel_str = segs.join("/");
            if LEAN_ARTIFACT_EXTS.iter().any(|ext| rel_str.ends_with(&format!(".{ext}"))) {
                out.push((rel_str, path));
            }
        }
        Ok(())
    }

    let mut files_to_hash: Vec<(String, PathBuf)> = Vec::new();
    for pkg in LEAN_SYSROOT_PACKAGES {
        for ext in LEAN_ARTIFACT_EXTS {
            let rel = format!("{pkg}.{ext}");
            let path = lean_stdlib.join(&rel);
            match fs::symlink_metadata(&path) {
                Ok(meta) => {
                    if meta.file_type().is_symlink() {
                        return Err(format!(
                            "symlink forbidden in Lean sysroot: {}",
                            path.display()
                        ));
                    }
                    if !meta.is_file() {
                        return Err(format!(
                            "unexpected non-regular entry in Lean sysroot: {}",
                            path.display()
                        ));
                    }
                    files_to_hash.push((rel, path));
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => {
                    return Err(format!("stat Lean sysroot {}: {e}", path.display()));
                }
            }
        }
        let pkg_dir = lean_stdlib.join(pkg);
        match fs::symlink_metadata(&pkg_dir) {
            Ok(meta) => {
                if meta.file_type().is_symlink() || !meta.is_dir() {
                    return Err(format!(
                        "Lean sysroot package dir must be a real directory: {}",
                        pkg_dir.display()
                    ));
                }
                walk_pkg_dir(lean_stdlib, &pkg_dir, &mut files_to_hash)?;
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => {
                return Err(format!("stat Lean sysroot dir {}: {e}", pkg_dir.display()));
            }
        }
    }

    let workers = thread::available_parallelism()
        .map(|n| n.get().clamp(1, 4))
        .unwrap_or(1)
        .min(files_to_hash.len().max(1));
    let mut entries: BTreeMap<String, String> = BTreeMap::new();
    if files_to_hash.len() <= 1 || workers <= 1 {
        for (rel, path) in files_to_hash {
            entries.insert(rel, sha256_file_hex(&path)?);
        }
    } else {
        let chunk_size = files_to_hash.len().div_ceil(workers);
        let chunk_results: Vec<Result<Vec<(String, String)>, String>> = thread::scope(|scope| {
            let handles: Vec<_> = files_to_hash
                .chunks(chunk_size)
                .map(|chunk| {
                    scope.spawn(move || {
                        let mut local = Vec::with_capacity(chunk.len());
                        for (rel, path) in chunk {
                            local.push((rel.clone(), sha256_file_hex(path)?));
                        }
                        Ok(local)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| {
                    h.join().unwrap_or_else(|_| Err("sysroot hash worker panicked".to_owned()))
                })
                .collect()
        });
        for res in chunk_results {
            for (rel, sha) in res? {
                entries.insert(rel, sha);
            }
        }
    }

    let mut manifest = String::new();
    for (rel, sha) in &entries {
        manifest.push_str(rel);
        manifest.push(':');
        manifest.push_str(sha);
        manifest.push('\n');
    }
    Ok(sha256_bytes_hex(manifest.as_bytes()))
}

fn inspect_prebuilt_overlay(
    prebuilt_dir: Option<&Path>,
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    active_sysroot_sha: &str,
) -> Result<VerifiedPrebuiltOverlay, String> {
    let Some(pb_dir) = prebuilt_dir else {
        return Ok(VerifiedPrebuiltOverlay {
            manifest_sha256: None,
            modules: BTreeMap::new(),
            fallback_label: "none".to_owned(),
        });
    };

    let pb_meta = match fs::symlink_metadata(pb_dir) {
        Ok(m) => m,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Ok(VerifiedPrebuiltOverlay {
                manifest_sha256: None,
                modules: BTreeMap::new(),
                fallback_label: "skipped:missing_prebuilt_dir".to_owned(),
            });
        }
        Err(_) => {
            return Ok(VerifiedPrebuiltOverlay {
                manifest_sha256: None,
                modules: BTreeMap::new(),
                fallback_label: "skipped:unreadable_prebuilt_dir".to_owned(),
            });
        }
    };
    if pb_meta.file_type().is_symlink() || !pb_meta.is_dir() {
        return Ok(VerifiedPrebuiltOverlay {
            manifest_sha256: None,
            modules: BTreeMap::new(),
            fallback_label: "skipped:invalid_prebuilt_dir".to_owned(),
        });
    }
    let canon_pb_dir = fs::canonicalize(pb_dir)
        .map_err(|e| format!("canonicalize prebuilt dir {}: {e}", pb_dir.display()))?;

    let manifest_path = canon_pb_dir.join("manifest.json");
    let m_meta = match fs::symlink_metadata(&manifest_path) {
        Ok(m) => m,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Ok(VerifiedPrebuiltOverlay {
                manifest_sha256: None,
                modules: BTreeMap::new(),
                fallback_label: "skipped:missing_manifest".to_owned(),
            });
        }
        Err(_) => {
            return Ok(VerifiedPrebuiltOverlay {
                manifest_sha256: None,
                modules: BTreeMap::new(),
                fallback_label: "skipped:unreadable_manifest".to_owned(),
            });
        }
    };
    if m_meta.file_type().is_symlink() || !m_meta.is_file() {
        return Ok(VerifiedPrebuiltOverlay {
            manifest_sha256: None,
            modules: BTreeMap::new(),
            fallback_label: "skipped:invalid_manifest_path".to_owned(),
        });
    }

    let manifest_bytes = fs::read(&manifest_path)
        .map_err(|e| format!("read prebuilt manifest {}: {e}", manifest_path.display()))?;
    let manifest_sha256 = sha256_bytes_hex(&manifest_bytes);
    let manifest: PrebuiltManifest = match serde_json::from_slice(&manifest_bytes) {
        Ok(m) => m,
        Err(_) => {
            return Ok(VerifiedPrebuiltOverlay {
                manifest_sha256: None,
                modules: BTreeMap::new(),
                fallback_label: "skipped:invalid_manifest_json".to_owned(),
            });
        }
    };
    if manifest.schema_version != PREBUILT_SCHEMA_VERSION {
        return Ok(VerifiedPrebuiltOverlay {
            manifest_sha256: None,
            modules: BTreeMap::new(),
            fallback_label: "skipped:unsupported_manifest_schema".to_owned(),
        });
    }

    let lean_sha = sha256_file_hex(lean_bin)?;
    let mut entries: BTreeMap<String, PrebuiltEntry> = BTreeMap::new();
    let mut duplicates: BTreeSet<String> = BTreeSet::new();
    for entry in manifest.entries {
        if entry.kind != "module" {
            continue;
        }
        if entries.contains_key(&entry.module) {
            duplicates.insert(entry.module.clone());
        } else {
            entries.insert(entry.module.clone(), entry);
        }
    }

    let dag_modules: BTreeSet<&'static str> = dag.iter().map(|s| s.module).collect();
    let mut verified_part_shas: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut verified_transitive_shas: BTreeMap<String, String> = BTreeMap::new();
    let mut verified_modules: BTreeMap<String, Vec<(String, PathBuf)>> = BTreeMap::new();
    for spec in dag {
        if duplicates.contains(spec.module) {
            continue;
        }
        if !spec.deps.iter().all(|d| verified_modules.contains_key(*d)) {
            continue;
        }
        let Some(entry) = entries.get(spec.module) else {
            continue;
        };
        if !entry.lean_sha256.eq_ignore_ascii_case(&lean_sha) {
            continue;
        }
        if !is_sha256_hex(&entry.sysroot_manifest_sha256)
            || !entry.sysroot_manifest_sha256.eq_ignore_ascii_case(active_sysroot_sha)
        {
            continue;
        }
        if !entry.flags.iter().map(String::as_str).eq(CANONICAL_PREBUILT_FLAGS.iter().copied()) {
            continue;
        }

        let rel = spec.module.replace('.', "/");
        let src_path = base_root.join(spec.rel_tree).join(format!("{rel}.lean"));
        let src_bytes = fs::read(&src_path)
            .map_err(|e| format!("read Lean source {}: {e}", src_path.display()))?;
        let src_sha = sha256_bytes_hex(&src_bytes);
        if !entry.source_sha256.eq_ignore_ascii_case(&src_sha) {
            continue;
        }
        if entry.is_module != Some(source_starts_with_module_keyword(&src_bytes)) {
            continue;
        }

        let mut seen_dag_imports: BTreeSet<&str> = BTreeSet::new();
        let mut imports_valid = true;
        for imp in &entry.imports {
            if imp.is_exported.is_none()
                || imp.import_all.is_none()
                || imp.is_meta.is_none()
                || imp.part_sha256s.is_empty()
                || !imp.part_sha256s.iter().all(|s| is_sha256_hex(s))
                || !is_sha256_hex(&imp.transitive_sha256)
            {
                imports_valid = false;
                break;
            }
            if dag_modules.contains(imp.module.as_str()) {
                let (Some(dep_shas), Some(dep_transitive)) = (
                    verified_part_shas.get(&imp.module),
                    verified_transitive_shas.get(&imp.module),
                ) else {
                    imports_valid = false;
                    break;
                };
                if imp.part_sha256s.len() != dep_shas.len()
                    || !imp
                        .part_sha256s
                        .iter()
                        .zip(dep_shas)
                        .all(|(a, b)| a.eq_ignore_ascii_case(b))
                    || !imp.transitive_sha256.eq_ignore_ascii_case(dep_transitive)
                {
                    imports_valid = false;
                    break;
                }
                seen_dag_imports.insert(imp.module.as_str());
            }
        }
        let expected_dag_deps: BTreeSet<&str> = spec.deps.iter().copied().collect();
        if !imports_valid || seen_dag_imports != expected_dag_deps {
            continue;
        }

        if entry.parts.is_empty() {
            continue;
        }
        let mut seen_suffixes = BTreeSet::new();
        let mut verified_parts = Vec::with_capacity(entry.parts.len());
        let mut this_part_shas = Vec::with_capacity(entry.parts.len());
        let mut all_parts_valid = true;
        for part in &entry.parts {
            if !LEAN_ARTIFACT_EXTS.contains(&part.suffix.as_str())
                || !seen_suffixes.insert(part.suffix.as_str())
            {
                all_parts_valid = false;
                break;
            }
            let Ok(part_abs) = resolve_safe_prebuilt_part(&canon_pb_dir, &part.path) else {
                all_parts_valid = false;
                break;
            };
            let Ok(actual_part_sha) = sha256_file_hex(&part_abs) else {
                all_parts_valid = false;
                break;
            };
            if !actual_part_sha.eq_ignore_ascii_case(&part.sha256) {
                all_parts_valid = false;
                break;
            }
            verified_parts.push((part.suffix.clone(), part_abs));
            this_part_shas.push(actual_part_sha);
        }
        if !all_parts_valid || entry.parts[0].suffix != "olean" {
            continue;
        }
        let Ok(this_transitive_sha) =
            compute_transitive_module_sha256(&this_part_shas, &entry.imports)
        else {
            continue;
        };
        verified_part_shas.insert(spec.module.to_owned(), this_part_shas);
        verified_transitive_shas.insert(spec.module.to_owned(), this_transitive_sha);
        verified_modules.insert(spec.module.to_owned(), verified_parts);
    }

    let fallback_label = if verified_modules.is_empty() {
        "skipped:digest_mismatch".to_owned()
    } else {
        format!("staged:{}/{}", verified_modules.len(), dag.len())
    };
    let effective_manifest_sha =
        if verified_modules.is_empty() { None } else { Some(manifest_sha256) };
    Ok(VerifiedPrebuiltOverlay {
        manifest_sha256: effective_manifest_sha,
        modules: verified_modules,
        fallback_label,
    })
}

fn compute_lean_cache_key(
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    active_sysroot_sha: &str,
    overlay: &VerifiedPrebuiltOverlay,
) -> Result<String, String> {
    let inv = apply_lean_tool_env(Invocation::new(lean_bin, &["--version"]), lean_bin);
    let work_dir = lean_bin.parent().unwrap_or_else(|| Path::new("/"));
    let ver = run_supervised_cmd(
        &inv,
        work_dir,
        effective_timeout_secs(LEAN_PROBE_TIMEOUT_SECS)?,
        "lean --version",
    )?;
    match ver.termination {
        Termination::Exited(s) if s.success() && !ver.stdout.is_empty() => {}
        other => {
            return Err(format!(
                "`{} --version` failed ({}): {}",
                lean_bin.display(),
                other.describe(),
                String::from_utf8_lossy(&ver.stderr)
            ));
        }
    }

    let lean_bin_sha = sha256_file_hex(lean_bin)?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-diff-lean-dag-v6\0");
    hasher.update(lean_bin_sha.as_bytes());
    hasher.update(b"\0");
    hasher.update(active_sysroot_sha.as_bytes());
    hasher.update(b"\0");
    hasher.update((ver.stdout.len() as u64).to_le_bytes());
    hasher.update(&ver.stdout);
    for flag in LEAN_COMPILE_FLAGS {
        hasher.update(flag.as_bytes());
        hasher.update(b"\0");
    }
    if let Some(msha) = &overlay.manifest_sha256 {
        hasher.update(b"prebuilt-manifest\0");
        hasher.update(msha.as_bytes());
        for module_name in overlay.modules.keys() {
            hasher.update(b"\0");
            hasher.update(module_name.as_bytes());
        }
        hasher.update(b"\0");
    } else {
        hasher.update(b"no-prebuilt-overlay\0");
    }
    for spec in dag {
        let rel = spec.module.replace('.', "/") + ".lean";
        let path = base_root.join(spec.rel_tree).join(&rel);
        let bytes =
            fs::read(&path).map_err(|e| format!("read Lean source {}: {e}", path.display()))?;
        hasher.update(spec.module.as_bytes());
        hasher.update(b"\0");
        hasher.update(if module_needs_eval_ir(spec.module) {
            b"eval-ir:1\0"
        } else {
            b"eval-ir:0\0"
        });
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(32);
    for b in &digest[..16] {
        let _ = write!(hex, "{b:02x}");
    }
    Ok(hex)
}

fn ensure_lean_dag_oleans(
    anneal_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    prebuilt_dir: Option<&Path>,
    cache_root: &Path,
) -> Result<(Vec<PathBuf>, String), String> {
    let active_sysroot_sha = compute_lean_sysroot_manifest_sha256(lean_stdlib)?;
    let overlay = inspect_prebuilt_overlay(
        prebuilt_dir,
        MIR_TOTAL_DAG,
        anneal_root,
        lean_bin,
        &active_sysroot_sha,
    )?;
    let key = compute_lean_cache_key(
        MIR_TOTAL_DAG,
        anneal_root,
        lean_bin,
        &active_sysroot_sha,
        &overlay,
    )?;
    fs::create_dir_all(cache_root)
        .map_err(|e| format!("create cache root {}: {e}", cache_root.display()))?;

    let dir_prefix =
        if overlay.modules.is_empty() { "lean-mirtotal-full" } else { "lean-mirtotal-overlay" };
    let out_dir = cache_root.join(format!("{dir_prefix}-{key}"));
    let lock_path = cache_root.join(format!("{dir_prefix}-{key}.lock"));
    ensure_dag_with_verified_overlay(
        MIR_TOTAL_DAG,
        anneal_root,
        lean_bin,
        lean_stdlib,
        &overlay,
        &out_dir,
        &lock_path,
    )
}

fn stage_prebuilt_module_artifacts(
    verified_parts: &[(String, PathBuf)],
    out_dir: &Path,
    rel: &str,
) -> Result<(), String> {
    for (ext, src_art) in verified_parts {
        let dst_art = out_dir.join(format!("{rel}.{ext}"));
        if let Some(parent) = dst_art.parent() {
            fs::create_dir_all(parent).map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
        }
        if fs::symlink_metadata(&dst_art).is_ok() {
            fs::remove_file(&dst_art)
                .map_err(|e| format!("remove stale {}: {e}", dst_art.display()))?;
        }
        fs::copy(src_art, &dst_art).map_err(|e| {
            format!("stage prebuilt artifact {} -> {}: {e}", src_art.display(), dst_art.display())
        })?;
    }
    Ok(())
}

/// Return `true` when `#eval` probes may execute computable definitions or
/// default-field initializers (`Query.callerMem._default`,
/// `State.callerMem._default`, etc.) from `module`, requiring `.ir` and
/// `.ir.sig` companion files alongside staged prebuilt `.olean` artifacts
/// (`ci/prebuild_bundled_oleans.py` strips `.ir` and `.ir.sig` because
/// `cargo-anneal verify` only runs kernel checking).
fn module_needs_eval_ir(module: &str) -> bool {
    module == "Trusted.MirAst"
        || module.starts_with("Trusted.MirAst.")
        || module == "Trusted.MirModel"
        || module == "Trusted.MirSemantics.State"
        || module == "Anneal.MirTotal"
        || module.starts_with("Anneal.MirTotal.")
        || module.starts_with("TestRoot.")
}

fn synthesize_missing_eval_ir(
    dag: &[LeanDagSpec],
    staged: &BTreeSet<&'static str>,
    base_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    out_dir: &Path,
    compile_timeout: u64,
) -> Result<(), String> {
    let missing: Vec<&LeanDagSpec> = dag
        .iter()
        .filter(|spec| {
            if !staged.contains(spec.module) || !module_needs_eval_ir(spec.module) {
                return false;
            }
            let rel = spec.module.replace('.', "/");
            !out_dir.join(format!("{rel}.ir")).is_file()
                || !out_dir.join(format!("{rel}.ir.sig")).is_file()
        })
        .collect();
    if missing.is_empty() {
        return Ok(());
    }

    let ir_scratch = out_dir.join(".ir_synth");
    if ir_scratch.exists() {
        fs::remove_dir_all(&ir_scratch)
            .map_err(|e| format!("clean {}: {e}", ir_scratch.display()))?;
    }
    fs::create_dir_all(&ir_scratch).map_err(|e| format!("create {}: {e}", ir_scratch.display()))?;
    for mod_name in staged {
        let rel = mod_name.replace('.', "/");
        for ext in LEAN_ARTIFACT_EXTS {
            let src_art = out_dir.join(format!("{rel}.{ext}"));
            if src_art.is_file() {
                let dst_art = ir_scratch.join(format!("{rel}.{ext}"));
                if let Some(parent) = dst_art.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
                }
                fs::copy(&src_art, &dst_art).map_err(|e| {
                    format!(
                        "seed staged {} -> {} for IR synthesis: {e}",
                        src_art.display(),
                        dst_art.display()
                    )
                })?;
            }
        }
    }
    let ir_lean_path = env::join_paths([ir_scratch.clone(), lean_stdlib.to_path_buf()])
        .map_err(|e| format!("join IR synthesis LEAN_PATH: {e}"))?
        .to_string_lossy()
        .into_owned();

    let synth_res = (|| -> Result<(), String> {
        for spec in missing {
            let rel = spec.module.replace('.', "/");
            let tree_root = base_root.join(spec.rel_tree);
            let src = tree_root.join(format!("{rel}.lean"));
            let scratch_olean = ir_scratch.join(format!("{rel}.olean"));
            if let Some(parent) = scratch_olean.parent() {
                fs::create_dir_all(parent)
                    .map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
            }
            let inv = apply_lean_tool_env(
                Invocation::new(lean_bin, LEAN_COMPILE_FLAGS)
                    .arg("-R")
                    .arg(&tree_root)
                    .arg("-o")
                    .arg(&scratch_olean)
                    .arg(&src)
                    .env("LEAN_PATH", &ir_lean_path),
                lean_bin,
            );
            let res = run_supervised_cmd(
                &inv,
                &tree_root,
                compile_timeout,
                &format!("lean synthesize IR {}", spec.module),
            )?;
            match res.termination {
                Termination::Exited(s) if s.success() => {}
                other => {
                    return Err(format!(
                        "synthesize IR for {} failed ({}):\nstdout:\n{}\nstderr:\n{}",
                        spec.module,
                        other.describe(),
                        String::from_utf8_lossy(&res.stdout),
                        String::from_utf8_lossy(&res.stderr)
                    ));
                }
            }
            for ext in ["ir", "ir.sig"] {
                let src_ir = ir_scratch.join(format!("{rel}.{ext}"));
                if !src_ir.is_file() {
                    return Err(format!(
                        "synthesized IR artifact missing for {}: {}",
                        spec.module,
                        src_ir.display()
                    ));
                }
                let dst_ir = out_dir.join(format!("{rel}.{ext}"));
                fs::copy(&src_ir, &dst_ir).map_err(|e| {
                    format!("copy synthesized {} -> {}: {e}", src_ir.display(), dst_ir.display())
                })?;
            }
        }
        Ok(())
    })();

    let cleanup_res = fs::remove_dir_all(&ir_scratch)
        .map_err(|e| format!("remove {}: {e}", ir_scratch.display()));
    synth_res?;
    cleanup_res?;
    Ok(())
}

#[cfg_attr(not(test), allow(dead_code))]
fn ensure_dag_with_overlay(
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    prebuilt_dir: Option<&Path>,
    out_dir: &Path,
    lock_path: &Path,
) -> Result<(Vec<PathBuf>, String), String> {
    let active_sysroot_sha = compute_lean_sysroot_manifest_sha256(lean_stdlib)?;
    let overlay =
        inspect_prebuilt_overlay(prebuilt_dir, dag, base_root, lean_bin, &active_sysroot_sha)?;
    ensure_dag_with_verified_overlay(
        dag,
        base_root,
        lean_bin,
        lean_stdlib,
        &overlay,
        out_dir,
        lock_path,
    )
}

fn ensure_dag_with_verified_overlay(
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    overlay: &VerifiedPrebuiltOverlay,
    out_dir: &Path,
    lock_path: &Path,
) -> Result<(Vec<PathBuf>, String), String> {
    let lock_file = File::options()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(lock_path)
        .map_err(|e| format!("open Lean cache lock {}: {e}", lock_path.display()))?;
    lock_file.lock().map_err(|e| format!("lock Lean cache {}: {e}", lock_path.display()))?;

    let ready = out_dir.join(".anneal-oleans-ready");
    // Always place all prebuilt + newly compiled module roots inside `out_dir`
    // so `LEAN_PATH` has a single workspace root before `lean_stdlib`.
    let search_paths = vec![out_dir.to_path_buf(), lean_stdlib.to_path_buf()];
    let lean_path = env::join_paths(&search_paths)
        .map_err(|e| format!("join LEAN_PATH: {e}"))?
        .to_string_lossy()
        .into_owned();

    let compile_timeout = effective_timeout_secs(LEAN_COMPILE_TIMEOUT_SECS)?;
    let overlay_label;
    if !ready.is_file() {
        // Wipe any unstamped partial `.olean` directory under the lock so stale
        // artifacts from interrupted builds can never poison the cache.
        if out_dir.exists() {
            fs::remove_dir_all(out_dir)
                .map_err(|e| format!("wipe unstamped Lean cache {}: {e}", out_dir.display()))?;
        }
        fs::create_dir_all(out_dir).map_err(|e| format!("create {}: {e}", out_dir.display()))?;

        let mut built: BTreeSet<&'static str> = BTreeSet::new();
        let mut staged: BTreeSet<&'static str> = BTreeSet::new();
        let mut remaining: Vec<&LeanDagSpec> = Vec::new();
        for spec in dag {
            let rel = spec.module.replace('.', "/");
            if let Some(verified_parts) = overlay.modules.get(spec.module)
                && spec.deps.iter().all(|d| staged.contains(d))
            {
                stage_prebuilt_module_artifacts(verified_parts, out_dir, &rel)?;
                built.insert(spec.module);
                staged.insert(spec.module);
            } else {
                remaining.push(spec);
            }
        }
        synthesize_missing_eval_ir(
            dag,
            &staged,
            base_root,
            lean_bin,
            lean_stdlib,
            out_dir,
            compile_timeout,
        )?;

        let max_workers = thread::available_parallelism().map(|n| n.get().clamp(1, 4)).unwrap_or(1);

        while !remaining.is_empty() {
            let mut ready_batch: Vec<&LeanDagSpec> = Vec::new();
            let mut next_remaining: Vec<&LeanDagSpec> = Vec::new();
            for spec in remaining {
                if spec.deps.iter().all(|d| built.contains(d)) {
                    ready_batch.push(spec);
                } else {
                    next_remaining.push(spec);
                }
            }
            if ready_batch.is_empty() {
                return Err("dependency cycle in Lean build DAG".to_owned());
            }

            for chunk in ready_batch.chunks(max_workers) {
                let batch_results: Vec<Result<&'static str, String>> = thread::scope(|scope| {
                    let mut handles = Vec::with_capacity(chunk.len());
                    for spec in chunk {
                        let lean_path_ref = &lean_path;
                        handles.push(scope.spawn(move || {
                            let rel = spec.module.replace('.', "/");
                            let tree_root = base_root.join(spec.rel_tree);
                            let src = tree_root.join(format!("{rel}.lean"));
                            let dst = out_dir.join(format!("{rel}.olean"));
                            if let Some(parent) = dst.parent() {
                                fs::create_dir_all(parent)
                                    .map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
                            }
                            let inv = apply_lean_tool_env(
                                Invocation::new(lean_bin, LEAN_COMPILE_FLAGS)
                                    .arg("-R")
                                    .arg(&tree_root)
                                    .arg("-o")
                                    .arg(&dst)
                                    .arg(&src)
                                    .env("LEAN_PATH", lean_path_ref),
                                lean_bin,
                            );
                            let res = run_supervised_cmd(
                                &inv,
                                &tree_root,
                                compile_timeout,
                                &format!("lean compile {}", spec.module),
                            )?;
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
                            h.join()
                                .unwrap_or_else(|_| Err("Lean compile worker panicked".to_owned()))
                        })
                        .collect()
                });
                for r in batch_results {
                    built.insert(r?);
                }
            }

            remaining = next_remaining;
        }

        overlay_label = if staged.is_empty() {
            overlay.fallback_label.clone()
        } else {
            format!("staged:{}/{}", staged.len(), dag.len())
        };
        fs::write(&ready, format!("{overlay_label}\n"))
            .map_err(|e| format!("write Lean ready stamp {}: {e}", ready.display()))?;
    } else if overlay.modules.is_empty() {
        overlay_label = overlay.fallback_label.clone();
    } else {
        let stamped = fs::read_to_string(&ready)
            .map_err(|e| format!("read Lean ready stamp {}: {e}", ready.display()))?;
        let trimmed = stamped.trim();
        overlay_label =
            if trimmed.is_empty() { overlay.fallback_label.clone() } else { trimmed.to_owned() };
    }
    drop(lock_file);

    Ok((search_paths, overlay_label))
}

fn join_library_path(primary: &Path) -> String {
    match env::var("LD_LIBRARY_PATH") {
        Ok(existing) if !existing.is_empty() => format!("{}:{existing}", primary.display()),
        _ => primary.display().to_string(),
    }
}

pub(crate) fn lean_val_expr(
    val: &MirValue,
    def_id: usize,
    arg_idx: usize,
) -> Result<String, String> {
    match val {
        MirValue::Int { int_kind, bits } => {
            Ok(format!(".scalar {}", int_kind.to_lean_scalar(*bits)))
        }
        MirValue::Bool { value } => {
            Ok(if *value { ".bool true" } else { ".bool false" }.to_owned())
        }
        MirValue::Char { scalar } => {
            char::from_u32(*scalar).ok_or_else(|| format!("invalid char scalar {scalar}"))?;
            Ok(format!(".char (Char.ofNat {scalar})"))
        }
        MirValue::Ordering { value } => Ok(value.to_lean_val().to_owned()),
        MirValue::Unit => Ok(".unit".to_owned()),
        MirValue::OverflowPair { int_kind, bits, overflow } => {
            let b_str = if *overflow { "true" } else { "false" };
            Ok(format!(".tuple [.scalar {}, .bool {}]", int_kind.to_lean_scalar(*bits), b_str))
        }
        MirValue::Enum { variant_index, .. } => {
            Ok(format!("(argEnumVal Captured.program {def_id} {arg_idx} {variant_index})"))
        }
    }
}

fn val_uses_128bit(v: &MirValue) -> bool {
    matches!(
        v,
        MirValue::Int { int_kind: IntKind::U128 | IntKind::I128, .. }
            | MirValue::OverflowPair { int_kind: IntKind::U128 | IntKind::I128, .. }
    )
}

fn case_uses_128bit(case: &LitmusCase) -> bool {
    case.args.iter().any(val_uses_128bit)
        || case.expected_return.as_ref().is_some_and(val_uses_128bit)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WpStepTrace {
    pub total_steps: usize,
    pub checkpoints: Vec<(usize, String)>,
}

fn is_wp_shape_candidate(captured: &CapturedModule, case: &LitmusCase) -> bool {
    let single_block_eligible =
        captured.kernel_whnf_eligible_by_fn.get(&case.function).copied().unwrap_or(false);
    let ub_sysroot_eligible =
        captured.kernel_whnf_ub_sysroot_by_fn.get(&case.function).copied().unwrap_or(false);
    let shape_eligible = match case.expected {
        Expectation::Pass => single_block_eligible,
        Expectation::Ub => single_block_eligible || ub_sysroot_eligible,
        Expectation::UnsupportedControl => false,
    };
    shape_eligible && !case_uses_128bit(case)
}

fn generate_lean_eval_probe(
    captured: &CapturedModule,
    cases: &[&LitmusCase],
) -> Result<String, String> {
    let mut out = format!(
        "-- Copyright 2026 The Fuchsia Authors\n\
         import Captured\n\
         import Anneal.MirTotal.ExecTotal\n\
         open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal\n\n\
         def widthName : IntWidth → String\n\
           | .i8 => \"i8\" | .i16 => \"i16\" | .i32 => \"i32\"\n\
           | .i64 => \"i64\" | .i128 => \"i128\" | .isize => \"isize\"\n\n\
         def renderPrimitive : Val → String\n\
           | .scalar sv => \"INT:\" ++ widthName sv.width ++ \":\" ++ (if sv.signed then \"s\" else \"u\") ++ \":\" ++ toString sv.bits.toNat\n\
           | .bool b => if b then \"BOOL:true\" else \"BOOL:false\"\n\
           | .char c => \"CHAR:\" ++ toString c.toNat\n\
           | .ordering .less => \"ORDERING:less\"\n\
           | .ordering .equal => \"ORDERING:equal\"\n\
           | .ordering .greater => \"ORDERING:greater\"\n\
           | .unit => \"UNIT\"\n\
           | .tuple [.scalar sv, .bool b] => \"OVF:\" ++ widthName sv.width ++ \":\" ++ (if sv.signed then \"s\" else \"u\") ++ \":\" ++ toString sv.bits.toNat ++ \":\" ++ (if b then \"true\" else \"false\")\n\
           | _ => \"OTHER\"\n\n\
         def argEnumVal (prog : Program) (defId argIdx variantIdx : Nat) : Val :=\n\
           match (prog.bodies[defId]?).bind (fun b => b.locals[argIdx + 1]?) with\n\
           | some (.enum ety) => .enumVal ety variantIdx\n\
           | _ => .unit\n\n\
         def renderBool (b : Bool) : String := if b then \"true\" else \"false\"\n\n\
         def renderWidth : IntWidth → String\n\
           | .i8 => \".i8\" | .i16 => \".i16\" | .i32 => \".i32\"\n\
           | .i64 => \".i64\" | .i128 => \".i128\" | .isize => \".isize\"\n\n\
         def renderEnumTagRepr : EnumTagRepr → String\n\
           | .zeroSized => \"EnumTagRepr.zeroSized\"\n\
           | .scalar w s => \"(EnumTagRepr.scalar \" ++ renderWidth w ++ \" \" ++ renderBool s ++ \")\"\n\n\
         def renderEnumTy (e : EnumTy) : String :=\n\
           \"{{ id := \" ++ toString e.id ++\n\
           \", discrWidth := \" ++ renderWidth e.discrWidth ++\n\
           \", discrSigned := \" ++ renderBool e.discrSigned ++\n\
           \", tagRepr := \" ++ renderEnumTagRepr e.tagRepr ++\n\
           \", discriminants := [\" ++ String.intercalate \", \" (e.discriminants.map toString) ++ \"] }}\"\n\n\
         mutual\n\
         partial def renderValList? : List Val → Option (List String)\n\
           | [] => some []\n\
           | v :: vs => do\n\
             let s ← renderVal? v\n\
             let ss ← renderValList? vs\n\
             some (s :: ss)\n\n\
         partial def renderVal? : Val → Option String\n\
           | .scalar sv =>\n\
             some (\"Val.scalar ⟨\" ++ renderWidth sv.width ++ \", \" ++ renderBool sv.signed ++\n\
               \", BitVec.ofNat 128 \" ++ toString sv.bits.toNat ++ \"⟩\")\n\
           | .bool b => some (\"Val.bool \" ++ renderBool b)\n\
           | .char c => some (\"Val.char (Char.ofNat \" ++ toString c.toNat ++ \")\")\n\
           | .ordering .less => some \"Val.ordering .less\"\n\
           | .ordering .equal => some \"Val.ordering .equal\"\n\
           | .ordering .greater => some \"Val.ordering .greater\"\n\
           | .unit => some \"Val.unit\"\n\
           | .enumVal ety var => some (\"Val.enumVal \" ++ renderEnumTy ety ++ \" \" ++ toString var)\n\
           | .tuple vs => do\n\
             let ss ← renderValList? vs\n\
             some (\"Val.tuple [\" ++ String.intercalate \", \" ss ++ \"]\")\n\
           | _ => none\n\
         end\n\n\
         def renderLocalSlot? : LocalSlot → Option String\n\
           | .dead => some \"LocalSlot.dead\"\n\
           | .immediate none => some \"LocalSlot.immediate none\"\n\
           | .immediate (some v) => do\n\
             let sv ← renderVal? v\n\
             some (\"LocalSlot.immediate (some (\" ++ sv ++ \"))\")\n\
           | _ => none\n\n\
         def renderSysrootKind : SysrootNumKind → String\n\
           | .uncheckedAdd => \".uncheckedAdd\"\n\
           | .uncheckedSub => \".uncheckedSub\"\n\
           | .uncheckedMul => \".uncheckedMul\"\n\
           | .wrappingAdd => \".wrappingAdd\"\n\
           | .wrappingSub => \".wrappingSub\"\n\
           | .wrappingMul => \".wrappingMul\"\n\n\
         def renderSysrootOp (op : SysrootNumOp) : String :=\n\
           \"{{ kind := \" ++ renderSysrootKind op.kind ++\n\
           \", width := \" ++ renderWidth op.width ++\n\
           \", signed := \" ++ renderBool op.signed ++ \" }}\"\n\n\
         def renderFrame? (f : FrameState) : Option String :=\n\
           match f.locals.mapM renderLocalSlot? with\n\
           | none => none\n\
           | some slotStrs =>\n\
             let sysStr := match f.sysrootOp? with\n\
               | none => \"\"\n\
               | some op => \", sysrootOp? := some \" ++ renderSysrootOp op\n\
             let retDstStr? : Option String := match f.retDst? with\n\
               | none => some \"\"\n\
               | some p =>\n\
                 if p.projection.isEmpty then some (\", retDst? := some ⟨\" ++ toString p.localId ++ \", []⟩\")\n\
                 else none\n\
             match retDstStr? with\n\
             | none => none\n\
             | some retDstStr =>\n\
               let retTgtStr := match f.retTarget? with\n\
                 | none => \"\"\n\
                 | some t => \", retTarget? := some \" ++ toString t\n\
               some (\"{{ defId := \" ++ toString f.defId ++\n\
                 \", blockIdx := \" ++ toString f.blockIdx ++\n\
                 \", stmtIdx := \" ++ toString f.stmtIdx ++\n\
                 \", locals := [\" ++ String.intercalate \", \" slotStrs ++ \"]\" ++\n\
                 sysStr ++ retDstStr ++ retTgtStr ++ \" }}\")\n\n\
         def renderState? (s : State) : Option String :=\n\
           if !s.callerMem.allocations.isEmpty || !s.mem.allocations.isEmpty || s.mem.nextAllocId != 2 then\n\
             none\n\
           else\n\
             match s.frames.mapM renderFrame? with\n\
             | none => none\n\
             | some fs =>\n\
               some (\"{{ frames := [\" ++ String.intercalate \", \" fs ++ \"], callerMem := ⟨[]⟩, mem := entryMemoryComp }}\")\n\n\
         def collectWpTrace (prog : Program) : Nat → Nat → State → List (Nat × String) → Option (Nat × List (Nat × String))\n\
           | 0, _, _, _ => none\n\
           | fuelRem + 1, elapsed, st, accRev =>\n\
             let nextAcc? : Option (List (Nat × String)) :=\n\
               if elapsed % {WP_TRACE_STRIDE} == 0 then\n\
                 match renderState? st with\n\
                 | none => none\n\
                 | some rendered => some ((elapsed, rendered) :: accRev)\n\
               else\n\
                 some accRev\n\
             match nextAcc? with\n\
             | none => none\n\
             | some accRev' =>\n\
               match evalMirStepBy (mirTyBeqAt 8) prog 0 st with\n\
               | .done _ | .fault _ => some (elapsed + 1, accRev'.reverse)\n\
               | .step st' => collectWpTrace prog fuelRem (elapsed + 1) st' accRev'\n\n\
         def dumpWpTrace (caseId : String) (defId wpFuel : Nat) (args : List Val) : String :=\n\
           let prog : Program := {{ Captured.program with entryDefId := defId }}\n\
           let payload : String :=\n\
             match initStateBy (mirTyBeqAt 8) prog {{ args := args }} with\n\
             | .ok s0 =>\n\
               (match collectWpTrace prog wpFuel 0 s0 [] with\n\
                | some (totalSteps, cps) =>\n\
                  toString totalSteps ++ \"|\" ++ String.intercalate \"|\" (cps.map (fun p => toString p.1 ++ \"@\" ++ p.2))\n\
                | none => \"SKIP\")\n\
             | .error _ => \"SKIP\"\n\
           \"ANNEAL_LEAN_TRACE:\" ++ caseId ++ \":\" ++ payload\n\n\
         def runCase (caseId : String) (defId fuel : Nat) (args : List Val) : String :=\n\
           let prog : Program := {{ Captured.program with entryDefId := defId }}\n\
           let res :=\n\
             match initStateBy (mirTyBeqAt 8) prog {{ args := args }} with\n\
             | .error .undefined => \"INIT_UNDEFINED\"\n\
             | .error .unsupported => \"INIT_UNSUPPORTED\"\n\
             | .ok s0 =>\n\
               match evalMirFuelBy (mirTyBeqAt 8) prog fuel s0 with\n\
               | .step _ => \"OUT_OF_FUEL\"\n\
               | .fault .undefined => \"FAULT:undefined\"\n\
               | .fault .unsupported => \"FAULT:unsupported\"\n\
               | .done (.unwound _) => \"UNWOUND\"\n\
               | .done (.aborted _) => \"ABORTED\"\n\
               | .done (.returned out) => \"RETURNED:\" ++ renderPrimitive out.ret\n\
           \"ANNEAL_LEAN_CASE:\" ++ caseId ++ \":\" ++ res\n\n",
    );

    for case in cases {
        let def_id = captured
            .body_ids_by_fn
            .get(&case.function)
            .copied()
            .ok_or_else(|| format!("missing defId for function {:?}", case.function))?;
        let args_lean = case
            .args
            .iter()
            .enumerate()
            .map(|(arg_idx, val)| lean_val_expr(val, def_id, arg_idx))
            .collect::<Result<Vec<_>, _>>()?
            .join(", ");
        out.push_str(&format!(
            "#eval runCase {:?} {def_id} {} [{args_lean}]\n",
            case.id, case.fuel
        ));
        if is_wp_shape_candidate(captured, case) {
            out.push_str(&format!(
                "#eval dumpWpTrace {:?} {def_id} {} [{args_lean}]\n",
                case.id,
                case.fuel.min(16)
            ));
        }
    }

    Ok(out)
}

pub(crate) fn parse_lean_wp_traces(stdout: &str) -> Result<BTreeMap<String, WpStepTrace>, String> {
    let mut traces = BTreeMap::new();
    let mut seen_ids = BTreeSet::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        let unquoted =
            trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(trimmed);
        let Some(rest) = unquoted.strip_prefix(LEAN_TRACE_PREFIX) else {
            continue;
        };
        let Some((id, payload)) = rest.split_once(':') else {
            return Err(format!("malformed Lean WP trace line {trimmed:?}"));
        };
        if id.is_empty() {
            return Err(format!("empty case id in Lean WP trace line {trimmed:?}"));
        }
        if payload.is_empty() {
            return Err(format!("empty payload in Lean WP trace for {id:?}"));
        }
        if !seen_ids.insert(id.to_owned()) {
            return Err(format!("duplicate Lean WP trace line for case {id:?}"));
        }
        if payload == "SKIP" {
            continue;
        }
        let mut parts = payload.split('|');
        let total_str = parts
            .next()
            .ok_or_else(|| format!("missing total step count in WP trace for {id:?}"))?;
        let total_steps = total_str.parse::<usize>().map_err(|e| {
            format!("invalid total steps {total_str:?} in WP trace for {id:?}: {e}")
        })?;
        if total_steps == 0 {
            return Err(format!("WP trace for {id:?} reported 0 total steps"));
        }
        let mut checkpoints = Vec::new();
        for cp in parts {
            let (step_str, state_expr) = cp
                .split_once('@')
                .ok_or_else(|| format!("malformed WP checkpoint {cp:?} for {id:?}"))?;
            let step = step_str.parse::<usize>().map_err(|e| {
                format!("invalid checkpoint step {step_str:?} in WP trace for {id:?}: {e}")
            })?;
            if step >= total_steps || state_expr.is_empty() {
                return Err(format!(
                    "out-of-range or empty WP checkpoint step={step} total={total_steps} for {id:?}"
                ));
            }
            if let Some(&(prev_step, _)) = checkpoints.last()
                && step <= prev_step
            {
                return Err(format!(
                    "non-monotonic WP checkpoint {step} <= {prev_step} for {id:?}"
                ));
            }
            checkpoints.push((step, state_expr.to_owned()));
        }
        if checkpoints.first().is_none_or(|(step, _)| *step != 0) {
            return Err(format!("WP trace for {id:?} missing step-0 checkpoint"));
        }
        traces.insert(id.to_owned(), WpStepTrace { total_steps, checkpoints });
    }
    Ok(traces)
}

/// Select budget-fitting non-128-bit cases whose `#eval` `StepCore` outcome
/// already matched `case.expected` so kernel `rfl` checking never aborts
/// structured verdict classification on semantic regressions.
fn select_wp_kernel_candidates<'a>(
    captured: &CapturedModule,
    cases: &[&'a LitmusCase],
    raw_outcomes: &BTreeMap<String, ObservedOutcome>,
) -> Vec<&'a LitmusCase> {
    let mut out = Vec::new();
    for &case in cases {
        if !is_wp_shape_candidate(captured, case) {
            continue;
        }
        let Some(obs) = raw_outcomes.get(&case.id) else {
            continue;
        };
        let matches_expected = match case.expected {
            Expectation::Pass => {
                matches!((obs, &case.expected_return), (ObservedOutcome::Returned { value }, Some(exp)) if value == exp)
            }
            Expectation::Ub => matches!(obs, ObservedOutcome::UndefinedBehavior { .. }),
            Expectation::UnsupportedControl => false,
        };
        if matches_expected {
            out.push(case);
        }
    }
    out
}

#[cfg(test)]
fn generate_lean_wp_probe(
    captured: &CapturedModule,
    candidates: &[&LitmusCase],
) -> Result<String, String> {
    generate_lean_wp_probe_with_traces(captured, candidates, &BTreeMap::new())
}

pub(crate) fn generate_lean_wp_probe_with_traces(
    captured: &CapturedModule,
    candidates: &[&LitmusCase],
    traces: &BTreeMap<String, WpStepTrace>,
) -> Result<String, String> {
    let mut out = String::from(
        "-- Copyright 2026 The Fuchsia Authors\n\
         import Captured\n\
         import Anneal.MirTotal.ExecTotal\n\
         open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal\n\n\
         def argEnumVal (prog : Program) (defId argIdx variantIdx : Nat) : Val :=\n\
         \x20\x20match (prog.bodies[defId]?).bind (fun b => b.locals[argIdx + 1]?) with\n\
         \x20\x20| some (.enum ety) => .enumVal ety variantIdx\n\
         \x20\x20| _ => .unit\n\n\
         private theorem evalFuel_split {p : Program} {n1 n2 n : Nat} {s0 s1 : State}\n\
         \x20\x20\x20\x20{out : StepResult State TerminalOut}\n\
         \x20\x20\x20\x20(hN : n2 + n1 = n)\n\
         \x20\x20\x20\x20(h1 : evalMirFuelTotal p n1 s0 = .step s1)\n\
         \x20\x20\x20\x20(h2 : evalMirFuelTotal p n2 s1 = out) :\n\
         \x20\x20\x20\x20evalMirFuelTotal p n s0 = out := by\n\
         \x20\x20subst hN\n\
         \x20\x20induction n1 generalizing s0 with\n\
         \x20\x20| zero =>\n\
         \x20\x20\x20\x20change StepResult.step s0 = StepResult.step s1 at h1\n\
         \x20\x20\x20\x20cases h1\n\
         \x20\x20\x20\x20exact h2\n\
         \x20\x20| succ k ih =>\n\
         \x20\x20\x20\x20change (match evalMirStepTotal p 0 s0 with\n\
         \x20\x20\x20\x20\x20\x20| .step st' => evalMirFuelTotal p k st'\n\
         \x20\x20\x20\x20\x20\x20| .done d => .done d\n\
         \x20\x20\x20\x20\x20\x20| .fault f => .fault f) = .step s1 at h1\n\
         \x20\x20\x20\x20change (match evalMirStepTotal p 0 s0 with\n\
         \x20\x20\x20\x20\x20\x20| .step st' => evalMirFuelTotal p (n2 + k) st'\n\
         \x20\x20\x20\x20\x20\x20| .done d => .done d\n\
         \x20\x20\x20\x20\x20\x20| .fault f => .fault f) = out\n\
         \x20\x20\x20\x20cases hStep : evalMirStepTotal p 0 s0 with\n\
         \x20\x20\x20\x20| step st' =>\n\
         \x20\x20\x20\x20\x20\x20rw [hStep] at h1\n\
         \x20\x20\x20\x20\x20\x20exact ih h1\n\
         \x20\x20\x20\x20| done d =>\n\
         \x20\x20\x20\x20\x20\x20rw [hStep] at h1\n\
         \x20\x20\x20\x20\x20\x20cases h1\n\
         \x20\x20\x20\x20| fault f =>\n\
         \x20\x20\x20\x20\x20\x20rw [hStep] at h1\n\
         \x20\x20\x20\x20\x20\x20cases h1\n\n",
    );

    for (idx, case) in candidates.iter().enumerate() {
        let def_id = captured
            .body_ids_by_fn
            .get(&case.function)
            .copied()
            .ok_or_else(|| format!("missing defId for function {:?}", case.function))?;
        let args_lean = case
            .args
            .iter()
            .enumerate()
            .map(|(arg_idx, val)| lean_val_expr(val, def_id, arg_idx))
            .collect::<Result<Vec<_>, _>>()?
            .join(", ");
        let wp_fuel = case.fuel.min(16);
        let trace = traces.get(&case.id).filter(|t| {
            !t.checkpoints.is_empty()
                && t.total_steps <= wp_fuel
                && t.checkpoints.first().is_some_and(|(s, _)| *s == 0)
                && t.checkpoints.last().is_some_and(|(s, _)| *s < t.total_steps)
        });

        let build_split_proof = |out: &mut String, trace: &WpStepTrace, terminal_rhs: &str| {
            for (j, (_, st_expr)) in trace.checkpoints.iter().enumerate() {
                out.push_str(&format!("private def wp_st_{idx}_{j} : State := {st_expr}\n"));
            }
            let num_cps = trace.checkpoints.len();
            for j in 0..(num_cps - 1) {
                let n1 = trace.checkpoints[j + 1].0 - trace.checkpoints[j].0;
                out.push_str(&format!(
                    "private theorem wp_seg_{idx}_{j} :\n\
                     \x20\x20evalMirFuelTotal (entryProgForBody Captured.program {def_id}) {n1} wp_st_{idx}_{j} = .step wp_st_{idx}_{next} := rfl\n",
                    next = j + 1
                ));
            }
            let last_idx = num_cps - 1;
            let tail_steps = trace.total_steps - trace.checkpoints[last_idx].0;
            out.push_str(&format!(
                "private theorem wp_tail_{idx} :\n\
                 \x20\x20evalMirFuelTotal (entryProgForBody Captured.program {def_id}) {tail_steps} wp_st_{idx}_{last_idx} =\n\
                 \x20\x20\x20\x20{terminal_rhs} := rfl\n"
            ));
            let mut proof_expr = format!("wp_tail_{idx}");
            for j in (0..(num_cps - 1)).rev() {
                let n1 = trace.checkpoints[j + 1].0 - trace.checkpoints[j].0;
                let n2 = trace.total_steps - trace.checkpoints[j + 1].0;
                proof_expr = format!(
                    "(evalFuel_split (n1 := {n1}) (n2 := {n2}) rfl wp_seg_{idx}_{j} {proof_expr})"
                );
            }
            proof_expr
        };

        if case.expected == Expectation::Pass
            && let Some(exp) = &case.expected_return
        {
            let exp_lean = lean_val_expr(exp, def_id, 0)?;
            if let Some(tr) = trace {
                let rhs = format!(".done (.returned ⟨{exp_lean}, ⟨[]⟩⟩)");
                let proof_expr = build_split_proof(&mut out, tr, &rhs);
                out.push_str(&format!(
                    "theorem wp_pass_check_{idx} :\n\
                     \x20\x20Anneal.MirWp.wpProg (entryProgForBody Captured.program {def_id}) {}\n\
                     \x20\x20\x20\x20{{ args := [{args_lean}] }}\n\
                     \x20\x20\x20\x20(fun out => out = .returned ⟨{exp_lean}, ⟨[]⟩⟩) :=\n\
                     \x20\x20wpProg_of_evalMirFuelTotal (s0 := wp_st_{idx}_0) rfl {proof_expr} rfl\n\n",
                    tr.total_steps
                ));
            } else {
                out.push_str(&format!(
                    "theorem wp_pass_check_{idx} :\n\
                     \x20\x20Anneal.MirWp.wpProg (entryProgForBody Captured.program {def_id}) {wp_fuel}\n\
                     \x20\x20\x20\x20{{ args := [{args_lean}] }}\n\
                     \x20\x20\x20\x20(fun out => out = .returned ⟨{exp_lean}, ⟨[]⟩⟩) :=\n\
                     \x20\x20wpProg_of_evalMirFuelTotal rfl rfl rfl\n\n"
                ));
            }
        } else if case.expected == Expectation::Ub {
            if let Some(tr) = trace {
                let proof_expr = build_split_proof(&mut out, tr, ".fault .undefined");
                out.push_str(&format!(
                    "theorem wp_ub_check_{idx} :\n\
                     \x20\x20Anneal.MirWp.wpFaultProg (entryProgForBody Captured.program {def_id}) {}\n\
                     \x20\x20\x20\x20{{ args := [{args_lean}] }} .undefined :=\n\
                     \x20\x20wpFaultProg_of_evalMirFuelTotal (s0 := wp_st_{idx}_0) rfl {proof_expr}\n\n",
                    tr.total_steps
                ));
            } else {
                out.push_str(&format!(
                    "theorem wp_ub_check_{idx} :\n\
                     \x20\x20Anneal.MirWp.wpFaultProg (entryProgForBody Captured.program {def_id}) {wp_fuel}\n\
                     \x20\x20\x20\x20{{ args := [{args_lean}] }} .undefined :=\n\
                     \x20\x20wpFaultProg_of_evalMirFuelTotal rfl rfl\n\n"
                ));
            }
        }
    }

    Ok(out)
}

/// Parse `ANNEAL_LEAN_CASE:<id>:<payload>` lines emitted by `#eval runCase`.
pub fn parse_lean_probe_output(
    stdout: &str,
    cases: &[&LitmusCase],
) -> Result<BTreeMap<String, ObservedOutcome>, String> {
    let mut raw_map = BTreeMap::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        let unquoted =
            trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(trimmed);
        let Some(rest) = unquoted.strip_prefix(LEAN_CASE_PREFIX) else {
            continue;
        };
        let Some((id, payload)) = rest.split_once(':') else {
            return Err(format!("malformed Lean output line {trimmed:?}"));
        };
        raw_map.insert(id.to_owned(), parse_lean_payload(payload)?);
    }

    let mut out = BTreeMap::new();
    for case in cases {
        let outcome = raw_map.remove(&case.id).unwrap_or_else(|| ObservedOutcome::ToolError {
            detail: format!("Lean output missing case {:?}", case.id),
        });
        out.insert(case.id.clone(), outcome);
    }
    Ok(out)
}

pub fn parse_lean_payload(payload: &str) -> Result<ObservedOutcome, String> {
    match payload {
        "INIT_UNSUPPORTED" => Ok(ObservedOutcome::InitUnsupported {
            detail: "Anneal.MirTotal.StepCore.initStateBy returned .error .unsupported".to_owned(),
        }),
        "INIT_UNDEFINED" => Ok(ObservedOutcome::InitUnsupported {
            detail: "Anneal.MirTotal.StepCore.initStateBy returned .error .undefined".to_owned(),
        }),
        "FAULT:undefined" => Ok(ObservedOutcome::UndefinedBehavior {
            detail: "Trusted.MirSemantics.FaultKind.undefined".to_owned(),
        }),
        "FAULT:unsupported" => Ok(ObservedOutcome::Unsupported {
            detail: "Trusted.MirSemantics.FaultKind.unsupported".to_owned(),
        }),
        "OUT_OF_FUEL" => Ok(ObservedOutcome::OutOfFuel {
            detail: "Anneal.MirTotal.evalMirFuelBy reached fuel limit".to_owned(),
        }),
        "UNWOUND" => Ok(ObservedOutcome::AbnormalAbort {
            detail: "Trusted.MirModel.TerminalOut.unwound".to_owned(),
        }),
        "ABORTED" => Ok(ObservedOutcome::AbnormalAbort {
            detail: "Trusted.MirModel.TerminalOut.aborted".to_owned(),
        }),
        _ => {
            let Some(ret_spec) = payload.strip_prefix("RETURNED:") else {
                return Err(format!("unknown Lean payload {payload:?}"));
            };
            Ok(ObservedOutcome::Returned { value: parse_lean_val_spec(ret_spec)? })
        }
    }
}

fn check_canonical_bits(int_kind: IntKind, bits_raw: &str) -> Result<u128, String> {
    let bits =
        bits_raw.parse::<u128>().map_err(|e| format!("invalid Lean bits {bits_raw:?}: {e}"))?;
    if bits > int_kind.mask() {
        return Err(format!(
            "non-canonical Lean scalar bits {bits} exceed {} mask {}",
            int_kind.rust_name(),
            int_kind.mask()
        ));
    }
    Ok(bits)
}

fn parse_lean_val_spec(spec: &str) -> Result<MirValue, String> {
    if spec == "UNIT" {
        return Ok(MirValue::Unit);
    }
    if let Some(rest) = spec.strip_prefix("INT:") {
        let mut parts = rest.splitn(3, ':');
        let width = parts.next().ok_or_else(|| format!("malformed Lean INT {spec:?}"))?;
        let sign = parts.next().ok_or_else(|| format!("malformed Lean INT {spec:?}"))?;
        let bits_raw = parts.next().ok_or_else(|| format!("malformed Lean INT {spec:?}"))?;
        let signed = match sign {
            "s" => true,
            "u" => false,
            _ => return Err(format!("invalid Lean signedness {sign:?}")),
        };
        let int_kind = IntKind::from_lean_parts(width, signed)?;
        let bits = check_canonical_bits(int_kind, bits_raw)?;
        return Ok(MirValue::Int { int_kind, bits });
    }
    if let Some(rest) = spec.strip_prefix("BOOL:") {
        return match rest {
            "true" => Ok(MirValue::Bool { value: true }),
            "false" => Ok(MirValue::Bool { value: false }),
            _ => Err(format!("invalid Lean BOOL {rest:?}")),
        };
    }
    if let Some(rest) = spec.strip_prefix("CHAR:") {
        let scalar: u32 = rest.parse().map_err(|e| format!("invalid Lean CHAR {rest:?}: {e}"))?;
        char::from_u32(scalar).ok_or_else(|| format!("invalid Lean char scalar {scalar}"))?;
        return Ok(MirValue::Char { scalar });
    }
    if let Some(rest) = spec.strip_prefix("ORDERING:") {
        return Ok(MirValue::Ordering { value: OrderingKind::parse(rest)? });
    }
    if let Some(rest) = spec.strip_prefix("OVF:") {
        let mut parts = rest.splitn(4, ':');
        let width = parts.next().ok_or_else(|| format!("malformed Lean OVF {spec:?}"))?;
        let sign = parts.next().ok_or_else(|| format!("malformed Lean OVF {spec:?}"))?;
        let bits_raw = parts.next().ok_or_else(|| format!("malformed Lean OVF {spec:?}"))?;
        let ovf_raw = parts.next().ok_or_else(|| format!("malformed Lean OVF {spec:?}"))?;
        let signed = match sign {
            "s" => true,
            "u" => false,
            _ => return Err(format!("invalid Lean OVF signedness {sign:?}")),
        };
        let int_kind = IntKind::from_lean_parts(width, signed)?;
        let bits = check_canonical_bits(int_kind, bits_raw)?;
        let overflow = match ovf_raw {
            "true" => true,
            "false" => false,
            _ => return Err(format!("invalid Lean OVF flag {ovf_raw:?}")),
        };
        return Ok(MirValue::OverflowPair { int_kind, bits, overflow });
    }
    Err(format!("unsupported Lean value specification {spec:?}"))
}

#[cfg(test)]
mod tests {
    use anneal_testkit::toolchain::default_lean_path;

    use super::*;

    #[test]
    fn parses_lean_eval_lines_and_rejects_unmasked_bits() {
        assert_eq!(
            parse_lean_payload("RETURNED:INT:i32:s:4294967276").unwrap(),
            ObservedOutcome::Returned {
                value: MirValue::Int { int_kind: IntKind::I32, bits: (-20i32 as u32) as u128 }
            }
        );
        assert!(parse_lean_payload("RETURNED:INT:i32:u:4294967300").is_err());
        assert!(parse_lean_payload("RETURNED:OVF:i32:u:4294967300:true").is_err());

        assert_eq!(
            parse_lean_payload("RETURNED:OVF:i64:u:4:true").unwrap(),
            ObservedOutcome::Returned {
                value: MirValue::OverflowPair { int_kind: IntKind::U64, bits: 4, overflow: true }
            }
        );
        assert!(matches!(
            parse_lean_payload("FAULT:undefined").unwrap(),
            ObservedOutcome::UndefinedBehavior { .. }
        ));
        assert!(matches!(
            parse_lean_payload("FAULT:unsupported").unwrap(),
            ObservedOutcome::Unsupported { .. }
        ));
        assert!(matches!(
            parse_lean_payload("INIT_UNSUPPORTED").unwrap(),
            ObservedOutcome::InitUnsupported { .. }
        ));
        assert!(matches!(
            parse_lean_payload("ABORTED").unwrap(),
            ObservedOutcome::AbnormalAbort { ref detail }
                if detail == "Trusted.MirModel.TerminalOut.aborted"
        ));
    }

    #[test]
    fn mir_total_dag_matches_lean_imports() {
        let anneal_root =
            ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))
                .expect("locate anneal root");
        let mut seen = BTreeSet::new();

        for spec in MIR_TOTAL_DAG {
            let rel = spec.module.replace('.', "/") + ".lean";
            let src_path = anneal_root.join(spec.rel_tree).join(&rel);
            let content = fs::read_to_string(&src_path)
                .unwrap_or_else(|e| panic!("read {}: {e}", src_path.display()));
            let mut actual_deps = BTreeSet::new();
            for line in content.lines() {
                let trimmed = line.trim();
                let target = trimmed
                    .strip_prefix("public import all ")
                    .or_else(|| trimmed.strip_prefix("public import "))
                    .or_else(|| trimmed.strip_prefix("import all "))
                    .or_else(|| trimmed.strip_prefix("import "));
                let Some(rest) = target else {
                    continue;
                };
                let module_name = rest.split_whitespace().next().unwrap_or("");
                if module_name.is_empty()
                    || module_name.starts_with("Init.")
                    || module_name.starts_with("Std.")
                    || module_name.starts_with("Lean.")
                    || matches!(module_name, "Init" | "Std" | "Lean")
                {
                    continue;
                }
                actual_deps.insert(module_name.to_owned());
            }

            let declared_deps: BTreeSet<String> =
                spec.deps.iter().map(|d| (*d).to_owned()).collect();
            assert_eq!(
                declared_deps, actual_deps,
                "MIR_TOTAL_DAG deps drifted for {}",
                spec.module
            );
            for dep in spec.deps {
                assert!(
                    seen.contains(dep),
                    "MIR_TOTAL_DAG dependency {dep} must precede {}",
                    spec.module
                );
            }
            seen.insert(spec.module);
        }
    }

    fn collect_test_prebuilt_parts_with_exts(
        prebuilt_dir: &Path,
        rel_stem: &str,
        exts: &[&str],
    ) -> (Vec<serde_json::Value>, Vec<String>) {
        let mut parts = Vec::new();
        let mut part_shas = Vec::new();
        for ext in exts {
            let p = prebuilt_dir.join(format!("{rel_stem}.{ext}"));
            if p.is_file() {
                let sha = sha256_file_hex(&p).unwrap();
                part_shas.push(sha.clone());
                parts.push(serde_json::json!({
                    "suffix": ext,
                    "path": format!("{rel_stem}.{ext}"),
                    "sha256": sha,
                }));
            }
        }
        assert!(!parts.is_empty());
        (parts, part_shas)
    }

    fn collect_test_prebuilt_parts(
        prebuilt_dir: &Path,
        rel_stem: &str,
    ) -> (Vec<serde_json::Value>, Vec<String>) {
        collect_test_prebuilt_parts_with_exts(
            prebuilt_dir,
            rel_stem,
            &["olean", "olean.server", "olean.private"],
        )
    }

    fn write_test_prebuilt_manifest(
        prebuilt_dir: &Path,
        lean_bin: &Path,
        sysroot_sha: &str,
        module: &str,
        rel_stem: &str,
        src_path: &Path,
    ) {
        let lean_sha = sha256_file_hex(lean_bin).unwrap();
        let src_sha = sha256_file_hex(src_path).unwrap();
        let (parts, _) = collect_test_prebuilt_parts(prebuilt_dir, rel_stem);
        let manifest = serde_json::json!({
            "schema_version": PREBUILT_SCHEMA_VERSION,
            "entries": [
                {
                    "kind": "module",
                    "module": module,
                    "lean_sha256": lean_sha,
                    "sysroot_manifest_sha256": sysroot_sha,
                    "source_sha256": src_sha,
                    "is_module": source_starts_with_module_keyword(&fs::read(src_path).unwrap()),
                    "flags": CANONICAL_PREBUILT_FLAGS,
                    "imports": [],
                    "parts": parts,
                }
            ]
        });
        fs::write(
            prebuilt_dir.join("manifest.json"),
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();
    }

    #[test]
    fn timeout_override_and_ambiguous_body_lookup_behave_cleanly() {
        assert_eq!(effective_timeout_secs_from(None, 120).unwrap(), 120);
        assert_eq!(effective_timeout_secs_from(Some(OsStr::new("")), 120).unwrap(), 120);
        assert_eq!(effective_timeout_secs_from(Some(OsStr::new("600")), 120).unwrap(), 600);
        assert!(effective_timeout_secs_from(Some(OsStr::new("0")), 120).is_err());
        assert!(effective_timeout_secs_from(Some(OsStr::new("3601")), 120).is_err());
        assert!(effective_timeout_secs_from(Some(OsStr::new("not-a-number")), 120).is_err());

        let bodies = vec![
            CaptureBody {
                identity: "rust-path-v1::m1::foo".to_owned(),
                arg_count: 0,
                local_tys: vec![],
                blocks: vec![],
            },
            CaptureBody {
                identity: "rust-path-v1::m2::foo".to_owned(),
                arg_count: 0,
                local_tys: vec![],
                blocks: vec![],
            },
        ];
        let ambig_err = select_captured_body(&bodies, "foo", Path::new("cap.json"))
            .err()
            .expect("ambiguous suffix must fail");
        assert!(ambig_err.contains("ambiguous"), "{ambig_err}");

        let with_exact = vec![
            CaptureBody {
                identity: "rust-path-v1::foo".to_owned(),
                arg_count: 0,
                local_tys: vec![],
                blocks: vec![],
            },
            CaptureBody {
                identity: "rust-path-v1::m2::foo".to_owned(),
                arg_count: 0,
                local_tys: vec![],
                blocks: vec![],
            },
        ];
        let (idx, chosen) =
            select_captured_body(&with_exact, "foo", Path::new("cap.json")).unwrap();
        assert_eq!(idx, 0);
        assert_eq!(chosen.identity, "rust-path-v1::foo");

        assert!(source_starts_with_module_keyword(b"module\nprelude\n"));
        assert!(source_starts_with_module_keyword(b"module"));
        assert!(source_starts_with_module_keyword(
            b"-- line\n/- nested /- block -/ -/\nmodule--comment\nprelude\n"
        ));
        assert!(source_starts_with_module_keyword(b"module/-block-/\nprelude\n"));
        assert!(!source_starts_with_module_keyword(b"modulefoo\nprelude\n"));
        assert!(!source_starts_with_module_keyword(b"module_1\nprelude\n"));
        assert!(!source_starts_with_module_keyword(b"prelude\nmodule\n"));
    }

    #[test]
    fn ensure_dag_with_overlay_verifies_manifest_rejects_stale_source_and_wipes_partial() {
        let lean_bin = fs::canonicalize(default_lean_path().expect("resolve pinned lean"))
            .expect("canonicalize lean");
        let lean_prefix = query_lean_prefix(&lean_bin).expect("query lean prefix");
        let lean_stdlib = lean_prefix.join("lib/lean");
        let active_sysroot_sha =
            compute_lean_sysroot_manifest_sha256(&lean_stdlib).expect("hash active lean stdlib");

        // Sysroot digest must include `.ir` and `.ir.sig` alongside `.olean*`
        // (parity with `ci/prebuild_bundled_oleans.py` and `cargo-anneal`), and
        // `module_needs_eval_ir` must include `Trusted.MirModel` and
        // `Trusted.MirSemantics.State`.
        assert!(module_needs_eval_ir("Trusted.MirModel"));
        assert!(module_needs_eval_ir("Trusted.MirSemantics.State"));
        let sys_tmp = tempfile::tempdir().unwrap();
        let mock_stdlib = sys_tmp.path().join("lib/lean");
        fs::create_dir_all(mock_stdlib.join("Init")).unwrap();
        for ext in LEAN_ARTIFACT_EXTS {
            fs::write(mock_stdlib.join(format!("Init/Core.{ext}")), b"v1").unwrap();
        }
        let sys_sha_1 = compute_lean_sysroot_manifest_sha256(&mock_stdlib).unwrap();
        fs::write(mock_stdlib.join("Init/Core.ir"), b"v2").unwrap();
        let sys_sha_2 = compute_lean_sysroot_manifest_sha256(&mock_stdlib).unwrap();
        assert_ne!(sys_sha_1, sys_sha_2, "sysroot manifest must track .ir changes");
        fs::write(mock_stdlib.join("Init/Core.ir.sig"), b"v2").unwrap();
        let sys_sha_3 = compute_lean_sysroot_manifest_sha256(&mock_stdlib).unwrap();
        assert_ne!(sys_sha_2, sys_sha_3, "sysroot manifest must track .ir.sig changes");

        let tmp = tempfile::tempdir().unwrap();
        let src_tree = tmp.path().join("src");
        let base_dir = src_tree.join("TestRoot");
        fs::create_dir_all(&base_dir).unwrap();
        let base_src = base_dir.join("Base.lean");
        let child_src = base_dir.join("Child.lean");
        fs::write(
            &base_src,
            "module\npublic def baseVal : Nat := 7\npublic def baseJoin (xs : List String) : String := String.intercalate \":\" xs\n",
        )
        .unwrap();
        fs::write(
            &child_src,
            "module\npublic import TestRoot.Base\npublic def childVal : Nat := baseVal + 1\n",
        )
        .unwrap();

        let prebuilt = tmp.path().join("prebuilt");
        fs::create_dir_all(prebuilt.join("lib/TestRoot")).unwrap();
        let prebuilt_inv = apply_lean_tool_env(
            Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-R")
                .arg(&src_tree)
                .arg("-o")
                .arg(prebuilt.join("lib/TestRoot/Base.olean"))
                .arg(&base_src)
                .env("LEAN_PATH", &lean_stdlib),
            &lean_bin,
        );
        let base_res = run_supervised_cmd(
            &prebuilt_inv,
            &src_tree,
            LEAN_COMPILE_TIMEOUT_SECS,
            "prebuilt base",
        )
        .unwrap();
        assert!(
            matches!(base_res.termination, Termination::Exited(s) if s.success()),
            "compile prebuilt Base: {}",
            base_res.describe()
        );
        write_test_prebuilt_manifest(
            &prebuilt,
            &lean_bin,
            &active_sysroot_sha,
            "TestRoot.Base",
            "lib/TestRoot/Base",
            &base_src,
        );

        let dag = [
            LeanDagSpec { module: "TestRoot.Base", rel_tree: "src", deps: &[] },
            LeanDagSpec { module: "TestRoot.Child", rel_tree: "src", deps: &["TestRoot.Base"] },
        ];
        let out_dir = tmp.path().join("overlay_out");
        let lock_path = tmp.path().join("overlay.lock");
        let (search_paths, overlay_status) = ensure_dag_with_overlay(
            &dag,
            tmp.path(),
            &lean_bin,
            &lean_stdlib,
            Some(&prebuilt),
            &out_dir,
            &lock_path,
        )
        .expect("overlay DAG compilation must succeed with verified manifest artifacts");

        assert_eq!(search_paths, vec![out_dir.clone(), lean_stdlib.clone()]);
        assert_eq!(overlay_status, "staged:1/2");
        assert!(out_dir.join("TestRoot/Base.olean").is_file());
        assert!(out_dir.join("TestRoot/Child.olean").is_file());

        // Mismatched `sysroot_manifest_sha256` MUST reject staging.
        let mut bad_sysroot_manifest: serde_json::Value =
            serde_json::from_slice(&fs::read(prebuilt.join("manifest.json")).unwrap()).unwrap();
        bad_sysroot_manifest["entries"][0]["sysroot_manifest_sha256"] =
            serde_json::json!("b".repeat(64));
        let bad_sysroot_pb = tmp.path().join("prebuilt_bad_sysroot");
        fs::create_dir_all(bad_sysroot_pb.join("lib/TestRoot")).unwrap();
        fs::copy(
            prebuilt.join("lib/TestRoot/Base.olean"),
            bad_sysroot_pb.join("lib/TestRoot/Base.olean"),
        )
        .unwrap();
        fs::write(
            bad_sysroot_pb.join("manifest.json"),
            serde_json::to_vec_pretty(&bad_sysroot_manifest).unwrap(),
        )
        .unwrap();
        let bad_sysroot_overlay = inspect_prebuilt_overlay(
            Some(&bad_sysroot_pb),
            &dag,
            tmp.path(),
            &lean_bin,
            &active_sysroot_sha,
        )
        .unwrap();
        assert!(bad_sysroot_overlay.modules.is_empty());
        assert_eq!(bad_sysroot_overlay.fallback_label, "skipped:digest_mismatch");

        // Tampering with `flags` in `manifest.json` MUST reject staging.
        let mut parsed_manifest: serde_json::Value =
            serde_json::from_slice(&fs::read(prebuilt.join("manifest.json")).unwrap()).unwrap();
        parsed_manifest["entries"][0]["flags"] = serde_json::json!(["-j1"]);
        let bad_flag_pb = tmp.path().join("prebuilt_bad_flag");
        fs::create_dir_all(bad_flag_pb.join("lib/TestRoot")).unwrap();
        fs::copy(
            prebuilt.join("lib/TestRoot/Base.olean"),
            bad_flag_pb.join("lib/TestRoot/Base.olean"),
        )
        .unwrap();
        fs::write(
            bad_flag_pb.join("manifest.json"),
            serde_json::to_vec_pretty(&parsed_manifest).unwrap(),
        )
        .unwrap();
        let bad_flag_overlay = inspect_prebuilt_overlay(
            Some(&bad_flag_pb),
            &dag,
            tmp.path(),
            &lean_bin,
            &active_sysroot_sha,
        )
        .unwrap();
        assert!(bad_flag_overlay.modules.is_empty());
        assert_eq!(bad_flag_overlay.fallback_label, "skipped:digest_mismatch");

        // Legacy `schema_version: 1` manifests must be skipped cleanly.
        let mut v1_manifest: serde_json::Value =
            serde_json::from_slice(&fs::read(prebuilt.join("manifest.json")).unwrap()).unwrap();
        v1_manifest["schema_version"] = serde_json::json!(1);
        let v1_pb = tmp.path().join("prebuilt_v1");
        fs::create_dir_all(&v1_pb).unwrap();
        fs::write(v1_pb.join("manifest.json"), serde_json::to_vec_pretty(&v1_manifest).unwrap())
            .unwrap();
        let v1_overlay = inspect_prebuilt_overlay(
            Some(&v1_pb),
            &dag,
            tmp.path(),
            &lean_bin,
            &active_sysroot_sha,
        )
        .unwrap();
        assert!(v1_overlay.modules.is_empty());
        assert_eq!(v1_overlay.fallback_label, "skipped:unsupported_manifest_schema");

        // Verify v2 `transitive_sha256` DAG verification stages
        // `SkipIrDep.Leaf + Base -> Child -> SynthHost` and rejects any
        // tampered `imports[].transitive_sha256`.
        let skip_ir_dir = src_tree.join("SkipIrDep");
        fs::create_dir_all(&skip_ir_dir).unwrap();
        let skip_dep_src = skip_ir_dir.join("Leaf.lean");
        fs::write(&skip_dep_src, "module\n@[expose] public def skipIrTag : Nat := 3\n").unwrap();
        let synth_host_src = base_dir.join("SynthHost.lean");
        fs::write(
            &synth_host_src,
            "module\npublic import SkipIrDep.Leaf\npublic import TestRoot.Child\npublic def synthVal : Nat := childVal + skipIrTag\n",
        )
        .unwrap();
        fs::create_dir_all(prebuilt.join("lib/SkipIrDep")).unwrap();
        let skip_dep_res = run_supervised_cmd(
            &apply_lean_tool_env(
                Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                    .arg("-R")
                    .arg(&src_tree)
                    .arg("-o")
                    .arg(prebuilt.join("lib/SkipIrDep/Leaf.olean"))
                    .arg(&skip_dep_src)
                    .env("LEAN_PATH", &lean_stdlib),
                &lean_bin,
            ),
            &src_tree,
            LEAN_COMPILE_TIMEOUT_SECS,
            "prebuilt skip-ir dep",
        )
        .unwrap();
        assert!(
            matches!(skip_dep_res.termination, Termination::Exited(s) if s.success()),
            "compile prebuilt SkipIrDep.Leaf: {}",
            skip_dep_res.describe()
        );
        let child_pb_inv = apply_lean_tool_env(
            Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-R")
                .arg(&src_tree)
                .arg("-o")
                .arg(prebuilt.join("lib/TestRoot/Child.olean"))
                .arg(&child_src)
                .env(
                    "LEAN_PATH",
                    env::join_paths([prebuilt.join("lib"), lean_stdlib.clone()]).unwrap(),
                ),
            &lean_bin,
        );
        let child_res = run_supervised_cmd(
            &child_pb_inv,
            &src_tree,
            LEAN_COMPILE_TIMEOUT_SECS,
            "prebuilt child",
        )
        .unwrap();
        assert!(
            matches!(child_res.termination, Termination::Exited(s) if s.success()),
            "compile prebuilt Child: {}",
            child_res.describe()
        );
        let synth_host_res = run_supervised_cmd(
            &apply_lean_tool_env(
                Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                    .arg("-R")
                    .arg(&src_tree)
                    .arg("-o")
                    .arg(prebuilt.join("lib/TestRoot/SynthHost.olean"))
                    .arg(&synth_host_src)
                    .env(
                        "LEAN_PATH",
                        env::join_paths([prebuilt.join("lib"), lean_stdlib.clone()]).unwrap(),
                    ),
                &lean_bin,
            ),
            &src_tree,
            LEAN_COMPILE_TIMEOUT_SECS,
            "prebuilt synth host",
        )
        .unwrap();
        assert!(
            matches!(synth_host_res.termination, Termination::Exited(s) if s.success()),
            "compile prebuilt SynthHost: {}",
            synth_host_res.describe()
        );
        let (skip_parts, skip_part_shas) =
            collect_test_prebuilt_parts(&prebuilt, "lib/SkipIrDep/Leaf");
        let (base_parts, base_part_shas) =
            collect_test_prebuilt_parts(&prebuilt, "lib/TestRoot/Base");
        let (child_parts, child_part_shas) =
            collect_test_prebuilt_parts(&prebuilt, "lib/TestRoot/Child");
        let (synth_parts, _) = collect_test_prebuilt_parts(&prebuilt, "lib/TestRoot/SynthHost");
        let skip_transitive = compute_transitive_module_sha256(&skip_part_shas, &[]).unwrap();
        let base_transitive = compute_transitive_module_sha256(&base_part_shas, &[]).unwrap();
        let child_transitive = compute_transitive_module_sha256(
            &child_part_shas,
            &[PrebuiltImport {
                module: "TestRoot.Base".to_owned(),
                is_exported: Some(true),
                import_all: Some(false),
                is_meta: Some(false),
                part_sha256s: base_part_shas.clone(),
                transitive_sha256: base_transitive.clone(),
            }],
        )
        .unwrap();
        let mut child_manifest = serde_json::json!({
            "schema_version": PREBUILT_SCHEMA_VERSION,
            "entries": [
                {
                    "kind": "module",
                    "module": "SkipIrDep.Leaf",
                    "lean_sha256": sha256_file_hex(&lean_bin).unwrap(),
                    "sysroot_manifest_sha256": active_sysroot_sha,
                    "source_sha256": sha256_file_hex(&skip_dep_src).unwrap(),
                    "is_module": true,
                    "flags": CANONICAL_PREBUILT_FLAGS,
                    "imports": [],
                    "parts": skip_parts,
                },
                {
                    "kind": "module",
                    "module": "TestRoot.Base",
                    "lean_sha256": sha256_file_hex(&lean_bin).unwrap(),
                    "sysroot_manifest_sha256": active_sysroot_sha,
                    "source_sha256": sha256_file_hex(&base_src).unwrap(),
                    "is_module": true,
                    "flags": CANONICAL_PREBUILT_FLAGS,
                    "imports": [],
                    "parts": base_parts,
                },
                {
                    "kind": "module",
                    "module": "TestRoot.Child",
                    "lean_sha256": sha256_file_hex(&lean_bin).unwrap(),
                    "sysroot_manifest_sha256": active_sysroot_sha,
                    "source_sha256": sha256_file_hex(&child_src).unwrap(),
                    "is_module": true,
                    "flags": CANONICAL_PREBUILT_FLAGS,
                    "imports": [{
                        "module": "TestRoot.Base",
                        "is_exported": true,
                        "import_all": false,
                        "is_meta": false,
                        "part_sha256s": base_part_shas,
                        "transitive_sha256": base_transitive,
                    }],
                    "parts": child_parts,
                },
                {
                    "kind": "module",
                    "module": "TestRoot.SynthHost",
                    "lean_sha256": sha256_file_hex(&lean_bin).unwrap(),
                    "sysroot_manifest_sha256": active_sysroot_sha,
                    "source_sha256": sha256_file_hex(&synth_host_src).unwrap(),
                    "is_module": true,
                    "flags": CANONICAL_PREBUILT_FLAGS,
                    "imports": [
                        {
                            "module": "SkipIrDep.Leaf",
                            "is_exported": true,
                            "import_all": false,
                            "is_meta": false,
                            "part_sha256s": skip_part_shas,
                            "transitive_sha256": skip_transitive,
                        },
                        {
                            "module": "TestRoot.Child",
                            "is_exported": true,
                            "import_all": false,
                            "is_meta": false,
                            "part_sha256s": child_part_shas,
                            "transitive_sha256": child_transitive,
                        }
                    ],
                    "parts": synth_parts,
                }
            ]
        });
        let pb_v2 = tmp.path().join("prebuilt_v2");
        fs::create_dir_all(pb_v2.join("lib/TestRoot")).unwrap();
        fs::create_dir_all(pb_v2.join("lib/SkipIrDep")).unwrap();
        for ext in ["olean", "olean.server", "olean.private"] {
            let skip_art = prebuilt.join(format!("lib/SkipIrDep/Leaf.{ext}"));
            if skip_art.is_file() {
                fs::copy(&skip_art, pb_v2.join(format!("lib/SkipIrDep/Leaf.{ext}"))).unwrap();
            }
            for stem in ["Base", "Child", "SynthHost"] {
                let src_art = prebuilt.join(format!("lib/TestRoot/{stem}.{ext}"));
                if src_art.is_file() {
                    fs::copy(&src_art, pb_v2.join(format!("lib/TestRoot/{stem}.{ext}"))).unwrap();
                }
            }
        }
        fs::write(pb_v2.join("manifest.json"), serde_json::to_vec_pretty(&child_manifest).unwrap())
            .unwrap();
        let dag_v2 = [
            LeanDagSpec { module: "SkipIrDep.Leaf", rel_tree: "src", deps: &[] },
            LeanDagSpec { module: "TestRoot.Base", rel_tree: "src", deps: &[] },
            LeanDagSpec { module: "TestRoot.Child", rel_tree: "src", deps: &["TestRoot.Base"] },
            LeanDagSpec {
                module: "TestRoot.SynthHost",
                rel_tree: "src",
                deps: &["SkipIrDep.Leaf", "TestRoot.Child"],
            },
        ];
        let v2_ok = inspect_prebuilt_overlay(
            Some(&pb_v2),
            &dag_v2,
            tmp.path(),
            &lean_bin,
            &active_sysroot_sha,
        )
        .unwrap();
        assert_eq!(v2_ok.fallback_label, "staged:4/4");

        // Staging an `.ir`-stripped prebuilt tree
        // (`prebuild_bundled_oleans.py`) MUST seed staged non-eval
        // dependencies (`SkipIrDep.Leaf`) into `.ir_synth` and synthesize
        // `.ir`/`.ir.sig` companions so `#eval` probes run cleanly.
        let v2_out_dir = tmp.path().join("v2_ir_out");
        let v2_lock = tmp.path().join("v2_ir.lock");
        let (v2_paths, v2_status) = ensure_dag_with_overlay(
            &dag_v2,
            tmp.path(),
            &lean_bin,
            &lean_stdlib,
            Some(&pb_v2),
            &v2_out_dir,
            &v2_lock,
        )
        .expect("staging .ir-stripped prebuilt v2 must synthesize missing .ir companions");
        assert_eq!(v2_status, "staged:4/4");
        assert!(!v2_out_dir.join("SkipIrDep/Leaf.ir").exists());
        assert!(v2_out_dir.join("TestRoot/Base.ir").is_file());
        assert!(v2_out_dir.join("TestRoot/Child.ir").is_file());
        assert!(v2_out_dir.join("TestRoot/SynthHost.ir").is_file());
        assert!(!v2_out_dir.join(".ir_synth").exists());

        let cap_dir = tmp.path().join("v2_cap");
        fs::create_dir_all(&cap_dir).unwrap();
        let cap_src = cap_dir.join("Captured.lean");
        fs::write(
            &cap_src,
            "import TestRoot.SynthHost\nstructure Holder where\n  val : Nat\n  label : String\ndef h : Holder := { val := synthVal, label := baseJoin [\"a\", \"b\"] }\n",
        )
        .unwrap();
        let mut cap_paths = vec![cap_dir.clone()];
        cap_paths.extend(v2_paths);
        let cap_lean_path = env::join_paths(&cap_paths).unwrap();
        let cap_res = run_supervised_cmd(
            &apply_lean_tool_env(
                Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                    .arg("-R")
                    .arg(&cap_dir)
                    .arg("-o")
                    .arg(cap_dir.join("Captured.olean"))
                    .arg(&cap_src)
                    .env("LEAN_PATH", &cap_lean_path),
                &lean_bin,
            ),
            &cap_dir,
            LEAN_COMPILE_TIMEOUT_SECS,
            "compile non-module Captured against .ir-stripped prebuilt",
        )
        .unwrap();
        assert!(
            matches!(cap_res.termination, Termination::Exited(s) if s.success()),
            "compile Captured failed: {}",
            cap_res.describe()
        );
        let v2_probe = cap_dir.join("Probe.lean");
        fs::write(&v2_probe, "import Captured\n#eval IO.println s!\"{h.val}:{h.label}\"\n")
            .unwrap();
        let v2_eval = run_supervised_cmd(
            &apply_lean_tool_env(
                Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                    .arg(&v2_probe)
                    .env("LEAN_PATH", &cap_lean_path),
                &lean_bin,
            ),
            &cap_dir,
            LEAN_EVAL_TIMEOUT_SECS,
            "eval Probe against synthesized .ir companions",
        )
        .unwrap();
        assert!(
            matches!(v2_eval.termination, Termination::Exited(s) if s.success()),
            "eval Probe failed: {}\nstdout: {}\nstderr: {}",
            v2_eval.describe(),
            String::from_utf8_lossy(&v2_eval.stdout),
            String::from_utf8_lossy(&v2_eval.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&v2_eval.stdout).trim(), "11:a:b");

        // Partially-stripped overlay: `TestRoot.Base` keeps `.ir`/`.ir.sig`
        // while dependents strip them. `synthesize_missing_eval_ir` MUST seed
        // `Base.ir*` into `.ir_synth` without adding `out_dir` to `LEAN_PATH`.
        let pb_partial = tmp.path().join("prebuilt_partial");
        fs::create_dir_all(pb_partial.join("lib/TestRoot")).unwrap();
        fs::create_dir_all(pb_partial.join("lib/SkipIrDep")).unwrap();
        for ext in LEAN_ARTIFACT_EXTS {
            let base_art = prebuilt.join(format!("lib/TestRoot/Base.{ext}"));
            if base_art.is_file() {
                fs::copy(&base_art, pb_partial.join(format!("lib/TestRoot/Base.{ext}"))).unwrap();
            }
        }
        for ext in ["olean", "olean.server", "olean.private"] {
            let skip_art = prebuilt.join(format!("lib/SkipIrDep/Leaf.{ext}"));
            if skip_art.is_file() {
                fs::copy(&skip_art, pb_partial.join(format!("lib/SkipIrDep/Leaf.{ext}"))).unwrap();
            }
            for stem in ["Child", "SynthHost"] {
                let src_art = prebuilt.join(format!("lib/TestRoot/{stem}.{ext}"));
                if src_art.is_file() {
                    fs::copy(&src_art, pb_partial.join(format!("lib/TestRoot/{stem}.{ext}")))
                        .unwrap();
                }
            }
        }
        let (partial_base_parts, partial_base_shas) = collect_test_prebuilt_parts_with_exts(
            &prebuilt,
            "lib/TestRoot/Base",
            LEAN_ARTIFACT_EXTS,
        );
        let partial_base_transitive =
            compute_transitive_module_sha256(&partial_base_shas, &[]).unwrap();
        let partial_child_transitive = compute_transitive_module_sha256(
            &child_part_shas,
            &[PrebuiltImport {
                module: "TestRoot.Base".to_owned(),
                is_exported: Some(true),
                import_all: Some(false),
                is_meta: Some(false),
                part_sha256s: partial_base_shas.clone(),
                transitive_sha256: partial_base_transitive.clone(),
            }],
        )
        .unwrap();
        let mut partial_manifest = child_manifest.clone();
        partial_manifest["entries"][1]["parts"] = serde_json::Value::Array(partial_base_parts);
        partial_manifest["entries"][2]["imports"][0]["part_sha256s"] =
            serde_json::json!(partial_base_shas);
        partial_manifest["entries"][2]["imports"][0]["transitive_sha256"] =
            serde_json::json!(partial_base_transitive);
        partial_manifest["entries"][3]["imports"][1]["transitive_sha256"] =
            serde_json::json!(partial_child_transitive);
        fs::write(
            pb_partial.join("manifest.json"),
            serde_json::to_vec_pretty(&partial_manifest).unwrap(),
        )
        .unwrap();
        let partial_out_dir = tmp.path().join("partial_ir_out");
        let partial_lock = tmp.path().join("partial_ir.lock");
        let (partial_paths, partial_status) = ensure_dag_with_overlay(
            &dag_v2,
            tmp.path(),
            &lean_bin,
            &lean_stdlib,
            Some(&pb_partial),
            &partial_out_dir,
            &partial_lock,
        )
        .expect("partially-stripped overlay must synthesize missing .ir companions cleanly");
        assert_eq!(partial_status, "staged:4/4");
        assert_eq!(
            sha256_file_hex(&partial_out_dir.join("TestRoot/Base.ir")).unwrap(),
            sha256_file_hex(&prebuilt.join("lib/TestRoot/Base.ir")).unwrap()
        );
        assert!(partial_out_dir.join("TestRoot/Child.ir").is_file());
        assert!(partial_out_dir.join("TestRoot/Child.ir.sig").is_file());
        assert!(partial_out_dir.join("TestRoot/SynthHost.ir").is_file());
        assert!(partial_out_dir.join("TestRoot/SynthHost.ir.sig").is_file());
        assert!(!partial_out_dir.join(".ir_synth").exists());
        assert!(!partial_paths.is_empty());

        child_manifest["entries"][2]["imports"][0]["transitive_sha256"] =
            serde_json::json!("f".repeat(64));
        fs::write(pb_v2.join("manifest.json"), serde_json::to_vec_pretty(&child_manifest).unwrap())
            .unwrap();
        let v2_tampered = inspect_prebuilt_overlay(
            Some(&pb_v2),
            &dag_v2,
            tmp.path(),
            &lean_bin,
            &active_sysroot_sha,
        )
        .unwrap();
        assert_eq!(v2_tampered.fallback_label, "staged:2/4");
        assert!(!v2_tampered.modules.contains_key("TestRoot.Child"));
        assert!(!v2_tampered.modules.contains_key("TestRoot.SynthHost"));

        // Modifying Base.lean without updating prebuilt/manifest.json MUST
        // invalidate prebuilt Base and recompile both from checkout source.
        fs::write(&base_src, "module\npublic def baseVal : Nat := 99\n").unwrap();
        let stale_out_dir = tmp.path().join("stale_out");
        let stale_lock = tmp.path().join("stale.lock");
        let (stale_paths, stale_status) = ensure_dag_with_overlay(
            &dag,
            tmp.path(),
            &lean_bin,
            &lean_stdlib,
            Some(&prebuilt),
            &stale_out_dir,
            &stale_lock,
        )
        .expect("modified source must compile fresh rather than failing on stale prebuilt");
        assert_eq!(stale_status, "skipped:digest_mismatch");

        let eval_probe = tmp.path().join("EvalChild.lean");
        fs::write(&eval_probe, "import TestRoot.Child\n#eval childVal\n").unwrap();
        let stale_lean_path = env::join_paths(&stale_paths).unwrap();
        let eval_res = run_supervised_cmd(
            &apply_lean_tool_env(
                Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                    .arg(&eval_probe)
                    .env("LEAN_PATH", &stale_lean_path),
                &lean_bin,
            ),
            tmp.path(),
            LEAN_EVAL_TIMEOUT_SECS,
            "eval fresh childVal",
        )
        .unwrap();
        assert!(
            matches!(eval_res.termination, Termination::Exited(s) if s.success()),
            "eval childVal failed: {}",
            eval_res.describe()
        );
        assert_eq!(String::from_utf8_lossy(&eval_res.stdout).trim(), "100");

        // Unstamped partial `.olean` garbage in `out_dir` MUST be wiped.
        let partial_out = tmp.path().join("partial_out");
        fs::create_dir_all(partial_out.join("TestRoot")).unwrap();
        fs::write(partial_out.join("TestRoot/Base.olean"), b"corrupt-partial-olean").unwrap();
        fs::write(partial_out.join("TestRoot/StaleJunk.txt"), b"leftover").unwrap();
        let partial_lock = tmp.path().join("partial.lock");
        let (_, clean_status) = ensure_dag_with_overlay(
            &dag,
            tmp.path(),
            &lean_bin,
            &lean_stdlib,
            None,
            &partial_out,
            &partial_lock,
        )
        .expect("unstamped partial cache must be wiped and rebuilt cleanly");
        assert_eq!(clean_status, "none");
        assert!(!partial_out.join("TestRoot/StaleJunk.txt").exists());
        assert!(partial_out.join(".anneal-oleans-ready").is_file());
    }

    #[test]
    fn body_exercises_move_then_reinit_rejects_copy_or_zst_and_accepts_non_zst_move() {
        let non_zst_enum = serde_json::json!({
            "kind": "enum",
            "id": 1,
            "discr_width": "i16",
            "discr_signed": true,
            "tag_repr": { "kind": "scalar", "width": "i16", "signed": true },
            "discriminants": ["65534", "0", "7"]
        });
        let zst_enum = serde_json::json!({
            "kind": "enum",
            "id": 2,
            "discr_width": "u8",
            "discr_signed": false,
            "tag_repr": { "kind": "zero_sized" },
            "discriminants": ["42"]
        });
        let i16_ty = serde_json::json!({ "kind": "int", "width": "i16", "signed": true });
        let u32_ty = serde_json::json!({ "kind": "int", "width": "i32", "signed": false });

        let valid_move_reinit = CaptureBody {
            identity: "probe::move_then_reinit".to_owned(),
            arg_count: 2,
            local_tys: vec![
                i16_ty.clone(),
                non_zst_enum.clone(),
                non_zst_enum.clone(),
                non_zst_enum.clone(),
                non_zst_enum,
            ],
            blocks: vec![CaptureBlock {
                statements: vec![
                    serde_json::json!({
                        "kind": "assign",
                        "local": 3,
                        "value": { "kind": "use", "operand": { "kind": "move", "local": 1 }, "with_retag": true }
                    }),
                    serde_json::json!({
                        "kind": "assign",
                        "local": 4,
                        "value": { "kind": "use", "operand": { "kind": "move", "local": 3 }, "with_retag": true }
                    }),
                    serde_json::json!({
                        "kind": "assign",
                        "local": 3,
                        "value": { "kind": "use", "operand": { "kind": "copy", "local": 2 }, "with_retag": true }
                    }),
                    serde_json::json!({
                        "kind": "assign",
                        "local": 0,
                        "value": { "kind": "discriminant", "place": { "local": 3, "projection": [] } }
                    }),
                ],
                terminator: serde_json::json!({ "kind": "ret" }),
            }],
        };
        assert!(body_exercises_move_then_reinit(&valid_move_reinit));

        // Reading a moved-out enum via `Discriminant { place }` before
        // reinitialization must reset stage tracking and fail cleanly.
        let mut disc_stmts = valid_move_reinit.blocks[0].statements.clone();
        disc_stmts.insert(
            2,
            serde_json::json!({
                "kind": "assign",
                "local": 4,
                "value": { "kind": "discriminant", "place": { "local": 3, "projection": [] } }
            }),
        );
        let discriminant_while_moved = CaptureBody {
            identity: "probe::disc_while_moved".to_owned(),
            arg_count: valid_move_reinit.arg_count,
            local_tys: valid_move_reinit.local_tys.clone(),
            blocks: vec![CaptureBlock {
                statements: disc_stmts,
                terminator: serde_json::json!({ "kind": "ret" }),
            }],
        };
        assert!(!body_exercises_move_then_reinit(&discriminant_while_moved));

        // Copy-only lowering (like the old `u32` `move_then_reinit`) must fail.
        let copy_only = CaptureBody {
            identity: "probe::old_copy_only".to_owned(),
            arg_count: 1,
            local_tys: vec![u32_ty.clone(), u32_ty.clone(), u32_ty.clone(), u32_ty],
            blocks: vec![CaptureBlock {
                statements: vec![
                    serde_json::json!({
                        "kind": "assign",
                        "local": 2,
                        "value": { "kind": "use", "operand": { "kind": "copy", "local": 1 }, "with_retag": true }
                    }),
                    serde_json::json!({
                        "kind": "assign",
                        "local": 3,
                        "value": { "kind": "use", "operand": { "kind": "copy", "local": 2 }, "with_retag": true }
                    }),
                    serde_json::json!({
                        "kind": "assign",
                        "local": 2,
                        "value": { "kind": "use", "operand": { "kind": "copy", "local": 3 }, "with_retag": true }
                    }),
                    serde_json::json!({
                        "kind": "assign",
                        "local": 0,
                        "value": { "kind": "use", "operand": { "kind": "copy", "local": 2 }, "with_retag": true }
                    }),
                ],
                terminator: serde_json::json!({ "kind": "ret" }),
            }],
        };
        assert!(!body_exercises_move_then_reinit(&copy_only));

        // Zero-sized enum local does not deinitialize on `Operand::Move`.
        let zst_only = CaptureBody {
            identity: "probe::zst_move".to_owned(),
            arg_count: 1,
            local_tys: vec![i16_ty, zst_enum.clone(), zst_enum.clone(), zst_enum],
            blocks: valid_move_reinit.blocks,
        };
        assert!(!body_exercises_move_then_reinit(&zst_only));
    }

    #[test]
    fn decoupled_eval_and_wp_probes_preserve_structured_verdicts_on_semantic_regression() {
        let mut body_ids_by_fn = BTreeMap::new();
        body_ids_by_fn.insert("ok_fn".to_owned(), 0usize);
        body_ids_by_fn.insert("regressed_val_fn".to_owned(), 1usize);
        body_ids_by_fn.insert("missed_ub_fn".to_owned(), 2usize);
        let mut kernel_whnf_eligible_by_fn = BTreeMap::new();
        kernel_whnf_eligible_by_fn.insert("ok_fn".to_owned(), true);
        kernel_whnf_eligible_by_fn.insert("regressed_val_fn".to_owned(), true);
        kernel_whnf_eligible_by_fn.insert("missed_ub_fn".to_owned(), true);

        let captured = CapturedModule {
            capture_dir: PathBuf::from("/tmp/cap"),
            capture_json: PathBuf::from("/tmp/cap/capture.json"),
            captured_lean: PathBuf::from("/tmp/cap/Captured.lean"),
            olean_dir: PathBuf::from("/tmp/cap/olean"),
            body_ids_by_fn,
            kernel_whnf_eligible_by_fn,
            kernel_whnf_ub_sysroot_by_fn: BTreeMap::new(),
            move_reinit_fns: BTreeSet::new(),
        };

        let make_case =
            |id: &str, func: &str, expected: Expectation, ret: Option<u128>| LitmusCase {
                id: id.to_owned(),
                source_rel: PathBuf::from("src/a.rs"),
                source_abs: PathBuf::from("/tmp/src/a.rs"),
                function: func.to_owned(),
                category: "arith".to_owned(),
                expected,
                miri_ub_contains: None,
                expected_miri: None,
                args: vec![MirValue::Int { int_kind: IntKind::U32, bits: 1 }],
                expected_return: ret.map(|bits| MirValue::Int { int_kind: IntKind::U32, bits }),
                fuel: 8,
            };

        let c_ok = make_case("c_ok", "ok_fn", Expectation::Pass, Some(2));
        let c_val_reg = make_case("c_val_reg", "regressed_val_fn", Expectation::Pass, Some(2));
        let c_missed_ub = make_case("c_missed_ub", "missed_ub_fn", Expectation::Ub, None);
        let cases = vec![&c_ok, &c_val_reg, &c_missed_ub];

        let eval_src = generate_lean_eval_probe(&captured, &cases).expect("generate eval probe");
        assert!(eval_src.contains("#eval runCase \"c_ok\""));
        assert!(eval_src.contains("#eval runCase \"c_val_reg\""));
        assert!(eval_src.contains("#eval runCase \"c_missed_ub\""));
        assert!(
            !eval_src.contains("theorem wp_"),
            "Probe.lean must omit kernel WP theorems so semantic regressions do not abort #eval"
        );

        let mut raw_outcomes = BTreeMap::new();
        raw_outcomes.insert(
            "c_ok".to_owned(),
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 2 } },
        );
        raw_outcomes.insert(
            "c_val_reg".to_owned(),
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 99 } },
        );
        raw_outcomes.insert(
            "c_missed_ub".to_owned(),
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 0 } },
        );

        let wp_cands = select_wp_kernel_candidates(&captured, &cases, &raw_outcomes);
        assert_eq!(wp_cands.len(), 1);
        assert_eq!(wp_cands[0].id, "c_ok");

        let wp_src = generate_lean_wp_probe(&captured, &wp_cands).expect("generate WP probe");
        assert!(wp_src.contains("theorem wp_pass_check_0"));
        assert!(!wp_src.contains("#eval runCase"));
    }

    #[test]
    fn sysroot_call_wp_eligibility_admits_ub_only() {
        let two_block_sysroot = CaptureBody {
            identity: "probe::u32_unchecked_add".to_owned(),
            arg_count: 2,
            local_tys: vec![],
            blocks: vec![
                CaptureBlock {
                    statements: vec![],
                    terminator: serde_json::json!({
                        "kind": "sysroot_call",
                        "op": { "kind": "unchecked_add", "ty": { "kind": "int", "width": "i32", "signed": false } },
                        "args": [],
                        "dst": 0,
                        "target": 1,
                        "unwind": "continue"
                    }),
                },
                CaptureBlock {
                    statements: vec![
                        serde_json::json!({ "kind": "storage_dead", "local": 3 }),
                        serde_json::json!({ "kind": "storage_dead", "local": 4 }),
                    ],
                    terminator: serde_json::json!({ "kind": "ret" }),
                },
            ],
        };
        assert!(!is_single_block_kernel_whnf(&two_block_sysroot));
        assert!(is_sysroot_ub_kernel_whnf(&two_block_sysroot));

        let non_sysroot_two_block = CaptureBody {
            identity: "probe::goto_ret".to_owned(),
            arg_count: 1,
            local_tys: vec![],
            blocks: vec![
                CaptureBlock {
                    statements: vec![],
                    terminator: serde_json::json!({ "kind": "goto", "block": 1 }),
                },
                CaptureBlock {
                    statements: vec![
                        serde_json::json!({ "kind": "storage_dead", "local": 3 }),
                        serde_json::json!({ "kind": "storage_dead", "local": 4 }),
                    ],
                    terminator: serde_json::json!({ "kind": "ret" }),
                },
            ],
        };
        assert!(!is_sysroot_ub_kernel_whnf(&non_sysroot_two_block));

        let mut body_ids_by_fn = BTreeMap::new();
        body_ids_by_fn.insert("sys_fn".to_owned(), 0usize);
        let mut kernel_whnf_eligible_by_fn = BTreeMap::new();
        kernel_whnf_eligible_by_fn.insert("sys_fn".to_owned(), false);
        let mut kernel_whnf_ub_sysroot_by_fn = BTreeMap::new();
        kernel_whnf_ub_sysroot_by_fn.insert("sys_fn".to_owned(), true);

        let captured = CapturedModule {
            capture_dir: PathBuf::from("/tmp/cap"),
            capture_json: PathBuf::from("/tmp/cap/capture.json"),
            captured_lean: PathBuf::from("/tmp/cap/Captured.lean"),
            olean_dir: PathBuf::from("/tmp/cap/olean"),
            body_ids_by_fn,
            kernel_whnf_eligible_by_fn,
            kernel_whnf_ub_sysroot_by_fn,
            move_reinit_fns: BTreeSet::new(),
        };

        let c_pass = LitmusCase {
            id: "c_sys_pass".to_owned(),
            source_rel: PathBuf::from("src/u.rs"),
            source_abs: PathBuf::from("/tmp/src/u.rs"),
            function: "sys_fn".to_owned(),
            category: "arith".to_owned(),
            expected: Expectation::Pass,
            miri_ub_contains: None,
            expected_miri: None,
            args: vec![MirValue::Int { int_kind: IntKind::U32, bits: 1 }],
            expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 2 }),
            fuel: 16,
        };
        let c_ub = LitmusCase {
            id: "c_sys_ub".to_owned(),
            source_rel: PathBuf::from("src/u.rs"),
            source_abs: PathBuf::from("/tmp/src/u.rs"),
            function: "sys_fn".to_owned(),
            category: "ub".to_owned(),
            expected: Expectation::Ub,
            miri_ub_contains: Some("arithmetic overflow".to_owned()),
            expected_miri: None,
            args: vec![MirValue::Int { int_kind: IntKind::U32, bits: u32::MAX as u128 }],
            expected_return: None,
            fuel: 16,
        };
        let cases = vec![&c_pass, &c_ub];

        let mut raw_outcomes = BTreeMap::new();
        raw_outcomes.insert(
            "c_sys_pass".to_owned(),
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 2 } },
        );
        raw_outcomes.insert(
            "c_sys_ub".to_owned(),
            ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
        );

        let wp_cands = select_wp_kernel_candidates(&captured, &cases, &raw_outcomes);
        assert_eq!(wp_cands.len(), 1);
        assert_eq!(wp_cands[0].id, "c_sys_ub");

        let wp_src = generate_lean_wp_probe(&captured, &wp_cands).expect("generate UB WP probe");
        assert!(wp_src.contains("theorem wp_ub_check_0"));
        assert!(!wp_src.contains("wp_pass_check"));
    }

    #[test]
    fn wp_trace_parser_and_split_generator_emit_segmented_theorems() {
        let stdout = "\"ANNEAL_LEAN_TRACE:c_ok:8|0@{ s0 }|3@{ s3 }|6@{ s6 }\"\n\
                      \"ANNEAL_LEAN_TRACE:c_skip:SKIP\"\n";
        let traces = parse_lean_wp_traces(stdout).expect("parse valid WP trace");
        assert_eq!(traces.len(), 1);
        let tr = traces.get("c_ok").expect("c_ok trace");
        assert_eq!(tr.total_steps, 8);
        assert_eq!(tr.checkpoints.len(), 3);

        let mut body_ids_by_fn = BTreeMap::new();
        body_ids_by_fn.insert("ok_fn".to_owned(), 0usize);
        let captured = CapturedModule {
            capture_dir: PathBuf::from("/tmp/cap"),
            capture_json: PathBuf::from("/tmp/cap/capture.json"),
            captured_lean: PathBuf::from("/tmp/cap/Captured.lean"),
            olean_dir: PathBuf::from("/tmp/cap/olean"),
            body_ids_by_fn,
            kernel_whnf_eligible_by_fn: BTreeMap::new(),
            kernel_whnf_ub_sysroot_by_fn: BTreeMap::new(),
            move_reinit_fns: BTreeSet::new(),
        };
        let c_ok = LitmusCase {
            id: "c_ok".to_owned(),
            source_rel: PathBuf::from("src/a.rs"),
            source_abs: PathBuf::from("/tmp/src/a.rs"),
            function: "ok_fn".to_owned(),
            category: "arith".to_owned(),
            expected: Expectation::Pass,
            miri_ub_contains: None,
            expected_miri: None,
            args: vec![MirValue::Int { int_kind: IntKind::U32, bits: 1 }],
            expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 4 }),
            fuel: 200,
        };
        let wp_src = generate_lean_wp_probe_with_traces(&captured, &[&c_ok], &traces)
            .expect("generate split WP probe");
        assert!(wp_src.contains("private def wp_st_0_0 : State := { s0 }"));
        assert!(wp_src.contains("private theorem wp_seg_0_0"));
        assert!(wp_src.contains("private theorem wp_tail_0"));
        assert!(wp_src.contains("evalFuel_split (n1 := 3) (n2 := 5) rfl wp_seg_0_0"));
        assert!(wp_src.contains("evalFuel_split (n1 := 3) (n2 := 2) rfl wp_seg_0_1 wp_tail_0"));
        assert!(wp_src.contains("wpProg_of_evalMirFuelTotal (s0 := wp_st_0_0) rfl"));

        // Single-checkpoint trace (`total_steps = 1`) emits `wp_tail` directly.
        let short_traces = parse_lean_wp_traces("\"ANNEAL_LEAN_TRACE:c_ok:1|0@{ s0 }\"\n").unwrap();
        let short_src =
            generate_lean_wp_probe_with_traces(&captured, &[&c_ok], &short_traces).unwrap();
        assert!(short_src.contains("private theorem wp_tail_0"));
        assert!(!short_src.contains("wp_seg_0_"));

        // Malformed / duplicate traces must fail closed.
        for bad_stdout in [
            "\"ANNEAL_LEAN_TRACE::SKIP\"\n",
            "\"ANNEAL_LEAN_TRACE::1|0@{ s0 }\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:\"\n",
            "\"ANNEAL_LEAN_TRACE:no_colon\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:8|0@{ s0 }\"\n\"ANNEAL_LEAN_TRACE:c_ok:8|0@{ s0 }\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:SKIP\"\n\"ANNEAL_LEAN_TRACE:c_ok:8|0@{ s0 }\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:8|0@{ s0 }\"\n\"ANNEAL_LEAN_TRACE:c_ok:SKIP\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:SKIP\"\n\"ANNEAL_LEAN_TRACE:c_ok:SKIP\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:0|0@{ s0 }\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:3|1@{ s1 }\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:8|0@{ s0 }|3@{ s3 }|3@{ s3 }\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:3|0@{ s0 }|3@{ s3 }\"\n",
            "\"ANNEAL_LEAN_TRACE:c_ok:3|0@\"\n",
        ] {
            assert!(
                parse_lean_wp_traces(bad_stdout).is_err(),
                "expected parse failure for {bad_stdout:?}"
            );
        }
    }
}
