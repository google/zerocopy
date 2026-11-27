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
    collections::{BTreeMap, BTreeSet, VecDeque},
    env,
    ffi::{OsStr, OsString},
    fmt::Write as _,
    fs::{self, File},
    io::Read as _,
    path::{Component, Path, PathBuf},
    sync::Arc,
    thread,
    time::{Duration, Instant},
};

use anneal_testkit::{Invocation, ProcessOutcome, Termination, ToolchainEnv};
use serde::{Deserialize, Serialize};
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
    pub(crate) lean_ld_library_path: String,
    pub(crate) lean_child_path: OsString,
    pub(crate) validated_tmpdir: Option<PathBuf>,
    pub(crate) _rust_sysroot_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
    pub(crate) _capture_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
    pub(crate) _lean_lib_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
    pub(crate) _lean_stdlib_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
    pub(crate) _lean_dag_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
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

/// Serialized captured MIR body slice for a Stage-2 fuzz case, allowing the
/// Python report verifier to recompute `capture_body_sha256` and cross-check
/// the captured function identity, parameter count, local types, and blocks
/// against the regenerated Rust source.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuzzCaptureBody {
    pub body_id: usize,
    pub fn_identity: String,
    pub arg_count: usize,
    pub local_tys: Vec<serde_json::Value>,
    pub blocks: Vec<serde_json::Value>,
    pub capture_body_sha256: String,
}

/// Stage-2 Lean evaluation result for one generated program, retaining capture
/// provenance for optional Leg 3 (`anneal-mir-eval`) cross-checking and
/// distinguishing capture-time refusal from runtime evaluation outcomes.
#[derive(Clone, Debug)]
pub struct FuzzLeanCaseResult {
    pub outcome: ObservedOutcome,
    pub capture_rejected: Option<String>,
    pub capture_refusal_json: Option<String>,
    pub capture_json: Option<PathBuf>,
    pub capture_body: Option<FuzzCaptureBody>,
    pub lean_probe_line: Option<String>,
    pub exercised_move_reinit: bool,
    pub move_reinit_evidence: Option<MoveReinitEvidence>,
}

/// Exact step and MIR coordinate in the captured body for one move/reinit
/// transition observed during concrete Lean `evalMirStepBy` execution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveReinitStep {
    pub step: usize,
    pub block: usize,
    pub stmt: usize,
}

/// Tamper-checked execution and captured-MIR witness proving a Stage-2 fuzz
/// case initialized, moved via `Operand::Move` (deinitializing), reinitialized,
/// and read a non-ZST local during concrete Lean evaluation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveReinitEvidence {
    pub body_id: usize,
    pub fn_identity: String,
    pub local_slot: usize,
    pub arg_count: usize,
    pub local_tys: Vec<serde_json::Value>,
    pub blocks: Vec<serde_json::Value>,
    pub total_steps: usize,
    pub init_step: MoveReinitStep,
    pub move_step: MoveReinitStep,
    pub reinit_step: MoveReinitStep,
    pub read_step: MoveReinitStep,
    pub lean_probe_line: String,
    pub capture_body_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedLeanFuzzProbeLine {
    body_id: Option<usize>,
    fn_identity: Option<String>,
    outcome: ObservedOutcome,
    lean_probe_line: Option<String>,
    move_reinit: Option<ParsedLeanMoveReinit>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedLeanMoveReinit {
    local_slot: usize,
    total_steps: usize,
    init_step: MoveReinitStep,
    move_step: MoveReinitStep,
    reinit_step: MoveReinitStep,
    read_step: MoveReinitStep,
}

#[derive(Deserialize)]
struct CaptureStatusOk {
    status: String,
    capture: PathBuf,
    lean: PathBuf,
    #[serde(default)]
    capture_shards: Option<PathBuf>,
}

#[derive(Deserialize)]
struct CaptureShardsManifest {
    shards: Vec<CaptureShardEntry>,
}

#[derive(Debug, Deserialize)]
struct CaptureShardEntry {
    shard_idx: usize,
    capture_module: String,
}

struct CaptureCompileEnv<'a> {
    out_dir: &'a Path,
    lean_path: &'a str,
    work_dir: &'a Path,
    deadline: Option<Instant>,
}

#[derive(Deserialize)]
struct CaptureManifest {
    program: CaptureProgram,
}

#[derive(Deserialize)]
struct CaptureProgram {
    bodies: Vec<CaptureBody>,
}

#[derive(Clone, Deserialize, Serialize)]
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

#[derive(Clone, Deserialize, Serialize)]
pub(crate) struct CaptureBody {
    pub(crate) identity: String,
    pub(crate) arg_count: usize,
    pub(crate) local_tys: Vec<serde_json::Value>,
    pub(crate) blocks: Vec<CaptureBlock>,
}

fn write_canonical_json(val: &serde_json::Value, out: &mut String) {
    match val {
        serde_json::Value::Null => out.push_str("null"),
        serde_json::Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        serde_json::Value::Number(n) => out.push_str(&n.to_string()),
        serde_json::Value::String(s) => {
            out.push_str(&serde_json::to_string(s).unwrap_or_else(|_| "\"\"".to_owned()));
        }
        serde_json::Value::Array(items) => {
            out.push('[');
            for (idx, item) in items.iter().enumerate() {
                if idx > 0 {
                    out.push(',');
                }
                write_canonical_json(item, out);
            }
            out.push(']');
        }
        serde_json::Value::Object(map) => {
            let mut keys: Vec<&str> = map.keys().map(String::as_str).collect();
            keys.sort_unstable();
            out.push('{');
            for (idx, k) in keys.iter().enumerate() {
                if idx > 0 {
                    out.push(',');
                }
                out.push_str(&serde_json::to_string(k).unwrap_or_else(|_| "\"\"".to_owned()));
                out.push(':');
                write_canonical_json(&map[*k], out);
            }
            out.push('}');
        }
    }
}

pub(crate) fn compute_capture_body_sha256(
    fn_identity: &str,
    arg_count: usize,
    local_tys: &[serde_json::Value],
    blocks: &[serde_json::Value],
) -> String {
    let payload = serde_json::json!({
        "identity": fn_identity,
        "arg_count": arg_count,
        "local_tys": local_tys,
        "blocks": blocks,
    });
    let mut canonical = String::new();
    write_canonical_json(&payload, &mut canonical);
    let mut hasher = Sha256::new();
    hasher.update(canonical.as_bytes());
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(hex, "{b:02x}");
    }
    hex
}

fn block_action_at<'a>(
    blocks: &'a [serde_json::Value],
    coord: &MoveReinitStep,
    label: &str,
) -> Result<(bool, &'a serde_json::Value), String> {
    let block = blocks
        .get(coord.block)
        .ok_or_else(|| format!("{label} block {} out of bounds ({})", coord.block, blocks.len()))?;
    let stmts = block
        .get("statements")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| format!("{label} block {} missing statements array", coord.block))?;
    if coord.stmt < stmts.len() {
        Ok((false, &stmts[coord.stmt]))
    } else if coord.stmt == stmts.len() {
        let term = block
            .get("terminator")
            .ok_or_else(|| format!("{label} block {} missing terminator", coord.block))?;
        if term.is_null() {
            return Err(format!("{label} block {} has null terminator", coord.block));
        }
        Ok((true, term))
    } else {
        Err(format!(
            "{label} stmt {} out of bounds for block {} (stmts={})",
            coord.stmt,
            coord.block,
            stmts.len()
        ))
    }
}

fn stmt_writes_local(stmt: &serde_json::Value, target_local: u64) -> Option<bool> {
    match stmt.get("kind").and_then(serde_json::Value::as_str)? {
        "assign" => {
            Some(stmt.get("local").and_then(serde_json::Value::as_u64) == Some(target_local))
        }
        "assign_place" => {
            let p = stmt.get("place")?;
            let proj_empty = p
                .get("projection")
                .and_then(serde_json::Value::as_array)
                .is_some_and(Vec::is_empty);
            Some(
                proj_empty
                    && p.get("local").and_then(serde_json::Value::as_u64) == Some(target_local),
            )
        }
        _ => Some(false),
    }
}

fn operand_moves_local(op: &serde_json::Value, target_local: u64) -> bool {
    match op.get("kind").and_then(serde_json::Value::as_str) {
        Some("move") => op.get("local").and_then(serde_json::Value::as_u64) == Some(target_local),
        Some("move_place") => {
            let Some(p) = op.get("place") else {
                return false;
            };
            let proj_empty = p
                .get("projection")
                .and_then(serde_json::Value::as_array)
                .is_some_and(Vec::is_empty);
            proj_empty && p.get("local").and_then(serde_json::Value::as_u64) == Some(target_local)
        }
        _ => false,
    }
}

fn operand_reads_local_any(op: &serde_json::Value, target_local: u64) -> bool {
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
}

fn rvalue_reads_local_extended(rvalue: &serde_json::Value, target_local: u64) -> bool {
    if rvalue_reads_local(rvalue, target_local) {
        return true;
    }
    match rvalue.get("kind").and_then(serde_json::Value::as_str) {
        Some("aggregate_tuple") => {
            rvalue.get("fields").and_then(serde_json::Value::as_array).is_some_and(|fields| {
                fields.iter().any(|op| operand_reads_local_any(op, target_local))
            })
        }
        Some("aggregate_range_to") => {
            rvalue.get("end").is_some_and(|op| operand_reads_local_any(op, target_local))
        }
        Some("aggregate_range_from") => {
            rvalue.get("start").is_some_and(|op| operand_reads_local_any(op, target_local))
        }
        _ => false,
    }
}

fn term_reads_local(term: &serde_json::Value, target_local: u64) -> bool {
    match term.get("kind").and_then(serde_json::Value::as_str) {
        Some("switch_int") => {
            term.get("operand").is_some_and(|op| operand_reads_local_any(op, target_local))
        }
        Some("assert") => {
            term.get("cond").is_some_and(|op| operand_reads_local_any(op, target_local))
        }
        Some("core_call" | "call" | "sysroot_call") => term
            .get("args")
            .and_then(serde_json::Value::as_array)
            .is_some_and(|args| args.iter().any(|op| operand_reads_local_any(op, target_local))),
        _ => false,
    }
}

fn block_successors(term: &serde_json::Value) -> Vec<usize> {
    let mut succs = Vec::new();
    match term.get("kind").and_then(serde_json::Value::as_str) {
        Some("goto") => {
            if let Some(b) = term.get("block").and_then(serde_json::Value::as_u64) {
                succs.push(b as usize);
            }
        }
        Some("switch_int") => {
            if let Some(targets) = term.get("targets").and_then(serde_json::Value::as_array) {
                for pair in targets {
                    if let Some(arr) = pair.as_array()
                        && let Some(b) = arr.get(1).and_then(serde_json::Value::as_u64)
                    {
                        succs.push(b as usize);
                    }
                }
            }
            if let Some(b) = term.get("otherwise").and_then(serde_json::Value::as_u64) {
                succs.push(b as usize);
            }
        }
        Some("assert" | "core_call" | "call" | "sysroot_call") => {
            if let Some(b) = term.get("target").and_then(serde_json::Value::as_u64) {
                succs.push(b as usize);
            }
        }
        _ => {}
    }
    succs
}

fn cfg_can_reach(
    blocks: &[serde_json::Value],
    from_block: usize,
    to_block: usize,
    allow_zero_edges: bool,
) -> bool {
    if allow_zero_edges && from_block == to_block {
        return true;
    }
    let mut seen = BTreeSet::new();
    let mut queue = VecDeque::new();
    let Some(first_term) = blocks.get(from_block).and_then(|b| b.get("terminator")) else {
        return false;
    };
    for s in block_successors(first_term) {
        if s < blocks.len() && seen.insert(s) {
            queue.push_back(s);
        }
    }
    while let Some(cur) = queue.pop_front() {
        if cur == to_block {
            return true;
        }
        if let Some(term) = blocks.get(cur).and_then(|b| b.get("terminator")) {
            for s in block_successors(term) {
                if s < blocks.len() && seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
    }
    false
}

fn cfg_step_follows(blocks: &[serde_json::Value], a: &MoveReinitStep, b: &MoveReinitStep) -> bool {
    if a.block == b.block && a.stmt < b.stmt {
        return true;
    }
    cfg_can_reach(blocks, a.block, b.block, a.block != b.block)
}

/// Independently verify every execution-trace and captured-MIR invariant of
/// [`MoveReinitEvidence`] against `fn_name` and `arg_count`.
pub(crate) fn verify_move_reinit_evidence(
    ev: &MoveReinitEvidence,
    case_id: &str,
    fn_name: &str,
    arg_count: usize,
) -> Result<(), String> {
    let matches_fn = ev.fn_identity == fn_name
        || ev.fn_identity == format!("rust-path-v1::{fn_name}")
        || ev.fn_identity.ends_with(&format!("::{fn_name}"));
    if !matches_fn {
        return Err(format!(
            "move_reinit_evidence fn_identity {:?} does not match {:?}",
            ev.fn_identity, fn_name
        ));
    }
    if ev.arg_count != arg_count {
        return Err(format!("move_reinit_evidence arg_count {} != {}", ev.arg_count, arg_count));
    }
    if ev.local_slot <= ev.arg_count || ev.local_slot >= ev.local_tys.len() {
        return Err(format!(
            "move_reinit_evidence local_slot {} invalid for arg_count={}, locals={}",
            ev.local_slot,
            ev.arg_count,
            ev.local_tys.len()
        ));
    }
    if !is_non_zst_captured_ty(&ev.local_tys[ev.local_slot]) {
        return Err(format!(
            "move_reinit_evidence local_slot {} has zero-sized/unsupported type {}",
            ev.local_slot, ev.local_tys[ev.local_slot]
        ));
    }
    if !(ev.init_step.step < ev.move_step.step
        && ev.move_step.step < ev.reinit_step.step
        && ev.reinit_step.step < ev.read_step.step
        && ev.read_step.step < ev.total_steps)
    {
        return Err("move_reinit_evidence step timestamps are not strictly increasing".to_owned());
    }
    let expected_sha =
        compute_capture_body_sha256(&ev.fn_identity, ev.arg_count, &ev.local_tys, &ev.blocks);
    if ev.capture_body_sha256 != expected_sha {
        return Err("move_reinit_evidence capture_body_sha256 mismatch".to_owned());
    }
    let expected_probe_prefix = format!(
        "ANNEAL_LEAN_CASE:{case_id}:BODY|{}|{}|MR1|{}|{}|{},{},{}|{},{},{}|{},{},{}|{},{},{}:",
        ev.body_id,
        ev.fn_identity,
        ev.local_slot,
        ev.total_steps,
        ev.init_step.step,
        ev.init_step.block,
        ev.init_step.stmt,
        ev.move_step.step,
        ev.move_step.block,
        ev.move_step.stmt,
        ev.reinit_step.step,
        ev.reinit_step.block,
        ev.reinit_step.stmt,
        ev.read_step.step,
        ev.read_step.block,
        ev.read_step.stmt,
    );
    if !ev.lean_probe_line.starts_with(&expected_probe_prefix) {
        return Err(format!(
            "move_reinit_evidence lean_probe_line {:?} does not bind prefix {:?}",
            ev.lean_probe_line, expected_probe_prefix
        ));
    }
    let slot_u64 = ev.local_slot as u64;
    let (init_is_term, init_act) = block_action_at(&ev.blocks, &ev.init_step, "init")?;
    if init_is_term || stmt_writes_local(init_act, slot_u64) != Some(true) {
        return Err("move_reinit_evidence init step does not assign local_slot".to_owned());
    }
    let (move_is_term, move_act) = block_action_at(&ev.blocks, &ev.move_step, "move")?;
    let moves_ok = if move_is_term {
        match move_act.get("kind").and_then(serde_json::Value::as_str) {
            Some("switch_int") => {
                move_act.get("operand").is_some_and(|op| operand_moves_local(op, slot_u64))
            }
            Some("assert") => {
                move_act.get("cond").is_some_and(|op| operand_moves_local(op, slot_u64))
            }
            Some("core_call" | "call" | "sysroot_call") => move_act
                .get("args")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|args| args.iter().any(|op| operand_moves_local(op, slot_u64))),
            _ => false,
        }
    } else if matches!(
        move_act.get("kind").and_then(serde_json::Value::as_str),
        Some("assign" | "assign_place")
    ) && stmt_writes_local(move_act, slot_u64) == Some(false)
    {
        let rv = move_act.get("value");
        rv.is_some_and(|r| {
            matches!(r.get("kind").and_then(serde_json::Value::as_str), Some("use" | "use_retag"))
                && r.get("operand").is_some_and(|op| operand_moves_local(op, slot_u64))
        })
    } else {
        false
    };
    if !moves_ok {
        return Err(
            "move_reinit_evidence move step is not an Operand::Move of local_slot".to_owned()
        );
    }
    let (reinit_is_term, reinit_act) = block_action_at(&ev.blocks, &ev.reinit_step, "reinit")?;
    if reinit_is_term || stmt_writes_local(reinit_act, slot_u64) != Some(true) {
        return Err("move_reinit_evidence reinit step does not reinitialize local_slot".to_owned());
    }
    let (read_is_term, read_act) = block_action_at(&ev.blocks, &ev.read_step, "read")?;
    let reads_ok = if read_is_term {
        term_reads_local(read_act, slot_u64)
    } else {
        matches!(
            read_act.get("kind").and_then(serde_json::Value::as_str),
            Some("assign" | "assign_place")
        ) && read_act.get("value").is_some_and(|r| rvalue_reads_local_extended(r, slot_u64))
    };
    if !reads_ok {
        return Err(
            "move_reinit_evidence read step does not read reinitialized local_slot".to_owned()
        );
    }
    if !cfg_can_reach(&ev.blocks, 0, ev.init_step.block, true)
        || !cfg_step_follows(&ev.blocks, &ev.init_step, &ev.move_step)
        || !cfg_step_follows(&ev.blocks, &ev.move_step, &ev.reinit_step)
        || !cfg_step_follows(&ev.blocks, &ev.reinit_step, &ev.read_step)
    {
        return Err(
            "move_reinit_evidence CFG blocks do not connect init -> move -> reinit -> read"
                .to_owned(),
        );
    }
    Ok(())
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
    match rvalue.get("kind").and_then(serde_json::Value::as_str) {
        Some("use" | "use_retag" | "unary" | "cast") => {
            rvalue.get("operand").is_some_and(|op| operand_reads_local_any(op, target_local))
        }
        Some("binary") => {
            rvalue.get("left").is_some_and(|op| operand_reads_local_any(op, target_local))
                || rvalue.get("right").is_some_and(|op| operand_reads_local_any(op, target_local))
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

/// Check whether a single-block straight-line `body` initializes a
/// non-argument, non-ZST local, moves out of it via
/// `Rvalue::Use(Operand::Move)` (deinitializing it), reinitializes that same
/// local, and subsequently reads or moves from it again.
///
/// Multi-block bodies are rejected here because basic-block order does not
/// establish reachability; Stage-2 fuzzing instead records move/reinit
/// coverage directly from the concrete `evalMirStepBy` execution trace.
pub(crate) fn body_exercises_move_then_reinit(body: &CaptureBody) -> bool {
    if body.blocks.len() != 1 {
        return false;
    }
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

pub(crate) fn effective_timeout_duration(
    default_secs: u64,
    deadline: Option<Instant>,
) -> Result<Duration, String> {
    let base = Duration::from_secs(effective_timeout_secs(default_secs)?);
    clamp_timeout_to_deadline(base, deadline)
}

pub(crate) fn clamp_timeout_to_deadline(
    base: Duration,
    deadline: Option<Instant>,
) -> Result<Duration, String> {
    let Some(dl) = deadline else {
        return Ok(base);
    };
    let now = Instant::now();
    if now >= dl {
        return Err("shrink wall-clock deadline exhausted before subprocess launch".to_owned());
    }
    Ok(base.min(dl.saturating_duration_since(now)).max(Duration::from_millis(1)))
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

pub(crate) fn run_supervised_cmd_in_tmp(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
    tmp_parent: Option<&Path>,
    context: &str,
) -> Result<ProcessOutcome, String> {
    crate::rustc_runner::run_supervised_in_tmp(
        inv,
        work_dir,
        Duration::from_secs(timeout_secs),
        tmp_parent,
        context,
    )
}

pub(crate) fn validated_system_child_path() -> Result<OsString, String> {
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let store_prefix = Path::new(crate::rustc_runner::STORE_PREFIX);
    let trusted_child_dirs: Vec<&Path> =
        crate::rustc_runner::TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
    crate::rustc_runner::build_child_path_with_bins(
        &[],
        None,
        store_prefix,
        &trusted_child_dirs,
        None,
        &caller_cwd,
    )
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug)]
pub(crate) struct PreparedLeanInvocation {
    pub(crate) inv: Invocation,
    pub(crate) validated_tmpdir: Option<PathBuf>,
    pub(crate) _staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
}

fn apply_prepared_lean_tool_env(
    mut inv: Invocation,
    ld_lib: &str,
    child_path: &OsStr,
    validated_tmpdir: Option<&Path>,
) -> Invocation {
    if !ld_lib.is_empty() {
        inv = inv.env("LD_LIBRARY_PATH", ld_lib);
    }
    inv = inv.env("PATH", child_path);
    if let Some(td) = validated_tmpdir {
        inv = inv.env("TMPDIR", td);
    }
    inv
}

fn rewrite_lean_invocation_executable(
    mut inv: Invocation,
    raw_lean_bin: &Path,
    staged_lean_bin: &Path,
    caller_cwd: &Path,
) -> Invocation {
    let raw_abs = if raw_lean_bin.is_absolute() {
        raw_lean_bin.to_path_buf()
    } else {
        caller_cwd.join(raw_lean_bin)
    };
    let inv_abs = if inv.executable.is_absolute() {
        inv.executable.clone()
    } else {
        caller_cwd.join(&inv.executable)
    };
    let bare_match = raw_lean_bin.file_name().is_some_and(|name| inv.executable == Path::new(name));
    if inv.executable == raw_lean_bin
        || bare_match
        || fs::canonicalize(&inv_abs).ok() == fs::canonicalize(&raw_abs).ok()
    {
        inv.executable = staged_lean_bin.to_path_buf();
    }
    inv
}

fn apply_lean_tool_env_validated(
    inv: Invocation,
    lean_bin: &Path,
    store_prefix: &Path,
    trusted_child_dirs: &[&Path],
    ambient_path: Option<&OsStr>,
    caller_cwd: &Path,
    validated_tmpdir: Option<PathBuf>,
) -> Result<PreparedLeanInvocation, String> {
    let prepared_libs =
        crate::rustc_runner::prepare_lean_library_path(lean_bin, store_prefix, caller_cwd)?;
    let valid_bin_dir = crate::rustc_runner::validated_store_aware_dir(
        &prepared_libs.bin_dir,
        store_prefix,
        caller_cwd,
        "Lean bin dir",
    )?;
    let raw_child_path = crate::rustc_runner::build_child_path_with_bins(
        &[&valid_bin_dir],
        None,
        store_prefix,
        trusted_child_dirs,
        ambient_path,
        caller_cwd,
    )?;
    let lean_guards = [prepared_libs._staging.as_ref()];
    let pinned_lean_bin = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
        &lean_guards,
        &prepared_libs.lean_bin,
    );
    let pinned_ld = if prepared_libs.ld_library_path.is_empty() {
        String::new()
    } else {
        crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
            &lean_guards,
            OsStr::new(&prepared_libs.ld_library_path),
        )?
        .to_string_lossy()
        .into_owned()
    };
    let pinned_child_path = crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
        &lean_guards,
        &raw_child_path,
    )?;
    let staged_inv = rewrite_lean_invocation_executable(
        apply_prepared_lean_tool_env(
            inv,
            &pinned_ld,
            &pinned_child_path,
            validated_tmpdir.as_deref(),
        ),
        lean_bin,
        &pinned_lean_bin,
        caller_cwd,
    );
    Ok(PreparedLeanInvocation {
        inv: staged_inv,
        validated_tmpdir,
        _staging: prepared_libs._staging,
    })
}

#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn apply_lean_tool_env_with_tmpdir(
    inv: Invocation,
    lean_bin: &Path,
    store_prefix: &Path,
    trusted_child_dirs: &[&Path],
    ambient_path: Option<&OsStr>,
    caller_cwd: &Path,
    tmpdir_env: Option<&OsStr>,
) -> Result<PreparedLeanInvocation, String> {
    let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
        tmpdir_env, caller_cwd, "TMPDIR",
    )?;
    apply_lean_tool_env_validated(
        inv,
        lean_bin,
        store_prefix,
        trusted_child_dirs,
        ambient_path,
        caller_cwd,
        validated_tmpdir,
    )
}

fn prepare_lean_tool_env(
    inv: Invocation,
    lean_bin: &Path,
    validated_tmpdir: Option<PathBuf>,
) -> Result<PreparedLeanInvocation, String> {
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let store_prefix = Path::new(crate::rustc_runner::STORE_PREFIX);
    let trusted_child_dirs: Vec<&Path> =
        crate::rustc_runner::TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
    let ambient_path = env::var_os("PATH");
    apply_lean_tool_env_validated(
        inv,
        lean_bin,
        store_prefix,
        &trusted_child_dirs,
        ambient_path.as_deref(),
        &caller_cwd,
        validated_tmpdir,
    )
}

fn run_lean_with_optional_env(
    inv: Invocation,
    lean_bin: &Path,
    work_dir: &Path,
    timeout_secs: u64,
    prepared_env: Option<LeanPreparedEnv<'_>>,
    validated_tmpdir: Option<&Path>,
    context: &str,
) -> Result<ProcessOutcome, String> {
    if let Some(env_cfg) = prepared_env {
        let prepared_inv = apply_prepared_lean_tool_env(
            inv,
            env_cfg.ld_library_path,
            env_cfg.child_path,
            env_cfg.validated_tmpdir,
        );
        return run_supervised_cmd_in_tmp(
            &prepared_inv,
            work_dir,
            timeout_secs,
            env_cfg.validated_tmpdir,
            context,
        );
    }
    run_lean_supervised_in_tmp(inv, lean_bin, work_dir, timeout_secs, validated_tmpdir, context)
}

fn run_lean_supervised_in_tmp(
    inv: Invocation,
    lean_bin: &Path,
    work_dir: &Path,
    timeout_secs: u64,
    validated_tmpdir: Option<&Path>,
    context: &str,
) -> Result<ProcessOutcome, String> {
    let prepared = prepare_lean_tool_env(inv, lean_bin, validated_tmpdir.map(Path::to_path_buf))?;
    run_supervised_cmd_in_tmp(
        &prepared.inv,
        work_dir,
        timeout_secs,
        prepared.validated_tmpdir.as_deref(),
        context,
    )
}

fn stage_immutable_lean_dir_in_tmp(
    src_dir: &Path,
    pinned: Option<(&crate::rustc_runner::PinnedPrivateDir, &Path)>,
    rel_subdir: &str,
    tmp_parent: Option<&Path>,
    label: &str,
) -> Result<(PathBuf, Arc<crate::rustc_runner::ImmutableStagingDir>), String> {
    let temp = crate::mir_eval_runner::build_temp_dir("anneal-lean-stage-", tmp_parent)?;
    let (_, staging) =
        crate::rustc_runner::ImmutableStagingDir::build_and_pin(temp, label, |_, pinned_root| {
            let dst = pinned_root.join(rel_subdir);
            if let Some((pin, rel_dir)) = pinned {
                pin.copy_rel_subtree_to(rel_dir, &dst, false, label)
            } else {
                crate::rustc_runner::copy_validated_subtree(src_dir, &dst, None, false, label)
            }
        })?;
    Ok((staging.root().join(rel_subdir), staging))
}

#[cfg_attr(not(test), allow(dead_code))]
fn resolve_immutable_lean_stdlib_in(
    lean_prefix: &Path,
    lean_bin: &Path,
    prepared_libs: &crate::rustc_runner::PreparedLeanLibs,
    store_prefix: &Path,
    caller_cwd: &Path,
    tmp_parent: Option<&Path>,
) -> Result<(PathBuf, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    let bin_prefix =
        lean_bin.parent().and_then(Path::parent).and_then(|p| fs::canonicalize(p).ok());
    if bin_prefix.as_deref() == Some(lean_prefix)
        && let Some(staged_lib_lean) = &prepared_libs.lib_lean_dir
    {
        return Ok((staged_lib_lean.clone(), None));
    }
    let stdlib_cand = lean_prefix.join("lib/lean");
    if let Some(res) = crate::rustc_runner::try_validate_store_contained_path(
        &stdlib_cand,
        store_prefix,
        caller_cwd,
        true,
        "lean stdlib",
    ) {
        let canon = res?;
        let canon_store =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
        crate::rustc_runner::validate_store_contained_dir_tree(
            &canon,
            &canon_store,
            &canon_store,
            "lean stdlib",
        )?;
        return Ok((canon, None));
    }
    let canon = crate::mir_eval_runner::validate_dir_path_no_symlinks(&stdlib_cand, caller_cwd)?;
    let (staged, guard) =
        stage_immutable_lean_dir_in_tmp(&canon, None, "lib/lean", tmp_parent, "lean stdlib")?;
    Ok((staged, Some(guard)))
}

#[derive(Clone, Copy)]
enum LeanCacheRoot<'a> {
    Path(&'a Path),
    Pinned(&'a crate::rustc_runner::PinnedPrivateDir),
}

impl LeanSession {
    pub(crate) fn apply_lean_env(&self, inv: Invocation) -> Invocation {
        apply_prepared_lean_tool_env(
            inv,
            &self.lean_ld_library_path,
            &self.lean_child_path,
            self.validated_tmpdir.as_deref(),
        )
    }

    /// Resolve `anneal-rustc-capture` and Lean 4.34.1, and ensure compiled
    /// `.olean` artifacts for `Anneal.MirTotal.{Ops,StepCore,ExecTotal}` exist
    /// in `cache_root`.
    pub fn prepare(
        anneal_root: &Path,
        tools: &ToolchainEnv,
        cache_root: &Path,
    ) -> Result<Self, String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let ambient_tmpdir = env::var_os("TMPDIR");
        Self::prepare_at(anneal_root, tools, cache_root, &caller_cwd, ambient_tmpdir.as_deref())
    }

    fn prepare_at(
        anneal_root: &Path,
        tools: &ToolchainEnv,
        cache_root: &Path,
        caller_cwd: &Path,
        tmpdir_env: Option<&OsStr>,
    ) -> Result<Self, String> {
        let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
            tmpdir_env, caller_cwd, "TMPDIR",
        )?;
        let store_prefix = Path::new(crate::rustc_runner::STORE_PREFIX);
        let prepared_sys = crate::rustc_runner::prepare_sysroot_binary_in(
            &tools.sysroot,
            &format!("bin/rustc{}", env::consts::EXE_SUFFIX),
            store_prefix,
            validated_tmpdir.as_deref(),
            "LeanSession rustc binary",
        )?;
        Self::prepare_from_sysroot_at_cache(
            anneal_root,
            tools,
            LeanCacheRoot::Path(cache_root),
            prepared_sys,
            caller_cwd,
            validated_tmpdir,
        )
    }

    pub(crate) fn prepare_from_sysroot(
        anneal_root: &Path,
        tools: &ToolchainEnv,
        cache_root: &Path,
        prepared_sys: crate::rustc_runner::PreparedSysroot,
    ) -> Result<Self, String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let ambient_tmpdir = env::var_os("TMPDIR");
        let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
            ambient_tmpdir.as_deref(),
            &caller_cwd,
            "TMPDIR",
        )?;
        Self::prepare_from_sysroot_at_cache(
            anneal_root,
            tools,
            LeanCacheRoot::Path(cache_root),
            prepared_sys,
            &caller_cwd,
            validated_tmpdir,
        )
    }

    pub(crate) fn prepare_from_sysroot_pinned(
        anneal_root: &Path,
        tools: &ToolchainEnv,
        cache_root: &crate::rustc_runner::PinnedPrivateDir,
        prepared_sys: crate::rustc_runner::PreparedSysroot,
    ) -> Result<Self, String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let ambient_tmpdir = env::var_os("TMPDIR");
        let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
            ambient_tmpdir.as_deref(),
            &caller_cwd,
            "TMPDIR",
        )?;
        Self::prepare_from_sysroot_at_cache(
            anneal_root,
            tools,
            LeanCacheRoot::Pinned(cache_root),
            prepared_sys,
            &caller_cwd,
            validated_tmpdir,
        )
    }

    fn prepare_from_sysroot_at_cache(
        anneal_root: &Path,
        tools: &ToolchainEnv,
        cache: LeanCacheRoot<'_>,
        prepared_sys: crate::rustc_runner::PreparedSysroot,
        caller_cwd: &Path,
        validated_tmpdir: Option<PathBuf>,
    ) -> Result<Self, String> {
        let store_prefix = Path::new(crate::rustc_runner::STORE_PREFIX);
        let trusted_child_dirs: Vec<&Path> =
            crate::rustc_runner::TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
        let raw_rust_sysroot = prepared_sys.sysroot;
        let raw_ld_library_path = prepared_sys.ld_library_path;
        let prepared_lean_libs = crate::rustc_runner::prepare_lean_runtime_library_path_in(
            &tools.lean,
            store_prefix,
            caller_cwd,
            validated_tmpdir.as_deref(),
        )?;
        let raw_lean_bin = prepared_lean_libs.lean_bin.clone();
        let valid_lean_bin_dir = crate::rustc_runner::validated_store_aware_dir(
            &prepared_lean_libs.bin_dir,
            store_prefix,
            caller_cwd,
            "Lean bin dir",
        )?;
        let valid_rust_bin = crate::rustc_runner::validated_store_aware_dir(
            &raw_rust_sysroot.join("bin"),
            store_prefix,
            caller_cwd,
            "LeanSession rust bin dir",
        )?;
        let ambient_path = env::var_os("PATH");
        let raw_child_path = crate::rustc_runner::build_child_path_with_bins(
            &[&valid_rust_bin],
            None,
            store_prefix,
            &trusted_child_dirs,
            ambient_path.as_deref(),
            caller_cwd,
        )?;
        let raw_lean_child_path = crate::rustc_runner::build_child_path_with_bins(
            &[&valid_lean_bin_dir],
            None,
            store_prefix,
            &trusted_child_dirs,
            ambient_path.as_deref(),
            caller_cwd,
        )?;
        let raw_capture_bin = resolve_explicit_capture_bin(tools)?;
        let (raw_capture_bin, capture_staging) =
            crate::rustc_runner::stage_immutable_named_executable(
                &raw_capture_bin,
                store_prefix,
                caller_cwd,
                validated_tmpdir.as_deref(),
                "capture binary",
            )?;

        let lean_guards = [prepared_lean_libs._staging.as_ref()];
        let lean_bin = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
            &lean_guards,
            &raw_lean_bin,
        );
        let lean_ld_library_path = if prepared_lean_libs.ld_library_path.is_empty() {
            String::new()
        } else {
            crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
                &lean_guards,
                OsStr::new(&prepared_lean_libs.ld_library_path),
            )?
            .to_string_lossy()
            .into_owned()
        };
        let lean_child_path = crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
            &lean_guards,
            &raw_lean_child_path,
        )?;

        let prebuilt_dir = env::var_os("ANNEAL_TEST_INSTALL_ROOT")
            .filter(|v| !v.is_empty())
            .map(|r| PathBuf::from(r).join("share/anneal/prebuilt"));
        let lean_tool_env = LeanPreparedEnv {
            ld_library_path: &lean_ld_library_path,
            child_path: &lean_child_path,
            validated_tmpdir: validated_tmpdir.as_deref(),
        };

        let lean_prefix = query_lean_prefix_with_env(&lean_bin, Some(lean_tool_env))?;
        let (lean_stdlib, lean_stdlib_staging) = resolve_immutable_lean_stdlib_in(
            &lean_prefix,
            &raw_lean_bin,
            &prepared_lean_libs,
            store_prefix,
            caller_cwd,
            validated_tmpdir.as_deref(),
        )?;
        let stdlib_guard =
            lean_stdlib_staging.as_deref().or(prepared_lean_libs._staging.as_deref());
        let source_lib_lean_dir = if lean_stdlib_staging.is_none() {
            prepared_lean_libs.source_lib_lean_dir.as_deref()
        } else {
            None
        };

        let (raw_olean_paths, prebuilt_overlay, lean_dag_staging) =
            ensure_lean_dag_oleans_in_tmp_inner(
                anneal_root,
                &lean_bin,
                &lean_stdlib,
                stdlib_guard,
                source_lib_lean_dir,
                prebuilt_dir.as_deref(),
                cache,
                Some(lean_tool_env),
            )?;

        let sysroot_guards = [prepared_sys._staging.as_ref()];
        let rust_sysroot = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
            &sysroot_guards,
            &raw_rust_sysroot,
        );
        let ld_library_path = if raw_ld_library_path.is_empty() {
            String::new()
        } else {
            crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
                &sysroot_guards,
                OsStr::new(&raw_ld_library_path),
            )?
            .to_string_lossy()
            .into_owned()
        };
        let child_path = crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
            &sysroot_guards,
            &raw_child_path,
        )?;
        let capture_bin = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
            &[capture_staging.as_ref()],
            &raw_capture_bin,
        );
        let olean_guards = [
            lean_dag_staging.as_ref(),
            lean_stdlib_staging.as_ref(),
            prepared_lean_libs._staging.as_ref(),
        ];
        let olean_paths = raw_olean_paths
            .into_iter()
            .map(|p| {
                crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(&olean_guards, &p)
            })
            .collect();

        Ok(Self {
            anneal_root: anneal_root.to_path_buf(),
            capture_bin,
            rust_sysroot,
            lean_bin,
            olean_paths,
            prebuilt_overlay,
            ld_library_path,
            child_path,
            lean_ld_library_path,
            lean_child_path,
            validated_tmpdir,
            _rust_sysroot_staging: prepared_sys._staging,
            _capture_staging: capture_staging,
            _lean_lib_staging: prepared_lean_libs._staging,
            _lean_stdlib_staging: lean_stdlib_staging,
            _lean_dag_staging: lean_dag_staging,
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

    fn compile_single_lean_module(
        &self,
        env: &CaptureCompileEnv<'_>,
        lean_src: &Path,
        olean_out: &Path,
        context: &str,
    ) -> Result<(), String> {
        if let Some(parent) = olean_out.parent() {
            fs::create_dir_all(parent).map_err(|e| format!("create {}: {e}", parent.display()))?;
        }
        let compile_inv = self.apply_lean_env(
            Invocation::new(&self.lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-R")
                .arg(env.out_dir)
                .arg("-o")
                .arg(olean_out)
                .arg(lean_src)
                .env("LEAN_PATH", env.lean_path),
        );
        let compile_cap = crate::rustc_runner::run_supervised_in_tmp(
            &compile_inv,
            env.work_dir,
            effective_timeout_duration(LEAN_COMPILE_TIMEOUT_SECS, env.deadline)?,
            self.validated_tmpdir.as_deref(),
            context,
        )?;
        match compile_cap.termination {
            Termination::Exited(s) if s.success() => Ok(()),
            other => Err(format!(
                "compiling {} failed ({}):\nstdout:\n{}\nstderr:\n{}",
                lean_src.display(),
                other.describe(),
                String::from_utf8_lossy(&compile_cap.stdout),
                String::from_utf8_lossy(&compile_cap.stderr)
            )),
        }
    }

    /// Compile any `Captured.Shard_*` modules emitted by `anneal-rustc-capture`
    /// before compiling root `Captured.lean`, returning
    /// `(olean_dir, lean_path)`.
    fn compile_captured_lean_modules(
        &self,
        group_dir: &Path,
        out_dir: &Path,
        status_ok: &CaptureStatusOk,
        deadline: Option<Instant>,
        label: &str,
    ) -> Result<(PathBuf, String), String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let canon_out_dir =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(out_dir, &caller_cwd)
                .map_err(|e| format!("invalid capture_out directory: {e}"))?;
        let valid_root_lean = validate_capture_output_file(
            &canon_out_dir,
            &caller_cwd,
            &status_ok.lean,
            "captured Lean module",
        )?;
        let mod_olean_dir = group_dir.join("olean_out");
        fs::create_dir_all(&mod_olean_dir)
            .map_err(|e| format!("create {}: {e}", mod_olean_dir.display()))?;
        let canon_mod_olean_dir =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(&mod_olean_dir, &caller_cwd)
                .map_err(|e| format!("invalid olean_out directory: {e}"))?;
        let lean_path = self.lean_path_with(Some(&canon_mod_olean_dir))?;
        let env = CaptureCompileEnv {
            out_dir: &canon_out_dir,
            lean_path: &lean_path,
            work_dir: group_dir,
            deadline,
        };
        let shards =
            load_capture_shards(&canon_out_dir, &caller_cwd, status_ok.capture_shards.as_deref())?;
        for shard in &shards {
            let rel = shard_module_rel_path(&shard.capture_module)?;
            let shard_src = validate_capture_output_file(
                &canon_out_dir,
                &caller_cwd,
                &canon_out_dir.join(rel.with_extension("lean")),
                &format!("captured shard {}", shard.capture_module),
            )?;
            let shard_olean = canon_mod_olean_dir.join(rel.with_extension("olean"));
            self.compile_single_lean_module(
                &env,
                &shard_src,
                &shard_olean,
                &format!("compile {} ({label})", shard.capture_module),
            )?;
        }
        self.compile_single_lean_module(
            &env,
            &valid_root_lean,
            &canon_mod_olean_dir.join("Captured.olean"),
            &format!("compile Captured.lean ({label})"),
        )?;
        Ok((canon_mod_olean_dir, lean_path))
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

        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let canon_group_dir =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(group_dir, &caller_cwd)
                .map_err(|e| format!("invalid capture group dir {}: {e}", group_dir.display()))?;
        let out_dir = canon_group_dir.join("capture_out");
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
            .env("PATH", &self.child_path);
        if !self.ld_library_path.is_empty() {
            cap_inv = cap_inv.env("LD_LIBRARY_PATH", &self.ld_library_path);
        }
        if let Some(td) = &self.validated_tmpdir {
            cap_inv = cap_inv.env("TMPDIR", td);
        }
        for f in &selected_fns {
            cap_inv = cap_inv.arg("--select").arg(f);
        }

        let cap_out = run_supervised_cmd_in_tmp(
            &cap_inv,
            &canon_group_dir,
            effective_timeout_secs(CAPTURE_TIMEOUT_SECS)?,
            self.validated_tmpdir.as_deref(),
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

        let mut status_ok: CaptureStatusOk =
            serde_json::from_str(cap_stdout.trim()).map_err(|e| {
                format!("parse capture output JSON for {crate_name}: {e}; raw={cap_stdout:?}")
            })?;
        if status_ok.status != "captured" {
            return Err(format!(
                "unexpected capture status {:?} for {crate_name}",
                status_ok.status
            ));
        }
        let canon_out_dir =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(&out_dir, &canon_group_dir)
                .map_err(|e| format!("invalid capture_out directory for {crate_name}: {e}"))?;
        status_ok.capture = validate_capture_output_file(
            &canon_out_dir,
            &canon_group_dir,
            &status_ok.capture,
            "capture manifest",
        )?;
        status_ok.lean = validate_capture_output_file(
            &canon_out_dir,
            &canon_group_dir,
            &status_ok.lean,
            "captured Lean module",
        )?;
        status_ok.capture_shards = status_ok
            .capture_shards
            .as_deref()
            .map(|p| {
                validate_capture_output_file(
                    &canon_out_dir,
                    &canon_group_dir,
                    p,
                    "capture shards manifest",
                )
            })
            .transpose()?;

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

        let (mod_olean_dir, lean_path) = self.compile_captured_lean_modules(
            &canon_group_dir,
            &canon_out_dir,
            &status_ok,
            None,
            crate_name,
        )?;

        let captured = CapturedModule {
            capture_dir: canon_out_dir,
            capture_json: status_ok.capture,
            captured_lean: status_ok.lean,
            olean_dir: mod_olean_dir,
            body_ids_by_fn,
            kernel_whnf_eligible_by_fn,
            kernel_whnf_ub_sysroot_by_fn,
            move_reinit_fns,
        };

        let results = self.evaluate_captured_group(
            &canon_group_dir,
            crate_name,
            &lean_path,
            &captured,
            cases,
        )?;
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

        let eval_inv = self.apply_lean_env(
            Invocation::new(&self.lean_bin, LEAN_COMPILE_FLAGS)
                .arg(&probe_path)
                .env("LEAN_PATH", lean_path),
        );
        let eval_out = run_supervised_cmd_in_tmp(
            &eval_inv,
            group_dir,
            effective_timeout_secs(LEAN_EVAL_TIMEOUT_SECS)?,
            self.validated_tmpdir.as_deref(),
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

        let wp_inv = self.apply_lean_env(
            Invocation::new(&self.lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-DwarningAsError=true")
                .arg(&wp_path)
                .env("LEAN_PATH", lean_path),
        );
        let wp_out = run_supervised_cmd_in_tmp(
            &wp_inv,
            group_dir,
            effective_timeout_secs(LEAN_EVAL_TIMEOUT_SECS)?,
            self.validated_tmpdir.as_deref(),
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

    /// Capture and evaluate a batch of Stage-2 [`crate::r#gen::GenProgram`]
    /// cases in a single `anneal-rustc-capture` + `lean` `#eval` pass for
    /// admitted/UB cases, isolating `ScopeControl` cases so expected capture
    /// rejections never bisect the admitted batch.
    pub fn capture_and_evaluate_fuzz_batch(
        &self,
        group_dir: &Path,
        crate_name: &str,
        programs: &[&crate::r#gen::GenProgram],
    ) -> Result<BTreeMap<String, FuzzLeanCaseResult>, String> {
        self.capture_and_evaluate_fuzz_batch_until(group_dir, crate_name, programs, None)
    }

    pub fn capture_and_evaluate_fuzz_batch_until(
        &self,
        group_dir: &Path,
        crate_name: &str,
        programs: &[&crate::r#gen::GenProgram],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, FuzzLeanCaseResult>, String> {
        if programs.is_empty() {
            return Ok(BTreeMap::new());
        }
        let mut clean_batch = Vec::new();
        let mut scope_controls = Vec::new();
        for &p in programs {
            if p.category == crate::r#gen::GenCategory::ScopeControl {
                scope_controls.push(p);
            } else {
                clean_batch.push(p);
            }
        }
        if !clean_batch.is_empty() && !scope_controls.is_empty() {
            let mut combined = self.capture_and_evaluate_fuzz_group(
                &group_dir.join("admitted"),
                &format!("{crate_name}_adm"),
                &clean_batch,
                deadline,
            )?;
            for (idx, sc) in scope_controls.into_iter().enumerate() {
                combined.extend(self.capture_and_evaluate_fuzz_group(
                    &group_dir.join(format!("scope_{idx}")),
                    &format!("{crate_name}_sc_{idx}"),
                    &[sc],
                    deadline,
                )?);
            }
            return Ok(combined);
        }
        self.capture_and_evaluate_fuzz_group(group_dir, crate_name, programs, deadline)
    }

    fn capture_and_evaluate_fuzz_group(
        &self,
        group_dir: &Path,
        crate_name: &str,
        programs: &[&crate::r#gen::GenProgram],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, FuzzLeanCaseResult>, String> {
        if programs.is_empty() {
            return Ok(BTreeMap::new());
        }
        fs::create_dir_all(group_dir)
            .map_err(|e| format!("create fuzz capture group dir {}: {e}", group_dir.display()))?;
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let canon_group_dir =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(group_dir, &caller_cwd)
                .map_err(|e| format!("invalid fuzz capture group dir: {e}"))?;

        let source_text = crate::r#gen::render_batch_crate(programs);
        let source_path = canon_group_dir.join("fuzz_batch.rs");
        fs::write(&source_path, &source_text)
            .map_err(|e| format!("write {}: {e}", source_path.display()))?;

        let out_dir = canon_group_dir.join("capture_out");
        let mut cap_inv = Invocation::new(&self.capture_bin, &["capture"])
            .arg("--crate-root")
            .arg(&source_path)
            .arg("--crate-name")
            .arg(crate_name)
            .arg("--target")
            .arg("x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&out_dir)
            .arg("--sysroot")
            .arg(&self.rust_sysroot)
            .arg("--source-file")
            .arg(&source_path)
            .env("PATH", &self.child_path);
        if !self.ld_library_path.is_empty() {
            cap_inv = cap_inv.env("LD_LIBRARY_PATH", &self.ld_library_path);
        }
        if let Some(td) = &self.validated_tmpdir {
            cap_inv = cap_inv.env("TMPDIR", td);
        }
        for p in programs {
            cap_inv = cap_inv.arg("--select").arg(&p.fn_name);
        }

        let cap_out = crate::rustc_runner::run_supervised_in_tmp(
            &cap_inv,
            &canon_group_dir,
            effective_timeout_duration(CAPTURE_TIMEOUT_SECS, deadline)?,
            self.validated_tmpdir.as_deref(),
            &format!("fuzz capture {crate_name}"),
        )?;
        let cap_stdout = String::from_utf8_lossy(&cap_out.stdout);
        let cap_stderr = String::from_utf8_lossy(&cap_out.stderr);
        let capture_ok = matches!(cap_out.termination, Termination::Exited(s) if s.success());
        if !capture_ok {
            if programs.len() == 1
                || !is_bisectable_capture_rejection(&cap_out.termination, &cap_stdout)
            {
                let expected_fn = (programs.len() == 1).then_some(programs[0].fn_name.as_str());
                let classified = classify_single_capture_failure(
                    &cap_out.termination,
                    &cap_stdout,
                    &cap_stderr,
                    expected_fn,
                );
                let mut out = BTreeMap::new();
                for p in programs {
                    out.insert(p.case_id.clone(), classified.clone());
                }
                return Ok(out);
            }
            let mid = programs.len() / 2;
            let mut combined = self.capture_and_evaluate_fuzz_batch_until(
                &canon_group_dir.join("bisect_l"),
                &format!("{crate_name}_l"),
                &programs[..mid],
                deadline,
            )?;
            combined.extend(self.capture_and_evaluate_fuzz_batch_until(
                &canon_group_dir.join("bisect_r"),
                &format!("{crate_name}_r"),
                &programs[mid..],
                deadline,
            )?);
            return Ok(combined);
        }

        let mut status_ok: CaptureStatusOk =
            serde_json::from_str(cap_stdout.trim()).map_err(|e| {
                format!("parse fuzz capture output JSON for {crate_name}: {e}; raw={cap_stdout:?}")
            })?;
        if status_ok.status != "captured" {
            return Err(format!(
                "unexpected fuzz capture status {:?} for {crate_name}",
                status_ok.status
            ));
        }
        let canon_out_dir =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(&out_dir, &canon_group_dir)
                .map_err(|e| format!("invalid fuzz capture_out directory for {crate_name}: {e}"))?;
        status_ok.capture = validate_capture_output_file(
            &canon_out_dir,
            &canon_group_dir,
            &status_ok.capture,
            "capture manifest",
        )?;
        status_ok.lean = validate_capture_output_file(
            &canon_out_dir,
            &canon_group_dir,
            &status_ok.lean,
            "captured Lean module",
        )?;
        status_ok.capture_shards = status_ok
            .capture_shards
            .as_deref()
            .map(|p| {
                validate_capture_output_file(
                    &canon_out_dir,
                    &canon_group_dir,
                    p,
                    "capture shards manifest",
                )
            })
            .transpose()?;

        let manifest_raw = fs::read_to_string(&status_ok.capture)
            .map_err(|e| format!("read {}: {e}", status_ok.capture.display()))?;
        let manifest: CaptureManifest = serde_json::from_str(&manifest_raw)
            .map_err(|e| format!("parse {}: {e}", status_ok.capture.display()))?;

        let mut body_ids_by_fn = BTreeMap::new();
        for p in programs {
            let (idx, _body) =
                select_captured_body(&manifest.program.bodies, &p.fn_name, &status_ok.capture)?;
            body_ids_by_fn.insert(p.fn_name.clone(), idx);
        }

        let (_mod_olean_dir, lean_path) = self.compile_captured_lean_modules(
            &canon_group_dir,
            &canon_out_dir,
            &status_ok,
            deadline,
            &format!("fuzz {crate_name}"),
        )?;

        let raw_outcomes = self.eval_fuzz_probe_with_bisection(
            &canon_group_dir,
            &lean_path,
            &body_ids_by_fn,
            programs,
            0,
            deadline,
        )?;
        let mut results = BTreeMap::new();
        for p in programs {
            let body_id = body_ids_by_fn.get(&p.fn_name).copied();
            let capture_body = if let Some(def_id) = body_id {
                let body = &manifest.program.bodies[def_id];
                let blocks_json: Vec<serde_json::Value> = body
                    .blocks
                    .iter()
                    .map(|b| serde_json::to_value(b).map_err(|e| format!("serialize block: {e}")))
                    .collect::<Result<Vec<_>, _>>()?;
                let cap_sha = compute_capture_body_sha256(
                    &body.identity,
                    body.arg_count,
                    &body.local_tys,
                    &blocks_json,
                );
                Some(FuzzCaptureBody {
                    body_id: def_id,
                    fn_identity: body.identity.clone(),
                    arg_count: body.arg_count,
                    local_tys: body.local_tys.clone(),
                    blocks: blocks_json,
                    capture_body_sha256: cap_sha,
                })
            } else {
                None
            };
            let parsed_entry =
                raw_outcomes.get(&p.case_id).cloned().unwrap_or_else(|| ParsedLeanFuzzProbeLine {
                    body_id: None,
                    fn_identity: None,
                    outcome: ObservedOutcome::ToolError {
                        detail: format!("Lean fuzz output missing case {:?}", p.case_id),
                    },
                    lean_probe_line: None,
                    move_reinit: None,
                });
            let (mut outcome, mut lean_probe_line, parsed_mr) =
                bind_fuzz_probe_result_to_capture_body(
                    &p.case_id,
                    parsed_entry,
                    capture_body.as_ref(),
                );
            let mut move_reinit_evidence = None;
            let mut exercised_move_reinit = false;
            if let Some(mr) = parsed_mr {
                let Some(cb) = &capture_body else {
                    outcome = ObservedOutcome::ToolError {
                        detail: format!("missing body_id for move/reinit witness {}", p.case_id),
                    };
                    results.insert(
                        p.case_id.clone(),
                        FuzzLeanCaseResult {
                            outcome,
                            capture_rejected: None,
                            capture_refusal_json: None,
                            capture_json: Some(status_ok.capture.clone()),
                            capture_body: None,
                            lean_probe_line: None,
                            exercised_move_reinit: false,
                            move_reinit_evidence: None,
                        },
                    );
                    continue;
                };
                let ev = MoveReinitEvidence {
                    body_id: cb.body_id,
                    fn_identity: cb.fn_identity.clone(),
                    local_slot: mr.local_slot,
                    arg_count: cb.arg_count,
                    local_tys: cb.local_tys.clone(),
                    blocks: cb.blocks.clone(),
                    total_steps: mr.total_steps,
                    init_step: mr.init_step,
                    move_step: mr.move_step,
                    reinit_step: mr.reinit_step,
                    read_step: mr.read_step,
                    lean_probe_line: lean_probe_line.clone().unwrap_or_default(),
                    capture_body_sha256: cb.capture_body_sha256.clone(),
                };
                match verify_move_reinit_evidence(&ev, &p.case_id, &p.fn_name, p.args().len()) {
                    Ok(()) => {
                        exercised_move_reinit = true;
                        move_reinit_evidence = Some(ev);
                    }
                    Err(err) => {
                        outcome = ObservedOutcome::ToolError {
                            detail: format!("invalid move/reinit witness for {}: {err}", p.case_id),
                        };
                        lean_probe_line = None;
                    }
                }
            }
            results.insert(
                p.case_id.clone(),
                FuzzLeanCaseResult {
                    outcome,
                    capture_rejected: None,
                    capture_refusal_json: None,
                    capture_json: Some(status_ok.capture.clone()),
                    capture_body,
                    lean_probe_line,
                    exercised_move_reinit,
                    move_reinit_evidence,
                },
            );
        }
        Ok(results)
    }

    fn eval_fuzz_probe_with_bisection(
        &self,
        group_dir: &Path,
        lean_path: &str,
        body_ids_by_fn: &BTreeMap<String, usize>,
        programs: &[&crate::r#gen::GenProgram],
        probe_tag: usize,
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, ParsedLeanFuzzProbeLine>, String> {
        let probe_src = generate_fuzz_lean_probe(body_ids_by_fn, programs)?;
        let probe_path = group_dir.join(format!("FuzzProbe_{probe_tag}.lean"));
        fs::write(&probe_path, &probe_src)
            .map_err(|e| format!("write {}: {e}", probe_path.display()))?;

        let eval_inv = self.apply_lean_env(
            Invocation::new(&self.lean_bin, LEAN_COMPILE_FLAGS)
                .arg(&probe_path)
                .env("LEAN_PATH", lean_path),
        );
        let eval_out = crate::rustc_runner::run_supervised_in_tmp(
            &eval_inv,
            group_dir,
            effective_timeout_duration(LEAN_EVAL_TIMEOUT_SECS, deadline)?,
            self.validated_tmpdir.as_deref(),
            &format!("eval FuzzProbe_{probe_tag}.lean"),
        )?;
        let stdout = String::from_utf8_lossy(&eval_out.stdout);
        let stderr = String::from_utf8_lossy(&eval_out.stderr);
        let eval_exited_ok = matches!(eval_out.termination, Termination::Exited(s) if s.success());
        let mut parse_err: Option<String> = None;
        if eval_exited_ok {
            let ids: Vec<&str> = programs.iter().map(|p| p.case_id.as_str()).collect();
            match parse_fuzz_lean_probe_output_ids(&stdout, &ids) {
                Ok(parsed) => return Ok(parsed),
                Err(err) => parse_err = Some(err),
            }
        }
        if programs.len() == 1
            || is_global_lean_probe_failure(
                &eval_out.termination,
                &probe_src,
                &probe_path,
                &stdout,
                &stderr,
            )
        {
            let diag = stderr
                .lines()
                .chain(stdout.lines())
                .filter(|l| !l.trim().is_empty())
                .take(6)
                .collect::<Vec<_>>()
                .join(" | ");
            let detail = if let Some(err) = parse_err {
                format!(
                    "Lean fuzz probe parse failed ({}): {err} ({diag})",
                    eval_out.termination.describe()
                )
            } else {
                format!("Lean fuzz probe failed ({}): {diag}", eval_out.termination.describe())
            };
            let mut out = BTreeMap::new();
            for p in programs {
                out.insert(
                    p.case_id.clone(),
                    ParsedLeanFuzzProbeLine {
                        body_id: None,
                        fn_identity: None,
                        outcome: ObservedOutcome::ToolError { detail: detail.clone() },
                        lean_probe_line: None,
                        move_reinit: None,
                    },
                );
            }
            return Ok(out);
        }

        let mid = programs.len() / 2;
        let mut combined = self.eval_fuzz_probe_with_bisection(
            group_dir,
            lean_path,
            body_ids_by_fn,
            &programs[..mid],
            probe_tag * 2 + 1,
            deadline,
        )?;
        combined.extend(self.eval_fuzz_probe_with_bisection(
            group_dir,
            lean_path,
            body_ids_by_fn,
            &programs[mid..],
            probe_tag * 2 + 2,
            deadline,
        )?);
        Ok(combined)
    }
}

/// Return `true` only when a failed fuzz Lean probe reflects a batch-wide
/// failure (timeout, launch failure, signal death, preamble/import error, or
/// CLI/loader error) rather than an `#eval runCase` case-local error that
/// bisection can isolate.
fn is_global_lean_probe_failure(
    termination: &Termination,
    probe_src: &str,
    probe_path: &Path,
    stdout: &str,
    stderr: &str,
) -> bool {
    match termination {
        Termination::TimedOut(_) | Termination::LaunchFailed(_) => true,
        Termination::Exited(status) => {
            if stdout.contains(LEAN_CASE_PREFIX) {
                return false;
            }
            let preamble_lines =
                probe_src.lines().take_while(|line| !line.starts_with("#eval runCase ")).count();
            if let Some(file_name) = probe_path.file_name().and_then(|n| n.to_str()) {
                let prefix = format!("{file_name}:");
                let mut saw_preamble_diag = false;
                let mut saw_case_diag = false;
                for line in stderr.lines().chain(stdout.lines()) {
                    if let Some((_, after)) = line.split_once(&prefix)
                        && let Some(line_str) = after.split(':').next()
                        && let Ok(diag_line) = line_str.parse::<usize>()
                    {
                        if diag_line <= preamble_lines {
                            saw_preamble_diag = true;
                        } else {
                            saw_case_diag = true;
                        }
                    }
                }
                if saw_preamble_diag {
                    return true;
                }
                if saw_case_diag {
                    return false;
                }
            }
            if status.code().is_none() {
                return true;
            }
            let combined_lower = format!("{stderr}\n{stdout}").to_ascii_lowercase();
            [
                "unknown module prefix",
                "unknown package",
                "error while loading shared libraries",
                "cannot open shared object file",
                "unrecognized option",
                "unknown option",
                "command line",
                "invalid object file",
                "no such file or directory",
                "does not exist",
            ]
            .iter()
            .any(|needle| combined_lower.contains(needle))
        }
    }
}

fn generate_fuzz_lean_probe(
    body_ids_by_fn: &BTreeMap<String, usize>,
    programs: &[&crate::r#gen::GenProgram],
) -> Result<String, String> {
    let mut out = String::from(
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
         structure StageRec where\n\
           stg : Nat := 0\n\
           iS : Nat := 0\n\
           iB : Nat := 0\n\
           iI : Nat := 0\n\
           mS : Nat := 0\n\
           mB : Nat := 0\n\
           mI : Nat := 0\n\
           rS : Nat := 0\n\
           rB : Nat := 0\n\
           rI : Nat := 0\n\
           rdS : Nat := 0\n\
           rdB : Nat := 0\n\
           rdI : Nat := 0\n\n\
         def mkZeroRecs : Nat → List StageRec\n\
           | 0 => []\n\
           | n + 1 => {} :: mkZeroRecs n\n\n\
         def mapIdxRecs : Nat → List StageRec → (Nat → StageRec → StageRec) → List StageRec\n\
           | _, [], _ => []\n\
           | idx, rec :: rest, f => f idx rec :: mapIdxRecs (idx + 1) rest f\n\n\
         def findWitness : Nat → List StageRec → Option (Nat × StageRec)\n\
           | _, [] => none\n\
           | idx, rec :: rest => if Nat.beq rec.stg 4 then some (idx, rec) else findWitness (idx + 1) rest\n\n\
         def opReadsSlot (slot : Nat) : Operand → Bool\n\
           | .copy p | .move p => Nat.beq p.localId slot\n\
           | _ => false\n\n\
         def rvReadsSlot (slot : Nat) : Rvalue → Bool\n\
           | .use op | .useRetag op | .unaryOp _ op | .cast _ op _\n\
           | .aggregateRangeTo _ op | .aggregateRangeFrom _ op => opReadsSlot slot op\n\
           | .binaryOp _ l r => opReadsSlot slot l || opReadsSlot slot r\n\
           | .discriminant p => Nat.beq p.localId slot\n\
           | .aggregateTuple ops => ops.any (opReadsSlot slot)\n\
           | _ => false\n\n\
         def stepReadsSlot (slot : Nat) (stmt? : Option StatementKind)\n\
             (term? : Option TerminatorKind) : Bool :=\n\
           match stmt? with\n\
           | some (.assign _ rv) => rvReadsSlot slot rv\n\
           | _ =>\n\
             match term? with\n\
             | some (.switchInt op _) | some (.assert op _ _ _ _) => opReadsSlot slot op\n\
             | some (.call _ ops _ _ _)\n\
             | some (.coreCall _ ops _ _ _)\n\
             | some (.sysrootCall _ ops _ _ _) => ops.any (opReadsSlot slot)\n\
             | _ => false\n\n\
         def stepMovesSlot (slot : Nat) (stmt? : Option StatementKind)\n\
             (term? : Option TerminatorKind) : Bool :=\n\
           match stmt? with\n\
           | some (.assign dst (.use (.move src))) | some (.assign dst (.useRetag (.move src))) =>\n\
             Nat.beq src.localId slot && src.projection.isEmpty && !Nat.beq dst.localId slot\n\
           | _ =>\n\
             match term? with\n\
             | some (.switchInt (.move src) _) | some (.assert (.move src) _ _ _ _) =>\n\
               Nat.beq src.localId slot && src.projection.isEmpty\n\
             | some (.call _ ops _ _ _)\n\
             | some (.coreCall _ ops _ _ _)\n\
             | some (.sysrootCall _ ops _ _ _) =>\n\
               ops.any (fun op =>\n\
                 match op with\n\
                 | .move src => Nat.beq src.localId slot && src.projection.isEmpty\n\
                 | _ => false)\n\
             | _ => false\n\n\
         def slotInit : Option LocalSlot → Bool\n\
           | some (.immediate (some _)) => true\n\
           | _ => false\n\n\
         def slotDeinit : Option LocalSlot → Bool\n\
           | some (.immediate none) => true\n\
           | _ => false\n\n\
         def slotDead : Option LocalSlot → Bool\n\
           | some .dead => true\n\
           | _ => false\n\n\
         def updateSlotRec (stepIdx argCount slot bbIdx stmtIdx : Nat) (rec : StageRec)\n\
             (bSlot aSlot : Option LocalSlot) (stmt? : Option StatementKind)\n\
             (term? : Option TerminatorKind) : StageRec :=\n\
           if Nat.ble slot argCount then {}\n\
           else if Nat.beq rec.stg 4 then rec\n\
           else if slotDead aSlot then {}\n\
           else if Nat.beq rec.stg 0 then\n\
             if slotInit aSlot then { stg := 1, iS := stepIdx, iB := bbIdx, iI := stmtIdx } else {}\n\
           else if Nat.beq rec.stg 1 then\n\
             if slotInit bSlot && stepMovesSlot slot stmt? term? && slotDeinit aSlot then\n\
               { rec with stg := 2, mS := stepIdx, mB := bbIdx, mI := stmtIdx }\n\
             else if slotInit aSlot then rec else {}\n\
           else if Nat.beq rec.stg 2 then\n\
             if slotInit aSlot then { rec with stg := 3, rS := stepIdx, rB := bbIdx, rI := stmtIdx }\n\
             else if slotDeinit aSlot then rec else {}\n\
           else\n\
             if slotInit bSlot && stepReadsSlot slot stmt? term? then\n\
               { rec with stg := 4, rdS := stepIdx, rdB := bbIdx, rdI := stmtIdx }\n\
             else if slotInit bSlot && stepMovesSlot slot stmt? term? && slotDeinit aSlot then\n\
               { rec with stg := 2, mS := stepIdx, mB := bbIdx, mI := stmtIdx }\n\
             else if slotInit aSlot then rec\n\
             else if slotDeinit aSlot then rec else {}\n\n\
         def advanceRecs (stepIdx : Nat) (body : Body) (defId : Nat) (f0 f1 : FrameState)\n\
             (recs : List StageRec) : List StageRec :=\n\
           if !(Nat.beq f0.defId defId && Nat.beq f1.defId defId) then recs\n\
           else\n\
             let bb? := body.basicBlocks[f0.blockIdx]?\n\
             let stmt? := bb?.bind (fun bb => bb.statements[f0.stmtIdx]?)\n\
             let term? := bb?.bind (fun bb =>\n\
               if Nat.beq f0.stmtIdx bb.statements.length then some bb.terminator else none)\n\
             mapIdxRecs 0 recs (fun slot rec =>\n\
               updateSlotRec stepIdx body.argumentCount slot f0.blockIdx f0.stmtIdx rec f0.locals[slot]? f1.locals[slot]? stmt? term?)\n\n\
         def binOpIsShift : BinOp → Bool\n\
           | .shl | .shlUnchecked | .shr | .shrUnchecked => true\n\
           | _ => false\n\n\
         def operandIsZeroScalar (f0 : FrameState) : Operand → Bool\n\
           | .constant c =>\n\
             (match c.lit with\n\
              | .scalar bits => Nat.beq bits.toNat 0\n\
              | _ => false)\n\
           | .copy p | .move p =>\n\
             if !p.projection.isEmpty then false\n\
             else\n\
               (match f0.locals[p.localId]? with\n\
                | some (.immediate (some (.scalar sv))) => Nat.beq sv.bits.toNat 0\n\
                | _ => false)\n\n\
         def describeUbFault (prog : Program) (st : State) : String :=\n\
           match st.frames.head? with\n\
           | none => \"undefined\"\n\
           | some f0 =>\n\
             (match (activeFrameBodyComp prog f0).bind (fun b => b.basicBlocks[f0.blockIdx]?) with\n\
              | none => \"undefined\"\n\
              | some bb =>\n\
                if Nat.blt f0.stmtIdx bb.statements.length then\n\
                  (match bb.statements[f0.stmtIdx]? with\n\
                   | some (.assign _ (.binaryOp op _ rhs)) =>\n\
                     if binOpIsShift op then \"overflowing shift\"\n\
                     else\n\
                       (match op with\n\
                        | .div | .rem =>\n\
                          if operandIsZeroScalar f0 rhs then \"dividing by zero\"\n\
                          else \"overflow in signed division\"\n\
                        | .addUnchecked | .subUnchecked | .mulUnchecked =>\n\
                          \"arithmetic overflow\"\n\
                        | _ => \"undefined\")\n\
                   | some (.assign _ (.cast _ _ _)) => \"invalid value\"\n\
                   | some (.assign _ _) => \"uninitialized\"\n\
                   | _ => \"undefined\")\n\
                else\n\
                  (match bb.terminator with\n\
                   | .unreachable => \"unreachable\"\n\
                   | .assert _ _ .divByZero _ _ | .assert _ _ .remByZero _ _ =>\n\
                     \"dividing by zero\"\n\
                   | .assert _ _ (.overflow op) _ _ =>\n\
                     (match op with\n\
                      | .div | .rem => \"overflow in signed division\"\n\
                      | _ => if binOpIsShift op then \"overflowing shift\" else \"arithmetic overflow\")\n\
                   | .assert _ _ .overflowNeg _ _ => \"overflow in signed negation\"\n\
                   | .assert _ _ .misalignedPtrDeref _ _\n\
                   | .assert _ _ .nullPtrDeref _ _\n\
                   | .assert _ _ .boundsCheck _ _ => \"invalid value\"\n\
                   | .coreCall .usizeUncheckedSub _ _ _ _ => \"arithmetic overflow\"\n\
                   | .return_ => \"uninitialized\"\n\
                   | _ => \"undefined\"))\n\n\
         def renderCoord (s b i : Nat) : String := toString s ++ \",\" ++ toString b ++ \",\" ++ toString i\n\n\
         def renderMrTag (totalSteps : Nat) (w? : Option (Nat × StageRec)) : String :=\n\
           match w? with\n\
           | none => \"MR0\"\n\
           | some (slot, rec) =>\n\
             \"MR1|\" ++ toString slot ++ \"|\" ++ toString totalSteps ++ \"|\" ++\n\
             renderCoord rec.iS rec.iB rec.iI ++ \"|\" ++\n\
             renderCoord rec.mS rec.mB rec.mI ++ \"|\" ++\n\
             renderCoord rec.rS rec.rB rec.rI ++ \"|\" ++\n\
             renderCoord rec.rdS rec.rdB rec.rdI\n\n\
         def evalTraceFuel (prog : Program) (defId stepIdx : Nat) :\n\
             Nat → State → List StageRec → StepResult State TerminalOut × Nat × Option (Nat × StageRec) × String\n\
           | 0, st, _ => (.step st, stepIdx, none, \"\")\n\
           | fuel + 1, st, recs =>\n\
             match evalMirStepBy (mirTyBeqAt 8) prog 0 st with\n\
             | .step st' =>\n\
               let recs' :=\n\
                 match prog.bodies[defId]?, st.frames, st'.frames with\n\
                 | some body, [f0], [f1] => advanceRecs stepIdx body defId f0 f1 recs\n\
                 | _, _, _ => recs\n\
               evalTraceFuel prog defId (stepIdx + 1) fuel st' recs'\n\
             | .done out =>\n\
               let recs' :=\n\
                 match prog.bodies[defId]?, st.frames with\n\
                 | some body, [f0] =>\n\
                   let bb? := body.basicBlocks[f0.blockIdx]?\n\
                   let term? := bb?.bind (fun bb =>\n\
                     if Nat.beq f0.stmtIdx bb.statements.length then some bb.terminator else none)\n\
                   mapIdxRecs 0 recs (fun slot rec =>\n\
                     if Nat.beq rec.stg 3 && slotInit f0.locals[slot]? && stepReadsSlot slot none term? then\n\
                       { rec with stg := 4, rdS := stepIdx, rdB := f0.blockIdx, rdI := f0.stmtIdx }\n\
                     else rec)\n\
                 | _, _ => recs\n\
               (.done out, stepIdx + 1, findWitness 0 recs', \"\")\n\
             | .fault .undefined => (.fault .undefined, stepIdx + 1, none, describeUbFault prog st)\n\
             | .fault .unsupported => (.fault .unsupported, stepIdx + 1, none, \"\")\n\n\
         def runCase (caseId : String) (defId fuel : Nat) (args : List Val) : String :=\n\
           let prog : Program := { Captured.program with entryDefId := defId }\n\
           let bodyIdent := match prog.bodies[defId]? with\n\
             | some b => ((b.identity.replace \"|\" \"_\").replace \"\\r\" \"_\").replace \"\\n\" \"_\"\n\
             | none => \"<MISSING_BODY>\"\n\
           let numLocals := match prog.bodies[defId]? with | some b => b.locals.length | none => 0\n\
           let (mrTag, res) :=\n\
             match initStateBy (mirTyBeqAt 8) prog { args := args } with\n\
             | .error .undefined => (\"MR0\", \"INIT_UNDEFINED\")\n\
             | .error .unsupported => (\"MR0\", \"INIT_UNSUPPORTED\")\n\
             | .ok s0 =>\n\
               match evalTraceFuel prog defId 0 fuel s0 (mkZeroRecs numLocals) with\n\
               | (.step _, _, _, _) => (\"MR0\", \"OUT_OF_FUEL\")\n\
               | (.fault .undefined, _, _, cause) => (\"MR0\", \"FAULT:undefined:\" ++ cause)\n\
               | (.fault .unsupported, _, _, _) => (\"MR0\", \"FAULT:unsupported\")\n\
               | (.done (.unwound _), totalSteps, w?, _) => (renderMrTag totalSteps w?, \"UNWOUND\")\n\
               | (.done (.aborted _), totalSteps, w?, _) => (renderMrTag totalSteps w?, \"ABORTED\")\n\
               | (.done (.returned out), totalSteps, w?, _) => (renderMrTag totalSteps w?, \"RETURNED:\" ++ renderPrimitive out.ret)\n\
           \"ANNEAL_LEAN_CASE:\" ++ caseId ++ \":BODY|\" ++ toString defId ++ \"|\" ++ bodyIdent ++ \"|\" ++ mrTag ++ \":\" ++ res\n\n",
    );

    for prog in programs {
        let def_id = body_ids_by_fn
            .get(&prog.fn_name)
            .copied()
            .ok_or_else(|| format!("missing defId for fuzz function {:?}", prog.fn_name))?;
        let args = prog.args();
        let args_lean = args
            .iter()
            .enumerate()
            .map(|(arg_idx, val)| lean_val_expr(val, def_id, arg_idx))
            .collect::<Result<Vec<_>, _>>()?
            .join(", ");
        out.push_str(&format!(
            "#eval runCase {:?} {def_id} {} [{args_lean}]\n",
            prog.case_id, prog.fuel
        ));
    }
    Ok(out)
}

#[derive(Deserialize)]
struct CaptureUnsupportedItem {
    #[serde(default)]
    path: String,
    #[serde(default)]
    reason: String,
}

#[derive(Deserialize)]
struct CaptureFailureStatus {
    status: String,
    #[serde(default)]
    diagnostics: Vec<String>,
    #[serde(default)]
    unsupported: Vec<CaptureUnsupportedItem>,
}

fn refusal_binds_fn(path: &str, fn_name: &str) -> bool {
    path == fn_name
        || path == format!("rust-path-v1::{fn_name}")
        || path.ends_with(&format!("::{fn_name}"))
}

/// Return `true` when a batch `anneal-rustc-capture` exit represents either an
/// item-level `{"status": "unsupported"}` refusal or a batch-rendered
/// `{"status": "compiler_failed"}` diagnostic worth bisecting with
/// subset-specific rendered crates, rather than a batch-wide timeout, launch
/// error, or infrastructure `tool_failed`.
fn is_bisectable_capture_rejection(termination: &Termination, stdout: &str) -> bool {
    if !matches!(termination, Termination::Exited(s) if s.code() == Some(1)) {
        return false;
    }
    for line in stdout.lines().rev() {
        let trimmed = line.trim();
        if !trimmed.starts_with('{') {
            continue;
        }
        if let Ok(parsed) = serde_json::from_str::<CaptureFailureStatus>(trimmed) {
            return matches!(parsed.status.as_str(), "unsupported" | "compiler_failed");
        }
    }
    false
}

/// Classify a failed single-program `anneal-rustc-capture` run:
/// only structured `{"status": "unsupported", ...}` on exit code `1` (with
/// non-empty diagnostics and case-bound unsupported items when `expected_fn` is
/// supplied) becomes `capture_rejected = Some(...)`; any `tool_failed`,
/// `compiler_failed`, signal, timeout, `LaunchFailed`, or unbound/malformed
/// JSON becomes `ToolError`.
fn classify_single_capture_failure(
    termination: &Termination,
    stdout: &str,
    stderr: &str,
    expected_fn: Option<&str>,
) -> FuzzLeanCaseResult {
    let summary = stderr.lines().chain(stdout.lines()).take(4).collect::<Vec<_>>().join(" | ");
    if matches!(termination, Termination::Exited(s) if s.code() == Some(1)) {
        for line in stdout.lines().rev() {
            let trimmed = line.trim();
            if !trimmed.starts_with('{') {
                continue;
            }
            if let Ok(parsed) = serde_json::from_str::<CaptureFailureStatus>(trimmed) {
                let has_diags = !parsed.diagnostics.is_empty()
                    && parsed.diagnostics.iter().all(|d| !d.trim().is_empty());
                let fn_bound = expected_fn.is_none_or(|fn_name| {
                    parsed
                        .unsupported
                        .iter()
                        .any(|u| !u.reason.trim().is_empty() && refusal_binds_fn(&u.path, fn_name))
                });
                if parsed.status == "unsupported" && has_diags && fn_bound {
                    let diag = format!("{} ({trimmed})", parsed.diagnostics.join("; "));
                    let reason = format!("capture unsupported: {diag}");
                    return FuzzLeanCaseResult {
                        outcome: ObservedOutcome::Unsupported { detail: reason.clone() },
                        capture_rejected: Some(reason),
                        capture_refusal_json: Some(trimmed.to_owned()),
                        capture_json: None,
                        capture_body: None,
                        lean_probe_line: None,
                        exercised_move_reinit: false,
                        move_reinit_evidence: None,
                    };
                }
                let detail =
                    format!("capture {} ({}): {}", parsed.status, termination.describe(), summary);
                return FuzzLeanCaseResult {
                    outcome: ObservedOutcome::ToolError { detail },
                    capture_rejected: None,
                    capture_refusal_json: None,
                    capture_json: None,
                    capture_body: None,
                    lean_probe_line: None,
                    exercised_move_reinit: false,
                    move_reinit_evidence: None,
                };
            }
        }
    }
    let detail =
        format!("capture infrastructure failure ({}): {}", termination.describe(), summary);
    FuzzLeanCaseResult {
        outcome: ObservedOutcome::ToolError { detail },
        capture_rejected: None,
        capture_refusal_json: None,
        capture_json: None,
        capture_body: None,
        lean_probe_line: None,
        exercised_move_reinit: false,
        move_reinit_evidence: None,
    }
}

fn parse_mr_coord(raw: &str) -> Result<MoveReinitStep, String> {
    let mut parts = raw.splitn(4, ',');
    let step = parts
        .next()
        .ok_or_else(|| format!("missing step in coord {raw:?}"))?
        .parse::<usize>()
        .map_err(|e| format!("invalid step in coord {raw:?}: {e}"))?;
    let block = parts
        .next()
        .ok_or_else(|| format!("missing block in coord {raw:?}"))?
        .parse::<usize>()
        .map_err(|e| format!("invalid block in coord {raw:?}: {e}"))?;
    let stmt = parts
        .next()
        .ok_or_else(|| format!("missing stmt in coord {raw:?}"))?
        .parse::<usize>()
        .map_err(|e| format!("invalid stmt in coord {raw:?}: {e}"))?;
    if parts.next().is_some() {
        return Err(format!("trailing fields in coord {raw:?}"));
    }
    Ok(MoveReinitStep { step, block, stmt })
}

fn parse_mr_witness_tag(tag: &str) -> Result<Option<ParsedLeanMoveReinit>, String> {
    if tag == "MR0" {
        return Ok(None);
    }
    let Some(rest) = tag.strip_prefix("MR1|") else {
        return Err(format!("invalid MR tag {tag:?}"));
    };
    let parts: Vec<&str> = rest.split('|').collect();
    if parts.len() != 6 {
        return Err(format!("malformed MR1 witness tag {tag:?}"));
    }
    let local_slot = parts[0]
        .parse::<usize>()
        .map_err(|e| format!("invalid MR1 local_slot {:?}: {e}", parts[0]))?;
    let total_steps = parts[1]
        .parse::<usize>()
        .map_err(|e| format!("invalid MR1 total_steps {:?}: {e}", parts[1]))?;
    let init_step = parse_mr_coord(parts[2])?;
    let move_step = parse_mr_coord(parts[3])?;
    let reinit_step = parse_mr_coord(parts[4])?;
    let read_step = parse_mr_coord(parts[5])?;
    if !(init_step.step < move_step.step
        && move_step.step < reinit_step.step
        && reinit_step.step < read_step.step
        && read_step.step < total_steps)
    {
        return Err(format!("non-monotonic MR1 step timestamps in {tag:?}"));
    }
    Ok(Some(ParsedLeanMoveReinit {
        local_slot,
        total_steps,
        init_step,
        move_step,
        reinit_step,
        read_step,
    }))
}

fn parse_fuzz_lean_probe_output_ids(
    stdout: &str,
    ids: &[&str],
) -> Result<BTreeMap<String, ParsedLeanFuzzProbeLine>, String> {
    let mut raw_map = BTreeMap::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        let unquoted =
            trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(trimmed);
        let Some(rest) = unquoted.strip_prefix(LEAN_CASE_PREFIX) else {
            continue;
        };
        let Some((id, after_id)) = rest.split_once(':') else {
            return Err(format!("malformed Lean fuzz output line {trimmed:?}"));
        };
        let Some(after_body) = after_id.strip_prefix("BODY|") else {
            return Err(format!("missing BODY binding in Lean fuzz line {trimmed:?}"));
        };
        let mut body_parts = after_body.splitn(3, '|');
        let (Some(body_id_raw), Some(fn_ident), Some(mr_and_payload)) =
            (body_parts.next(), body_parts.next(), body_parts.next())
        else {
            return Err(format!("malformed BODY binding in Lean fuzz line {trimmed:?}"));
        };
        let body_id = body_id_raw.parse::<usize>().map_err(|e| {
            format!("invalid BODY defId {body_id_raw:?} in Lean fuzz line {trimmed:?}: {e}")
        })?;
        if fn_ident.is_empty() {
            return Err(format!("empty BODY fn_identity in Lean fuzz line {trimmed:?}"));
        }
        let Some((mr_tag, payload)) = mr_and_payload.split_once(':') else {
            return Err(format!("missing MR0/MR1 trace tag in Lean fuzz line {trimmed:?}"));
        };
        let move_reinit = parse_mr_witness_tag(mr_tag)?;
        let outcome = parse_lean_payload(payload)?;
        raw_map.insert(
            id.to_owned(),
            ParsedLeanFuzzProbeLine {
                body_id: Some(body_id),
                fn_identity: Some(fn_ident.to_owned()),
                outcome,
                lean_probe_line: Some(unquoted.to_owned()),
                move_reinit,
            },
        );
    }

    let mut out = BTreeMap::new();
    for &id in ids {
        let entry = raw_map.remove(id).unwrap_or_else(|| ParsedLeanFuzzProbeLine {
            body_id: None,
            fn_identity: None,
            outcome: ObservedOutcome::ToolError {
                detail: format!("Lean output missing case {id:?}"),
            },
            lean_probe_line: None,
            move_reinit: None,
        });
        out.insert(id.to_owned(), entry);
    }
    Ok(out)
}

fn bind_fuzz_probe_result_to_capture_body(
    case_id: &str,
    parsed: ParsedLeanFuzzProbeLine,
    capture_body: Option<&FuzzCaptureBody>,
) -> (ObservedOutcome, Option<String>, Option<ParsedLeanMoveReinit>) {
    if parsed.lean_probe_line.is_some() {
        let Some(cb) = capture_body else {
            return (
                ObservedOutcome::ToolError {
                    detail: format!("missing captured body for Lean fuzz probe {case_id}"),
                },
                None,
                None,
            );
        };
        if parsed.body_id != Some(cb.body_id)
            || parsed.fn_identity.as_deref() != Some(cb.fn_identity.as_str())
        {
            return (
                ObservedOutcome::ToolError {
                    detail: format!(
                        "Lean fuzz probe body mismatch for {case_id}: probe reported body_id={:?} identity={:?}, expected body_id={} identity={:?}",
                        parsed.body_id, parsed.fn_identity, cb.body_id, cb.fn_identity
                    ),
                },
                None,
                None,
            );
        }
    }
    (parsed.outcome, parsed.lean_probe_line, parsed.move_reinit)
}

fn shard_module_rel_path(module: &str) -> Result<PathBuf, String> {
    if !module.starts_with("Captured.") {
        return Err(format!(
            "invalid captured shard module {module:?}: must start with \"Captured.\""
        ));
    }
    let mut rel = PathBuf::new();
    for seg in module.split('.') {
        if seg.is_empty() || !seg.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
            return Err(format!(
                "invalid captured shard module {module:?}: unsafe segment {seg:?}"
            ));
        }
        rel.push(seg);
    }
    Ok(rel)
}

/// Validate a capture-reported artifact path BEFORE opening or passing it to
/// Lean: rejects symlink leaves/ancestors, non-regular files, hardlinks
/// (`nlink > 1`), and paths escaping `canon_out_dir`.
fn validate_capture_output_file(
    canon_out_dir: &Path,
    work_dir: &Path,
    raw_path: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    let canon_file =
        crate::mir_eval_runner::validate_executable_no_links(raw_path, work_dir, label)?;
    let rel = canon_file.strip_prefix(canon_out_dir).map_err(|_| {
        format!(
            "{label} escapes capture_out directory {}: {}",
            canon_out_dir.display(),
            canon_file.display()
        )
    })?;
    if rel.as_os_str().is_empty() {
        return Err(format!("{label} must name a file inside {}", canon_out_dir.display()));
    }
    Ok(canon_file)
}

fn load_capture_shards(
    canon_out_dir: &Path,
    work_dir: &Path,
    status_shards: Option<&Path>,
) -> Result<Vec<CaptureShardEntry>, String> {
    let fallback_path = canon_out_dir.join("capture_shards.json");
    let captured_dir = canon_out_dir.join("Captured");
    let valid_path = if let Some(explicit) = status_shards {
        Some(validate_capture_output_file(
            canon_out_dir,
            work_dir,
            explicit,
            "capture shards manifest",
        )?)
    } else if fs::symlink_metadata(&fallback_path).is_ok() {
        Some(validate_capture_output_file(
            canon_out_dir,
            work_dir,
            &fallback_path,
            "capture shards manifest",
        )?)
    } else if fs::symlink_metadata(&captured_dir).is_ok() {
        return Err(format!(
            "captured shard directory {} exists without {}",
            captured_dir.display(),
            fallback_path.display()
        ));
    } else {
        None
    };

    let Some(path) = valid_path else {
        return Ok(Vec::new());
    };
    let raw = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let manifest: CaptureShardsManifest =
        serde_json::from_str(&raw).map_err(|e| format!("parse {}: {e}", path.display()))?;
    if manifest.shards.is_empty() {
        return Err(format!("capture shard manifest {} lists zero shards", path.display()));
    }
    let mut shards = manifest.shards;
    shards.sort_by_key(|entry| entry.shard_idx);
    let mut seen_idxs = BTreeSet::new();
    let mut seen_mods = BTreeSet::new();
    for shard in &shards {
        if !seen_idxs.insert(shard.shard_idx) {
            return Err(format!("duplicate shard_idx {} in {}", shard.shard_idx, path.display()));
        }
        let _ = shard_module_rel_path(&shard.capture_module)?;
        if !seen_mods.insert(shard.capture_module.clone()) {
            return Err(format!(
                "duplicate capture_module {:?} in {}",
                shard.capture_module,
                path.display()
            ));
        }
    }
    Ok(shards)
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

#[derive(Clone, Copy)]
struct LeanPreparedEnv<'a> {
    ld_library_path: &'a str,
    child_path: &'a OsStr,
    validated_tmpdir: Option<&'a Path>,
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

fn query_lean_prefix_with_env(
    lean_bin: &Path,
    prepared_env: Option<LeanPreparedEnv<'_>>,
) -> Result<PathBuf, String> {
    query_lean_prefix_with_env_and_tmp(
        lean_bin,
        prepared_env,
        prepared_env.and_then(|e| e.validated_tmpdir),
    )
}

fn query_lean_prefix_with_env_and_tmp(
    lean_bin: &Path,
    prepared_env: Option<LeanPreparedEnv<'_>>,
    validated_tmpdir: Option<&Path>,
) -> Result<PathBuf, String> {
    let work_dir = lean_bin.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_lean_with_optional_env(
        Invocation::new(lean_bin, &["--print-prefix"]),
        lean_bin,
        work_dir,
        effective_timeout_secs(LEAN_PROBE_TIMEOUT_SECS)?,
        prepared_env,
        validated_tmpdir,
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
fn is_lean_sysroot_artifact_rel_for_packages(rel: &str, packages: &[&str]) -> bool {
    let has_ext = LEAN_ARTIFACT_EXTS.iter().any(|ext| rel.ends_with(&format!(".{ext}")));
    if !has_ext {
        return false;
    }
    packages
        .iter()
        .any(|pkg| rel.starts_with(&format!("{pkg}/")) || rel.starts_with(&format!("{pkg}.")))
}

fn is_lean_sysroot_artifact_rel(rel: &str) -> bool {
    is_lean_sysroot_artifact_rel_for_packages(rel, LEAN_SYSROOT_PACKAGES)
}

fn collect_lean_sysroot_artifact_entries(
    lean_stdlib: &Path,
    packages: &[&str],
) -> Result<BTreeMap<String, String>, String> {
    #[cfg(unix)]
    {
        use std::os::fd::{AsFd as _, OwnedFd};

        let root_fd =
            crate::rustc_runner::open_dir_handle_no_symlinks(lean_stdlib, None, "Lean sysroot")?;
        let mut out = BTreeMap::new();
        let top_entries =
            crate::rustc_runner::read_dir_entries_from_fd(root_fd.as_fd(), "Lean sysroot")?;
        let mut stack: Vec<(OwnedFd, PathBuf)> = Vec::new();
        for entry in top_entries {
            let Some(name_str) = entry.os_name.to_str() else {
                continue;
            };
            if crate::rustc_runner::is_dir_mode(&entry.stat) {
                if packages.contains(&name_str) {
                    let child = crate::rustc_runner::open_child_dir_nofollow(
                        root_fd.as_fd(),
                        &entry.c_name,
                        Some(crate::rustc_runner::stat_dev_ino(&entry.stat)),
                        "Lean sysroot",
                    )?;
                    stack.push((child, PathBuf::from(&entry.os_name)));
                }
            } else if crate::rustc_runner::is_lnk_mode(&entry.stat) {
                if is_lean_sysroot_artifact_rel_for_packages(name_str, packages)
                    || packages.contains(&name_str)
                {
                    return Err(format!("symlink forbidden in Lean sysroot: {name_str}"));
                }
            } else if crate::rustc_runner::is_reg_mode(&entry.stat)
                && is_lean_sysroot_artifact_rel_for_packages(name_str, packages)
            {
                let mut f = crate::rustc_runner::open_regular_file_from_fd(
                    root_fd.as_fd(),
                    &entry.c_name,
                    Some(crate::rustc_runner::stat_dev_ino(&entry.stat)),
                    false,
                    "Lean sysroot",
                )?
                .0;
                let sha = crate::rustc_runner::sha256_opened_file_hex(&mut f, name_str)?;
                out.insert(name_str.to_owned(), sha);
            } else if is_lean_sysroot_artifact_rel_for_packages(name_str, packages) {
                return Err(format!("unexpected non-regular entry in Lean sysroot: {name_str}"));
            }
        }
        while let Some((dir_fd, rel_prefix)) = stack.pop() {
            let entries =
                crate::rustc_runner::read_dir_entries_from_fd(dir_fd.as_fd(), "Lean sysroot")?;
            for entry in entries {
                let next_rel = rel_prefix.join(&entry.os_name);
                if crate::rustc_runner::is_lnk_mode(&entry.stat) {
                    return Err(format!(
                        "symlink forbidden in Lean sysroot: {}",
                        next_rel.display()
                    ));
                } else if crate::rustc_runner::is_dir_mode(&entry.stat) {
                    let child = crate::rustc_runner::open_child_dir_nofollow(
                        dir_fd.as_fd(),
                        &entry.c_name,
                        Some(crate::rustc_runner::stat_dev_ino(&entry.stat)),
                        "Lean sysroot",
                    )?;
                    stack.push((child, next_rel));
                } else if crate::rustc_runner::is_reg_mode(&entry.stat) {
                    let rel_key =
                        crate::rustc_runner::path_slashes_utf8(&next_rel, "Lean sysroot")?;
                    if LEAN_ARTIFACT_EXTS.iter().any(|ext| rel_key.ends_with(&format!(".{ext}"))) {
                        let mut f = crate::rustc_runner::open_regular_file_from_fd(
                            dir_fd.as_fd(),
                            &entry.c_name,
                            Some(crate::rustc_runner::stat_dev_ino(&entry.stat)),
                            false,
                            "Lean sysroot",
                        )?
                        .0;
                        let sha = crate::rustc_runner::sha256_opened_file_hex(&mut f, &rel_key)?;
                        out.insert(rel_key, sha);
                    }
                } else {
                    return Err(format!(
                        "unexpected non-regular entry in Lean sysroot: {}",
                        next_rel.display()
                    ));
                }
            }
        }
        Ok(out)
    }
    #[cfg(not(unix))]
    {
        Ok(crate::rustc_runner::collect_rel_file_sha256s_nofollow(
            lean_stdlib,
            None,
            "Lean sysroot",
        )?
        .into_iter()
        .filter(|(rel, _)| is_lean_sysroot_artifact_rel_for_packages(rel, packages))
        .collect())
    }
}

pub(crate) fn compute_lean_sysroot_manifest_sha256(lean_stdlib: &Path) -> Result<String, String> {
    compute_lean_sysroot_manifest_sha256_inner(lean_stdlib, None, None)
}

fn compute_lean_sysroot_manifest_sha256_inner(
    lean_stdlib: &Path,
    stdlib_guard: Option<&crate::rustc_runner::ImmutableStagingDir>,
    source_lib_lean_dir: Option<&Path>,
) -> Result<String, String> {
    let mut entries: BTreeMap<String, String> = if let Some(guard) = stdlib_guard {
        guard
            .collect_rel_file_sha256s(Some(Path::new("lib/lean")), None, "Lean sysroot")?
            .into_iter()
            .filter(|(rel, _)| is_lean_sysroot_artifact_rel(rel))
            .collect()
    } else {
        collect_lean_sysroot_artifact_entries(lean_stdlib, LEAN_SYSROOT_PACKAGES)?
    };
    if let Some(orig_lib_lean) = source_lib_lean_dir {
        let omitted = collect_lean_sysroot_artifact_entries(
            orig_lib_lean,
            crate::rustc_runner::LEAN_RUNTIME_OMITTED_SYSROOT_PACKAGES,
        )?;
        for (rel, sha) in omitted {
            entries.entry(rel).or_insert(sha);
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

fn compute_lean_cache_key_with_env(
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    active_sysroot_sha: &str,
    overlay: &VerifiedPrebuiltOverlay,
    prepared_env: Option<LeanPreparedEnv<'_>>,
) -> Result<String, String> {
    let work_dir = lean_bin.parent().unwrap_or_else(|| Path::new("/"));
    let ver = run_lean_with_optional_env(
        Invocation::new(lean_bin, &["--version"]),
        lean_bin,
        work_dir,
        effective_timeout_secs(LEAN_PROBE_TIMEOUT_SECS)?,
        prepared_env,
        prepared_env.and_then(|e| e.validated_tmpdir),
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

#[allow(clippy::too_many_arguments)]
fn ensure_lean_dag_oleans_in_tmp_inner(
    anneal_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    stdlib_guard: Option<&crate::rustc_runner::ImmutableStagingDir>,
    source_lib_lean_dir: Option<&Path>,
    prebuilt_dir: Option<&Path>,
    cache: LeanCacheRoot<'_>,
    prepared_env: Option<LeanPreparedEnv<'_>>,
) -> Result<(Vec<PathBuf>, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    let active_sysroot_sha =
        compute_lean_sysroot_manifest_sha256_inner(lean_stdlib, stdlib_guard, source_lib_lean_dir)?;
    let overlay = inspect_prebuilt_overlay(
        prebuilt_dir,
        MIR_TOTAL_DAG,
        anneal_root,
        lean_bin,
        &active_sysroot_sha,
    )?;
    let key = compute_lean_cache_key_with_env(
        MIR_TOTAL_DAG,
        anneal_root,
        lean_bin,
        &active_sysroot_sha,
        &overlay,
        prepared_env,
    )?;
    let dir_prefix =
        if overlay.modules.is_empty() { "lean-mirtotal-full" } else { "lean-mirtotal-overlay" };
    let out_rel = PathBuf::from(format!("{dir_prefix}-{key}"));
    let lock_rel = PathBuf::from(format!("{dir_prefix}-{key}.lock"));
    let (out_dir, lock_path, pinned_rel) = match cache {
        LeanCacheRoot::Path(cache_root) => {
            fs::create_dir_all(cache_root)
                .map_err(|e| format!("create cache root {}: {e}", cache_root.display()))?;
            (cache_root.join(&out_rel), cache_root.join(&lock_rel), None)
        }
        LeanCacheRoot::Pinned(pinned) => (
            pinned.pin_path(&out_rel),
            pinned.pin_path(&lock_rel),
            Some((pinned, out_rel.as_path())),
        ),
    };
    let pinned_stdlib =
        stdlib_guard.map_or_else(|| lean_stdlib.to_path_buf(), |g| g.pin_path(lean_stdlib));
    ensure_dag_with_verified_overlay_in(
        MIR_TOTAL_DAG,
        anneal_root,
        lean_bin,
        &pinned_stdlib,
        &overlay,
        &out_dir,
        pinned_rel,
        &lock_path,
        prepared_env,
        true,
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

#[allow(clippy::too_many_arguments)]
fn synthesize_missing_eval_ir(
    dag: &[LeanDagSpec],
    staged: &BTreeSet<&'static str>,
    base_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    out_dir: &Path,
    compile_timeout: u64,
    prepared_env: Option<LeanPreparedEnv<'_>>,
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
            let res = run_lean_with_optional_env(
                Invocation::new(lean_bin, LEAN_COMPILE_FLAGS)
                    .arg("-R")
                    .arg(&tree_root)
                    .arg("-o")
                    .arg(&scratch_olean)
                    .arg(&src)
                    .env("LEAN_PATH", &ir_lean_path),
                lean_bin,
                &tree_root,
                compile_timeout,
                prepared_env,
                prepared_env.and_then(|e| e.validated_tmpdir),
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

#[derive(Debug, Deserialize, Serialize)]
struct LeanDagCacheStamp {
    version: u32,
    label: String,
    files: BTreeMap<String, String>,
}

const LEAN_DAG_CACHE_STAMP_VERSION: u32 = 2;

fn expected_dag_cache_label(dag: &[LeanDagSpec], overlay: &VerifiedPrebuiltOverlay) -> String {
    let mut staged: BTreeSet<&'static str> = BTreeSet::new();
    for spec in dag {
        if overlay.modules.contains_key(spec.module) && spec.deps.iter().all(|d| staged.contains(d))
        {
            staged.insert(spec.module);
        }
    }
    if staged.is_empty() {
        overlay.fallback_label.clone()
    } else {
        format!("staged:{}/{}", staged.len(), dag.len())
    }
}

fn collect_dag_cache_file_digests(out_dir: &Path) -> Result<BTreeMap<String, String>, String> {
    crate::rustc_runner::collect_rel_file_sha256s_nofollow(
        out_dir,
        Some(Path::new(".anneal-oleans-ready")),
        "Lean DAG cache",
    )
}

#[cfg_attr(not(test), allow(dead_code))]
fn verify_and_read_dag_cache_stamp(
    out_dir: &Path,
    dag: &[LeanDagSpec],
    expected_label: &str,
) -> Option<String> {
    verify_dag_cache_stamp_with_staging(out_dir, None, dag, expected_label)
}

fn verify_dag_cache_stamp_from_parts(
    mut ready_file: File,
    disk_files: BTreeMap<String, String>,
    dag: &[LeanDagSpec],
    expected_label: &str,
) -> Option<String> {
    let mut raw = String::new();
    std::io::Read::read_to_string(&mut ready_file, &mut raw).ok()?;
    let stamp: LeanDagCacheStamp = serde_json::from_str(&raw).ok()?;
    if stamp.version != LEAN_DAG_CACHE_STAMP_VERSION || stamp.label != expected_label {
        return None;
    }
    for spec in dag {
        let rel_olean = format!("{}.olean", spec.module.replace('.', "/"));
        if !disk_files.contains_key(&rel_olean) {
            return None;
        }
    }
    if disk_files.len() != stamp.files.len() {
        return None;
    }
    for (k, expected_sha) in &stamp.files {
        let actual_sha = disk_files.get(k)?;
        if !actual_sha.eq_ignore_ascii_case(expected_sha) {
            return None;
        }
    }
    Some(stamp.label)
}

fn verify_dag_cache_stamp_from_pinned(
    pinned: &crate::rustc_runner::PinnedPrivateDir,
    rel_dir: &Path,
    dag: &[LeanDagSpec],
    expected_label: &str,
) -> Option<String> {
    if !pinned.has_rel_dir(rel_dir, "Lean DAG cache") {
        return None;
    }
    let ready = pinned
        .open_verified_rel_file(&rel_dir.join(".anneal-oleans-ready"), "Lean DAG stamp")
        .ok()?;
    let files = pinned
        .collect_rel_file_sha256s(
            Some(rel_dir),
            Some(Path::new(".anneal-oleans-ready")),
            "Lean DAG cache",
        )
        .ok()?;
    verify_dag_cache_stamp_from_parts(ready, files, dag, expected_label)
}

fn verify_dag_cache_stamp_with_staging(
    out_dir: &Path,
    staging: Option<&crate::rustc_runner::ImmutableStagingDir>,
    dag: &[LeanDagSpec],
    expected_label: &str,
) -> Option<String> {
    let (ready_file, disk_files) = if let Some(guard) = staging {
        let ready = guard
            .open_verified_rel_file(Path::new("dag/.anneal-oleans-ready"), "Lean DAG stamp")
            .ok()?;
        let files = guard
            .collect_rel_file_sha256s(
                Some(Path::new("dag")),
                Some(Path::new(".anneal-oleans-ready")),
                "Lean DAG cache",
            )
            .ok()?;
        (ready, files)
    } else {
        #[cfg(unix)]
        {
            use std::os::fd::AsFd as _;
            let out_fd =
                crate::rustc_runner::open_dir_handle_no_symlinks(out_dir, None, "Lean DAG cache")
                    .ok()?;
            let (ready, _) = crate::rustc_runner::open_regular_file_from_fd(
                out_fd.as_fd(),
                c".anneal-oleans-ready",
                None,
                false,
                "Lean DAG stamp",
            )
            .ok()?;
            let files = crate::rustc_runner::collect_rel_file_sha256s_from_fd(
                out_fd.as_fd(),
                Some(Path::new(".anneal-oleans-ready")),
                "Lean DAG cache",
            )
            .ok()?;
            (ready, files)
        }
        #[cfg(not(unix))]
        {
            let dir_meta = fs::symlink_metadata(out_dir).ok()?;
            if dir_meta.file_type().is_symlink() || !dir_meta.is_dir() {
                return None;
            }
            let ready = out_dir.join(".anneal-oleans-ready");
            let ready_meta = fs::symlink_metadata(&ready).ok()?;
            if ready_meta.file_type().is_symlink()
                || !ready_meta.is_file()
                || crate::rustc_runner::hardlink_count(&ready_meta) > 1
            {
                return None;
            }
            let ready_file = File::open(&ready).ok()?;
            let files = collect_dag_cache_file_digests(out_dir).ok()?;
            (ready_file, files)
        }
    };
    verify_dag_cache_stamp_from_parts(ready_file, disk_files, dag, expected_label)
}

fn write_dag_cache_stamp_in(
    out_dir: &Path,
    pinned: Option<(&crate::rustc_runner::PinnedPrivateDir, &Path)>,
    dag: &[LeanDagSpec],
    overlay_label: &str,
) -> Result<(), String> {
    use std::io::Write as _;

    let ready = out_dir.join(".anneal-oleans-ready");
    if fs::symlink_metadata(&ready).is_ok() {
        fs::remove_file(&ready)
            .map_err(|e| format!("remove stale Lean ready stamp {}: {e}", ready.display()))?;
    }
    let files = if let Some((pin, rel_dir)) = pinned {
        pin.collect_rel_file_sha256s(
            Some(rel_dir),
            Some(Path::new(".anneal-oleans-ready")),
            "Lean DAG cache",
        )?
    } else {
        collect_dag_cache_file_digests(out_dir)?
    };
    for spec in dag {
        let rel_olean = format!("{}.olean", spec.module.replace('.', "/"));
        if !files.contains_key(&rel_olean) {
            return Err(format!(
                "missing compiled `.olean` for {} in {}",
                spec.module,
                out_dir.display()
            ));
        }
    }
    let payload = serde_json::to_string_pretty(&LeanDagCacheStamp {
        version: LEAN_DAG_CACHE_STAMP_VERSION,
        label: overlay_label.to_owned(),
        files,
    })
    .map_err(|e| format!("serialize Lean ready stamp: {e}"))?;

    let mut opts = fs::OpenOptions::new();
    opts.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let mut file = opts
        .open(&ready)
        .map_err(|e| format!("write Lean ready stamp {}: {e}", ready.display()))?;
    file.write_all(payload.as_bytes())
        .map_err(|e| format!("write Lean ready stamp {}: {e}", ready.display()))?;
    file.write_all(b"\n")
        .map_err(|e| format!("flush Lean ready stamp {}: {e}", ready.display()))?;
    file.flush().map_err(|e| format!("flush Lean ready stamp {}: {e}", ready.display()))?;
    Ok(())
}

#[cfg(test)]
fn stage_and_verify_lean_dag_dir(
    out_dir: &Path,
    dag: &[LeanDagSpec],
    expected_label: &str,
) -> Result<(PathBuf, Arc<crate::rustc_runner::ImmutableStagingDir>), String> {
    stage_and_verify_lean_dag_dir_in(out_dir, None, dag, expected_label)
}

#[cfg(test)]
fn stage_and_verify_lean_dag_dir_in(
    out_dir: &Path,
    pinned: Option<(&crate::rustc_runner::PinnedPrivateDir, &Path)>,
    dag: &[LeanDagSpec],
    expected_label: &str,
) -> Result<(PathBuf, Arc<crate::rustc_runner::ImmutableStagingDir>), String> {
    stage_and_verify_lean_dag_dir_in_tmp(out_dir, pinned, None, dag, expected_label)
}

fn stage_and_verify_lean_dag_dir_in_tmp(
    out_dir: &Path,
    pinned: Option<(&crate::rustc_runner::PinnedPrivateDir, &Path)>,
    tmp_parent: Option<&Path>,
    dag: &[LeanDagSpec],
    expected_label: &str,
) -> Result<(PathBuf, Arc<crate::rustc_runner::ImmutableStagingDir>), String> {
    let (staged_dag, guard) =
        stage_immutable_lean_dir_in_tmp(out_dir, pinned, "dag", tmp_parent, "Lean DAG cache")?;
    if verify_dag_cache_stamp_with_staging(&staged_dag, Some(&guard), dag, expected_label).is_none()
    {
        return Err(format!(
            "frozen Lean DAG cache failed `.anneal-oleans-ready` verification: {}",
            staged_dag.display()
        ));
    }
    Ok((staged_dag, guard))
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(not(test), allow(dead_code))]
fn ensure_dag_with_overlay(
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    prebuilt_dir: Option<&Path>,
    out_dir: &Path,
    lock_path: &Path,
    prepared_env: Option<LeanPreparedEnv<'_>>,
) -> Result<(Vec<PathBuf>, String), String> {
    let active_sysroot_sha = compute_lean_sysroot_manifest_sha256(lean_stdlib)?;
    let overlay =
        inspect_prebuilt_overlay(prebuilt_dir, dag, base_root, lean_bin, &active_sysroot_sha)?;
    let (paths, label, _) = ensure_dag_with_verified_overlay(
        dag,
        base_root,
        lean_bin,
        lean_stdlib,
        &overlay,
        out_dir,
        lock_path,
        prepared_env,
        false,
    )?;
    Ok((paths, label))
}

#[allow(clippy::too_many_arguments)]
fn ensure_dag_with_verified_overlay(
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    overlay: &VerifiedPrebuiltOverlay,
    out_dir: &Path,
    lock_path: &Path,
    prepared_env: Option<LeanPreparedEnv<'_>>,
    stage_immutable: bool,
) -> Result<(Vec<PathBuf>, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    ensure_dag_with_verified_overlay_in(
        dag,
        base_root,
        lean_bin,
        lean_stdlib,
        overlay,
        out_dir,
        None,
        lock_path,
        prepared_env,
        stage_immutable,
    )
}

#[allow(clippy::too_many_arguments)]
fn ensure_dag_with_verified_overlay_in(
    dag: &[LeanDagSpec],
    base_root: &Path,
    lean_bin: &Path,
    lean_stdlib: &Path,
    overlay: &VerifiedPrebuiltOverlay,
    out_dir: &Path,
    pinned: Option<(&crate::rustc_runner::PinnedPrivateDir, &Path)>,
    lock_path: &Path,
    prepared_env: Option<LeanPreparedEnv<'_>>,
    stage_immutable: bool,
) -> Result<(Vec<PathBuf>, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    let lock_file = File::options()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(lock_path)
        .map_err(|e| format!("open Lean cache lock {}: {e}", lock_path.display()))?;
    lock_file.lock().map_err(|e| format!("lock Lean cache {}: {e}", lock_path.display()))?;

    // Always place all prebuilt + newly compiled module roots inside `out_dir`
    // so `LEAN_PATH` has a single workspace root before `lean_stdlib`.
    let mut search_paths = vec![out_dir.to_path_buf(), lean_stdlib.to_path_buf()];
    let lean_path = env::join_paths(&search_paths)
        .map_err(|e| format!("join LEAN_PATH: {e}"))?
        .to_string_lossy()
        .into_owned();

    let compile_timeout = effective_timeout_secs(LEAN_COMPILE_TIMEOUT_SECS)?;
    let expected_label = expected_dag_cache_label(dag, overlay);
    let overlay_label;
    let verified = match pinned {
        Some((pin, rel_dir)) => {
            verify_dag_cache_stamp_from_pinned(pin, rel_dir, dag, &expected_label)
        }
        None => verify_and_read_dag_cache_stamp(out_dir, dag, &expected_label),
    };
    if let Some(verified_label) = verified {
        overlay_label = verified_label;
    } else {
        // Wipe any unstamped, partial, or tampered `.olean` directory under the
        // lock so stale or substituted artifacts can never poison the cache.
        if let Ok(meta) = fs::symlink_metadata(out_dir) {
            if meta.file_type().is_symlink() || !meta.is_dir() {
                fs::remove_file(out_dir)
                    .map_err(|e| format!("wipe Lean cache entry {}: {e}", out_dir.display()))?;
            } else {
                fs::remove_dir_all(out_dir)
                    .map_err(|e| format!("wipe Lean cache {}: {e}", out_dir.display()))?;
            }
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
            prepared_env,
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

            let validated_tmpdir = prepared_env.and_then(|e| e.validated_tmpdir);
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
                            let res = run_lean_with_optional_env(
                                Invocation::new(lean_bin, LEAN_COMPILE_FLAGS)
                                    .arg("-R")
                                    .arg(&tree_root)
                                    .arg("-o")
                                    .arg(&dst)
                                    .arg(&src)
                                    .env("LEAN_PATH", lean_path_ref),
                                lean_bin,
                                &tree_root,
                                compile_timeout,
                                prepared_env,
                                validated_tmpdir,
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
        write_dag_cache_stamp_in(out_dir, pinned, dag, &overlay_label)?;
    }
    let staging_guard = if stage_immutable {
        let (staged_dag, guard) = stage_and_verify_lean_dag_dir_in_tmp(
            out_dir,
            pinned,
            prepared_env.and_then(|e| e.validated_tmpdir),
            dag,
            &overlay_label,
        )?;
        search_paths[0] = staged_dag;
        Some(guard)
    } else {
        None
    };
    drop(lock_file);

    Ok((search_paths, overlay_label, staging_guard))
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
        "UNWOUND" => Ok(ObservedOutcome::Unwound {
            detail: "Trusted.MirModel.TerminalOut.unwound".to_owned(),
        }),
        "ABORTED" => Ok(ObservedOutcome::AbnormalAbort {
            detail: "Trusted.MirModel.TerminalOut.aborted".to_owned(),
        }),
        _ => {
            if let Some(cause) = payload.strip_prefix("FAULT:undefined:") {
                let detail = if cause.is_empty() {
                    "Trusted.MirSemantics.FaultKind.undefined".to_owned()
                } else {
                    format!("Trusted.MirSemantics.FaultKind.undefined ({cause})")
                };
                return Ok(ObservedOutcome::UndefinedBehavior { detail });
            }
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
        assert!(matches!(parse_lean_payload("UNWOUND").unwrap(), ObservedOutcome::Unwound { .. }));
    }

    #[test]
    fn classify_single_capture_failure_accepts_only_unsupported_status() {
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            let exit_1 = Termination::Exited(std::process::ExitStatus::from_raw(1 << 8));
            let unsup = classify_single_capture_failure(
                &exit_1,
                "{\"status\":\"unsupported\",\"diagnostics\":[\"1 unsupported\"],\"unsupported\":[]}\n",
                "",
                None,
            );
            assert!(unsup.capture_rejected.is_some());
            assert!(unsup.capture_refusal_json.is_some());
            assert!(matches!(unsup.outcome, ObservedOutcome::Unsupported { .. }));
            let bound_json = "{\"status\":\"unsupported\",\"diagnostics\":[\"1 required obligations are unsupported\"],\"unsupported\":[{\"def_id\":1,\"path\":\"fuzz_batch::fuzz_case_0003\",\"reason\":\"unsupported intrinsic\"}]}";
            let bound_ok = classify_single_capture_failure(
                &exit_1,
                &format!("{bound_json}\n"),
                "",
                Some("fuzz_case_0003"),
            );
            assert!(bound_ok.capture_rejected.is_some());
            assert_eq!(bound_ok.capture_refusal_json.as_deref(), Some(bound_json));
            for bad_bound in [
                "{\"status\":\"unsupported\",\"diagnostics\":[\"1 unsupported\"],\"unsupported\":[]}\n",
                "{\"status\":\"unsupported\",\"diagnostics\":[\"1 unsupported\"],\"unsupported\":[{\"def_id\":1,\"path\":\"fuzz_batch::other_fn\",\"reason\":\"unsupported\"}]}\n",
            ] {
                let rej =
                    classify_single_capture_failure(&exit_1, bad_bound, "", Some("fuzz_case_0003"));
                assert!(rej.capture_rejected.is_none());
                assert!(rej.capture_refusal_json.is_none());
                assert!(matches!(rej.outcome, ObservedOutcome::ToolError { .. }));
            }
            assert!(is_bisectable_capture_rejection(
                &exit_1,
                "{\"status\":\"unsupported\",\"diagnostics\":[\"1 unsupported\"]}\n",
            ));

            let tool_fail = classify_single_capture_failure(
                &exit_1,
                "{\"status\":\"tool_failed\",\"diagnostics\":[\"panicked\"],\"unsupported\":[]}\n",
                "thread 'rustc' panicked",
                None,
            );
            assert!(tool_fail.capture_rejected.is_none());
            assert!(matches!(tool_fail.outcome, ObservedOutcome::ToolError { .. }));
            assert!(!is_bisectable_capture_rejection(
                &exit_1,
                "{\"status\":\"tool_failed\",\"diagnostics\":[\"panicked\"]}\n",
            ));
            assert!(!is_bisectable_capture_rejection(
                &Termination::TimedOut(std::process::ExitStatus::from_raw(9)),
                "{\"status\":\"unsupported\",\"diagnostics\":[\"stalled\"]}\n",
            ));

            assert!(is_bisectable_capture_rejection(
                &exit_1,
                "{\"status\":\"compiler_failed\",\"diagnostics\":[\"syntax error\"]}\n",
            ));

            let comp_fail = classify_single_capture_failure(
                &exit_1,
                "{\"status\":\"compiler_failed\",\"diagnostics\":[\"syntax error\"],\"unsupported\":[]}\n",
                "",
                None,
            );
            assert!(comp_fail.capture_rejected.is_none());
            assert!(matches!(comp_fail.outcome, ObservedOutcome::ToolError { .. }));

            let garbage = classify_single_capture_failure(&exit_1, "not json\n", "boom", None);
            assert!(garbage.capture_rejected.is_none());
            assert!(matches!(garbage.outcome, ObservedOutcome::ToolError { .. }));

            let sig = Termination::Exited(std::process::ExitStatus::from_raw(9));
            let killed = classify_single_capture_failure(
                &sig,
                "{\"status\":\"unsupported\",\"diagnostics\":[],\"unsupported\":[]}\n",
                "",
                None,
            );
            assert!(killed.capture_rejected.is_none());
            assert!(matches!(killed.outcome, ObservedOutcome::ToolError { .. }));
        }
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
        let raw_lean_bin = fs::canonicalize(default_lean_path().expect("resolve pinned lean"))
            .expect("canonicalize lean");
        let caller_cwd = env::current_dir().expect("cwd");
        let store_prefix = Path::new(crate::rustc_runner::STORE_PREFIX);
        let trusted_child_dirs: Vec<&Path> =
            crate::rustc_runner::TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
        let prepared_lean = crate::rustc_runner::prepare_lean_library_path(
            &raw_lean_bin,
            store_prefix,
            &caller_cwd,
        )
        .expect("stage lean toolchain once for overlay test");
        let lean_bin = prepared_lean.lean_bin.clone();
        let valid_lean_bin_dir = crate::rustc_runner::validated_store_aware_dir(
            &prepared_lean.bin_dir,
            store_prefix,
            &caller_cwd,
            "Lean bin dir",
        )
        .expect("validated staged Lean bin dir");
        let lean_child_path = crate::rustc_runner::build_child_path_with_bins(
            &[&valid_lean_bin_dir],
            None,
            store_prefix,
            &trusted_child_dirs,
            env::var_os("PATH").as_deref(),
            &caller_cwd,
        )
        .expect("build staged Lean child PATH");
        let lean_tool_env = LeanPreparedEnv {
            ld_library_path: &prepared_lean.ld_library_path,
            child_path: &lean_child_path,
            validated_tmpdir: None,
        };
        let lean_prefix =
            query_lean_prefix_with_env(&lean_bin, Some(lean_tool_env)).expect("query lean prefix");
        let (lean_stdlib, _stdlib_staging) = resolve_immutable_lean_stdlib_in(
            &lean_prefix,
            &lean_bin,
            &prepared_lean,
            store_prefix,
            &caller_cwd,
            None,
        )
        .expect("resolve immutable lean stdlib");
        let active_sysroot_sha =
            compute_lean_sysroot_manifest_sha256(&lean_stdlib).expect("hash active lean stdlib");
        let run_test_lean = |inv: Invocation, work_dir: &Path, timeout: u64, ctx: &str| {
            run_lean_with_optional_env(
                inv,
                &lean_bin,
                work_dir,
                timeout,
                Some(lean_tool_env),
                None,
                ctx,
            )
        };

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
        #[cfg(unix)]
        {
            let alias = sys_tmp.path().join("alias.olean");
            fs::hard_link(mock_stdlib.join("Init/Core.olean"), &alias).unwrap();
            let err_hard = compute_lean_sysroot_manifest_sha256(&mock_stdlib).unwrap_err();
            assert!(err_hard.contains("hardlink"), "{err_hard}");
            fs::remove_file(&alias).unwrap();
        }

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
        let base_res = run_test_lean(
            Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-R")
                .arg(&src_tree)
                .arg("-o")
                .arg(prebuilt.join("lib/TestRoot/Base.olean"))
                .arg(&base_src)
                .env("LEAN_PATH", &lean_stdlib),
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
            Some(lean_tool_env),
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
        let skip_dep_res = run_test_lean(
            Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-R")
                .arg(&src_tree)
                .arg("-o")
                .arg(prebuilt.join("lib/SkipIrDep/Leaf.olean"))
                .arg(&skip_dep_src)
                .env("LEAN_PATH", &lean_stdlib),
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
        let child_res = run_test_lean(
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
        let synth_host_res = run_test_lean(
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
            Some(lean_tool_env),
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
        let cap_res = run_test_lean(
            Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                .arg("-R")
                .arg(&cap_dir)
                .arg("-o")
                .arg(cap_dir.join("Captured.olean"))
                .arg(&cap_src)
                .env("LEAN_PATH", &cap_lean_path),
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
        let v2_eval = run_test_lean(
            Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                .arg(&v2_probe)
                .env("LEAN_PATH", &cap_lean_path),
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
            Some(lean_tool_env),
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
            Some(lean_tool_env),
        )
        .expect("modified source must compile fresh rather than failing on stale prebuilt");
        assert_eq!(stale_status, "skipped:digest_mismatch");

        let eval_probe = tmp.path().join("EvalChild.lean");
        fs::write(&eval_probe, "import TestRoot.Child\n#eval childVal\n").unwrap();
        let stale_lean_path = env::join_paths(&stale_paths).unwrap();
        let eval_res = run_test_lean(
            Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                .arg(&eval_probe)
                .env("LEAN_PATH", &stale_lean_path),
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
            Some(lean_tool_env),
        )
        .expect("unstamped partial cache must be wiped and rebuilt cleanly");
        assert_eq!(clean_status, "none");
        assert!(!partial_out.join("TestRoot/StaleJunk.txt").exists());
        assert!(partial_out.join(".anneal-oleans-ready").is_file());

        // Tampering a cached `.olean` or injecting an unmanifested file despite
        // a present `.anneal-oleans-ready` MUST fail verification, wipe, and
        // rebuild cleanly from source.
        let good_base_sha = sha256_file_hex(&partial_out.join("TestRoot/Base.olean")).unwrap();
        fs::write(partial_out.join("TestRoot/Base.olean"), b"poisoned-base-olean").unwrap();
        fs::write(partial_out.join("TestRoot/Injected.olean"), b"injected-olean").unwrap();
        let (_, rebuilt_status) = ensure_dag_with_overlay(
            &dag,
            tmp.path(),
            &lean_bin,
            &lean_stdlib,
            None,
            &partial_out,
            &partial_lock,
            Some(lean_tool_env),
        )
        .expect("tampered cache must wipe and rebuild cleanly");
        assert_eq!(rebuilt_status, "none");
        assert!(!partial_out.join("TestRoot/Injected.olean").exists());
        assert_eq!(
            sha256_file_hex(&partial_out.join("TestRoot/Base.olean")).unwrap(),
            good_base_sha
        );

        // Frozen immutable Lean DAG staging under lock (`stage_immutable=true`)
        // freezes `out_dir`, verifies `.anneal-oleans-ready` on the frozen
        // copy, and stays immune to post-staging source cache tamper.
        let no_overlay =
            inspect_prebuilt_overlay(None, &dag, tmp.path(), &lean_bin, &active_sysroot_sha)
                .unwrap();
        let (staged_paths, staged_status, staged_guard) = ensure_dag_with_verified_overlay(
            &dag,
            tmp.path(),
            &lean_bin,
            &lean_stdlib,
            &no_overlay,
            &partial_out,
            &partial_lock,
            Some(lean_tool_env),
            true,
        )
        .expect("locked immutable Lean DAG staging and verification must pass");
        assert_eq!(staged_status, "none");
        let _staged_guard = staged_guard.expect("stage_immutable=true must retain guard");
        let staged_dag = &staged_paths[0];
        assert_ne!(staged_dag, &partial_out);
        #[cfg(unix)]
        {
            use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};
            let dag_meta = fs::symlink_metadata(staged_dag).unwrap();
            assert_eq!(dag_meta.permissions().mode() & 0o777, 0o555);
            let olean_meta = fs::symlink_metadata(staged_dag.join("TestRoot/Base.olean")).unwrap();
            assert_eq!(olean_meta.permissions().mode() & 0o777, 0o444);
            assert_eq!(olean_meta.nlink(), 1);
        }
        assert!(verify_and_read_dag_cache_stamp(staged_dag, &dag, "none").is_some());
        let bad_label_err = stage_and_verify_lean_dag_dir(&partial_out, &dag, "wrong").unwrap_err();
        assert!(bad_label_err.contains("frozen Lean DAG cache failed"), "{bad_label_err}");
        fs::write(partial_out.join("TestRoot/Base.olean"), b"post-freeze-poison").unwrap();
        assert_eq!(
            sha256_file_hex(&staged_dag.join("TestRoot/Base.olean")).unwrap(),
            good_base_sha
        );
        let tampered_stage_err =
            stage_and_verify_lean_dag_dir(&partial_out, &dag, "none").unwrap_err();
        assert!(
            tampered_stage_err.contains("frozen Lean DAG cache failed"),
            "{tampered_stage_err}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn runtime_init_only_lean_staging_preserves_full_prebuilt_sysroot_manifest() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon tempdir");
        let fake_store = base.join("nix-store");
        fs::create_dir_all(&fake_store).unwrap();

        let lean_tc = base.join("lean-install-root");
        let orig_lib_lean = lean_tc.join("lib/lean");
        for dir in ["Init", "Std", "Lean", "Lake"] {
            fs::create_dir_all(orig_lib_lean.join(dir)).unwrap();
        }
        fs::create_dir_all(lean_tc.join("bin")).unwrap();
        let lean_bin_orig = lean_tc.join("bin/lean");
        fs::write(
            &lean_bin_orig,
            "#!/bin/sh\nif [ \"${1:-}\" = \"--print-prefix\" ]; then\n  CDPATH= cd -- \"$(dirname -- \"$0\")/..\" && pwd -P\n  exit 0\nfi\nexit 1\n",
        )
        .unwrap();
        fs::set_permissions(&lean_bin_orig, fs::Permissions::from_mode(0o755)).unwrap();
        fs::write(lean_tc.join("lib/libleanshared.so"), b"so").unwrap();
        fs::write(orig_lib_lean.join("Init.olean"), b"init-top").unwrap();
        fs::write(orig_lib_lean.join("Init/Core.olean"), b"init-core-olean").unwrap();
        fs::write(orig_lib_lean.join("Init/Core.ir"), b"init-core-ir").unwrap();
        fs::write(orig_lib_lean.join("Std.olean"), b"std-top").unwrap();
        fs::write(orig_lib_lean.join("Std/Data.olean"), b"std-data-olean").unwrap();
        fs::write(orig_lib_lean.join("Std/Data.ir.sig"), b"std-data-irsig").unwrap();
        fs::write(orig_lib_lean.join("Lean.olean"), b"lean-top").unwrap();
        fs::write(orig_lib_lean.join("Lean/Meta.olean"), b"lean-meta-olean").unwrap();
        fs::write(orig_lib_lean.join("Lake/Core.olean"), b"lake-ignored").unwrap();
        fs::write(orig_lib_lean.join("libLean.a"), b"static-ignored").unwrap();

        let expected_full_sha =
            compute_lean_sysroot_manifest_sha256(&orig_lib_lean).expect("full sysroot sha");
        let prepared_lean_libs = crate::rustc_runner::prepare_lean_runtime_library_path_in(
            &lean_bin_orig,
            &fake_store,
            &base,
            Some(&base),
        )
        .expect("stage init-only runtime Lean libs");
        assert_eq!(
            prepared_lean_libs.source_lib_lean_dir.as_deref(),
            Some(orig_lib_lean.as_path())
        );

        let lean_guards = [prepared_lean_libs._staging.as_ref()];
        let lean_bin = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
            &lean_guards,
            &prepared_lean_libs.lean_bin,
        );
        let valid_bin_dir = crate::rustc_runner::validated_store_aware_dir(
            &prepared_lean_libs.bin_dir,
            &fake_store,
            &base,
            "Lean bin dir",
        )
        .unwrap();
        let trusted_child_dirs: Vec<&Path> =
            crate::rustc_runner::TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
        let raw_child_path = crate::rustc_runner::build_child_path_with_bins(
            &[&valid_bin_dir],
            None,
            &fake_store,
            &trusted_child_dirs,
            None,
            &base,
        )
        .unwrap();
        let lean_child_path = crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
            &lean_guards,
            &raw_child_path,
        )
        .unwrap();
        let lean_tool_env = LeanPreparedEnv {
            ld_library_path: &prepared_lean_libs.ld_library_path,
            child_path: &lean_child_path,
            validated_tmpdir: Some(&base),
        };
        let lean_prefix =
            query_lean_prefix_with_env(&lean_bin, Some(lean_tool_env)).expect("query prefix");
        let (lean_stdlib, lean_stdlib_staging) = resolve_immutable_lean_stdlib_in(
            &lean_prefix,
            &prepared_lean_libs.lean_bin,
            &prepared_lean_libs,
            &fake_store,
            &base,
            None,
        )
        .expect("resolve runtime stdlib");
        assert!(lean_stdlib_staging.is_none());
        assert!(!lean_stdlib.join("Std").exists());
        assert!(!lean_stdlib.join("Lean").exists());
        assert!(!lean_stdlib.join("Lake").exists());

        let stdlib_guard =
            lean_stdlib_staging.as_deref().or(prepared_lean_libs._staging.as_deref());
        let stripped_only_sha =
            compute_lean_sysroot_manifest_sha256_inner(&lean_stdlib, stdlib_guard, None).unwrap();
        assert_ne!(stripped_only_sha, expected_full_sha);

        let active_sysroot_sha = compute_lean_sysroot_manifest_sha256_inner(
            &lean_stdlib,
            stdlib_guard,
            prepared_lean_libs.source_lib_lean_dir.as_deref(),
        )
        .expect("compute Init+Std+Lean sysroot sha from runtime staging + validated source");
        assert_eq!(active_sysroot_sha, expected_full_sha);

        let src_tree = base.join("src");
        let base_dir = src_tree.join("TestRoot");
        fs::create_dir_all(&base_dir).unwrap();
        let base_src = base_dir.join("Base.lean");
        fs::write(&base_src, "module\npublic def baseVal : Nat := 7\n").unwrap();
        let prebuilt = base.join("prebuilt");
        fs::create_dir_all(prebuilt.join("lib/TestRoot")).unwrap();
        fs::write(prebuilt.join("lib/TestRoot/Base.olean"), b"fake-olean").unwrap();
        write_test_prebuilt_manifest(
            &prebuilt,
            &lean_bin,
            &expected_full_sha,
            "TestRoot.Base",
            "lib/TestRoot/Base",
            &base_src,
        );
        let dag = [LeanDagSpec { module: "TestRoot.Base", rel_tree: "src", deps: &[] }];
        let overlay =
            inspect_prebuilt_overlay(Some(&prebuilt), &dag, &base, &lean_bin, &active_sysroot_sha)
                .unwrap();
        assert_eq!(overlay.fallback_label, "staged:1/1");

        // Tampering or symlinking omitted `Std`/`Lean` packages in the source
        // sysroot must either mismatch `manifest.json` or fail closed.
        fs::write(orig_lib_lean.join("Std/Data.olean"), b"tampered-std").unwrap();
        let tampered_sha = compute_lean_sysroot_manifest_sha256_inner(
            &lean_stdlib,
            stdlib_guard,
            prepared_lean_libs.source_lib_lean_dir.as_deref(),
        )
        .unwrap();
        assert_ne!(tampered_sha, expected_full_sha);
        let mismatch_overlay =
            inspect_prebuilt_overlay(Some(&prebuilt), &dag, &base, &lean_bin, &tampered_sha)
                .unwrap();
        assert_eq!(mismatch_overlay.fallback_label, "skipped:digest_mismatch");

        symlink(&base_src, orig_lib_lean.join("Lean/Evil.olean")).unwrap();
        let err_sym = compute_lean_sysroot_manifest_sha256_inner(
            &lean_stdlib,
            stdlib_guard,
            prepared_lean_libs.source_lib_lean_dir.as_deref(),
        )
        .unwrap_err();
        assert!(err_sym.contains("symlink"), "{err_sym}");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn lean_pinned_cache_dir_resists_parent_rename_during_staging() {
        let tmp = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(tmp.path()).unwrap();
        let tmp_parent = base.join("tmpdir");
        fs::create_dir_all(&tmp_parent).unwrap();
        let pinned = crate::rustc_runner::PinnedPrivateDir::create(
            "lean-pin-",
            Some(&tmp_parent),
            &base,
            "pinned lean cache",
        )
        .expect("create pinned lean cache");
        assert!(pinned.path().starts_with("/proc/self/fd/"));

        let disk_path = pinned.fs_root().to_path_buf();
        let out_rel = Path::new("lean-mirtotal-full-test");
        let real_out = pinned.pin_path(out_rel);
        fs::create_dir_all(real_out.join("TestRoot")).unwrap();
        fs::write(real_out.join("TestRoot/Base.olean"), b"legit-olean").unwrap();

        let moved_path = base.join("moved-lean");
        fs::rename(&disk_path, &moved_path).unwrap();
        fs::create_dir_all(disk_path.join("lean-mirtotal-full-test/TestRoot")).unwrap();
        fs::write(disk_path.join("lean-mirtotal-full-test/TestRoot/Base.olean"), b"trojan-olean")
            .unwrap();

        let dag = [LeanDagSpec { module: "TestRoot.Base", rel_tree: "src", deps: &[] }];
        write_dag_cache_stamp_in(&real_out, Some((&pinned, out_rel)), &dag, "none")
            .expect("stamp write/hash via PinnedPrivateDir fd must succeed");
        let (staged_dag, guard) =
            stage_and_verify_lean_dag_dir_in(&real_out, Some((&pinned, out_rel)), &dag, "none")
                .expect("staging via PinnedPrivateDir fd must ignore trojan TMPDIR replacement");
        let _guard = guard;
        assert_eq!(fs::read(staged_dag.join("TestRoot/Base.olean")).unwrap(), b"legit-olean");
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
        let valid_blocks_json: Vec<serde_json::Value> =
            valid_move_reinit.blocks.iter().map(|b| serde_json::to_value(b).unwrap()).collect();
        let valid_sha = compute_capture_body_sha256(
            &valid_move_reinit.identity,
            valid_move_reinit.arg_count,
            &valid_move_reinit.local_tys,
            &valid_blocks_json,
        );
        let valid_ev = MoveReinitEvidence {
            body_id: 0,
            fn_identity: valid_move_reinit.identity.clone(),
            local_slot: 3,
            arg_count: 2,
            local_tys: valid_move_reinit.local_tys.clone(),
            blocks: valid_blocks_json.clone(),
            total_steps: 5,
            init_step: MoveReinitStep { step: 0, block: 0, stmt: 0 },
            move_step: MoveReinitStep { step: 1, block: 0, stmt: 1 },
            reinit_step: MoveReinitStep { step: 2, block: 0, stmt: 2 },
            read_step: MoveReinitStep { step: 3, block: 0, stmt: 3 },
            lean_probe_line:
                "ANNEAL_LEAN_CASE:c_taken:BODY|0|probe::move_then_reinit|MR1|3|5|0,0,0|1,0,1|2,0,2|3,0,3:RETURNED:INT:i16:s:4"
                    .to_owned(),
            capture_body_sha256: valid_sha,
        };
        verify_move_reinit_evidence(&valid_ev, "c_taken", "move_then_reinit", 2).unwrap();

        let mut bad_sha_ev = valid_ev.clone();
        bad_sha_ev.capture_body_sha256 = "0".repeat(64);
        assert!(
            verify_move_reinit_evidence(&bad_sha_ev, "c_taken", "move_then_reinit", 2).is_err()
        );

        let mut bad_probe_ev = valid_ev.clone();
        bad_probe_ev.lean_probe_line =
            "ANNEAL_LEAN_CASE:c_taken:BODY|9|probe::move_then_reinit|MR1|3|5|0,0,0|1,0,1|2,0,2|3,0,3:RETURNED:INT:i16:s:4"
                .to_owned();
        assert!(
            verify_move_reinit_evidence(&bad_probe_ev, "c_taken", "move_then_reinit", 2).is_err()
        );

        let mut bad_copy_blocks = valid_blocks_json;
        bad_copy_blocks[0]["statements"][1]["value"]["operand"]["kind"] = serde_json::json!("copy");
        let mut copy_ev = valid_ev.clone();
        copy_ev.blocks = bad_copy_blocks;
        copy_ev.capture_body_sha256 = compute_capture_body_sha256(
            &copy_ev.fn_identity,
            copy_ev.arg_count,
            &copy_ev.local_tys,
            &copy_ev.blocks,
        );
        assert!(verify_move_reinit_evidence(&copy_ev, "c_taken", "move_then_reinit", 2).is_err());

        // `assign_place` read steps must be accepted cleanly while non-assign
        // `move_step` statements with a `value` field must be rejected.
        let mut ap_read_ev = valid_ev.clone();
        ap_read_ev.blocks[0]["statements"][3] = serde_json::json!({
            "kind": "assign_place",
            "place": { "local": 0, "projection": [] },
            "value": valid_ev.blocks[0]["statements"][3]["value"].clone(),
        });
        ap_read_ev.capture_body_sha256 = compute_capture_body_sha256(
            &ap_read_ev.fn_identity,
            ap_read_ev.arg_count,
            &ap_read_ev.local_tys,
            &ap_read_ev.blocks,
        );
        verify_move_reinit_evidence(&ap_read_ev, "c_taken", "move_then_reinit", 2)
            .expect("assign_place read_step must satisfy move/reinit verification");

        let mut bad_kind_move_ev = valid_ev;
        bad_kind_move_ev.blocks[0]["statements"][1] = serde_json::json!({
            "kind": "storage_live",
            "local": 4,
            "value": bad_kind_move_ev.blocks[0]["statements"][1]["value"].clone(),
        });
        bad_kind_move_ev.capture_body_sha256 = compute_capture_body_sha256(
            &bad_kind_move_ev.fn_identity,
            bad_kind_move_ev.arg_count,
            &bad_kind_move_ev.local_tys,
            &bad_kind_move_ev.blocks,
        );
        assert!(
            verify_move_reinit_evidence(&bad_kind_move_ev, "c_taken", "move_then_reinit", 2)
                .is_err()
        );

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
            local_tys: vec![i16_ty.clone(), zst_enum.clone(), zst_enum.clone(), zst_enum],
            blocks: valid_move_reinit.blocks,
        };
        assert!(!body_exercises_move_then_reinit(&zst_only));

        // Multi-block bodies must be rejected by the static single-block helper
        // so dead-branch `MoveReinit` blocks cannot satisfy non-vacuity gates.
        let mut split_blocks = zst_only.blocks;
        let tail_stmt = split_blocks[0].statements.pop().unwrap();
        split_blocks.push(CaptureBlock {
            statements: vec![tail_stmt],
            terminator: serde_json::json!({ "kind": "ret" }),
        });
        let multi_block = CaptureBody {
            identity: "probe::multi_block_dead_arm".to_owned(),
            arg_count: 2,
            local_tys: vec![
                i16_ty,
                serde_json::json!({
                    "kind": "enum",
                    "id": 1,
                    "discr_width": "i16",
                    "discr_signed": true,
                    "tag_repr": { "kind": "scalar", "width": "i16", "signed": true },
                    "discriminants": ["65534", "0", "7"]
                }),
                serde_json::json!({
                    "kind": "enum",
                    "id": 1,
                    "discr_width": "i16",
                    "discr_signed": true,
                    "tag_repr": { "kind": "scalar", "width": "i16", "signed": true },
                    "discriminants": ["65534", "0", "7"]
                }),
                serde_json::json!({
                    "kind": "enum",
                    "id": 1,
                    "discr_width": "i16",
                    "discr_signed": true,
                    "tag_repr": { "kind": "scalar", "width": "i16", "signed": true },
                    "discriminants": ["65534", "0", "7"]
                }),
                serde_json::json!({
                    "kind": "enum",
                    "id": 1,
                    "discr_width": "i16",
                    "discr_signed": true,
                    "tag_repr": { "kind": "scalar", "width": "i16", "signed": true },
                    "discriminants": ["65534", "0", "7"]
                }),
            ],
            blocks: split_blocks,
        };
        assert!(!body_exercises_move_then_reinit(&multi_block));

        let parsed = parse_fuzz_lean_probe_output_ids(
            "\"ANNEAL_LEAN_CASE:c_taken:BODY|0|rust-path-v1::fuzz_case_0000|MR1|3|5|0,0,0|1,0,1|2,0,2|3,0,3:RETURNED:INT:i16:s:4\"\n\
             \"ANNEAL_LEAN_CASE:c_dead:BODY|1|rust-path-v1::fuzz_case_0001|MR0:RETURNED:INT:i16:s:0\"\n\
             \"ANNEAL_LEAN_CASE:c_ub:BODY|2|rust-path-v1::fuzz_case_0002|MR0:FAULT:undefined\"\n",
            &["c_taken", "c_dead", "c_ub"],
        )
        .unwrap();
        assert_eq!(parsed["c_taken"].body_id, Some(0));
        assert_eq!(parsed["c_taken"].fn_identity.as_deref(), Some("rust-path-v1::fuzz_case_0000"));
        assert!(parsed["c_taken"].move_reinit.is_some());
        assert!(parsed["c_taken"].lean_probe_line.is_some());
        assert!(parsed["c_dead"].move_reinit.is_none());
        assert!(parsed["c_dead"].lean_probe_line.is_some());
        assert!(parsed["c_ub"].move_reinit.is_none());
        assert!(parsed["c_ub"].lean_probe_line.is_some());

        let expected_cb = FuzzCaptureBody {
            body_id: 1,
            fn_identity: "rust-path-v1::fuzz_case_0001".to_owned(),
            arg_count: 0,
            local_tys: vec![],
            blocks: vec![],
            capture_body_sha256: "0".repeat(64),
        };
        let (ok_out, ok_line, _) = bind_fuzz_probe_result_to_capture_body(
            "c_dead",
            parsed["c_dead"].clone(),
            Some(&expected_cb),
        );
        assert!(matches!(ok_out, ObservedOutcome::Returned { .. }));
        assert!(ok_line.is_some());

        let mut wrong_id_cb = expected_cb.clone();
        wrong_id_cb.body_id = 9;
        let (bad_id_out, bad_id_line, bad_id_mr) = bind_fuzz_probe_result_to_capture_body(
            "c_dead",
            parsed["c_dead"].clone(),
            Some(&wrong_id_cb),
        );
        assert!(matches!(bad_id_out, ObservedOutcome::ToolError { .. }));
        assert!(bad_id_line.is_none());
        assert!(bad_id_mr.is_none());

        let mut wrong_ident_cb = expected_cb;
        wrong_ident_cb.fn_identity = "rust-path-v1::other_fn".to_owned();
        let (bad_ident_out, bad_ident_line, _) = bind_fuzz_probe_result_to_capture_body(
            "c_dead",
            parsed["c_dead"].clone(),
            Some(&wrong_ident_cb),
        );
        assert!(matches!(bad_ident_out, ObservedOutcome::ToolError { .. }));
        assert!(bad_ident_line.is_none());

        assert!(
            parse_fuzz_lean_probe_output_ids(
                "\"ANNEAL_LEAN_CASE:c_missing_body:MR0:RETURNED:INT:i16:s:4\"\n",
                &["c_missing_body"],
            )
            .is_err()
        );
        assert!(
            parse_fuzz_lean_probe_output_ids(
                "\"ANNEAL_LEAN_CASE:c_bare_mr1:BODY|0|crate::f|MR1:RETURNED:INT:i16:s:4\"\n",
                &["c_bare_mr1"],
            )
            .is_err()
        );
        assert!(
            parse_fuzz_lean_probe_output_ids(
                "\"ANNEAL_LEAN_CASE:c_bad_order:BODY|0|crate::f|MR1|3|5|2,0,0|1,0,1|3,0,2|4,0,3:RETURNED:INT:i16:s:4\"\n",
                &["c_bad_order"],
            )
            .is_err()
        );
        assert!(
            parse_fuzz_lean_probe_output_ids(
                "\"ANNEAL_LEAN_CASE:c_legacy:RETURNED:INT:i16:s:4\"\n",
                &["c_legacy"],
            )
            .is_err()
        );
    }

    #[test]
    fn clamp_timeout_to_deadline_enforces_wall_clock_cutoff_on_stalled_subprocess() {
        let base = Duration::from_secs(120);
        assert_eq!(clamp_timeout_to_deadline(base, None).unwrap(), base);

        let expired = Instant::now() - Duration::from_millis(5);
        assert!(
            clamp_timeout_to_deadline(base, Some(expired)).is_err(),
            "expired shrink deadline must fail closed before spawning a child"
        );

        let tight_deadline = Instant::now() + Duration::from_millis(200);
        let clamped = clamp_timeout_to_deadline(base, Some(tight_deadline)).unwrap();
        assert!(clamped <= Duration::from_millis(200));
        assert!(!clamped.is_zero());

        let work = tempfile::tempdir().unwrap();
        let inv = Invocation::new("/bin/sh", &["-c", "sleep 30"]);
        let started = Instant::now();
        let out = crate::rustc_runner::run_supervised_in_tmp(
            &inv,
            work.path(),
            clamped,
            None,
            "deadline clamp probe",
        )
        .unwrap();
        assert!(
            matches!(out.termination, Termination::TimedOut(_)),
            "expected stalled child to time out at clamped deadline, got {:?}",
            out.termination
        );
        assert!(
            started.elapsed() < Duration::from_secs(3),
            "clamped subprocess ran too long: {:?}",
            started.elapsed()
        );
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

    #[cfg(unix)]
    #[test]
    fn eval_fuzz_probe_bisects_case_local_nonzero_exit_and_propagates_global_failures() {
        use std::os::unix::{fs::PermissionsExt as _, process::ExitStatusExt as _};

        let tmp = tempfile::tempdir().unwrap();
        let progs = crate::r#gen::generate_campaign(
            &crate::r#gen::GenConfig {
                master_seed: 20261124,
                max_stmts: 4,
                ub_ratio: 0.2,
                default_fuel: 1500,
            },
            4,
        );
        let refs: Vec<&crate::r#gen::GenProgram> = progs.iter().collect();
        let mut body_ids_by_fn = BTreeMap::new();
        for (idx, p) in progs.iter().enumerate() {
            body_ids_by_fn.insert(p.fn_name.clone(), idx);
        }
        let sample_src = generate_fuzz_lean_probe(&body_ids_by_fn, &refs).unwrap();
        let preamble_lines =
            sample_src.lines().take_while(|line| !line.starts_with("#eval runCase ")).count();
        let fake_probe_path = Path::new("/tmp/FuzzProbe_0.lean");

        assert!(is_global_lean_probe_failure(
            &Termination::TimedOut(std::process::ExitStatus::from_raw(9)),
            &sample_src,
            fake_probe_path,
            "",
            "",
        ));
        assert!(is_global_lean_probe_failure(
            &Termination::LaunchFailed("enoent".to_owned()),
            &sample_src,
            fake_probe_path,
            "",
            "",
        ));
        assert!(is_global_lean_probe_failure(
            &Termination::Exited(std::process::ExitStatus::from_raw(1 << 8)),
            &sample_src,
            fake_probe_path,
            "",
            &format!(
                "FuzzProbe_0.lean:2:0: error: unknown module prefix 'Captured'\n\
                 FuzzProbe_0.lean:{}:0: error: unknown identifier 'Captured.program'",
                preamble_lines + 1
            ),
        ));
        assert!(!is_global_lean_probe_failure(
            &Termination::Exited(std::process::ExitStatus::from_raw(1 << 8)),
            &sample_src,
            fake_probe_path,
            "",
            &format!(
                "FuzzProbe_0.lean:{}:0: error: simulated elaboration failure",
                preamble_lines + 2
            ),
        ));

        let bad_id = &progs[2].case_id;
        let case_fail_lean = tmp.path().join("case_fail_lean.sh");
        let case_script = format!(
            "#!/bin/sh\n\
             probe=\"\"\n\
             for a in \"$@\"; do probe=\"$a\"; done\n\
             if grep -Fq '{bad_id}' \"$probe\"; then\n\
               echo \"$(basename \"$probe\"):$(( $(grep -n '^#eval runCase ' \"$probe\" | head -n1 | cut -d: -f1) )):0: error: simulated case-local failure in {bad_id}\" >&2\n\
               exit 1\n\
             fi\n\
             grep '^#eval runCase ' \"$probe\" | sed -E 's/^#eval runCase \"([^\"]+)\".*/\"ANNEAL_LEAN_CASE:\\1:BODY|0|rust-path-v1::fuzz_case|MR0:RETURNED:INT:i32:u:7\"/'\n\
             exit 0\n"
        );
        fs::write(&case_fail_lean, case_script).unwrap();
        fs::set_permissions(&case_fail_lean, fs::Permissions::from_mode(0o755)).unwrap();

        let make_session = |lean_bin: PathBuf| LeanSession {
            anneal_root: tmp.path().to_path_buf(),
            capture_bin: tmp.path().join("cap"),
            rust_sysroot: tmp.path().to_path_buf(),
            lean_bin,
            olean_paths: vec![tmp.path().to_path_buf()],
            prebuilt_overlay: "none".to_owned(),
            ld_library_path: String::new(),
            child_path: validated_system_child_path().unwrap(),
            lean_ld_library_path: String::new(),
            lean_child_path: validated_system_child_path().unwrap(),
            validated_tmpdir: None,
            _rust_sysroot_staging: None,
            _capture_staging: None,
            _lean_lib_staging: None,
            _lean_stdlib_staging: None,
            _lean_dag_staging: None,
        };

        let case_dir = tmp.path().join("case_bisect");
        fs::create_dir_all(&case_dir).unwrap();
        let bisected = make_session(case_fail_lean)
            .eval_fuzz_probe_with_bisection(
                &case_dir,
                tmp.path().to_str().unwrap(),
                &body_ids_by_fn,
                &refs,
                0,
                None,
            )
            .expect("case-local probe failure must bisect cleanly");
        assert_eq!(bisected.len(), 4);
        for (idx, p) in progs.iter().enumerate() {
            let entry = &bisected[&p.case_id];
            if idx == 2 {
                assert!(
                    matches!(&entry.outcome, ObservedOutcome::ToolError { detail } if detail.contains("simulated case-local failure")),
                    "expected ToolError for {}, got {:?}",
                    p.case_id,
                    entry.outcome
                );
            } else {
                assert_eq!(
                    entry.outcome,
                    ObservedOutcome::Returned {
                        value: MirValue::Int { int_kind: IntKind::U32, bits: 7 }
                    }
                );
            }
        }

        // Batch-wide preamble failure must NOT bisect across all programs.
        let global_fail_lean = tmp.path().join("global_fail_lean.sh");
        let count_file = tmp.path().join("global_count.txt");
        let global_script = format!(
            "#!/bin/sh\n\
             echo x >> '{}'\n\
             probe=\"\"\n\
             for a in \"$@\"; do probe=\"$a\"; done\n\
             echo \"$(basename \"$probe\"):2:0: error: unknown module prefix 'Captured'\" >&2\n\
             exit 1\n",
            count_file.display()
        );
        fs::write(&global_fail_lean, global_script).unwrap();
        fs::set_permissions(&global_fail_lean, fs::Permissions::from_mode(0o755)).unwrap();

        let global_dir = tmp.path().join("global_fail");
        fs::create_dir_all(&global_dir).unwrap();
        let global_res = make_session(global_fail_lean)
            .eval_fuzz_probe_with_bisection(
                &global_dir,
                tmp.path().to_str().unwrap(),
                &body_ids_by_fn,
                &refs,
                0,
                None,
            )
            .expect("global failure must emit structured ToolError batch");
        assert_eq!(global_res.len(), 4);
        assert_eq!(fs::read_to_string(&count_file).unwrap().lines().count(), 1);
        for p in &progs {
            assert!(matches!(global_res[&p.case_id].outcome, ObservedOutcome::ToolError { .. }));
        }
    }

    #[test]
    fn compile_captured_lean_modules_handles_sharded_modules_and_rejects_invalid_manifests() {
        let lean_bin = fs::canonicalize(default_lean_path().expect("resolve pinned lean"))
            .expect("canonicalize lean");
        let tmp = tempfile::tempdir().unwrap();
        let make_session = || LeanSession {
            anneal_root: tmp.path().to_path_buf(),
            capture_bin: tmp.path().join("cap"),
            rust_sysroot: tmp.path().to_path_buf(),
            lean_bin: lean_bin.clone(),
            olean_paths: Vec::new(),
            prebuilt_overlay: "none".to_owned(),
            ld_library_path: String::new(),
            child_path: validated_system_child_path().unwrap(),
            lean_ld_library_path: String::new(),
            lean_child_path: validated_system_child_path().unwrap(),
            validated_tmpdir: None,
            _rust_sysroot_staging: None,
            _capture_staging: None,
            _lean_lib_staging: None,
            _lean_stdlib_staging: None,
            _lean_dag_staging: None,
        };
        let session = make_session();

        // Real Lean 4 `module` sharded tree (`Shard_000` + `Shard_001` ->
        // `Captured.lean`) listed out of order in `capture_shards.json`.
        let out_dir = tmp.path().join("sharded_out");
        let sharded_group = tmp.path().join("sharded_group");
        fs::create_dir_all(out_dir.join("Captured")).unwrap();
        fs::create_dir_all(&sharded_group).unwrap();
        fs::write(
            out_dir.join("Captured/Shard_000.lean"),
            "module\n@[expose] public section\nnamespace Captured.Shard_000\ndef a : Nat := 19\nend Captured.Shard_000\nend\n",
        )
        .unwrap();
        fs::write(
            out_dir.join("Captured/Shard_001.lean"),
            "module\npublic import Captured.Shard_000\n@[expose] public section\nnamespace Captured.Shard_001\ndef b : Nat := Captured.Shard_000.a + 23\nend Captured.Shard_001\nend\n",
        )
        .unwrap();
        let root_lean = out_dir.join("Captured.lean");
        fs::write(
            &root_lean,
            "module\npublic import Captured.Shard_000\npublic import Captured.Shard_001\n@[expose] public section\nnamespace Captured\ndef answer : Nat := Captured.Shard_001.b\nend Captured\nend\n",
        )
        .unwrap();
        let shards_json = out_dir.join("capture_shards.json");
        fs::write(
            &shards_json,
            r#"{"shards":[{"shard_idx":1,"capture_module":"Captured.Shard_001"},{"shard_idx":0,"capture_module":"Captured.Shard_000"}]}"#,
        )
        .unwrap();

        let status = CaptureStatusOk {
            status: "captured".to_owned(),
            capture: out_dir.join("capture.json"),
            lean: root_lean.clone(),
            capture_shards: Some(shards_json.clone()),
        };
        let (olean_dir, lean_path) = session
            .compile_captured_lean_modules(&sharded_group, &out_dir, &status, None, "shard_unit")
            .expect("sharded modules must compile in shard_idx order");
        assert!(olean_dir.join("Captured/Shard_000.olean").is_file());
        assert!(olean_dir.join("Captured/Shard_001.olean").is_file());
        assert!(olean_dir.join("Captured.olean").is_file());

        let probe = tmp.path().join("ShardProbe.lean");
        fs::write(&probe, "import Captured\n#eval IO.println s!\"ANS:{Captured.answer}\"\n")
            .unwrap();
        let probe_res = run_supervised_cmd_in_tmp(
            &session.apply_lean_env(
                Invocation::new(&lean_bin, LEAN_COMPILE_FLAGS)
                    .arg(&probe)
                    .env("LEAN_PATH", &lean_path),
            ),
            tmp.path(),
            LEAN_EVAL_TIMEOUT_SECS,
            None,
            "eval sharded Captured probe",
        )
        .unwrap();
        assert!(
            matches!(probe_res.termination, Termination::Exited(s) if s.success()),
            "sharded probe failed: {}",
            probe_res.describe()
        );
        assert!(String::from_utf8_lossy(&probe_res.stdout).contains("ANS:42"));

        // Fallback discovery without explicit `status.capture_shards` path.
        let fallback_group = tmp.path().join("fallback_group");
        fs::create_dir_all(&fallback_group).unwrap();
        let status_no_field = CaptureStatusOk {
            status: "captured".to_owned(),
            capture: out_dir.join("capture.json"),
            lean: root_lean,
            capture_shards: None,
        };
        let (fallback_olean, _) = session
            .compile_captured_lean_modules(
                &fallback_group,
                &out_dir,
                &status_no_field,
                None,
                "shard_fallback",
            )
            .expect("fallback discovery of capture_shards.json must succeed");
        assert!(fallback_olean.join("Captured.olean").is_file());

        // Reject unsafe module prefixes, missing manifests with `Captured/`,
        // duplicate shard indices, and missing shard source files.
        assert!(shard_module_rel_path("Other.Shard_000").is_err());
        assert!(shard_module_rel_path("Captured.../../Evil").is_err());
        assert!(shard_module_rel_path("Captured.Shard/000").is_err());

        let orphan_dir = tmp.path().join("orphan");
        fs::create_dir_all(orphan_dir.join("Captured")).unwrap();
        let orphan_err = load_capture_shards(&orphan_dir, tmp.path(), None).err().unwrap();
        assert!(orphan_err.contains("capture_shards.json"), "{orphan_err}");

        let dup_manifest = out_dir.join("dup_shards.json");
        fs::write(
            &dup_manifest,
            r#"{"shards":[{"shard_idx":0,"capture_module":"Captured.Shard_000"},{"shard_idx":0,"capture_module":"Captured.Shard_001"}]}"#,
        )
        .unwrap();
        let dup_err = load_capture_shards(&out_dir, tmp.path(), Some(&dup_manifest)).err().unwrap();
        assert!(dup_err.contains("duplicate shard_idx"), "{dup_err}");

        let fallback_empty_dir = tmp.path().join("fallback_empty_shards");
        fs::create_dir_all(&fallback_empty_dir).unwrap();
        fs::write(fallback_empty_dir.join("capture_shards.json"), r#"{"shards":[]}"#).unwrap();
        let empty_err = load_capture_shards(&fallback_empty_dir, tmp.path(), None).err().unwrap();
        assert!(empty_err.contains("zero shards"), "{empty_err}");

        let probe_src =
            generate_fuzz_lean_probe(&BTreeMap::new(), &[]).expect("empty batch probe renders");
        assert!(probe_src.contains("activeFrameBodyComp prog f0"), "{probe_src}");
        assert!(probe_src.contains("\"arithmetic overflow\""), "{probe_src}");
        assert!(!probe_src.contains("\"overflow in signed arithmetic\""), "{probe_src}");
        assert!(probe_src.contains("some (.sysrootCall _ ops _ _ _)"), "{probe_src}");
        assert!(probe_src.contains("some (.coreCall _ ops _ _ _)"), "{probe_src}");

        let missing_src_out = tmp.path().join("missing_src_out");
        fs::create_dir_all(&missing_src_out).unwrap();
        fs::write(missing_src_out.join("Captured.lean"), "def ok : Nat := 0\n").unwrap();
        let missing_src_manifest = missing_src_out.join("capture_shards.json");
        fs::write(
            &missing_src_manifest,
            r#"{"shards":[{"shard_idx":9,"capture_module":"Captured.Shard_009"}]}"#,
        )
        .unwrap();
        let status_missing = CaptureStatusOk {
            status: "captured".to_owned(),
            capture: missing_src_out.join("capture.json"),
            lean: missing_src_out.join("Captured.lean"),
            capture_shards: Some(missing_src_manifest),
        };
        let missing_group = tmp.path().join("missing_group");
        fs::create_dir_all(&missing_group).unwrap();
        let missing_err = session
            .compile_captured_lean_modules(
                &missing_group,
                &missing_src_out,
                &status_missing,
                None,
                "missing_src",
            )
            .unwrap_err();
        assert!(
            missing_err.contains("captured shard Captured.Shard_009"),
            "unexpected missing shard error: {missing_err}"
        );

        #[cfg(unix)]
        {
            // Out-of-tree, symlinked, and hardlinked capture artifacts must
            // fail closed before Lean/JSON reads.
            let outside_file = tmp.path().join("outside_manifest.json");
            fs::write(&outside_file, r#"{"shards":[]}"#).unwrap();
            let esc_err = validate_capture_output_file(
                &out_dir,
                tmp.path(),
                &outside_file,
                "capture manifest",
            )
            .unwrap_err();
            assert!(esc_err.contains("escapes capture_out directory"), "{esc_err}");

            let esc_shard_manifest_err =
                load_capture_shards(&out_dir, tmp.path(), Some(&outside_file)).unwrap_err();
            assert!(
                esc_shard_manifest_err.contains("escapes capture_out directory"),
                "{esc_shard_manifest_err}"
            );

            let sym_dir = tmp.path().join("sym_artifact_out");
            fs::create_dir_all(&sym_dir).unwrap();
            let evil_lean = tmp.path().join("evil_target.lean");
            fs::write(&evil_lean, "def evil : Nat := 1\n").unwrap();
            std::os::unix::fs::symlink(&evil_lean, sym_dir.join("Captured.lean")).unwrap();
            let sym_status = CaptureStatusOk {
                status: "captured".to_owned(),
                capture: sym_dir.join("capture.json"),
                lean: sym_dir.join("Captured.lean"),
                capture_shards: None,
            };
            let sym_err = session
                .compile_captured_lean_modules(&missing_group, &sym_dir, &sym_status, None, "sym")
                .unwrap_err();
            assert!(sym_err.contains("symlink"), "{sym_err}");

            let hard_dir = tmp.path().join("hard_artifact_out");
            fs::create_dir_all(&hard_dir).unwrap();
            fs::hard_link(&evil_lean, hard_dir.join("Captured.lean")).unwrap();
            let hard_status = CaptureStatusOk {
                status: "captured".to_owned(),
                capture: hard_dir.join("capture.json"),
                lean: hard_dir.join("Captured.lean"),
                capture_shards: None,
            };
            let hard_err = session
                .compile_captured_lean_modules(
                    &missing_group,
                    &hard_dir,
                    &hard_status,
                    None,
                    "hard",
                )
                .unwrap_err();
            assert!(hard_err.contains("hardlink"), "{hard_err}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn capture_fuzz_batch_bisects_compiler_failed_and_validates_reported_artifact_paths() {
        use std::os::unix::fs::PermissionsExt as _;

        let tmp = tempfile::tempdir().unwrap();
        let progs = crate::r#gen::generate_campaign(
            &crate::r#gen::GenConfig {
                master_seed: 20261124,
                max_stmts: 4,
                ub_ratio: 0.2,
                default_fuel: 1500,
            },
            4,
        );
        let refs: Vec<&crate::r#gen::GenProgram> = progs.iter().collect();
        let bad_fn = &progs[1].fn_name;

        let fake_cap = tmp.path().join("fake_capture_bisect.sh");
        let cap_script = format!(
            r#"#!/bin/sh
src=""
outdir=""
selected=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --crate-root) src="$2"; shift 2 ;;
    --out-dir) outdir="$2"; shift 2 ;;
    --select) selected="$selected $2"; shift 2 ;;
    *) shift ;;
  esac
done
if grep -Fq "{bad_fn}" "$src"; then
  echo '{{"status":"compiler_failed","diagnostics":["simulated case syntax error"],"unsupported":[]}}'
  exit 1
fi
mkdir -p "$outdir"
python3 - "$outdir" $selected <<'PY'
import json, sys
from pathlib import Path
out_dir = Path(sys.argv[1])
bodies = []
for fn in sys.argv[2:]:
    bodies.append({{
        "identity": f"rust-path-v1::{{fn}}",
        "arg_count": 0,
        "local_tys": ["u32"],
        "blocks": [{{"statements": [], "terminator": {{"kind": "return"}}}}],
    }})
cap_path = out_dir / "capture.json"
lean_path = out_dir / "Captured.lean"
cap_path.write_text(json.dumps({{"program": {{"bodies": bodies}}}}), encoding="utf-8")
lean_path.write_text("-- stub\n", encoding="utf-8")
print(json.dumps({{"status": "captured", "capture": str(cap_path), "lean": str(lean_path)}}))
PY
"#
        );
        fs::write(&fake_cap, cap_script).unwrap();
        fs::set_permissions(&fake_cap, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_lean = tmp.path().join("fake_lean_ok.sh");
        let lean_script = r#"#!/bin/sh
probe=""
for a in "$@"; do probe="$a"; done
case "$probe" in
  *FuzzProbe_*.lean)
    python3 - "$probe" <<'PY'
import json, re, sys
from pathlib import Path
probe = Path(sys.argv[1])
text = probe.read_text(encoding="utf-8")
cap = json.loads((probe.parent / "capture_out" / "capture.json").read_text(encoding="utf-8"))
bodies = cap["program"]["bodies"]
for cid, did in re.findall(r'#eval runCase "([^"]+)" (\d+)\b', text):
    ident = bodies[int(did)]["identity"]
    print(f'"ANNEAL_LEAN_CASE:{cid}:BODY|{did}|{ident}|MR0:RETURNED:INT:i32:u:7"')
PY
    ;;
esac
exit 0
"#;
        fs::write(&fake_lean, lean_script).unwrap();
        fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

        let session = LeanSession {
            anneal_root: tmp.path().to_path_buf(),
            capture_bin: fake_cap,
            rust_sysroot: tmp.path().to_path_buf(),
            lean_bin: fake_lean.clone(),
            olean_paths: vec![tmp.path().to_path_buf()],
            prebuilt_overlay: "none".to_owned(),
            ld_library_path: String::new(),
            child_path: validated_system_child_path().unwrap(),
            lean_ld_library_path: String::new(),
            lean_child_path: validated_system_child_path().unwrap(),
            validated_tmpdir: None,
            _rust_sysroot_staging: None,
            _capture_staging: None,
            _lean_lib_staging: None,
            _lean_stdlib_staging: None,
            _lean_dag_staging: None,
        };

        let bisect_dir = tmp.path().join("compiler_bisect");
        let bisect_res = session
            .capture_and_evaluate_fuzz_batch(&bisect_dir, "cmp_bisect", &refs)
            .expect("case-local compiler_failed must bisect cleanly");
        assert_eq!(bisect_res.len(), 4);
        for (idx, p) in progs.iter().enumerate() {
            let entry = &bisect_res[&p.case_id];
            if idx == 1 {
                assert!(
                    matches!(&entry.outcome, ObservedOutcome::ToolError { detail } if detail.contains("compiler_failed")),
                    "expected ToolError for {}, got {:?}",
                    p.case_id,
                    entry.outcome
                );
            } else {
                assert_eq!(
                    entry.outcome,
                    ObservedOutcome::Returned {
                        value: MirValue::Int { int_kind: IntKind::U32, bits: 7 }
                    }
                );
            }
        }

        // Genuine batch-wide `tool_failed` on a multi-program batch still
        // avoids bisection (1 invocation for the non-ScopeControl batch).
        let clean_refs: Vec<&crate::r#gen::GenProgram> = progs
            .iter()
            .filter(|p| p.category != crate::r#gen::GenCategory::ScopeControl)
            .collect();
        assert!(clean_refs.len() >= 2);
        let tool_fail_count = tmp.path().join("tool_fail_count.txt");
        let fake_tool_fail = tmp.path().join("fake_capture_tool_fail.sh");
        fs::write(
            &fake_tool_fail,
            format!(
                "#!/bin/sh\necho x >> '{}'\necho '{{\"status\":\"tool_failed\",\"diagnostics\":[\"broken sysroot\"],\"unsupported\":[]}}'\nexit 1\n",
                tool_fail_count.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_tool_fail, fs::Permissions::from_mode(0o755)).unwrap();
        let tool_fail_session = LeanSession { capture_bin: fake_tool_fail, ..session.clone() };
        let tf_dir = tmp.path().join("tool_fail_group");
        let tf_res = tool_fail_session
            .capture_and_evaluate_fuzz_batch(&tf_dir, "tool_fail", &clean_refs)
            .expect("tool_failed batch emits structured ToolError");
        assert_eq!(fs::read_to_string(&tool_fail_count).unwrap().lines().count(), 1);
        for p in &clean_refs {
            assert!(matches!(tf_res[&p.case_id].outcome, ObservedOutcome::ToolError { .. }));
        }

        // Capture JSON naming an out-of-tree artifact path fails closed.
        let evil_cap_target = tmp.path().join("escaped_capture.json");
        fs::write(&evil_cap_target, r#"{"program":{"bodies":[]}}"#).unwrap();
        let fake_evil_cap = tmp.path().join("fake_capture_escape.sh");
        fs::write(
            &fake_evil_cap,
            format!(
                r#"#!/bin/sh
outdir=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out-dir) outdir="$2"; shift 2 ;;
    *) shift ;;
  esac
done
mkdir -p "$outdir"
echo "-- stub" > "$outdir/Captured.lean"
printf '{{"status":"captured","capture":"{}","lean":"%s/Captured.lean"}}\n' "$outdir"
"#,
                evil_cap_target.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_evil_cap, fs::Permissions::from_mode(0o755)).unwrap();
        let evil_session = LeanSession { capture_bin: fake_evil_cap, ..session };
        let esc_group = tmp.path().join("escape_group");
        let esc_err = evil_session
            .capture_and_evaluate_fuzz_batch(&esc_group, "esc", &refs[..1])
            .unwrap_err();
        assert!(esc_err.contains("escapes capture_out directory"), "{esc_err}");

        // Capture JSON reporting a `sub/../capture.json` parent-traversal path
        // inside `capture_out` also fails closed.
        let fake_trav_cap = tmp.path().join("fake_capture_trav.sh");
        fs::write(
            &fake_trav_cap,
            r#"#!/bin/sh
outdir=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out-dir) outdir="$2"; shift 2 ;;
    *) shift ;;
  esac
done
mkdir -p "$outdir/sub"
echo '{"program":{"bodies":[]}}' > "$outdir/capture.json"
echo "-- stub" > "$outdir/Captured.lean"
printf '{"status":"captured","capture":"%s/sub/../capture.json","lean":"%s/Captured.lean"}\n' "$outdir" "$outdir"
"#,
        )
        .unwrap();
        fs::set_permissions(&fake_trav_cap, fs::Permissions::from_mode(0o755)).unwrap();
        let trav_session = LeanSession { capture_bin: fake_trav_cap, ..evil_session };
        let trav_group = tmp.path().join("trav_group");
        let trav_err = trav_session
            .capture_and_evaluate_fuzz_batch(&trav_group, "trav", &refs[..1])
            .unwrap_err();
        assert!(trav_err.contains(".."), "{trav_err}");
    }

    #[cfg(unix)]
    #[test]
    fn apply_lean_tool_env_strips_ambient_paths_and_rejects_poisoned_lean_dirs() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(tmp.path()).unwrap();
        let prefix = base.join("lean-toolchain");
        let evil_dir = base.join("evil-dir");
        for d in [prefix.join("bin"), prefix.join("lib/lean"), evil_dir.clone()] {
            fs::create_dir_all(d).unwrap();
        }
        let lean_bin = prefix.join("bin/lean");
        fs::write(&lean_bin, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&lean_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_store = base.join("nix-store");
        fs::create_dir_all(&fake_store).unwrap();
        let trusted_child_dirs: Vec<&Path> =
            crate::rustc_runner::TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
        let poisoned_path = env::join_paths([&evil_dir, &PathBuf::from("./rel-evil")]).unwrap();

        fs::write(prefix.join("lib/lean/Init.olean"), b"init").unwrap();
        let built = apply_lean_tool_env_with_tmpdir(
            Invocation::new(&lean_bin, &[]),
            &lean_bin,
            &fake_store,
            &trusted_child_dirs,
            Some(poisoned_path.as_os_str()),
            &base,
            None,
        )
        .expect("clean Lean toolchain should build sanitized Invocation");
        assert!(built._staging.is_some());
        let built_ld = built
            .inv
            .environment
            .get(OsStr::new("LD_LIBRARY_PATH"))
            .expect("validated Lean LD_LIBRARY_PATH");
        let built_ld_dirs: Vec<PathBuf> = env::split_paths(built_ld).collect();
        assert_eq!(built_ld_dirs.len(), 2);
        assert_ne!(built_ld_dirs[0], prefix.join("lib/lean"));
        assert_ne!(built_ld_dirs[1], prefix.join("lib"));
        let staged_init = built_ld_dirs[0].join("Init.olean");
        assert_eq!(fs::read(&staged_init).unwrap(), b"init");
        fs::write(prefix.join("lib/lean/Init.olean"), b"tampered-init").unwrap();
        assert_eq!(fs::read(&staged_init).unwrap(), b"init");
        let built_path_dirs: Vec<PathBuf> =
            env::split_paths(built.inv.environment.get(OsStr::new("PATH")).unwrap()).collect();
        assert!(!built_path_dirs.contains(&evil_dir));
        assert!(!built_path_dirs.contains(&PathBuf::from("./rel-evil")));
        assert!(!built_path_dirs.contains(&prefix.join("bin")));
        assert_ne!(built.inv.executable, lean_bin);
        let staged_lean_meta = fs::symlink_metadata(&built.inv.executable).unwrap();
        assert!(!staged_lean_meta.file_type().is_symlink());
        assert_eq!(crate::rustc_runner::hardlink_count(&staged_lean_meta), 1);
        assert!(staged_lean_meta.permissions().readonly());
        let staged_bin_dir = built.inv.executable.parent().unwrap().to_path_buf();
        assert!(built_path_dirs.contains(&staged_bin_dir));
        fs::write(&lean_bin, b"#!/bin/sh\nexit 99\n").unwrap();
        assert_eq!(fs::read(&built.inv.executable).unwrap(), b"#!/bin/sh\nexit 0\n");
        fs::write(&lean_bin, b"#!/bin/sh\nexit 0\n").unwrap();

        // Symlinked `lib/lean` must fail closed before running Lean.
        let bad_prefix = base.join("bad-lean-toolchain");
        fs::create_dir_all(bad_prefix.join("bin")).unwrap();
        fs::create_dir_all(bad_prefix.join("lib")).unwrap();
        let bad_lean = bad_prefix.join("bin/lean");
        fs::write(&bad_lean, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&bad_lean, fs::Permissions::from_mode(0o755)).unwrap();
        symlink(&evil_dir, bad_prefix.join("lib/lean")).unwrap();
        let err_sym = apply_lean_tool_env_with_tmpdir(
            Invocation::new(&bad_lean, &[]),
            &bad_lean,
            &fake_store,
            &trusted_child_dirs,
            None,
            &base,
            None,
        )
        .unwrap_err();
        assert!(err_sym.contains("symlink"), "{err_sym}");

        // Relative `TMPDIR` anchors to `caller_cwd`; bad `TMPDIR` fails closed.
        let caller_cwd = base.join("caller");
        let rel_tmp = caller_cwd.join("rel-tmp");
        fs::create_dir_all(&rel_tmp).unwrap();
        let with_rel_tmp = apply_lean_tool_env_with_tmpdir(
            Invocation::new(&lean_bin, &[]),
            &lean_bin,
            &fake_store,
            &trusted_child_dirs,
            None,
            &caller_cwd,
            Some(OsStr::new("rel-tmp")),
        )
        .expect("relative existing TMPDIR must anchor cleanly");
        assert_eq!(with_rel_tmp.validated_tmpdir.as_deref(), Some(rel_tmp.as_path()));
        assert_eq!(
            with_rel_tmp.inv.environment.get(OsStr::new("TMPDIR")).map(OsString::as_os_str),
            Some(rel_tmp.as_os_str())
        );

        let sym_tmp = caller_cwd.join("sym-tmp");
        symlink(&rel_tmp, &sym_tmp).unwrap();
        for bad_tmp in [OsStr::new("../outside"), sym_tmp.as_os_str(), OsStr::new("missing-tmp")] {
            let err_tmp = apply_lean_tool_env_with_tmpdir(
                Invocation::new(&lean_bin, &[]),
                &lean_bin,
                &fake_store,
                &trusted_child_dirs,
                None,
                &caller_cwd,
                Some(bad_tmp),
            )
            .unwrap_err();
            assert!(err_tmp.contains("TMPDIR"), "bad TMPDIR {:?} -> {err_tmp}", bad_tmp);
        }

        // `LeanSession` forwards anchored canonical `TMPDIR` to both capture
        // and Lean subprocesses even after switching into private group dirs,
        // and `LeanSession::prepare_at` rejects unsafe `TMPDIR` upfront.
        let fake_rust_sys = base.join("rust-sys");
        fs::create_dir_all(fake_rust_sys.join("bin")).unwrap();
        fs::create_dir_all(fake_rust_sys.join("lib")).unwrap();
        fs::write(fake_rust_sys.join("bin/rustc"), "#!/bin/sh\nexit 0\n").unwrap();
        let cap_tmp_log = base.join("cap-tmp.txt");
        let lean_tmp_log = base.join("lean-tmp.txt");
        let fake_cap = base.join("fake-capture.sh");
        fs::write(
            &fake_cap,
            format!(
                "#!/bin/sh\nset -eu\n\
                 printf '%s\\n' \"${{TMPDIR:-}}\" >> '{}'\n\
                 outdir=\"\"\nwhile [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in --out-dir) outdir=\"$2\"; shift 2 ;; *) shift ;; esac\n\
                 done\n\
                 mkdir -p \"$outdir\"\n\
                 echo '-- stub' > \"$outdir/Captured.lean\"\n\
                 echo '{{\"program\":{{\"bodies\":[{{\"identity\":\"rust-path-v1::fuzz_ok\",\"arg_count\":0,\"local_tys\":[\"u32\"],\"blocks\":[{{\"statements\":[],\"terminator\":{{\"kind\":\"return\"}}}}]}}]}}}}' > \"$outdir/capture.json\"\n\
                 printf '{{\"status\":\"captured\",\"capture\":\"%s/capture.json\",\"lean\":\"%s/Captured.lean\"}}\\n' \"$outdir\" \"$outdir\"\n",
                cap_tmp_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_cap, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_lean_run = prefix.join("bin/lean");
        fs::write(
            &fake_lean_run,
            format!(
                "#!/bin/sh\nset -eu\n\
                 printf '%s\\n' \"${{TMPDIR:-}}\" >> '{}'\n\
                 out=\"\"\nprobe=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     -o) out=\"$2\"; shift 2 ;;\n\
                     -R|-D) shift 2 ;;\n\
                     *) probe=\"$1\"; shift ;;\n\
                   esac\n\
                 done\n\
                 if [ -n \"$out\" ]; then : > \"$out\"; exit 0; fi\n\
                 echo '\"ANNEAL_LEAN_CASE:c0:BODY|0|rust-path-v1::fuzz_ok|MR0:RETURNED:INT:i32:u:7\"'\n",
                lean_tmp_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_lean_run, fs::Permissions::from_mode(0o755)).unwrap();

        let bad_tools = ToolchainEnv {
            sysroot: fake_rust_sys.clone(),
            lean: fake_lean_run.clone(),
            lean_bin_dir: prefix.join("bin"),
            cli: None,
            capture: Some(fake_cap.clone()),
            auditor: None,
            has_ndjson_quorum_tools: false,
        };
        let err_prep_tmp = LeanSession::prepare_at(
            &base,
            &bad_tools,
            &base.join("lean-cache"),
            &caller_cwd,
            Some(OsStr::new("../outside")),
        )
        .unwrap_err();
        assert!(err_prep_tmp.contains("TMPDIR"), "{err_prep_tmp}");
        assert!(!lean_tmp_log.exists(), "lean must not run with bad TMPDIR");

        let child_path = crate::rustc_runner::build_child_path_with_bins(
            &[&prefix.join("bin")],
            None,
            &fake_store,
            &trusted_child_dirs,
            None,
            &caller_cwd,
        )
        .unwrap();
        let session = LeanSession {
            anneal_root: base.clone(),
            capture_bin: fake_cap,
            rust_sysroot: fake_rust_sys,
            lean_bin: fake_lean_run,
            olean_paths: vec![base.clone()],
            prebuilt_overlay: "none".to_owned(),
            ld_library_path: String::new(),
            child_path: child_path.clone(),
            lean_ld_library_path: prefix.join("lib/lean").to_string_lossy().into_owned(),
            lean_child_path: child_path,
            validated_tmpdir: Some(rel_tmp.clone()),
            _rust_sysroot_staging: None,
            _capture_staging: None,
            _lean_lib_staging: None,
            _lean_stdlib_staging: None,
            _lean_dag_staging: None,
        };
        let prog = crate::r#gen::GenProgram {
            case_id: "c0".to_owned(),
            fn_name: "fuzz_ok".to_owned(),
            master_seed: 1,
            case_index: 0,
            category: crate::r#gen::GenCategory::SafeAdmitted,
            is_unsafe: false,
            params: vec![],
            locals: vec![],
            body: vec![],
            ret_ty: crate::r#gen::GenType::Int(IntKind::U32),
            ret_expr: crate::r#gen::GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
            fuel: 100,
        };
        let res = session
            .capture_and_evaluate_fuzz_batch(&base.join("group_tmp"), "tmp_mod", &[&prog])
            .expect("capture and lean eval must succeed with anchored TMPDIR");
        assert_eq!(
            res["c0"].outcome,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
        assert_eq!(fs::read_to_string(&cap_tmp_log).unwrap().trim(), rel_tmp.display().to_string());
        let lean_tmps = fs::read_to_string(&lean_tmp_log).unwrap();
        assert_eq!(lean_tmps.lines().count(), 2, "{lean_tmps}");
        assert!(lean_tmps.lines().all(|l| l == rel_tmp.display().to_string()), "{lean_tmps}");
    }

    #[cfg(unix)]
    #[test]
    fn lean_session_prepare_stages_non_store_lean_and_capture_against_post_prepare_tamper() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

        let tmp = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(tmp.path()).unwrap();
        let anneal_root = base.join("anneal");
        let tc = base.join("writable-lean-tc");
        let rust_sys = base.join("rust-sys");
        for d in [tc.join("bin"), tc.join("lib/lean"), rust_sys.join("bin"), rust_sys.join("lib")] {
            fs::create_dir_all(d).unwrap();
        }
        for spec in MIR_TOTAL_DAG {
            let rel_mod = spec.module.replace('.', "/");
            let lean_src = anneal_root.join(spec.rel_tree).join(format!("{rel_mod}.lean"));
            fs::create_dir_all(lean_src.parent().unwrap()).unwrap();
            fs::write(&lean_src, "-- stub\n").unwrap();
        }
        fs::write(rust_sys.join("bin/rustc"), "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(rust_sys.join("bin/rustc"), fs::Permissions::from_mode(0o755)).unwrap();
        fs::write(tc.join("lib/lean/Init.olean"), b"init").unwrap();
        fs::write(tc.join("lib/libleanshared.so"), b"lean-so").unwrap();

        let cap_bin = base.join("writable-capture");
        let cap_script = "#!/bin/sh\nset -eu\n\
             outdir=\"\"\nwhile [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in --out-dir) outdir=\"$2\"; shift 2 ;; *) shift ;; esac\n\
             done\n\
             mkdir -p \"$outdir\"\n\
             echo '-- stub' > \"$outdir/Captured.lean\"\n\
             echo '{\"program\":{\"bodies\":[{\"identity\":\"rust-path-v1::fuzz_ok\",\"arg_count\":0,\"local_tys\":[\"u32\"],\"blocks\":[{\"statements\":[],\"terminator\":{\"kind\":\"return\"}}]}]}}' > \"$outdir/capture.json\"\n\
             printf '{\"status\":\"captured\",\"capture\":\"%s/capture.json\",\"lean\":\"%s/Captured.lean\"}\\n' \"$outdir\" \"$outdir\"\n";
        fs::write(&cap_bin, cap_script).unwrap();
        fs::set_permissions(&cap_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let lean_bin = tc.join("bin/lean");
        let lean_script = "#!/bin/sh\nset -eu\n\
             if [ \"${1:-}\" = \"--print-prefix\" ]; then\n\
               bin_dir=$(cd \"$(dirname \"$0\")\" && pwd -P)\n\
               dirname \"$bin_dir\"\n\
               exit 0\n\
             fi\n\
             out=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in\n\
                 -o) out=\"$2\"; shift 2 ;;\n\
                 -R|-D) shift 2 ;;\n\
                 *) shift ;;\n\
               esac\n\
             done\n\
             if [ -n \"$out\" ]; then mkdir -p \"$(dirname \"$out\")\"; : > \"$out\"; exit 0; fi\n\
             echo '\"ANNEAL_LEAN_CASE:c0:BODY|0|rust-path-v1::fuzz_ok|MR0:RETURNED:INT:i32:u:7\"'\n";
        fs::write(&lean_bin, lean_script).unwrap();
        fs::set_permissions(&lean_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let tools = ToolchainEnv {
            sysroot: rust_sys,
            lean: lean_bin.clone(),
            lean_bin_dir: tc.join("bin"),
            cli: None,
            capture: Some(cap_bin.clone()),
            auditor: None,
            has_ndjson_quorum_tools: false,
        };
        let session =
            LeanSession::prepare_at(&anneal_root, &tools, &base.join("lean-cache"), &base, None)
                .expect("LeanSession::prepare_at must succeed on clean writable Lean toolchain");

        assert_ne!(session.lean_bin, lean_bin);
        assert_ne!(session.capture_bin, cap_bin);
        assert!(session._lean_dag_staging.is_some());
        assert_ne!(session.olean_paths[0], base.join("lean-cache"));
        assert_eq!(
            fs::symlink_metadata(&session.olean_paths[0]).unwrap().permissions().mode() & 0o777,
            0o555
        );
        for staged in [&session.lean_bin, &session.capture_bin] {
            let meta = fs::symlink_metadata(staged).unwrap();
            assert!(!meta.file_type().is_symlink());
            assert_eq!(meta.nlink(), 1);
            assert_eq!(meta.permissions().mode() & 0o777, 0o555);
            assert_eq!(
                fs::symlink_metadata(staged.parent().unwrap()).unwrap().permissions().mode()
                    & 0o777,
                0o555
            );
        }
        let lean_path_dirs: Vec<PathBuf> = env::split_paths(&session.lean_child_path).collect();
        assert!(lean_path_dirs.contains(&session.lean_bin.parent().unwrap().to_path_buf()));
        assert!(!lean_path_dirs.contains(&tc.join("bin")));
        assert_eq!(
            session.olean_paths.last().map(PathBuf::as_path),
            Some(session.lean_bin.parent().unwrap().parent().unwrap().join("lib/lean").as_path())
        );

        // Overwrite original `lean_bin` and `capture_bin` after prepare:
        // session must keep executing the frozen immutable staged copies.
        fs::write(&lean_bin, "#!/bin/sh\necho TAMPERED_LEAN >&2\nexit 99\n").unwrap();
        fs::write(&cap_bin, "#!/bin/sh\necho TAMPERED_CAP >&2\nexit 99\n").unwrap();
        let prog = crate::r#gen::GenProgram {
            case_id: "c0".to_owned(),
            fn_name: "fuzz_ok".to_owned(),
            master_seed: 1,
            case_index: 0,
            category: crate::r#gen::GenCategory::SafeAdmitted,
            is_unsafe: false,
            params: vec![],
            locals: vec![],
            body: vec![],
            ret_ty: crate::r#gen::GenType::Int(IntKind::U32),
            ret_expr: crate::r#gen::GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
            fuel: 100,
        };
        let res = session
            .capture_and_evaluate_fuzz_batch(&base.join("group_tmp"), "tmp_mod", &[&prog])
            .expect("staged lean and capture binaries must resist post-prepare source tamper");
        assert_eq!(
            res["c0"].outcome,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
    }
}
