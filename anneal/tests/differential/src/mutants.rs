// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Self-check AST-mutated program probes (`--self-check-oracle`).
//!
//! Each corpus-linked mutant rewrites a captured MIR body's AST (operator or
//! local integer signedness) and evaluates the mutated program under the
//! unmodified Lean `evalMirFuelBy` evaluator against real corpus Miri
//! reference outcomes (using arguments derived directly from the manifest).
//! A separate `synthetic_lean_probes` entry exercises a Lean-only `Use.move`
//! deinitialization program without polluting corpus kill percentages. Guard
//! mutations of the Lean TCB itself are checked separately by
//! `ci/check_guard_mutation.py`.

use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

use anneal_testkit::{Invocation, Termination};
use serde::{Deserialize, Serialize};

use crate::{
    corpus::LitmusCase,
    lean_runner::{
        CapturedModule, LEAN_COMPILE_FLAGS, LeanSession, effective_timeout_secs, lean_val_expr,
        parse_lean_payload, run_supervised_cmd_in_tmp,
    },
    verdict::{Expectation, ObservedOutcome, evaluate_case},
};

const MUTANT_PROBE_TIMEOUT_SECS: u64 = 180;

/// Report covering a single corpus-linked AST-mutated oracle probe.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MutantResult {
    pub mutant_id: String,
    pub target_case_id: String,
    pub description: String,
    pub killed: bool,
    pub expected_kill_verdict: String,
    pub actual_verdict: String,
}

/// Report covering a synthetic Lean-only semantics self-probe (not counted in
/// corpus mutant kill percentages).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SyntheticProbeResult {
    pub probe_id: String,
    pub description: String,
    pub passed: bool,
    pub expected_kill_verdict: String,
    pub actual_verdict: String,
}

/// Summary report across all Stage-1 oracle self-check mutants and synthetic
/// probes.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MutantSuiteReport {
    pub total_mutants: usize,
    pub killed_mutants: usize,
    pub killed_pct: f64,
    pub results: Vec<MutantResult>,
    pub synthetic_lean_probes: Vec<SyntheticProbeResult>,
}

struct MutantSpec {
    id: &'static str,
    target_case_id: &'static str,
    description: &'static str,
    expected_kill: &'static str,
}

const MUTANT_SPECS: &[MutantSpec] = &[
    MutantSpec {
        id: "mutant_unchecked_add_wraps",
        target_case_id: "ub_unchecked_add_u32_ovf",
        description: "AST rewrite replaces SysrootCall uncheckedAdd with wrappingAdd so u32::MAX + 1 returns 0 instead of faulting UB",
        expected_kill: "UnsoundMissedFault",
    },
    MutantSpec {
        id: "mutant_unchecked_sub_wraps",
        target_case_id: "ub_unchecked_sub_i32_ovf",
        description: "AST rewrite replaces SysrootCall uncheckedSub with wrappingSub so i32::MIN - 1 returns i32::MAX instead of faulting UB",
        expected_kill: "UnsoundMissedFault",
    },
    MutantSpec {
        id: "mutant_unchecked_mul_wraps",
        target_case_id: "ub_unchecked_mul_i8_ovf",
        description: "AST rewrite replaces SysrootCall uncheckedMul with wrappingMul so 64i8 * 4 returns 0 instead of faulting UB",
        expected_kill: "UnsoundMissedFault",
    },
    MutantSpec {
        id: "mutant_shl_swapped_to_shr",
        target_case_id: "arith_u32_shl_over_width",
        description: "AST rewrite swaps BinaryOp::Shl to Shr so 1u32 << 35 evaluates 1u32 >> 35 (0 instead of 8)",
        expected_kill: "ValueMismatch",
    },
    MutantSpec {
        id: "mutant_int_to_int_drops_sign_extend",
        target_case_id: "cast_char_bool_int_branch_false",
        description: "AST rewrite narrows i32 cast target/local to unsigned u16 so widening negative i16 zero-extends instead of sign-extending",
        expected_kill: "ValueMismatch",
    },
];

/// Run all 5 manifest-derived AST-mutated probes against real Miri outcomes
/// (plus the standalone `moveDeinitProg` Lean probe) and verify 100% kills.
pub fn run_self_check_mutants(
    lean: &LeanSession,
    captured_by_source: &BTreeMap<PathBuf, CapturedModule>,
    cases: &[LitmusCase],
    miri_outcomes: &BTreeMap<String, ObservedOutcome>,
) -> Result<MutantSuiteReport, String> {
    let mut case_by_id = BTreeMap::new();
    for c in cases {
        case_by_id.insert(c.id.as_str(), c);
    }

    let arith_cap = find_captured_suffix(captured_by_source, "arith_pass.rs")?;
    let cf_cap = find_captured_suffix(captured_by_source, "control_enum_pass.rs")?;
    let ub_cap = find_captured_suffix(captured_by_source, "ub_corpus.rs")?;

    let tmp =
        crate::mir_eval_runner::build_temp_dir("anneal-mutant-", lean.validated_tmpdir.as_deref())?;
    let probe_sources = build_mutant_probe_sources(arith_cap, cf_cap, ub_cap, &case_by_id)?;
    let raw_outcomes =
        run_mutant_probes(lean, tmp.path(), &probe_sources, arith_cap, cf_cap, ub_cap)?;

    let mut results = Vec::with_capacity(MUTANT_SPECS.len());
    let mut killed = 0usize;

    for spec in MUTANT_SPECS {
        let mutant_lean =
            raw_outcomes.get(spec.id).cloned().unwrap_or_else(|| ObservedOutcome::ToolError {
                detail: format!("missing Lean mutant result for {}", spec.id),
            });

        let case = case_by_id
            .get(spec.target_case_id)
            .ok_or_else(|| format!("missing corpus case {:?}", spec.target_case_id))?;
        let miri_out = miri_outcomes.get(spec.target_case_id).ok_or_else(|| {
            format!("missing Miri reference outcome for mutant target {:?}", spec.target_case_id)
        })?;
        let verdict = evaluate_case(
            case.expected,
            case.expected_return.as_ref(),
            case.miri_ub_contains.as_deref(),
            case.expected_miri,
            miri_out,
            &mutant_lean,
            None,
        );

        let is_killed = !verdict.is_ok() && verdict.label() == spec.expected_kill;
        if is_killed {
            killed += 1;
        }
        results.push(MutantResult {
            mutant_id: spec.id.to_owned(),
            target_case_id: spec.target_case_id.to_owned(),
            description: spec.description.to_owned(),
            killed: is_killed,
            expected_kill_verdict: spec.expected_kill.to_owned(),
            actual_verdict: verdict.label().to_owned(),
        });
    }

    let unmutated_move = raw_outcomes.get("ref_move_deinit").cloned().unwrap_or_else(|| {
        ObservedOutcome::ToolError { detail: "missing unmutated move-deinit reference".to_owned() }
    });
    let mutated_move =
        raw_outcomes.get("probe_move_deinit_ignored").cloned().unwrap_or_else(|| {
            ObservedOutcome::ToolError { detail: "missing mutated move-deinit probe".to_owned() }
        });
    let move_verdict =
        evaluate_case(Expectation::Ub, None, None, None, &unmutated_move, &mutated_move, None);
    let move_killed = !move_verdict.is_ok() && move_verdict.label() == "UnsoundMissedFault";
    let synthetic_lean_probes = vec![SyntheticProbeResult {
        probe_id: "probe_move_deinit_ignored".to_owned(),
        description: "Synthetic Lean-only Use.move-to-Use.copy AST rewrite verifies move deinitialization fault detection".to_owned(),
        passed: move_killed,
        expected_kill_verdict: "UnsoundMissedFault".to_owned(),
        actual_verdict: move_verdict.label().to_owned(),
    }];

    let total = MUTANT_SPECS.len();
    let killed_pct = if total == 0 { 0.0 } else { (killed as f64) * 100.0 / (total as f64) };
    Ok(MutantSuiteReport {
        total_mutants: total,
        killed_mutants: killed,
        killed_pct,
        results,
        synthetic_lean_probes,
    })
}

fn find_captured_suffix<'a>(
    map: &'a BTreeMap<PathBuf, CapturedModule>,
    suffix: &str,
) -> Result<&'a CapturedModule, String> {
    map.iter()
        .find(|(p, _)| p.ends_with(suffix))
        .map(|(_, c)| c)
        .ok_or_else(|| format!("missing captured module for {suffix} in mutant self-check"))
}

fn format_manifest_args(
    case_by_id: &BTreeMap<&str, &LitmusCase>,
    cap: &CapturedModule,
    case_id: &str,
) -> Result<(usize, usize, String), String> {
    let case = case_by_id
        .get(case_id)
        .copied()
        .ok_or_else(|| format!("missing manifest case {case_id:?} for mutant probe"))?;
    let def_id = cap
        .body_ids_by_fn
        .get(&case.function)
        .copied()
        .ok_or_else(|| format!("missing defId for function {:?} ({case_id})", case.function))?;
    let args_lean = case
        .args
        .iter()
        .enumerate()
        .map(|(arg_idx, val)| lean_val_expr(val, def_id, arg_idx))
        .collect::<Result<Vec<_>, _>>()?
        .join(", ");
    Ok((def_id, case.fuel, args_lean))
}

const SHARED_AST_MUTATORS_LEAN: &str = r#"
import Captured
import Anneal.MirTotal.ExecTotal
open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal

def widthName : IntWidth → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32"
  | .i64 => "i64" | .i128 => "i128" | .isize => "isize"

def renderPrim : Val → String
  | .scalar sv => "INT:" ++ widthName sv.width ++ ":" ++ (if sv.signed then "s" else "u") ++ ":" ++ toString sv.bits.toNat
  | .bool b => if b then "BOOL:true" else "BOOL:false"
  | _ => "OTHER"

def argEnumVal (prog : Program) (defId argIdx variantIdx : Nat) : Val :=
  match (prog.bodies[defId]?).bind (fun b => b.locals[argIdx + 1]?) with
  | some (.enum ety) => .enumVal ety variantIdx
  | _ => .unit

def evalMutatedProg (prog : Program) (fuel : Nat) (args : List Val) : String :=
  match initStateBy (mirTyBeqAt 8) prog { args := args } with
  | .error .undefined => "INIT_UNDEFINED"
  | .error .unsupported => "INIT_UNSUPPORTED"
  | .ok s0 =>
    match evalMirFuelBy (mirTyBeqAt 8) prog fuel s0 with
    | .step _ => "OUT_OF_FUEL"
    | .fault .undefined => "FAULT:undefined"
    | .fault .unsupported => "FAULT:unsupported"
    | .done (.unwound _) => "UNWOUND"
    | .done (.aborted _) => "ABORTED"
    | .done (.returned out) => "RETURNED:" ++ renderPrim out.ret

def mapBody (defId : Nat) (f : Body → Body) (p : Program) : Program :=
  let bodies' := p.bodies.mapIdx (fun i b => if i == defId then f b else b)
  { p with bodies := bodies', entryDefId := defId }

def mapStmts (f : StatementKind → StatementKind) (b : Body) : Body :=
  { b with basicBlocks := b.basicBlocks.map (fun bb => { bb with statements := bb.statements.map f }) }

def mapTerminators (f : TerminatorKind → TerminatorKind) (b : Body) : Body :=
  { b with basicBlocks := b.basicBlocks.map (fun bb => { bb with terminator := f bb.terminator }) }
"#;

fn build_mutant_probe_sources(
    arith_cap: &CapturedModule,
    cf_cap: &CapturedModule,
    ub_cap: &CapturedModule,
    case_by_id: &BTreeMap<&str, &LitmusCase>,
) -> Result<(String, String, String), String> {
    let (ub_add, ub_add_fuel, ub_add_args) =
        format_manifest_args(case_by_id, ub_cap, "ub_unchecked_add_u32_ovf")?;
    let (ub_sub, ub_sub_fuel, ub_sub_args) =
        format_manifest_args(case_by_id, ub_cap, "ub_unchecked_sub_i32_ovf")?;
    let (ub_mul, ub_mul_fuel, ub_mul_args) =
        format_manifest_args(case_by_id, ub_cap, "ub_unchecked_mul_i8_ovf")?;
    let (arith_shl, arith_shl_fuel, arith_shl_args) =
        format_manifest_args(case_by_id, arith_cap, "arith_u32_shl_over_width")?;
    let (cf_cast, cf_cast_fuel, cf_cast_args) =
        format_manifest_args(case_by_id, cf_cap, "cast_char_bool_int_branch_false")?;

    let ub_probe = format!(
        "{SHARED_AST_MUTATORS_LEAN}\n\
         def sysrootKindEq : SysrootNumKind → SysrootNumKind → Bool\n\
         \x20\x20| .uncheckedAdd, .uncheckedAdd => true\n\
         \x20\x20| .uncheckedSub, .uncheckedSub => true\n\
         \x20\x20| .uncheckedMul, .uncheckedMul => true\n\
         \x20\x20| .wrappingAdd, .wrappingAdd => true\n\
         \x20\x20| .wrappingSub, .wrappingSub => true\n\
         \x20\x20| .wrappingMul, .wrappingMul => true\n\
         \x20\x20| _, _ => false\n\n\
         def rewriteSysrootKind (fromKind toKind : SysrootNumKind) : TerminatorKind → TerminatorKind\n\
         \x20\x20| .sysrootCall op args dst target unwind =>\n\
         \x20\x20\x20\x20if sysrootKindEq op.kind fromKind then\n\
         \x20\x20\x20\x20\x20\x20.sysrootCall {{ op with kind := toKind }} args dst target unwind\n\
         \x20\x20\x20\x20else\n\
         \x20\x20\x20\x20\x20\x20.sysrootCall op args dst target unwind\n\
         \x20\x20| t => t\n\n\
         def moveDeinitProg : Program :=\n\
         \x20\x20{{ bodies := [Body.mk 1 [.int .i32 false, .int .i32 false] [BasicBlock.mk [.assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)), .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))] .return_ false] false \"mutant::move_deinit\"],\n\
         \x20\x20\x20\x20entryDefId := 0,\n\
         \x20\x20\x20\x20pointerWidthBits := 64,\n\
         \x20\x20\x20\x20mirProfileVersion := 1,\n\
         \x20\x20\x20\x20scope := .unit,\n\
         \x20\x20\x20\x20overflowChecks := false,\n\
         \x20\x20\x20\x20panicStrategy := .unwind,\n\
         \x20\x20\x20\x20hasLocalPanicHandler := true }}\n\n\
         def rewriteMoveToCopy : StatementKind → StatementKind\n\
         \x20\x20| .assign dst (.use (.move p)) => .assign dst (.use (.copy p))\n\
         \x20\x20| s => s\n\n\
         #eval \"MUTANT:mutant_unchecked_add_wraps:\" ++ (evalMutatedProg (mapBody {ub_add} (mapTerminators (rewriteSysrootKind .uncheckedAdd .wrappingAdd)) Captured.program) {ub_add_fuel} [{ub_add_args}])\n\
         #eval \"MUTANT:mutant_unchecked_sub_wraps:\" ++ (evalMutatedProg (mapBody {ub_sub} (mapTerminators (rewriteSysrootKind .uncheckedSub .wrappingSub)) Captured.program) {ub_sub_fuel} [{ub_sub_args}])\n\
         #eval \"MUTANT:mutant_unchecked_mul_wraps:\" ++ (evalMutatedProg (mapBody {ub_mul} (mapTerminators (rewriteSysrootKind .uncheckedMul .wrappingMul)) Captured.program) {ub_mul_fuel} [{ub_mul_args}])\n\
         #eval \"MUTANT:ref_move_deinit:\" ++ (evalMutatedProg moveDeinitProg 50 [.scalar ⟨.i32, false, BitVec.ofNat 128 42⟩])\n\
         #eval \"MUTANT:probe_move_deinit_ignored:\" ++ (evalMutatedProg (mapBody 0 (mapStmts rewriteMoveToCopy) moveDeinitProg) 50 [.scalar ⟨.i32, false, BitVec.ofNat 128 42⟩])\n"
    );

    let arith_probe = format!(
        "{SHARED_AST_MUTATORS_LEAN}\n\
         def rewriteShlToShr : StatementKind → StatementKind\n\
         \x20\x20| .assign dst (.binaryOp .shl l r) => .assign dst (.binaryOp .shr l r)\n\
         \x20\x20| s => s\n\n\
         #eval \"MUTANT:mutant_shl_swapped_to_shr:\" ++ (evalMutatedProg (mapBody {arith_shl} (mapStmts rewriteShlToShr) Captured.program) {arith_shl_fuel} [{arith_shl_args}])\n"
    );

    let cf_probe = format!(
        "{SHARED_AST_MUTATORS_LEAN}\n\
         def dropSignedExtCast : StatementKind → StatementKind\n\
         \x20\x20| .assign dst (.cast .intToInt op (.int .i32 true)) => .assign dst (.cast .intToInt op (.int .i16 false))\n\
         \x20\x20| s => s\n\n\
         def dropSignedExtLocal (b : Body) : Body :=\n\
         \x20\x20let b' := {{ b with locals := b.locals.mapIdx (fun idx ty => if idx == 0 || idx > b.argumentCount then match ty with | .int .i32 true => .int .i16 false | _ => ty else ty) }}\n\
         \x20\x20mapStmts dropSignedExtCast b'\n\n\
         #eval \"MUTANT:mutant_int_to_int_drops_sign_extend:\" ++ (evalMutatedProg (mapBody {cf_cast} dropSignedExtLocal Captured.program) {cf_cast_fuel} [{cf_cast_args}])\n"
    );

    Ok((ub_probe, arith_probe, cf_probe))
}

fn run_mutant_probes(
    lean: &LeanSession,
    dir: &Path,
    probes: &(String, String, String),
    arith_cap: &CapturedModule,
    cf_cap: &CapturedModule,
    ub_cap: &CapturedModule,
) -> Result<BTreeMap<String, ObservedOutcome>, String> {
    let mut results = BTreeMap::new();
    let specs = [
        (dir.join("mut_ub.lean"), &ub_cap.olean_dir, &probes.0),
        (dir.join("mut_arith.lean"), &arith_cap.olean_dir, &probes.1),
        (dir.join("mut_cf.lean"), &cf_cap.olean_dir, &probes.2),
    ];

    let probe_timeout = effective_timeout_secs(MUTANT_PROBE_TIMEOUT_SECS)?;
    for (path, olean_dir, src) in specs {
        fs::write(&path, src).map_err(|e| format!("write {}: {e}", path.display()))?;
        let lean_path = lean.lean_path_with(Some(olean_dir))?;
        let inv = lean.apply_lean_env(
            Invocation::new(&lean.lean_bin, LEAN_COMPILE_FLAGS)
                .arg(&path)
                .env("LEAN_PATH", &lean_path),
        );
        let out = run_supervised_cmd_in_tmp(
            &inv,
            dir,
            probe_timeout,
            lean.validated_tmpdir.as_deref(),
            &format!("mutant probe {}", path.display()),
        )?;
        match out.termination {
            Termination::Exited(s) if s.success() => {}
            other => {
                return Err(format!(
                    "mutant probe {} failed ({}):\nstdout:\n{}\nstderr:\n{}",
                    path.display(),
                    other.describe(),
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                ));
            }
        }
        let stdout = String::from_utf8_lossy(&out.stdout);
        for line in stdout.lines() {
            let trimmed = line.trim();
            let unquoted =
                trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(trimmed);
            if let Some(rest) = unquoted.strip_prefix("MUTANT:")
                && let Some((id, payload)) = rest.split_once(':')
            {
                results.insert(id.to_owned(), parse_lean_payload(payload)?);
            }
        }
    }
    Ok(results)
}
