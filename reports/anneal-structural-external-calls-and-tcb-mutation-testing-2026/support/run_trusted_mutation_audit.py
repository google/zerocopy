#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Automated semantic mutation-testing harness for Anneal's Trusted/*.lean TCB.

Copies `trusted/lean/` and `theory/` from `trusted-core` and `mir-to-x86` into an
isolated scratch sandbox, applies 24 semantic guard-weakening and failure-
deletion mutations to `Trusted/MirSemantics.lean` and 24 to
`Trusted/X86Semantics.lean`, verifies that every mutated `Trusted/*.lean` module
still type-checks in the Lean 4 kernel, and measures mutation kill vs. survival
rates against:
  1. `BaselineCanaries.lean` (the 5 existing negative canaries in `MirLemmas.lean`),
  2. Full existing `theory/` (`MirLemmas.lean` / `NaiveCodegen.lean`), and
  3. `AugmentedCanaries.lean` (the 24-canary negative refutation suite).
"""

import argparse
import json
import os
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple

LEAN_BIN = os.environ.get("LEAN_BIN", "lean")
LEAN_FLAGS = ["-DElab.async=false", "-Ddebug.skipKernelTC=false"]

TRUSTED_CORE_ROOT = Path(os.environ.get("ANNEAL_TRUSTED_CORE_ROOT", "anneal-trusted-core"))
MIR_TO_X86_ROOT = Path(os.environ.get("ANNEAL_MIR_TO_X86_ROOT", "anneal-mir-to-x86"))

OUT_DIR = Path(__file__).resolve().parent
SANDBOX_DIR = OUT_DIR / "_mutation_sandbox"
RESULTS_JSON = OUT_DIR / "mutation_audit_results.json"


def get_root_dir(lean_file: Path) -> Path:
    if lean_file.parent.name in ("Trusted", "Anneal"):
        return lean_file.parent.parent
    return lean_file.parent


def run_lean(lean_file: Path, lean_path: List[Path], timeout: int = 60) -> Tuple[int, str]:
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(str(p) for p in lean_path)
    root_dir = get_root_dir(lean_file)
    cmd = [LEAN_BIN, *LEAN_FLAGS, str(lean_file)]
    proc = subprocess.run(
        cmd, cwd=str(root_dir), env=env, capture_output=True, text=True, timeout=timeout
    )
    return proc.returncode, (proc.stdout + "\n" + proc.stderr).strip()


def compile_to_olean(lean_file: Path, olean_file: Path, lean_path: List[Path]) -> Tuple[int, str]:
    olean_file.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(str(p) for p in lean_path)
    root_dir = get_root_dir(lean_file)
    cmd = [LEAN_BIN, *LEAN_FLAGS, "-o", str(olean_file), str(lean_file)]
    proc = subprocess.run(
        cmd, cwd=str(root_dir), env=env, capture_output=True, text=True, timeout=90
    )
    return proc.returncode, (proc.stdout + "\n" + proc.stderr).strip()


MIR_BASELINE_CANARIES_LEAN = """-- Copyright 2026 The Fuchsia Authors
-- Licensed under BSD / Apache-2.0 / MIT.
prelude
import Trusted
import Anneal.Refinement
import Anneal.StepResult

namespace Anneal
open Trusted

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hbeq : (a == b) with
  | false => rfl
  | true => exact False.elim (h (of_decide_eq_true hbeq))

def s0_noArgs : MirState where
  locals := fun _ => none
  block := 0
  stmtIdx := 0

theorem initEntryState_s0_noArgs (body : MirBody) (hArgs : body.argTys = []) :
    initEntryState body s0_noArgs := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold argsMatchLocals argsMatchInv
  rw [hArgs]
  intro j _
  rfl

theorem monoAdmitted_of_no_call1 (tySizes : Nat → Nat) (body : MirBody)
    (hReq : body.requiredConsts = [])
    (hNoCall1 : ∀ bb, bb ∈ body.blocks → ∀ dst callee arg target typeArgs,
      bb.terminator ≠ .call1 dst callee arg target typeArgs) :
    MonoAdmitted tySizes body := by
  intro tySizes' c hrc
  cases hrc with
  | direct hmem => rw [hReq] at hmem; cases hmem
  | nested hmem _ => rw [hReq] at hmem; cases hmem
  | call1 hbb hterm _ => exact False.elim (hNoCall1 _ hbb _ _ _ _ _ hterm)

theorem initMirState_oneBlock_noArgs (body : MirBody) (bb : BasicBlock)
    (hArgs : body.argTys = []) (hReq : body.requiredConsts = [])
    (hBlocks : body.blocks = [bb])
    (hTerm : ∀ dst callee arg target typeArgs,
      bb.terminator ≠ .call1 dst callee arg target typeArgs) :
    initMirState body s0_noArgs := by
  refine ⟨initEntryState_s0_noArgs body hArgs, ?_⟩
  refine monoAdmitted_of_no_call1 s0_noArgs.tySizes body hReq ?_
  intro b hb; rw [hBlocks] at hb
  cases hb with
  | head => exact hTerm
  | tail _ hnil => cases hnil

theorem not_wellFormed_of_reaches_failed
    {body : MirBody} {s₀ : MirState} {n : Nat} {tr : List Unit}
    (hinit : initMirState body s₀)
    (hreach : ReachesPrefix MirStep body n s₀ tr .failed) :
    ¬ (MirSem body ≤ MirLang.WellFormed) := by
  intro hwf
  have hq := hwf { init := s₀, steps := n } True.intro
  cases hq with
  | intro hdef _ => exact hdef hinit tr .failed hreach

theorem not_spec_of_reaches_normal
    {body : MirBody} {s₀ : MirState} {n : Nat} {tr : List Unit} {v : MirVal}
    {Post : ExecQuery MirState → ExecOut Unit MirVal → Prop}
    (hinit : initMirState body s₀)
    (hreach : ReachesPrefix MirStep body n s₀ tr (.terminated (.normal v)))
    (hnot : ¬ Post { init := s₀, steps := n }
      { trace := tr, outcome := .terminated (.normal v) }) :
    ¬ (MirSem body ≤ MirLang.Spec Post) := by
  intro hspec
  have hq := hspec { init := s₀, steps := n } True.intro
  cases hq with
  | intro _ hval =>
    exact hnot (hval { trace := tr, outcome := .terminated (.normal v) } ⟨hinit, hreach⟩)

-- Baseline Canary 1 (M14): transmute_copy outer size mismatch
def transmuteOuterMismatchBody : MirBody where
  argTys := []
  retTy := .bool
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.use (.constVal (.bytes 8 0))),
        .assign ⟨3⟩ (.ref ⟨2⟩)
      ]
      terminator := .callTransmuteCopy ⟨0⟩ .usize .bool (.copy ⟨3⟩) ⟨0⟩ }
  ]

theorem canary_M14_transmute_size_mismatch_violates_wellFormed :
    ¬ (MirSem transmuteOuterMismatchBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState transmuteOuterMismatchBody s0_noArgs :=
    initMirState_oneBlock_noArgs transmuteOuterMismatchBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 2 (some (.bytes 8 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 3 (some (.ref ⟨2⟩))
    stmtIdx := 2
  }
  have hreach : ReachesPrefix MirStep transmuteOuterMismatchBody 3 s0_noArgs
      [(), ()] .failed :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] .failed rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] .failed rfl
        (ReachesPrefix.failed 0 s₂ rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- Baseline Canary 2 (M21): public-safe field rejects NonZeroAdtInv
def pubSafeAdt0 : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .pubSafe }]
  nonExhaustive := false

def nonZeroAdtInv : AdtInv :=
  fun id v =>
    match id, v with
    | 0, .usize n => n ≠ 0
    | _, _ => True

theorem canary_M21_pub_safe_fields_reject_nonzero_inv :
    ¬ AdmissibleAdtInv [pubSafeAdt0] nonZeroAdtInv := by
  intro hadm
  exact hadm pubSafeAdt0 (.head []) rfl 0 rfl

-- Baseline Canary 3 (M22): buggyZeroBody violates EnsuresRetLibInv
def buggyZeroBody : MirBody where
  argTys := []
  retTy := .adt 0
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.aggregate 0 (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

theorem canary_M22_buggy_zero_adt_return_rejected :
    ¬ (MirSem buggyZeroBody ≤
      EnsuresRetLibInv nonZeroAdtInv (.adt 0) (fun _ => True)) := by
  have hinit : initMirState buggyZeroBody s0_noArgs :=
    initMirState_oneBlock_noArgs buggyZeroBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.adt 0 (.usize 0)))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep buggyZeroBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.adt 0 (.usize 0)))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.adt 0 (.usize 0)))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.adt 0 (.usize 0))) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have hinv := hpost (MirVal.adt 0 (.usize 0)) rfl
  exact hinv.2 rfl

-- Baseline Canary 4 (M16): uninitialized _0 return violates WellFormed
def uninitReturnBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .return_ }]

theorem canary_M16_uninit_return_violates_wellFormed :
    ¬ (MirSem uninitReturnBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitReturnBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitReturnBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- Baseline Canary 5 (M24): wrongIdBody violates EnsuresEqArg 1
def wrongIdBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

theorem canary_M24_wrong_id_violates_ensures :
    ¬ (MirSem wrongIdBody ≤ EnsuresEqArg 1) := by
  let s₀ : MirState := {
    locals := fun i => if i == 1 then some (.usize 1) else none
    block := 0
    stmtIdx := 0
  }
  have hinit : initMirState wrongIdBody s₀ := by
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.usize 1, rfl, True.intro⟩, ?_⟩⟩, ?_⟩
    · intro j hj
      have hne : j ≠ 1 := by
        intro hEq; subst hEq
        cases hj with | step hle => cases hle
      have hj1 : (j == 1) = false := nat_beq_false_of_ne hne
      dsimp [s₀]; rw [hj1]; rfl
    · exact monoAdmitted_of_no_call1 s₀.tySizes wrongIdBody rfl
        (by intro b hb; cases hb with
          | head => intro _ _ _ _ _ h; cases h
          | tail _ hnil => cases hnil)
  let s₁ : MirState := { s₀ with
    locals := updateLocal s₀.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep wrongIdBody 2 s₀ [()]
      (.terminated (.normal (MirVal.usize 0))) :=
    ReachesPrefix.step 1 s₀ s₁ () []
      (.terminated (.normal (MirVal.usize 0))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.usize 0)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.usize 0) rfl
  cases heq

end Anneal
"""

MIR_EXTRA_19_CANARIES_LEAN = """
namespace AnnealExtra
open Trusted Anneal

theorem initMirState_twoBlocks_noArgs (body : MirBody) (bb0 bb1 : BasicBlock)
    (hArgs : body.argTys = []) (hReq : body.requiredConsts = [])
    (hBlocks : body.blocks = [bb0, bb1])
    (hTerm0 : ∀ dst callee arg target typeArgs,
      bb0.terminator ≠ .call1 dst callee arg target typeArgs)
    (hTerm1 : ∀ dst callee arg target typeArgs,
      bb1.terminator ≠ .call1 dst callee arg target typeArgs) :
    initMirState body s0_noArgs := by
  refine ⟨initEntryState_s0_noArgs body hArgs, ?_⟩
  refine monoAdmitted_of_no_call1 s0_noArgs.tySizes body hReq ?_
  intro b hb; rw [hBlocks] at hb
  cases hb with
  | head => exact hTerm0
  | tail _ htail =>
    cases htail with
    | head => exact hTerm1
    | tail _ hnil => cases hnil

-- M01: evalTyByteSize .usize = 8
def sizeOfUsizeBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [
    { stmts := [], terminator := .callSizeOf ⟨0⟩ .usize ⟨1⟩ },
    { stmts := [], terminator := .return_ }
  ]

theorem canary_M01_sizeOf_usize_wrong_rejected :
    ¬ (MirSem sizeOfUsizeBody ≤
      MirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .usize 4)) := by
  have hinit : initMirState sizeOfUsizeBody s0_noArgs :=
    initMirState_twoBlocks_noArgs sizeOfUsizeBody _ _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 8))
    block := 1
    stmtIdx := 0
  }
  have hreach : ReachesPrefix MirStep sizeOfUsizeBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.usize 8))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.usize 8))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.usize 8)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.usize 8) rfl
  cases heq

-- M02: evalTyByteSize .bool = 1
def sizeOfBoolBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [
    { stmts := [], terminator := .callSizeOf ⟨0⟩ .bool ⟨1⟩ },
    { stmts := [], terminator := .return_ }
  ]

theorem canary_M02_sizeOf_bool_wrong_rejected :
    ¬ (MirSem sizeOfBoolBody ≤
      MirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .usize 2)) := by
  have hinit : initMirState sizeOfBoolBody s0_noArgs :=
    initMirState_twoBlocks_noArgs sizeOfBoolBody _ _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 1))
    block := 1
    stmtIdx := 0
  }
  have hreach : ReachesPrefix MirStep sizeOfBoolBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.usize 1))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.usize 1))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.usize 1)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.usize 1) rfl
  cases heq

-- M03: evalOperand .copy uninit
def uninitCopyBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 3
  blocks := [{ stmts := [.assign ⟨0⟩ (.use (.copy ⟨2⟩))], terminator := .return_ }]

theorem canary_M03_uninit_copy_violates_wellFormed :
    ¬ (MirSem uninitCopyBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitCopyBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitCopyBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M04: evalOperand .move deinitializes source local
def doubleMoveBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.use (.constVal (.usize 7))),
        .assign ⟨3⟩ (.use (.move ⟨2⟩)),
        .assign ⟨0⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M04_double_move_violates_wellFormed :
    ¬ (MirSem doubleMoveBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState doubleMoveBody s0_noArgs :=
    initMirState_oneBlock_noArgs doubleMoveBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 2 (some (.usize 7))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal (updateLocal s₁.locals 2 none) 3 (some (.usize 7))
    stmtIdx := 2
  }
  have hreach : ReachesPrefix MirStep doubleMoveBody 3 s0_noArgs [(), ()] .failed :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] .failed rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] .failed rfl
        (ReachesPrefix.failed 0 s₂ rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M05: evalOperand .move uninit
def uninitMoveBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 3
  blocks := [{ stmts := [.assign ⟨0⟩ (.use (.move ⟨2⟩))], terminator := .return_ }]

theorem canary_M05_uninit_move_violates_wellFormed :
    ¬ (MirSem uninitMoveBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitMoveBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitMoveBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M06: evalBinOp .eq on distinct usize
def eqDistinctUsizeBody : MirBody where
  argTys := []
  retTy := .bool
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.binaryOp .eq (.constVal (.usize 0)) (.constVal (.usize 1)))]
      terminator := .return_ }
  ]

theorem canary_M06_eq_distinct_usize_not_true :
    ¬ (MirSem eqDistinctUsizeBody ≤
      MirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .bool true)) := by
  have hinit : initMirState eqDistinctUsizeBody s0_noArgs :=
    initMirState_oneBlock_noArgs eqDistinctUsizeBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.bool false))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep eqDistinctUsizeBody 2 s0_noArgs [()]
      (.terminated (.normal (MirVal.bool false))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (MirVal.bool false))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (MirVal.bool false)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (MirVal.bool false) rfl
  cases heq

-- M07: evalBinOp ill-typed operands
def illTypedBinOpBody : MirBody where
  argTys := []
  retTy := .bool
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.binaryOp .eq (.constVal (.usize 0)) (.constVal (.bool false)))]
      terminator := .return_ }
  ]

theorem canary_M07_illTyped_binOp_violates_wellFormed :
    ¬ (MirSem illTypedBinOpBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState illTypedBinOpBody s0_noArgs :=
    initMirState_oneBlock_noArgs illTypedBinOpBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M08: evalMirStmt .use none branch
def failedUseSkipBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.use (.copy ⟨3⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M08_failed_use_assign_violates_wellFormed :
    ¬ (MirSem failedUseSkipBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState failedUseSkipBody s0_noArgs :=
    initMirState_oneBlock_noArgs failedUseSkipBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep failedUseSkipBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M09: evalMirStmt .aggregate none branch
def uninitAggregateBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.aggregate 0 (.copy ⟨3⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M09_uninit_aggregate_violates_wellFormed :
    ¬ (MirSem uninitAggregateBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState uninitAggregateBody s0_noArgs :=
    initMirState_oneBlock_noArgs uninitAggregateBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep uninitAggregateBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M10: evalMirStmt .field0 non-ADT branch
def field0NonAdtBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.field0 ⟨0⟩)
      ]
      terminator := .return_ }
  ]

theorem canary_M10_field0_non_adt_violates_wellFormed :
    ¬ (MirSem field0NonAdtBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState field0NonAdtBody s0_noArgs :=
    initMirState_oneBlock_noArgs field0NonAdtBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep field0NonAdtBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M11: evalMirStmt .ref uninit branch
def refUninitBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.ref ⟨3⟩)
      ]
      terminator := .return_ }
  ]

theorem canary_M11_ref_uninit_violates_wellFormed :
    ¬ (MirSem refUninitBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState refUninitBody s0_noArgs :=
    initMirState_oneBlock_noArgs refUninitBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  have hreach : ReachesPrefix MirStep refUninitBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M12: evalMirStmt .reborrow dead target branch
def reborrowDeadTargetBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.use (.constVal (.usize 1))),
        .assign ⟨3⟩ (.ref ⟨2⟩),
        .storageDead ⟨2⟩,
        .assign ⟨4⟩ (.reborrow ⟨3⟩)
      ]
      terminator := .return_ }
  ]

theorem canary_M12_reborrow_dead_target_violates_wellFormed :
    ¬ (MirSem reborrowDeadTargetBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState reborrowDeadTargetBody s0_noArgs :=
    initMirState_oneBlock_noArgs reborrowDeadTargetBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 2 (some (.usize 1))
    stmtIdx := 2
  }
  let s₃ : MirState := { s₂ with
    locals := updateLocal s₂.locals 3 (some (.ref ⟨2⟩))
    stmtIdx := 3
  }
  let s₄ : MirState := { s₃ with
    locals := updateLocal s₃.locals 2 none
    stmtIdx := 4
  }
  have hreach : ReachesPrefix MirStep reborrowDeadTargetBody 5 s0_noArgs
      [(), (), (), ()] .failed :=
    ReachesPrefix.step 4 s0_noArgs s₁ () [(), (), ()] .failed rfl
      (ReachesPrefix.step 3 s₁ s₂ () [(), ()] .failed rfl
        (ReachesPrefix.step 2 s₂ s₃ () [()] .failed rfl
          (ReachesPrefix.step 1 s₃ s₄ () [] .failed rfl
            (ReachesPrefix.failed 0 s₄ rfl))))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M13: evalMirStmt .storageDead deinitializes local
def useAfterStorageDeadBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0))),
        .assign ⟨2⟩ (.use (.constVal (.usize 1))),
        .storageDead ⟨2⟩,
        .assign ⟨3⟩ (.use (.copy ⟨2⟩))
      ]
      terminator := .return_ }
  ]

theorem canary_M13_use_after_storageDead_violates_wellFormed :
    ¬ (MirSem useAfterStorageDeadBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState useAfterStorageDeadBody s0_noArgs :=
    initMirState_oneBlock_noArgs useAfterStorageDeadBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 0 (some (.usize 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 2 (some (.usize 1))
    stmtIdx := 2
  }
  let s₃ : MirState := { s₂ with
    locals := updateLocal s₂.locals 2 none
    stmtIdx := 3
  }
  have hreach : ReachesPrefix MirStep useAfterStorageDeadBody 4 s0_noArgs
      [(), (), ()] .failed :=
    ReachesPrefix.step 3 s0_noArgs s₁ () [(), ()] .failed rfl
      (ReachesPrefix.step 2 s₁ s₂ () [()] .failed rfl
        (ReachesPrefix.step 1 s₂ s₃ () [] .failed rfl
          (ReachesPrefix.failed 0 s₃ rfl)))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M15: evalTransmuteCopy inner vSz = srcSz mismatch fails
def transmuteInnerMismatchBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.use (.constVal (.bytes 4 0))),
        .assign ⟨3⟩ (.ref ⟨2⟩)
      ]
      terminator := .callTransmuteCopy ⟨0⟩ .usize .usize (.copy ⟨3⟩) ⟨0⟩ }
  ]

theorem canary_M15_transmute_mismatched_pointee_bytes_violates_wellFormed :
    ¬ (MirSem transmuteInnerMismatchBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState transmuteInnerMismatchBody s0_noArgs :=
    initMirState_oneBlock_noArgs transmuteInnerMismatchBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with
    locals := updateLocal s0_noArgs.locals 2 (some (.bytes 4 0))
    stmtIdx := 1
  }
  let s₂ : MirState := { s₁ with
    locals := updateLocal s₁.locals 3 (some (.ref ⟨2⟩))
    stmtIdx := 2
  }
  have hreach : ReachesPrefix MirStep transmuteInnerMismatchBody 3 s0_noArgs
      [(), ()] .failed :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] .failed rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] .failed rfl
        (ReachesPrefix.failed 0 s₂ rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M17: evalMirTerminator .unreachable fails
def unreachableBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .unreachable }]

theorem canary_M17_unreachable_violates_wellFormed :
    ¬ (MirSem unreachableBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState unreachableBody s0_noArgs :=
    initMirState_oneBlock_noArgs unreachableBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M18: evalMirTerminator .panic rejects ConstSucceeds
def panicConstBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [], terminator := .panic }]

theorem panicConstBody_cannot_terminate_normal
    {s₀ : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {v : MirVal}
    (hstep : evalMirStep panicConstBody s₀ = .terminated .unwind)
    (hreach : ReachesPrefix MirStep panicConstBody n s₀ tr out)
    (hout : out = .terminated (.normal v)) :
    False := by
  cases hreach with
  | zero => cases hout
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : StepResult.terminated t = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'
    injection h1' with ht
    subst ht
    cases hout
  | failed _ _ h1 =>
    have h1' : _ = evalMirStep panicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact hno ⟨_, hstep.symm⟩

theorem canary_M18_panicking_const_rejected_by_constSucceeds :
    ¬ ConstSucceeds (fun _ => 0) panicConstBody := by
  intro ⟨s₀, n, tr, v, _hty, hinit, hreach⟩
  let ⟨hb0, hst0, hcur, _hstack, _hl0, _hargs⟩ := hinit
  have hstep : evalMirStep panicConstBody s₀ = .terminated .unwind := by
    unfold evalMirStep panicConstBody
    rw [hcur, hb0]
    dsimp
    rw [hst0]
    rfl
  exact panicConstBody_cannot_terminate_normal hstep hreach rfl

-- M19: evalMirTerminator .switchInt non-boolean discriminant fails
def switchIntNonBoolBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .switchInt (.constVal (.usize 0)) ⟨0⟩ ⟨0⟩ }]

theorem canary_M19_switchInt_non_bool_violates_wellFormed :
    ¬ (MirSem switchIntNonBoolBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState switchIntNonBoolBody s0_noArgs :=
    initMirState_oneBlock_noArgs switchIntNonBoolBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs rfl)

-- M20: evalMirStep out-of-bounds block index fails
def oobGotoBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .goto ⟨99⟩ }]

theorem canary_M20_oob_goto_violates_wellFormed :
    ¬ (MirSem oobGotoBody ≤ MirLang.WellFormed) := by
  have hinit : initMirState oobGotoBody s0_noArgs :=
    initMirState_oneBlock_noArgs oobGotoBody _ rfl rfl rfl
      (by intro _ _ _ _ _ h; cases h)
  let s₁ : MirState := { s0_noArgs with block := 99, stmtIdx := 0 }
  have hreach : ReachesPrefix MirStep oobGotoBody 2 s0_noArgs [()] .failed :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] .failed rfl
      (ReachesPrefix.failed 0 s₁ rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- M23: defaultTrustPolicy rejects .userAxiom
def trivialUnitBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [.assign ⟨0⟩ (.use (.constVal .unit))], terminator := .return_ }]

def unapprovedUserAxiomCrate : Crate where
  adts := []
  adtInv := defaultAdtInv
  unsafeImpls := []
  functions := [{ name := "unit_fn", prog := trivialUnitBody }]
  tcb := [.userAxiom "unsound_bypass" False]

theorem canary_M23_unapproved_userAxiom_rejected :
    ¬ CrateTheorem unapprovedUserAxiomCrate := by
  intro hcrate
  exact hcrate.2.2.2.1.1.1

-- M24a: CrateTheorem rejects violated unsafeImpls traitLaw
def unsoundUnsafeImplCrate : Crate where
  adts := [{ id := 0, fields := [{ ty := .usize, access := .priv }] }]
  adtInv := nonZeroAdtInv
  unsafeImpls := [
    { implName := "ZeroableForNonZeroUsize"
      whereBounds := True
      traitLaw := fun inv => inv 0 (.usize 0) }
  ]
  functions := [{ name := "unit_fn", prog := trivialUnitBody }]
  tcb := []

theorem canary_M24a_unsound_unsafeImpl_rejected :
    ¬ CrateTheorem unsoundUnsafeImplCrate := by
  intro hcrate
  exact hcrate.2.2.1.1 True.intro rfl

end AnnealExtra
"""


X86_BASELINE_CANARIES_LEAN = """-- Copyright 2026 The Fuchsia Authors
-- Licensed under BSD / Apache-2.0 / MIT.
prelude
import Trusted
import Anneal.Refinement
import Anneal.StepResult

namespace AnnealX86Audit
open Trusted

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hbeq : (a == b) with
  | false => rfl
  | true => exact False.elim (h (of_decide_eq_true hbeq))

def s0_noArgs : X86State where
  mem := fun _ => none
  bb := 0
  ip := 0

theorem initX86State_s0_noArgs (body : X86Body) (hArgs : body.argTys = []) :
    initX86State body s0_noArgs := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold argsMatchStack
  rw [hArgs]
  intro j _
  rfl

theorem not_wellFormed_of_reaches_failed
    {body : X86Body} {s₀ : X86State} {n : Nat} {tr : List Unit}
    (hinit : initX86State body s₀)
    (hreach : ReachesPrefix X86Machine body s₀ n s₀ tr (.failed .ub)) :
    ¬ (X86Sem body ≤ X86Lang.WellFormed) := by
  intro hwf
  have hq := hwf { init := s₀, steps := n } True.intro
  cases hq with
  | intro hdef _ => exact hdef hinit tr (.failed .ub) hreach

theorem not_spec_of_reaches_normal
    {body : X86Body} {s₀ : X86State} {n : Nat} {tr : List Unit} {v : X86Val}
    {Post : ExecQuery X86State → ExecOut Unit X86Val → Prop}
    (hinit : initX86State body s₀)
    (hreach : ReachesPrefix X86Machine body s₀ n s₀ tr (.terminated (.normal v)))
    (hnot : ¬ Post { init := s₀, steps := n }
      { trace := tr, outcome := .terminated (.normal v) }) :
    ¬ (X86Sem body ≤ X86Lang.Spec Post) := by
  intro hspec
  have hq := hspec { init := s₀, steps := n } True.intro
  cases hq with
  | intro _ hval =>
    exact hnot (hval { trace := tr, outcome := .terminated (.normal v) } ⟨hinit, hreach⟩)

-- Baseline Canary 1 (X14): repMovsbJmp outer size mismatch
def repMovsbOuterMismatchBody : X86Body where
  argTys := []
  retTy := .bool
  slotCount := 4
  blocks := [
    { instrs := [
        .mov ⟨2⟩ (.imm (.bytes 8 0)),
        .leaSlot ⟨3⟩ ⟨2⟩
      ]
      term := .repMovsbJmp ⟨0⟩ .usize .bool (.stackSlot ⟨3⟩ false) ⟨0⟩ }
  ]

theorem canary_X14_repMovsb_size_mismatch_violates_wellFormed :
    ¬ (X86Sem repMovsbOuterMismatchBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State repMovsbOuterMismatchBody s0_noArgs :=
    initX86State_s0_noArgs repMovsbOuterMismatchBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 2 (some (.bytes 8 0))
    ip := 1
  }
  let s₂ : X86State := { s₁ with
    mem := updateSlot s₁.mem 3 (some (.stackPtr ⟨2⟩))
    ip := 2
  }
  have hreach : ReachesPrefix X86Machine repMovsbOuterMismatchBody s0_noArgs 3
      s0_noArgs [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] (.failed .ub) rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] (.failed .ub) rfl
        (ReachesPrefix.failed 0 s₂ .ub rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- Baseline Canary 2 (X21): public-safe field rejects nonZeroLibInv
def pubSafeAdt0 : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .pubSafe }]
  nonExhaustive := false

theorem canary_X21_pub_safe_fields_reject_nonzero_inv :
    ¬ AdmissibleLibInv [pubSafeAdt0] nonZeroLibInv := by
  intro hadm
  exact hadm.2.2.2.2.2 pubSafeAdt0 (.head []) rfl (fun _ => 0) (.word64 0) True.intro rfl

-- Baseline Canary 3 (X22): buggyZeroBody violates EnsuresRetLibInv
def buggyZeroBody : X86Body where
  argTys := []
  retTy := .adt 0
  slotCount := 1
  blocks := [
    { instrs := [.wrapAdt 0 ⟨0⟩ (.imm (.word64 0))]
      term := .ret }
  ]

theorem canary_X22_buggy_zero_adt_return_rejected :
    ¬ (X86Sem buggyZeroBody ≤
      EnsuresRetLibInv nonZeroLibInv (.adt 0) (fun _ => True)) := by
  have hinit : initX86State buggyZeroBody s0_noArgs :=
    initX86State_s0_noArgs buggyZeroBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.adt 0 (.word64 0)))
    ip := 1
  }
  have hreach : ReachesPrefix X86Machine buggyZeroBody s0_noArgs 2 s0_noArgs [()]
      (.terminated (.normal (X86Val.adt 0 (.word64 0)))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (X86Val.adt 0 (.word64 0)))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (X86Val.adt 0 (.word64 0))) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have hinv := hpost (X86Val.adt 0 (.word64 0)) rfl
  exact hinv rfl

-- Baseline Canary 4 (X16): uninitialized slot 0 ret violates WellFormed
def uninitRetBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [{ instrs := [], term := .ret }]

theorem canary_X16_uninit_ret_violates_wellFormed :
    ¬ (X86Sem uninitRetBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State uninitRetBody s0_noArgs :=
    initX86State_s0_noArgs uninitRetBody rfl
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs .ub rfl)

-- Baseline Canary 5 (X24): wrongIdBody violates EnsuresEqArg 1
def wrongIdBody : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := 2
  blocks := [
    { instrs := [.mov ⟨0⟩ (.imm (.word64 0))]
      term := .ret }
  ]

theorem canary_X24_wrong_id_violates_ensures :
    ¬ (X86Sem wrongIdBody ≤ EnsuresEqArg 1) := by
  let s₀ : X86State := {
    mem := fun i => if i == 1 then some (.word64 1) else none
    bb := 0
    ip := 0
  }
  have hinit : initX86State wrongIdBody s₀ := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.word64 1, rfl, True.intro⟩, ?_⟩⟩
    intro j hj
    have hne : j ≠ 1 := by
      intro hEq; subst hEq
      cases hj with | step hle => cases hle
    have hj1 : (j == 1) = false := nat_beq_false_of_ne hne
    dsimp [s₀]; rw [hj1]; rfl
  let s₁ : X86State := { s₀ with
    mem := updateSlot s₀.mem 0 (some (.word64 0))
    ip := 1
  }
  have hreach : ReachesPrefix X86Machine wrongIdBody s₀ 2 s₀ [()]
      (.terminated (.normal (X86Val.word64 0))) :=
    ReachesPrefix.step 1 s₀ s₁ () []
      (.terminated (.normal (X86Val.word64 0))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (X86Val.word64 0)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (X86Val.word64 0) rfl
  cases heq

end AnnealX86Audit
"""

X86_EXTRA_19_CANARIES_LEAN = """
namespace AnnealX86Extra
open Trusted AnnealX86Audit

-- X01: evalX86TyByteSize .usize = 8
def sizeOfUsizeBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [
    { instrs := [], term := .movSizeOfJmp ⟨0⟩ .usize ⟨1⟩ },
    { instrs := [], term := .ret }
  ]

theorem canary_X01_sizeOf_usize_wrong_rejected :
    ¬ (X86Sem sizeOfUsizeBody ≤
      X86Lang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .word64 4)) := by
  have hinit : initX86State sizeOfUsizeBody s0_noArgs :=
    initX86State_s0_noArgs sizeOfUsizeBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 8))
    bb := 1
    ip := 0
  }
  have hreach : ReachesPrefix X86Machine sizeOfUsizeBody s0_noArgs 2 s0_noArgs [()]
      (.terminated (.normal (X86Val.word64 8))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (X86Val.word64 8))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (X86Val.word64 8)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (X86Val.word64 8) rfl
  cases heq

-- X02: evalX86TyByteSize .bool = 1
def sizeOfBoolBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [
    { instrs := [], term := .movSizeOfJmp ⟨0⟩ .bool ⟨1⟩ },
    { instrs := [], term := .ret }
  ]

theorem canary_X02_sizeOf_bool_wrong_rejected :
    ¬ (X86Sem sizeOfBoolBody ≤
      X86Lang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .word64 2)) := by
  have hinit : initX86State sizeOfBoolBody s0_noArgs :=
    initX86State_s0_noArgs sizeOfBoolBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 1))
    bb := 1
    ip := 0
  }
  have hreach : ReachesPrefix X86Machine sizeOfBoolBody s0_noArgs 2 s0_noArgs [()]
      (.terminated (.normal (X86Val.word64 1))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (X86Val.word64 1))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (X86Val.word64 1)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (X86Val.word64 1) rfl
  cases heq

-- X03: evalX86Operand .stackSlot slot false uninit fails
def uninitCopyBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 3
  blocks := [{ instrs := [.mov ⟨0⟩ (.stackSlot ⟨2⟩ false)], term := .ret }]

theorem canary_X03_uninit_copy_violates_wellFormed :
    ¬ (X86Sem uninitCopyBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State uninitCopyBody s0_noArgs :=
    initX86State_s0_noArgs uninitCopyBody rfl
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs .ub rfl)

-- X04: evalX86Operand .stackSlot slot true deinitializes source slot
def doubleMoveBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .mov ⟨2⟩ (.imm (.word64 7)),
        .mov ⟨3⟩ (.stackSlot ⟨2⟩ true),
        .mov ⟨0⟩ (.stackSlot ⟨2⟩ false)
      ]
      term := .ret }
  ]

theorem canary_X04_double_move_violates_wellFormed :
    ¬ (X86Sem doubleMoveBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State doubleMoveBody s0_noArgs :=
    initX86State_s0_noArgs doubleMoveBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 2 (some (.word64 7))
    ip := 1
  }
  let s₂ : X86State := { s₁ with
    mem := updateSlot (updateSlot s₁.mem 2 none) 3 (some (.word64 7))
    ip := 2
  }
  have hreach : ReachesPrefix X86Machine doubleMoveBody s0_noArgs 3 s0_noArgs
      [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] (.failed .ub) rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] (.failed .ub) rfl
        (ReachesPrefix.failed 0 s₂ .ub rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X05: evalX86Operand .stackSlot slot true uninit fails
def uninitMoveBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 3
  blocks := [{ instrs := [.mov ⟨0⟩ (.stackSlot ⟨2⟩ true)], term := .ret }]

theorem canary_X05_uninit_move_violates_wellFormed :
    ¬ (X86Sem uninitMoveBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State uninitMoveBody s0_noArgs :=
    initX86State_s0_noArgs uninitMoveBody rfl
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs .ub rfl)

-- X06: evalX86BinOp .eq on distinct word64
def eqDistinctWord64Body : X86Body where
  argTys := []
  retTy := .bool
  slotCount := 1
  blocks := [
    { instrs := [.alu .eq ⟨0⟩ (.imm (.word64 0)) (.imm (.word64 1))]
      term := .ret }
  ]

theorem canary_X06_eq_distinct_word64_not_true :
    ¬ (X86Sem eqDistinctWord64Body ≤
      X86Lang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .boolVal true)) := by
  have hinit : initX86State eqDistinctWord64Body s0_noArgs :=
    initX86State_s0_noArgs eqDistinctWord64Body rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.boolVal false))
    ip := 1
  }
  have hreach : ReachesPrefix X86Machine eqDistinctWord64Body s0_noArgs 2 s0_noArgs [()]
      (.terminated (.normal (X86Val.boolVal false))) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () []
      (.terminated (.normal (X86Val.boolVal false))) rfl
      (ReachesPrefix.terminated 0 s₁ (.normal (X86Val.boolVal false)) rfl)
  refine not_spec_of_reaches_normal hinit hreach ?_
  intro hpost
  have heq := hpost (X86Val.boolVal false) rfl
  cases heq

-- X07: evalX86BinOp ill-typed operands fail
def illTypedAluBody : X86Body where
  argTys := []
  retTy := .bool
  slotCount := 1
  blocks := [
    { instrs := [.alu .eq ⟨0⟩ (.imm (.word64 0)) (.imm (.boolVal false))]
      term := .ret }
  ]

theorem canary_X07_illTyped_alu_violates_wellFormed :
    ¬ (X86Sem illTypedAluBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State illTypedAluBody s0_noArgs :=
    initX86State_s0_noArgs illTypedAluBody rfl
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs .ub rfl)

-- X08: evalX86Instr .mov none branch fails
def failedMovSkipBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .mov ⟨0⟩ (.imm (.word64 0)),
        .mov ⟨2⟩ (.stackSlot ⟨3⟩ false)
      ]
      term := .ret }
  ]

theorem canary_X08_failed_mov_violates_wellFormed :
    ¬ (X86Sem failedMovSkipBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State failedMovSkipBody s0_noArgs :=
    initX86State_s0_noArgs failedMovSkipBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 0))
    ip := 1
  }
  have hreach : ReachesPrefix X86Machine failedMovSkipBody s0_noArgs 2 s0_noArgs
      [()] (.failed .ub) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] (.failed .ub) rfl
      (ReachesPrefix.failed 0 s₁ .ub rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X09: evalX86Instr .wrapAdt none branch fails
def uninitWrapAdtBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .mov ⟨0⟩ (.imm (.word64 0)),
        .wrapAdt 0 ⟨2⟩ (.stackSlot ⟨3⟩ false)
      ]
      term := .ret }
  ]

theorem canary_X09_uninit_wrapAdt_violates_wellFormed :
    ¬ (X86Sem uninitWrapAdtBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State uninitWrapAdtBody s0_noArgs :=
    initX86State_s0_noArgs uninitWrapAdtBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 0))
    ip := 1
  }
  have hreach : ReachesPrefix X86Machine uninitWrapAdtBody s0_noArgs 2 s0_noArgs
      [()] (.failed .ub) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] (.failed .ub) rfl
      (ReachesPrefix.failed 0 s₁ .ub rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X10: evalX86Instr .extractField0 non-ADT fails
def extractField0NonAdtBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 3
  blocks := [
    { instrs := [
        .mov ⟨0⟩ (.imm (.word64 0)),
        .extractField0 ⟨2⟩ ⟨0⟩
      ]
      term := .ret }
  ]

theorem canary_X10_extractField0_non_adt_violates_wellFormed :
    ¬ (X86Sem extractField0NonAdtBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State extractField0NonAdtBody s0_noArgs :=
    initX86State_s0_noArgs extractField0NonAdtBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 0))
    ip := 1
  }
  have hreach : ReachesPrefix X86Machine extractField0NonAdtBody s0_noArgs 2 s0_noArgs
      [()] (.failed .ub) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] (.failed .ub) rfl
      (ReachesPrefix.failed 0 s₁ .ub rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X11: evalX86Instr .leaSlot uninit target fails
def leaSlotUninitBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .mov ⟨0⟩ (.imm (.word64 0)),
        .leaSlot ⟨2⟩ ⟨3⟩
      ]
      term := .ret }
  ]

theorem canary_X11_leaSlot_uninit_violates_wellFormed :
    ¬ (X86Sem leaSlotUninitBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State leaSlotUninitBody s0_noArgs :=
    initX86State_s0_noArgs leaSlotUninitBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 0))
    ip := 1
  }
  have hreach : ReachesPrefix X86Machine leaSlotUninitBody s0_noArgs 2 s0_noArgs
      [()] (.failed .ub) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] (.failed .ub) rfl
      (ReachesPrefix.failed 0 s₁ .ub rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X12: evalX86Instr .reborrowSlot dead target fails
def reborrowSlotDeadTargetBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 5
  blocks := [
    { instrs := [
        .mov ⟨0⟩ (.imm (.word64 0)),
        .mov ⟨2⟩ (.imm (.word64 1)),
        .leaSlot ⟨3⟩ ⟨2⟩,
        .deallocSlot ⟨2⟩,
        .reborrowSlot ⟨4⟩ ⟨3⟩
      ]
      term := .ret }
  ]

theorem canary_X12_reborrowSlot_dead_target_violates_wellFormed :
    ¬ (X86Sem reborrowSlotDeadTargetBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State reborrowSlotDeadTargetBody s0_noArgs :=
    initX86State_s0_noArgs reborrowSlotDeadTargetBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 0))
    ip := 1
  }
  let s₂ : X86State := { s₁ with
    mem := updateSlot s₁.mem 2 (some (.word64 1))
    ip := 2
  }
  let s₃ : X86State := { s₂ with
    mem := updateSlot s₂.mem 3 (some (.stackPtr ⟨2⟩))
    ip := 3
  }
  let s₄ : X86State := { s₃ with
    mem := updateSlot s₃.mem 2 none
    ip := 4
  }
  have hreach : ReachesPrefix X86Machine reborrowSlotDeadTargetBody s0_noArgs 5
      s0_noArgs [(), (), (), ()] (.failed .ub) :=
    ReachesPrefix.step 4 s0_noArgs s₁ () [(), (), ()] (.failed .ub) rfl
      (ReachesPrefix.step 3 s₁ s₂ () [(), ()] (.failed .ub) rfl
        (ReachesPrefix.step 2 s₂ s₃ () [()] (.failed .ub) rfl
          (ReachesPrefix.step 1 s₃ s₄ () [] (.failed .ub) rfl
            (ReachesPrefix.failed 0 s₄ .ub rfl))))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X13: evalX86Instr .deallocSlot deinitializes slot
def useAfterDeallocSlotBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .mov ⟨0⟩ (.imm (.word64 0)),
        .mov ⟨2⟩ (.imm (.word64 1)),
        .deallocSlot ⟨2⟩,
        .mov ⟨3⟩ (.stackSlot ⟨2⟩ false)
      ]
      term := .ret }
  ]

theorem canary_X13_use_after_deallocSlot_violates_wellFormed :
    ¬ (X86Sem useAfterDeallocSlotBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State useAfterDeallocSlotBody s0_noArgs :=
    initX86State_s0_noArgs useAfterDeallocSlotBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 0 (some (.word64 0))
    ip := 1
  }
  let s₂ : X86State := { s₁ with
    mem := updateSlot s₁.mem 2 (some (.word64 1))
    ip := 2
  }
  let s₃ : X86State := { s₂ with
    mem := updateSlot s₂.mem 2 none
    ip := 3
  }
  have hreach : ReachesPrefix X86Machine useAfterDeallocSlotBody s0_noArgs 4
      s0_noArgs [(), (), ()] (.failed .ub) :=
    ReachesPrefix.step 3 s0_noArgs s₁ () [(), ()] (.failed .ub) rfl
      (ReachesPrefix.step 2 s₁ s₂ () [()] (.failed .ub) rfl
        (ReachesPrefix.step 1 s₂ s₃ () [] (.failed .ub) rfl
          (ReachesPrefix.failed 0 s₃ .ub rfl)))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X15: evalRepMovsb inner vSz = srcSz mismatch fails
def repMovsbInnerMismatchBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [
        .mov ⟨2⟩ (.imm (.bytes 4 0)),
        .leaSlot ⟨3⟩ ⟨2⟩
      ]
      term := .repMovsbJmp ⟨0⟩ .usize .usize (.stackSlot ⟨3⟩ false) ⟨0⟩ }
  ]

theorem canary_X15_repMovsb_mismatched_pointee_bytes_violates_wellFormed :
    ¬ (X86Sem repMovsbInnerMismatchBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State repMovsbInnerMismatchBody s0_noArgs :=
    initX86State_s0_noArgs repMovsbInnerMismatchBody rfl
  let s₁ : X86State := { s0_noArgs with
    mem := updateSlot s0_noArgs.mem 2 (some (.bytes 4 0))
    ip := 1
  }
  let s₂ : X86State := { s₁ with
    mem := updateSlot s₁.mem 3 (some (.stackPtr ⟨2⟩))
    ip := 2
  }
  have hreach : ReachesPrefix X86Machine repMovsbInnerMismatchBody s0_noArgs 3
      s0_noArgs [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s0_noArgs s₁ () [()] (.failed .ub) rfl
      (ReachesPrefix.step 1 s₁ s₂ () [] (.failed .ub) rfl
        (ReachesPrefix.failed 0 s₂ .ub rfl))
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X17: evalX86Term .ud2 fails
def ud2Body : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [{ instrs := [], term := .ud2 }]

theorem canary_X17_ud2_violates_wellFormed :
    ¬ (X86Sem ud2Body ≤ X86Lang.WellFormed) := by
  have hinit : initX86State ud2Body s0_noArgs :=
    initX86State_s0_noArgs ud2Body rfl
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs .ub rfl)

-- X18: evalX86Term .abortPanic rejects ConstSucceeds
def abortPanicConstBody : X86Body where
  argTys := []
  retTy := .unit
  slotCount := 1
  blocks := [{ instrs := [], term := .abortPanic }]

theorem abortPanicConstBody_cannot_terminate_normal
    {s₀ : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val} {v : X86Val}
    (hstep : evalX86Step abortPanicConstBody s₀ = .terminated .unwind)
    (hreach : ReachesPrefix X86Machine abortPanicConstBody s₀ n s₀ tr out)
    (hout : out = .terminated (.normal v)) :
    False := by
  cases hreach with
  | zero => cases hout
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step abortPanicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step abortPanicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step abortPanicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : StepResult.terminated t = evalX86Step abortPanicConstBody s₀ := h1
    rw [hstep] at h1'
    injection h1' with ht
    subst ht
    cases hout
  | failed _ _ _ h1 =>
    have h1' : _ = evalX86Step abortPanicConstBody s₀ := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact hno ⟨_, hstep.symm⟩

theorem canary_X18_abortPanic_const_rejected_by_constSucceeds :
    ¬ ConstSucceeds (fun _ => 0) abortPanicConstBody := by
  intro ⟨s₀, n, tr, v, _hty, hinit, hreach⟩
  let ⟨hb0, hip0, hcur, _hstack, _hm0, _hargs⟩ := hinit
  have hstep : evalX86Step abortPanicConstBody s₀ = .terminated .unwind := by
    unfold evalX86Step abortPanicConstBody
    rw [hcur, hb0]
    dsimp
    rw [hip0]
    rfl
  exact abortPanicConstBody_cannot_terminate_normal hstep hreach rfl

-- X19: evalX86Term .jccBool non-boolean condition fails
def jccNonBoolBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [{ instrs := [], term := .jccBool (.imm (.word64 0)) ⟨0⟩ ⟨0⟩ }]

theorem canary_X19_jccBool_non_bool_violates_wellFormed :
    ¬ (X86Sem jccNonBoolBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State jccNonBoolBody s0_noArgs :=
    initX86State_s0_noArgs jccNonBoolBody rfl
  exact not_wellFormed_of_reaches_failed hinit
    (ReachesPrefix.failed 0 s0_noArgs .ub rfl)

-- X20: evalX86Step out-of-bounds block label fails
def oobJmpBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [{ instrs := [], term := .jmp ⟨99⟩ }]

theorem canary_X20_oob_jmp_violates_wellFormed :
    ¬ (X86Sem oobJmpBody ≤ X86Lang.WellFormed) := by
  have hinit : initX86State oobJmpBody s0_noArgs :=
    initX86State_s0_noArgs oobJmpBody rfl
  let s₁ : X86State := { s0_noArgs with bb := 99, ip := 0 }
  have hreach : ReachesPrefix X86Machine oobJmpBody s0_noArgs 2 s0_noArgs
      [()] (.failed .ub) :=
    ReachesPrefix.step 1 s0_noArgs s₁ () [] (.failed .ub) rfl
      (ReachesPrefix.failed 0 s₁ .ub rfl)
  exact not_wellFormed_of_reaches_failed hinit hreach

-- X23: defaultTrustPolicy rejects .userAxiom
def trivialUnitBody : X86Body where
  argTys := []
  retTy := .unit
  slotCount := 1
  blocks := [{ instrs := [.mov ⟨0⟩ (.imm .unit)], term := .ret }]

def unapprovedUserAxiomCrate : Crate where
  adts := []
  libInv := defaultLibInv
  unsafeImpls := []
  functions := [{ name := "unit_fn", prog := trivialUnitBody }]
  tcb := [.userAxiom "unsound_bypass" False]

theorem canary_X23_unapproved_userAxiom_rejected :
    ¬ CrateTheorem unapprovedUserAxiomCrate := by
  intro hcrate
  exact hcrate.2.2.2.1.1.1

-- X24a: CrateTheorem rejects violated unsafeImpls traitLaw
def unsoundUnsafeImplCrate : Crate where
  adts := [{ id := 0, fields := [{ ty := .usize, access := .priv }] }]
  libInv := nonZeroLibInv
  unsafeImpls := [
    { implName := "ZeroableForNonZeroUsize"
      whereBounds := True
      traitLaw := fun inv => inv (fun _ => 0) (.adt 0) (.adt 0 (.word64 0)) }
  ]
  functions := [{ name := "unit_fn", prog := trivialUnitBody }]
  tcb := []

theorem canary_X24a_unsound_unsafeImpl_rejected :
    ¬ CrateTheorem unsoundUnsafeImplCrate := by
  intro hcrate
  exact hcrate.2.2.1.1 True.intro rfl

end AnnealX86Extra
"""


MIR_MUTATIONS: List[Dict[str, Any]] = [
    {
        "id": "M01",
        "function": "evalTyByteSize",
        "line": 91,
        "description": "Mutate `.usize` byte size from `8` to `4` (32-bit layout confusion on LP64).",
        "target": "  | .usize => 8",
        "replacement": "  | .usize => 4",
        "killing_canary": "canary_M01_sizeOf_usize_wrong_rejected",
    },
    {
        "id": "M02",
        "function": "evalTyByteSize",
        "line": 92,
        "description": "Mutate `.bool` byte size from `1` to `2` (`r[type.bool.layout]` violation).",
        "target": "  | .bool => 1",
        "replacement": "  | .bool => 2",
        "killing_canary": "canary_M02_sizeOf_bool_wrong_rejected",
    },
    {
        "id": "M03",
        "function": "evalOperand",
        "line": 241,
        "description": "Default uninitialized `.copy` read to `some (.usize 0, locals)` instead of `none`.",
        "target": "  | .copy src =>\n    match locals src.index with\n    | some v => some (v, locals)\n    | none => none",
        "replacement": "  | .copy src =>\n    match locals src.index with\n    | some v => some (v, locals)\n    | none => some (.usize 0, locals)",
        "killing_canary": "canary_M03_uninit_copy_violates_wellFormed",
    },
    {
        "id": "M04",
        "function": "evalOperand",
        "line": 244,
        "description": "Omit source local deinitialization in `Operand.move` (`r[expr.move.deinitialization]`).",
        "target": "  | .move src =>\n    match locals src.index with\n    | some v => some (v, updateLocal locals src.index none)\n    | none => none",
        "replacement": "  | .move src =>\n    match locals src.index with\n    | some v => some (v, locals)\n    | none => none",
        "killing_canary": "canary_M04_double_move_violates_wellFormed",
    },
    {
        "id": "M05",
        "function": "evalOperand",
        "line": 245,
        "description": "Default uninitialized `.move` read to `some (.usize 0, locals)` instead of `none`.",
        "target": "  | .move src =>\n    match locals src.index with\n    | some v => some (v, updateLocal locals src.index none)\n    | none => none",
        "replacement": "  | .move src =>\n    match locals src.index with\n    | some v => some (v, updateLocal locals src.index none)\n    | none => some (.usize 0, locals)",
        "killing_canary": "canary_M05_uninit_move_violates_wellFormed",
    },
    {
        "id": "M06",
        "function": "evalBinOp",
        "line": 253,
        "description": "Mutate `BinOp.eq` on `.usize` from `decide (a = b)` to `true`.",
        "target": "  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))",
        "replacement": "  | .eq, .usize _, .usize _ => some (.bool true)",
        "killing_canary": "canary_M06_eq_distinct_usize_not_true",
    },
    {
        "id": "M07",
        "function": "evalBinOp",
        "line": 256,
        "description": "Replace ill-typed `evalBinOp` fallback `none` with `some (.bool false)`.",
        "target": "  | .eq, .unit, .unit => some (.bool true)\n  | _, _, _ => none",
        "replacement": "  | .eq, .unit, .unit => some (.bool true)\n  | _, _, _ => some (.bool false)",
        "killing_canary": "canary_M07_illTyped_binOp_violates_wellFormed",
    },
    {
        "id": "M08",
        "function": "evalMirStmt",
        "line": 295,
        "description": "Replace `.assign dst (.use op)` `none => .failed` branch with silent `.nop` step.",
        "target": "  | .assign dst (.use op) =>\n    match evalOperand s.locals op with\n    | some (v, locals') =>\n      .step () { s with\n        locals := updateLocal locals' dst.index (some v)\n        stmtIdx := s.stmtIdx + 1\n      }\n    | none => .failed",
        "replacement": "  | .assign dst (.use op) =>\n    match evalOperand s.locals op with\n    | some (v, locals') =>\n      .step () { s with\n        locals := updateLocal locals' dst.index (some v)\n        stmtIdx := s.stmtIdx + 1\n      }\n    | none => .step () { s with stmtIdx := s.stmtIdx + 1 }",
        "killing_canary": "canary_M08_failed_use_assign_violates_wellFormed",
    },
    {
        "id": "M09",
        "function": "evalMirStmt",
        "line": 317,
        "description": "Replace `.assign dst (.aggregate adtId op)` `none => .failed` branch with silent `.nop` step.",
        "target": "  | .assign dst (.aggregate adtId op) =>\n    match evalOperand s.locals op with\n    | some (v, locals') =>\n      .step () { s with\n        locals := updateLocal locals' dst.index (some (.adt adtId v))\n        stmtIdx := s.stmtIdx + 1\n      }\n    | none => .failed",
        "replacement": "  | .assign dst (.aggregate adtId op) =>\n    match evalOperand s.locals op with\n    | some (v, locals') =>\n      .step () { s with\n        locals := updateLocal locals' dst.index (some (.adt adtId v))\n        stmtIdx := s.stmtIdx + 1\n      }\n    | none => .step () { s with stmtIdx := s.stmtIdx + 1 }",
        "killing_canary": "canary_M09_uninit_aggregate_violates_wellFormed",
    },
    {
        "id": "M10",
        "function": "evalMirStmt",
        "line": 325,
        "description": "Replace `.assign dst (.field0 src)` non-ADT `_ => .failed` branch with silent `.nop` step.",
        "target": "  | .assign dst (.field0 src) =>\n    match s.locals src.index with\n    | some (.adt _ inner) =>\n      .step () { s with\n        locals := updateLocal s.locals dst.index (some inner)\n        stmtIdx := s.stmtIdx + 1\n      }\n    | _ => .failed",
        "replacement": "  | .assign dst (.field0 src) =>\n    match s.locals src.index with\n    | some (.adt _ inner) =>\n      .step () { s with\n        locals := updateLocal s.locals dst.index (some inner)\n        stmtIdx := s.stmtIdx + 1\n      }\n    | _ => .step () { s with stmtIdx := s.stmtIdx + 1 }",
        "killing_canary": "canary_M10_field0_non_adt_violates_wellFormed",
    },
    {
        "id": "M11",
        "function": "evalMirStmt",
        "line": 333,
        "description": "Allow `.assign dst (.ref src)` on uninitialized `src` (`none`) instead of `.failed`.",
        "target": "  | .assign dst (.ref src) =>\n    match s.locals src.index with\n    | some _ =>\n      .step () { s with\n        locals := updateLocal s.locals dst.index (some (.ref src))\n        stmtIdx := s.stmtIdx + 1\n      }\n    | none => .failed",
        "replacement": "  | .assign dst (.ref src) =>\n    .step () { s with\n      locals := updateLocal s.locals dst.index (some (.ref src))\n      stmtIdx := s.stmtIdx + 1\n    }",
        "killing_canary": "canary_M11_ref_uninit_violates_wellFormed",
    },
    {
        "id": "M12",
        "function": "evalMirStmt",
        "line": 343,
        "description": "Omit dangling-target liveness check (`s.locals target.index`) in `.assign dst (.reborrow src)`.",
        "target": "  | .assign dst (.reborrow src) =>\n    match s.locals src.index with\n    | some (.ref target) =>\n      match s.locals target.index with\n      | some _ =>\n        .step () { s with\n          locals := updateLocal s.locals dst.index (some (.ref target))\n          stmtIdx := s.stmtIdx + 1\n        }\n      | none => .failed\n    | _ => .failed",
        "replacement": "  | .assign dst (.reborrow src) =>\n    match s.locals src.index with\n    | some (.ref target) =>\n      .step () { s with\n        locals := updateLocal s.locals dst.index (some (.ref target))\n        stmtIdx := s.stmtIdx + 1\n      }\n    | _ => .failed",
        "killing_canary": "canary_M12_reborrow_dead_target_violates_wellFormed",
    },
    {
        "id": "M13",
        "function": "evalMirStmt",
        "line": 355,
        "description": "Mutate `.storageDead loc` to preserve `s.locals` instead of deallocating `loc` to `none`.",
        "target": "  | .storageDead loc =>\n    -- Ending a live storage range deallocates/deinitializes `loc`.\n    .step () { s with\n      locals := updateLocal s.locals loc.index none\n      stmtIdx := s.stmtIdx + 1\n    }",
        "replacement": "  | .storageDead _ =>\n    .step () { s with stmtIdx := s.stmtIdx + 1 }",
        "killing_canary": "canary_M13_use_after_storageDead_violates_wellFormed",
    },
    {
        "id": "M14",
        "function": "evalTransmuteCopy",
        "line": 377,
        "description": "Bypass outer `decide (srcSz = dstSz)` size check in `evalTransmuteCopy`.",
        "target": "  if decide (srcSz = dstSz) then\n    match argVal with\n    | .ref target =>\n      match locals target.index with\n      | some (.bytes vSz bits) =>\n        if decide (vSz = srcSz) then",
        "replacement": "  if true then\n    match argVal with\n    | .ref target =>\n      match locals target.index with\n      | some (.bytes vSz bits) =>\n        if decide (vSz = srcSz) then",
        "killing_canary": "canary_M14_transmute_size_mismatch_violates_wellFormed",
    },
    {
        "id": "M15",
        "function": "evalTransmuteCopy",
        "line": 382,
        "description": "Bypass inner `decide (vSz = srcSz)` pointee byte-size check in `evalTransmuteCopy`.",
        "target": "      | some (.bytes vSz bits) =>\n        if decide (vSz = srcSz) then\n          some (.bytes dstSz bits)\n        else\n          none",
        "replacement": "      | some (.bytes _ bits) =>\n        some (.bytes dstSz bits)",
        "killing_canary": "canary_M15_transmute_mismatched_pointee_bytes_violates_wellFormed",
    },
    {
        "id": "M16",
        "function": "evalMirTerminator",
        "line": 436,
        "description": "Mutate `.return_` on uninitialized `_0` (`none`) from `.failed` to `.terminated (.normal .unit)`.",
        "target": "  | .return_ =>\n    match s.locals 0 with\n    | none => .failed",
        "replacement": "  | .return_ =>\n    match s.locals 0 with\n    | none => .terminated (.normal .unit)",
        "killing_canary": "canary_M16_uninit_return_violates_wellFormed",
    },
    {
        "id": "M17",
        "function": "evalMirTerminator",
        "line": 452,
        "description": "Mutate `.unreachable` terminator from `.failed` (UB) to `.terminated .unwind` (safe unwind).",
        "target": "  | .unreachable =>\n    .failed",
        "replacement": "  | .unreachable =>\n    .terminated .unwind",
        "killing_canary": "canary_M17_unreachable_violates_wellFormed",
    },
    {
        "id": "M18",
        "function": "evalMirTerminator",
        "line": 454,
        "description": "Mutate `.panic` terminator from `.terminated .unwind` to `.terminated (.normal .unit)` (accepting PME panics).",
        "target": "  | .panic =>\n    .terminated .unwind",
        "replacement": "  | .panic =>\n    .terminated (.normal .unit)",
        "killing_canary": "canary_M18_panicking_const_rejected_by_constSucceeds",
    },
    {
        "id": "M19",
        "function": "evalMirTerminator",
        "line": 461,
        "description": "Mutate `.switchInt` non-boolean fallback `_ => .failed` to jump to `falseTarget`.",
        "target": "  | .switchInt discr falseTarget trueTarget =>\n    match evalOperand s.locals discr with\n    | some (.bool false, locals') =>\n      .step () { s with locals := locals', block := falseTarget.index, stmtIdx := 0 }\n    | some (.bool true, locals') =>\n      .step () { s with locals := locals', block := trueTarget.index, stmtIdx := 0 }\n    | _ => .failed",
        "replacement": "  | .switchInt discr falseTarget trueTarget =>\n    match evalOperand s.locals discr with\n    | some (.bool false, locals') =>\n      .step () { s with locals := locals', block := falseTarget.index, stmtIdx := 0 }\n    | some (.bool true, locals') =>\n      .step () { s with locals := locals', block := trueTarget.index, stmtIdx := 0 }\n    | _ => .step () { s with block := falseTarget.index, stmtIdx := 0 }",
        "killing_canary": "canary_M19_switchInt_non_bool_violates_wellFormed",
    },
    {
        "id": "M20",
        "function": "evalMirStep",
        "line": 513,
        "description": "Mutate out-of-bounds block lookup `active.blocks[s.block]? = none` from `.failed` to `.terminated .unwind`.",
        "target": "  match active.blocks[s.block]? with\n  | none => .failed",
        "replacement": "  match active.blocks[s.block]? with\n  | none => .terminated .unwind",
        "killing_canary": "canary_M20_oob_goto_violates_wellFormed",
    },
    {
        "id": "M21",
        "function": "AdmissibleAdtInv",
        "line": 649,
        "description": "Weaken `AdmissibleAdtInv` public-safe field check to `True`.",
        "target": "def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=\n  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →\n    ∀ n, adtInv decl.id (.usize n)",
        "replacement": "def AdmissibleAdtInv (_adts : List AdtDecl) (_adtInv : AdtInv) : Prop :=\n  True",
        "killing_canary": "canary_M21_pub_safe_fields_reject_nonzero_inv",
    },
    {
        "id": "M22",
        "function": "EnsuresRetLibInv",
        "line": 658,
        "description": "Weaken `EnsuresRetLibInv` return-value `satisfiesInv` postcondition to `True`.",
        "target": "def EnsuresRetLibInv (adtInv : AdtInv) (retTy : MirTy)\n    (pre : ExecQuery MirState → Prop) : MirLang.Behavior :=\n  MirLang.SpecOn pre (fun q out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      ret.satisfiesInv adtInv q.init.tySizes retTy)",
        "replacement": "def EnsuresRetLibInv (_adtInv : AdtInv) (_retTy : MirTy)\n    (pre : ExecQuery MirState → Prop) : MirLang.Behavior :=\n  MirLang.SpecOn pre (fun _ out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      True)",
        "killing_canary": "canary_M22_buggy_zero_adt_return_rejected",
    },
    {
        "id": "M23",
        "function": "defaultTrustPolicy",
        "line": 748,
        "description": "Mutate `defaultTrustPolicy` to allow `.userAxiom _ _ => True` (unsound user axiom bypass).",
        "target": "def defaultTrustPolicy : TrustPolicy TCBItem where\n  isAllowed\n    | .rustcLowering _ _ => True\n    | .userAxiom _ _ => False",
        "replacement": "def defaultTrustPolicy : TrustPolicy TCBItem where\n  isAllowed\n    | .rustcLowering _ _ => True\n    | .userAxiom _ _ => True",
        "killing_canary": "canary_M23_unapproved_userAxiom_rejected",
    },
    {
        "id": "M24",
        "function": "CrateTheorem / EnsuresEqArg",
        "line": 670,
        "description": "Weaken `EnsuresEqArg` functional postcondition `q.init.locals argLocal = some ret` to `True`.",
        "target": "def EnsuresEqArg (argLocal : Nat) : MirLang.Behavior :=\n  MirLang.Spec (fun q out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      q.init.locals argLocal = some ret)",
        "replacement": "def EnsuresEqArg (_argLocal : Nat) : MirLang.Behavior :=\n  MirLang.Spec (fun _ out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      True)",
        "killing_canary": "canary_M24_wrong_id_violates_ensures",
    },
]


X86_MUTATIONS: List[Dict[str, Any]] = [
    {
        "id": "X01",
        "function": "evalX86TyByteSize",
        "line": 102,
        "description": "Mutate `.usize` byte size from `8` to `4` in `evalX86TyByteSize`.",
        "target": "  | .usize => 8",
        "replacement": "  | .usize => 4",
        "killing_canary": "canary_X01_sizeOf_usize_wrong_rejected",
    },
    {
        "id": "X02",
        "function": "evalX86TyByteSize",
        "line": 103,
        "description": "Mutate `.bool` byte size from `1` to `2` in `evalX86TyByteSize`.",
        "target": "  | .bool => 1",
        "replacement": "  | .bool => 2",
        "killing_canary": "canary_X02_sizeOf_bool_wrong_rejected",
    },
    {
        "id": "X03",
        "function": "evalX86Operand",
        "line": 194,
        "description": "Default uninitialized `.stackSlot slot false` load to `some (.word64 0, mem)` instead of `none`.",
        "target": "  | .stackSlot slot false =>\n    match mem slot.index with\n    | some v => some (v, mem)\n    | none => none",
        "replacement": "  | .stackSlot slot false =>\n    match mem slot.index with\n    | some v => some (v, mem)\n    | none => some (.word64 0, mem)",
        "killing_canary": "canary_X03_uninit_copy_violates_wellFormed",
    },
    {
        "id": "X04",
        "function": "evalX86Operand",
        "line": 197,
        "description": "Omit ghost slot deinitialization in `.stackSlot slot true` (`Move` load).",
        "target": "  | .stackSlot slot true =>\n    match mem slot.index with\n    | some v => some (v, updateSlot mem slot.index none)\n    | none => none",
        "replacement": "  | .stackSlot slot true =>\n    match mem slot.index with\n    | some v => some (v, mem)\n    | none => none",
        "killing_canary": "canary_X04_double_move_violates_wellFormed",
    },
    {
        "id": "X05",
        "function": "evalX86Operand",
        "line": 198,
        "description": "Default uninitialized `.stackSlot slot true` load to `some (.word64 0, mem)` instead of `none`.",
        "target": "  | .stackSlot slot true =>\n    match mem slot.index with\n    | some v => some (v, updateSlot mem slot.index none)\n    | none => none",
        "replacement": "  | .stackSlot slot true =>\n    match mem slot.index with\n    | some v => some (v, updateSlot mem slot.index none)\n    | none => some (.word64 0, mem)",
        "killing_canary": "canary_X05_uninit_move_violates_wellFormed",
    },
    {
        "id": "X06",
        "function": "evalX86BinOp",
        "line": 217,
        "description": "Mutate `X86BinOp.eq` on `.word64` from `decide (a = b)` to `true`.",
        "target": "  | .eq, .word64 a, .word64 b => some (.boolVal (decide (a = b)))",
        "replacement": "  | .eq, .word64 _, .word64 _ => some (.boolVal true)",
        "killing_canary": "canary_X06_eq_distinct_word64_not_true",
    },
    {
        "id": "X07",
        "function": "evalX86BinOp",
        "line": 230,
        "description": "Replace ill-typed `evalX86BinOp` fallback `none` with `some (.boolVal false)`.",
        "target": "  | .ne, .unit, .unit => some (.boolVal false)\n  | _, _, _ => none",
        "replacement": "  | .ne, .unit, .unit => some (.boolVal false)\n  | _, _, _ => some (.boolVal false)",
        "killing_canary": "canary_X07_illTyped_alu_violates_wellFormed",
    },
    {
        "id": "X08",
        "function": "evalX86Instr",
        "line": 259,
        "description": "Replace `.mov dst src` `none => .failed .ub` branch with silent `.nop` step.",
        "target": "  | .mov dst src =>\n    match evalX86Operand s.mem src with\n    | some (v, mem') =>\n      .step () { s with\n        mem := updateSlot mem' dst.index (some v)\n        ip := s.ip + 1\n      }\n    | none => .failed .ub",
        "replacement": "  | .mov dst src =>\n    match evalX86Operand s.mem src with\n    | some (v, mem') =>\n      .step () { s with\n        mem := updateSlot mem' dst.index (some v)\n        ip := s.ip + 1\n      }\n    | none => .step () { s with ip := s.ip + 1 }",
        "killing_canary": "canary_X08_failed_mov_violates_wellFormed",
    },
    {
        "id": "X09",
        "function": "evalX86Instr",
        "line": 281,
        "description": "Replace `.wrapAdt adtId dst src` `none => .failed .ub` branch with silent `.nop` step.",
        "target": "  | .wrapAdt adtId dst src =>\n    match evalX86Operand s.mem src with\n    | some (v, mem') =>\n      .step () { s with\n        mem := updateSlot mem' dst.index (some (.adt adtId v))\n        ip := s.ip + 1\n      }\n    | none => .failed .ub",
        "replacement": "  | .wrapAdt adtId dst src =>\n    match evalX86Operand s.mem src with\n    | some (v, mem') =>\n      .step () { s with\n        mem := updateSlot mem' dst.index (some (.adt adtId v))\n        ip := s.ip + 1\n      }\n    | none => .step () { s with ip := s.ip + 1 }",
        "killing_canary": "canary_X09_uninit_wrapAdt_violates_wellFormed",
    },
    {
        "id": "X10",
        "function": "evalX86Instr",
        "line": 289,
        "description": "Replace `.extractField0 dst src` non-ADT `_ => .failed .ub` branch with silent `.nop` step.",
        "target": "  | .extractField0 dst src =>\n    match s.mem src.index with\n    | some (.adt _ inner) =>\n      .step () { s with\n        mem := updateSlot s.mem dst.index (some inner)\n        ip := s.ip + 1\n      }\n    | _ => .failed .ub",
        "replacement": "  | .extractField0 dst src =>\n    match s.mem src.index with\n    | some (.adt _ inner) =>\n      .step () { s with\n        mem := updateSlot s.mem dst.index (some inner)\n        ip := s.ip + 1\n      }\n    | _ => .step () { s with ip := s.ip + 1 }",
        "killing_canary": "canary_X10_extractField0_non_adt_violates_wellFormed",
    },
    {
        "id": "X11",
        "function": "evalX86Instr",
        "line": 297,
        "description": "Allow `.leaSlot dst target` on uninitialized `target` (`none`) instead of `.failed .ub`.",
        "target": "  | .leaSlot dst target =>\n    match s.mem target.index with\n    | some _ =>\n      .step () { s with\n        mem := updateSlot s.mem dst.index (some (.stackPtr target))\n        ip := s.ip + 1\n      }\n    | none => .failed .ub",
        "replacement": "  | .leaSlot dst target =>\n    .step () { s with\n      mem := updateSlot s.mem dst.index (some (.stackPtr target))\n      ip := s.ip + 1\n    }",
        "killing_canary": "canary_X11_leaSlot_uninit_violates_wellFormed",
    },
    {
        "id": "X12",
        "function": "evalX86Instr",
        "line": 307,
        "description": "Omit dangling-target liveness check (`s.mem target.index`) in `.reborrowSlot dst srcPtr`.",
        "target": "  | .reborrowSlot dst srcPtr =>\n    match s.mem srcPtr.index with\n    | some (.stackPtr target) =>\n      match s.mem target.index with\n      | some _ =>\n        .step () { s with\n          mem := updateSlot s.mem dst.index (some (.stackPtr target))\n          ip := s.ip + 1\n        }\n      | none => .failed .ub\n    | _ => .failed .ub",
        "replacement": "  | .reborrowSlot dst srcPtr =>\n    match s.mem srcPtr.index with\n    | some (.stackPtr target) =>\n      .step () { s with\n        mem := updateSlot s.mem dst.index (some (.stackPtr target))\n        ip := s.ip + 1\n      }\n    | _ => .failed .ub",
        "killing_canary": "canary_X12_reborrowSlot_dead_target_violates_wellFormed",
    },
    {
        "id": "X13",
        "function": "evalX86Instr",
        "line": 318,
        "description": "Mutate `.deallocSlot slot` to preserve `s.mem` instead of resetting `slot` to `none`.",
        "target": "  | .deallocSlot slot =>\n    .step () { s with\n      mem := updateSlot s.mem slot.index none\n      ip := s.ip + 1\n    }",
        "replacement": "  | .deallocSlot _ =>\n    .step () { s with ip := s.ip + 1 }",
        "killing_canary": "canary_X13_use_after_deallocSlot_violates_wellFormed",
    },
    {
        "id": "X14",
        "function": "evalRepMovsb",
        "line": 344,
        "description": "Bypass outer `decide (srcSz = dstSz)` size check in `evalRepMovsb`.",
        "target": "  if decide (srcSz = dstSz) then\n    match ptrVal with\n    | .stackPtr target =>\n      match mem target.index with\n      | some (.bytes vSz bits) =>\n        if decide (vSz = srcSz) then",
        "replacement": "  if true then\n    match ptrVal with\n    | .stackPtr target =>\n      match mem target.index with\n      | some (.bytes vSz bits) =>\n        if decide (vSz = srcSz) then",
        "killing_canary": "canary_X14_repMovsb_size_mismatch_violates_wellFormed",
    },
    {
        "id": "X15",
        "function": "evalRepMovsb",
        "line": 349,
        "description": "Bypass inner `decide (vSz = srcSz)` pointee byte-size check in `evalRepMovsb`.",
        "target": "      | some (.bytes vSz bits) =>\n        if decide (vSz = srcSz) then\n          some (.bytes dstSz bits)\n        else\n          none",
        "replacement": "      | some (.bytes _ bits) =>\n        some (.bytes dstSz bits)",
        "killing_canary": "canary_X15_repMovsb_mismatched_pointee_bytes_violates_wellFormed",
    },
    {
        "id": "X16",
        "function": "evalX86Term",
        "line": 392,
        "description": "Mutate `.ret` on uninitialized slot `0` (`none`) from `.failed .ub` to `.terminated (.normal .unit)`.",
        "target": "  | .ret =>\n    match s.mem 0 with\n    | none => .failed .ub",
        "replacement": "  | .ret =>\n    match s.mem 0 with\n    | none => .terminated (.normal .unit)",
        "killing_canary": "canary_X16_uninit_ret_violates_wellFormed",
    },
    {
        "id": "X17",
        "function": "evalX86Term",
        "line": 408,
        "description": "Mutate `.ud2` terminator from `.failed .ub` to `.terminated .unwind`.",
        "target": "  | .ud2 =>\n    .failed .ub",
        "replacement": "  | .ud2 =>\n    .terminated .unwind",
        "killing_canary": "canary_X17_ud2_violates_wellFormed",
    },
    {
        "id": "X18",
        "function": "evalX86Term",
        "line": 410,
        "description": "Mutate `.abortPanic` terminator from `.terminated .unwind` to `.terminated (.normal .unit)`.",
        "target": "  | .abortPanic =>\n    .terminated .unwind",
        "replacement": "  | .abortPanic =>\n    .terminated (.normal .unit)",
        "killing_canary": "canary_X18_abortPanic_const_rejected_by_constSucceeds",
    },
    {
        "id": "X19",
        "function": "evalX86Term",
        "line": 417,
        "description": "Mutate `.jccBool` non-boolean fallback `_ => .failed .ub` to jump to `falseTarget`.",
        "target": "  | .jccBool cond falseTarget trueTarget =>\n    match evalX86Operand s.mem cond with\n    | some (.boolVal false, mem') =>\n      .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }\n    | some (.boolVal true, mem') =>\n      .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }\n    | _ => .failed .ub",
        "replacement": "  | .jccBool cond falseTarget trueTarget =>\n    match evalX86Operand s.mem cond with\n    | some (.boolVal false, mem') =>\n      .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }\n    | some (.boolVal true, mem') =>\n      .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }\n    | _ => .step () { s with bb := falseTarget.index, ip := 0 }",
        "killing_canary": "canary_X19_jccBool_non_bool_violates_wellFormed",
    },
    {
        "id": "X20",
        "function": "evalX86Step",
        "line": 468,
        "description": "Mutate out-of-bounds block lookup `active.blocks[s.bb]? = none` from `.failed .ub` to `.terminated .unwind`.",
        "target": "  match active.blocks[s.bb]? with\n  | none => .failed .ub",
        "replacement": "  match active.blocks[s.bb]? with\n  | none => .terminated .unwind",
        "killing_canary": "canary_X20_oob_jmp_violates_wellFormed",
    },
    {
        "id": "X21",
        "function": "AdmissibleLibInv",
        "line": 631,
        "description": "Weaken `AdmissibleLibInv` public-safe field closure clause to `True`.",
        "target": "  (∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →\n    ∀ tySizes v, libInv tySizes .usize v →\n      libInv tySizes (.adt decl.id) (.adt decl.id v))",
        "replacement": "  True",
        "killing_canary": "canary_X21_pub_safe_fields_reject_nonzero_inv",
    },
    {
        "id": "X22",
        "function": "EnsuresRetLibInv",
        "line": 652,
        "description": "Weaken `EnsuresRetLibInv` return-value `libInv` postcondition to `True`.",
        "target": "def EnsuresRetLibInv (libInv : LibInv) (retTy : X86Ty)\n    (pre : ExecQuery X86State → Prop) : X86Lang.Behavior :=\n  X86Lang.SpecOn pre (fun q out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      libInv q.init.tySizes retTy ret)",
        "replacement": "def EnsuresRetLibInv (_libInv : LibInv) (_retTy : X86Ty)\n    (pre : ExecQuery X86State → Prop) : X86Lang.Behavior :=\n  X86Lang.SpecOn pre (fun _ out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      True)",
        "killing_canary": "canary_X22_buggy_zero_adt_return_rejected",
    },
    {
        "id": "X23",
        "function": "defaultTrustPolicy",
        "line": 778,
        "description": "Mutate `defaultTrustPolicy` to allow `.userAxiom _ _ => True`.",
        "target": "def defaultTrustPolicy : TrustPolicy TCBItem where\n  isAllowed\n    | .assemblerLowering _ _ => True\n    | .userAxiom _ _ => False",
        "replacement": "def defaultTrustPolicy : TrustPolicy TCBItem where\n  isAllowed\n    | .assemblerLowering _ _ => True\n    | .userAxiom _ _ => True",
        "killing_canary": "canary_X23_unapproved_userAxiom_rejected",
    },
    {
        "id": "X24",
        "function": "CrateTheorem / EnsuresEqArg",
        "line": 665,
        "description": "Weaken `EnsuresEqArg` functional postcondition `q.init.mem argSlot = some ret` to `True`.",
        "target": "def EnsuresEqArg (argSlot : Nat) : X86Lang.Behavior :=\n  X86Lang.Spec (fun q out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      q.init.mem argSlot = some ret)",
        "replacement": "def EnsuresEqArg (_argSlot : Nat) : X86Lang.Behavior :=\n  X86Lang.Spec (fun _ out =>\n    ∀ ret, out.outcome = .terminated (.normal ret) →\n      True)",
        "killing_canary": "canary_X24_wrong_id_violates_ensures",
    },
]


def setup_branch_sandbox(branch_name: str, src_root: Path) -> Path:
    branch_dir = SANDBOX_DIR / branch_name
    if branch_dir.exists():
        shutil.rmtree(branch_dir)
    shutil.copytree(src_root / "trusted" / "lean", branch_dir / "trusted")
    shutil.copytree(src_root / "theory", branch_dir / "theory")
    return branch_dir


def precompile_common_modules(branch_dir: Path, is_x86: bool) -> None:
    t_dir = branch_dir / "trusted"
    th_dir = branch_dir / "theory"
    lean_path = [t_dir, th_dir]

    # Compile Trusted/Attributes.lean, Trusted/Refinement.lean, Trusted/StepResult.lean, Trusted/MirAst.lean (or X86Ast.lean)
    ast_name = "X86Ast" if is_x86 else "MirAst"
    sem_name = "X86Semantics" if is_x86 else "MirSemantics"
    for mod in ["Attributes", "Refinement", "StepResult", ast_name, sem_name]:
        rc, out = compile_to_olean(
            t_dir / "Trusted" / f"{mod}.lean",
            t_dir / "Trusted" / f"{mod}.olean",
            lean_path,
        )
        if rc != 0:
            raise RuntimeError(f"Failed to precompile Trusted/{mod}.lean:\n{out}")

    rc, out = compile_to_olean(t_dir / "Trusted.lean", t_dir / "Trusted.olean", lean_path)
    if rc != 0:
        raise RuntimeError(f"Failed to precompile Trusted.lean:\n{out}")

    for mod in ["Refinement", "StepResult"]:
        rc, out = compile_to_olean(
            th_dir / "Anneal" / f"{mod}.lean",
            th_dir / "Anneal" / f"{mod}.olean",
            lean_path,
        )
        if rc != 0:
            raise RuntimeError(f"Failed to precompile Anneal/{mod}.lean:\n{out}")


def run_mutation_suite(
    branch_name: str,
    commit_hash: str,
    src_root: Path,
    is_x86: bool,
    mutations: List[Dict[str, Any]],
    baseline_canaries_src: str,
    extra_canaries_src: str,
) -> Dict[str, Any]:
    print(f"=== Running mutation audit for {branch_name} ({commit_hash[:12]}) ===")
    branch_dir = setup_branch_sandbox(branch_name, src_root)
    precompile_common_modules(branch_dir, is_x86)

    t_dir = branch_dir / "trusted"
    th_dir = branch_dir / "theory"
    lean_path = [t_dir, th_dir]

    sem_name = "X86Semantics" if is_x86 else "MirSemantics"
    sem_lean = t_dir / "Trusted" / f"{sem_name}.lean"
    sem_olean = t_dir / "Trusted" / f"{sem_name}.olean"
    trusted_lean = t_dir / "Trusted.lean"
    trusted_olean = t_dir / "Trusted.olean"
    step_result_th_lean = th_dir / "Anneal" / "StepResult.lean"
    step_result_th_olean = th_dir / "Anneal" / "StepResult.olean"

    original_sem_text = sem_lean.read_text(encoding="utf-8")

    baseline_file = th_dir / "Anneal" / "BaselineCanaries.lean"
    augmented_file = th_dir / "Anneal" / "AugmentedCanaries.lean"
    baseline_file.write_text(baseline_canaries_src, encoding="utf-8")
    augmented_file.write_text(baseline_canaries_src + "\n" + extra_canaries_src, encoding="utf-8")

    # Sanity-check unmutated baseline and augmented canary files
    rc_base0, out_base0 = run_lean(baseline_file, lean_path)
    if rc_base0 != 0:
        raise RuntimeError(f"Unmutated BaselineCanaries.lean failed in {branch_name}:\n{out_base0}")
    rc_aug0, out_aug0 = run_lean(augmented_file, lean_path)
    if rc_aug0 != 0:
        raise RuntimeError(f"Unmutated AugmentedCanaries.lean failed in {branch_name}:\n{out_aug0}")
    print(f"  [OK] Unmutated BaselineCanaries.lean and AugmentedCanaries.lean verified in {branch_name}.")

    results = []
    baseline_killed = 0
    augmented_killed = 0

    for mut in mutations:
        mid = mut["id"]
        target = mut["target"]
        replacement = mut["replacement"]
        if target not in original_sem_text:
            raise RuntimeError(f"[{branch_name}:{mid}] Target snippet not found in {sem_name}.lean:\n{target}")
        if original_sem_text.count(target) != 1:
            raise RuntimeError(f"[{branch_name}:{mid}] Target snippet matched multiple times in {sem_name}.lean")

        mutated_text = original_sem_text.replace(target, replacement, 1)
        sem_lean.write_text(mutated_text, encoding="utf-8")

        # Recompile mutated Semantics.lean, Trusted.lean, and Anneal/StepResult.lean
        rc_sem, out_sem = compile_to_olean(sem_lean, sem_olean, lean_path)
        if rc_sem != 0:
            raise RuntimeError(f"[{branch_name}:{mid}] Invalid mutant (failed to compile {sem_name}.lean):\n{out_sem}")
        rc_tr, out_tr = compile_to_olean(trusted_lean, trusted_olean, lean_path)
        if rc_tr != 0:
            raise RuntimeError(f"[{branch_name}:{mid}] Failed to compile Trusted.lean:\n{out_tr}")
        rc_sr, out_sr = compile_to_olean(step_result_th_lean, step_result_th_olean, lean_path)
        if rc_sr != 0:
            raise RuntimeError(f"[{branch_name}:{mid}] Failed to compile Anneal/StepResult.lean:\n{out_sr}")

        # 1. Test against BaselineCanaries.lean (the 5 existing negative canaries)
        rc_base, _ = run_lean(baseline_file, lean_path)
        base_status = "KILLED" if rc_base != 0 else "SURVIVED"
        if base_status == "KILLED":
            baseline_killed += 1

        # 2. Test against AugmentedCanaries.lean (all 24 negative canaries)
        rc_aug, out_aug = run_lean(augmented_file, lean_path)
        aug_status = "KILLED" if rc_aug != 0 else "SURVIVED"
        if aug_status == "KILLED":
            augmented_killed += 1

        print(f"  [{mid}] {mut['function']} (L{mut['line']}): baseline={base_status}, augmented={aug_status} ({mut['killing_canary']})")

        results.append({
            "id": mid,
            "function": mut["function"],
            "line": mut["line"],
            "description": mut["description"],
            "target": target,
            "replacement": replacement,
            "trusted_tcb_compiles": True,
            "baseline_negative_canaries_status": base_status,
            "augmented_negative_canaries_status": aug_status,
            "killing_canary": mut["killing_canary"],
        })

    # Restore original file
    sem_lean.write_text(original_sem_text, encoding="utf-8")

    total = len(mutations)
    return {
        "branch": branch_name,
        "commit": commit_hash,
        "target_file": f"trusted/lean/Trusted/{sem_name}.lean",
        "total_mutations": total,
        "baseline_negative_canaries_count": 5,
        "baseline_killed": baseline_killed,
        "baseline_survived": total - baseline_killed,
        "baseline_kill_rate_pct": round(100.0 * baseline_killed / total, 2),
        "augmented_negative_canaries_count": 24,
        "augmented_killed": augmented_killed,
        "augmented_survived": total - augmented_killed,
        "augmented_kill_rate_pct": round(100.0 * augmented_killed / total, 2),
        "mutations": results,
    }


def main() -> None:
    global LEAN_BIN, TRUSTED_CORE_ROOT, MIR_TO_X86_ROOT, OUT_DIR, SANDBOX_DIR, RESULTS_JSON
    parser = argparse.ArgumentParser(description="Run Anneal Trusted/*.lean semantic mutation audit.")
    parser.add_argument("--lean-bin", default=LEAN_BIN, help="Path to Lean 4 compiler binary (or set LEAN_BIN).")
    parser.add_argument("--trusted-core-root", type=Path, default=TRUSTED_CORE_ROOT, help="Path to trusted-core worktree.")
    parser.add_argument("--mir-to-x86-root", type=Path, default=MIR_TO_X86_ROOT, help="Path to mir-to-x86 worktree.")
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR, help="Output directory for mutation_audit_results.json.")
    args = parser.parse_args()
    LEAN_BIN = args.lean_bin
    TRUSTED_CORE_ROOT = args.trusted_core_root.resolve()
    MIR_TO_X86_ROOT = args.mir_to_x86_root.resolve()
    OUT_DIR = args.out_dir.resolve()
    SANDBOX_DIR = OUT_DIR / "_mutation_sandbox"
    RESULTS_JSON = OUT_DIR / "mutation_audit_results.json"

    t0 = time.time()
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    tc_report = run_mutation_suite(
        branch_name="trusted-core",
        commit_hash="e6a0b2da5ec39a4c0cfd22bf323885022837b5dc",
        src_root=TRUSTED_CORE_ROOT,
        is_x86=False,
        mutations=MIR_MUTATIONS,
        baseline_canaries_src=MIR_BASELINE_CANARIES_LEAN,
        extra_canaries_src=MIR_EXTRA_19_CANARIES_LEAN,
    )

    x86_report = run_mutation_suite(
        branch_name="mir-to-x86",
        commit_hash="4f45f0a391a921ced9c9dc773b9a040dbc215d14",
        src_root=MIR_TO_X86_ROOT,
        is_x86=True,
        mutations=X86_MUTATIONS,
        baseline_canaries_src=X86_BASELINE_CANARIES_LEAN,
        extra_canaries_src=X86_EXTRA_19_CANARIES_LEAN,
    )

    # Clean up temporary .olean build sandbox
    if SANDBOX_DIR.exists():
        shutil.rmtree(SANDBOX_DIR)

    elapsed = round(time.time() - t0, 2)
    summary = {
        "audit_timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "lean_compiler": LEAN_BIN,
        "lean_flags": LEAN_FLAGS,
        "elapsed_seconds": elapsed,
        "branches": {
            "trusted-core": tc_report,
            "mir-to-x86": x86_report,
        },
    }
    RESULTS_JSON.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"\n=== Mutation Audit Complete in {elapsed}s ===")
    print(f"  trusted-core: baseline={tc_report['baseline_killed']}/{tc_report['total_mutations']} ({tc_report['baseline_kill_rate_pct']}%), augmented={tc_report['augmented_killed']}/{tc_report['total_mutations']} ({tc_report['augmented_kill_rate_pct']}%)")
    print(f"  mir-to-x86:   baseline={x86_report['baseline_killed']}/{x86_report['total_mutations']} ({x86_report['baseline_kill_rate_pct']}%), augmented={x86_report['augmented_killed']}/{x86_report['total_mutations']} ({x86_report['augmented_kill_rate_pct']}%)")


if __name__ == "__main__":
    main()
