-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Pre-Proved Lowering Passes & Validators (`ProbePreprovedPasses.lean`)

This self-contained Lean 4.34.1 probe models Anneal's `Trusted.Refinement` and
`Anneal.Refinement` algebra (`Language`, `Behavior`, `BehaviorCodec`,
`Abstracts`, `pass_trans`, `verify_through_passes`) and benchmarks the
4-point spectrum of compile-time pre-proved transformations in `theory/Anneal/`:

1. **Point 1 (Per-Function Tactical Proof Generation in `Proof.lean`):**
   Each function's proof steps through small-step operational transitions one
   statement/branch at a time using per-step lemmas (`SafeReturns.of_step`).
2. **Point 2 (Universal Verified Lowering Pass `lowerToPure_sound`):**
   `theory/Anneal/` defines `lowerToPure (body : MirBody) := evalSym
   (computePlan body) body` and proves `lowerToPure_sound` once at Anneal
   compile time. At runtime, `Proof.lean` invokes `lowerToPure_sound body`, and
   functional equivalence `lowerToPure body s = some spec` forces the Lean
   kernel's `whnf`/`isDefEq` engine to reduce both `computePlan body` (including
   CFG reachability and NLL loan-liveness scans) and `evalSym`.
3. **Point 3 (Universal Verified Translation Validator / Pre-Emitted Hint
   Witness `evalSym_sound`):**
   `anneal-rustc-capture` computes `plan : TransPlan` in native Rust and emits
   it into `Proof.lean`. At runtime, `Proof.lean` invokes `evalSym_sound plan
   body`, so the Lean kernel never reduces `computePlan body` and only checks
   the linear `evalSym plan body` execution.
4. **Point 4 (Pre-Proved Compositional Multi-Pass Pipeline `pipeline_sound`):**
   `theory/Anneal/` chains multiple passes (`MirRaw` -> `MirNorm` -> `PureLang`)
   via `BehaviorCodec.comp` and `pass_trans` into a single compile-time theorem
   `pipeline_sound`, compared against chaining individual passes per function in
   `Proof.lean`.
-/

open Lean

namespace ProbePreprovedPasses

/-!
## 1. Minimal Refinement Algebra (Mirroring `Trusted/Refinement.lean`)
-/

structure Partial (α : Type) : Type where
  defined : Prop
  val : defined → α

instance {Out : Type} : LE (Partial (Out → Prop)) where
  le p q := (q.defined → p.defined) ∧
    ∀ (hq : q.defined) (hp : p.defined) (o : Out), p.val hp o → q.val hq o

def Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

instance {Query Out : Type} : LE (Behavior Query Out) where
  le b₁ b₂ := ∀ q, b₁ q ≤ b₂ q

theorem Behavior.le_refl {Query Out : Type} (b : Behavior Query Out) : b ≤ b :=
  fun _ => ⟨id, fun _ _ _ h => h⟩

theorem Behavior.le_trans {Query Out : Type}
    {b₁ b₂ b₃ : Behavior Query Out} (h₁₂ : b₁ ≤ b₂) (h₂₃ : b₂ ≤ b₃) :
    b₁ ≤ b₃ := by
  intro q
  refine ⟨fun h3 => (h₁₂ q).1 ((h₂₃ q).1 h3), ?_⟩
  intro h3 h1 o ho
  have h2 : (b₂ q).defined := (h₂₃ q).1 h3
  exact (h₂₃ q).2 h3 h2 o ((h₁₂ q).2 h2 h1 o ho)

structure Language (SemObs : Type) where
  Prog : Type
  Query : Type
  Out : Type
  obs : Out → SemObs
  sem : Prog → Behavior Query Out

def Monotone {Q₁ O₁ Q₂ O₂ : Type}
    (π : Behavior Q₁ O₁ → Behavior Q₂ O₂) : Prop :=
  ∀ ⦃b₁ b₂⦄, b₁ ≤ b₂ → π b₁ ≤ π b₂

def Abstracts {Obs : Type} (L_v L_src : Language Obs)
    (π_v : Behavior L_v.Query L_v.Out → Behavior L_src.Query L_src.Out)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

theorem pass_trans {Obs : Type} {L₁ L₂ L₃ : Language Obs}
    {π₁₂ : Behavior L₁.Query L₁.Out → Behavior L₂.Query L₂.Out}
    {π₂₃ : Behavior L₂.Query L₂.Out → Behavior L₃.Query L₃.Out}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h_mono : Monotone π₂₃)
    (h₁₂ : Abstracts L₁ L₂ π₁₂ p₁ p₂)
    (h₂₃ : Abstracts L₂ L₃ π₂₃ p₂ p₃) :
    Abstracts L₁ L₃ (π₂₃ ∘ π₁₂) p₁ p₃ :=
  Behavior.le_trans h₂₃ (h_mono h₁₂)

/-!
## 2. Concrete & Symbolic MIR Fragment with Mutable Borrow Joins and Loops
-/

inductive Stmt where
  | assignConst (dst : Nat) (val : Nat)
  | assignCopy (dst : Nat) (src : Nat)
  | assignAdd (dst : Nat) (lhs : Nat) (rhs : Nat)
  | assignLt (dst : Nat) (lhs : Nat) (rhs : Nat)
  | derefRead (dst : Nat) (refLoc : Nat)
  | derefWrite (refLoc : Nat) (src : Nat)
  | nop
  deriving Repr, DecidableEq

inductive Terminator where
  | goto (target : Nat)
  | switchInt (discr : Nat) (falseBlk : Nat) (trueBlk : Nat)
  | return_ (src : Nat)
  deriving Repr, DecidableEq

structure BasicBlock where
  stmts : List Stmt
  term : Terminator
  deriving Repr, DecidableEq

structure MirBody where
  blocks : List BasicBlock
  deriving Repr, DecidableEq

/-- Concrete state for a 2-borrow, 4-register machine. -/
structure MirState where
  r0 : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat
  mem0 : Nat
  mem1 : Nat
  refReg : Bool
  blk : Nat
  stmtIdx : Nat
  deriving Repr, DecidableEq

def getReg (s : MirState) (idx : Nat) : Nat :=
  match idx with
  | 0 => s.r0
  | 1 => s.r1
  | 2 => s.r2
  | 3 => s.r3
  | _ => 0

def setReg (s : MirState) (idx : Nat) (v : Nat) : MirState :=
  match idx with
  | 0 => { s with r0 := v }
  | 1 => { s with r1 := v }
  | 2 => { s with r2 := v }
  | 3 => { s with r3 := v }
  | _ => s

def readRef (s : MirState) (refId : Nat) : Nat :=
  match refId with
  | 0 => s.mem0
  | 1 => s.mem1
  | _ => if s.refReg then s.mem1 else s.mem0

def writeRef (s : MirState) (refId : Nat) (v : Nat) : MirState :=
  match refId with
  | 0 => { s with mem0 := v }
  | 1 => { s with mem1 := v }
  | _ => if s.refReg then { s with mem1 := v } else { s with mem0 := v }

def evalStmt (s : MirState) (stmt : Stmt) : MirState :=
  match stmt with
  | .assignConst dst val => { setReg s dst val with stmtIdx := s.stmtIdx + 1 }
  | .assignCopy dst src => { setReg s dst (getReg s src) with stmtIdx := s.stmtIdx + 1 }
  | .assignAdd dst lhs rhs =>
    { setReg s dst (getReg s lhs + getReg s rhs) with stmtIdx := s.stmtIdx + 1 }
  | .assignLt dst lhs rhs =>
    { setReg s dst (if decide (getReg s lhs < getReg s rhs) then 1 else 0) with
      stmtIdx := s.stmtIdx + 1 }
  | .derefRead dst refLoc =>
    { setReg s dst (readRef s refLoc) with stmtIdx := s.stmtIdx + 1 }
  | .derefWrite refLoc src =>
    { writeRef s refLoc (getReg s src) with stmtIdx := s.stmtIdx + 1 }
  | .nop => { s with stmtIdx := s.stmtIdx + 1 }

inductive StepOut where
  | step (next : MirState)
  | ret (val : Nat)
  | stuck
  deriving Repr, DecidableEq

def evalMirStep (body : MirBody) (s : MirState) : StepOut :=
  match body.blocks[s.blk]? with
  | none => .stuck
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => .step (evalStmt s stmt)
    | none =>
      match bb.term with
      | .goto target => .step { s with blk := target, stmtIdx := 0 }
      | .switchInt discr fBlk tBlk =>
        let nextBlk := if getReg s discr == 0 then fBlk else tBlk
        .step { s with blk := nextBlk, stmtIdx := 0 }
      | .return_ src => .ret (getReg s src)

/-- Safe termination predicate: `SafeReturns body s ret` holds iff `body`
    steps deterministically from `s` to `.ret ret`. -/
inductive SafeReturns (body : MirBody) : MirState → Nat → Prop where
  | of_ret {s : MirState} {ret : Nat}
      (h : evalMirStep body s = .ret ret) :
      SafeReturns body s ret
  | of_step {s s' : MirState} {ret : Nat}
      (h : evalMirStep body s = .step s')
      (hnext : SafeReturns body s' ret) :
      SafeReturns body s ret

theorem SafeReturns.det {body : MirBody} {s : MirState} {r₁ r₂ : Nat}
    (h₁ : SafeReturns body s r₁) (h₂ : SafeReturns body s r₂) : r₁ = r₂ := by
  induction h₁ with
  | of_ret hr1 =>
    cases h₂ with
    | of_ret hr2 =>
      rw [hr1] at hr2
      injection hr2
    | of_step hs2 _ =>
      rw [hr1] at hs2
      cases hs2
  | of_step hs1 _ ih =>
    cases h₂ with
    | of_ret hr2 =>
      rw [hs1] at hr2
      cases hr2
    | of_step hs2 hnext2 =>
      rw [hs1] at hs2
      injection hs2 with heq
      subst heq
      exact ih hnext2

def MirLang : Language Nat where
  Prog := MirBody
  Query := MirState
  Out := Nat
  obs := id
  sem body s := {
    defined := ∃ r, SafeReturns body s r
    val := fun _ r => SafeReturns body s r
  }

def PureLang : Language Nat where
  Prog := MirState → Option Nat
  Query := MirState
  Out := Nat
  obs := id
  sem f s := {
    defined := (f s).isSome = true
    val := fun _ r => f s = some r
  }

def π_pure : Behavior PureLang.Query PureLang.Out → Behavior MirLang.Query MirLang.Out :=
  id

theorem π_pure_mono : Monotone π_pure :=
  fun _ _ h => h

/-!
## 3. Hint-Guided Symbolic Evaluator (`TransPlan`, `evalSym`) with Loop Support
-/

inductive TransPlan where
  | ret (src : Nat)
  | stepStmt (next : TransPlan)
  | stepGoto (next : TransPlan)
  | branch (falsePlan : TransPlan) (truePlan : TransPlan)
  | whileLoop (fuel : Nat) (condSteps : List Bool) (bodySteps : List Bool) (exitPlan : TransPlan)
  | fail
  deriving Repr, DecidableEq

/-- Helper to run a straight-line sequence of statement steps (`true`) or goto
    steps (`false`). -/
def evalLinearSteps : List Bool → MirBody → MirState → Option MirState
  | [], _, s => some s
  | true :: rest, body, s =>
    match body.blocks[s.blk]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some stmt => evalLinearSteps rest body (evalStmt s stmt)
      | none => none
  | false :: rest, body, s =>
    match body.blocks[s.blk]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]?, bb.term with
      | none, .goto target => evalLinearSteps rest body { s with blk := target, stmtIdx := 0 }
      | _, _ => none

theorem evalLinearSteps_sound :
    ∀ (steps : List Bool) (body : MirBody) (s s' : MirState) (ret : Nat),
      evalLinearSteps steps body s = some s' →
      SafeReturns body s' ret →
      SafeReturns body s ret
  | [], _, s, s', _, h, hSafe => by
    injection h with heq; subst heq; exact hSafe
  | true :: rest, body, s, s', ret, h, hSafe => by
    unfold evalLinearSteps at h
    cases hbb : body.blocks[s.blk]? with
    | none => rw [hbb] at h; cases h
    | some bb =>
      rw [hbb] at h; dsimp at h
      cases hstmt : bb.stmts[s.stmtIdx]? with
      | none => rw [hstmt] at h; cases h
      | some stmt =>
        rw [hstmt] at h; dsimp at h
        have hStep : evalMirStep body s = .step (evalStmt s stmt) := by
          unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]
        exact SafeReturns.of_step hStep
          (evalLinearSteps_sound rest body (evalStmt s stmt) s' ret h hSafe)
  | false :: rest, body, s, s', ret, h, hSafe => by
    unfold evalLinearSteps at h
    cases hbb : body.blocks[s.blk]? with
    | none => rw [hbb] at h; cases h
    | some bb =>
      rw [hbb] at h; dsimp at h
      cases hstmt : bb.stmts[s.stmtIdx]? with
      | some _ => rw [hstmt] at h; cases h
      | none =>
        rw [hstmt] at h
        cases hterm : bb.term with
        | return_ _ | switchInt _ _ _ => rw [hterm] at h; cases h
        | goto target =>
          rw [hterm] at h; dsimp at h
          have hStep : evalMirStep body s = .step { s with blk := target, stmtIdx := 0 } := by
            unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]
          exact SafeReturns.of_step hStep
            (evalLinearSteps_sound rest body { s with blk := target, stmtIdx := 0 } s' ret h hSafe)

/-- Structurally recursive loop evaluator on `fuel`. -/
def evalWhileLoop :
    Nat → List Bool → List Bool → (MirBody → MirState → Option Nat) →
    MirBody → MirState → Option Nat
  | 0, _, _, _, _, _ => none
  | fuel + 1, condSteps, bodySteps, evalExit, body, s =>
    match evalLinearSteps condSteps body s with
    | none => none
    | some sSwitch =>
      match body.blocks[sSwitch.blk]? with
      | none => none
      | some bb =>
        match bb.stmts[sSwitch.stmtIdx]?, bb.term with
        | none, .switchInt discr fBlk tBlk =>
          if getReg sSwitch discr == 0 then
            evalExit body { sSwitch with blk := fBlk, stmtIdx := 0 }
          else
            match evalLinearSteps bodySteps body { sSwitch with blk := tBlk, stmtIdx := 0 } with
            | none => none
            | some sNext =>
              evalWhileLoop fuel condSteps bodySteps evalExit body sNext
        | _, _ => none

theorem evalWhileLoop_sound :
    ∀ (fuel : Nat) (condSteps bodySteps : List Bool)
      (evalExit : MirBody → MirState → Option Nat) (body : MirBody)
      (_hExit : ∀ sExit r, evalExit body sExit = some r → SafeReturns body sExit r)
      (s : MirState) (ret : Nat),
      evalWhileLoop fuel condSteps bodySteps evalExit body s = some ret →
      SafeReturns body s ret
  | 0, _, _, _, _, _, _, _, h => by cases h
  | fuel + 1, condSteps, bodySteps, evalExit, body, hExit, s, ret, h => by
    unfold evalWhileLoop at h
    cases hCond : evalLinearSteps condSteps body s with
    | none => rw [hCond] at h; cases h
    | some sSwitch =>
      rw [hCond] at h; dsimp at h
      cases hbb : body.blocks[sSwitch.blk]? with
      | none => rw [hbb] at h; cases h
      | some bb =>
        rw [hbb] at h; dsimp at h
        cases hstmt : bb.stmts[sSwitch.stmtIdx]? with
        | some _ => rw [hstmt] at h; cases h
        | none =>
          rw [hstmt] at h
          cases hterm : bb.term with
          | return_ _ | goto _ => rw [hterm] at h; cases h
          | switchInt discr fBlk tBlk =>
            rw [hterm] at h; dsimp at h
            cases hbr : (getReg sSwitch discr == 0) with
            | true =>
              rw [hbr] at h; dsimp at h
              have hStepSw : evalMirStep body sSwitch = .step { sSwitch with blk := fBlk, stmtIdx := 0 } := by
                unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]; dsimp; rw [hbr]; rfl
              exact evalLinearSteps_sound condSteps body s sSwitch ret hCond
                (SafeReturns.of_step hStepSw (hExit { sSwitch with blk := fBlk, stmtIdx := 0 } ret h))
            | false =>
              rw [hbr] at h; dsimp at h
              have hStepSw : evalMirStep body sSwitch = .step { sSwitch with blk := tBlk, stmtIdx := 0 } := by
                unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]; dsimp; rw [hbr]; rfl
              cases hBody : evalLinearSteps bodySteps body { sSwitch with blk := tBlk, stmtIdx := 0 } with
              | none => rw [hBody] at h; cases h
              | some sNext =>
                rw [hBody] at h; dsimp at h
                have hRec := evalWhileLoop_sound fuel condSteps bodySteps evalExit body hExit sNext ret h
                have hBodySafe := evalLinearSteps_sound bodySteps body
                  { sSwitch with blk := tBlk, stmtIdx := 0 } sNext ret hBody hRec
                exact evalLinearSteps_sound condSteps body s sSwitch ret hCond
                  (SafeReturns.of_step hStepSw hBodySafe)

/-- Symbolic/functional evaluator guided by a positional `TransPlan`. -/
def evalSym : TransPlan → MirBody → MirState → Option Nat
  | .fail, _, _ => none
  | .ret src, body, s =>
    match body.blocks[s.blk]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]?, bb.term with
      | none, .return_ src' =>
        if src == src' then some (getReg s src') else none
      | _, _ => none
  | .stepStmt next, body, s =>
    match body.blocks[s.blk]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some stmt => evalSym next body (evalStmt s stmt)
      | none => none
  | .stepGoto next, body, s =>
    match body.blocks[s.blk]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]?, bb.term with
      | none, .goto target => evalSym next body { s with blk := target, stmtIdx := 0 }
      | _, _ => none
  | .branch fPlan tPlan, body, s =>
    match body.blocks[s.blk]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]?, bb.term with
      | none, .switchInt discr fBlk tBlk =>
        if getReg s discr == 0 then
          evalSym fPlan body { s with blk := fBlk, stmtIdx := 0 }
        else
          evalSym tPlan body { s with blk := tBlk, stmtIdx := 0 }
      | _, _ => none
  | .whileLoop fuel condSteps bodySteps exitPlan, body, s =>
    evalWhileLoop fuel condSteps bodySteps (evalSym exitPlan) body s

/-- **Pre-Proved Universal Validator Soundness (`evalSym_sound`)**:
    Proved once at Anneal compile time in `theory/Anneal/`. Holds for *every*
    `plan : TransPlan` (including `.whileLoop`) and *every* `body : MirBody`. -/
theorem evalSym_step_sound :
    ∀ (plan : TransPlan) (body : MirBody) (s : MirState) (ret : Nat),
      evalSym plan body s = some ret →
      SafeReturns body s ret
  | .fail, _, _, _, h => by cases h
  | .ret src, body, s, ret, h => by
    unfold evalSym at h
    cases hbb : body.blocks[s.blk]? with
    | none => rw [hbb] at h; cases h
    | some bb =>
      rw [hbb] at h; dsimp at h
      cases hstmt : bb.stmts[s.stmtIdx]? with
      | some _ => rw [hstmt] at h; cases h
      | none =>
        rw [hstmt] at h
        cases hterm : bb.term with
        | goto _ | switchInt _ _ _ => rw [hterm] at h; cases h
        | return_ src' =>
          rw [hterm] at h; dsimp at h
          cases hbeq : (src == src') with
          | false => rw [hbeq] at h; cases h
          | true =>
            rw [hbeq] at h; injection h with hret; subst hret
            have hRet : evalMirStep body s = .ret (getReg s src') := by
              unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]
            exact SafeReturns.of_ret hRet
  | .stepStmt next, body, s, ret, h => by
    unfold evalSym at h
    cases hbb : body.blocks[s.blk]? with
    | none => rw [hbb] at h; cases h
    | some bb =>
      rw [hbb] at h; dsimp at h
      cases hstmt : bb.stmts[s.stmtIdx]? with
      | none => rw [hstmt] at h; cases h
      | some stmt =>
        rw [hstmt] at h; dsimp at h
        have hStep : evalMirStep body s = .step (evalStmt s stmt) := by
          unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]
        exact SafeReturns.of_step hStep (evalSym_step_sound next body (evalStmt s stmt) ret h)
  | .stepGoto next, body, s, ret, h => by
    unfold evalSym at h
    cases hbb : body.blocks[s.blk]? with
    | none => rw [hbb] at h; cases h
    | some bb =>
      rw [hbb] at h; dsimp at h
      cases hstmt : bb.stmts[s.stmtIdx]? with
      | some _ => rw [hstmt] at h; cases h
      | none =>
        rw [hstmt] at h
        cases hterm : bb.term with
        | return_ _ | switchInt _ _ _ => rw [hterm] at h; cases h
        | goto target =>
          rw [hterm] at h; dsimp at h
          have hStep : evalMirStep body s = .step { s with blk := target, stmtIdx := 0 } := by
            unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]
          exact SafeReturns.of_step hStep
            (evalSym_step_sound next body { s with blk := target, stmtIdx := 0 } ret h)
  | .branch fPlan tPlan, body, s, ret, h => by
    unfold evalSym at h
    cases hbb : body.blocks[s.blk]? with
    | none => rw [hbb] at h; cases h
    | some bb =>
      rw [hbb] at h; dsimp at h
      cases hstmt : bb.stmts[s.stmtIdx]? with
      | some _ => rw [hstmt] at h; cases h
      | none =>
        rw [hstmt] at h
        cases hterm : bb.term with
        | return_ _ | goto _ => rw [hterm] at h; cases h
        | switchInt discr fBlk tBlk =>
          rw [hterm] at h; dsimp at h
          cases hcond : (getReg s discr == 0) with
          | true =>
            rw [hcond] at h; dsimp at h
            have hStep : evalMirStep body s = .step { s with blk := fBlk, stmtIdx := 0 } := by
              unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]; dsimp; rw [hcond]; rfl
            exact SafeReturns.of_step hStep
              (evalSym_step_sound fPlan body { s with blk := fBlk, stmtIdx := 0 } ret h)
          | false =>
            rw [hcond] at h; dsimp at h
            have hStep : evalMirStep body s = .step { s with blk := tBlk, stmtIdx := 0 } := by
              unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]; dsimp; rw [hcond]; rfl
            exact SafeReturns.of_step hStep
              (evalSym_step_sound tPlan body { s with blk := tBlk, stmtIdx := 0 } ret h)
  | .whileLoop fuel condSteps bodySteps exitPlan, body, s, ret, h => by
    unfold evalSym at h
    exact evalWhileLoop_sound fuel condSteps bodySteps (evalSym exitPlan) body
      (fun sExit r hr => evalSym_step_sound exitPlan body sExit r hr) s ret h

theorem evalSym_sound (plan : TransPlan) (body : MirBody) :
    Abstracts PureLang MirLang π_pure (evalSym plan body) body := by
  intro s
  refine ⟨?_, ?_⟩
  · intro hdef
    change (evalSym plan body s).isSome = true at hdef
    cases h : evalSym plan body s with
    | none => rw [h] at hdef; cases hdef
    | some r => exact ⟨r, evalSym_step_sound plan body s r h⟩
  · intro hdef _ r hr
    change (evalSym plan body s).isSome = true at hdef
    cases h : evalSym plan body s with
    | none => rw [h] at hdef; cases hdef
    | some r₀ =>
      have hr₀ : SafeReturns body s r₀ := evalSym_step_sound plan body s r₀ h
      have heq : r = r₀ := SafeReturns.det hr hr₀
      subst heq
      exact h

/-!
## 4. Untrusted CFG + Liveness Planner (`computePlan`) vs. Pre-Emitted Hints
-/

def stmtReadsReg (stmt : Stmt) (reg : Nat) : Bool :=
  match stmt with
  | .assignConst _ _ | .nop => false
  | .assignCopy _ src | .derefWrite _ src => src == reg
  | .assignAdd _ l r | .assignLt _ l r => l == reg || r == reg
  | .derefRead _ _ => false

def blockUsesRegFrom (stmts : List Stmt) (reg : Nat) : Bool :=
  stmts.any (fun st => stmtReadsReg st reg)

/-- Untrusted planner that scans remaining statements and reachable CFG blocks
    to structure a `MirBody` into a `TransPlan`. -/
def computePlanAux : Nat → MirBody → Nat → Nat → TransPlan
  | 0, _, _, _ => .fail
  | fuel + 1, body, blk, idx =>
    match body.blocks[blk]? with
    | none => .fail
    | some bb =>
      match bb.stmts[idx]? with
      | some _ =>
        let livenessCost :=
          body.blocks.foldl (fun acc b =>
            acc + (if blockUsesRegFrom b.stmts 0 || blockUsesRegFrom b.stmts 1 ||
                      blockUsesRegFrom b.stmts 2 || blockUsesRegFrom b.stmts 3
                   then 1 else 0)) 0
        if livenessCost < 1000000 then
          .stepStmt (computePlanAux fuel body blk (idx + 1))
        else
          .fail
      | none =>
        match bb.term with
        | .return_ src => .ret src
        | .goto target => .stepGoto (computePlanAux fuel body target 0)
        | .switchInt _ fBlk tBlk =>
          .branch (computePlanAux fuel body fBlk 0) (computePlanAux fuel body tBlk 0)

def computePlan (body : MirBody) : TransPlan :=
  computePlanAux 512 body 0 0

def lowerToPure (body : MirBody) : PureLang.Prog :=
  evalSym (computePlan body) body

theorem lowerToPure_sound (body : MirBody) :
    Abstracts PureLang MirLang π_pure (lowerToPure body) body :=
  evalSym_sound (computePlan body) body

/-!
## 5. Point 4: Pre-Proved Multi-Pass Pipeline (`MirRaw` -> `MirNorm` -> `PureLang`)
-/

def normalizeBody (body : MirBody) : MirBody :=
  { blocks := body.blocks }

def NormLang : Language Nat := MirLang

def π_norm : Behavior NormLang.Query NormLang.Out → Behavior MirLang.Query MirLang.Out :=
  id

theorem normalizeBody_sound (body : MirBody) :
    Abstracts NormLang MirLang π_norm (normalizeBody body) body :=
  Behavior.le_refl (MirLang.sem body)

theorem pipeline_sound (plan : TransPlan) (body : MirBody) :
    Abstracts PureLang MirLang (π_norm ∘ π_pure)
      (evalSym plan (normalizeBody body)) body :=
  pass_trans (fun _ _ h => h) (evalSym_sound plan (normalizeBody body)) (normalizeBody_sound body)

/-!
## 6. Scaling Benchmark Family: $N$-Block Pipeline ($N \in \{4, 8, 12\}$)
-/

def mkChainBlocks : Nat → Nat → List BasicBlock
  | 0, _ =>
    [{ stmts := [.assignAdd 0 0 1], term := .return_ 0 }]
  | k + 1, blkIdx =>
    { stmts := [
        .assignConst 2 1,
        .assignAdd 0 0 2,
        .assignAdd 1 1 2
      ]
      term := .goto (blkIdx + 1) } :: mkChainBlocks k (blkIdx + 1)

def mkChainBody (n : Nat) : MirBody :=
  { blocks := mkChainBlocks n 0 }

def mkChainPlan : Nat → TransPlan
  | 0 => .stepStmt (.ret 0)
  | k + 1 => .stepStmt (.stepStmt (.stepStmt (.stepGoto (mkChainPlan k))))

def body4 : MirBody := mkChainBody 4
def plan4 : TransPlan := mkChainPlan 4

def body8 : MirBody := mkChainBody 8
def plan8 : TransPlan := mkChainPlan 8

def body12 : MirBody := mkChainBody 12
def plan12 : TransPlan := mkChainPlan 12

/-- Helper to advance one block (3 statements + 1 goto) in Tactical Mode
    (Point 1), mirroring `MirLemmas.lean`'s explicit step-by-step chaining. -/
theorem stepChainBlock {body : MirBody} {r0 r1 r2 r3 m0 m1 : Nat} {rr : Bool}
    {blk : Nat} {ret : Nat}
    (hs1 : evalMirStep body ⟨r0, r1, r2, r3, m0, m1, rr, blk, 0⟩ =
      .step ⟨r0, r1, 1, r3, m0, m1, rr, blk, 1⟩)
    (hs2 : evalMirStep body ⟨r0, r1, 1, r3, m0, m1, rr, blk, 1⟩ =
      .step ⟨r0 + 1, r1, 1, r3, m0, m1, rr, blk, 2⟩)
    (hs3 : evalMirStep body ⟨r0 + 1, r1, 1, r3, m0, m1, rr, blk, 2⟩ =
      .step ⟨r0 + 1, r1 + 1, 1, r3, m0, m1, rr, blk, 3⟩)
    (hs4 : evalMirStep body ⟨r0 + 1, r1 + 1, 1, r3, m0, m1, rr, blk, 3⟩ =
      .step ⟨r0 + 1, r1 + 1, 1, r3, m0, m1, rr, blk + 1, 0⟩)
    (hnext : SafeReturns body ⟨r0 + 1, r1 + 1, 1, r3, m0, m1, rr, blk + 1, 0⟩ ret) :
    SafeReturns body ⟨r0, r1, r2, r3, m0, m1, rr, blk, 0⟩ ret :=
  SafeReturns.of_step hs1
    (SafeReturns.of_step hs2
      (SafeReturns.of_step hs3
        (SafeReturns.of_step hs4 hnext)))

-- Point 1: Tactical Step-by-Step Proofs (N = 4, 8, 12)
theorem point1_tactical_body4 (r0 r1 : Nat) :
    SafeReturns body4 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 4 + (r1 + 4)) := by
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  exact SafeReturns.of_step rfl (SafeReturns.of_ret rfl)

theorem point1_tactical_body8 (r0 r1 : Nat) :
    SafeReturns body8 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 8 + (r1 + 8)) := by
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  exact SafeReturns.of_step rfl (SafeReturns.of_ret rfl)

theorem point1_tactical_body12 (r0 r1 : Nat) :
    SafeReturns body12 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 12 + (r1 + 12)) := by
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  refine stepChainBlock rfl rfl rfl rfl ?_
  exact SafeReturns.of_step rfl (SafeReturns.of_ret rfl)

-- Point 2: Universal Lowering Pass (`lowerToPure` running `computePlan` in kernel)
theorem point2_lowerToPure_body4 (r0 r1 : Nat) :
    SafeReturns body4 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 4 + (r1 + 4)) :=
  evalSym_step_sound (computePlan body4) body4 _ _ rfl

theorem point2_lowerToPure_body8 (r0 r1 : Nat) :
    SafeReturns body8 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 8 + (r1 + 8)) :=
  evalSym_step_sound (computePlan body8) body8 _ _ rfl

theorem point2_lowerToPure_body12 (r0 r1 : Nat) :
    SafeReturns body12 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 12 + (r1 + 12)) :=
  evalSym_step_sound (computePlan body12) body12 _ _ rfl

-- Point 3: Pre-Emitted Hint Validator (`evalSym plan` bypassing `computePlan`)
theorem point3_evalSym_body4 (r0 r1 : Nat) :
    SafeReturns body4 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 4 + (r1 + 4)) :=
  evalSym_step_sound plan4 body4 _ _ rfl

theorem point3_evalSym_body8 (r0 r1 : Nat) :
    SafeReturns body8 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 8 + (r1 + 8)) :=
  evalSym_step_sound plan8 body8 _ _ rfl

theorem point3_evalSym_body12 (r0 r1 : Nat) :
    SafeReturns body12 ⟨r0, r1, 0, 0, 0, 0, false, 0, 0⟩ (r0 + 12 + (r1 + 12)) :=
  evalSym_step_sound plan12 body12 _ _ rfl

-- Point 4: Pre-Proved Multi-Pass Pipeline vs. Per-Function Chaining
theorem point4_unchained_body12 :
    Abstracts PureLang MirLang (π_norm ∘ π_pure)
      (evalSym plan12 (normalizeBody body12)) body12 :=
  pass_trans (fun _ _ h => h) (evalSym_sound plan12 (normalizeBody body12)) (normalizeBody_sound body12)

theorem point4_preproved_pipeline_body12 :
    Abstracts PureLang MirLang (π_norm ∘ π_pure)
      (evalSym plan12 (normalizeBody body12)) body12 :=
  pipeline_sound plan12 body12

-- Bonus: Bounded While-Loop Verification via Pre-Proved `.whileLoop` Combinator
def loopSumBody : MirBody := {
  blocks := [
    { stmts := [.assignConst 3 10, .assignLt 2 1 3]
      term := .switchInt 2 2 1 },
    { stmts := [.assignConst 3 1, .assignAdd 0 0 3, .assignAdd 1 1 3]
      term := .goto 0 },
    { stmts := []
      term := .return_ 0 }
  ]
}

def loopSumPlan : TransPlan :=
  .whileLoop 12 [true, true] [true, true, true, false] (.ret 0)

theorem loopSum_verified_by_rfl :
    SafeReturns loopSumBody ⟨0, 0, 0, 0, 0, 0, false, 0, 0⟩ 10 :=
  evalSym_step_sound loopSumPlan loopSumBody _ _ rfl

/-- **Pre-Proved Symbolic Loop Combinator (`symbolicWhile_sound`)**:
    Eliminates per-function induction over fuel when the loop bound `bound : Nat`
    is symbolic (`∀ n : Nat`). Given any state family `inv : Nat → MirState`
    such that:
    1. For `k < bound`, `evalLinearSteps condSteps` reaches a `switchInt` that
       takes the loop-body branch and `evalLinearSteps bodySteps` advances
       `inv (k + 1)` to `inv k`, and
    2. At `k = 0`, `evalWhileLoop 1 condSteps bodySteps (evalSym exitPlan)`
       returns `some ret`,
    then `SafeReturns body (inv bound) ret` holds for all `bound : Nat`! -/
theorem symbolicWhileAux
    (body : MirBody) (condSteps bodySteps : List Bool) (exitPlan : TransPlan)
    (bound : Nat) (inv : Nat → MirState) (ret : Nat)
    (hStep : ∀ k, k < bound →
      ∃ sSw,
        evalLinearSteps condSteps body (inv (k + 1)) = some sSw ∧
        (∃ bb discr fBlk tBlk,
          body.blocks[sSw.blk]? = some bb ∧
          bb.stmts[sSw.stmtIdx]? = none ∧
          bb.term = .switchInt discr fBlk tBlk ∧
          (getReg sSw discr == 0) = false ∧
          evalLinearSteps bodySteps body { sSw with blk := tBlk, stmtIdx := 0 } = some (inv k)))
    (hBase : evalWhileLoop 1 condSteps bodySteps (evalSym exitPlan) body (inv 0) = some ret) :
    ∀ k, k ≤ bound → SafeReturns body (inv k) ret
  | 0, _ =>
    evalWhileLoop_sound 1 condSteps bodySteps (evalSym exitPlan) body
      (fun sExit r hr => evalSym_step_sound exitPlan body sExit r hr) (inv 0) ret hBase
  | k + 1, hle => by
    have ⟨sSw, hCond, bb, discr, fBlk, tBlk, hbb, hstmt, hterm, hbr, hBody⟩ := hStep k hle
    have hStepSw : evalMirStep body sSw = .step { sSw with blk := tBlk, stmtIdx := 0 } := by
      unfold evalMirStep; rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]; dsimp; rw [hbr]; rfl
    have ih := symbolicWhileAux body condSteps bodySteps exitPlan bound inv ret hStep hBase k (Nat.le_of_succ_le hle)
    have hBodySafe := evalLinearSteps_sound bodySteps body
      { sSw with blk := tBlk, stmtIdx := 0 } (inv k) ret hBody ih
    exact evalLinearSteps_sound condSteps body (inv (k + 1)) sSw ret hCond
      (SafeReturns.of_step hStepSw hBodySafe)

theorem symbolicWhile_sound
    (body : MirBody) (condSteps bodySteps : List Bool) (exitPlan : TransPlan)
    (bound : Nat) (inv : Nat → MirState) (ret : Nat)
    (hStep : ∀ k, k < bound →
      ∃ sSw,
        evalLinearSteps condSteps body (inv (k + 1)) = some sSw ∧
        (∃ bb discr fBlk tBlk,
          body.blocks[sSw.blk]? = some bb ∧
          bb.stmts[sSw.stmtIdx]? = none ∧
          bb.term = .switchInt discr fBlk tBlk ∧
          (getReg sSw discr == 0) = false ∧
          evalLinearSteps bodySteps body { sSw with blk := tBlk, stmtIdx := 0 } = some (inv k)))
    (hBase : evalWhileLoop 1 condSteps bodySteps (evalSym exitPlan) body (inv 0) = some ret) :
    SafeReturns body (inv bound) ret :=
  symbolicWhileAux body condSteps bodySteps exitPlan bound inv ret hStep hBase bound (Nat.le_refl bound)

/-- Symbolic-bound loop `while r1 < r0 { r1 := r1 + 1 } return r1`:
    verified for all `n : Nat` in 15 lines using `symbolicWhile_sound`. -/
def symCountBody : MirBody := {
  blocks := [
    -- bb0: r2 = (r1 < r0); switchInt r2 -> [0: bb2, otherwise: bb1]
    { stmts := [.assignLt 2 1 0]
      term := .switchInt 2 2 1 },
    -- bb1: r3 = 1; r1 = r1 + r3; r2 = 0; goto bb0
    { stmts := [.assignConst 3 1, .assignAdd 1 1 3, .assignConst 2 0]
      term := .goto 0 },
    -- bb2: return r1
    { stmts := []
      term := .return_ 1 }
  ]
}

def symCountInv (n : Nat) (k : Nat) : MirState :=
  ⟨n, n - k, 0, 1, 0, 0, false, 0, 0⟩

theorem symCount_verified (n : Nat) :
    SafeReturns symCountBody (symCountInv n n) n := by
  refine symbolicWhile_sound symCountBody [true] [true, true, true, false] (.ret 1) n (symCountInv n) n ?_ ?_
  · intro k hk
    have hlt : n - (k + 1) < n := Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) hk) (Nat.zero_lt_succ k)
    have hdec : decide (n - (k + 1) < n) = true := decide_eq_true hlt
    refine ⟨⟨n, n - (k + 1), 1, 1, 0, 0, false, 0, 1⟩, ?_,
      { stmts := [.assignLt 2 1 0], term := .switchInt 2 2 1 }, 2, 2, 1, rfl, rfl, rfl, rfl, ?_⟩
    · change some (MirState.mk n (n - (k + 1)) (if decide (n - (k + 1) < n) then 1 else 0) 1 0 0 false 0 1) = _
      rw [hdec]; rfl
    · change some (MirState.mk n (n - (k + 1) + 1) 0 1 0 0 false 0 0) =
        some (MirState.mk n (n - k) 0 1 0 0 false 0 0)
      have hsub : n - (k + 1) + 1 = n - k := by omega
      rw [hsub]
  · change (if (if decide (n - 0 < n) then 1 else 0) == 0 then some (n - 0) else _) = some n
    have hsub0 : n - 0 = n := Nat.sub_zero n
    rw [hsub0]
    have hdec0 : decide (n < n) = false := decide_eq_false (Nat.lt_irrefl n)
    rw [hdec0]; rfl

/-!
## 7. In-Kernel Replay & Proof-Term Size Measurement Harness
-/

def measureTheorem (env : Environment) (declName : Name) (iters : Nat) : IO String := do
  let some ci := env.find? declName
    | return s!"missing {declName}"
  let some val := ci.value? (allowOpaque := true)
    | return s!"no value for {declName}"
  let objs ← val.numObjs
  let bytes := val.sizeWithoutSharing
  let mut totalNs : Nat := 0
  for i in [0:iters] do
    let aliasName := declName.num i
    let aliasCi := ConstantInfo.thmInfo {
      name := aliasName
      levelParams := ci.levelParams
      type := ci.type
      value := val
      all := [aliasName]
    }
    let mut map : Std.HashMap Name ConstantInfo := {}
    map := map.insert aliasName aliasCi
    let t0 ← IO.monoNanosNow
    let _ ← env.toKernelEnv.replay map
    let t1 ← IO.monoNanosNow
    totalNs := totalNs + (t1 - t0)
  let avgUs := totalNs / (iters * 1000)
  return s!"{declName} | DAG nodes: {objs} | Tree size: {bytes} | Kernel check avg: {avgUs} us ({iters} runs)"

#eval show MetaM Unit from do
  let env ← getEnv
  IO.println "=== Pre-Proved Lowering Passes & Validators: Kernel Typechecking & Proof-Term Metrics ==="
  let names := [
    ``point1_tactical_body4,
    ``point1_tactical_body8,
    ``point1_tactical_body12,
    ``point2_lowerToPure_body4,
    ``point2_lowerToPure_body8,
    ``point2_lowerToPure_body12,
    ``point3_evalSym_body4,
    ``point3_evalSym_body8,
    ``point3_evalSym_body12,
    ``point4_unchained_body12,
    ``point4_preproved_pipeline_body12,
    ``loopSum_verified_by_rfl,
    ``symCount_verified
  ]
  for n in names do
    let line ← measureTheorem env n 10
    IO.println line

end ProbePreprovedPasses
