-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanization of Multi-Profile `.anneal-mir` Subsumption (`overflow-checks`, `debug-assertions`, and `panic=unwind/abort`) in Lean v4.34.1

Mechanizes:
1. The 3-flag `.anneal-mir` profile lattice `ProfileConfig { overflowChecks,
   debugAssertions, panicAbort }` ($2^3 = 8$ profiles);
2. Paired `Runtime(PostCleanup)` MIR operational semantics (`MirStmt`, `evalStmt`,
   `evalProg`) modeling `AddWithOverflow + Assert(!ovf)` vs. wrapping `Add`
   (`compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs:456-479`),
   `debug_assert!` guard diamonds vs. release no-ops, and `UnwindAction::Cleanup`
   vs. `UnwindAction::Terminate` (`abort_unwinding_calls.rs:133-136`);
3. The syntactic Paired Profile Structural Diff Checker (`checkProfileSubsumption`);
4. The three individual axis theorems (`CheckedImpliesWrapping_sound`,
   `DebugAssertImpliesRelease_sound`, `UnwindImpliesAbort_sound`) and the
   composed 8-profile theorem (`MasterProfileSubsumption_sound`), proving that
   any `VerifyNoPanic P Q` theorem discharged once on the strictest profile
   `(overflow-checks=on, debug-assertions=on, panic=unwind)` automatically holds
   on `(overflow-checks=off, debug-assertions=off, panic=abort)`;
5. Negative soundness test (`sideEffectingDebugAssert_subsumption_rejected`)
   rejecting side-effecting `debug_assert!` / `#[cfg(debug_assertions)]` state
   mutations.
-/

namespace MirProfileSubsumptionProbe

/-- The three profile flags that affect `Runtime(PostCleanup)` MIR generation
    (`compiler/rustc_mir_transform/src/lib.rs`). -/
structure ProfileConfig where
  overflowChecks  : Bool
  debugAssertions : Bool
  panicAbort      : Bool
  deriving DecidableEq, Repr

/-- Strictest verification profile: `(overflow-checks=on, debug-assertions=on, panic=unwind)`. -/
def strictProfile : ProfileConfig :=
  { overflowChecks := true, debugAssertions := true, panicAbort := false }

/-- Production release profile: `(overflow-checks=off, debug-assertions=off, panic=abort)`. -/
def releaseProfile : ProfileConfig :=
  { overflowChecks := false, debugAssertions := false, panicAbort := true }

/-- Subsumption ordering on `ProfileConfig`: `strict` subsumes `target` when
    `strict` enables at least every check that `target` enables (`target.overflowChecks →
    strict.overflowChecks`, `target.debugAssertions → strict.debugAssertions`,
    `strict.panicAbort → target.panicAbort`). -/
def configSubsumes (strictCfg targetCfg : ProfileConfig) : Bool :=
  (!targetCfg.overflowChecks || strictCfg.overflowChecks) &&
  (!targetCfg.debugAssertions || strictCfg.debugAssertions) &&
  (!strictCfg.panicAbort || targetCfg.panicAbort)

/-- Execution outcome of a `Runtime(PostCleanup)` MIR statement or body on state `Nat`:
    - `ok s`: normal termination in state `s`;
    - `panicUnwind`: assertion failure or callee unwind reaching `UnwindResume`;
    - `panicAbort`: process termination via `UnwindAction::Terminate`. -/
inductive MirOutcome where
  | ok (st : Nat)
  | panicUnwind
  | panicAbort
  deriving DecidableEq, Repr

/-- Canonical `Runtime(PostCleanup)` MIR statement/terminator constructs across
    profiles (`modulus = 2^64` modeled by `bound : Nat`). -/
inductive MirNode where
  | pureAssign (delta : Nat)
  | checkedAdd (delta bound : Nat) (abortOnPanic : Bool)
  | wrappingAdd (delta bound : Nat)
  | pureDebugAssert (minVal : Nat) (abortOnPanic : Bool)
  | sideEffectDebugAssert (delta minVal : Nat) (abortOnPanic : Bool)
  | noopDebugAssert
  | callWithUnwind (fails : Bool) (delta : Nat)
  | callWithTerminate (fails : Bool) (delta : Nat)
  deriving DecidableEq, Repr

def evalNode (st : Nat) (node : MirNode) : MirOutcome :=
  match node with
  | .pureAssign delta =>
    .ok (st + delta)
  | .checkedAdd delta bound abortOnPanic =>
    if st + delta < bound then
      .ok ((st + delta) % bound)
    else if abortOnPanic then
      .panicAbort
    else
      .panicUnwind
  | .wrappingAdd delta bound =>
    .ok ((st + delta) % bound)
  | .pureDebugAssert minVal abortOnPanic =>
    if minVal ≤ st then
      .ok st
    else if abortOnPanic then
      .panicAbort
    else
      .panicUnwind
  | .sideEffectDebugAssert delta minVal abortOnPanic =>
    let st' := st + delta
    if minVal ≤ st' then
      .ok st'
    else if abortOnPanic then
      .panicAbort
    else
      .panicUnwind
  | .noopDebugAssert =>
    .ok st
  | .callWithUnwind fails delta =>
    if fails then .panicUnwind else .ok (st + delta)
  | .callWithTerminate fails delta =>
    if fails then .panicAbort else .ok (st + delta)

def evalProg (st : Nat) (prog : List MirNode) : MirOutcome :=
  match prog with
  | [] => .ok st
  | n :: ns =>
    match evalNode st n with
    | .ok st'      => evalProg st' ns
    | .panicUnwind => .panicUnwind
    | .panicAbort  => .panicAbort

/-- Anneal's `Trusted.VerificationResult` (`NoPanic` + postcondition `Q`):
    For every initial state `st` satisfying precondition `P st`, `evalProg st prog`
    succeeds without panicking or aborting (`.ok stFinal`) and satisfies `Q st stFinal`. -/
def VerifyNoPanic (P : Nat → Prop) (Q : Nat → Nat → Prop) (prog : List MirNode) : Prop :=
  ∀ st, P st → ∃ stFinal, evalProg st prog = .ok stFinal ∧ Q st stFinal

/-!
## 1. Structural Profile Subsumption Checker (`checkNodeSubsumption` & `checkProfileSubsumption`)
-/

/-- Verifies that a single node `targetNode` in the looser profile is a sound
    quotient of `strictNode` in the stricter profile:
    - Identical `pureAssign`;
    - `checkedAdd` -> `wrappingAdd` (or `checkedAdd` with `abortOnPanic` toggled);
    - `pureDebugAssert` -> `noopDebugAssert` (side-effecting `sideEffectDebugAssert`
      is strictly rejected when lowered to `noopDebugAssert`!);
    - `callWithUnwind` -> `callWithTerminate`. -/
def checkNodeSubsumption (strictNode targetNode : MirNode) : Bool :=
  match strictNode, targetNode with
  | .pureAssign d1, .pureAssign d2 => d1 == d2
  | .checkedAdd d1 b1 _, .checkedAdd d2 b2 _ => (d1 == d2) && (b1 == b2)
  | .checkedAdd d1 b1 _, .wrappingAdd d2 b2 => (d1 == d2) && (b1 == b2)
  | .wrappingAdd d1 b1, .wrappingAdd d2 b2 => (d1 == d2) && (b1 == b2)
  | .pureDebugAssert m1 _, .pureDebugAssert m2 _ => m1 == m2
  | .pureDebugAssert _ _, .noopDebugAssert => true
  | .noopDebugAssert, .noopDebugAssert => true
  | .callWithUnwind f1 d1, .callWithUnwind f2 d2 => (f1 == f2) && (d1 == d2)
  | .callWithUnwind f1 d1, .callWithTerminate f2 d2 => (f1 == f2) && (d1 == d2)
  | .callWithTerminate f1 d1, .callWithTerminate f2 d2 => (f1 == f2) && (d1 == d2)
  | _, _ => false

def checkProfileSubsumption (strictProg targetProg : List MirNode) : Bool :=
  match strictProg, targetProg with
  | [], [] => true
  | s :: ss, t :: ts => checkNodeSubsumption s t && checkProfileSubsumption ss ts
  | _, _ => false

/-!
## 2. Axis-by-Axis and Master Subsumption Soundness Theorems
-/

/-- Key lemma: if `checkNodeSubsumption strictNode targetNode = true` and
    `evalNode st strictNode = .ok st'`, then `evalNode st targetNode = .ok st'`
    (the exact same post-state `st'` is produced!). -/
theorem evalNode_subsumption_preserves_ok
    (st st' : Nat) (strictNode targetNode : MirNode)
    (hSub : checkNodeSubsumption strictNode targetNode = true)
    (hOk : evalNode st strictNode = .ok st') :
    evalNode st targetNode = .ok st' := by
  match strictNode, targetNode with
  | .pureAssign d1, .pureAssign d2 =>
    simp [checkNodeSubsumption] at hSub
    subst hSub
    exact hOk
  | .checkedAdd d1 b1 a1, .checkedAdd d2 b2 a2 =>
    simp [checkNodeSubsumption] at hSub
    rcases hSub with ⟨hd, hb⟩
    subst hd; subst hb
    dsimp [evalNode] at hOk ⊢
    by_cases hLt : st + d1 < b1
    · simp [hLt] at hOk ⊢
      exact hOk
    · simp [hLt] at hOk
      cases a1 <;> simp at hOk
  | .checkedAdd d1 b1 a1, .wrappingAdd d2 b2 =>
    simp [checkNodeSubsumption] at hSub
    rcases hSub with ⟨hd, hb⟩
    subst hd; subst hb
    dsimp [evalNode] at hOk ⊢
    by_cases hLt : st + d1 < b1
    · simp [hLt] at hOk ⊢
      exact hOk
    · simp [hLt] at hOk
      cases a1 <;> simp at hOk
  | .wrappingAdd d1 b1, .wrappingAdd d2 b2 =>
    simp [checkNodeSubsumption] at hSub
    rcases hSub with ⟨hd, hb⟩
    subst hd; subst hb
    exact hOk
  | .pureDebugAssert m1 a1, .pureDebugAssert m2 a2 =>
    simp [checkNodeSubsumption] at hSub
    subst hSub
    dsimp [evalNode] at hOk ⊢
    by_cases hLe : m1 ≤ st
    · simp [hLe] at hOk ⊢
      exact hOk
    · simp [hLe] at hOk
      cases a1 <;> simp at hOk
  | .pureDebugAssert m1 a1, .noopDebugAssert =>
    dsimp [evalNode] at hOk ⊢
    by_cases hLe : m1 ≤ st
    · simp [hLe] at hOk ⊢
      exact hOk
    · simp [hLe] at hOk
      cases a1 <;> simp at hOk
  | .noopDebugAssert, .noopDebugAssert =>
    exact hOk
  | .callWithUnwind f1 d1, .callWithUnwind f2 d2 =>
    simp [checkNodeSubsumption] at hSub
    rcases hSub with ⟨hf, hd⟩
    subst hf; subst hd
    exact hOk
  | .callWithUnwind f1 d1, .callWithTerminate f2 d2 =>
    simp [checkNodeSubsumption] at hSub
    rcases hSub with ⟨hf, hd⟩
    subst hf; subst hd
    dsimp [evalNode] at hOk ⊢
    cases f1
    · exact hOk
    · contradiction
  | .callWithTerminate f1 d1, .callWithTerminate f2 d2 =>
    simp [checkNodeSubsumption] at hSub
    rcases hSub with ⟨hf, hd⟩
    subst hf; subst hd
    exact hOk

/-- Multi-step trajectory preservation across `evalProg`. -/
theorem evalProg_subsumption_preserves_ok
    (st stFinal : Nat) (strictProg targetProg : List MirNode)
    (hSub : checkProfileSubsumption strictProg targetProg = true)
    (hOk : evalProg st strictProg = .ok stFinal) :
    evalProg st targetProg = .ok stFinal := by
  induction strictProg generalizing st targetProg with
  | nil =>
    cases targetProg with
    | nil => exact hOk
    | cons _ _ => contradiction
  | cons s ss ih =>
    cases targetProg with
    | nil => contradiction
    | cons t ts =>
      simp [checkProfileSubsumption] at hSub
      rcases hSub with ⟨hNode, hRest⟩
      dsimp [evalProg] at hOk ⊢
      cases hEvalS : evalNode st s with
      | panicUnwind => rw [hEvalS] at hOk; contradiction
      | panicAbort  => rw [hEvalS] at hOk; contradiction
      | ok stMid =>
        rw [hEvalS] at hOk
        have hEvalT := evalNode_subsumption_preserves_ok st stMid s t hNode hEvalS
        rw [hEvalT]
        exact ih stMid ts hRest hOk

/-- Theorem 1 (`CheckedImpliesWrapping_sound`):
    Discharging `VerifyNoPanic P Q` on `[.checkedAdd delta bound false]`
    (`overflow-checks=on`) automatically certifies `[.wrappingAdd delta bound]`
    (`overflow-checks=off`). -/
theorem CheckedImpliesWrapping_sound
    (P : Nat → Prop) (Q : Nat → Nat → Prop) (delta bound : Nat)
    (hVerified : VerifyNoPanic P Q [.checkedAdd delta bound false]) :
    VerifyNoPanic P Q [.wrappingAdd delta bound] := by
  intro st hP
  rcases hVerified st hP with ⟨stFinal, hOk, hQ⟩
  refine ⟨stFinal, ?_, hQ⟩
  apply evalProg_subsumption_preserves_ok st stFinal
    [.checkedAdd delta bound false] [.wrappingAdd delta bound]
  · simp [checkProfileSubsumption, checkNodeSubsumption]
  · exact hOk

/-- Theorem 2 (`DebugAssertImpliesRelease_sound`):
    Discharging `VerifyNoPanic P Q` on `[.pureDebugAssert minVal false]`
    (`debug-assertions=on`) automatically certifies `[.noopDebugAssert]`
    (`debug-assertions=off`). -/
theorem DebugAssertImpliesRelease_sound
    (P : Nat → Prop) (Q : Nat → Nat → Prop) (minVal : Nat)
    (hVerified : VerifyNoPanic P Q [.pureDebugAssert minVal false]) :
    VerifyNoPanic P Q [.noopDebugAssert] := by
  intro st hP
  rcases hVerified st hP with ⟨stFinal, hOk, hQ⟩
  refine ⟨stFinal, ?_, hQ⟩
  apply evalProg_subsumption_preserves_ok st stFinal
    [.pureDebugAssert minVal false] [.noopDebugAssert]
  · rfl
  · exact hOk

/-- Theorem 3 (`UnwindImpliesAbort_sound`):
    Discharging `VerifyNoPanic P Q` on `[.callWithUnwind fails delta]`
    (`panic=unwind`) automatically certifies `[.callWithTerminate fails delta]`
    (`panic=abort`). -/
theorem UnwindImpliesAbort_sound
    (P : Nat → Prop) (Q : Nat → Nat → Prop) (fails : Bool) (delta : Nat)
    (hVerified : VerifyNoPanic P Q [.callWithUnwind fails delta]) :
    VerifyNoPanic P Q [.callWithTerminate fails delta] := by
  intro st hP
  rcases hVerified st hP with ⟨stFinal, hOk, hQ⟩
  refine ⟨stFinal, ?_, hQ⟩
  apply evalProg_subsumption_preserves_ok st stFinal
    [.callWithUnwind fails delta] [.callWithTerminate fails delta]
  · simp [checkProfileSubsumption, checkNodeSubsumption]
  · exact hOk

/-- Theorem 4 (`MasterProfileSubsumption_sound`):
    Whenever `checkProfileSubsumption strictProg targetProg = true`, a single
    Anneal proof `VerifyNoPanic P Q strictProg` on the strictest verification
    profile `(overflow-checks=on, debug-assertions=on, panic=unwind)` certifies
    `VerifyNoPanic P Q targetProg` on any looser profile, including production
    release `(overflow-checks=off, debug-assertions=off, panic=abort)`. -/
theorem MasterProfileSubsumption_sound
    (P : Nat → Prop) (Q : Nat → Nat → Prop)
    (strictProg targetProg : List MirNode)
    (hSub : checkProfileSubsumption strictProg targetProg = true)
    (hVerified : VerifyNoPanic P Q strictProg) :
    VerifyNoPanic P Q targetProg := by
  intro st hP
  rcases hVerified st hP with ⟨stFinal, hOk, hQ⟩
  exact ⟨stFinal, evalProg_subsumption_preserves_ok st stFinal strictProg targetProg hSub hOk, hQ⟩

/-!
## 3. Negative Soundness Test: Side-Effecting `debug_assert!` Rejected
-/

/-- Theorem 5 (`sideEffectingDebugAssert_subsumption_rejected`):
    If a `debug_assert!` or `#[cfg(debug_assertions)]` block mutates state
    (`.sideEffectDebugAssert 1 1` -> `.noopDebugAssert`), `checkProfileSubsumption`
    returns `false`. -/
theorem sideEffectingDebugAssert_subsumption_rejected :
    checkProfileSubsumption [.sideEffectDebugAssert 1 1 false] [.noopDebugAssert] = false := by
  rfl

#print axioms CheckedImpliesWrapping_sound
#print axioms DebugAssertImpliesRelease_sound
#print axioms UnwindImpliesAbort_sound
#print axioms MasterProfileSubsumption_sound
#print axioms sideEffectingDebugAssert_subsumption_rejected

end MirProfileSubsumptionProbe
