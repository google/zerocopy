-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.Data.Option.Basic
public import Trusted.Framework
public import Anneal.InitLemmas
public import Anneal.Framework.StepWp
public import Anneal.Hybrid
public import Anneal.Backend.CongruenceDagCtx

public section

/-!
# Checked Pass Composition and Contract Lifting (`Anneal.Backend.PassRefines`)

Connects `CongruenceDagCtx` and `checkBlockOpt` to `Anneal.Hybrid`:

1. **Direct `Anneal.Hybrid` Reuse:** Imports `RawOutcome`, `HybridErr`,
   `CertifiedGate`, `evalGate`, `firstAccepted`, `withFallback`,
   `foldHintSteps`, `gateCheckBounded`, and `certGateCut_sound` from
   `Anneal.Hybrid` (`0` duplicate gate definitions, `0` `._unsafe_rec`).
2. **Pass Composition (`PassRefines`, `verifiedPassToGate`,
   `composePassGates`):** Unifies directly verified total passes (`W = Unit`)
   with certificate-checked passes, packaging intermediate representations
   inside composite witnesses (`M × W1 × W2`).
3. **Conditional Contract Lifting (`liftContractAlongRefinement`):** Transfers
   `SimpleContract` properties (`pre`, `terminates`, `noAbort`, `postReturn`)
   along `SemRefinesUnder EntryPre` whenever `c.pre` implies `EntryPre`.
4. **Candidate-Filtering Block Gate (`blockOptGate`):** Filters
   `SourceBlockUnit.candidates` through `extractProvenFacts` inside `check` so
   `fuzz` and `sorryStub` entries are ignored structurally, establishing
   `SemRefinesUnder (SourceEntryPre src)` with gate precondition `True`.
-/

namespace Anneal.Backend

open Trusted.Framework Anneal.InitLemmas Anneal.Hybrid

/-! ## 1. Verified and Certificate-Checked Pass Composition -/

/-- Specification predicate shared by `CertifiedGate` checkers and directly
verified passes. -/
@[expose] def PassRefines {X Y E : Type} (Pre : X → Prop)
    (Spec : X → Y → Prop) (runPass : X → Except E Y) : Prop :=
  ∀ x y, Pre x → runPass x = .ok y → Spec x y

/-- A total pass proved sound directly without an external witness. -/
structure VerifiedPass (X Y : Type) (Pre : X → Prop) (Spec : X → Y → Prop) where
  run : X → Y
  sound : ∀ x, Pre x → Spec x (run x)

/-- Lift a `VerifiedPass` (`W := Unit`, `maxWitness := 0`) into a
`CertifiedGate` over `beqY` so verified and certificate-checked passes compose
through the same combinators. -/
@[expose] def verifiedPassToGate {X Y : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (vp : VerifiedPass X Y Pre Spec)
    (beqY : Y → Y → Bool) (hBeq : ∀ a b, beqY a b = true → a = b) :
    CertifiedGate X Y Unit Pre Spec where
  maxWitness := fun _ => 0
  wSize := fun _ => 0
  check := fun x y _ => beqY y (vp.run x)
  sound := fun x y _ hPre _ hChk => by
    rw [hBeq y (vp.run x) hChk]
    exact vp.sound x hPre

theorem evalGate_passRefines {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec)
    (prod : X → RawOutcome E Y W) :
    PassRefines Pre Spec (fun x => evalGate g x (prod x)) :=
  fun x y hPre hOk => evalGate_sound g x (prod x) y hPre hOk

theorem verifiedPass_passRefines {X Y E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (vp : VerifiedPass X Y Pre Spec) :
    PassRefines Pre Spec (fun x => (Except.ok (vp.run x) : Except E Y)) :=
  fun x y hPre hOk => by
    injection hOk with hEq
    rw [← hEq]
    exact vp.sound x hPre

/-- Sequential gate composition across distinct representations (`X -> M -> Z`),
packaging intermediate value `m : M` inside composite witness `M × W1 × W2`. -/
@[expose] def composePassGates {X M Z W1 W2 : Type}
    {PreX : X → Prop} {PreM : M → Prop}
    {R1 : X → M → Prop} {R2 : M → Z → Prop} {R13 : X → Z → Prop}
    (g1 : CertifiedGate X M W1 PreX (fun x m => PreM m ∧ R1 x m))
    (g2 : CertifiedGate M Z W2 PreM R2)
    (midSize : M → Nat)
    (maxMidPlusW2 : X → Nat)
    (hTrans : ∀ x m z, R1 x m → R2 m z → R13 x z) :
    CertifiedGate X Z (M × W1 × W2) PreX R13 where
  maxWitness := fun x => g1.maxWitness x + maxMidPlusW2 x
  wSize := fun mw => g1.wSize mw.2.1 + midSize mw.1 + g2.wSize mw.2.2
  check := fun x z mw =>
    Nat.ble (g1.wSize mw.2.1) (g1.maxWitness x) &&
    Nat.ble (g2.wSize mw.2.2) (g2.maxWitness mw.1) &&
    g1.check x mw.1 mw.2.1 &&
    g2.check mw.1 z mw.2.2
  sound := by
    intro x z mw hPreX _ hChk
    have h2Chk := bool_and_right hChk
    have c3 := bool_and_left hChk
    have h1Chk := bool_and_right c3
    have c2 := bool_and_left c3
    have h2Cap := Nat.le_of_ble_eq_true (bool_and_right c2)
    have h1Cap := Nat.le_of_ble_eq_true (bool_and_left c2)
    have ⟨hPreM, hR1⟩ := g1.sound x mw.1 mw.2.1 hPreX h1Cap h1Chk
    have hR2 := g2.sound mw.1 z mw.2.2 hPreM h2Cap h2Chk
    exact hTrans x mw.1 z hR1 hR2

/-! ## 2. Conditional Behavioral Contract Lifting (`SemRefinesUnder`) -/

/-- Behavioral contract over `ExecOutcome` covering input precondition `pre`,
termination (`effects.terminates`), absence of panic abort (`effects.noAbort`),
and return postcondition `postReturn`. -/
structure SimpleContract (Q Val Mem : Type) where
  pre : Q → Prop
  effects : EffectMask
  postReturn : Q → Val → Mem → Prop

@[expose] def SatisfiesContract {Q Val Mem : Type}
    (sem : Q → ExecOutcome Val Mem → Prop)
    (c : SimpleContract Q Val Mem) : Prop :=
  ∀ q, c.pre q →
    (¬ sem q .faultUB) ∧
    (c.effects.terminates = true → ¬ sem q .diverged) ∧
    (∀ m, sem q (.aborted m) → c.effects.noAbort = false) ∧
    (∀ v m, sem q (.returned v m) → c.postReturn q v m)

/-- Transfer a `SimpleContract` from `semSrc` to `semTgt` along
`SemRefinesUnder EntryPre` whenever `c.pre` entails `EntryPre`. -/
theorem liftContractAlongRefinement {Q Val Mem : Type}
    {EntryPre : Q → Prop}
    {semSrc semTgt : Q → ExecOutcome Val Mem → Prop}
    {c : SimpleContract Q Val Mem}
    (hImpl : ∀ q, c.pre q → EntryPre q)
    (hSrc : SatisfiesContract semSrc c)
    (hRef : SemRefinesUnder EntryPre semSrc semTgt) :
    SatisfiesContract semTgt c := by
  intro q hPre
  have ⟨hSrcNoUb, hSrcTerm, hSrcAbort, hSrcRet⟩ := hSrc q hPre
  have ⟨hTgtNoUb, hSub⟩ := hRef q (hImpl q hPre) hSrcNoUb
  exact ⟨hTgtNoUb,
    fun hTerm hDiv => hSrcTerm hTerm (hSub .diverged hDiv),
    fun m hAb => hSrcAbort m (hSub (.aborted m) hAb),
    fun v m hRet => hSrcRet v m (hSub (.returned v m) hRet)⟩

/-! ## 3. Candidate-Filtering Expression-Block `CertifiedGate` -/

/-- Guarded expression-block input carrying assertion `guards`, expression DAG
`arena`, source return node `srcRetId`, and tier-tagged `candidates`. -/
structure SourceBlockUnit where
  guards : List GuardCond
  arena : List DagNode
  srcRetId : Nat
  candidates : List CandidateFact

/-- Candidate output block carrying remaining `guardsOut`, `arenaOut`, and
selected return node `retId`. -/
structure CompiledBlockUnit where
  guardsOut : List GuardCond
  arenaOut : List DagNode
  retId : Nat

@[expose] def evalSourceBlockUnit (src : SourceBlockUnit) :
    (Nat → Nat) → ExecOutcome Nat Unit → Prop :=
  evalBlockWithGuards src.guards src.arena src.srcRetId

@[expose] def evalCompiledBlockUnit (u : CompiledBlockUnit) :
    (Nat → Nat) → ExecOutcome Nat Unit → Prop :=
  evalBlockWithGuards u.guardsOut u.arenaOut u.retId

/-- Per-input entry precondition induced by the `.proven` subset of
`src.candidates`. -/
@[expose] def SourceEntryPre (src : SourceBlockUnit) (env : Nat → Nat) : Prop :=
  EntryFactsHold src.arena (extractProvenFacts src.candidates) env

private theorem list_eq_of_nthOpt_eq {α : Type} :
    ∀ (xs ys : List α),
      xs.length = ys.length →
      (∀ k, k < ys.length → listNthOpt xs k = listNthOpt ys k) →
      xs = ys
  | [] => fun ys hLen _ => by
    cases ys with
    | nil => rfl
    | cons _ _ => nomatch hLen
  | _ :: xs' => fun ys hLen hAt => by
    cases ys with
    | nil => nomatch hLen
    | cons _ ys' =>
      have h0 := hAt 0 (Nat.zero_lt_succ _)
      dsimp only [listNthOpt] at h0
      injection h0 with hXY
      have hTailLen : xs'.length = ys'.length := Nat.succ.inj hLen
      have hTailAt :
          ∀ k, k < ys'.length → listNthOpt xs' k = listNthOpt ys' k :=
        fun k hk => hAt (k + 1) (Nat.succ_lt_succ hk)
      rw [hXY, list_eq_of_nthOpt_eq xs' ys' hTailLen hTailAt]

@[expose] def checkArenaNodesEq (a1 a2 : List DagNode)
    (n : Nat) : Bool :=
  List.foldr
    (fun p acc =>
      match listNthOpt a1 p with
      | none => false
      | some d1 =>
        match listNthOpt a2 p with
        | none => false
        | some d2 =>
          SsaOp.beq d1.op d2.op && natListBeq d1.args d2.args && acc)
    true
    (@Nat.rec (fun _ => List Nat) [] (fun k xs => k :: xs) n)

private theorem checkArenaNodesEq_sound (a1 a2 : List DagNode) :
    ∀ (n : Nat),
      checkArenaNodesEq a1 a2 n = true →
      ∀ (k : Nat), k < n → listNthOpt a1 k = listNthOpt a2 k :=
  @Nat.rec
    (fun n =>
      checkArenaNodesEq a1 a2 n = true →
      ∀ k, k < n → listNthOpt a1 k = listNthOpt a2 k)
    (fun _ _ hk => absurd hk (Nat.not_lt_zero _))
    (fun m ih hFold k hk => by
      revert hFold
      change
        (match listNthOpt a1 m with
         | none => false
         | some d1 =>
           match listNthOpt a2 m with
           | none => false
           | some d2 =>
             SsaOp.beq d1.op d2.op && natListBeq d1.args d2.args &&
               checkArenaNodesEq a1 a2 m) = true → _
      cases hO : listNthOpt a1 m with
      | none => intro h; cases h
      | some d1 =>
        dsimp only
        cases hS : listNthOpt a2 m with
        | none => intro h; cases h
        | some d2 =>
          dsimp only
          intro hFold
          cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
          | inl hEqK =>
            rw [hEqK, hO, hS]
            have hPair := bool_and_left hFold
            have hOp := ssaOp_eq_of_beq (bool_and_left hPair)
            have hAr := eq_of_natListBeq (bool_and_right hPair)
            cases d1 with
            | mk op1 args1 =>
              cases d2 with
              | mk op2 args2 =>
                dsimp only at hOp hAr
                rw [hOp, hAr]
          | inr hLtM =>
            exact ih (bool_and_right hFold) k hLtM)

/-- `CertifiedGate` for guarded expression-block optimization: filters
`src.candidates` through `extractProvenFacts` before invoking `checkBlockOpt`,
capping proof traces at `maxStepsPerNode * (arena.length + 1)` with gate
precondition `True`. -/
@[expose] def blockOptGate (maxStepsPerNode : Nat) :
    CertifiedGate SourceBlockUnit CompiledBlockUnit (List DagStep)
      (fun _ => True)
      (fun src out =>
        SemRefinesUnder (SourceEntryPre src)
          (evalSourceBlockUnit src) (evalCompiledBlockUnit out)) where
  maxWitness := fun src => maxStepsPerNode * (src.arena.length + 1)
  wSize := List.length
  check := fun src out steps =>
    guardListBeq out.guardsOut [] &&
    checkBlockOpt src.guards src.arena (extractProvenFacts src.candidates)
      steps src.srcRetId out.retId &&
    Nat.beq out.arenaOut.length src.arena.length &&
    checkArenaNodesEq out.arenaOut src.arena src.arena.length
  sound := by
    intro src out steps _ _ hChk
    have hNodes := bool_and_right hChk
    have c2 := bool_and_left hChk
    have hLenEq := nat_eq_of_beq (bool_and_right c2)
    have c1 := bool_and_left c2
    have hOpt := bool_and_right c1
    have hEmptyG := eq_of_guardListBeq out.guardsOut [] (bool_and_left c1)
    have hArenaEq : out.arenaOut = src.arena :=
      list_eq_of_nthOpt_eq out.arenaOut src.arena hLenEq
        (checkArenaNodesEq_sound out.arenaOut src.arena src.arena.length hNodes)
    have hSem := checkBlockOpt_sound src.guards src.arena
      (extractProvenFacts src.candidates) steps src.srcRetId out.retId hOpt
    dsimp only [evalCompiledBlockUnit, evalSourceBlockUnit, SourceEntryPre]
    rw [hEmptyG, hArenaEq]
    exact hSem

/-- Unmodified identity fallback pass: preserves `guards` and `srcRetId`
unchanged, proved sound directly without invoking `blockOptGate`. -/
@[expose] def baselineIdentityPass :
    VerifiedPass SourceBlockUnit CompiledBlockUnit (fun _ => True)
      (fun src out =>
        SemRefinesUnder (SourceEntryPre src)
          (evalSourceBlockUnit src) (evalCompiledBlockUnit out)) where
  run := fun src =>
    { guardsOut := src.guards
      arenaOut := src.arena
      retId := src.srcRetId }
  sound := fun src _ => semRefinesUnder_refl (SourceEntryPre src) _

/-- Structural Boolean equality on `CompiledBlockUnit` for `verifiedPassToGate`.
-/
@[expose] def CompiledBlockUnit.beq (u1 u2 : CompiledBlockUnit) : Bool :=
  guardListBeq u1.guardsOut u2.guardsOut &&
  Nat.beq u1.retId u2.retId &&
  Nat.beq u1.arenaOut.length u2.arenaOut.length &&
  checkArenaNodesEq u1.arenaOut u2.arenaOut u2.arenaOut.length

theorem compiledBlockUnit_eq_of_beq (u1 u2 : CompiledBlockUnit)
    (h : CompiledBlockUnit.beq u1 u2 = true) : u1 = u2 := by
  have hNodes := bool_and_right h
  have c2 := bool_and_left h
  have hLen := nat_eq_of_beq (bool_and_right c2)
  have c1 := bool_and_left c2
  have hRet := nat_eq_of_beq (bool_and_right c1)
  have hGs := eq_of_guardListBeq u1.guardsOut u2.guardsOut (bool_and_left c1)
  have hAr : u1.arenaOut = u2.arenaOut :=
    list_eq_of_nthOpt_eq u1.arenaOut u2.arenaOut hLen
      (checkArenaNodesEq_sound u1.arenaOut u2.arenaOut u2.arenaOut.length
        hNodes)
  cases u1 with
  | mk g1 a1 r1 =>
    cases u2 with
    | mk g2 a2 r2 =>
      dsimp only at hGs hAr hRet
      rw [hGs, hAr, hRet]

end Anneal.Backend

end
