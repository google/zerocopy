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
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Framework.StepWp
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore
public import Anneal.Core.BlockTree

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.Framework.StepWp Anneal.MirWp
  Anneal.MirTotal

/-!
# Zero-`Prop`-Argument Stage Cuts and Compositional WP Rules (`Core.StageCut`)

Provides LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`) cutpoint
barriers and compositional weakest-precondition combinators over
`Anneal.MirWp.wpOutcomeState`:

1. `StepStageCut` (`@[irreducible]`, `0` `Prop` arguments) and `MirStageCut`:
   Generic fuel-bounded step-reachability barrier preventing `whnf` / `dsimp` /
   `rw` term blowup across multi-diamond joins (`2^m -> m`), paired with
   `MirStageCut.ofBlockTree` and `wpUntilCutStep_iff_exists_stepStageCut`.
2. `BoolCertCut` (`@[irreducible]`, `0` `Prop` arguments): Generic reflective
   certificate barrier sealing `check cert = true` with zero `Prop` arguments
   and constant-time seal/unseal/pairing soundness combinators.
3. `wlpOutcomeState` and `wpOutcomeState_conj_of_wlp_noDiv`: Two-pass
   conjunctive split separating safety/termination (`wpState`) from functional
   correctness (`wlpOutcomeState`) without re-proving step safety.
4. `twoTrackPost`, `cleanup_block_return_faults_unsupported`, `DropSpineCut`
   (`@[irreducible]`, `0` `Prop` arguments), and
   `wpOutcomeState_loop_early_return_sound`: Normal-vs-unwind postconditions,
   cleanup-return fault rejection, shared `O(K)` LIFO `StorageDead` spine cuts,
   and bounded loops with early-return (`?`) exit guards.

Why zero-`Prop`-argument barriers: Lean 4's `rw` (`kabstract` + `congrArg`) and
`simp` (`simpApp` -> `congrArgs`) descend into explicit `Prop` arguments even
beneath an `@[irreducible]` head constant (such as `Hold P` or
`Firewall tag P`). Carrying only computational data arguments inside
`@[irreducible]` cutpoint predicates (`StepStageCut`, `BoolCertCut`,
`DropSpineCut`) blocks tactic traversal into sealed obligations while keeping
every seal and unseal lemma linear-time and axiom-free.
-/

/-! ## Generic Zero-`Prop`-Argument `StepStageCut` and `wpUntilCutStep` -/

export Anneal.Framework.StepWp
  (StepStageCut StepStageCut.refl StepStageCut.step StepStageCut.fuel_mono
   StepStageCut.trans StepStageCut.congr_step wpUntilCutStep
   wpUntilCutStep_here wpUntilCutStep_step
   wpUntilCutStep_iff_exists_stepStageCut wpUntilCutStep_mono
   wpUntilCutStep_fuel_mono wpUntilCutStep_trans)

/-- Program-level `MirStageCut` specialization of `StepStageCut` to
`Trusted.MirSemantics.evalStep p 0`. -/
abbrev MirStageCut (p : Program) (fuel : Nat) (s₀ s₁ : State) : Prop :=
  StepStageCut (evalStep p 0) fuel s₀ s₁

/-- Lifts a `BlockTree`-accelerated `StepStageCut` into `MirStageCut
(bodyProg body)` whenever `tyEq` agrees with `MirTy.beq` and `bt` is valid. -/
theorem MirStageCut.ofBlockTree {tyEq : MirTy → MirTy → Bool}
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    {body : Body} {bt : BlockTree BasicBlock}
    (hValid : ValidBlockTree body.basicBlocks bt)
    {fuel : Nat} {s₀ s₁ : State}
    (hCut : StepStageCut (evalMirStepBlockTreeBy tyEq bt body) fuel s₀ s₁) :
    MirStageCut (bodyProg body) fuel s₀ s₁ :=
  (StepStageCut.congr_step
    (evalMirStepBlockTreeBy_eq_evalStep tyEq hTyEq hValid)).mp hCut

/-- Specialization of `MirStageCut.ofBlockTree` to `BlockTree.ofList
body.basicBlocks`. -/
theorem MirStageCut.ofBlockTreeOfList {tyEq : MirTy → MirTy → Bool}
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    {body : Body} {fuel : Nat} {s₀ s₁ : State}
    (hCut : StepStageCut
      (evalMirStepBlockTreeBy tyEq (BlockTree.ofList body.basicBlocks) body)
      fuel s₀ s₁) :
    MirStageCut (bodyProg body) fuel s₀ s₁ :=
  MirStageCut.ofBlockTree hTyEq (valid_blockTree_ofList body.basicBlocks) hCut

/-- Prepend a `MirStageCut` prefix onto `execOutcomeState`. -/
theorem execOutcomeState_of_mirStageCut {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {f₁ f₂ : Nat} {s₀ s₁ : State}
    (hCut : MirStageCut p f₁ s₀ s₁)
    (hCont : execOutcomeState p onDone onFault f₂ s₁) :
    execOutcomeState p onDone onFault (f₁ + f₂) s₀ :=
  execStepPred_of_stepStageCut hCut hCont

/-- Prepend a `MirStageCut` prefix onto `wpOutcomeState`. -/
theorem wpOutcomeState_of_mirStageCut {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {f₁ f₂ : Nat} {s₀ s₁ : State}
    (hCut : MirStageCut p f₁ s₀ s₁)
    (hCont : wpOutcomeState p onDone onFault f₂ s₁) :
    wpOutcomeState p onDone onFault (f₁ + f₂) s₀ :=
  wpStepPred_of_stepStageCut (c₀ := 0) (fun _ _ => Iff.rfl) hCut hCont

/-- Composes a `BlockTree`-accelerated `wpUntilCutStep` prefix with a
`wpOutcomeState` continuation on `bodyProg body`. -/
theorem wpOutcomeState_of_wpUntilCutBlockTree {tyEq : MirTy → MirTy → Bool}
    (hTyEq : ∀ a b, tyEq a b = MirTy.beq a b)
    {body : Body} {bt : BlockTree BasicBlock}
    (hValid : ValidBlockTree body.basicBlocks bt)
    {cut : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {f₁ f₂ : Nat} {s₀ : State}
    (hPre : wpUntilCutStep (evalMirStepBlockTreeBy tyEq bt body) cut f₁ s₀)
    (hCont : ∀ sc : State, cut sc →
      wpOutcomeState (bodyProg body) onDone onFault f₂ sc) :
    wpOutcomeState (bodyProg body) onDone onFault (f₁ + f₂) s₀ := by
  let ⟨s₁, hCut, hc⟩ := wpUntilCutStep_iff_exists_stepStageCut.mp hPre
  exact wpOutcomeState_of_mirStageCut
    (MirStageCut.ofBlockTree hTyEq hValid hCut) (hCont s₁ hc)

/-- Composes a `wpUntilCutStep (evalStep p 0)` prefix with a `wpOutcomeState`
continuation on `p`. -/
theorem wpOutcomeState_of_wpUntilCutMir {p : Program}
    {cut : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {f₁ f₂ : Nat} {s₀ : State}
    (hPre : wpUntilCutStep (evalStep p 0) cut f₁ s₀)
    (hCont : ∀ sc : State, cut sc → wpOutcomeState p onDone onFault f₂ sc) :
    wpOutcomeState p onDone onFault (f₁ + f₂) s₀ :=
  wpStepPred_of_wpUntilCutStep (c₀ := 0) (fun _ _ => Iff.rfl) hPre hCont

/-! ## Generic Zero-`Prop`-Argument Reflective Barrier (`BoolCertCut`) -/

export Anneal.Framework.StepWp
  (BoolCertCut BoolCertCut.seal BoolCertCut.unseal BoolCertCut.elim
   BoolCertCut.sound BoolCertCut.congr_check BoolCertCut.pair BoolCertCut.fst
   BoolCertCut.snd)

/-- Canary: sealing, pairing, and discharging via `BoolCertCut.sound` require
zero axioms and keep `BoolCertCut` opaque after sealing. -/
theorem boolCertCut_roundtrip_canary : (7 : Nat) = 7 ∧ (42 : Nat) = 42 := by
  let check : Nat × Nat → Bool := fun p => Nat.beq p.1 p.2
  have h1 : BoolCertCut check (7, 7) := BoolCertCut.seal check (7, 7) rfl
  have h2 : BoolCertCut check (42, 42) := BoolCertCut.seal check (42, 42) rfl
  have hPair :
      BoolCertCut (fun p : (Nat × Nat) × (Nat × Nat) => check p.1 && check p.2)
        ((7, 7), (42, 42)) :=
    BoolCertCut.pair h1 h2
  have hSound : ∀ p : Nat × Nat, check p = true → p.1 = p.2 :=
    fun p h => Nat.eq_of_beq_eq_true h
  exact ⟨BoolCertCut.sound hSound (BoolCertCut.fst hPair),
         BoolCertCut.sound hSound (BoolCertCut.snd hPair)⟩

/-! ## Two-Pass Safety / Functional-Spec Split (`wlpOutcomeState`) -/

/-- Weakest liberal precondition over `evalStep` (`0` `noncomputable`):
out-of-fuel defaults to `True` while every terminating or faulting path within
`fuel` must satisfy `onDone` / `onFault`. -/
@[expose] def wlpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (fuel : Nat) (s : State) : Prop :=
  wlpStepOutcome (ValidChoice p) (evalStep p) onDone onFault fuel s

/-- Whole-program weakest liberal precondition (`0` `noncomputable`). -/
@[expose] def wlpProg (p : Program) (fuel : Nat) (q : Query)
    (onDone : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => wlpOutcomeState p onDone (fun _ => True) fuel s₀

/-- Conjunctive split: combining total termination/safety (`wpOutcomeState`)
with partial functional correctness (`wlpOutcomeState`) yields conjunctive
total correctness without re-proving termination or fault absence. -/
theorem wpOutcomeState_conj_of_wlp_noDiv {p : Program}
    {onDone₁ onDone₂ : TerminalOut → Prop}
    {onFault₁ onFault₂ : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (hSafe : wpOutcomeState p onDone₁ onFault₁ fuel s)
    (hWlp : wlpOutcomeState p onDone₂ onFault₂ fuel s) :
    wpOutcomeState p (fun out => onDone₁ out ∧ onDone₂ out)
      (fun fk => onFault₁ fk ∧ onFault₂ fk) fuel s :=
  wpStepPred_conj_of_wlp hSafe hWlp

/-- Combines baseline `wpState p fuel s (fun _ => True)` with `wlpOutcomeState`
to establish `wpState p fuel s post`. -/
theorem wpState_of_wlp_and_safety {p : Program} {fuel : Nat} {s : State}
    {post : TerminalOut → Prop}
    (hSafe : wpState p fuel s (fun _ => True))
    (hWlp : wlpOutcomeState p post (fun _ => True) fuel s) :
    wpState p fuel s post :=
  wpOutcomeState_mono (fun _ hp => hp.2) (fun _ hf => hf.1)
    (wpOutcomeState_conj_of_wlp_noDiv hSafe hWlp)

/-- Whole-program two-pass combination of `wpProg` safety and `wlpProg`
functional correctness. -/
theorem wpProg_of_wlp_and_safety {p : Program} {fuel : Nat} {q : Query}
    {post : TerminalOut → Prop}
    (hSafe : wpProg p fuel q (fun _ => True))
    (hWlp : wlpProg p fuel q post) :
    wpProg p fuel q post := by
  unfold wpProg at hSafe
  unfold wlpProg at hWlp
  unfold wpProg
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at hSafe
    exact False.elim hSafe
  | ok s₀ =>
    rw [hInit] at hSafe hWlp
    exact wpState_of_wlp_and_safety hSafe hWlp

/-! ## Two-Track Postconditions, `DropSpineCut`, and Early-Return Loops -/

/-- Splits a `TerminalOut` postcondition into `(onRet, onUnwind)`. -/
@[expose] def twoTrackPost (onRet : Out → Prop) (onUnwind : CallerMemory → Prop) :
    TerminalOut → Prop
  | .returned out => onRet out
  | .unwound cm => onUnwind cm

/-- Two-track state-level weakest precondition forbidding faults (`0`
`noncomputable`). -/
@[expose] def wpTwoTrack (p : Program) (fuel : Nat) (s : State)
    (onRet : Out → Prop) (onUnwind : CallerMemory → Prop) : Prop :=
  wpOutcomeState p (twoTrackPost onRet onUnwind) (fun _ => False) fuel s

/-- Entering an empty `cleanup = true` entry block (`basicBlocks[0]`) whose
terminator is `TerminatorKind.return_` faults in 1 step with
`FaultKind.unsupported` and never reaches `.done`. -/
theorem cleanup_block_return_faults_unsupported
    (body : Body) (args : List Val) (bb₀ : BasicBlock)
    (hAdm : BodyStaticAdmitted (bodyProg body) body = true)
    (hArgs : ValidEntryArgs body args)
    (hBb₀ : Trusted.MirSemantics.getElem? body.basicBlocks 0 = some bb₀)
    (hStmts : bb₀.statements = [])
    (hTerm : bb₀.terminator = .return_)
    (hClean : bb₀.cleanup = true) :
    wpFaultProg (bodyProg body) 1 { args := args } .unsupported ∧
    ReachesResult (bodyProg body) { args := args } (.fault .unsupported) ∧
    ∀ out : TerminalOut,
      ¬ ReachesResult (bodyProg body) { args := args } (.done out) := by
  have hInit := initState_eq_ok (p := bodyProg body) rfl hAdm hArgs
  have hDefId : (bodyProg body).entryDefId = 0 := rfl
  rw [hDefId] at hInit
  have hStepFault :
      evalStep (bodyProg body) 0
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) =
      .fault .unsupported := by
    unfold mkState bodyProg evalStep
    dsimp only [Trusted.MirSemantics.getElem?]
    rw [hBb₀]
    cases bb₀ with
    | mk bS bT bC =>
      dsimp only at hStmts hTerm hClean
      subst hStmts; subst hTerm; subst hClean
      rfl
  have hWpFault :
      wpFaultProg (bodyProg body) 1 { args := args } .unsupported := by
    unfold wpFaultProg
    rw [hInit]
    exact ⟨⟨0, rfl⟩, fun c hc => by subst hc; rw [hStepFault]⟩
  have hClaim := reaches_fault_and_exclusive_of_wpFault_base
    (bodyProg body) { args := args } 1 .unsupported hWpFault
  exact ⟨hWpFault, hClaim.1, hClaim.2.2.1⟩

/-- True iff `slot` is `.dead` or `.immediate _` (so `deallocateLocal` is a
memory no-op). -/
@[expose] def slotNonIndirect (slot : LocalSlot) : Bool :=
  match slot with
  | .indirect _ => false
  | .dead | .immediate _ | .partialTuple _ => true

/-- True iff every slot in `ls` is non-indirect. -/
@[expose] def allSlotsNonIndirect (ls : List LocalSlot) : Bool :=
  ls.all slotNonIndirect

private theorem getElem?_nonIndirect_of_all {ls : List LocalSlot}
    (hAll : allSlotsNonIndirect ls = true) :
    ∀ {idx : Nat} {slot : LocalSlot},
      Trusted.MirSemantics.getElem? ls idx = some slot →
      slotNonIndirect slot = true := by
  induction ls with
  | nil => intro _ _ h; cases h
  | cons hd tl ih =>
    unfold allSlotsNonIndirect at hAll
    change (slotNonIndirect hd && tl.all slotNonIndirect) = true at hAll
    cases hHd : slotNonIndirect hd with
    | false => rw [hHd] at hAll; cases hAll
    | true =>
      rw [hHd, Bool.true_and] at hAll
      intro idx slot hGet
      cases idx with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact hHd
      | succ k => exact ih hAll hGet

private theorem allSlotsNonIndirect_set_dead {ls : List LocalSlot} :
    ∀ {idx : Nat} {ls' : List LocalSlot},
      allSlotsNonIndirect ls = true →
      Trusted.MirSemantics.setElem? ls idx .dead = some ls' →
      allSlotsNonIndirect ls' = true := by
  induction ls with
  | nil => intro _ _ _ hSet; cases hSet
  | cons hd tl ih =>
    intro idx ls' hAll hSet
    unfold allSlotsNonIndirect at hAll
    change (slotNonIndirect hd && tl.all slotNonIndirect) = true at hAll
    cases hHd : slotNonIndirect hd with
    | false => rw [hHd] at hAll; cases hAll
    | true =>
      rw [hHd, Bool.true_and] at hAll
      cases idx with
      | zero =>
        injection hSet with hEq
        subst hEq
        unfold allSlotsNonIndirect
        exact hAll
      | succ k =>
        dsimp only [Trusted.MirSemantics.setElem?] at hSet
        cases hSub : Trusted.MirSemantics.setElem? tl k .dead with
        | none => rw [hSub] at hSet; cases hSet
        | some tl' =>
          rw [hSub] at hSet
          injection hSet with hEq
          subst hEq
          have hSubAll := ih hAll hSub
          unfold allSlotsNonIndirect
          change (slotNonIndirect hd && tl'.all slotNonIndirect) = true
          rw [hHd, Bool.true_and]
          exact hSubAll

private theorem getElem?_some_of_lt {α : Type} :
    ∀ (xs : List α) {idx : Nat},
      idx < xs.length → ∃ v : α, Trusted.MirSemantics.getElem? xs idx = some v
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: tl, _ + 1, h => getElem?_some_of_lt tl (Nat.lt_of_succ_lt_succ h)

private theorem setElem?_some_of_lt {α : Type} :
    ∀ (xs : List α) {idx : Nat} (v : α),
      idx < xs.length →
      ∃ xs' : List α,
        Trusted.MirSemantics.setElem? xs idx v = some xs' ∧
        xs'.length = xs.length
  | [], _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: tl, 0, v, _ => ⟨v :: tl, rfl, rfl⟩
  | x :: tl, k + 1, v, h => by
    let ⟨tl', hSet, hLen⟩ :=
      setElem?_some_of_lt tl v (Nat.lt_of_succ_lt_succ h)
    refine ⟨x :: tl', ?_, congrArg Nat.succ hLen⟩
    dsimp only [Trusted.MirSemantics.setElem?]
    rw [hSet]

private theorem getElem?_setElem?_ne_of_some {α : Type} :
    ∀ {xs xs' : List α} {idx j : Nat} {v : α},
      j ≠ idx →
      Trusted.MirSemantics.setElem? xs idx v = some xs' →
      Trusted.MirSemantics.getElem? xs' j =
        Trusted.MirSemantics.getElem? xs j
  | [], _, _, _, _, _, hSet => by cases hSet
  | _ :: _, _, 0, 0, _, hNe, _ => False.elim (hNe rfl)
  | _ :: _, _, 0, _ + 1, _, _, hSet => by
    injection hSet with hEq
    subst hEq
    rfl
  | _ :: tl, _, k + 1, 0, v, _, hSet => by
    dsimp only [Trusted.MirSemantics.setElem?] at hSet
    cases hSub : Trusted.MirSemantics.setElem? tl k v with
    | none => rw [hSub] at hSet; cases hSet
    | some tl' =>
      rw [hSub] at hSet
      injection hSet with hEq
      subst hEq
      rfl
  | _ :: tl, _, k + 1, m + 1, v, hNe, hSet => by
    dsimp only [Trusted.MirSemantics.setElem?] at hSet
    cases hSub : Trusted.MirSemantics.setElem? tl k v with
    | none => rw [hSub] at hSet; cases hSet
    | some tl' =>
      rw [hSub] at hSet
      injection hSet with hEq
      subst hEq
      exact @getElem?_setElem?_ne_of_some α tl tl' k m v
        (fun he => hNe (congrArg Nat.succ he)) hSub

private theorem getElem?_setElem?_same_of_some {α : Type} :
    ∀ {xs xs' : List α} {idx : Nat} {v : α},
      Trusted.MirSemantics.setElem? xs idx v = some xs' →
      Trusted.MirSemantics.getElem? xs' idx = some v
  | [], _, _, _, hSet => by cases hSet
  | _ :: _, _, 0, _, hSet => by
    injection hSet with hEq
    subst hEq
    rfl
  | _ :: tl, _, k + 1, v, hSet => by
    dsimp only [Trusted.MirSemantics.setElem?] at hSet
    cases hSub : Trusted.MirSemantics.setElem? tl k v with
    | none => rw [hSub] at hSet; cases hSet
    | some tl' =>
      rw [hSub] at hSet
      injection hSet with hEq
      subst hEq
      exact @getElem?_setElem?_same_of_some α tl tl' k v hSub

/-- Contiguous suffix-deadness assertion `ls[start .. start + count) = .dead`.
-/
@[expose] def slotsDeadFrom (start count : Nat) (ls : List LocalSlot) : Prop :=
  @Nat.rec (fun _ => Nat → Prop)
    (fun _ => True)
    (fun _ ih pos =>
      Trusted.MirSemantics.getElem? ls pos = some .dead ∧ ih (pos + 1))
    count start

private theorem slotsDeadFrom_set_below {start count idx : Nat}
    {ls ls' : List LocalSlot} {v : LocalSlot}
    (hBelow : idx < start)
    (hSet : Trusted.MirSemantics.setElem? ls idx v = some ls')
    (hDead : slotsDeadFrom start count ls) :
    slotsDeadFrom start count ls' := by
  induction count generalizing start with
  | zero => exact True.intro
  | succ k ih =>
    have hNe : start ≠ idx := fun he => by
      subst he
      exact Nat.lt_irrefl start hBelow
    exact ⟨by rw [getElem?_setElem?_ne_of_some hNe hSet]; exact hDead.1,
           ih (Nat.lt_trans hBelow (Nat.lt_succ_self start)) hDead.2⟩

private theorem slotsDeadFrom_cons_head {pos count : Nat}
    {ls ls' : List LocalSlot}
    (hSet : Trusted.MirSemantics.setElem? ls pos .dead = some ls')
    (hRest : slotsDeadFrom (pos + 1) count ls) :
    slotsDeadFrom pos (count + 1) ls' :=
  ⟨getElem?_setElem?_same_of_some hSet,
   slotsDeadFrom_set_below (Nat.lt_succ_self pos) hSet hRest⟩

/-- Entry state invariant for a shared LIFO `StorageDead` cleanup spine. -/
@[expose] def DropSpineInv (firstDead totalEnd : Nat) (retVal : Val) (blk : BasicBlockId)
    (s : State) : Prop :=
  ∃ (ls : List LocalSlot) (cm : CallerMemory) (mem : MemoryState),
    s = { frames := [{ defId := 0, blockIdx := blk, stmtIdx := 0, locals := ls }],
          callerMem := cm, mem := mem } ∧
    firstDead ≤ totalEnd ∧
    totalEnd ≤ ls.length ∧
    allSlotsNonIndirect ls = true ∧
    Trusted.MirSemantics.getElem? ls 0 = some (.immediate (some retVal)) ∧
    slotsDeadFrom firstDead (totalEnd - firstDead) ls

/-- Zero-`Prop`-argument LIFO `StorageDead` spine cut predicate (sealed
`@[irreducible]` below), proving normal return with `out.ret = retVal` and
ruling out unwind outcomes (`onUnwind := fun _ => False`). -/
@[expose] def DropSpineCut (body : Body) (bt : BlockTree BasicBlock)
    (blk : BasicBlockId) (firstDead totalEnd : Nat) (retVal : Val)
    (dropFuel : Nat) : Prop :=
  ValidBlockTree body.basicBlocks bt →
  ∀ s : State,
    DropSpineInv firstDead totalEnd retVal blk s →
    wpTwoTrack (bodyProg body) dropFuel s
      (fun out => out.ret = retVal) (fun _ => False)

/-- Base return block at the bottom of a `DropSpineCut` chain (`1` step). -/
theorem dropSpineCut_base_ret {body : Body} (bt : BlockTree BasicBlock)
    {retBlk firstDead totalEnd : Nat} {retVal : Val}
    (hBlk : bt.lookup retBlk =
      some { statements := [], terminator := .return_, cleanup := false }) :
    DropSpineCut body bt retBlk firstDead totalEnd retVal 1 := by
  intro hValid s hInv
  let ⟨ls, cm, mem, hs, _, _, _, hRet0, _⟩ := hInv
  subst hs
  apply wpOutcomeState_of_execOutcomeState
  have hGetBlk : Trusted.MirSemantics.getElem? body.basicBlocks retBlk =
      some { statements := [], terminator := .return_, cleanup := false } := by
    rw [← BlockTree.lookup_eq_getElem? hValid retBlk]
    exact hBlk
  dsimp only [execOutcomeState, execStepOutcome]
  rw [execStepPred_succ_iff]
  unfold bodyProg evalStep
  dsimp only [Trusted.MirSemantics.getElem?]
  rw [hGetBlk]
  dsimp only [Trusted.MirSemantics.getElem?, evalTerminator]
  rw [hRet0]
  rfl

/-- Prepend a single `StorageDead dropIdx; goto nextBlk` block onto a
`DropSpineCut` suffix (`O(1)` per scope instead of `O(K^2)` re-evaluation). -/
theorem dropSpineCut_prepend_storageDead {body : Body}
    (bt : BlockTree BasicBlock)
    {blk nextBlk dropIdx totalEnd nextFuel : Nat} {retVal : Val}
    (hNz : 0 < dropIdx)
    (hLtEnd : dropIdx < totalEnd)
    (hBlk : bt.lookup blk =
      some { statements := [.storageDead dropIdx],
             terminator := .goto nextBlk, cleanup := false })
    (hNext : DropSpineCut body bt nextBlk dropIdx totalEnd retVal nextFuel) :
    DropSpineCut body bt blk (dropIdx + 1) totalEnd retVal (2 + nextFuel) := by
  intro hValid s hInv
  let ⟨ls, cm, mem, hs, _, hTotLe, hNonInd, hRet0, hDead⟩ := hInv
  subst hs
  have hGetBlk : Trusted.MirSemantics.getElem? body.basicBlocks blk =
      some { statements := [.storageDead dropIdx],
             terminator := .goto nextBlk, cleanup := false } := by
    rw [← BlockTree.lookup_eq_getElem? hValid blk]
    exact hBlk
  have hDropLtLs : dropIdx < ls.length := Nat.lt_of_lt_of_le hLtEnd hTotLe
  let ⟨oldSlot, hOldGet⟩ := getElem?_some_of_lt ls hDropLtLs
  let ⟨ls', hSet, hLen'⟩ := setElem?_some_of_lt ls .dead hDropLtLs
  have hOldNonInd : slotNonIndirect oldSlot = true :=
    getElem?_nonIndirect_of_all hNonInd hOldGet
  have hDealloc : deallocateLocal mem oldSlot = .ok mem := by
    cases oldSlot with
    | dead | immediate _ | partialTuple _ => rfl
    | indirect _ => cases hOldNonInd
  have hDropBeqF : Nat.beq dropIdx 0 = false := by
    cases dropIdx with
    | zero => exact False.elim (Nat.lt_irrefl 0 hNz)
    | succ _ => rfl
  have h0NeDrop : (0 : Nat) ≠ dropIdx := fun he => by
    subst he
    exact Nat.lt_irrefl 0 hNz
  let sMid : State :=
    { frames := [{ defId := 0, blockIdx := blk, stmtIdx := 1, locals := ls' }],
      callerMem := cm, mem := mem }
  let sNext : State :=
    { frames := [{ defId := 0, blockIdx := nextBlk, stmtIdx := 0, locals := ls' }],
      callerMem := cm, mem := mem }
  have hStep0 : evalStep (bodyProg body) 0
      { frames := [{ defId := 0, blockIdx := blk, stmtIdx := 0, locals := ls }],
        callerMem := cm, mem := mem } = .step sMid := by
    unfold bodyProg evalStep
    dsimp only [Trusted.MirSemantics.getElem?]
    rw [hGetBlk]
    dsimp only [Trusted.MirSemantics.getElem?, evalStatement]
    rw [hDropBeqF]
    rw [hOldGet]
    dsimp only
    rw [hSet]
    dsimp only
    rw [hDealloc]
    rfl
  have hStep1 : evalStep (bodyProg body) 0 sMid = .step sNext := by
    unfold sMid bodyProg evalStep
    dsimp only [Trusted.MirSemantics.getElem?]
    rw [hGetBlk]
    rfl
  have hCut2 : MirStageCut (bodyProg body) 2
      { frames := [{ defId := 0, blockIdx := blk, stmtIdx := 0, locals := ls }],
        callerMem := cm, mem := mem }
      sNext :=
    StepStageCut.step hStep0
      (StepStageCut.step hStep1 (StepStageCut.refl _ 0 sNext))
  have hSub : totalEnd - dropIdx = (totalEnd - (dropIdx + 1)) + 1 := by
    have h1 : dropIdx + 1 ≤ totalEnd := Nat.succ_le_of_lt hLtEnd
    have hc : (totalEnd - (dropIdx + 1) + 1) + dropIdx = totalEnd := by
      rw [Nat.add_assoc, Nat.add_comm 1 dropIdx]
      exact Nat.sub_add_cancel h1
    exact (congrArg (fun z => z - dropIdx) hc).symm.trans
      (Nat.add_sub_cancel (totalEnd - (dropIdx + 1) + 1) dropIdx)
  have hDeadNext : slotsDeadFrom dropIdx (totalEnd - dropIdx) ls' := by
    rw [hSub]
    exact slotsDeadFrom_cons_head hSet hDead
  have hRet0' : Trusted.MirSemantics.getElem? ls' 0 =
      some (.immediate (some retVal)) := by
    rw [getElem?_setElem?_ne_of_some h0NeDrop hSet]
    exact hRet0
  have hInvNext : DropSpineInv dropIdx totalEnd retVal nextBlk sNext :=
    ⟨ls', cm, mem, rfl, Nat.le_of_lt hLtEnd,
     by rw [hLen']; exact hTotLe,
     allSlotsNonIndirect_set_dead hNonInd hSet,
     hRet0', hDeadNext⟩
  exact wpOutcomeState_of_mirStageCut hCut2 (hNext hValid sNext hInvNext)

/-- Discharges `wpTwoTrack` at an entry to a shared `DropSpineCut` block. -/
theorem wpTwoTrack_of_dropSpineCut {body : Body} {bt : BlockTree BasicBlock}
    {blk firstDead totalEnd dropFuel : Nat} {retVal : Val} {s : State}
    (hValid : ValidBlockTree body.basicBlocks bt)
    (hCut : DropSpineCut body bt blk firstDead totalEnd retVal dropFuel)
    (hInv : DropSpineInv firstDead totalEnd retVal blk s) :
    wpTwoTrack (bodyProg body) dropFuel s
      (fun out => out.ret = retVal) (fun _ => False) :=
  hCut hValid s hInv

attribute [irreducible] DropSpineCut

/-! ## Bounded Early-Return (`?`) Loop Invariant Rule -/

export Anneal.Framework.StepWp
  (compNatMax le_compNatMax_left le_compNatMax_right compNatMin
   compNatMin_le_left compNatMin_le_right)

/-- Bounded loop invariant driver supporting both normal loop exit
(`normalExit`) and mid-loop `?` / `break` early-return cleanup exit
(`earlyClean`), stepping each iteration via `wpUntilCutStep (evalStep p 0)` (`0`
`noncomputable`). -/
@[expose] def wpIterWithRetGuard (p : Program)
    (inv earlyClean normalExit : State → Prop)
    (stepBudget iters : Nat) (s : State) : Prop :=
  wpIterCut (evalStep p 0) inv earlyClean normalExit stepBudget iters s

/-- Soundness of `wpIterWithRetGuard` into `wpTwoTrack` (`wpOutcomeState` with
`onFault := fun _ => False`) in `iters * stepBudget + compNatMax fuelNormal
fuelEarly` steps. -/
theorem wpOutcomeState_loop_early_return_sound {p : Program}
    {inv earlyClean normalExit : State → Prop}
    {onRet : Out → Prop} {onUnwind : CallerMemory → Prop}
    {stepBudget iters fuelNormal fuelEarly : Nat} {s : State}
    (hLoop : wpIterWithRetGuard p inv earlyClean normalExit stepBudget iters s)
    (hNorm : ∀ st : State, normalExit st →
      wpTwoTrack p fuelNormal st onRet onUnwind)
    (hEarly : ∀ st : State, earlyClean st →
      wpTwoTrack p fuelEarly st onRet onUnwind) :
    wpTwoTrack p (iters * stepBudget + compNatMax fuelNormal fuelEarly) s
      onRet onUnwind :=
  wpStepPred_loop_early_return_sound (c₀ := 0) (fun _ _ => Iff.rfl)
    hLoop hNorm hEarly

/-- Inductive loop-invariant introduction rule for `wpIterWithRetGuard`: if
`inv` (indexed by remaining iteration budget) implies `normalExit ∨ earlyClean`
at `0` and advances in at most `stepBudget` steps to `inv k ∨ normalExit ∨
earlyClean` at `k + 1`, then `inv iters s` establishes `wpIterWithRetGuard`. -/
theorem wpIterWithRetGuard_of_step {p : Program}
    {inv : Nat → State → Prop} {earlyClean normalExit : State → Prop}
    {stepBudget : Nat}
    (hZero : ∀ st : State, inv 0 st → normalExit st ∨ earlyClean st)
    (hStep : ∀ (k : Nat) (st : State), inv (k + 1) st →
      normalExit st ∨ earlyClean st ∨
        wpUntilCutStep (evalStep p 0)
          (fun st' => inv k st' ∨ normalExit st' ∨ earlyClean st')
          stepBudget st)
    {iters : Nat} {s : State} (hInv : inv iters s) :
    wpIterWithRetGuard p (fun st => ∃ m : Nat, inv m st)
      earlyClean normalExit stepBudget iters s :=
  wpIterCut_of_step hZero hStep hInv

end Anneal.Core

end
