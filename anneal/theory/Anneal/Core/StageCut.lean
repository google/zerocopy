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
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore
public import Anneal.Core.BlockTree

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.MirTotal

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

/-- Underlying bounded `.step`-reachability relation for `StepStageCut`. -/
@[expose] def reachStepIn {S Out : Type} (step : S → StepResult S Out)
    (fuel : Nat) (s₀ s₁ : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun st => st = s₁)
    (fun _ ih st =>
      st = s₁ ∨
      match step st with
      | .step st' => ih st'
      | .done _ => False
      | .fault _ => False)
    fuel s₀

/-- Zero-`Prop`-argument stage-cut barrier asserting that `s₀` reaches `s₁`
within `fuel` transitions of `step` without faulting or halting prematurely
(sealed `@[irreducible]` below after its introduction and composition laws).

Keeping `StepStageCut` free of `Prop` arguments ensures downstream `rw` and
`simp` passes cannot traverse into the reachability body via
`congrArg` / `congrArgs` without explicitly applying the elimination lemmas. -/
@[expose] def StepStageCut {S Out : Type} (step : S → StepResult S Out)
    (fuel : Nat) (s₀ s₁ : S) : Prop :=
  reachStepIn step fuel s₀ s₁

/-- Zero-step reflexivity at any fuel budget `fuel`. -/
theorem StepStageCut.refl {S Out : Type} (step : S → StepResult S Out)
    (fuel : Nat) (s : S) : StepStageCut step fuel s s := by
  cases fuel with
  | zero => rfl
  | succ _ => exact .inl rfl

/-- Prepend a single `.step` transition onto a `StepStageCut` derivation. -/
theorem StepStageCut.step {S Out : Type} {step : S → StepResult S Out}
    {fuel : Nat} {s₀ s₁ s₂ : S}
    (hStep : step s₀ = .step s₁)
    (hRest : StepStageCut step fuel s₁ s₂) :
    StepStageCut step (fuel + 1) s₀ s₂ := by
  refine .inr ?_
  change (match step s₀ with
    | .step st' => reachStepIn step fuel st' s₂
    | .done _ => False
    | .fault _ => False)
  rw [hStep]
  exact hRest

/-- Fuel weakening `f₁ ≤ f₂` for `StepStageCut`. -/
theorem StepStageCut.fuel_mono {S Out : Type} {step : S → StepResult S Out} :
    ∀ {f₁ f₂ : Nat} {s₀ s₁ : S},
      f₁ ≤ f₂ → StepStageCut step f₁ s₀ s₁ → StepStageCut step f₂ s₀ s₁
  | 0, f₂, _, s₁, _, h => by
    change _ = s₁ at h
    subst h
    exact StepStageCut.refl step f₂ _
  | n + 1, 0, _, _, hLe, _ => False.elim (Nat.not_succ_le_zero n hLe)
  | n + 1, m + 1, s₀, s₁, hLe, h => by
    cases h with
    | inl hEq => exact .inl hEq
    | inr hSt =>
      refine .inr ?_
      change (match step s₀ with
        | .step st' => reachStepIn step n st' s₁
        | .done _ => False
        | .fault _ => False) at hSt
      change (match step s₀ with
        | .step st' => reachStepIn step m st' s₁
        | .done _ => False
        | .fault _ => False)
      cases hEv : step s₀ with
      | step st' =>
        rw [hEv] at hSt
        exact StepStageCut.fuel_mono (Nat.le_of_succ_le_succ hLe) hSt
      | done _ => rw [hEv] at hSt; exact False.elim hSt
      | fault _ => rw [hEv] at hSt; exact False.elim hSt

/-- Sequential composition of `StepStageCut` segments (`f₁ + f₂` steps). -/
theorem StepStageCut.trans {S Out : Type} {step : S → StepResult S Out} :
    ∀ {f₁ f₂ : Nat} {s₀ s₁ s₂ : S},
      StepStageCut step f₁ s₀ s₁ →
      StepStageCut step f₂ s₁ s₂ →
      StepStageCut step (f₁ + f₂) s₀ s₂
  | 0, f₂, _, s₁, _, h₀₁, h₁₂ => by
    change _ = s₁ at h₀₁
    subst h₀₁
    rw [Nat.zero_add]
    exact h₁₂
  | n + 1, f₂, s₀, s₁, s₂, h₀₁, h₁₂ => by
    cases h₀₁ with
    | inl hEq =>
      subst hEq
      exact StepStageCut.fuel_mono (Nat.le_add_left f₂ (n + 1)) h₁₂
    | inr hSt =>
      rw [Nat.succ_add]
      refine .inr ?_
      change (match step s₀ with
        | .step st' => reachStepIn step n st' s₁
        | .done _ => False
        | .fault _ => False) at hSt
      change (match step s₀ with
        | .step st' => reachStepIn step (n + f₂) st' s₂
        | .done _ => False
        | .fault _ => False)
      cases hEv : step s₀ with
      | step st' =>
        rw [hEv] at hSt
        exact StepStageCut.trans hSt h₁₂
      | done _ => rw [hEv] at hSt; exact False.elim hSt
      | fault _ => rw [hEv] at hSt; exact False.elim hSt

private theorem stepStageCut_imp_of_step_eq {S Out : Type}
    {step₁ step₂ : S → StepResult S Out}
    (hEq : ∀ s : S, step₁ s = step₂ s) :
    ∀ {fuel : Nat} {s₀ s₁ : S},
      StepStageCut step₁ fuel s₀ s₁ → StepStageCut step₂ fuel s₀ s₁
  | 0, _, _, h => h
  | n + 1, s₀, s₁, h => by
    cases h with
    | inl hSame => exact .inl hSame
    | inr hSt =>
      refine .inr ?_
      change (match step₁ s₀ with
        | .step st' => reachStepIn step₁ n st' s₁
        | .done _ => False
        | .fault _ => False) at hSt
      change (match step₂ s₀ with
        | .step st' => reachStepIn step₂ n st' s₁
        | .done _ => False
        | .fault _ => False)
      rw [← hEq s₀]
      cases hEv : step₁ s₀ with
      | step st' =>
        rw [hEv] at hSt
        exact stepStageCut_imp_of_step_eq hEq hSt
      | done _ => rw [hEv] at hSt; exact False.elim hSt
      | fault _ => rw [hEv] at hSt; exact False.elim hSt

/-- Pointwise transition congruence for `StepStageCut`. -/
theorem StepStageCut.congr_step {S Out : Type}
    {step₁ step₂ : S → StepResult S Out}
    (hEq : ∀ s : S, step₁ s = step₂ s) {fuel : Nat} {s₀ s₁ : S} :
    StepStageCut step₁ fuel s₀ s₁ ↔ StepStageCut step₂ fuel s₀ s₁ :=
  ⟨stepStageCut_imp_of_step_eq hEq,
   stepStageCut_imp_of_step_eq (fun s => (hEq s).symm)⟩

/-- Predicate-level cutpoint weakest precondition over `step` (`0`
`noncomputable`). -/
@[expose] def wpUntilCutStep {S Out : Type} (step : S → StepResult S Out)
    (cut : S → Prop) (fuel : Nat) (s₀ : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun st => cut st)
    (fun _ ih st =>
      cut st ∨
      match step st with
      | .step st' => ih st'
      | .done _ => False
      | .fault _ => False)
    fuel s₀

/-- Base introduction rule for `wpUntilCutStep` when `cut s` already holds. -/
theorem wpUntilCutStep_here {S Out : Type} {step : S → StepResult S Out}
    {cut : S → Prop} (fuel : Nat) {s : S} (h : cut s) :
    wpUntilCutStep step cut fuel s := by
  cases fuel with
  | zero => exact h
  | succ _ => exact .inl h

/-- Single-step introduction rule for `wpUntilCutStep`. -/
theorem wpUntilCutStep_step {S Out : Type} {step : S → StepResult S Out}
    {cut : S → Prop} {fuel : Nat} {s s' : S}
    (hStep : step s = .step s')
    (hNext : wpUntilCutStep step cut fuel s') :
    wpUntilCutStep step cut (fuel + 1) s := by
  refine .inr ?_
  change (match step s with
    | .step st' => wpUntilCutStep step cut fuel st'
    | .done _ => False
    | .fault _ => False)
  rw [hStep]
  exact hNext

/-- Constructive equivalence between predicate-level `wpUntilCutStep` and
existential witness reachability over `StepStageCut` (`0` axioms). -/
theorem wpUntilCutStep_iff_exists_stepStageCut {S Out : Type}
    {step : S → StepResult S Out} {cut : S → Prop} :
    ∀ {fuel : Nat} {s₀ : S},
      wpUntilCutStep step cut fuel s₀ ↔
      ∃ s₁ : S, StepStageCut step fuel s₀ s₁ ∧ cut s₁
  | 0, s₀ =>
    ⟨fun h => ⟨s₀, rfl, h⟩,
     fun h => by
       let ⟨s₁, hs, hc⟩ := h
       change s₀ = s₁ at hs
       subst hs
       exact hc⟩
  | n + 1, s₀ => by
    constructor
    · intro h
      cases h with
      | inl hc => exact ⟨s₀, .inl rfl, hc⟩
      | inr hSt =>
        change (match step s₀ with
          | .step st' => wpUntilCutStep step cut n st'
          | .done _ => False
          | .fault _ => False) at hSt
        cases hEv : step s₀ with
        | step st' =>
          rw [hEv] at hSt
          let ⟨s₁, hReach, hc⟩ :=
            (wpUntilCutStep_iff_exists_stepStageCut (fuel := n)).mp hSt
          refine ⟨s₁, .inr ?_, hc⟩
          change (match step s₀ with
            | .step st' => reachStepIn step n st' s₁
            | .done _ => False
            | .fault _ => False)
          rw [hEv]
          exact hReach
        | done _ => rw [hEv] at hSt; exact False.elim hSt
        | fault _ => rw [hEv] at hSt; exact False.elim hSt
    · intro hEx
      let ⟨s₁, hReach, hc⟩ := hEx
      cases hReach with
      | inl hs =>
        subst hs
        exact .inl hc
      | inr hSt =>
        change (match step s₀ with
          | .step st' => reachStepIn step n st' s₁
          | .done _ => False
          | .fault _ => False) at hSt
        refine .inr ?_
        change (match step s₀ with
          | .step st' => wpUntilCutStep step cut n st'
          | .done _ => False
          | .fault _ => False)
        cases hEv : step s₀ with
        | step st' =>
          rw [hEv] at hSt
          exact (wpUntilCutStep_iff_exists_stepStageCut (fuel := n)).mpr
            ⟨s₁, hSt, hc⟩
        | done _ => rw [hEv] at hSt; exact False.elim hSt
        | fault _ => rw [hEv] at hSt; exact False.elim hSt

/-- Postcondition monotonicity for `wpUntilCutStep`. -/
theorem wpUntilCutStep_mono {S Out : Type} {step : S → StepResult S Out}
    {c₁ c₂ : S → Prop} (hImp : ∀ s, c₁ s → c₂ s)
    {fuel : Nat} {s₀ : S} (h : wpUntilCutStep step c₁ fuel s₀) :
    wpUntilCutStep step c₂ fuel s₀ := by
  let ⟨s₁, hCut, hc₁⟩ := wpUntilCutStep_iff_exists_stepStageCut.mp h
  exact wpUntilCutStep_iff_exists_stepStageCut.mpr ⟨s₁, hCut, hImp s₁ hc₁⟩

/-- Fuel monotonicity for `wpUntilCutStep`. -/
theorem wpUntilCutStep_fuel_mono {S Out : Type} {step : S → StepResult S Out}
    {cut : S → Prop} {f₁ f₂ : Nat} {s₀ : S} (hLe : f₁ ≤ f₂)
    (h : wpUntilCutStep step cut f₁ s₀) :
    wpUntilCutStep step cut f₂ s₀ := by
  let ⟨s₁, hCut, hc⟩ := wpUntilCutStep_iff_exists_stepStageCut.mp h
  exact wpUntilCutStep_iff_exists_stepStageCut.mpr
    ⟨s₁, StepStageCut.fuel_mono hLe hCut, hc⟩

/-- Transitive cutpoint chaining for `wpUntilCutStep`. -/
theorem wpUntilCutStep_trans {S Out : Type} {step : S → StepResult S Out}
    {c₁ c₂ : S → Prop} {f₁ f₂ : Nat} {s₀ : S}
    (h₁ : wpUntilCutStep step c₁ f₁ s₀)
    (h₂ : ∀ sc, c₁ sc → wpUntilCutStep step c₂ f₂ sc) :
    wpUntilCutStep step c₂ (f₁ + f₂) s₀ := by
  let ⟨s₁, hCut₁, hc₁⟩ := wpUntilCutStep_iff_exists_stepStageCut.mp h₁
  let ⟨s₂, hCut₂, hc₂⟩ := wpUntilCutStep_iff_exists_stepStageCut.mp (h₂ s₁ hc₁)
  exact wpUntilCutStep_iff_exists_stepStageCut.mpr
    ⟨s₂, StepStageCut.trans hCut₁ hCut₂, hc₂⟩

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
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {f₁ f₂ : Nat} {s₀ s₁ : State},
      MirStageCut p f₁ s₀ s₁ →
      execOutcomeState p onDone onFault f₂ s₁ →
      execOutcomeState p onDone onFault (f₁ + f₂) s₀
  | 0, f₂, _, s₁, hCut, hCont => by
    change _ = s₁ at hCut
    subst hCut
    rw [Nat.zero_add]
    exact hCont
  | n + 1, f₂, s₀, s₁, hCut, hCont => by
    cases hCut with
    | inl hEq =>
      subst hEq
      exact wpOutcomeState_iff_execOutcomeState.mp
        (wpOutcomeState_fuel_mono (Nat.le_add_left f₂ (n + 1))
          (wpOutcomeState_iff_execOutcomeState.mpr hCont))
    | inr hSt =>
      rw [Nat.succ_add]
      change (match evalStep p 0 s₀ with
        | .step st' => execOutcomeState p onDone onFault (n + f₂) st'
        | .done out => onDone out
        | .fault k => onFault k)
      cases hEv : evalStep p 0 s₀ with
      | step st' =>
        rw [hEv] at hSt
        exact execOutcomeState_of_mirStageCut hSt hCont
      | done _ => rw [hEv] at hSt; exact False.elim hSt
      | fault _ => rw [hEv] at hSt; exact False.elim hSt

/-- Prepend a `MirStageCut` prefix onto `wpOutcomeState`. -/
theorem wpOutcomeState_of_mirStageCut {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {f₁ f₂ : Nat} {s₀ s₁ : State}
    (hCut : MirStageCut p f₁ s₀ s₁)
    (hCont : wpOutcomeState p onDone onFault f₂ s₁) :
    wpOutcomeState p onDone onFault (f₁ + f₂) s₀ :=
  wpOutcomeState_of_execOutcomeState
    (execOutcomeState_of_mirStageCut hCut
      (execOutcomeState_of_wpOutcomeState hCont))

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
    wpOutcomeState p onDone onFault (f₁ + f₂) s₀ := by
  let ⟨s₁, hCut, hc⟩ := wpUntilCutStep_iff_exists_stepStageCut.mp hPre
  exact wpOutcomeState_of_mirStageCut hCut (hCont s₁ hc)

attribute [irreducible] StepStageCut

/-! ## Generic Zero-`Prop`-Argument Reflective Barrier (`BoolCertCut`) -/

/-- Zero-`Prop`-argument reflective certificate barrier asserting that
computable checker `check : Code → Bool` accepts certificate `cert : Code`
(`check cert = true`), sealed `@[irreducible]` below after its seal, unseal,
and pairing laws.

Why zero `Prop` arguments: wrapping a `Prop` inside an `@[irreducible]`
constant (such as `Hold (P : Prop)` or `Firewall tag P`) does not block Lean
4's `rw` (`kabstract` + `congrArg`) or `simp` (`simpApp` -> `congrArgs`), which
still descend into explicit `Prop` arguments without unfolding the head
constant. Parameterizing `BoolCertCut` strictly by computational data (`Code`,
`check`, `cert`) keeps the sealed proposition opaque to downstream rewriting
while supporting zero-axiom reflective proofs.
-/
@[expose] def BoolCertCut {Code : Type} (check : Code → Bool) (cert : Code) : Prop :=
  check cert = true

/-- Seals a concrete or derived `check cert = true` witness behind
`BoolCertCut`. -/
theorem BoolCertCut.seal {Code : Type} (check : Code → Bool) (cert : Code)
    (h : check cert = true) : BoolCertCut check cert :=
  h

/-- Unseals `BoolCertCut check cert` back to `check cert = true`. -/
theorem BoolCertCut.unseal {Code : Type} {check : Code → Bool} {cert : Code}
    (h : BoolCertCut check cert) : check cert = true :=
  h

/-- Applies a pointwise soundness implication directly to a sealed
`BoolCertCut` witness without exposing the definition to downstream tactics. -/
theorem BoolCertCut.elim {Code : Type} {check : Code → Bool} {cert : Code}
    {P : Prop} (hSound : check cert = true → P)
    (hCut : BoolCertCut check cert) : P :=
  hSound hCut

/-- Applies a universal checker soundness theorem
`∀ c, check c = true → interp c` to a sealed `BoolCertCut check cert`. -/
theorem BoolCertCut.sound {Code : Type} {check : Code → Bool}
    {interp : Code → Prop}
    (hSound : ∀ c : Code, check c = true → interp c)
    {cert : Code} (hCut : BoolCertCut check cert) : interp cert :=
  hSound cert hCut

/-- Pointwise checker congruence for `BoolCertCut`. -/
theorem BoolCertCut.congr_check {Code : Type}
    {check₁ check₂ : Code → Bool}
    (hEq : ∀ c : Code, check₁ c = check₂ c) {cert : Code} :
    BoolCertCut check₁ cert ↔ BoolCertCut check₂ cert := by
  unfold BoolCertCut
  rw [hEq cert]

/-- Conjoins two `BoolCertCut` witnesses into a single paired certificate
checker without introducing any `Prop` arguments. -/
theorem BoolCertCut.pair {C₁ C₂ : Type}
    {check₁ : C₁ → Bool} {check₂ : C₂ → Bool} {c₁ : C₁} {c₂ : C₂}
    (h₁ : BoolCertCut check₁ c₁) (h₂ : BoolCertCut check₂ c₂) :
    BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2) (c₁, c₂) := by
  unfold BoolCertCut at h₁ h₂
  unfold BoolCertCut
  dsimp only
  rw [h₁, h₂]
  rfl

/-- Extracts the left `BoolCertCut` component from a paired certificate. -/
theorem BoolCertCut.fst {C₁ C₂ : Type}
    {check₁ : C₁ → Bool} {check₂ : C₂ → Bool} {c₁ : C₁} {c₂ : C₂}
    (h : BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2) (c₁, c₂)) :
    BoolCertCut check₁ c₁ := by
  unfold BoolCertCut at h
  unfold BoolCertCut
  dsimp only at h
  cases h1 : check₁ c₁ with
  | true => rfl
  | false =>
    rw [h1] at h
    cases h

/-- Extracts the right `BoolCertCut` component from a paired certificate. -/
theorem BoolCertCut.snd {C₁ C₂ : Type}
    {check₁ : C₁ → Bool} {check₂ : C₂ → Bool} {c₁ : C₁} {c₂ : C₂}
    (h : BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2) (c₁, c₂)) :
    BoolCertCut check₂ c₂ := by
  unfold BoolCertCut at h
  unfold BoolCertCut
  dsimp only at h
  cases h1 : check₁ c₁ with
  | false =>
    rw [h1] at h
    cases h
  | true =>
    rw [h1, Bool.true_and] at h
    exact h

attribute [irreducible] BoolCertCut

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
  @Nat.rec (fun _ => State → Prop)
    (fun _ => True)
    (fun _ ih st =>
      ∀ c : Choice, ValidChoice p st c →
        match evalStep p c st with
        | .step st' => ih st'
        | .done out => onDone out
        | .fault fk => onFault fk)
    fuel s

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
    {onFault₁ onFault₂ : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : State},
      wpOutcomeState p onDone₁ onFault₁ fuel s →
      wlpOutcomeState p onDone₂ onFault₂ fuel s →
      wpOutcomeState p (fun out => onDone₁ out ∧ onDone₂ out)
        (fun fk => onFault₁ fk ∧ onFault₂ fk) fuel s
  | 0, _, hSafe, _ => False.elim hSafe
  | k + 1, s, hSafe, hWlp => by
    change ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step st' => wpOutcomeState p onDone₁ onFault₁ k st'
        | .done out => onDone₁ out
        | .fault fk => onFault₁ fk) at hSafe
    change (∀ c : Choice, ValidChoice p s c →
      match evalStep p c s with
      | .step st' => wlpOutcomeState p onDone₂ onFault₂ k st'
      | .done out => onDone₂ out
      | .fault fk => onFault₂ fk) at hWlp
    refine ⟨hSafe.1, fun c hc => ?_⟩
    have h₁ := hSafe.2 c hc
    have h₂ := hWlp c hc
    cases hEv : evalStep p c s with
    | step st' =>
      rw [hEv] at h₁ h₂
      exact wpOutcomeState_conj_of_wlp_noDiv h₁ h₂
    | done out =>
      rw [hEv] at h₁ h₂
      exact ⟨h₁, h₂⟩
    | fault fk =>
      rw [hEv] at h₁ h₂
      exact ⟨h₁, h₂⟩

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
  | .dead | .immediate _ => true

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
  change (match evalStep (bodyProg body) 0
        { frames := [{ defId := 0, blockIdx := retBlk, stmtIdx := 0, locals := ls }],
          callerMem := cm, mem := mem } with
      | .step st' => False
      | .done out =>
        twoTrackPost (fun o => o.ret = retVal) (fun _ => False) out
      | .fault _ => False)
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
    | dead | immediate _ => rfl
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

/-- Computable maximum of two natural numbers. -/
@[expose] def compNatMax (a b : Nat) : Nat :=
  if Nat.ble a b then b else a

/-- Left upper-bound law `a ≤ compNatMax a b`. -/
theorem le_compNatMax_left (a b : Nat) : a ≤ compNatMax a b := by
  unfold compNatMax
  cases h : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true h
  | false => exact Nat.le_refl a

/-- Right upper-bound law `b ≤ compNatMax a b`. -/
theorem le_compNatMax_right (a b : Nat) : b ≤ compNatMax a b := by
  unfold compNatMax
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl b
  | false =>
    cases Nat.lt_or_ge a b with
    | inl hlt =>
      have hbt := Nat.ble_eq_true_of_le (Nat.le_of_lt hlt)
      rw [h] at hbt
      cases hbt
    | inr hge => exact hge

/-- Computable minimum of two natural numbers. -/
@[expose] def compNatMin (a b : Nat) : Nat :=
  if Nat.ble a b then a else b

/-- Left lower-bound law `compNatMin a b ≤ a`. -/
theorem compNatMin_le_left (a b : Nat) : compNatMin a b ≤ a := by
  unfold compNatMin
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl a
  | false =>
    cases Nat.lt_or_ge a b with
    | inl hlt =>
      have hbt := Nat.ble_eq_true_of_le (Nat.le_of_lt hlt)
      rw [h] at hbt
      cases hbt
    | inr hge => exact hge

/-- Right lower-bound law `compNatMin a b ≤ b`. -/
theorem compNatMin_le_right (a b : Nat) : compNatMin a b ≤ b := by
  unfold compNatMin
  cases h : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true h
  | false => exact Nat.le_refl b

/-- Bounded loop invariant driver supporting both normal loop exit
(`normalExit`) and mid-loop `?` / `break` early-return cleanup exit
(`earlyClean`), stepping each iteration via `wpUntilCutStep (evalStep p 0)` (`0`
`noncomputable`). -/
@[expose] def wpIterWithRetGuard (p : Program)
    (inv earlyClean normalExit : State → Prop)
    (stepBudget iters : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun st => normalExit st ∨ earlyClean st)
    (fun _ ih st =>
      normalExit st ∨ earlyClean st ∨
        (inv st ∧ wpUntilCutStep (evalStep p 0) ih stepBudget st))
    iters s

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
      onRet onUnwind := by
  induction iters generalizing s with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add]
    cases hLoop with
    | inl hn =>
      exact wpOutcomeState_fuel_mono
        (le_compNatMax_left fuelNormal fuelEarly) (hNorm s hn)
    | inr he =>
      exact wpOutcomeState_fuel_mono
        (le_compNatMax_right fuelNormal fuelEarly) (hEarly s he)
  | succ k ih =>
    have hMul :
        (k + 1) * stepBudget + compNatMax fuelNormal fuelEarly =
          stepBudget + (k * stepBudget + compNatMax fuelNormal fuelEarly) := by
      rw [Nat.add_mul, Nat.one_mul,
        Nat.add_comm (k * stepBudget) stepBudget, Nat.add_assoc]
    rw [hMul]
    cases hLoop with
    | inl hn =>
      have hLe : fuelNormal ≤
          stepBudget + (k * stepBudget + compNatMax fuelNormal fuelEarly) :=
        Nat.le_trans (le_compNatMax_left fuelNormal fuelEarly)
          (Nat.le_trans
            (Nat.le_add_left (compNatMax fuelNormal fuelEarly) (k * stepBudget))
            (Nat.le_add_left _ stepBudget))
      exact wpOutcomeState_fuel_mono hLe (hNorm s hn)
    | inr hRest =>
      cases hRest with
      | inl he =>
        have hLe : fuelEarly ≤
            stepBudget + (k * stepBudget + compNatMax fuelNormal fuelEarly) :=
          Nat.le_trans (le_compNatMax_right fuelNormal fuelEarly)
            (Nat.le_trans
              (Nat.le_add_left (compNatMax fuelNormal fuelEarly) (k * stepBudget))
              (Nat.le_add_left _ stepBudget))
        exact wpOutcomeState_fuel_mono hLe (hEarly s he)
      | inr hAnd =>
        exact wpOutcomeState_of_wpUntilCutMir hAnd.2 (fun st hNext => ih hNext)

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
          stepBudget st) :
    ∀ {iters : Nat} {s : State},
      inv iters s →
      wpIterWithRetGuard p (fun st => ∃ m : Nat, inv m st)
        earlyClean normalExit stepBudget iters s
  | 0, s, hInv => hZero s hInv
  | k + 1, s, hInv => by
    cases hStep k s hInv with
    | inl hNorm => exact .inl hNorm
    | inr hRest =>
      cases hRest with
      | inl hEarly => exact .inr (.inl hEarly)
      | inr hCut =>
        refine .inr (.inr ⟨⟨k + 1, hInv⟩, ?_⟩)
        refine wpUntilCutStep_mono (fun st' hNext => ?_) hCut
        cases hNext with
        | inl hInvK =>
          exact wpIterWithRetGuard_of_step hZero hStep hInvK
        | inr hExit =>
          cases k with
          | zero => exact hExit
          | succ _ =>
            cases hExit with
            | inl hn => exact .inl hn
            | inr he => exact .inr (.inl he)

end Anneal.Core

end
