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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Trusted.MirModel

public section

namespace Anneal.Framework.StepWp

open Trusted.MirSemantics

/-!
# Generic Fuel-Bounded Step & Checkpoint WPs (`Anneal.Framework.StepWp`)

Purely MIR-agnostic (`Trusted.MirModel.StepResult` only, `0` operational
semantics, `0` axioms beyond `propext`) step-transition calculus unifying:

1. `BoolCertCut` (`@[irreducible]`, `0` `Prop` args): reflective certificate
   firewall sealing `check cert = true`.
2. `wpStepPred` / `wlpStepPred` / `execStepPred` (+ outcome-only abbrevs):
   fuel-bounded demonic and deterministic weakest preconditions over arbitrary
   `step : C → S → StepResult S Out`.
3. `wpUntilPred` / `execUntilPred` / `wpUntilCutStep` and `@[irreducible]
   StepStageCut`: checkpoint weakest preconditions, cutpoint barriers, and
   sequential fuel composition.
4. Generic loop-induction, well-founded `Acc`, countdown, list-traversal,
   abstract-simulation, bounded early-return (`wpIterCut`), and deterministic
   `Nat`-rank termination rules.
-/

/-! ## 1. Reflective Zero-`Prop`-Argument Certificate Barrier (`BoolCertCut`) -/

/-- Zero-`Prop`-argument reflective certificate barrier asserting that
computable checker `check : Code → Bool` accepts certificate `cert : Code`
(`check cert = true`), sealed `@[irreducible]` below after its seal, unseal,
and pairing laws. -/
@[expose] def BoolCertCut {Code : Type} (check : Code → Bool)
    (cert : Code) : Prop :=
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
`BoolCertCut` witness without exposing the definition to tactics. -/
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
    (h : BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2)
      (c₁, c₂)) :
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
    (h : BoolCertCut (fun p : C₁ × C₂ => check₁ p.1 && check₂ p.2)
      (c₁, c₂)) :
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

/-! ## 2. Generic Step WP (`wpStepPred`, `wlpStepPred`, `execStepPred`) -/

/-- Fuel-bounded demonic weakest precondition over an arbitrary step function
`step : C → S → StepResult S Out`, passing the pre-step state alongside
`.done` and `.fault` outcomes. Uses `@Nat.rec` into `Prop` so kernel
evaluation avoids `_unsafe_rec` and codegen exemptions. -/
@[expose] def wpStepPred {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out)
    (onDone : S → Out → Prop) (onFault : S → FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun _ => False)
    (fun _ ih st =>
      (∃ c₀ : C, validChoice st c₀) ∧
      ∀ c : C, validChoice st c →
        match step c st with
        | .step st' => ih st'
        | .done out => onDone st out
        | .fault k => onFault st k)
    fuel s

/-- Outcome-only specialization of `wpStepPred`. -/
abbrev wpStepOutcome {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out)
    (onDone : Out → Prop) (onFault : FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  wpStepPred validChoice step (fun _ => onDone) (fun _ => onFault) fuel s

/-- Weakest liberal precondition over `step`: running out of fuel yields
`True`, while every `.done` / `.fault` within `fuel` must satisfy `onDone` /
`onFault`. -/
@[expose] def wlpStepPred {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out)
    (onDone : S → Out → Prop) (onFault : S → FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun _ => True)
    (fun _ ih st =>
      ∀ c : C, validChoice st c →
        match step c st with
        | .step st' => ih st'
        | .done out => onDone st out
        | .fault k => onFault st k)
    fuel s

/-- Outcome-only specialization of `wlpStepPred`. -/
abbrev wlpStepOutcome {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out)
    (onDone : Out → Prop) (onFault : FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  wlpStepPred validChoice step (fun _ => onDone) (fun _ => onFault) fuel s

/-- Deterministic counterpart of `wpStepPred` over
`step : S → StepResult S Out`. Concrete runs reduce directly by `rfl`. -/
@[expose] def execStepPred {S Out : Type}
    (step : S → StepResult S Out)
    (onDone : S → Out → Prop) (onFault : S → FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun _ => False)
    (fun _ ih st =>
      match step st with
      | .step st' => ih st'
      | .done out => onDone st out
      | .fault k => onFault st k)
    fuel s

/-- Outcome-only specialization of `execStepPred`. -/
abbrev execStepOutcome {S Out : Type}
    (step : S → StepResult S Out)
    (onDone : Out → Prop) (onFault : FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  execStepPred step (fun _ => onDone) (fun _ => onFault) fuel s

/-- Unfold `wpStepPred` at fuel `0`. -/
theorem wpStepPred_zero_iff {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} {s : S} :
    wpStepPred validChoice step onDone onFault 0 s ↔ False :=
  Iff.rfl

/-- Unfold `wpStepPred` at fuel `fuel + 1`. -/
theorem wpStepPred_succ_iff {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S} :
    wpStepPred validChoice step onDone onFault (fuel + 1) s ↔
      ((∃ c₀ : C, validChoice s c₀) ∧
        ∀ c : C, validChoice s c →
          match step c s with
          | .step st' => wpStepPred validChoice step onDone onFault fuel st'
          | .done out => onDone s out
          | .fault k => onFault s k) :=
  Iff.rfl

/-- Unfold `execStepPred` at fuel `0`. -/
theorem execStepPred_zero_iff {S Out : Type}
    {step : S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} {s : S} :
    execStepPred step onDone onFault 0 s ↔ False :=
  Iff.rfl

/-- Unfold `execStepPred` at fuel `fuel + 1`. -/
theorem execStepPred_succ_iff {S Out : Type}
    {step : S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S} :
    execStepPred step onDone onFault (fuel + 1) s ↔
      (match step s with
        | .step st' => execStepPred step onDone onFault fuel st'
        | .done out => onDone s out
        | .fault k => onFault s k) :=
  Iff.rfl

/-- Transport `wpStepPred` along an equality of fuel budgets. -/
theorem wpStepPred_fuel_cast {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {a b : Nat} {s : S} (hEq : a = b)
    (h : wpStepPred validChoice step onDone onFault a s) :
    wpStepPred validChoice step onDone onFault b s := by
  subst hEq
  exact h

/-- Transport `execStepPred` along an equality of fuel budgets. -/
theorem execStepPred_fuel_cast {S Out : Type}
    {step : S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {a b : Nat} {s : S} (hEq : a = b)
    (h : execStepPred step onDone onFault a s) :
    execStepPred step onDone onFault b s := by
  subst hEq
  exact h

/-- Exact equivalence between `wpStepPred` and deterministic `execStepPred`
whenever `validChoice` admits a unique choice `c₀` at every state. -/
theorem wpStepPred_iff_execStepPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} :
    ∀ {fuel : Nat} {s : S},
      wpStepPred validChoice step onDone onFault fuel s ↔
      execStepPred (step c₀) onDone onFault fuel s
  | 0, _ => Iff.rfl
  | fuel + 1, s => by
    change ((∃ cInit : C, validChoice s cInit) ∧
        ∀ c : C, validChoice s c →
          match step c s with
          | .step st' => wpStepPred validChoice step onDone onFault fuel st'
          | .done out => onDone s out
          | .fault k => onFault s k) ↔
      (match step c₀ s with
        | .step st' => execStepPred (step c₀) onDone onFault fuel st'
        | .done out => onDone s out
        | .fault k => onFault s k)
    constructor
    · intro h
      have h0 := h.2 c₀ ((hUnique s c₀).mpr rfl)
      cases hStep : step c₀ s with
      | step st' =>
        rw [hStep] at h0
        exact (wpStepPred_iff_execStepPred hUnique).mp h0
      | done out =>
        rw [hStep] at h0
        exact h0
      | fault k =>
        rw [hStep] at h0
        exact h0
    · intro h
      refine ⟨⟨c₀, (hUnique s c₀).mpr rfl⟩, fun c hc => ?_⟩
      have hcEq : c = c₀ := (hUnique s c).mp hc
      subst hcEq
      cases hStep : step c s with
      | step st' =>
        rw [hStep] at h
        exact (wpStepPred_iff_execStepPred hUnique).mpr h
      | done out =>
        rw [hStep] at h
        exact h
      | fault k =>
        rw [hStep] at h
        exact h

/-- Lift deterministic `execStepPred` into `wpStepPred`. -/
theorem wpStepPred_of_execStepPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S}
    (h : execStepPred (step c₀) onDone onFault fuel s) :
    wpStepPred validChoice step onDone onFault fuel s :=
  (wpStepPred_iff_execStepPred hUnique).mpr h

/-- Project `wpStepPred` onto deterministic `execStepPred`. -/
theorem execStepPred_of_wpStepPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S}
    (h : wpStepPred validChoice step onDone onFault fuel s) :
    execStepPred (step c₀) onDone onFault fuel s :=
  (wpStepPred_iff_execStepPred hUnique).mp h

/-- Rule of consequence for `wpStepPred`. -/
theorem wpStepPred_mono {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone₁ onDone₂ : S → Out → Prop}
    {onFault₁ onFault₂ : S → FaultKind → Prop}
    (hDone : ∀ s out, onDone₁ s out → onDone₂ s out)
    (hFault : ∀ s k, onFault₁ s k → onFault₂ s k) :
    ∀ {fuel : Nat} {s : S},
      wpStepPred validChoice step onDone₁ onFault₁ fuel s →
      wpStepPred validChoice step onDone₂ onFault₂ fuel s
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    refine ⟨h.1, fun c hc => ?_⟩
    have hc' := h.2 c hc
    cases hStep : step c s with
    | step st' =>
      rw [hStep] at hc'
      exact wpStepPred_mono hDone hFault hc'
    | done out =>
      rw [hStep] at hc'
      exact hDone s out hc'
    | fault k =>
      rw [hStep] at hc'
      exact hFault s k hc'

/-- Rule of consequence for `execStepPred` (derived from `wpStepPred_mono`).
-/
theorem execStepPred_mono {S Out : Type} {step : S → StepResult S Out}
    {onDone₁ onDone₂ : S → Out → Prop}
    {onFault₁ onFault₂ : S → FaultKind → Prop}
    (hDone : ∀ s out, onDone₁ s out → onDone₂ s out)
    (hFault : ∀ s k, onFault₁ s k → onFault₂ s k)
    {fuel : Nat} {s : S}
    (h : execStepPred step onDone₁ onFault₁ fuel s) :
    execStepPred step onDone₂ onFault₂ fuel s :=
  (wpStepPred_iff_execStepPred (C := Unit) (step := fun _ => step)
      (c₀ := ()) (fun _ _ => Iff.rfl)).mp
    (wpStepPred_mono hDone hFault
      ((wpStepPred_iff_execStepPred (C := Unit) (step := fun _ => step)
        (c₀ := ()) (fun _ _ => Iff.rfl)).mpr h))

/-- Fuel weakening `fuel₁ ≤ fuel₂` for `wpStepPred`. -/
theorem wpStepPred_fuel_mono {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} :
    ∀ {fuel₁ fuel₂ : Nat} {s : S},
      fuel₁ ≤ fuel₂ →
      wpStepPred validChoice step onDone onFault fuel₁ s →
      wpStepPred validChoice step onDone onFault fuel₂ s
  | 0, _, _, _, h => False.elim h
  | fuel₁ + 1, 0, _, hLe, _ =>
    False.elim (Nat.not_succ_le_zero fuel₁ hLe)
  | fuel₁ + 1, fuel₂ + 1, s, hLe, h => by
    have hLe' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hLe
    refine ⟨h.1, fun c hc => ?_⟩
    have hc' := h.2 c hc
    cases hStep : step c s with
    | step st' =>
      rw [hStep] at hc'
      exact wpStepPred_fuel_mono hLe' hc'
    | done _ =>
      rw [hStep] at hc'
      exact hc'
    | fault _ =>
      rw [hStep] at hc'
      exact hc'

/-- Fuel weakening `fuel₁ ≤ fuel₂` for `execStepPred`. -/
theorem execStepPred_fuel_mono {S Out : Type} {step : S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel₁ fuel₂ : Nat} {s : S} (hLe : fuel₁ ≤ fuel₂)
    (h : execStepPred step onDone onFault fuel₁ s) :
    execStepPred step onDone onFault fuel₂ s :=
  (wpStepPred_iff_execStepPred (C := Unit) (step := fun _ => step)
      (c₀ := ()) (fun _ _ => Iff.rfl)).mp
    (wpStepPred_fuel_mono hLe
      ((wpStepPred_iff_execStepPred (C := Unit) (step := fun _ => step)
        (c₀ := ()) (fun _ _ => Iff.rfl)).mpr h))

/-- Pointwise step-function congruence for `execStepPred`. -/
theorem execStepPred_congr {S Out : Type}
    {step₁ step₂ : S → StepResult S Out}
    (hEq : ∀ s : S, step₁ s = step₂ s)
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} :
    ∀ {fuel : Nat} {s : S},
      execStepPred step₁ onDone onFault fuel s →
      execStepPred step₂ onDone onFault fuel s
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    rw [execStepPred_succ_iff] at h
    rw [execStepPred_succ_iff, ← hEq s]
    cases hS : step₁ s with
    | step st' =>
      rw [hS] at h
      exact execStepPred_congr hEq h
    | done out =>
      rw [hS] at h
      exact h
    | fault k =>
      rw [hS] at h
      exact h

/-- Bisimulation across state projection `map : S₁ → S₂` preserving invariant
`Inv` and single-step outcomes. -/
theorem execStepOutcome_bisim {S₁ S₂ Out : Type}
    {step₁ : S₁ → StepResult S₁ Out} {step₂ : S₂ → StepResult S₂ Out}
    {Inv : S₁ → Prop} {map : S₁ → S₂}
    (hInvStep : ∀ s s', Inv s → step₁ s = .step s' → Inv s')
    (hSim : ∀ s, Inv s →
      step₂ (map s) =
        match step₁ s with
        | .step s' => .step (map s')
        | .done out => .done out
        | .fault k => .fault k)
    {onDone : Out → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : S₁}, Inv s →
      (execStepOutcome step₂ onDone onFault fuel (map s) ↔
       execStepOutcome step₁ onDone onFault fuel s)
  | 0, _, _ => Iff.rfl
  | fuel + 1, s, hInv => by
    dsimp only [execStepOutcome]
    rw [execStepPred_succ_iff, execStepPred_succ_iff, hSim s hInv]
    cases hSt : step₁ s with
    | step next =>
      exact execStepOutcome_bisim hInvStep hSim (hInvStep s next hInv hSt)
    | done _ => exact Iff.rfl
    | fault _ => exact Iff.rfl

/-- Single-step introduction for `wpStepPred` along a deterministic step. -/
theorem wpStepPred_step {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S}
    (h : match step c₀ s with
      | .step st' => wpStepPred validChoice step onDone onFault fuel st'
      | .done out => onDone s out
      | .fault k => onFault s k) :
    wpStepPred validChoice step onDone onFault (fuel + 1) s := by
  refine wpStepPred_succ_iff.mpr ⟨⟨c₀, (hUnique s c₀).mpr rfl⟩, fun c hc => ?_⟩
  have hEq : c = c₀ := (hUnique s c).mp hc
  subst hEq
  exact h

/-- Conjunctive split combining total `wpStepPred` with liberal `wlpStepPred`
without re-proving termination. -/
theorem wpStepPred_conj_of_wlp {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone₁ onDone₂ : S → Out → Prop}
    {onFault₁ onFault₂ : S → FaultKind → Prop} :
    ∀ {fuel : Nat} {s : S},
      wpStepPred validChoice step onDone₁ onFault₁ fuel s →
      wlpStepPred validChoice step onDone₂ onFault₂ fuel s →
      wpStepPred validChoice step
        (fun st out => onDone₁ st out ∧ onDone₂ st out)
        (fun st k => onFault₁ st k ∧ onFault₂ st k) fuel s
  | 0, _, hSafe, _ => False.elim hSafe
  | k + 1, s, hSafe, hWlp => by
    refine ⟨hSafe.1, fun c hc => ?_⟩
    have h1 := hSafe.2 c hc
    have h2 := hWlp c hc
    cases hEv : step c s with
    | step st' =>
      rw [hEv] at h1 h2
      exact wpStepPred_conj_of_wlp h1 h2
    | done out =>
      rw [hEv] at h1 h2
      exact ⟨h1, h2⟩
    | fault fk =>
      rw [hEv] at h1 h2
      exact ⟨h1, h2⟩

/-- Relational small-step transition over `(validChoice, step)`. -/
@[expose] def StepRel {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out)
    (s : S) (res : StepResult S Out) : Prop :=
  ∃ c : C, validChoice s c ∧ step c s = res

/-- Finite-step `.step` reachability over `(validChoice, step)`. -/
inductive StepReaches {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out) :
    S → S → Prop where
  | refl (s : S) : StepReaches validChoice step s s
  | tail {s₁ s₂ s₃ : S} :
      StepReaches validChoice step s₁ s₂ →
      StepRel validChoice step s₂ (.step s₃) →
      StepReaches validChoice step s₁ s₃

/-- Prepend a single step onto `StepReaches`. -/
theorem StepReaches.head {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {s₁ s₂ s₃ : S}
    (hFirst : StepRel validChoice step s₁ (.step s₂))
    (hRest : StepReaches validChoice step s₂ s₃) :
    StepReaches validChoice step s₁ s₃ := by
  induction hRest with
  | refl => exact StepReaches.tail (StepReaches.refl s₁) hFirst
  | tail _ hLast ih => exact StepReaches.tail ih hLast

/-- Any state reachable from `s₁` preserves `wpStepPred` at some remaining
fuel. -/
theorem wpStepPred_of_reaches {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {s₁ s₂ : S} {fuel : Nat}
    (hWp : wpStepPred validChoice step onDone onFault fuel s₁)
    (hReach : StepReaches validChoice step s₁ s₂) :
    ∃ fuel', wpStepPred validChoice step onDone onFault fuel' s₂ := by
  induction hReach with
  | refl => exact ⟨fuel, hWp⟩
  | tail _ hStep ih =>
    let ⟨fuel₁, hWp₁⟩ := ih
    cases fuel₁ with
    | zero => exact False.elim hWp₁
    | succ fuel₂ =>
      let ⟨c, hc, hEval⟩ := hStep
      have hBranch := hWp₁.2 c hc
      rw [hEval] at hBranch
      exact ⟨fuel₂, hBranch⟩

/-- Every state satisfying `wpStepPred` reaches a terminal `.done` or `.fault`
transition within `fuel` steps. -/
theorem exists_terminal_of_wpStepPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S}
    (hWp : wpStepPred validChoice step onDone onFault fuel s) :
    ∃ sEnd res, StepReaches validChoice step s sEnd ∧
      StepRel validChoice step sEnd res ∧
      match res with
      | .step _ => False
      | .done out => onDone sEnd out
      | .fault k => onFault sEnd k := by
  induction fuel generalizing s with
  | zero => exact False.elim hWp
  | succ f ih =>
    let ⟨⟨c₀, hc₀⟩, hAll⟩ := hWp
    have hStep := hAll c₀ hc₀
    cases hEval : step c₀ s with
    | step s' =>
      rw [hEval] at hStep
      let ⟨sEnd, res, hReach, hTerm, hRes⟩ := ih hStep
      exact ⟨sEnd, res,
        StepReaches.head ⟨c₀, hc₀, hEval⟩ hReach, hTerm, hRes⟩
    | done out =>
      rw [hEval] at hStep
      exact ⟨s, .done out, StepReaches.refl s, ⟨c₀, hc₀, hEval⟩, hStep⟩
    | fault k =>
      rw [hEval] at hStep
      exact ⟨s, .fault k, StepReaches.refl s, ⟨c₀, hc₀, hEval⟩, hStep⟩

/-- No state satisfying `wpStepPred` admits an infinite `.step` trace. -/
theorem not_infinite_trace_of_wpStepPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} :
    ∀ {fuel : Nat} (trace : Nat → S),
      wpStepPred validChoice step onDone onFault fuel (trace 0) →
      (∀ n : Nat, StepRel validChoice step (trace n) (.step (trace (n + 1)))) →
      False
  | 0, _, hWp, _ => hWp
  | _ + 1, trace, hWp, hSteps => by
    let ⟨c, hc, hEval⟩ := hSteps 0
    have hBranch := hWp.2 c hc
    rw [hEval] at hBranch
    exact not_infinite_trace_of_wpStepPred (fun n => trace (n + 1))
      hBranch (fun n => hSteps (n + 1))

/-! ## 3. Checkpoint WP (`wpUntilPred`, `execUntilPred`) & `StepStageCut` -/

/-- Fuel-bounded demonic checkpoint weakest precondition over `step`. -/
@[expose] def wpUntilPred {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out)
    (stop : S → Prop) (onDone : S → Out → Prop) (onFault : S → FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun st => stop st)
    (fun _ ih st =>
      stop st ∨
      ((∃ c₀ : C, validChoice st c₀) ∧
        ∀ c : C, validChoice st c →
          match step c st with
          | .step st' => ih st'
          | .done out => onDone st out
          | .fault k => onFault st k))
    fuel s

/-- Outcome-only specialization of `wpUntilPred`. -/
abbrev wpUntil {S Out C : Type}
    (validChoice : S → C → Prop) (step : C → S → StepResult S Out)
    (stop : S → Prop) (onDone : Out → Prop) (onFault : FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  wpUntilPred validChoice step stop (fun _ => onDone) (fun _ => onFault) fuel s

/-- Deterministic counterpart of `wpUntilPred` over
`step : S → StepResult S Out`. -/
@[expose] def execUntilPred {S Out : Type}
    (step : S → StepResult S Out)
    (stop : S → Prop) (onDone : S → Out → Prop) (onFault : S → FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun st => stop st)
    (fun _ ih st =>
      stop st ∨
      match step st with
      | .step st' => ih st'
      | .done out => onDone st out
      | .fault k => onFault st k)
    fuel s

/-- Outcome-only specialization of `execUntilPred`. -/
abbrev execUntil {S Out : Type}
    (step : S → StepResult S Out)
    (stop : S → Prop) (onDone : Out → Prop) (onFault : FaultKind → Prop)
    (fuel : Nat) (s : S) : Prop :=
  execUntilPred step stop (fun _ => onDone) (fun _ => onFault) fuel s

/-- Predicate-level cutpoint weakest precondition over deterministic `step`. -/
abbrev wpUntilCutStep {S Out : Type} (step : S → StepResult S Out)
    (cut : S → Prop) (fuel : Nat) (s₀ : S) : Prop :=
  execUntilPred step cut (fun _ _ => False) (fun _ _ => False) fuel s₀

/-- Unfold `wpUntilPred` at fuel `0`. -/
theorem wpUntilPred_zero_iff {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {s : S} :
    wpUntilPred validChoice step stop onDone onFault 0 s ↔ stop s :=
  Iff.rfl

/-- Unfold `wpUntilPred` at fuel `fuel + 1`. -/
theorem wpUntilPred_succ_iff {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S} :
    wpUntilPred validChoice step stop onDone onFault (fuel + 1) s ↔
      (stop s ∨
        ((∃ c₀ : C, validChoice s c₀) ∧
          ∀ c : C, validChoice s c →
            match step c s with
            | .step st' =>
              wpUntilPred validChoice step stop onDone onFault fuel st'
            | .done out => onDone s out
            | .fault k => onFault s k)) :=
  Iff.rfl

/-- Unfold `execUntilPred` at fuel `0`. -/
theorem execUntilPred_zero_iff {S Out : Type}
    {step : S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {s : S} :
    execUntilPred step stop onDone onFault 0 s ↔ stop s :=
  Iff.rfl

/-- Unfold `execUntilPred` at fuel `fuel + 1`. -/
theorem execUntilPred_succ_iff {S Out : Type}
    {step : S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S} :
    execUntilPred step stop onDone onFault (fuel + 1) s ↔
      (stop s ∨
        match step s with
        | .step st' => execUntilPred step stop onDone onFault fuel st'
        | .done out => onDone s out
        | .fault k => onFault s k) :=
  Iff.rfl

/-- Transport `wpUntilPred` along an equality of fuel budgets. -/
theorem wpUntilPred_fuel_cast {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {a b : Nat} {s : S} (hEq : a = b)
    (h : wpUntilPred validChoice step stop onDone onFault a s) :
    wpUntilPred validChoice step stop onDone onFault b s := by
  subst hEq
  exact h

/-- A state satisfying `stop` satisfies `wpUntilPred` at every fuel. -/
theorem wpUntilPred_stop {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S} (h : stop s) :
    wpUntilPred validChoice step stop onDone onFault fuel s := by
  cases fuel with
  | zero => exact h
  | succ _ => exact Or.inl h

/-- A state satisfying `stop` satisfies `execUntilPred` at every fuel. -/
theorem execUntilPred_stop {S Out : Type}
    {step : S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (fuel : Nat) {s : S} (h : stop s) :
    execUntilPred step stop onDone onFault fuel s := by
  cases fuel with
  | zero => exact h
  | succ _ => exact Or.inl h

/-- Single-step introduction for `execUntilPred`. -/
theorem execUntilPred_step {S Out : Type}
    {step : S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s s' : S} (hStep : step s = .step s')
    (hNext : execUntilPred step stop onDone onFault fuel s') :
    execUntilPred step stop onDone onFault (fuel + 1) s := by
  refine Or.inr ?_
  change (match step s with
    | .step st' => execUntilPred step stop onDone onFault fuel st'
    | .done out => onDone s out
    | .fault k => onFault s k)
  rw [hStep]
  exact hNext

/-- Single-step introduction for `wpUntilPred` along a deterministic step. -/
theorem wpUntilPred_step {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S}
    (h : match step c₀ s with
      | .step st' => wpUntilPred validChoice step stop onDone onFault fuel st'
      | .done out => onDone s out
      | .fault k => onFault s k) :
    wpUntilPred validChoice step stop onDone onFault (fuel + 1) s := by
  refine wpUntilPred_succ_iff.mpr (Or.inr ⟨⟨c₀, (hUnique s c₀).mpr rfl⟩, ?_⟩)
  intro c hc
  have hEq : c = c₀ := (hUnique s c).mp hc
  subst hEq
  exact h

/-- Exact equivalence between `wpUntilPred` and deterministic `execUntilPred`.
-/
theorem wpUntilPred_iff_execUntilPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} :
    ∀ {fuel : Nat} {s : S},
      wpUntilPred validChoice step stop onDone onFault fuel s ↔
      execUntilPred (step c₀) stop onDone onFault fuel s
  | 0, _ => Iff.rfl
  | fuel + 1, s => by
    change (stop s ∨
        ((∃ cInit : C, validChoice s cInit) ∧
          ∀ c : C, validChoice s c →
            match step c s with
            | .step st' =>
              wpUntilPred validChoice step stop onDone onFault fuel st'
            | .done out => onDone s out
            | .fault k => onFault s k)) ↔
      (stop s ∨
        match step c₀ s with
        | .step st' => execUntilPred (step c₀) stop onDone onFault fuel st'
        | .done out => onDone s out
        | .fault k => onFault s k)
    constructor
    · intro h
      cases h with
      | inl hs => exact Or.inl hs
      | inr hr =>
        refine Or.inr ?_
        have h0 := hr.2 c₀ ((hUnique s c₀).mpr rfl)
        cases hStep : step c₀ s with
        | step st' =>
          rw [hStep] at h0
          exact (wpUntilPred_iff_execUntilPred hUnique).mp h0
        | done out =>
          rw [hStep] at h0
          exact h0
        | fault k =>
          rw [hStep] at h0
          exact h0
    · intro h
      cases h with
      | inl hs => exact Or.inl hs
      | inr hr =>
        refine Or.inr ⟨⟨c₀, (hUnique s c₀).mpr rfl⟩, fun c hc => ?_⟩
        have hcEq : c = c₀ := (hUnique s c).mp hc
        subst hcEq
        cases hStep : step c s with
        | step st' =>
          rw [hStep] at hr
          exact (wpUntilPred_iff_execUntilPred hUnique).mpr hr
        | done out =>
          rw [hStep] at hr
          exact hr
        | fault k =>
          rw [hStep] at hr
          exact hr

/-- Lift deterministic `execUntilPred` into `wpUntilPred`. -/
theorem wpUntilPred_of_execUntilPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S}
    (h : execUntilPred (step c₀) stop onDone onFault fuel s) :
    wpUntilPred validChoice step stop onDone onFault fuel s :=
  (wpUntilPred_iff_execUntilPred hUnique).mpr h

/-- Project `wpUntilPred` onto deterministic `execUntilPred`. -/
theorem execUntilPred_of_wpUntilPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel : Nat} {s : S}
    (h : wpUntilPred validChoice step stop onDone onFault fuel s) :
    execUntilPred (step c₀) stop onDone onFault fuel s :=
  (wpUntilPred_iff_execUntilPred hUnique).mp h

/-- Rule of consequence for `wpUntilPred`. -/
theorem wpUntilPred_mono {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop₁ stop₂ : S → Prop}
    {onDone₁ onDone₂ : S → Out → Prop}
    {onFault₁ onFault₂ : S → FaultKind → Prop}
    (hStop : ∀ s, stop₁ s → stop₂ s)
    (hDone : ∀ s out, onDone₁ s out → onDone₂ s out)
    (hFault : ∀ s k, onFault₁ s k → onFault₂ s k) :
    ∀ {fuel : Nat} {s : S},
      wpUntilPred validChoice step stop₁ onDone₁ onFault₁ fuel s →
      wpUntilPred validChoice step stop₂ onDone₂ onFault₂ fuel s
  | 0, s, h => hStop s h
  | fuel + 1, s, h => by
    cases h with
    | inl hs => exact Or.inl (hStop s hs)
    | inr hr =>
      refine Or.inr ⟨hr.1, fun c hc => ?_⟩
      have hc' := hr.2 c hc
      cases hStep : step c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntilPred_mono hStop hDone hFault hc'
      | done out =>
        rw [hStep] at hc'
        exact hDone s out hc'
      | fault k =>
        rw [hStep] at hc'
        exact hFault s k hc'

/-- Rule of consequence for `execUntilPred`. -/
theorem execUntilPred_mono {S Out : Type}
    {step : S → StepResult S Out}
    {stop₁ stop₂ : S → Prop}
    {onDone₁ onDone₂ : S → Out → Prop}
    {onFault₁ onFault₂ : S → FaultKind → Prop}
    (hStop : ∀ s, stop₁ s → stop₂ s)
    (hDone : ∀ s out, onDone₁ s out → onDone₂ s out)
    (hFault : ∀ s k, onFault₁ s k → onFault₂ s k)
    {fuel : Nat} {s : S}
    (h : execUntilPred step stop₁ onDone₁ onFault₁ fuel s) :
    execUntilPred step stop₂ onDone₂ onFault₂ fuel s :=
  (wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
      (c₀ := ()) (fun _ _ => Iff.rfl)).mp
    (wpUntilPred_mono hStop hDone hFault
      ((wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
        (c₀ := ()) (fun _ _ => Iff.rfl)).mpr h))

/-- Fuel weakening `fuel₁ ≤ fuel₂` for `wpUntilPred`. -/
theorem wpUntilPred_fuel_mono {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} :
    ∀ {fuel₁ fuel₂ : Nat} {s : S},
      fuel₁ ≤ fuel₂ →
      wpUntilPred validChoice step stop onDone onFault fuel₁ s →
      wpUntilPred validChoice step stop onDone onFault fuel₂ s
  | 0, _, _, _, h => wpUntilPred_stop h
  | fuel₁ + 1, 0, _, hLe, _ =>
    False.elim (Nat.not_succ_le_zero fuel₁ hLe)
  | fuel₁ + 1, fuel₂ + 1, s, hLe, h => by
    have hLe' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hLe
    cases h with
    | inl hs => exact Or.inl hs
    | inr hr =>
      refine Or.inr ⟨hr.1, fun c hc => ?_⟩
      have hc' := hr.2 c hc
      cases hStep : step c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntilPred_fuel_mono hLe' hc'
      | done _ =>
        rw [hStep] at hc'
        exact hc'
      | fault _ =>
        rw [hStep] at hc'
        exact hc'

/-- Fuel weakening `fuel₁ ≤ fuel₂` for `execUntilPred`. -/
theorem execUntilPred_fuel_mono {S Out : Type}
    {step : S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {fuel₁ fuel₂ : Nat} {s : S} (hLe : fuel₁ ≤ fuel₂)
    (h : execUntilPred step stop onDone onFault fuel₁ s) :
    execUntilPred step stop onDone onFault fuel₂ s :=
  (wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
      (c₀ := ()) (fun _ _ => Iff.rfl)).mp
    (wpUntilPred_fuel_mono hLe
      ((wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
        (c₀ := ()) (fun _ _ => Iff.rfl)).mpr h))

/-- Sequential composition of `wpUntilPred` checkpoints with budget
`f₂ + f₁`. -/
theorem wpUntilPred_bind_rev {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {mid stop : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₂ : Nat}
    (hK : ∀ s', mid s' → wpUntilPred validChoice step stop onDone onFault f₂ s') :
    ∀ {f₁ : Nat} {s : S},
      wpUntilPred validChoice step mid onDone onFault f₁ s →
      wpUntilPred validChoice step stop onDone onFault (f₂ + f₁) s
  | 0, s, h =>
    wpUntilPred_fuel_cast (Nat.add_zero f₂).symm (hK s h)
  | f₁ + 1, s, h => by
    cases h with
    | inl hm =>
      exact wpUntilPred_fuel_mono (Nat.le_add_right f₂ (f₁ + 1)) (hK s hm)
    | inr hr =>
      refine wpUntilPred_fuel_cast (Nat.add_assoc f₂ f₁ 1)
        (wpUntilPred_succ_iff.mpr (Or.inr ⟨hr.1, fun c hc => ?_⟩))
      have hc' := hr.2 c hc
      cases hStep : step c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntilPred_bind_rev hK hc'
      | done _ =>
        rw [hStep] at hc'
        exact hc'
      | fault _ =>
        rw [hStep] at hc'
        exact hc'

/-- Sequential composition of `wpUntilPred` checkpoints with budget
`f₁ + f₂`. -/
theorem wpUntilPred_bind {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {mid stop : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₁ f₂ : Nat} {s : S}
    (hFirst : wpUntilPred validChoice step mid onDone onFault f₁ s)
    (hK : ∀ s', mid s' → wpUntilPred validChoice step stop onDone onFault f₂ s') :
    wpUntilPred validChoice step stop onDone onFault (f₁ + f₂) s :=
  wpUntilPred_fuel_cast (Nat.add_comm f₂ f₁) (wpUntilPred_bind_rev hK hFirst)

/-- Helper for `wpUntilPred_bind_exists` under singleton choice `c₀`. -/
private theorem wpUntilPred_bind_exists_aux {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {mid stop : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hK : ∀ s', mid s' →
      ∃ f₂, wpUntilPred validChoice step stop onDone onFault f₂ s') :
    ∀ {f₁ : Nat} {s : S},
      wpUntilPred validChoice step mid onDone onFault f₁ s →
      ∃ F, wpUntilPred validChoice step stop onDone onFault F s
  | 0, s, h => hK s h
  | _ + 1, s, h => by
    cases h with
    | inl hm => exact hK s hm
    | inr hr =>
      have h0 := hr.2 c₀ ((hUnique s c₀).mpr rfl)
      cases hStep : step c₀ s with
      | step st' =>
        rw [hStep] at h0
        let ⟨F, hF⟩ := wpUntilPred_bind_exists_aux hUnique hK h0
        refine ⟨F + 1, wpUntilPred_step hUnique ?_⟩
        rw [hStep]
        exact hF
      | done out =>
        rw [hStep] at h0
        refine ⟨1, wpUntilPred_step hUnique ?_⟩
        rw [hStep]
        exact h0
      | fault k =>
        rw [hStep] at h0
        refine ⟨1, wpUntilPred_step hUnique ?_⟩
        rw [hStep]
        exact h0

/-- Existential sequential composition of `wpUntilPred` checkpoints under
singleton choice `c₀`. -/
theorem wpUntilPred_bind_exists {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {mid stop : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} {s : S}
    (hFirst : ∃ f₁, wpUntilPred validChoice step mid onDone onFault f₁ s)
    (hK : ∀ s', mid s' →
      ∃ f₂, wpUntilPred validChoice step stop onDone onFault f₂ s') :
    ∃ F, wpUntilPred validChoice step stop onDone onFault F s := by
  let ⟨_, h1⟩ := hFirst
  exact wpUntilPred_bind_exists_aux hUnique hK h1

/-- Hand a checkpoint proof `wpUntilPred` over to `wpStepPred` with budget
`f₂ + f₁`. -/
theorem wpUntilPred_to_wpStepPred_rev {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₂ : Nat}
    (hK : ∀ s', stop s' → wpStepPred validChoice step onDone onFault f₂ s') :
    ∀ {f₁ : Nat} {s : S},
      wpUntilPred validChoice step stop onDone onFault f₁ s →
      wpStepPred validChoice step onDone onFault (f₂ + f₁) s
  | 0, s, h => wpStepPred_fuel_cast (Nat.add_zero f₂).symm (hK s h)
  | f₁ + 1, s, h => by
    cases h with
    | inl hs => exact wpStepPred_fuel_mono (Nat.le_add_right f₂ (f₁ + 1)) (hK s hs)
    | inr hr =>
      refine wpStepPred_fuel_cast (Nat.add_assoc f₂ f₁ 1)
        (wpStepPred_succ_iff.mpr ⟨hr.1, fun c hc => ?_⟩)
      have hc' := hr.2 c hc
      cases hStep : step c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntilPred_to_wpStepPred_rev hK hc'
      | done _ =>
        rw [hStep] at hc'
        exact hc'
      | fault _ =>
        rw [hStep] at hc'
        exact hc'

/-- Hand a checkpoint proof `wpUntilPred` over to `wpStepPred` with budget
`f₁ + f₂`. -/
theorem wpUntilPred_to_wpStepPred {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₁ f₂ : Nat} {s : S}
    (h : wpUntilPred validChoice step stop onDone onFault f₁ s)
    (hK : ∀ s', stop s' → wpStepPred validChoice step onDone onFault f₂ s') :
    wpStepPred validChoice step onDone onFault (f₁ + f₂) s :=
  wpStepPred_fuel_cast (Nat.add_comm f₂ f₁) (wpUntilPred_to_wpStepPred_rev hK h)

private theorem wpUntilPred_to_wpStepPred_exists_aux {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hK : ∀ s', stop s' →
      ∃ f₂, wpStepPred validChoice step onDone onFault f₂ s') :
    ∀ {f₁ : Nat} {s : S},
      wpUntilPred validChoice step stop onDone onFault f₁ s →
      ∃ F, wpStepPred validChoice step onDone onFault F s
  | 0, s, h => hK s h
  | _ + 1, s, h => by
    cases h with
    | inl hs => exact hK s hs
    | inr hr =>
      have h0 := hr.2 c₀ ((hUnique s c₀).mpr rfl)
      cases hStep : step c₀ s with
      | step st' =>
        rw [hStep] at h0
        let ⟨F, hF⟩ := wpUntilPred_to_wpStepPred_exists_aux hUnique hK h0
        refine ⟨F + 1, wpStepPred_step hUnique ?_⟩
        rw [hStep]
        exact hF
      | done out =>
        rw [hStep] at h0
        refine ⟨1, wpStepPred_step hUnique ?_⟩
        rw [hStep]
        exact h0
      | fault k =>
        rw [hStep] at h0
        refine ⟨1, wpStepPred_step hUnique ?_⟩
        rw [hStep]
        exact h0

/-- Hand a checkpoint proof `wpUntilPred` over to `wpStepPred` with
existential continuation fuel under singleton choice `c₀`. -/
theorem wpUntilPred_to_wpStepPred_exists {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {s : S}
    (h : ∃ f₁, wpUntilPred validChoice step stop onDone onFault f₁ s)
    (hK : ∀ s', stop s' →
      ∃ f₂, wpStepPred validChoice step onDone onFault f₂ s') :
    ∃ F, wpStepPred validChoice step onDone onFault F s := by
  let ⟨_, h1⟩ := h
  exact wpUntilPred_to_wpStepPred_exists_aux hUnique hK h1

/-- Deterministic checkpoint handoff to `execStepPred`. -/
theorem execUntilPred_to_execStepPred_rev {S Out : Type}
    {step : S → StepResult S Out} {stop : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₁ f₂ : Nat} {s : S}
    (hK : ∀ s', stop s' → execStepPred step onDone onFault f₂ s')
    (h : execUntilPred step stop onDone onFault f₁ s) :
    execStepPred step onDone onFault (f₂ + f₁) s :=
  (wpStepPred_iff_execStepPred (C := Unit) (step := fun _ => step)
      (c₀ := ()) (fun _ _ => Iff.rfl)).mp
    (wpUntilPred_to_wpStepPred_rev
      (fun s' hs' =>
        (wpStepPred_iff_execStepPred (C := Unit) (step := fun _ => step)
          (c₀ := ()) (fun _ _ => Iff.rfl)).mpr (hK s' hs'))
      ((wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
        (c₀ := ()) (fun _ _ => Iff.rfl)).mpr h))

/-- Deterministic checkpoint handoff to `execStepPred` with budget `f₁ + f₂`.
-/
theorem execUntilPred_to_execStepPred {S Out : Type}
    {step : S → StepResult S Out} {stop : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₁ f₂ : Nat} {s : S}
    (h : execUntilPred step stop onDone onFault f₁ s)
    (hK : ∀ s', stop s' → execStepPred step onDone onFault f₂ s') :
    execStepPred step onDone onFault (f₁ + f₂) s :=
  execStepPred_fuel_cast (Nat.add_comm f₂ f₁)
    (execUntilPred_to_execStepPred_rev hK h)

/-- Zero-`Prop`-argument stage-cut barrier asserting that `s₀` reaches `s₁`
within `fuel` transitions of `step` without faulting or halting prematurely
(sealed `@[irreducible]` below after its core laws). -/
@[expose] def StepStageCut {S Out : Type} (step : S → StepResult S Out)
    (fuel : Nat) (s₀ s₁ : S) : Prop :=
  wpUntilCutStep step (fun st => st = s₁) fuel s₀

/-- Zero-step reflexivity at any fuel budget `fuel`. -/
theorem StepStageCut.refl {S Out : Type} (step : S → StepResult S Out)
    (fuel : Nat) (s : S) : StepStageCut step fuel s s :=
  execUntilPred_stop fuel rfl

/-- Prepend a single `.step` transition onto a `StepStageCut` derivation. -/
theorem StepStageCut.step {S Out : Type} {step : S → StepResult S Out}
    {fuel : Nat} {s₀ s₁ s₂ : S}
    (hStep : step s₀ = .step s₁)
    (hRest : StepStageCut step fuel s₁ s₂) :
    StepStageCut step (fuel + 1) s₀ s₂ :=
  execUntilPred_step hStep hRest

/-- Fuel weakening `f₁ ≤ f₂` for `StepStageCut`. -/
theorem StepStageCut.fuel_mono {S Out : Type} {step : S → StepResult S Out}
    {f₁ f₂ : Nat} {s₀ s₁ : S} (hLe : f₁ ≤ f₂)
    (h : StepStageCut step f₁ s₀ s₁) : StepStageCut step f₂ s₀ s₁ :=
  execUntilPred_fuel_mono hLe h

/-- Sequential composition of `StepStageCut` segments (`f₁ + f₂` steps). -/
theorem StepStageCut.trans {S Out : Type} {step : S → StepResult S Out}
    {f₁ f₂ : Nat} {s₀ s₁ s₂ : S}
    (h₀₁ : StepStageCut step f₁ s₀ s₁)
    (h₁₂ : StepStageCut step f₂ s₁ s₂) :
    StepStageCut step (f₁ + f₂) s₀ s₂ := by
  have hK : ∀ sc, sc = s₁ →
      wpUntilPred (fun (_ : S) (c : Unit) => c = ()) (fun _ => step)
        (fun st => st = s₂) (fun _ _ => False) (fun _ _ => False) f₂ sc := by
    intro sc he
    subst he
    exact (wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
      (c₀ := ()) (fun _ _ => Iff.rfl)).mpr h₁₂
  exact (wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
      (c₀ := ()) (fun _ _ => Iff.rfl)).mp
    (wpUntilPred_bind
      ((wpUntilPred_iff_execUntilPred (C := Unit) (step := fun _ => step)
        (c₀ := ()) (fun _ _ => Iff.rfl)).mpr h₀₁)
      hK)

private theorem execUntilPred_congr_step {S Out : Type}
    {step₁ step₂ : S → StepResult S Out}
    (hEq : ∀ s : S, step₁ s = step₂ s)
    {stop : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop} :
    ∀ {fuel : Nat} {s₀ : S},
      execUntilPred step₁ stop onDone onFault fuel s₀ →
      execUntilPred step₂ stop onDone onFault fuel s₀
  | 0, _, h => h
  | _ + 1, s₀, h => by
    cases h with
    | inl hs => exact Or.inl hs
    | inr hSt =>
      refine Or.inr ?_
      change (match step₁ s₀ with
        | .step st' => execUntilPred step₁ stop onDone onFault _ st'
        | .done out => onDone s₀ out
        | .fault k => onFault s₀ k) at hSt
      change (match step₂ s₀ with
        | .step st' => execUntilPred step₂ stop onDone onFault _ st'
        | .done out => onDone s₀ out
        | .fault k => onFault s₀ k)
      rw [← hEq s₀]
      cases hEv : step₁ s₀ with
      | step st' =>
        rw [hEv] at hSt
        exact execUntilPred_congr_step hEq hSt
      | done out =>
        rw [hEv] at hSt
        exact hSt
      | fault k =>
        rw [hEv] at hSt
        exact hSt

/-- Pointwise transition congruence for `StepStageCut`. -/
theorem StepStageCut.congr_step {S Out : Type}
    {step₁ step₂ : S → StepResult S Out}
    (hEq : ∀ s : S, step₁ s = step₂ s) {fuel : Nat} {s₀ s₁ : S} :
    StepStageCut step₁ fuel s₀ s₁ ↔ StepStageCut step₂ fuel s₀ s₁ :=
  ⟨execUntilPred_congr_step hEq,
   execUntilPred_congr_step (fun s => (hEq s).symm)⟩

/-- Base introduction rule for `wpUntilCutStep` when `cut s` already holds. -/
theorem wpUntilCutStep_here {S Out : Type} {step : S → StepResult S Out}
    {cut : S → Prop} (fuel : Nat) {s : S} (h : cut s) :
    wpUntilCutStep step cut fuel s :=
  execUntilPred_stop fuel h

/-- Single-step introduction rule for `wpUntilCutStep`. -/
theorem wpUntilCutStep_step {S Out : Type} {step : S → StepResult S Out}
    {cut : S → Prop} {fuel : Nat} {s s' : S}
    (hStep : step s = .step s')
    (hNext : wpUntilCutStep step cut fuel s') :
    wpUntilCutStep step cut (fuel + 1) s :=
  execUntilPred_step hStep hNext

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
      | inl hc => exact ⟨s₀, StepStageCut.refl step (n + 1) s₀, hc⟩
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
          exact ⟨s₁, StepStageCut.step hEv hReach, hc⟩
        | done _ => rw [hEv] at hSt; exact False.elim hSt
        | fault _ => rw [hEv] at hSt; exact False.elim hSt
    · intro hEx
      let ⟨s₁, hReach, hc⟩ := hEx
      have hU :
          execUntilPred step (fun st => st = s₁)
            (fun _ _ => False) (fun _ _ => False) (n + 1) s₀ := hReach
      exact execUntilPred_mono (fun _ he => by subst he; exact hc)
        (fun _ _ h => h) (fun _ _ h => h) hU

/-- Postcondition monotonicity for `wpUntilCutStep`. -/
theorem wpUntilCutStep_mono {S Out : Type} {step : S → StepResult S Out}
    {c₁ c₂ : S → Prop} (hImp : ∀ s, c₁ s → c₂ s)
    {fuel : Nat} {s₀ : S} (h : wpUntilCutStep step c₁ fuel s₀) :
    wpUntilCutStep step c₂ fuel s₀ :=
  execUntilPred_mono hImp (fun _ _ x => x) (fun _ _ x => x) h

/-- Fuel monotonicity for `wpUntilCutStep`. -/
theorem wpUntilCutStep_fuel_mono {S Out : Type} {step : S → StepResult S Out}
    {cut : S → Prop} {f₁ f₂ : Nat} {s₀ : S} (hLe : f₁ ≤ f₂)
    (h : wpUntilCutStep step cut f₁ s₀) :
    wpUntilCutStep step cut f₂ s₀ :=
  execUntilPred_fuel_mono hLe h

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

/-- Prepend a deterministic `StepStageCut` prefix onto `execStepPred`. -/
theorem execStepPred_of_stepStageCut {S Out : Type}
    {step : S → StepResult S Out}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₁ f₂ : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut step f₁ s₀ s₁)
    (hCont : execStepPred step onDone onFault f₂ s₁) :
    execStepPred step onDone onFault (f₁ + f₂) s₀ := by
  have hCutU :
      execUntilPred step (fun st => st = s₁)
        (fun _ _ => False) (fun _ _ => False) f₁ s₀ := hCut
  have hUntil : execUntilPred step (fun st => st = s₁) onDone onFault f₁ s₀ :=
    execUntilPred_mono (fun _ h => h) (fun _ _ h => False.elim h)
      (fun _ _ h => False.elim h) hCutU
  exact execUntilPred_to_execStepPred hUntil
    (fun _ he => by subst he; exact hCont)

/-- Prepend a `StepStageCut` prefix onto singleton-choice `wpStepPred`. -/
theorem wpStepPred_of_stepStageCut {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₁ f₂ : Nat} {s₀ s₁ : S}
    (hCut : StepStageCut (step c₀) f₁ s₀ s₁)
    (hCont : wpStepPred validChoice step onDone onFault f₂ s₁) :
    wpStepPred validChoice step onDone onFault (f₁ + f₂) s₀ :=
  wpStepPred_of_execStepPred hUnique
    (execStepPred_of_stepStageCut hCut
      (execStepPred_of_wpStepPred hUnique hCont))

/-- Composes a `wpUntilCutStep (step c₀)` prefix with a `wpStepPred`
continuation under singleton choice `c₀`. -/
theorem wpStepPred_of_wpUntilCutStep {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {cut : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {f₁ f₂ : Nat} {s₀ : S}
    (hPre : wpUntilCutStep (step c₀) cut f₁ s₀)
    (hCont : ∀ sc : S, cut sc →
      wpStepPred validChoice step onDone onFault f₂ sc) :
    wpStepPred validChoice step onDone onFault (f₁ + f₂) s₀ := by
  let ⟨s₁, hCut, hc⟩ := wpUntilCutStep_iff_exists_stepStageCut.mp hPre
  exact wpStepPred_of_stepStageCut hUnique hCut (hCont s₁ hc)

attribute [irreducible] StepStageCut

/-! ## 4. Generic Loop Induction, Simulation & Early-Return Cut Loops -/

/-- Well-founded (`Acc rel`) loop-invariant induction over `wpUntilPred`:
if `(a, s)` satisfies `Inv a s` with `Acc rel a`, and every non-`Exit` step
advances in some fuel `f` to `Exit` or to `(a', s')` with `rel a' a` and
`Inv a' s'`, then `s` reaches `Exit` in finite total fuel. -/
theorem wpLoop_acc_exists {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {rel : α → α → Prop} {Inv : α → S → Prop} {Exit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hStep : ∀ a s, Inv a s →
      Exit s ∨ ∃ f, wpUntilPred validChoice step
        (fun s' => (∃ a', rel a' a ∧ Inv a' s') ∨ Exit s')
        onDone onFault f s)
    {a : α} (hAcc : Acc rel a) :
    ∀ s : S, Inv a s →
      ∃ F, wpUntilPred validChoice step Exit onDone onFault F s := by
  induction hAcc with
  | intro x _ ih =>
    intro s hInv
    cases hStep x s hInv with
    | inl hExit => exact ⟨0, wpUntilPred_stop hExit⟩
    | inr hIter =>
      refine wpUntilPred_bind_exists hUnique
        (mid := fun s' => (∃ a', rel a' x ∧ Inv a' s') ∨ Exit s')
        hIter ?_
      intro s' hMid
      cases hMid with
      | inl hCont =>
        let ⟨a', hRel, hInv'⟩ := hCont
        exact ih a' hRel s' hInv'
      | inr hExit' => exact ⟨0, wpUntilPred_stop hExit'⟩

/-- Bounded `Nat`-variant loop rule with fixed per-iteration fuel. -/
theorem wpLoop_nat_le {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {Inv Exit : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : S → Nat} {stepFuel : Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧
        wpUntilPred validChoice step
          (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault stepFuel s)) :
    ∀ (n : Nat) (s : S), Inv s → rank s ≤ n →
      wpUntilPred validChoice step Exit onDone onFault (n * stepFuel) s := by
  intro n
  induction n with
  | zero =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact wpUntilPred_stop hExit
    | inr hIter =>
      exact False.elim
        (Nat.not_lt_zero 0 (Nat.lt_of_lt_of_le hIter.1 hLe))
  | succ n ih =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact wpUntilPred_stop hExit
    | inr hIter =>
      have hK : ∀ s', ((Inv s' ∧ rank s' < rank s) ∨ Exit s') →
          wpUntilPred validChoice step Exit onDone onFault (n * stepFuel) s' := by
        intro s' hMid
        cases hMid with
        | inl hCont =>
          exact ih s' hCont.1
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hCont.2 hLe))
        | inr hExit' => exact wpUntilPred_stop hExit'
      exact wpUntilPred_fuel_cast (Nat.succ_mul n stepFuel).symm
        (wpUntilPred_bind_rev
          (mid := fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          hK hIter.2)

/-- Fixed-budget `Nat`-variant loop rule (`rank s * stepFuel`). -/
theorem wpLoop_nat {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {Inv Exit : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : S → Nat} {stepFuel : Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧
        wpUntilPred validChoice step
          (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault stepFuel s))
    (s : S) (hInv : Inv s) :
    wpUntilPred validChoice step Exit onDone onFault (rank s * stepFuel) s :=
  wpLoop_nat_le hStep (rank s) s hInv (Nat.le_refl (rank s))

private theorem wpLoop_nat_exists_aux {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv Exit : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : S → Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧ ∃ f,
        wpUntilPred validChoice step
          (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault f s)) :
    ∀ (n : Nat) (s : S), Inv s → rank s ≤ n →
      ∃ F, wpUntilPred validChoice step Exit onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact ⟨0, wpUntilPred_stop hExit⟩
    | inr hIter =>
      exact False.elim
        (Nat.not_lt_zero 0 (Nat.lt_of_lt_of_le hIter.1 hLe))
  | succ n ih =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact ⟨0, wpUntilPred_stop hExit⟩
    | inr hIter =>
      refine wpUntilPred_bind_exists hUnique
        (mid := fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
        hIter.2 ?_
      intro s' hMid
      cases hMid with
      | inl hCont =>
        exact ih s' hCont.1
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hCont.2 hLe))
      | inr hExit' => exact ⟨0, wpUntilPred_stop hExit'⟩

/-- Variable-budget `Nat`-variant loop rule under singleton choice `c₀`. -/
theorem wpLoop_nat_exists {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv Exit : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : S → Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧ ∃ f,
        wpUntilPred validChoice step
          (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault f s))
    (s : S) (hInv : Inv s) :
    ∃ F, wpUntilPred validChoice step Exit onDone onFault F s :=
  wpLoop_nat_exists_aux hUnique hStep (rank s) s hInv (Nat.le_refl (rank s))

/-- Exact countdown loop rule with variable per-iteration budget. -/
theorem wpLoop_countdown {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv : Nat → S → Prop} {Exit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hBase : ∀ s, Inv 0 s → Exit s)
    (hStep : ∀ n s, Inv (n + 1) s →
      ∃ f, wpUntilPred validChoice step (fun s' => Inv n s' ∨ Exit s')
        onDone onFault f s) :
    ∀ (n : Nat) (s : S), Inv n s →
      ∃ F, wpUntilPred validChoice step Exit onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro s hInv
    exact ⟨0, wpUntilPred_stop (hBase s hInv)⟩
  | succ n ih =>
    intro s hInv
    refine wpUntilPred_bind_exists hUnique
      (mid := fun s' => Inv n s' ∨ Exit s') (hStep n s hInv) ?_
    intro s' hMid
    cases hMid with
    | inl hCont => exact ih s' hCont
    | inr hExit => exact ⟨0, wpUntilPred_stop hExit⟩

/-- Exact countdown loop rule with fixed per-iteration budget `stepFuel`. -/
theorem wpLoop_countdown_fuel {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {Inv : Nat → S → Prop} {Exit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {stepFuel : Nat}
    (hBase : ∀ s, Inv 0 s → Exit s)
    (hStep : ∀ n s, Inv (n + 1) s →
      wpUntilPred validChoice step (fun s' => Inv n s' ∨ Exit s')
        onDone onFault stepFuel s) :
    ∀ (n : Nat) (s : S), Inv n s →
      wpUntilPred validChoice step Exit onDone onFault (n * stepFuel) s := by
  intro n
  induction n with
  | zero =>
    intro s hInv
    exact wpUntilPred_stop (hBase s hInv)
  | succ n ih =>
    intro s hInv
    have hK : ∀ s', (Inv n s' ∨ Exit s') →
        wpUntilPred validChoice step Exit onDone onFault (n * stepFuel) s' := by
      intro s' hMid
      cases hMid with
      | inl hCont => exact ih s' hCont
      | inr hExit => exact wpUntilPred_stop hExit
    exact wpUntilPred_fuel_cast (Nat.succ_mul n stepFuel).symm
      (wpUntilPred_bind_rev (mid := fun s' => Inv n s' ∨ Exit s') hK
        (hStep n s hInv))

/-- Structural list-traversal loop rule over `wpUntilPred`. -/
theorem wpLoop_list {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv : List α → S → Prop} {Exit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ x xs s, Inv (x :: xs) s →
      ∃ f, wpUntilPred validChoice step (fun s' => Inv xs s' ∨ Exit s')
        onDone onFault f s) :
    ∀ (xs : List α) (s : S), Inv xs s →
      ∃ F, wpUntilPred validChoice step Exit onDone onFault F s := by
  intro xs
  induction xs with
  | nil =>
    intro s hInv
    exact ⟨0, wpUntilPred_stop (hBase s hInv)⟩
  | cons x xs ih =>
    intro s hInv
    refine wpUntilPred_bind_exists hUnique
      (mid := fun s' => Inv xs s' ∨ Exit s') (hStep x xs s hInv) ?_
    intro s' hMid
    cases hMid with
    | inl hCont => exact ih s' hCont
    | inr hExit => exact ⟨0, wpUntilPred_stop hExit⟩

/-- A suffix is no longer than the list it ends. -/
theorem length_le_append {α : Type} (pre rest : List α) :
    rest.length ≤ (pre ++ rest).length := by
  induction pre with
  | nil => exact Nat.le_refl rest.length
  | cons x pre ih => exact Nat.le_succ_of_le ih

/-- Removing a non-empty prefix strictly shortens a list. -/
theorem length_lt_append_of_ne_nil {α : Type} (pre rest : List α)
    (hNe : pre ≠ []) : rest.length < (pre ++ rest).length := by
  cases pre with
  | nil => exact False.elim (hNe rfl)
  | cons x pre => exact Nat.lt_succ_of_le (length_le_append pre rest)

private theorem wpLoop_list_measure_aux {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv : List α → S → Prop} {Exit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      ∃ f, wpUntilPred validChoice step
        (fun s' => (∃ ys, ys.length < xs.length ∧ Inv ys s') ∨ Exit s')
        onDone onFault f s) :
    ∀ (n : Nat) (xs : List α) (s : S), Inv xs s → xs.length ≤ n →
      ∃ F, wpUntilPred validChoice step Exit onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro xs s hInv hLe
    cases xs with
    | nil => exact ⟨0, wpUntilPred_stop (hBase s hInv)⟩
    | cons x rest =>
      exact False.elim (Nat.not_succ_le_zero rest.length hLe)
  | succ n ih =>
    intro xs s hInv hLe
    cases xs with
    | nil => exact ⟨0, wpUntilPred_stop (hBase s hInv)⟩
    | cons x rest =>
      have hNe : x :: rest ≠ [] := by
        intro hEq
        cases hEq
      refine wpUntilPred_bind_exists hUnique
        (mid := fun s' =>
          (∃ ys, ys.length < (x :: rest).length ∧ Inv ys s') ∨ Exit s')
        (hStep (x :: rest) s hInv hNe) ?_
      intro s' hMid
      cases hMid with
      | inl hCont =>
        let ⟨ys, hLt, hInvYs⟩ := hCont
        exact ih ys s' hInvYs
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hLe))
      | inr hExit => exact ⟨0, wpUntilPred_stop hExit⟩

/-- List loop rule by length over `wpUntilPred`. -/
theorem wpLoop_list_measure {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv : List α → S → Prop} {Exit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      ∃ f, wpUntilPred validChoice step
        (fun s' => (∃ ys, ys.length < xs.length ∧ Inv ys s') ∨ Exit s')
        onDone onFault f s)
    (xs : List α) (s : S) (hInv : Inv xs s) :
    ∃ F, wpUntilPred validChoice step Exit onDone onFault F s :=
  wpLoop_list_measure_aux hUnique hBase hStep xs.length xs s hInv
    (Nat.le_refl xs.length)

/-- Chunked list-traversal loop rule over `wpUntilPred`. -/
theorem wpLoop_list_split {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv : List α → S → Prop} {Exit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      ∃ f, wpUntilPred validChoice step
        (fun s' =>
          (∃ pre rest, xs = pre ++ rest ∧ pre ≠ [] ∧ Inv rest s') ∨
            Exit s')
        onDone onFault f s)
    (xs : List α) (s : S) (hInv : Inv xs s) :
    ∃ F, wpUntilPred validChoice step Exit onDone onFault F s := by
  refine wpLoop_list_measure hUnique hBase ?_ xs s hInv
  intro ys t hInvYs hNe
  let ⟨f, hf⟩ := hStep ys t hInvYs hNe
  refine ⟨f, wpUntilPred_mono ?_ (fun _ _ h => h) (fun _ _ h => h) hf⟩
  intro t' hMid
  cases hMid with
  | inl hSplit =>
    let ⟨pre, rest, hEq, hPre, hInvRest⟩ := hSplit
    subst hEq
    exact Or.inl ⟨rest, length_lt_append_of_ne_nil pre rest hPre, hInvRest⟩
  | inr hExit => exact Or.inr hExit

/-- Breakable `Nat`-variant loop rule feeding into `wpStepPred`. -/
theorem wpLoop_nat_or_done {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {Inv Exit : S → Prop} {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : S → Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧ ∃ f,
        wpUntilPred validChoice step
          (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault f s))
    (hExit : ∀ s, Exit s →
      ∃ f, wpStepPred validChoice step onDone onFault f s)
    (s : S) (hInv : Inv s) :
    ∃ F, wpStepPred validChoice step onDone onFault F s :=
  wpUntilPred_to_wpStepPred_exists hUnique
    (wpLoop_nat_exists hUnique hStep s hInv) hExit

/-- Reflexive-transitive closure of an abstract step relation. -/
inductive ReflTrans {α : Type} (step : α → α → Prop) : α → α → Prop where
  | refl (a : α) : ReflTrans step a a
  | head {a b c : α} :
      step a b → ReflTrans step b c → ReflTrans step a c

private theorem wpSim_rel_aux {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {StepAbs : α → α → Prop} {DoneAbs : α → Prop}
    {R : α → S → Prop} {Exit : α → S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (DoneAbs a ∧ Exit a s) ∨
      (∃ a', StepAbs a a' ∧ rank a' < rank a ∧
        ∃ f, wpUntilPred validChoice step (fun s' => R a' s')
          onDone onFault f s)) :
    ∀ (n : Nat) (a : α) (s : S), R a s → rank a ≤ n →
      ∃ F, wpUntilPred validChoice step
        (fun s' => ∃ a', ReflTrans StepAbs a a' ∧ DoneAbs a' ∧ Exit a' s')
        onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro a s hR hLe
    cases hSim a s hR with
    | inl hDone =>
      exact ⟨0, wpUntilPred_stop ⟨a, ReflTrans.refl a, hDone.1, hDone.2⟩⟩
    | inr hNext =>
      let ⟨a', _, hLt, _⟩ := hNext
      exact False.elim
        (Nat.not_lt_zero (rank a') (Nat.lt_of_lt_of_le hLt hLe))
  | succ n ih =>
    intro a s hR hLe
    cases hSim a s hR with
    | inl hDone =>
      exact ⟨0, wpUntilPred_stop ⟨a, ReflTrans.refl a, hDone.1, hDone.2⟩⟩
    | inr hNext =>
      let ⟨a', hAbs, hLt, hIter⟩ := hNext
      refine wpUntilPred_bind_exists hUnique (mid := fun s' => R a' s')
        hIter ?_
      intro s' hR'
      let ⟨F, hF⟩ := ih a' s' hR'
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hLe))
      refine ⟨F, wpUntilPred_mono ?_ (fun _ _ h => h) (fun _ _ h => h) hF⟩
      intro t hStop
      let ⟨aF, hRT, hD, hE⟩ := hStop
      exact ⟨aF, ReflTrans.head hAbs hRT, hD, hE⟩

/-- Relational simulation rule over `wpUntilPred`. -/
theorem wpSim_rel {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {StepAbs : α → α → Prop} {DoneAbs : α → Prop}
    {R : α → S → Prop} {Exit : α → S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (DoneAbs a ∧ Exit a s) ∨
      (∃ a', StepAbs a a' ∧ rank a' < rank a ∧
        ∃ f, wpUntilPred validChoice step (fun s' => R a' s')
          onDone onFault f s))
    (a : α) (s : S) (hR : R a s) :
    ∃ F, wpUntilPred validChoice step
      (fun s' => ∃ a', ReflTrans StepAbs a a' ∧ DoneAbs a' ∧ Exit a' s')
      onDone onFault F s :=
  wpSim_rel_aux hUnique hSim (rank a) a s hR (Nat.le_refl (rank a))

/-- Iterate abstract step function `stepAbs` at most `k` times until `none`.
-/
@[expose] def runAbsFuel {α : Type} (stepAbs : α → Option α) (k : Nat)
    (a : α) : α :=
  @Nat.rec (fun _ => α → α)
    (fun a => a)
    (fun _ ih a =>
      match stepAbs a with
      | some a' => ih a'
      | none => a)
    k a

/-- One more iteration of `runAbsFuel` from a state that can step. -/
theorem runAbsFuel_succ_of_some {α : Type} {stepAbs : α → Option α}
    {a a' : α} (h : stepAbs a = some a') (k : Nat) :
    runAbsFuel stepAbs (k + 1) a = runAbsFuel stepAbs k a' := by
  change (match stepAbs a with
    | some b => runAbsFuel stepAbs k b
    | none => a) = runAbsFuel stepAbs k a'
  cases hE : stepAbs a with
  | none =>
    rw [hE] at h
    cases h
  | some b =>
    rw [hE] at h
    injection h with hEq
    subst hEq
    rfl

private theorem wpSim_det_aux {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stepAbs : α → Option α} {R : α → S → Prop} {Exit : α → S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        ∃ f, wpUntilPred validChoice step (fun s' => R a' s')
          onDone onFault f s)) :
    ∀ (n : Nat) (a : α) (s : S), R a s → rank a ≤ n →
      ∃ F, wpUntilPred validChoice step
        (fun s' => ∃ k, k ≤ n ∧
          stepAbs (runAbsFuel stepAbs k a) = none ∧
          R (runAbsFuel stepAbs k a) s' ∧
          Exit (runAbsFuel stepAbs k a) s')
        onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro a s hR hLe
    cases hOpt : stepAbs a with
    | none =>
      exact ⟨0, wpUntilPred_stop ⟨0, Nat.le_refl 0, hOpt, hR, (hSim a s hR).1 hOpt⟩⟩
    | some a' =>
      exact False.elim
        (Nat.not_lt_zero (rank a')
          (Nat.lt_of_lt_of_le ((hSim a s hR).2 a' hOpt).1 hLe))
  | succ n ih =>
    intro a s hR hLe
    cases hOpt : stepAbs a with
    | none =>
      exact ⟨0, wpUntilPred_stop
        ⟨0, Nat.zero_le (n + 1), hOpt, hR, (hSim a s hR).1 hOpt⟩⟩
    | some a' =>
      have hNext := (hSim a s hR).2 a' hOpt
      refine wpUntilPred_bind_exists hUnique (mid := fun s' => R a' s')
        hNext.2 ?_
      intro s' hR'
      let ⟨F, hF⟩ := ih a' s' hR'
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hNext.1 hLe))
      refine ⟨F, wpUntilPred_mono ?_ (fun _ _ h => h) (fun _ _ h => h) hF⟩
      intro t hStop
      let ⟨k, hk, hNone, hRk, hEk⟩ := hStop
      have hRun :
          runAbsFuel stepAbs (k + 1) a = runAbsFuel stepAbs k a' :=
        runAbsFuel_succ_of_some hOpt k
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_, ?_, ?_⟩
      · rw [hRun]; exact hNone
      · rw [hRun]; exact hRk
      · rw [hRun]; exact hEk

/-- Deterministic simulation rule with exact abstract run `runAbsFuel`. -/
theorem wpSim_det_run {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stepAbs : α → Option α} {R : α → S → Prop} {Exit : α → S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        ∃ f, wpUntilPred validChoice step (fun s' => R a' s')
          onDone onFault f s))
    (a : α) (s : S) (hR : R a s) :
    ∃ F, wpUntilPred validChoice step
      (fun s' => ∃ k, k ≤ rank a ∧
        stepAbs (runAbsFuel stepAbs k a) = none ∧
        R (runAbsFuel stepAbs k a) s' ∧
        Exit (runAbsFuel stepAbs k a) s')
      onDone onFault F s :=
  wpSim_det_aux hUnique hSim (rank a) a s hR (Nat.le_refl (rank a))

/-- Deterministic simulation rule reaching a halted abstract state. -/
theorem wpSim_det {α S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {stepAbs : α → Option α} {R : α → S → Prop} {Exit : α → S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        ∃ f, wpUntilPred validChoice step (fun s' => R a' s')
          onDone onFault f s))
    (a : α) (s : S) (hR : R a s) :
    ∃ F, wpUntilPred validChoice step
      (fun s' => ∃ aFinal,
        stepAbs aFinal = none ∧ R aFinal s' ∧ Exit aFinal s')
      onDone onFault F s := by
  let ⟨F, hF⟩ := wpSim_det_run hUnique hSim a s hR
  refine ⟨F, wpUntilPred_mono ?_ (fun _ _ h => h) (fun _ _ h => h) hF⟩
  intro t hStop
  let ⟨k, _, hNone, hRk, hEk⟩ := hStop
  exact ⟨runAbsFuel stepAbs k a, hNone, hRk, hEk⟩

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

/-- Bounded loop invariant driver supporting both normal loop exit and
early-return exit over `wpUntilCutStep step`. -/
@[expose] def wpIterCut {S Out : Type} (step : S → StepResult S Out)
    (inv earlyClean normalExit : S → Prop)
    (stepBudget iters : Nat) (s : S) : Prop :=
  @Nat.rec (fun _ => S → Prop)
    (fun st => normalExit st ∨ earlyClean st)
    (fun _ ih st =>
      normalExit st ∨ earlyClean st ∨
        (inv st ∧ wpUntilCutStep step ih stepBudget st))
    iters s

/-- Soundness of `wpIterCut` into singleton-choice `wpStepPred`. -/
theorem wpStepPred_loop_early_return_sound {S Out C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out}
    {c₀ : C} (hUnique : ∀ s c, validChoice s c ↔ c = c₀)
    {inv earlyClean normalExit : S → Prop}
    {onDone : S → Out → Prop} {onFault : S → FaultKind → Prop}
    {stepBudget iters fuelNormal fuelEarly : Nat} {s : S}
    (hLoop : wpIterCut (step c₀) inv earlyClean normalExit stepBudget iters s)
    (hNorm : ∀ st : S, normalExit st →
      wpStepPred validChoice step onDone onFault fuelNormal st)
    (hEarly : ∀ st : S, earlyClean st →
      wpStepPred validChoice step onDone onFault fuelEarly st) :
    wpStepPred validChoice step onDone onFault
      (iters * stepBudget + compNatMax fuelNormal fuelEarly) s := by
  induction iters generalizing s with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add]
    cases hLoop with
    | inl hn =>
      exact wpStepPred_fuel_mono
        (le_compNatMax_left fuelNormal fuelEarly) (hNorm s hn)
    | inr he =>
      exact wpStepPred_fuel_mono
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
      exact wpStepPred_fuel_mono hLe (hNorm s hn)
    | inr hRest =>
      cases hRest with
      | inl he =>
        have hLe : fuelEarly ≤
            stepBudget + (k * stepBudget + compNatMax fuelNormal fuelEarly) :=
          Nat.le_trans (le_compNatMax_right fuelNormal fuelEarly)
            (Nat.le_trans
              (Nat.le_add_left (compNatMax fuelNormal fuelEarly)
                (k * stepBudget))
              (Nat.le_add_left _ stepBudget))
        exact wpStepPred_fuel_mono hLe (hEarly s he)
      | inr hAnd =>
        exact wpStepPred_of_wpUntilCutStep hUnique hAnd.2
          (fun _ hNext => ih hNext)

/-- Inductive introduction rule for `wpIterCut`. -/
theorem wpIterCut_of_step {S Out : Type} {step : S → StepResult S Out}
    {inv : Nat → S → Prop} {earlyClean normalExit : S → Prop}
    {stepBudget : Nat}
    (hZero : ∀ st : S, inv 0 st → normalExit st ∨ earlyClean st)
    (hStep : ∀ (k : Nat) (st : S), inv (k + 1) st →
      normalExit st ∨ earlyClean st ∨
        wpUntilCutStep step
          (fun st' => inv k st' ∨ normalExit st' ∨ earlyClean st')
          stepBudget st) :
    ∀ {iters : Nat} {s : S},
      inv iters s →
      wpIterCut step (fun st => ∃ m : Nat, inv m st)
        earlyClean normalExit stepBudget iters s
  | 0, s, hInv => hZero s hInv
  | k + 1, s, hInv => by
    cases hStep k s hInv with
    | inl hNorm => exact Or.inl hNorm
    | inr hRest =>
      cases hRest with
      | inl hEarly => exact Or.inr (Or.inl hEarly)
      | inr hCut =>
        refine Or.inr (Or.inr ⟨⟨k + 1, hInv⟩, ?_⟩)
        refine wpUntilCutStep_mono (fun st' hNext => ?_) hCut
        cases hNext with
        | inl hInvK => exact wpIterCut_of_step hZero hStep hInvK
        | inr hExit =>
          cases k with
          | zero => exact hExit
          | succ _ =>
            cases hExit with
            | inl hn => exact Or.inl hn
            | inr he => exact Or.inr (Or.inl he)

/-- Deterministic `Nat`-ranked termination over `execStepPred`: if every
`Inv s` state either exits (`Exit s ∧ step s = .done s`) or takes one
`.step s'` decreasing `rank s' < rank s`, then `rank s ≤ fuel` suffices for
`execStepPred step (fun _ out => out = sFinal) (fun _ _ => False) (fuel + 1) s`
with `Inv sFinal` and `Exit sFinal`. -/
theorem execStep_nat_rank_done {S : Type}
    (step : S → StepResult S S)
    (Inv Exit : S → Prop) (rank : S → Nat)
    (hStep : ∀ s, Inv s →
      (Exit s ∧ step s = .done s) ∨
      (∃ s', step s = .step s' ∧ Inv s' ∧ rank s' < rank s)) :
    ∀ fuel s, Inv s → rank s ≤ fuel →
      ∃ sFinal,
        execStepPred step (fun _ out => out = sFinal) (fun _ _ => False)
          (fuel + 1) s ∧
        Inv sFinal ∧ Exit sFinal
  | 0, s, hInv, hRank => by
    cases hStep s hInv with
    | inl hDone =>
      refine ⟨s, ?_, hInv, hDone.1⟩
      rw [execStepPred_succ_iff, hDone.2]
    | inr hNext =>
      let ⟨_, _, _, hLt⟩ := hNext
      exact False.elim
        (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hLt hRank))
  | k + 1, s, hInv, hRank => by
    cases hStep s hInv with
    | inl hDone =>
      refine ⟨s, ?_, hInv, hDone.1⟩
      rw [execStepPred_succ_iff, hDone.2]
    | inr hNext =>
      let ⟨s', hS', hInv', hLt⟩ := hNext
      let ⟨sFinal, hExec, hInvF, hExitF⟩ :=
        execStep_nat_rank_done step Inv Exit rank hStep k s' hInv'
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hRank))
      refine ⟨sFinal, ?_, hInvF, hExitF⟩
      rw [execStepPred_succ_iff, hS']
      exact hExec

end Anneal.Framework.StepWp

end
