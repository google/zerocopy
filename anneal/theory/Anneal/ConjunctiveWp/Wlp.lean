-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.MirWp
public import Anneal.LoopInv
public import Anneal.Core.StageCut

public section

/-!
# Conjunctive WP, Anti-Monotonic `wlp`, Divergence Certificates, & Doubling Fuel

This untrusted `theory/` module extends `Anneal.MirWp`, `Anneal.LoopInv`, and
module `Anneal.Core.StageCut` (`Anneal.Core.wlpOutcomeState`,
`Anneal.Core.compNatMin`) with four reusable verification combinators over
`Trusted.MirSemantics`:

1. **Deterministic `execWlp*`, Anti-Monotonicity, & Asymmetric Two-Pass Rules:**
   pairs `Anneal.Core.wlpOutcomeState` with deterministic `c = 0` fast-path
   `execWlpOutcomeState` / `execWlpState` / `execWlpProg` (reducible by `rfl` on
   concrete states), proves fuel anti-monotonicity (`wlpOutcomeState_fuel_anti`:
   checking `fuel₂` steps implies checking `fuel₁ ≤ fuel₂` steps), lifts
   `wpOutcomeState` into `wlpOutcomeState`, and derives asymmetric-fuel two-pass
   combinations (`wpOutcomeState_of_wlp_and_safety_le`,
   `wpState_of_wlp_and_safety_le`, `wpProg_of_wlp_and_safety_le`,
   `wellFormed_and_spec_of_wlp_and_safety_le`) whenever `fuelSafe ≤ fuelWlp`.
2. **Minimum-Budget Conjunctive Composition (`compNatMin`):** combines two
   independent `wlpOutcomeState`, `wpOutcomeState`, `wpProg`, or `wpUntil`
   derivations at distinct fuel budgets `n₁` and `n₂` into their conjoined
   postcondition at `compNatMin n₁ n₂`.
3. **Productive State-Transition Divergence Certificates:** defines
   `ProductiveStepWitness p next inv` and proves `diverges_of_productiveWitness`
   and `divergesAtChoices_of_productiveWitness`, establishing both
   `Trusted.MirSemantics.Diverges` and `DivergesAtChoices p q (fun _ => 0)`
   constructively via `@Nat.rec` without classical choice.
4. **Logarithmic Binary-Doubling Fuel (`wpPow2Cont`, `execPow2Cont`):** composes
   up to `2^k` MIR steps in `@Nat.rec` depth `k` via continuation-passing
   doubling, proving $O(k)$ invariant lifting (`wpPow2Cont_inv`,
   `wlpOutcomeState_of_wpPow2Cont`), exact equivalence
   (`wpPow2_iff_wpOutcomeState`, `wpProgPow2_iff_wpProg`) to `wpOutcomeState` /
   `wpProg` at `pow2Fuel k`, and direct adequacy
   (`wellFormed_and_spec_of_wpProgPow2`, `positiveCanary_of_execProgPow2`).

All authored definitions are `0` `noncomputable`, `0` `._unsafe_rec`, and `0`
`omega`. Five public declarations (`compNatMin_succ_succ`, `iterState`,
`pow2Fuel`, `pow2Fuel_succ`, `pow2Fuel_eq_pow2`) use `[]` zero axioms; the
remaining 48 public declarations over `Trusted.MirSemantics` use `[propext]`
only (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.ConjunctiveWp

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirWp Anneal.LoopInv Anneal.Core

/-! ## Part I: Deterministic `execWlp*`, Anti-Monotonicity, & Asymmetric WLP -/

/-- Successor reduction for `Anneal.Core.compNatMin`. -/
theorem compNatMin_succ_succ (a b : Nat) :
    compNatMin (a + 1) (b + 1) = compNatMin a b + 1 := by
  dsimp only [compNatMin]
  change (if Nat.ble a b = true then a + 1 else b + 1) =
    (if Nat.ble a b = true then a else b) + 1
  cases Nat.ble a b <;> rfl

/-- State-level weakest liberal precondition forbidding all faults while
allowing fuel exhaustion, built atop `Anneal.Core.wlpOutcomeState`. -/
abbrev wlpState (p : Program) (fuel : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  wlpOutcomeState p post (fun _ => False) fuel s

/-- Whole-program fuel-bounded weakest liberal precondition forbidding faults
along every `fuel`-step prefix (complementing `Anneal.Core.wlpProg`, which
leaves fault absence to a companion safety pass). -/
@[expose] def wlpProgStrict (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => wlpState p fuel s₀ post

/-- Deterministic `c = 0` fast-path weakest liberal precondition over
`evalStep p 0`. -/
@[expose] def execWlpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => True)
    (fun _ ih st =>
      match evalStep p 0 st with
      | .step st' => ih st'
      | .done out => onDone out
      | .fault k => onFault k)
    fuel s

/-- Deterministic `c = 0` state-level weakest liberal precondition forbidding
faults. -/
abbrev execWlpState (p : Program) (fuel : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  execWlpOutcomeState p post (fun _ => False) fuel s

/-- Deterministic `c = 0` whole-program weakest liberal precondition matching
`Anneal.Core.wlpProg` (`onFault := fun _ => True`). -/
@[expose] def execWlpProg (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => execWlpOutcomeState p post (fun _ => True) fuel s₀

/-- Deterministic `c = 0` whole-program weakest liberal precondition forbidding
faults (`wlpProgStrict`). -/
@[expose] def execWlpProgStrict (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => execWlpState p fuel s₀ post

/-- Unfold `wlpOutcomeState` at fuel `0`. -/
theorem wlpOutcomeState_zero (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (s : State) :
    wlpOutcomeState p onDone onFault 0 s :=
  trivial

/-- Exact equivalence between `wlpOutcomeState` and deterministic
`execWlpOutcomeState`. -/
theorem wlpOutcomeState_iff_execWlpOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : State},
      wlpOutcomeState p onDone onFault fuel s ↔
      execWlpOutcomeState p onDone onFault fuel s
  | 0, _ => Iff.rfl
  | fuel + 1, s => by
    -- Unfold only the deterministic side here: the `wlpOutcomeState` side is
    -- consumed by application, because its `match` belongs to
    -- `Anneal.Framework.StepWp.wlpStepPred` and is not defeq to a local
    -- `match`.
    refine ⟨?_, ?_⟩
    · intro h
      have h0 := h 0 rfl
      change match evalStep p 0 s with
        | .step st' => execWlpOutcomeState p onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k
      cases hStep : evalStep p 0 s with
      | step st' =>
        rw [hStep] at h0
        exact wlpOutcomeState_iff_execWlpOutcomeState.mp h0
      | done out =>
        rw [hStep] at h0
        exact h0
      | fault k =>
        rw [hStep] at h0
        exact h0
    · intro h c hc
      subst hc
      change match evalStep p 0 s with
        | .step st' => execWlpOutcomeState p onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k at h
      cases hStep : evalStep p 0 s with
      | step st' =>
        rw [hStep] at h
        exact wlpOutcomeState_iff_execWlpOutcomeState.mpr h
      | done out =>
        rw [hStep] at h
        exact h
      | fault k =>
        rw [hStep] at h
        exact h

/-- Lift deterministic `execWlpOutcomeState` into `wlpOutcomeState`. -/
theorem wlpOutcomeState_of_execWlpOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : execWlpOutcomeState p onDone onFault fuel s) :
    wlpOutcomeState p onDone onFault fuel s :=
  wlpOutcomeState_iff_execWlpOutcomeState.mpr h

/-- Exact equivalence between `Anneal.Core.wlpProg` and `execWlpProg`. -/
theorem wlpProg_iff_execWlpProg {p : Program} {fuel : Nat} {q : Query}
    {post : TerminalOut → Prop} :
    wlpProg p fuel q post ↔ execWlpProg p fuel q post := by
  unfold wlpProg execWlpProg
  cases initState p q with
  | error _ => exact Iff.rfl
  | ok _ => exact wlpOutcomeState_iff_execWlpOutcomeState

/-- Lift deterministic `execWlpProg` into `Anneal.Core.wlpProg`. -/
theorem wlpProg_of_execWlpProg {p : Program} {fuel : Nat} {q : Query}
    {post : TerminalOut → Prop} (h : execWlpProg p fuel q post) :
    wlpProg p fuel q post :=
  wlpProg_iff_execWlpProg.mpr h

/-- Exact equivalence between `wlpProgStrict` and `execWlpProgStrict`. -/
theorem wlpProgStrict_iff_execWlpProgStrict {p : Program} {fuel : Nat}
    {q : Query} {post : TerminalOut → Prop} :
    wlpProgStrict p fuel q post ↔ execWlpProgStrict p fuel q post := by
  unfold wlpProgStrict execWlpProgStrict
  cases initState p q with
  | error _ => exact Iff.rfl
  | ok _ => exact wlpOutcomeState_iff_execWlpOutcomeState

/-- Single-step introduction rule for `wlpOutcomeState` along `evalStep p 0`. -/
theorem wlpOutcomeState_step_eq {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStep p 0 s = .step s')
    (h : wlpOutcomeState p onDone onFault fuel s') :
    wlpOutcomeState p onDone onFault (fuel + 1) s := by
  refine wlpOutcomeState_of_execWlpOutcomeState ?_
  change match evalStep p 0 s with
    | .step st' => execWlpOutcomeState p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k
  rw [hStep]
  exact wlpOutcomeState_iff_execWlpOutcomeState.mp h

/-- Terminal `.done` introduction rule for `wlpOutcomeState`. -/
theorem wlpOutcomeState_done_eq {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStep p 0 s = .done out) (h : onDone out) :
    wlpOutcomeState p onDone onFault (fuel + 1) s := by
  refine wlpOutcomeState_of_execWlpOutcomeState ?_
  change match evalStep p 0 s with
    | .step st' => execWlpOutcomeState p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k
  rw [hStep]
  exact h

/-- Rule of consequence (covariant weakening) for `wlpOutcomeState`. -/
theorem wlpOutcomeState_mono {p : Program}
    {onDone₁ onDone₂ : TerminalOut → Prop}
    {onFault₁ onFault₂ : FaultKind → Prop}
    (hDone : ∀ out, onDone₁ out → onDone₂ out)
    (hFault : ∀ k, onFault₁ k → onFault₂ k) :
    ∀ {fuel : Nat} {s : State},
      wlpOutcomeState p onDone₁ onFault₁ fuel s →
      wlpOutcomeState p onDone₂ onFault₂ fuel s
  | 0, _, _ => trivial
  | fuel + 1, s, h => by
    intro c hc
    have hc' := h c hc
    cases hStep : evalStep p c s with
    | step st' =>
      rw [hStep] at hc'
      exact wlpOutcomeState_mono hDone hFault hc'
    | done out =>
      rw [hStep] at hc'
      exact hDone out hc'
    | fault k =>
      rw [hStep] at hc'
      exact hFault k hc'

/-- Fuel anti-monotonicity for `wlpOutcomeState`: checking more steps
(`fuel₁ ≤ fuel₂`) implies checking fewer steps. -/
theorem wlpOutcomeState_fuel_anti {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel₁ fuel₂ : Nat} {s : State},
      fuel₁ ≤ fuel₂ →
      wlpOutcomeState p onDone onFault fuel₂ s →
      wlpOutcomeState p onDone onFault fuel₁ s
  | 0, _, _, _, _ => trivial
  | fuel₁ + 1, 0, _, hLe, _ => False.elim (Nat.not_succ_le_zero fuel₁ hLe)
  | fuel₁ + 1, fuel₂ + 1, s, hLe, h => by
    have hLe' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hLe
    intro c hc
    have hc' := h c hc
    cases hStep : evalStep p c s with
    | step st' =>
      rw [hStep] at hc'
      exact wlpOutcomeState_fuel_anti hLe' hc'
    | done _ =>
      rw [hStep] at hc'
      exact hc'
    | fault _ =>
      rw [hStep] at hc'
      exact hc'

/-- Every terminating `wpOutcomeState` derivation implies `wlpOutcomeState` at
the same fuel. -/
theorem wlpOutcomeState_of_wpOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : State},
      wpOutcomeState p onDone onFault fuel s →
      wlpOutcomeState p onDone onFault fuel s
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    intro c hc
    have hc' := h.2 c hc
    cases hStep : evalStep p c s with
    | step st' =>
      rw [hStep] at hc'
      exact wlpOutcomeState_of_wpOutcomeState hc'
    | done _ =>
      rw [hStep] at hc'
      exact hc'
    | fault _ =>
      rw [hStep] at hc'
      exact hc'

/-! ## Part II: Minimum-Budget Conjunctive WP & Asymmetric Two-Pass Rules -/

/-- Conjunctive composition for `wlpOutcomeState` at `compNatMin n₁ n₂`. -/
theorem wlpOutcomeState_conj {p : Program}
    {d₁ d₂ : TerminalOut → Prop} {f₁ f₂ : FaultKind → Prop} :
    ∀ {n₁ n₂ : Nat} {s : State},
      wlpOutcomeState p d₁ f₁ n₁ s →
      wlpOutcomeState p d₂ f₂ n₂ s →
      wlpOutcomeState p (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
        (compNatMin n₁ n₂) s
  | 0, _, _, _, _ => trivial
  | _ + 1, 0, _, _, _ => trivial
  | n₁ + 1, n₂ + 1, s, h₁, h₂ => by
    rw [compNatMin_succ_succ]
    intro c hc
    have hc₁ := h₁ c hc
    have hc₂ := h₂ c hc
    cases hStep : evalStep p c s with
    | step st' =>
      rw [hStep] at hc₁ hc₂
      exact wlpOutcomeState_conj hc₁ hc₂
    | done out =>
      rw [hStep] at hc₁ hc₂
      exact ⟨hc₁, hc₂⟩
    | fault k =>
      rw [hStep] at hc₁ hc₂
      exact ⟨hc₁, hc₂⟩

/-- Conjunctive composition for `wpOutcomeState`: two independent terminating
derivations at budgets `n₁` and `n₂` combine into their conjoined outcome
predicate at budget `compNatMin n₁ n₂`. -/
theorem wpOutcomeState_conj {p : Program}
    {d₁ d₂ : TerminalOut → Prop} {f₁ f₂ : FaultKind → Prop} :
    ∀ {n₁ n₂ : Nat} {s : State},
      wpOutcomeState p d₁ f₁ n₁ s →
      wpOutcomeState p d₂ f₂ n₂ s →
      wpOutcomeState p (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
        (compNatMin n₁ n₂) s
  | 0, _, _, h₁, _ => False.elim h₁
  | _ + 1, 0, _, _, h₂ => False.elim h₂
  | n₁ + 1, n₂ + 1, s, h₁, h₂ => by
    rw [compNatMin_succ_succ]
    refine ⟨h₁.1, fun c hc => ?_⟩
    have hc₁ := h₁.2 c hc
    have hc₂ := h₂.2 c hc
    cases hStep : evalStep p c s with
    | step st' =>
      rw [hStep] at hc₁ hc₂
      exact wpOutcomeState_conj hc₁ hc₂
    | done out =>
      rw [hStep] at hc₁ hc₂
      exact ⟨hc₁, hc₂⟩
    | fault k =>
      rw [hStep] at hc₁ hc₂
      exact ⟨hc₁, hc₂⟩

/-- Conjunctive composition for `wpProg` at `compNatMin n₁ n₂`. -/
theorem wpProg_conj {p : Program} {n₁ n₂ : Nat} {q : Query}
    {post₁ post₂ : TerminalOut → Prop}
    (h₁ : wpProg p n₁ q post₁) (h₂ : wpProg p n₂ q post₂) :
    wpProg p (compNatMin n₁ n₂) q (fun out => post₁ out ∧ post₂ out) := by
  unfold wpProg at h₁ h₂
  unfold wpProg
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at h₁
    exact False.elim h₁
  | ok s₀ =>
    rw [hInit] at h₁ h₂
    exact wpOutcomeState_mono (fun _ h => h) (fun _ h => h.1)
      (wpOutcomeState_conj h₁ h₂)

/-- Conjunctive composition for `wpUntil` sharing a checkpoint predicate `stop`
at `compNatMin n₁ n₂`. -/
theorem wpUntil_conj_same_stop {p : Program} {stop : State → Prop}
    {d₁ d₂ : TerminalOut → Prop} {f₁ f₂ : FaultKind → Prop} :
    ∀ {n₁ n₂ : Nat} {s : State},
      wpUntil p stop d₁ f₁ n₁ s →
      wpUntil p stop d₂ f₂ n₂ s →
      wpUntil p stop (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
        (compNatMin n₁ n₂) s
  | 0, _, _, h₁, _ => wpUntil_stop (wpUntil_zero_iff.mp h₁)
  | _ + 1, 0, _, _, h₂ => wpUntil_stop (wpUntil_zero_iff.mp h₂)
  | n₁ + 1, n₂ + 1, s, h₁, h₂ => by
    rw [compNatMin_succ_succ]
    cases wpUntil_succ_iff.mp h₁ with
    | inl hStop => exact wpUntil_stop hStop
    | inr hStep₁ =>
      cases wpUntil_succ_iff.mp h₂ with
      | inl hStop => exact wpUntil_stop hStop
      | inr hStep₂ =>
        refine wpUntil_succ_iff.mpr (Or.inr ⟨hStep₁.1, fun c hc => ?_⟩)
        have hc₁ := hStep₁.2 c hc
        have hc₂ := hStep₂.2 c hc
        cases hEval : evalStep p c s with
        | step st' =>
          rw [hEval] at hc₁ hc₂
          exact wpUntil_conj_same_stop hc₁ hc₂
        | done out =>
          rw [hEval] at hc₁ hc₂
          exact ⟨hc₁, hc₂⟩
        | fault k =>
          rw [hEval] at hc₁ hc₂
          exact ⟨hc₁, hc₂⟩

/-- Asymmetric-fuel two-pass state combination: a functional `wlpOutcomeState`
derivation at `fuelWlp` plus a termination/safety `wpOutcomeState` derivation
at `fuelSafe ≤ fuelWlp` yields their conjoined `wpOutcomeState` at
`fuelSafe`. -/
theorem wpOutcomeState_of_wlp_and_safety_le {p : Program}
    {dWlp dSafe : TerminalOut → Prop} {fWlp fSafe : FaultKind → Prop}
    {fuelSafe fuelWlp : Nat} {s : State}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpOutcomeState p dWlp fWlp fuelWlp s)
    (hSafe : wpOutcomeState p dSafe fSafe fuelSafe s) :
    wpOutcomeState p (fun o => dWlp o ∧ dSafe o)
      (fun k => fWlp k ∧ fSafe k) fuelSafe s :=
  wpOutcomeState_mono (fun _ h => ⟨h.2, h.1⟩) (fun _ h => ⟨h.2, h.1⟩)
    (wpOutcomeState_conj_of_wlp_noDiv hSafe
      (wlpOutcomeState_fuel_anti hLe hWlp))

/-- Asymmetric-fuel state rule combining `wlpOutcomeState` at `fuelWlp` with a
`post := fun _ => True` safety/termination proof at `fuelSafe ≤ fuelWlp`. -/
theorem wpState_of_wlp_and_safety_le {p : Program}
    {fuelSafe fuelWlp : Nat} {s : State} {post : TerminalOut → Prop}
    {onFault : FaultKind → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpOutcomeState p post onFault fuelWlp s)
    (hSafe : wpState p fuelSafe s (fun _ => True)) :
    wpState p fuelSafe s post :=
  wpOutcomeState_mono (fun _ h => h.1) (fun _ h => h.2)
    (wpOutcomeState_of_wlp_and_safety_le hLe hWlp hSafe)

/-- Asymmetric-fuel whole-program two-pass rule combining `Anneal.Core.wlpProg`
at `fuelWlp` with `wpProg ... (fun _ => True)` at `fuelSafe ≤ fuelWlp`. -/
theorem wpProg_of_wlp_and_safety_le {p : Program}
    {fuelSafe fuelWlp : Nat} {q : Query} {post : TerminalOut → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpProg p fuelWlp q post)
    (hSafe : wpProg p fuelSafe q (fun _ => True)) :
    wpProg p fuelSafe q post := by
  unfold wlpProg at hWlp
  unfold wpProg at hSafe
  unfold wpProg
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at hSafe
    exact False.elim hSafe
  | ok s₀ =>
    rw [hInit] at hWlp hSafe
    exact wpState_of_wlp_and_safety_le hLe hWlp hSafe

/-- Direct trusted adequacy from an asymmetric-fuel two-pass (`wlpProg` at
`fuelWlp` + safety `wpProg` at `fuelSafe ≤ fuelWlp`) proof. -/
theorem wellFormed_and_spec_of_wlp_and_safety_le {p : Program}
    {fuelSafe fuelWlp : Nat} {q : Query} {post : TerminalOut → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpProg p fuelWlp q post)
    (hSafe : wpProg p fuelSafe q (fun _ => True)) :
    SatisfiesPost p q post ∧ ¬ Diverges p q ∧
      ∃ out, Behavior p q out ∧ post out :=
  wellFormed_and_spec_of_wp_base p q fuelSafe post
    (wpProg_of_wlp_and_safety_le hLe hWlp hSafe)

/-! ## Part III: Constructive Productive-Invariant Divergence Certificates -/

/-- Constructive productive step witness for `p`: every state satisfying `inv`
steps deterministically under `c = 0` to `next s`, which again satisfies
`inv`. -/
structure ProductiveStepWitness (p : Program) (next : State → State)
    (inv : State → Prop) : Prop where
  stepOk : ∀ s : State, inv s → evalStep p 0 s = .step (next s)
  preserves : ∀ s : State, inv s → inv (next s)

/-- Iterates `next` `n` times starting from `s₀` via `@Nat.rec`. -/
@[expose] def iterState (next : State → State) (s₀ : State) (n : Nat) : State :=
  @Nat.rec (fun _ => State) s₀ (fun _ st => next st) n

private theorem iterState_inv {p : Program} {next : State → State}
    {inv : State → Prop} (hw : ProductiveStepWitness p next inv)
    {s₀ : State} (h₀ : inv s₀) :
    ∀ n : Nat, inv (iterState next s₀ n)
  | 0 => h₀
  | n + 1 => hw.preserves (iterState next s₀ n) (iterState_inv hw h₀ n)

/-- Constructive choice-coupled divergence certificate: an `initState p q = .ok
s₀` entry state satisfying a `ProductiveStepWitness` diverges along the constant
`0` choice stream (`DivergesAtChoices p q (fun _ => 0)`). -/
theorem divergesAtChoices_of_productiveWitness {p : Program} {q : Query}
    {next : State → State} {inv : State → Prop} {s₀ : State}
    (hInit : initState p q = .ok s₀)
    (hInv₀ : inv s₀)
    (hw : ProductiveStepWitness p next inv) :
    DivergesAtChoices p q (fun _ => 0) :=
  ⟨s₀, hInit, iterState next s₀, rfl, fun n =>
    ⟨rfl, hw.stepOk (iterState next s₀ n) (iterState_inv hw hInv₀ n)⟩⟩

/-- Constructive `Trusted.MirSemantics.Diverges` certificate from a
`ProductiveStepWitness` (`0` `Classical.choice`). -/
theorem diverges_of_productiveWitness {p : Program} {q : Query}
    {next : State → State} {inv : State → Prop} {s₀ : State}
    (hInit : initState p q = .ok s₀)
    (hInv₀ : inv s₀)
    (hw : ProductiveStepWitness p next inv) :
    Diverges p q :=
  ⟨s₀, hInit, iterState next s₀, rfl, fun n =>
    ⟨0, rfl, hw.stepOk (iterState next s₀ n) (iterState_inv hw hInv₀ n)⟩⟩

/-- Any state satisfying a `ProductiveStepWitness` invariant satisfies
`wlpOutcomeState` for every finite `fuel` and every `onDone` / `onFault`
predicate (confirming why `wlpOutcomeState` alone is partial correctness and
must be paired with `wpOutcomeState` for total adequacy). -/
theorem wlpOutcomeState_of_productiveWitness {p : Program}
    {next : State → State} {inv : State → Prop}
    (hw : ProductiveStepWitness p next inv)
    (onDone : TerminalOut → Prop) (onFault : FaultKind → Prop) :
    ∀ (fuel : Nat) {s : State}, inv s →
      wlpOutcomeState p onDone onFault fuel s
  | 0, _, _ => trivial
  | fuel + 1, s, hs =>
    wlpOutcomeState_step_eq (hw.stepOk s hs)
      (wlpOutcomeState_of_productiveWitness hw onDone onFault fuel
        (hw.preserves s hs))

/-! ## Part IV: Logarithmic Binary-Doubling Fuel (`wpPow2`, `execPow2`) -/

/-- Exact power-of-two fuel count `2^k` computed via `@Nat.rec` doubling. -/
@[expose] def pow2Fuel (k : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => ih + ih) k

/-- `pow2Fuel (k + 1) = pow2Fuel k + pow2Fuel k`. -/
theorem pow2Fuel_succ (k : Nat) :
    pow2Fuel (k + 1) = pow2Fuel k + pow2Fuel k :=
  rfl

/-- Exact arithmetic bridge `pow2Fuel k = Anneal.Core.pow2 k` (`[]` zero
axioms). -/
theorem pow2Fuel_eq_pow2 : ∀ k : Nat, pow2Fuel k = pow2 k
  | 0 => rfl
  | k + 1 => by
    rw [pow2Fuel_succ, pow2_succ, Nat.two_mul, pow2Fuel_eq_pow2 k]

/-- Continuation-passing `ValidChoice`-quantified WP executing up to `2^k`
steps in recursion depth `k`, handing any surviving state after `2^k` steps to
`cont`. -/
@[expose] def wpPow2Cont (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (k : Nat) (cont : State → Prop)
    (s : State) : Prop :=
  @Nat.rec (fun _ => (State → Prop) → State → Prop)
    (fun c st =>
      (∃ c₀ : Choice, ValidChoice p st c₀) ∧
      ∀ ch : Choice, ValidChoice p st ch →
        match evalStep p ch st with
        | .step st' => c st'
        | .done out => onDone out
        | .fault fk => onFault fk)
    (fun _ ih c st => ih (fun st' => ih c st') st)
    k cont s

/-- Continuation-passing deterministic `c = 0` fast-path WP executing up to
`2^k` steps in recursion depth `k`. -/
@[expose] def execPow2Cont (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (k : Nat) (cont : State → Prop)
    (s : State) : Prop :=
  @Nat.rec (fun _ => (State → Prop) → State → Prop)
    (fun c st =>
      match evalStep p 0 st with
      | .step st' => c st'
      | .done out => onDone out
      | .fault fk => onFault fk)
    (fun _ ih c st => ih (fun st' => ih c st') st)
    k cont s

/-- `ValidChoice`-quantified binary-doubling WP requiring termination within
`2^k` steps (`cont := fun _ => False`). -/
abbrev wpPow2 (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (k : Nat) (s : State) : Prop :=
  wpPow2Cont p onDone onFault k (fun _ => False) s

/-- Normal-termination state WP with binary-doubling fuel `2^k`. -/
abbrev wpStatePow2 (p : Program) (k : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  wpPow2 p post (fun _ => False) k s

/-- Whole-program normal-termination WP with binary-doubling fuel `2^k`. -/
@[expose] def wpProgPow2 (p : Program) (k : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => wpStatePow2 p k s₀ post

/-- Deterministic `c = 0` binary-doubling WP requiring termination within `2^k`
steps. -/
abbrev execPow2 (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (k : Nat) (s : State) : Prop :=
  execPow2Cont p onDone onFault k (fun _ => False) s

/-- Deterministic `c = 0` normal-termination state WP with budget `2^k`. -/
abbrev execStatePow2 (p : Program) (k : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  execPow2 p post (fun _ => False) k s

/-- Deterministic `c = 0` whole-program WP with binary-doubling budget `2^k`. -/
@[expose] def execProgPow2 (p : Program) (k : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => execStatePow2 p k s₀ post

/-- Exact doubling identity for `wpPow2Cont`. -/
theorem wpPow2Cont_succ (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (k : Nat) (cont : State → Prop) (s : State) :
    wpPow2Cont p onDone onFault (k + 1) cont s ↔
      wpPow2Cont p onDone onFault k (wpPow2Cont p onDone onFault k cont) s :=
  Iff.rfl

/-- Covariant monotonicity of `wpPow2Cont` in `onDone`, `onFault`, and
`cont`. -/
theorem wpPow2Cont_mono {p : Program}
    {d₁ d₂ : TerminalOut → Prop} {f₁ f₂ : FaultKind → Prop}
    (hD : ∀ out, d₁ out → d₂ out) (hF : ∀ fk, f₁ fk → f₂ fk) :
    ∀ {k : Nat} {c₁ c₂ : State → Prop},
      (∀ st, c₁ st → c₂ st) →
      ∀ {s : State},
        wpPow2Cont p d₁ f₁ k c₁ s →
        wpPow2Cont p d₂ f₂ k c₂ s
  | 0, _, _, hC, s, h => by
    refine ⟨h.1, fun ch hch => ?_⟩
    have hStep := h.2 ch hch
    cases hEv : evalStep p ch s with
    | step st' =>
      rw [hEv] at hStep
      exact hC st' hStep
    | done out =>
      rw [hEv] at hStep
      exact hD out hStep
    | fault fk =>
      rw [hEv] at hStep
      exact hF fk hStep
  | _ + 1, _, _, hC, _, h =>
    wpPow2Cont_mono hD hF
      (fun _ hInner => wpPow2Cont_mono hD hF hC hInner) h

/-- Exact equivalence between `wpPow2Cont` and deterministic `execPow2Cont`. -/
theorem wpPow2Cont_iff_execPow2Cont {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {k : Nat} {c₁ c₂ : State → Prop},
      (∀ st, c₁ st ↔ c₂ st) →
      ∀ {s : State},
        wpPow2Cont p onDone onFault k c₁ s ↔
        execPow2Cont p onDone onFault k c₂ s
  | 0, c₁, c₂, hC, s => by
    change ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
        ∀ ch : Choice, ValidChoice p s ch →
          match evalStep p ch s with
          | .step st' => c₁ st'
          | .done out => onDone out
          | .fault fk => onFault fk) ↔
      (match evalStep p 0 s with
        | .step st' => c₂ st'
        | .done out => onDone out
        | .fault fk => onFault fk)
    refine ⟨?_, ?_⟩
    · intro h
      have h0 := h.2 0 rfl
      cases hEv : evalStep p 0 s with
      | step st' =>
        rw [hEv] at h0
        exact (hC st').mp h0
      | done out =>
        rw [hEv] at h0
        exact h0
      | fault fk =>
        rw [hEv] at h0
        exact h0
    · intro h
      refine ⟨⟨0, rfl⟩, fun ch hch => ?_⟩
      subst hch
      cases hEv : evalStep p 0 s with
      | step st' =>
        rw [hEv] at h
        exact (hC st').mpr h
      | done out =>
        rw [hEv] at h
        exact h
      | fault fk =>
        rw [hEv] at h
        exact h
  | _ + 1, _, _, hC, _ =>
    wpPow2Cont_iff_execPow2Cont
      (fun _ => wpPow2Cont_iff_execPow2Cont hC)

/-- Lift deterministic `execPow2` into `wpPow2`. -/
theorem wpPow2_of_execPow2 {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {k : Nat} {s : State} (h : execPow2 p onDone onFault k s) :
    wpPow2 p onDone onFault k s :=
  (wpPow2Cont_iff_execPow2Cont (fun _ => Iff.rfl)).mpr h

/-- Lift deterministic `execProgPow2` into `wpProgPow2`. -/
theorem wpProgPow2_of_execProgPow2 {p : Program} {k : Nat} {q : Query}
    {post : TerminalOut → Prop} (h : execProgPow2 p k q post) :
    wpProgPow2 p k q post := by
  unfold execProgPow2 at h
  unfold wpProgPow2
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    exact wpPow2_of_execPow2 h

/-- Internal linear continuation-passing step predicate used to relate
`wpPow2Cont` to `wpOutcomeState`. -/
private def wpStepsCont (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (n : Nat) (cont : State → Prop)
    (s : State) : Prop :=
  @Nat.rec (fun _ => (State → Prop) → State → Prop)
    (fun c st => c st)
    (fun _ ih c st =>
      (∃ c₀ : Choice, ValidChoice p st c₀) ∧
      ∀ ch : Choice, ValidChoice p st ch →
        match evalStep p ch st with
        | .step st' => ih c st'
        | .done out => onDone out
        | .fault fk => onFault fk)
    n cont s

private theorem wpStepsCont_add {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {m n : Nat} {cont : State → Prop} {s : State},
      wpStepsCont p onDone onFault (m + n) cont s ↔
      wpStepsCont p onDone onFault m
        (wpStepsCont p onDone onFault n cont) s
  | 0, _, _, _ => by
    rw [Nat.zero_add]
    exact Iff.rfl
  | m + 1, n, cont, s => by
    rw [Nat.succ_add]
    refine ⟨?_, ?_⟩
    · intro h
      refine ⟨h.1, fun ch hch => ?_⟩
      have hStep := h.2 ch hch
      cases hEv : evalStep p ch s with
      | step st' =>
        rw [hEv] at hStep
        exact wpStepsCont_add.mp hStep
      | done out =>
        rw [hEv] at hStep
        exact hStep
      | fault fk =>
        rw [hEv] at hStep
        exact hStep
    · intro h
      refine ⟨h.1, fun ch hch => ?_⟩
      have hStep := h.2 ch hch
      cases hEv : evalStep p ch s with
      | step st' =>
        rw [hEv] at hStep
        exact wpStepsCont_add.mpr hStep
      | done out =>
        rw [hEv] at hStep
        exact hStep
      | fault fk =>
        rw [hEv] at hStep
        exact hStep

private theorem wpStepsCont_congr {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {n : Nat} {c₁ c₂ : State → Prop},
      (∀ st, c₁ st ↔ c₂ st) →
      ∀ {s : State},
        wpStepsCont p onDone onFault n c₁ s ↔
        wpStepsCont p onDone onFault n c₂ s
  | 0, _, _, hC, s => hC s
  | _ + 1, _, _, hC, s => by
    refine ⟨?_, ?_⟩
    · intro h
      refine ⟨h.1, fun ch hch => ?_⟩
      have hStep := h.2 ch hch
      cases hEv : evalStep p ch s with
      | step st' =>
        rw [hEv] at hStep
        exact (wpStepsCont_congr hC).mp hStep
      | done out =>
        rw [hEv] at hStep
        exact hStep
      | fault fk =>
        rw [hEv] at hStep
        exact hStep
    · intro h
      refine ⟨h.1, fun ch hch => ?_⟩
      have hStep := h.2 ch hch
      cases hEv : evalStep p ch s with
      | step st' =>
        rw [hEv] at hStep
        exact (wpStepsCont_congr hC).mpr hStep
      | done out =>
        rw [hEv] at hStep
        exact hStep
      | fault fk =>
        rw [hEv] at hStep
        exact hStep

private theorem wpPow2Cont_iff_wpStepsCont {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {k : Nat} {cont : State → Prop} {s : State},
      wpPow2Cont p onDone onFault k cont s ↔
      wpStepsCont p onDone onFault (pow2Fuel k) cont s
  | 0, _, _ => Iff.rfl
  | k + 1, _, _ => by
    rw [pow2Fuel_succ]
    refine Iff.trans (wpPow2Cont_iff_wpStepsCont (k := k)) ?_
    refine Iff.trans
      (wpStepsCont_congr (fun _ => wpPow2Cont_iff_wpStepsCont (k := k))) ?_
    exact wpStepsCont_add.symm

private theorem wpStepsCont_false_iff_wpOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {n : Nat} {s : State},
      wpStepsCont p onDone onFault n (fun _ => False) s ↔
      wpOutcomeState p onDone onFault n s
  | 0, _ => Iff.rfl
  | _ + 1, s => by
    refine ⟨?_, ?_⟩
    · intro h
      refine ⟨h.1, fun ch hch => ?_⟩
      have hStep := h.2 ch hch
      cases hEv : evalStep p ch s with
      | step st' =>
        rw [hEv] at hStep
        exact wpStepsCont_false_iff_wpOutcomeState.mp hStep
      | done out =>
        rw [hEv] at hStep
        exact hStep
      | fault fk =>
        rw [hEv] at hStep
        exact hStep
    · intro h
      refine ⟨h.1, fun ch hch => ?_⟩
      have hStep := h.2 ch hch
      cases hEv : evalStep p ch s with
      | step st' =>
        rw [hEv] at hStep
        exact wpStepsCont_false_iff_wpOutcomeState.mpr hStep
      | done out =>
        rw [hEv] at hStep
        exact hStep
      | fault fk =>
        rw [hEv] at hStep
        exact hStep

/-- Exact equivalence between depth-`k` binary-doubling `wpPow2` and linear
`wpOutcomeState` at fuel `pow2Fuel k` (`2^k`). -/
theorem wpPow2_iff_wpOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {k : Nat} {s : State} :
    wpPow2 p onDone onFault k s ↔
    wpOutcomeState p onDone onFault (pow2Fuel k) s :=
  Iff.trans wpPow2Cont_iff_wpStepsCont wpStepsCont_false_iff_wpOutcomeState

/-- Exact equivalence between whole-program `wpProgPow2 p k` and
`wpProg p (pow2Fuel k)`. -/
theorem wpProgPow2_iff_wpProg {p : Program} {k : Nat} {q : Query}
    {post : TerminalOut → Prop} :
    wpProgPow2 p k q post ↔ wpProg p (pow2Fuel k) q post := by
  unfold wpProgPow2 wpProg
  cases initState p q with
  | error _ => exact Iff.rfl
  | ok _ => exact wpPow2_iff_wpOutcomeState

/-- Soundness, termination, and productivity of `wpProgPow2` directly in terms
of `Trusted.MirSemantics.{SatisfiesPost, Diverges, Behavior}`. -/
theorem wellFormed_and_spec_of_wpProgPow2 {p : Program} {k : Nat} {q : Query}
    {post : TerminalOut → Prop} (h : wpProgPow2 p k q post) :
    SatisfiesPost p q post ∧ ¬ Diverges p q ∧
      ∃ out, Behavior p q out ∧ post out :=
  wellFormed_and_spec_of_wp_base p q (pow2Fuel k) post
    (wpProgPow2_iff_wpProg.mp h)

/-- Establish `PositiveCanaryClaim` directly from a depth-`k` deterministic
binary-doubling `execProgPow2` derivation (reducible by `rfl` on concrete runs
within `pow2Fuel k` steps). -/
theorem positiveCanary_of_execProgPow2 {p : Program} {k : Nat} {q : Query}
    {expectedRet : Val}
    (h : execProgPow2 p k q (fun out => out = .returned ⟨expectedRet, ⟨[]⟩⟩)) :
    PositiveCanaryClaim p q expectedRet :=
  positiveCanary_of_wp (wpProgPow2_iff_wpProg.mp (wpProgPow2_of_execProgPow2 h))

/-- Lift a 1-step `wpPow2Cont` invariant (`k = 0`) to depth `k` (`2^k` steps) in
`k` recursive-doubling steps without unary induction over `pow2Fuel k`. -/
theorem wpPow2Cont_inv {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {inv : State → Prop}
    (hStep : ∀ s : State, inv s → wpPow2Cont p onDone onFault 0 inv s) :
    ∀ (k : Nat) {s : State}, inv s → wpPow2Cont p onDone onFault k inv s
  | 0, _, hs => hStep _ hs
  | k + 1, _, hs =>
    wpPow2Cont_mono (fun _ h => h) (fun _ h => h)
      (fun _ hMid => wpPow2Cont_inv hStep k hMid)
      (wpPow2Cont_inv hStep k hs)

private theorem wlpOutcomeState_of_wpStepsCont {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {n : Nat} {cont : State → Prop} {s : State},
      wpStepsCont p onDone onFault n cont s →
      wlpOutcomeState p onDone onFault n s
  | 0, _, _, _ => trivial
  | _ + 1, _, s, h => by
    intro ch hch
    have hStep := h.2 ch hch
    cases hEv : evalStep p ch s with
    | step st' =>
      rw [hEv] at hStep
      exact wlpOutcomeState_of_wpStepsCont hStep
    | done out =>
      rw [hEv] at hStep
      exact hStep
    | fault fk =>
      rw [hEv] at hStep
      exact hStep

/-- Any depth-`k` `wpPow2Cont` derivation (for any continuation `cont`) implies
bounded partial correctness `wlpOutcomeState` across all `pow2Fuel k` (`2^k`)
steps. -/
theorem wlpOutcomeState_of_wpPow2Cont {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {k : Nat} {cont : State → Prop} {s : State}
    (h : wpPow2Cont p onDone onFault k cont s) :
    wlpOutcomeState p onDone onFault (pow2Fuel k) s :=
  wlpOutcomeState_of_wpStepsCont (wpPow2Cont_iff_wpStepsCont.mp h)

end Anneal.ConjunctiveWp

end
