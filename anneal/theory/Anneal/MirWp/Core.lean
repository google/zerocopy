-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Part I: Unified Fuel-Bounded Weakest Precondition & Adequacy -/

/-- Unified structural fuel-bounded weakest precondition over `evalStep`.
Using `@Nat.rec` into `Prop` avoids both codegen exemptions and `_unsafe_rec`
while preserving the `ValidChoice`-quantified shape expected by downstream
correspondence proofs. -/
@[expose] def wpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st =>
      (∃ c₀ : Choice, ValidChoice p st c₀) ∧
      ∀ c : Choice, ValidChoice p st c →
        match evalStep p c st with
        | .step st' => ih st'
        | .done out => onDone out
        | .fault k => onFault k)
    fuel s

/-- State-level weakest precondition requiring normal termination satisfying
`post` and forbidding all faults (`onFault := fun _ => False`). -/
abbrev wpState (p : Program) (fuel : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  wpOutcomeState p post (fun _ => False) fuel s

/-- State-level fault verifier requiring execution from `s` to terminate in
`.fault expected`. -/
abbrev wpFaultState (p : Program) (fuel : Nat) (s : State)
    (expected : FaultKind) : Prop :=
  wpOutcomeState p (fun _ => False) (fun k => k = expected) fuel s

/-- Whole-program fuel-bounded weakest precondition starting from
`initState p q`. -/
@[expose] def wpProg (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => wpState p fuel s₀ post

/-- Whole-program fuel-bounded fault verifier starting from `initState p q`. -/
@[expose] def wpFaultProg (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initState p q with
  | .error k => k = expected
  | .ok s₀ => wpFaultState p fuel s₀ expected

/-- Deterministic `c = 0` fast-path structural fuel-bounded execution
predicate over `evalStep p 0`. Concrete runs reduce directly by `rfl` and lift
into `wpOutcomeState` via `wpOutcomeState_of_execOutcomeState`. -/
@[expose] def execOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st =>
      match evalStep p 0 st with
      | .step st' => ih st'
      | .done out => onDone out
      | .fault k => onFault k)
    fuel s

/-- State-level deterministic `c = 0` normal-termination predicate. -/
abbrev execState (p : Program) (fuel : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  execOutcomeState p post (fun _ => False) fuel s

/-- State-level deterministic `c = 0` fault-termination predicate. -/
abbrev execFaultState (p : Program) (fuel : Nat) (s : State)
    (expected : FaultKind) : Prop :=
  execOutcomeState p (fun _ => False) (fun k => k = expected) fuel s

/-- Whole-program deterministic `c = 0` normal-termination predicate starting
from `initState p q`. -/
@[expose] def execProg (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => execState p fuel s₀ post

/-- Whole-program deterministic `c = 0` fault-termination predicate starting
from `initState p q`. -/
@[expose] def execFaultProg (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initState p q with
  | .error k => k = expected
  | .ok s₀ => execFaultState p fuel s₀ expected

/-- Exact equivalence between `ValidChoice`-quantified `wpOutcomeState` and the
deterministic `c = 0` fast path `execOutcomeState`. -/
theorem wpOutcomeState_iff_execOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : State},
      wpOutcomeState p onDone onFault fuel s ↔
      execOutcomeState p onDone onFault fuel s
  | 0, _ => Iff.rfl
  | fuel + 1, s => by
    change ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
        ∀ c : Choice, ValidChoice p s c →
          match evalStep p c s with
          | .step st' => wpOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k) ↔
      (match evalStep p 0 s with
        | .step st' => execOutcomeState p onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k)
    constructor
    · intro h
      have h0 := h.2 0 rfl
      cases hStep : evalStep p 0 s with
      | step st' =>
        rw [hStep] at h0
        exact wpOutcomeState_iff_execOutcomeState.mp h0
      | done out =>
        rw [hStep] at h0
        exact h0
      | fault k =>
        rw [hStep] at h0
        exact h0
    · intro h
      refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
      subst hc
      cases hStep : evalStep p 0 s with
      | step st' =>
        rw [hStep] at h
        exact wpOutcomeState_iff_execOutcomeState.mpr h
      | done out =>
        rw [hStep] at h
        exact h
      | fault k =>
        rw [hStep] at h
        exact h

/-- Lift a deterministic `execOutcomeState` derivation into `wpOutcomeState`. -/
theorem wpOutcomeState_of_execOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : execOutcomeState p onDone onFault fuel s) :
    wpOutcomeState p onDone onFault fuel s :=
  wpOutcomeState_iff_execOutcomeState.mpr h

/-- Project `wpOutcomeState` onto the deterministic `c = 0` fast path. -/
theorem execOutcomeState_of_wpOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : wpOutcomeState p onDone onFault fuel s) :
    execOutcomeState p onDone onFault fuel s :=
  wpOutcomeState_iff_execOutcomeState.mp h

/-- Exact equivalence between `wpProg` and deterministic `execProg`. -/
theorem wpProg_iff_execProg {p : Program} {fuel : Nat} {q : Query}
    {post : TerminalOut → Prop} :
    wpProg p fuel q post ↔ execProg p fuel q post := by
  unfold wpProg execProg
  cases initState p q with
  | error _ => exact Iff.rfl
  | ok _ => exact wpOutcomeState_iff_execOutcomeState

/-- Lift a deterministic `execProg` proof into `wpProg`. -/
theorem wpProg_of_execProg {p : Program} {fuel : Nat} {q : Query}
    {post : TerminalOut → Prop} (h : execProg p fuel q post) :
    wpProg p fuel q post :=
  wpProg_iff_execProg.mpr h

/-- Exact equivalence between `wpFaultProg` and deterministic `execFaultProg`.
-/
theorem wpFaultProg_iff_execFaultProg {p : Program} {fuel : Nat} {q : Query}
    {expected : FaultKind} :
    wpFaultProg p fuel q expected ↔ execFaultProg p fuel q expected := by
  unfold wpFaultProg execFaultProg
  cases initState p q with
  | error _ => exact Iff.rfl
  | ok _ => exact wpOutcomeState_iff_execOutcomeState

/-- Lift a deterministic `execFaultProg` proof into `wpFaultProg`. -/
theorem wpFaultProg_of_execFaultProg {p : Program} {fuel : Nat} {q : Query}
    {expected : FaultKind} (h : execFaultProg p fuel q expected) :
    wpFaultProg p fuel q expected :=
  wpFaultProg_iff_execFaultProg.mpr h

/-- Rule of consequence (covariant outcome weakening) for `wpOutcomeState`. -/
theorem wpOutcomeState_mono {p : Program}
    {onDone₁ onDone₂ : TerminalOut → Prop}
    {onFault₁ onFault₂ : FaultKind → Prop}
    (hDone : ∀ out, onDone₁ out → onDone₂ out)
    (hFault : ∀ k, onFault₁ k → onFault₂ k) :
    ∀ {fuel : Nat} {s : State},
      wpOutcomeState p onDone₁ onFault₁ fuel s →
      wpOutcomeState p onDone₂ onFault₂ fuel s
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    change ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step st' => wpOutcomeState p onDone₁ onFault₁ fuel st'
        | .done out => onDone₁ out
        | .fault k => onFault₁ k) at h
    change ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step st' => wpOutcomeState p onDone₂ onFault₂ fuel st'
        | .done out => onDone₂ out
        | .fault k => onFault₂ k)
    refine ⟨h.1, fun c hc => ?_⟩
    have hc' := h.2 c hc
    cases hStep : evalStep p c s with
    | step st' =>
      rw [hStep] at hc'
      exact wpOutcomeState_mono hDone hFault hc'
    | done out =>
      rw [hStep] at hc'
      exact hDone out hc'
    | fault k =>
      rw [hStep] at hc'
      exact hFault k hc'

/-- Fuel weakening: terminating within `fuel₁` steps implies terminating within
any larger budget `fuel₂ ≥ fuel₁`. -/
theorem wpOutcomeState_fuel_mono {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel₁ fuel₂ : Nat} {s : State},
      fuel₁ ≤ fuel₂ →
      wpOutcomeState p onDone onFault fuel₁ s →
      wpOutcomeState p onDone onFault fuel₂ s
  | 0, _, _, _, h => False.elim h
  | fuel₁ + 1, 0, _, hLe, _ => False.elim (Nat.not_succ_le_zero fuel₁ hLe)
  | fuel₁ + 1, fuel₂ + 1, s, hLe, h => by
    have hLe' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hLe
    change ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step st' => wpOutcomeState p onDone onFault fuel₁ st'
        | .done out => onDone out
        | .fault k => onFault k) at h
    change ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step st' => wpOutcomeState p onDone onFault fuel₂ st'
        | .done out => onDone out
        | .fault k => onFault k)
    refine ⟨h.1, fun c hc => ?_⟩
    have hc' := h.2 c hc
    cases hStep : evalStep p c s with
    | step st' =>
      rw [hStep] at hc'
      exact wpOutcomeState_fuel_mono hLe' hc'
    | done _ =>
      rw [hStep] at hc'
      exact hc'
    | fault _ =>
      rw [hStep] at hc'
      exact hc'

/-- Whole-program rule of consequence for `wpProg`. -/
theorem wpProg_mono {p : Program} {fuel : Nat} {q : Query}
    {post₁ post₂ : TerminalOut → Prop}
    (hImp : ∀ out, post₁ out → post₂ out)
    (hWp : wpProg p fuel q post₁) :
    wpProg p fuel q post₂ := by
  unfold wpProg at hWp
  unfold wpProg
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at hWp
    exact False.elim hWp
  | ok s₀ =>
    rw [hInit] at hWp
    exact wpOutcomeState_mono hImp (fun _ h => h) hWp

/-- Prepend a single step `Step p s₁ (.step s₂)` to a reachability chain
`Reaches p s₂ s₃`. -/
theorem Reaches.head {p : Program} {s₁ s₂ s₃ : State}
    (h_first : Step p s₁ (.step s₂))
    (h_rest : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction h_rest with
  | refl => exact Reaches.tail (Reaches.refl s₁) h_first
  | tail _ h_last ih => exact Reaches.tail ih h_last

/-- Any state `s₂` reachable from `s₁` preserves `wpOutcomeState` at some
remaining fuel `fuel'`. -/
theorem wpOutcomeState_of_reaches
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s₁ s₂ : State} {fuel : Nat}
    (h_wp : wpOutcomeState p onDone onFault fuel s₁)
    (h_reach : Reaches p s₁ s₂) :
    ∃ fuel', wpOutcomeState p onDone onFault fuel' s₂ := by
  induction h_reach with
  | refl => exact ⟨fuel, h_wp⟩
  | tail _ h_step ih =>
    let ⟨fuel₁, h_wp₁⟩ := ih
    cases fuel₁ with
    | zero => exact False.elim h_wp₁
    | succ fuel₂ =>
      let ⟨c, hc, h_eval⟩ := h_step
      have h_branch := h_wp₁.2 c hc
      rw [h_eval] at h_branch
      exact ⟨fuel₂, h_branch⟩

/-- Every state satisfying `wpOutcomeState` reaches a terminal `.done` or
`.fault` step within `fuel` steps along its witnessed choice path. -/
theorem exists_terminal_of_wpOutcomeState
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h_wp : wpOutcomeState p onDone onFault fuel s) :
    ∃ s_end res, Reaches p s s_end ∧ Step p s_end res ∧
      match res with
      | .step _ => False
      | .done out => onDone out
      | .fault k => onFault k := by
  induction fuel generalizing s with
  | zero => exact False.elim h_wp
  | succ f ih =>
    let ⟨⟨c₀, hc₀⟩, h_all⟩ := h_wp
    have h_step := h_all c₀ hc₀
    cases h_eval : evalStep p c₀ s with
    | step s' =>
      rw [h_eval] at h_step
      let ⟨s_end, res, h_reach, h_term, h_res⟩ := ih h_step
      exact ⟨s_end, res, Reaches.head ⟨c₀, hc₀, h_eval⟩ h_reach, h_term, h_res⟩
    | done out =>
      rw [h_eval] at h_step
      exact ⟨s, .done out, Reaches.refl s, ⟨c₀, hc₀, h_eval⟩, h_step⟩
    | fault k =>
      rw [h_eval] at h_step
      exact ⟨s, .fault k, Reaches.refl s, ⟨c₀, hc₀, h_eval⟩, h_step⟩

/-- No state satisfying `wpOutcomeState` admits an infinite non-terminating
`Step` trace. -/
theorem not_infinite_trace_of_wpOutcomeState
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} (trace : Nat → State),
      wpOutcomeState p onDone onFault fuel (trace 0) →
      (∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))) →
      False
  | 0, _, h_wp, _ => h_wp
  | fuel + 1, trace, h_wp, h_steps => by
    let ⟨c, hc, h_eval⟩ := h_steps 0
    have h_branch := h_wp.2 c hc
    rw [h_eval] at h_branch
    exact not_infinite_trace_of_wpOutcomeState (fun n => trace (n + 1))
      h_branch (fun n => h_steps (n + 1))

/-- Any `(p, q)` satisfying `wpProg` terminates and therefore cannot diverge. -/
theorem not_diverges_of_wpProg {p : Program} {fuel : Nat} {q : Query}
    {post : TerminalOut → Prop} (h_wp : wpProg p fuel q post) :
    ¬ Diverges p q := by
  intro h_div
  let ⟨s₀, h_init, trace, h_tr0, h_steps⟩ := h_div
  unfold wpProg at h_wp
  rw [h_init, ← h_tr0] at h_wp
  exact not_infinite_trace_of_wpOutcomeState trace h_wp h_steps

/-- Any `(p, q)` satisfying `wpFaultProg` faults in finitely many steps and
therefore cannot diverge. -/
theorem not_diverges_of_wpFaultProg {p : Program} {fuel : Nat} {q : Query}
    {expected : FaultKind} (h_wp : wpFaultProg p fuel q expected) :
    ¬ Diverges p q := by
  intro h_div
  let ⟨s₀, h_init, trace, h_tr0, h_steps⟩ := h_div
  unfold wpFaultProg at h_wp
  rw [h_init, ← h_tr0] at h_wp
  exact not_infinite_trace_of_wpOutcomeState trace h_wp h_steps

/-- Soundness, all-path termination, and productivity of `wpProg`: proving
`wpProg p fuel q post` establishes `SatisfiesPost p q post`, `¬ Diverges p q`,
and the existence of a terminating execution `Behavior p q out ∧ post out`. -/
theorem wellFormed_and_spec_of_wp_base : WpSoundnessClaim wpProg := by
  intro p q fuel post h_wp_orig
  have h_ndiv : ¬ Diverges p q := not_diverges_of_wpProg h_wp_orig
  have h_wp := h_wp_orig
  unfold wpProg at h_wp
  cases h_init : initState p q with
  | error _ =>
    rw [h_init] at h_wp
    exact False.elim h_wp
  | ok s₀ =>
    rw [h_init] at h_wp
    refine ⟨⟨⟨⟨s₀, h_init, ?_⟩, ?_⟩, ?_⟩, h_ndiv, ?_⟩
    · intro s h_reach
      let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_reach
      cases fuel' with
      | zero => exact False.elim h_wp'
      | succ _ => exact h_wp'.1
    · intro k h_fault
      unfold ReachesResult at h_fault
      rw [h_init] at h_fault
      let ⟨s, h_reach, c, hc, h_eval⟩ := h_fault
      let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_reach
      cases fuel' with
      | zero => exact False.elim h_wp'
      | succ _ =>
        have h_branch := h_wp'.2 c hc
        rw [h_eval] at h_branch
        exact h_branch
    · intro out h_beh
      unfold Behavior ReachesResult at h_beh
      rw [h_init] at h_beh
      let ⟨s, h_reach, c, hc, h_eval⟩ := h_beh
      let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_reach
      cases fuel' with
      | zero => exact False.elim h_wp'
      | succ _ =>
        have h_branch := h_wp'.2 c hc
        rw [h_eval] at h_branch
        exact h_branch
    · let ⟨s_end, res, h_reach, h_term, h_res⟩ :=
        exists_terminal_of_wpOutcomeState h_wp
      cases res with
      | step _ => exact False.elim h_res
      | fault _ => exact False.elim h_res
      | done out =>
        refine ⟨out, ?_, h_res⟩
        unfold Behavior ReachesResult
        rw [h_init]
        exact ⟨s_end, h_reach, h_term⟩

/-- Soundness, all-path termination, and exclusivity of `wpFaultProg`: proving
`wpFaultProg p fuel q expected` establishes
`ReachesResult p q (.fault expected)`, rules out any other fault kind
`k ≠ expected`, any normal terminal outcome `.done out`, and divergence
`Diverges p q`, and refutes `WellFormed p q`. -/
theorem reaches_fault_and_exclusive_of_wpFault_base :
    WpFaultSoundnessClaim wpFaultProg := by
  intro p q fuel expected h_wp_orig
  have h_wp := h_wp_orig
  unfold wpFaultProg at h_wp
  cases h_init : initState p q with
  | error k =>
    rw [h_init] at h_wp
    subst h_wp
    have h_reaches_exp : ReachesResult p q (.fault k) := by
      unfold ReachesResult; rw [h_init]
    have h_ndiv : ¬ Diverges p q := by
      intro h_div
      let ⟨_, h_init', _⟩ := h_div
      rw [h_init] at h_init'
      cases h_init'
    refine ⟨h_reaches_exp, ?_, ?_, h_ndiv, fun hwf => hwf.2 k h_reaches_exp⟩
    · intro k' h_ne h_res
      unfold ReachesResult at h_res
      rw [h_init] at h_res
      injection h_res with h_eq
      exact h_ne h_eq
    · intro out h_res
      unfold ReachesResult at h_res
      rw [h_init] at h_res
      cases h_res
  | ok s₀ =>
    have h_ndiv : ¬ Diverges p q := not_diverges_of_wpFaultProg h_wp_orig
    rw [h_init] at h_wp
    let ⟨s_end, res, h_reach, h_term, h_res⟩ :=
      exists_terminal_of_wpOutcomeState h_wp
    cases res with
    | step _ => exact False.elim h_res
    | done _ => exact False.elim h_res
    | fault k_end =>
      dsimp only at h_res
      subst h_res
      have h_reaches_exp : ReachesResult p q (.fault k_end) := by
        unfold ReachesResult; rw [h_init]; exact ⟨s_end, h_reach, h_term⟩
      refine ⟨h_reaches_exp, ?_, ?_, h_ndiv,
        fun hwf => hwf.2 k_end h_reaches_exp⟩
      · intro k h_ne h_res_k
        unfold ReachesResult at h_res_k
        rw [h_init] at h_res_k
        let ⟨s, h_r, c, hc, h_eval⟩ := h_res_k
        let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_r
        cases fuel' with
        | zero => exact False.elim h_wp'
        | succ _ =>
          have h_branch := h_wp'.2 c hc
          rw [h_eval] at h_branch
          exact h_ne h_branch
      · intro out h_res_done
        unfold ReachesResult at h_res_done
        rw [h_init] at h_res_done
        let ⟨s, h_r, c, hc, h_eval⟩ := h_res_done
        let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_r
        cases fuel' with
        | zero => exact False.elim h_wp'
        | succ _ =>
          have h_branch := h_wp'.2 c hc
          rw [h_eval] at h_branch
          exact h_branch

/-- Exact-outcome adequacy corollary deriving `WellFormed`, `Behavior`,
`¬ Diverges`, and `SatisfiesPost` from `wpProg p fuel q (fun o => o = out)`. -/
theorem spec_and_behavior_of_wp_eq {p : Program} {q : Query} {fuel : Nat}
    {out : TerminalOut}
    (h_wp : wpProg p fuel q (fun o => o = out)) :
    WellFormed p q ∧ Behavior p q out ∧ ¬ Diverges p q ∧
      ∀ post : TerminalOut → Prop, post out → SatisfiesPost p q post := by
  let ⟨h_sat, h_ndiv, out', h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp_base p q fuel (fun o => o = out) h_wp
  subst h_eq
  refine ⟨h_sat.1, h_beh, h_ndiv, ?_⟩
  intro post h_post
  refine ⟨h_sat.1, fun o h_o => ?_⟩
  rw [h_sat.2 o h_o]
  exact h_post

/-- Establish `PositiveCanaryClaim p q expectedRet` from a `wpProg` proof. -/
theorem positiveCanary_of_wp {p : Program} {q : Query} {fuel : Nat}
    {expectedRet : Val}
    (h_wp : wpProg p fuel q (fun out => out = .returned ⟨expectedRet, ⟨[]⟩⟩)) :
    PositiveCanaryClaim p q expectedRet :=
  let h := spec_and_behavior_of_wp_eq h_wp
  ⟨h.1, h.2.1⟩

/-- Establish `PositiveCanaryClaim p q expectedRet` from a deterministic
`execProg` proof (which reduces directly by `rfl` on concrete programs). -/
theorem positiveCanary_of_exec {p : Program} {q : Query} {fuel : Nat}
    {expectedRet : Val}
    (h_exec :
      execProg p fuel q (fun out => out = .returned ⟨expectedRet, ⟨[]⟩⟩)) :
    PositiveCanaryClaim p q expectedRet :=
  positiveCanary_of_wp (wpProg_of_execProg h_exec)

/-- Establish `NegativeCanaryClaim p q expectedFault otherFault` from a
`wpFaultProg` proof. -/
theorem negativeCanary_of_wpFault {p : Program} {q : Query} {fuel : Nat}
    {expectedFault otherFault : FaultKind}
    (h_ne : otherFault ≠ expectedFault)
    (h_wp : wpFaultProg p fuel q expectedFault) :
    NegativeCanaryClaim p q expectedFault otherFault := by
  let ⟨h_f, h_excl, _, _, h_nwf⟩ :=
    reaches_fault_and_exclusive_of_wpFault_base p q fuel expectedFault h_wp
  exact ⟨h_f, h_excl otherFault h_ne, h_nwf⟩

/-- Establish `NegativeCanaryClaim p q expectedFault otherFault` from a
deterministic `execFaultProg` proof (which reduces directly by `rfl`). -/
theorem negativeCanary_of_execFault {p : Program} {q : Query} {fuel : Nat}
    {expectedFault otherFault : FaultKind}
    (h_ne : otherFault ≠ expectedFault)
    (h_exec : execFaultProg p fuel q expectedFault) :
    NegativeCanaryClaim p q expectedFault otherFault :=
  negativeCanary_of_wpFault h_ne (wpFaultProg_of_execFaultProg h_exec)

/-! ## Part II: Profile v2 Fuel-Bounded Execution & Adequacy -/

/-- Fuel-bounded execution predicate over deterministic Profile v2
small-step transitions `evalStepV2 p`. -/
@[expose] def execOutcomeStateV2 (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun _ => False)
    (fun _ ih st =>
      match evalStepV2 p st with
      | .step st' => ih st'
      | .done out => onDone out
      | .fault k => onFault k)
    fuel s

/-- Profile v2 state-level normal-termination predicate. -/
abbrev execStateV2 (p : Program) (fuel : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  execOutcomeStateV2 p post (fun _ => False) fuel s

/-- Whole-program Profile v2 normal-termination predicate starting from
`initStateV2 p q`. -/
@[expose] def execProgV2 (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initStateV2 p q with
  | .error _ => False
  | .ok s₀ => execStateV2 p fuel s₀ post

/-- Prepend a single `StepV2 p s₁ (.step s₂)` to a `ReachesV2 p s₂ s₃` chain. -/
theorem ReachesV2.head {p : Program} {s₁ s₂ s₃ : State}
    (h_first : StepV2 p s₁ (.step s₂))
    (h_rest : ReachesV2 p s₂ s₃) :
    ReachesV2 p s₁ s₃ := by
  induction h_rest with
  | refl => exact ReachesV2.tail (ReachesV2.refl s₁) h_first
  | tail _ h_last ih => exact ReachesV2.tail ih h_last

/-- Any state reachable via `ReachesV2` preserves `execOutcomeStateV2` at some
positive remaining fuel. -/
theorem execOutcomeStateV2_of_reaches
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s₁ s₂ : State} {fuel : Nat}
    (h_exec : execOutcomeStateV2 p onDone onFault fuel s₁)
    (h_reach : ReachesV2 p s₁ s₂) :
    ∃ fuel', execOutcomeStateV2 p onDone onFault fuel' s₂ := by
  induction h_reach with
  | refl => exact ⟨fuel, h_exec⟩
  | @tail sMid sNext _ h_step ih =>
    let ⟨fuel₁, h_e₁⟩ := ih
    cases fuel₁ with
    | zero => exact False.elim h_e₁
    | succ fuel₂ =>
      let ⟨c, _, h_eval⟩ := h_step
      have h_eval' : evalStepV2 p sMid = .step sNext := h_eval
      change (match evalStepV2 p sMid with
        | .step st' => execOutcomeStateV2 p onDone onFault fuel₂ st'
        | .done out => onDone out
        | .fault k => onFault k) at h_e₁
      rw [h_eval'] at h_e₁
      exact ⟨fuel₂, h_e₁⟩

/-- Every state satisfying `execOutcomeStateV2` reaches a terminal `.done` or
`.fault` step within `fuel` steps. -/
theorem exists_terminal_of_execOutcomeStateV2
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h_exec : execOutcomeStateV2 p onDone onFault fuel s) :
    ∃ s_end res, ReachesV2 p s s_end ∧ StepV2 p s_end res ∧
      match res with
      | .step _ => False
      | .done out => onDone out
      | .fault k => onFault k := by
  induction fuel generalizing s with
  | zero => exact False.elim h_exec
  | succ f ih =>
    change (match evalStepV2 p s with
      | .step st' => execOutcomeStateV2 p onDone onFault f st'
      | .done out => onDone out
      | .fault k => onFault k) at h_exec
    cases h_eval : evalStepV2 p s with
    | step s' =>
      rw [h_eval] at h_exec
      let ⟨s_end, res, h_reach, h_term, h_res⟩ := ih h_exec
      exact ⟨s_end, res, ReachesV2.head ⟨0, rfl, h_eval⟩ h_reach, h_term, h_res⟩
    | done out =>
      rw [h_eval] at h_exec
      exact ⟨s, .done out, ReachesV2.refl s, ⟨0, rfl, h_eval⟩, h_exec⟩
    | fault k =>
      rw [h_eval] at h_exec
      exact ⟨s, .fault k, ReachesV2.refl s, ⟨0, rfl, h_eval⟩, h_exec⟩

/-- No state satisfying `execOutcomeStateV2` admits an infinite `StepV2`
trace. -/
theorem not_infinite_trace_of_execOutcomeStateV2
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} (trace : Nat → State),
      execOutcomeStateV2 p onDone onFault fuel (trace 0) →
      (∀ n : Nat, StepV2 p (trace n) (.step (trace (n + 1)))) →
      False
  | 0, _, h_exec, _ => h_exec
  | fuel + 1, trace, h_exec, h_steps => by
    let ⟨c, _, h_eval⟩ := h_steps 0
    have h_eval' : evalStepV2 p (trace 0) = .step (trace 1) := h_eval
    change (match evalStepV2 p (trace 0) with
      | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
      | .done out => onDone out
      | .fault k => onFault k) at h_exec
    rw [h_eval'] at h_exec
    exact not_infinite_trace_of_execOutcomeStateV2 (fun n => trace (n + 1))
      h_exec (fun n => h_steps (n + 1))

/-- Exact-outcome adequacy theorem for Profile v2 `execProgV2`: derives
`WellFormedV2`, `BehaviorV2`, `¬ DivergesV2`, and `SatisfiesPostV2` directly. -/
theorem spec_and_behaviorV2_of_exec_eq {p : Program} {q : Query} {fuel : Nat}
    {out : TerminalOut}
    (h_exec : execProgV2 p fuel q (fun o => o = out)) :
    WellFormedV2 p q ∧ BehaviorV2 p q out ∧ ¬ DivergesV2 p q ∧
      ∀ post : TerminalOut → Prop, post out → SatisfiesPostV2 p q post := by
  have h_ndiv : ¬ DivergesV2 p q := by
    intro h_div
    let ⟨s₀, h_init, trace, h_tr0, h_steps⟩ := h_div
    unfold execProgV2 at h_exec
    rw [h_init, ← h_tr0] at h_exec
    exact not_infinite_trace_of_execOutcomeStateV2 trace h_exec h_steps
  unfold execProgV2 at h_exec
  cases h_init : initStateV2 p q with
  | error _ => rw [h_init] at h_exec; exact False.elim h_exec
  | ok s₀ =>
    rw [h_init] at h_exec
    have h_wf : WellFormedV2 p q := by
      refine ⟨⟨s₀, h_init, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
      intro k h_fault
      unfold ReachesResultV2 at h_fault
      rw [h_init] at h_fault
      let ⟨s, h_reach, c, hc, h_eval⟩ := h_fault
      let ⟨fuel', h_e'⟩ := execOutcomeStateV2_of_reaches h_exec h_reach
      cases fuel' with
      | zero => exact False.elim h_e'
      | succ f' =>
        have h_eval' : evalStepV2 p s = .fault k := h_eval
        change (match evalStepV2 p s with
          | .step st' => execOutcomeStateV2 p (fun o => o = out) (fun _ => False) f' st'
          | .done o => o = out
          | .fault _ => False) at h_e'
        rw [h_eval'] at h_e'
        exact h_e'
    have h_beh : BehaviorV2 p q out := by
      let ⟨s_end, res, h_reach, h_term, h_res⟩ :=
        exists_terminal_of_execOutcomeStateV2 h_exec
      cases res with
      | step _ => exact False.elim h_res
      | fault _ => exact False.elim h_res
      | done out' =>
        dsimp only at h_res
        subst h_res
        unfold BehaviorV2 ReachesResultV2
        rw [h_init]
        exact ⟨s_end, h_reach, h_term⟩
    refine ⟨h_wf, h_beh, h_ndiv, fun post h_post => ⟨h_wf, fun out' h_b => ?_⟩⟩
    unfold BehaviorV2 ReachesResultV2 at h_b
    rw [h_init] at h_b
    let ⟨s, h_reach, c, hc, h_eval⟩ := h_b
    let ⟨fuel', h_e'⟩ := execOutcomeStateV2_of_reaches h_exec h_reach
    cases fuel' with
    | zero => exact False.elim h_e'
    | succ f' =>
      have h_eval' : evalStepV2 p s = .done out' := h_eval
      change (match evalStepV2 p s with
        | .step st' => execOutcomeStateV2 p (fun o => o = out) (fun _ => False) f' st'
        | .done o => o = out
        | .fault _ => False) at h_e'
      rw [h_eval'] at h_e'
      rw [h_e']
      exact h_post

end Anneal.MirWp

end
