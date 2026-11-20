-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.MirAst
import Trusted.MirSemantics

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-!
# Fuel-Bounded Weakest Precondition and Scalar Adequacy (`MirWp`)

This untrusted `theory/` module provides the core fuel-bounded weakest
precondition calculus, adequacy theorems, width-parametric scalar theory,
and Day-1 non-vacuity canaries over `Trusted.MirAst` and
`Trusted.MirSemantics`:

1. **Unified Fuel-Bounded Weakest Precondition (`wpOutcomeState`, `wpState`,
   `wpFaultState`, `wpProg`, `wpFaultProg`) and Deterministic Fast Path
   (`execOutcomeState`, `execState`, `execFaultState`, `execProg`,
   `execFaultProg`):** `@Nat.rec` outcome predicates into `Prop` (no codegen
   exemptions or `_unsafe_rec`), preserving the `ValidChoice`-quantified shape
   of `wpOutcomeState`/`wpProg`/`wpFaultProg` while bridging deterministic
   `c = 0` `rfl`-reducible execution via `wpProg_of_execProg` and
   `wpFaultProg_of_execFaultProg`, together with rule of consequence, fuel
   weakening, non-divergence, and the audited adequacy theorems
   (`wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg` and
   `reaches_fault_and_exclusive_of_wpFault : WpFaultSoundnessClaim
   wpFaultProg`).
2. **Width-Parametric Bitvector and Scalar Adequacy:** Exact modular
   characterization and idempotence of `truncateBits`, totality and
   well-formedness of `truncateScalar`, and all 19 Pass 1 non-vacuity and
   parameter-boundary canaries.
-/

/-! ## Part I: Unified Fuel-Bounded Weakest Precondition & Adequacy -/

/-- Unified structural fuel-bounded weakest precondition over `evalStep`.
Using `@Nat.rec` into `Prop` avoids both codegen exemptions and `_unsafe_rec`
while preserving the `ValidChoice`-quantified shape expected by downstream
correspondence proofs. -/
def wpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
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
def wpProg (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => wpState p fuel s₀ post

/-- Whole-program fuel-bounded fault verifier starting from `initState p q`. -/
def wpFaultProg (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initState p q with
  | .error k => k = expected
  | .ok s₀ => wpFaultState p fuel s₀ expected

/-- Deterministic `c = 0` fast-path structural fuel-bounded execution
predicate over `evalStep p 0`. Concrete runs reduce directly by `rfl` and lift
into `wpOutcomeState` via `wpOutcomeState_of_execOutcomeState`. -/
def execOutcomeState (p : Program) (onDone : TerminalOut → Prop)
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
def execProg (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => execState p fuel s₀ post

/-- Whole-program deterministic `c = 0` fault-termination predicate starting
from `initState p q`. -/
def execFaultProg (p : Program) (fuel : Nat) (q : Query)
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
theorem wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg := by
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
theorem reaches_fault_and_exclusive_of_wpFault :
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
    wellFormed_and_spec_of_wp p q fuel (fun o => o = out) h_wp
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
    reaches_fault_and_exclusive_of_wpFault p q fuel expectedFault h_wp
  exact ⟨h_f, h_excl otherFault h_ne, h_nwf⟩

/-- Establish `NegativeCanaryClaim p q expectedFault otherFault` from a
deterministic `execFaultProg` proof (which reduces directly by `rfl`). -/
theorem negativeCanary_of_execFault {p : Program} {q : Query} {fuel : Nat}
    {expectedFault otherFault : FaultKind}
    (h_ne : otherFault ≠ expectedFault)
    (h_exec : execFaultProg p fuel q expectedFault) :
    NegativeCanaryClaim p q expectedFault otherFault :=
  negativeCanary_of_wpFault h_ne (wpFaultProg_of_execFaultProg h_exec)

/-! ## Width-Parametric `IntWidth`, `BitVec`, and `truncateScalar` Adequacy -/

/-- Extensionality of `BitVec n` via `.toNat`. -/
theorem bitVec_eq_of_toNat_eq {n : Nat} {a b : BitVec n}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

/-- Unsigned modulus $2^{\text{bitWidth}}$ for proof-side wrapping and range
lemmas. Defined directly in `theory/` rather than `Trusted.MirAst` so the
trusted specification stays free of proof-only arithmetic helpers. -/
def intWidthModulus : IntWidth → Nat
  | .i8 => Nat.pow 2 8
  | .i16 => Nat.pow 2 16
  | .i32 => Nat.pow 2 32
  | .i64 | .isize => Nat.pow 2 64
  | .i128 => Nat.pow 2 128

/-- Every `IntWidth` has a strictly positive unsigned modulus $2^{\text{bits}}$.
-/
theorem intWidth_modulus_pos (w : IntWidth) : 0 < intWidthModulus w := by
  cases w <;> decide

/-- Exact arithmetic characterization of `truncateBits` across all six
`IntWidth` variants (`.i8`, `.i16`, `.i32`, `.i64`, `.i128`, `.isize`). -/
theorem toNat_truncateBits (w : IntWidth) (x : BitVec 128) :
    (truncateBits w x).toNat = Nat.mod x.toNat (intWidthModulus w) := by
  cases w
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 7 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 15 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 31 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 63 0 x).isLt (by decide))
  · exact Nat.mod_eq_of_lt (bvExtractLsb 127 0 x).isLt
  · exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (bvExtractLsb 63 0 x).isLt (by decide))

/-- Width-parametric idempotence of `truncateBits` across all `IntWidth`s. -/
theorem truncateBits_idem (w : IntWidth) (x : BitVec 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, toNat_truncateBits]
  exact Nat.mod_eq_of_lt (Nat.mod_lt x.toNat (intWidth_modulus_pos w))

/-- `.i64` specialization of `truncateBits_idem` for 64-bit scalar proofs. -/
theorem truncateBits_i64_idem (x : BitVec 128) :
    truncateBits .i64 (truncateBits .i64 x) = truncateBits .i64 x :=
  truncateBits_idem .i64 x

/-- Any `BitVec 128` bounded by `intWidthModulus w` is fixed by
`truncateBits w`. -/
theorem truncateBits_of_toNat_lt {w : IntWidth} {x : BitVec 128}
    (h : x.toNat < intWidthModulus w) :
    truncateBits w x = x := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits]
  exact Nat.mod_eq_of_lt h

/-- Every scalar payload produced by `truncateBits w` satisfies `ScalarVal.wf`.
-/
theorem scalarWf_truncateBits (w : IntWidth) (s : Bool) (x : BitVec 128) :
    ScalarVal.wf ⟨w, s, truncateBits w x⟩ = true := by
  unfold ScalarVal.wf
  dsimp only
  rw [truncateBits_idem]
  exact beq_self_eq_true (truncateBits w x)

/-- Simplify a propositional `if-then-else` when the condition holds. -/
theorem ite_prop_true {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : P) : (@ite α P inst t e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

/-- Simplify a propositional `if-then-else` when the condition is refuted. -/
theorem ite_prop_false {α : Type} {P : Prop} {inst : Decidable P}
    {t e : α} (h : ¬ P) : (@ite α P inst t e) = e := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

/-- Simplify a boolean `if-then-else` when the condition is `true`. -/
theorem ite_bool_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

/-- Simplify a boolean `if-then-else` when the condition is `false`. -/
theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

/-- Every 128-bit bitvector decodes via `bvToInt` strictly within the signed
`i128` range `[-2^127, 2^127)`, refuting the `.unsupported` range guard in
`truncateScalar`. -/
theorem bvToInt_in_i128_range (x : BitVec 128) :
    (decide (bvToInt x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (bvToInt x ≥ HPow.hPow (2 : Int) 127)) = false := by
  unfold bvToInt
  have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
  have hHalf128 : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
  have hInt127 : HPow.hPow (2 : Int) 127 = Int.ofNat (Nat.pow 2 127) := by
    decide
  have hNeg127 : Neg.neg (Int.ofNat (Nat.pow 2 127)) =
      Int.negSucc (Nat.pow 2 127 - 1) := by decide
  rw [hInt127, hNeg127]
  cases Nat.lt_or_ge (2 * x.toNat) (Nat.pow 2 128) with
  | inl hCmp =>
    rw [ite_prop_true hCmp]
    have hLt2 : 2 * x.toNat < 2 * Nat.pow 2 127 := by
      rw [← hPow128]
      exact hCmp
    have hLt : x.toNat < Nat.pow 2 127 := by
      cases Nat.lt_or_ge x.toNat (Nat.pow 2 127) with
      | inl h => exact h
      | inr hGe =>
        have hGe2 : 2 * Nat.pow 2 127 ≤ 2 * x.toNat :=
          Nat.mul_le_mul_left 2 hGe
        exact False.elim (Nat.not_le_of_gt hLt2 hGe2)
    have hNotNeg :
        ¬ (Int.ofNat x.toNat < Int.negSucc (Nat.pow 2 127 - 1)) :=
      fun h => nomatch h
    have hNotGe : ¬ (Int.ofNat x.toNat ≥ Int.ofNat (Nat.pow 2 127)) := by
      intro hGeI
      have hPos127 : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) := by decide
      rw [hPos127] at hGeI
      change Int.NonNeg
        (Int.subNatNat x.toNat (Nat.succ (Nat.pow 2 127 - 1))) at hGeI
      rw [← hPos127] at hGeI
      unfold Int.subNatNat at hGeI
      cases hSub : Nat.pow 2 127 - x.toNat with
      | zero => exact Nat.not_le_of_gt hLt (Nat.le_of_sub_eq_zero hSub)
      | succ k => rw [hSub] at hGeI; nomatch hGeI
    rw [decide_eq_false hNotNeg, decide_eq_false hNotGe]
    rfl
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)]
    have hGe2 : 2 * Nat.pow 2 127 ≤ 2 * x.toNat := by
      rw [← hPow128]
      exact hCmp
    have hGe : Nat.pow 2 127 ≤ x.toNat := by
      cases Nat.lt_or_ge x.toNat (Nat.pow 2 127) with
      | inr h => exact h
      | inl hLt =>
        have hLt2 : 2 * x.toNat < 2 * Nat.pow 2 127 := by
          have h1 : x.toNat + x.toNat < Nat.pow 2 127 + Nat.pow 2 127 :=
            Nat.add_lt_add hLt hLt
          have hMulL : 2 * x.toNat = x.toNat + x.toNat :=
            Nat.succ_mul 1 x.toNat ▸ congrArg (fun z => z + x.toNat)
              (Nat.one_mul x.toNat)
          have hMulR : 2 * Nat.pow 2 127 =
              Nat.pow 2 127 + Nat.pow 2 127 :=
            Nat.succ_mul 1 (Nat.pow 2 127) ▸
              congrArg (fun z => z + Nat.pow 2 127)
                (Nat.one_mul (Nat.pow 2 127))
          rw [hMulL, hMulR]
          exact h1
        exact False.elim (Nat.not_lt_of_ge hGe2 hLt2)
    have hSubDef :
        Int.ofNat x.toNat - Int.ofNat (Nat.pow 2 128) =
        Int.subNatNat x.toNat (Nat.pow 2 128) := by
      have h1 : Neg.neg (Int.ofNat (Nat.pow 2 128)) =
          Int.negSucc (Nat.pow 2 128 - 1) := by decide
      have h2 : Nat.succ (Nat.pow 2 128 - 1) = Nat.pow 2 128 := by decide
      change Int.add (Int.ofNat x.toNat)
        (Neg.neg (Int.ofNat (Nat.pow 2 128))) = _
      rw [h1]
      change Int.subNatNat x.toNat (Nat.succ (Nat.pow 2 128 - 1)) = _
      rw [h2]
    rw [hSubDef]
    unfold Int.subNatNat
    cases hDiff : Nat.pow 2 128 - x.toNat with
    | zero =>
      exact False.elim (Nat.not_le_of_gt x.isLt (Nat.le_of_sub_eq_zero hDiff))
    | succ k =>
      dsimp only
      have hKLt : k < Nat.pow 2 127 := by
        have hSum : x.toNat + (k + 1) = Nat.pow 2 127 + Nat.pow 2 127 := by
          have hAdd := Nat.add_sub_of_le (Nat.le_of_lt x.isLt)
          have hHalfPow :
              HPow.hPow (2 : Nat) 128 = Nat.pow 2 127 + Nat.pow 2 127 := by
            decide
          change x.toNat + (Nat.pow 2 128 - x.toNat) =
            HPow.hPow (2 : Nat) 128 at hAdd
          rw [hDiff, hHalfPow] at hAdd
          exact hAdd
        have hLeAdd : Nat.pow 2 127 + (k + 1) ≤
            Nat.pow 2 127 + Nat.pow 2 127 := by
          rw [← hSum]
          exact Nat.add_le_add_right hGe (k + 1)
        exact Nat.le_of_add_le_add_left hLeAdd
      have hNotGe : ¬ (Int.negSucc k ≥ Int.ofNat (Nat.pow 2 127)) := by
        intro hGeI
        have hPos127 : Nat.pow 2 127 = Nat.succ (Nat.pow 2 127 - 1) := by
          decide
        rw [hPos127] at hGeI
        nomatch hGeI
      have hNotLt :
          ¬ (Int.negSucc k < Int.negSucc (Nat.pow 2 127 - 1)) := by
        intro hLtI
        cases k with
        | zero =>
          have hZ : Int.negSucc 0 + 1 = Int.ofNat 0 := by decide
          change Int.NonNeg
            (Int.negSucc (Nat.pow 2 127 - 1) - (Int.negSucc 0 + 1)) at hLtI
          rw [hZ] at hLtI
          nomatch hLtI
        | succ k' =>
          have hSucc127 : Nat.succ (Nat.pow 2 127 - 1) = Nat.pow 2 127 := by
            decide
          change Int.NonNeg
            (Int.subNatNat (Nat.succ k')
              (Nat.succ (Nat.pow 2 127 - 1))) at hLtI
          rw [hSucc127] at hLtI
          unfold Int.subNatNat at hLtI
          cases hRem : Nat.pow 2 127 - Nat.succ k' with
          | zero =>
            exact Nat.not_le_of_gt hKLt (Nat.le_of_sub_eq_zero hRem)
          | succ r =>
            rw [hRem] at hLtI
            nomatch hLtI
      rw [decide_eq_false hNotLt, decide_eq_false hNotGe]
      rfl

/-- Totality and `ScalarVal.wf` preservation of `truncateScalar` across all six
`IntWidth` variants, both signedness modes, and all integers `value : Int`. -/
theorem truncateScalar_ok (w : IntWidth) (s : Bool) (value : Int) :
    ∃ (sv : ScalarVal) (lossy : Bool),
      truncateScalar w s value = .ok (sv, lossy) ∧
      sv.width = w ∧ sv.signed = s ∧ sv.wf = true := by
  unfold truncateScalar
  cases s with
  | false =>
    exact ⟨⟨w, false, truncateBits w (bvOfInt 128 value)⟩,
      truncateBits w (bvOfInt 128 value) != bvOfInt 128 value,
      rfl, rfl, rfl, scalarWf_truncateBits w false (bvOfInt 128 value)⟩
  | true =>
    dsimp only
    rw [bvToInt_in_i128_range (bvOfInt 128 value)]
    let wrapped := bvToInt (bvOfInt 128 value)
    let raw := bvOfInt 128 wrapped
    let trunc := truncateBits w raw
    exact ⟨⟨w, true, trunc⟩, signExtendBits w trunc != wrapped,
      rfl, rfl, rfl, scalarWf_truncateBits w true raw⟩

/-! ## Concrete Day-1 Non-Vacuity and Parameter-Boundary Canaries -/

/-- Canary `D1`: `progAddU32` on `(30, 12)` is well-formed and returns `42`. -/
theorem canary_positive_add_anneal : CanaryPositiveAddAnnealClaim :=
  positiveCanary_of_exec (fuel := 2) rfl

/-- Canary `D2`: `progEmptyUnitFn` is well-formed and returns `Val.unit`. -/
theorem canary_positive_empty_unit_fn : CanaryPositiveEmptyUnitFnClaim :=
  positiveCanary_of_exec (fuel := 1) rfl

/-- Control-flow and statement canary (`nop`, `storageLive`, `storageDead`,
`goto`, and both matched and `otherwise` arms of `switchInt`). -/
theorem canary_positive_stmts_and_cf_anneal :
    CanaryPositiveStmtsAndCfAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 10) rfl,
   positiveCanary_of_exec (fuel := 10) rfl⟩

/-- Unary-operator canary (`UnOp.not` on `bool` and `u8`, `UnOp.neg` on signed
`i8` including wrapping `-INT_MIN == INT_MIN`). -/
theorem canary_positive_unop_anneal : CanaryPositiveUnopAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Binary-operator canary covering every supported `BinOp` variant at boundary
values across unsigned integers, signed integers, shifts, and booleans. -/
theorem canary_positive_all_binops_anneal :
    CanaryPositiveAllBinopsAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Integer-width boundary canary covering all six `IntWidth` variants (`.i8`,
`.i16`, `.i32`, `.i64`, `.i128`, `.isize`) in both unsigned (`MAX + 1 = 0`) and
signed (`INT_MAX + 1 = INT_MIN`) modes. -/
theorem canary_positive_all_int_widths_anneal :
    CanaryPositiveAllIntWidthsAnnealClaim :=
  ⟨⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩,
   ⟨positiveCanary_of_exec (fuel := 2) rfl,
    positiveCanary_of_exec (fuel := 2) rfl⟩⟩

/-- Canary `D3`: dividing by zero reaches `.fault .undefined` (and not
`.fault .unsupported`) and refutes `WellFormed`. -/
theorem canary_negative_ub_div_zero_anneal :
    CanaryNegativeUbDivZeroAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Canary `D4`: signed `(-128i8) % (-1i8)` reaches `.fault .undefined` (and
not `.fault .unsupported`) and refutes `WellFormed`. -/
theorem canary_negative_ub_signed_rem_overflow_i8 :
    CanaryNegativeUbSignedRemOverflowI8Claim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Canary `D5`: executing `.unsupported` reaches `.fault .unsupported` (and
not `.fault .undefined`) and refutes `WellFormed`. -/
theorem canary_negative_unsupported_anneal :
    CanaryNegativeUnsupportedAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unchecked-overflow canary: on `(u32::MAX, 1)`, `AddUnchecked`
(`progAddUncheckedU32`) reaches `.fault .undefined` (and not
`.fault .unsupported`) and refutes `WellFormed`, while wrapping `Add`
(`progAddU32`) on the same inputs is well-formed and returns `0`. -/
theorem canary_negative_ub_add_unchecked_overflow_u32 :
    CanaryNegativeUbAddUncheckedOverflowU32Claim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   positiveCanary_of_exec (fuel := 2) rfl⟩

/-- Shift-overflow canary: `ShlUnchecked` at shift amount `== bitWidth` (`32`
on `u32`) and `ShrUnchecked` at negative signed shift (`-1i8` on `u32`) both
reach `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_shift_unchecked_at_bitwidth_anneal :
    CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 1)
     (fun h => FaultKind.noConfusion h) rfl⟩

/-- Storage-dead read canary: reading a local after `StatementKind.storageDead`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_storage_dead_read_anneal :
    CanaryNegativeUbStorageDeadReadAnnealClaim :=
  negativeCanary_of_execFault (fuel := 4)
    (fun h => FaultKind.noConfusion h) rfl

/-- Storage-dead return-place canary: executing `StatementKind.storageDead 0`
on `_0` reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_ub_storage_dead_return_place_anneal :
    CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unreachable terminator canary: executing `TerminatorKind.unreachable`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_unreachable_anneal :
    CanaryNegativeUbUnreachableAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Unsigned-negation canary: executing `UnOp.neg` on an unsigned integer
(`u32`) reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_unsupported_unsigned_neg_anneal :
    CanaryNegativeUnsupportedUnsignedNegAnnealClaim :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Explicit-repr fieldless enum positive canary: `#[repr(u8)]` non-index tag
decoding + `u8` `Rvalue.discriminant` and signed `i8` -> `isize` sign-extended
tag decoding. -/
theorem canary_positive_enum_explicit_repr_anneal :
    CanaryPositiveEnumExplicitReprAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 5) rfl,
   positiveCanary_of_exec (fuel := 5) rfl⟩

/-- Single-variant inhabited ZST enum positive canary: implicit return without
writing `_0`, non-deinitializing `Operand.move`, `ConstLit.zeroSized`, and
`Rvalue.discriminant`. -/
theorem canary_positive_zst_single_enum_anneal :
    CanaryPositiveZstSingleEnumAnnealClaim :=
  ⟨positiveCanary_of_exec (fuel := 1) rfl,
   positiveCanary_of_exec (fuel := 10) rfl⟩

/-- Fieldless enum negative UB canary: invalid constant scalar tag `1` on
`ReprU8 { A = 10, B = 20 }` and reading `Rvalue.discriminant` from an
uninitialized scalar-tagged enum local both reach `.fault .undefined`. -/
theorem canary_negative_ub_enum_invalid_tag_and_uninit_anneal :
    CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim :=
  ⟨negativeCanary_of_execFault (fuel := 2)
     (fun h => FaultKind.noConfusion h) rfl,
   negativeCanary_of_execFault (fuel := 2)
     (fun h => FaultKind.noConfusion h) rfl⟩

/-- Crate/unit/body verification canary exercising positive `CrateTheorem` and
`UnitTheorem` acceptance, safe vs. `unsafe` contract gating (`isUnsafe`),
`MirTy.never` static-admission non-vacuity, `p.bodies[defId]` lookup binding in
`BodyVerified`, empty-`bodies` / out-of-bounds `entryDefId` / duplicate
`identity` rejection, non-`BodyVerified` body rejection inside a crate, false
`specs.property` rejection, and `.crate` vs. `.unit` scope mismatch rejection.
-/
theorem canary_crate_and_body_verified_anneal :
    CanaryCrateAndBodyVerifiedAnnealClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    intro defId body hGet
    cases defId with
    | zero =>
      injection hGet with hBody; subst hBody
      refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
      cases args with
      | nil =>
        refine (positiveCanary_of_exec (fuel := 1) (expectedRet := .unit) ?_).1
        rfl
      | cons _ _ => exact Bool.noConfusion hArgs
    | succ defId =>
      cases defId with
      | zero =>
        injection hGet with hBody; subst hBody
        refine ⟨rfl, rfl, fun args _ hSafe => ?_⟩
        have hEq : args = [.bool true] := hSafe rfl
        subst hEq
        refine (positiveCanary_of_exec (fuel := 3)
          (expectedRet := u32Val 42) ?_).1
        rfl
      | succ defId =>
        cases defId with
        | zero =>
          injection hGet with hBody; subst hBody
          refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
          cases args with
          | nil => exact Bool.noConfusion hArgs
          | cons v rest =>
            have hCheck : checkVal v .never = true := by
              revert hArgs
              change (checkVal v .never && checkArgsMatch rest []) = true → _
              cases checkVal v .never <;> intro h <;>
                first | rfl | exact Bool.noConfusion h
            cases v with
            | scalar sv =>
              revert hCheck
              dsimp [checkVal, Val.ty?, MirTy.beq]
              cases sv.wf <;> intro h <;> exact Bool.noConfusion h
            | ptr _ | bool _ | unit | tuple _ | bytes _ =>
              exact Bool.noConfusion hCheck
            | enumVal ety idx =>
              revert hCheck
              dsimp [checkVal, Val.ty?, MirTy.beq]
              cases enumAdmitted ety <;>
                cases Nat.blt idx ety.discriminants.length <;>
                intro h <;> exact Bool.noConfusion h
        | succ _ =>
          dsimp [canaryValidCrate, Trusted.MirSemantics.getElem?] at hGet
          cases hGet
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    intro defId body hGet
    cases defId with
    | zero =>
      injection hGet with hBody; subst hBody
      refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
      cases args with
      | nil =>
        refine (positiveCanary_of_exec (fuel := 1) (expectedRet := .unit) ?_).1
        rfl
      | cons _ _ => exact Bool.noConfusion hArgs
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hVer
    have hWf := hVer.2.2 [.bool false] rfl (fun h => Bool.noConfusion h)
    have hNeg : NegativeCanaryClaim
        (entryProgForBody {
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canaryUnsafeGuardedBody false]
        } 0)
        { args := [.bool false] } .undefined .unsupported :=
      negativeCanary_of_execFault (fuel := 2)
        (fun h => FaultKind.noConfusion h) rfl
    exact hNeg.2.2 hWf
  · intro hVer
    exact Bool.noConfusion hVer.2.1
  · intro hVer
    have hEq : canarySafeUnitBody = canaryUnsafeGuardedBody false := by
      injection hVer.1
    have hArg : (canarySafeUnitBody).argumentCount =
        (canaryUnsafeGuardedBody false).argumentCount :=
      congrArg Body.argumentCount hEq
    exact Nat.noConfusion hArg
  · intro hVer
    have hEq : canaryUnsafeGuardedBody false = canaryNeverParamBody false := by
      injection hVer.1
    have hLoc : (canaryUnsafeGuardedBody false).locals =
        (canaryNeverParamBody false).locals :=
      congrArg Body.locals hEq
    injection hLoc with hHead
    exact MirTy.noConfusion hHead
  · intro hCrate
    exact Bool.noConfusion hCrate.2.2.2.1
  · intro hUnit
    exact Bool.noConfusion hUnit.2.2.2.2.1
  · intro hCrate
    exact Bool.noConfusion hCrate.2.2.2.2.2.1
  · intro hCrate
    have hVer :=
      hCrate.2.2.2.2.2.2.1 1 (canaryUnsafeGuardedBody false) rfl
    have hWf := hVer.2.2 [.bool false] rfl (fun h => Bool.noConfusion h)
    have hNeg : NegativeCanaryClaim
        (entryProgForBody {
          scope := .crate
          pointerWidthBits := 64
          mirProfileVersion := 1
          bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false]
        } 1)
        { args := [.bool false] } .undefined .unsupported :=
      negativeCanary_of_execFault (fuel := 2)
        (fun h => FaultKind.noConfusion h) rfl
    exact hNeg.2.2 hWf
  · intro hCrate
    exact hCrate.2.2.2.2.2.2.2
  · intro hUnit
    exact hUnit.2.2.2.2.2.2.2
  · intro hCrate
    exact VerificationScope.noConfusion hCrate.1
  · intro hUnit
    exact VerificationScope.noConfusion hUnit.1

end Anneal.MirWp
