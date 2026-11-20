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
import Anneal.NatBitwise

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-!
# Fuel-Bounded Weakest Precondition, Adequacy, and Type/Scalar Theory (`MirWp`)

This untrusted `theory/` module provides the program-logic and inversion
machinery over `Trusted.MirAst` and `Trusted.MirSemantics`:

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
2. **Width-Parametric Bitvector, Scalar, and Operator Adequacy:** Exact modular
   characterization and idempotence of `truncateBits`, totality and
   well-formedness of `truncateScalar`, all 19 Pass 1 non-vacuity and
   parameter-boundary canaries, and width/signedness-parametric operator
   totality across all six `IntWidth` variants.
3. **Lawful Type Equality and `checkVal` / `ValidEntryArgs` Inversion:**
   Complete `MirTy.beq t₁ t₂ = true ↔ t₁ = t₂` reflection, constructor-level
   `checkVal` characterizations (including fieldless enums of arbitrary variant
   count and uninhabited `MirTy.never`), arity-generic `checkArgsMatch`
   inversion, the `initState` entry equation (`initState_eq_ok`), and
   compositional `BodiesVerified` dispatch.
4. **Single-Body Execution, Productive Divergence, and Multi-Body Retagging:**
   Single-body `Reach`, `SafeFrom`, `ReturnsFrom`, `Executes`, and the
   fuel-bounded run certificate `RunsFrom` (`Runs` from the entry state),
   stated as propositions over the trusted transition
   `evalStep (bodyProg body) 0` and bridged to `execState`/`wpState`
   (`executes_iff_wpState`), `Classical.choice`-free `ProductiveInvariant`
   divergence proofs, and single-pass `retagDefId` simulation to
   `entryProgForBody p defId` for call-free bodies (`bodyCallFree`).
5. **Interprocedural Modular Call Summaries and Core Builtin Stepping:**
   Stack-composition simulation (`attachCallers`, `StackWellShaped`,
   `evalStep_attachState`, `wpOutcomeState_attachState`), reusable callee
   contracts (`CallSpec`), single-step modular call combinators (`wpCallStep`,
   `wpCallSummary`, `execCallStep`, `execCallSummary`), and `CoreBuiltin`
   stepping lemmas (`evalStep_callBuiltin`, `wpCallBuiltin`,
   `execCallBuiltin`).
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
            | ptr _ | bool _ | unit | bytes _ =>
              exact Bool.noConfusion hCheck
            | tuple fields =>
              revert hCheck
              dsimp [checkVal, Val.ty?, MirTy.beq]
              cases fields.isEmpty <;> cases Val.tys? fields <;>
                intro h <;> exact Bool.noConfusion h
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

/-! ## Part II: Type Reflection, `checkVal` / `ValidEntryArgs` Inversion, and
Operator Adequacy -/

/-- Exact boolean-to-propositional equality law for `IntWidth.beq`. -/
theorem IntWidth.beq_iff {w₁ w₂ : IntWidth} :
    IntWidth.beq w₁ w₂ = true ↔ w₁ = w₂ := by
  constructor
  · intro h
    cases w₁ <;> cases w₂ <;> first | rfl | cases h
  · intro h
    subst h
    cases w₁ <;> rfl

/-- Exact boolean-to-propositional equality law for `Mutability.beq`. -/
theorem Mutability.beq_iff {m₁ m₂ : Mutability} :
    Mutability.beq m₁ m₂ = true ↔ m₁ = m₂ := by
  constructor
  · intro h
    cases m₁ <;> cases m₂ <;> first | rfl | cases h
  · intro h
    subst h
    cases m₁ <;> rfl

/-- Exact boolean-to-propositional equality law for `natListBeq`. -/
theorem natListBeq_iff {xs ys : List Nat} :
    natListBeq xs ys = true ↔ xs = ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => cases h
    | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
        change (Nat.beq x y && natListBeq xs ys) = true at h
        cases hxy : Nat.beq x y with
        | false => rw [hxy] at h; cases h
        | true =>
          rw [hxy] at h
          rw [Nat.eq_of_beq_eq_true hxy, ih h]
  · intro h
    subst h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change (Nat.beq x x && natListBeq xs xs) = true
      rw [Nat.beq_refl, ih]
      rfl

/-- Exact boolean-to-propositional equality law for `EnumTagRepr.beq`. -/
theorem EnumTagRepr.beq_iff {r₁ r₂ : EnumTagRepr} :
    EnumTagRepr.beq r₁ r₂ = true ↔ r₁ = r₂ := by
  constructor
  · intro h
    cases r₁ with
    | zeroSized =>
      cases r₂ with
      | zeroSized => rfl
      | scalar _ _ => cases h
    | scalar w₁ s₁ =>
      cases r₂ with
      | zeroSized => cases h
      | scalar w₂ s₂ =>
        cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
          first | rfl | cases h
  · intro h
    subst h
    cases r₁ with
    | zeroSized => rfl
    | scalar w s => cases w <;> cases s <;> rfl

/-- Exact boolean-to-propositional equality law for `EnumTy.beq`. -/
theorem EnumTy.beq_iff {e₁ e₂ : EnumTy} :
    EnumTy.beq e₁ e₂ = true ↔ e₁ = e₂ := by
  constructor
  · intro h
    cases e₁ with
    | mk id₁ dw₁ ds₁ tr₁ discs₁ =>
      cases e₂ with
      | mk id₂ dw₂ ds₂ tr₂ discs₂ =>
        unfold EnumTy.beq at h
        dsimp only at h
        cases h1 : Nat.beq id₁ id₂ with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          cases h2 : IntWidth.beq dw₁ dw₂ with
          | false => rw [h2] at h; cases h
          | true =>
            rw [h2] at h
            cases h3 : (ds₁ == ds₂) with
            | false => rw [h3] at h; cases h
            | true =>
              rw [h3] at h
              cases h4 : EnumTagRepr.beq tr₁ tr₂ with
              | false => rw [h4] at h; cases h
              | true =>
                rw [h4] at h
                rw [Nat.eq_of_beq_eq_true h1, IntWidth.beq_iff.mp h2,
                    eq_of_beq h3, EnumTagRepr.beq_iff.mp h4,
                    natListBeq_iff.mp h]
  · intro h
    subst h
    cases e₁ with
    | mk id₁ dw₁ ds₁ tr₁ discs₁ =>
      unfold EnumTy.beq
      dsimp only
      rw [Nat.beq_refl, IntWidth.beq_iff.mpr rfl, beq_self_eq_true,
          EnumTagRepr.beq_iff.mpr rfl, natListBeq_iff.mpr rfl]
      rfl

mutual
  /-- Soundness direction of `MirTy.beq`. -/
  theorem mirTy_beq_sound :
      ∀ (t₁ : MirTy), ∀ (t₂ : MirTy), MirTy.beq t₁ t₂ = true → t₁ = t₂
    | .bool => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .int w₁ s₁ => fun t₂ h => by
      cases t₂ with
      | int w₂ s₂ =>
        change (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true at h
        cases hw : IntWidth.beq w₁ w₂ with
        | false => rw [hw] at h; cases h
        | true =>
          rw [hw] at h
          rw [IntWidth.beq_iff.mp hw, eq_of_beq h]
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
      | unsupported => cases h
    | .unit => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .never => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .enum ety₁ => fun t₂ h => by
      cases t₂ with
      | enum ety₂ =>
        change EnumTy.beq ety₁ ety₂ = true at h
        rw [EnumTy.beq_iff.mp h]
      | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _
      | unsupported => cases h
    | .tuple fs₁ => fun t₂ h => by
      cases t₂ with
      | tuple fs₂ =>
        change MirTy.beqList fs₁ fs₂ = true at h
        rw [mirTy_beqList_sound fs₁ fs₂ h]
      | bool | int _ _ | unit | never | enum _ | ref _ _ | rawPtr _ _
      | unsupported => cases h
    | .ref m₁ p₁ => fun t₂ h => by
      cases t₂ with
      | ref m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases hm : Mutability.beq m₁ m₂ with
        | false => rw [hm] at h; cases h
        | true =>
          rw [hm] at h
          rw [Mutability.beq_iff.mp hm, mirTy_beq_sound p₁ p₂ h]
      | bool | int _ _ | unit | never | enum _ | tuple _ | rawPtr _ _
      | unsupported => cases h
    | .rawPtr m₁ p₁ => fun t₂ h => by
      cases t₂ with
      | rawPtr m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases hm : Mutability.beq m₁ m₂ with
        | false => rw [hm] at h; cases h
        | true =>
          rw [hm] at h
          rw [Mutability.beq_iff.mp hm, mirTy_beq_sound p₁ p₂ h]
      | bool | int _ _ | unit | never | enum _ | tuple _ | ref _ _
      | unsupported => cases h
    | .unsupported => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h

  /-- Soundness direction of `MirTy.beqList`. -/
  theorem mirTy_beqList_sound :
      ∀ (fs₁ : List MirTy), ∀ (fs₂ : List MirTy),
        MirTy.beqList fs₁ fs₂ = true → fs₁ = fs₂
    | [] => fun fs₂ h => by
      cases fs₂ with
      | nil => rfl
      | cons _ _ => cases h
    | x :: xs => fun fs₂ h => by
      cases fs₂ with
      | nil => cases h
      | cons y ys =>
        change (MirTy.beq x y && MirTy.beqList xs ys) = true at h
        cases hx : MirTy.beq x y with
        | false => rw [hx] at h; cases h
        | true =>
          rw [hx] at h
          rw [mirTy_beq_sound x y hx, mirTy_beqList_sound xs ys h]
end

mutual
  /-- Reflexivity of `MirTy.beq` across the full `MirTy` grammar. -/
  theorem mirTy_beq_refl : ∀ (t : MirTy), MirTy.beq t t = true
    | .bool => rfl
    | .int w s => by
      change (IntWidth.beq w w && (s == s)) = true
      rw [IntWidth.beq_iff.mpr rfl, beq_self_eq_true]
      rfl
    | .unit => rfl
    | .never => rfl
    | .enum ety => EnumTy.beq_iff.mpr rfl
    | .tuple fs => mirTy_beqList_refl fs
    | .ref m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_iff.mpr rfl, mirTy_beq_refl p]
      rfl
    | .rawPtr m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_iff.mpr rfl, mirTy_beq_refl p]
      rfl
    | .unsupported => rfl

  /-- Reflexivity of `MirTy.beqList`. -/
  theorem mirTy_beqList_refl : ∀ (fs : List MirTy), MirTy.beqList fs fs = true
    | [] => rfl
    | x :: xs => by
      change (MirTy.beq x x && MirTy.beqList xs xs) = true
      rw [mirTy_beq_refl x, mirTy_beqList_refl xs]
      rfl
end

/-- Complete structural `beq ↔ =` law across all `MirTy` constructors. -/
theorem MirTy.beq_iff {t₁ t₂ : MirTy} : MirTy.beq t₁ t₂ = true ↔ t₁ = t₂ :=
  ⟨mirTy_beq_sound t₁ t₂, fun h => by subst h; exact mirTy_beq_refl t₁⟩

/-- Master characterization of `checkVal` via `Val.ty?`. -/
theorem checkVal_iff_ty? {v : Val} {ty : MirTy} :
    checkVal v ty = true ↔ v.ty? = some ty := by
  unfold checkVal
  cases hTy : v.ty? with
  | none =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | some vTy =>
    dsimp only
    constructor
    · intro h
      rw [MirTy.beq_iff.mp h]
    · intro h
      injection h with hEq
      subst hEq
      exact MirTy.beq_iff.mpr rfl

/-- A tuple value can only have a tuple type. -/
theorem ty?_tuple_inv {fields : List Val} {ty : MirTy}
    (h : (Val.tuple fields).ty? = some ty) :
    ∃ tys : List MirTy, Val.tys? fields = some tys ∧ ty = .tuple tys := by
  dsimp only [Val.ty?] at h
  cases hEmp : fields.isEmpty with
  | true =>
    rw [ite_bool_true hEmp] at h
    cases h
  | false =>
    rw [ite_bool_false hEmp] at h
    cases hTys : Val.tys? fields with
    | none =>
      rw [hTys] at h
      cases h
    | some tys =>
      rw [hTys] at h
      injection h with hEq
      exact ⟨tys, rfl, hEq.symm⟩

/-- Width- and signedness-parametric `checkVal` introduction for truncated
128-bit scalar payloads across all 12 integer types. -/
theorem checkVal_scalar_truncateBits (w : IntWidth) (s : Bool)
    (x : BitVec 128) :
    checkVal (.scalar ⟨w, s, truncateBits w x⟩) (.int w s) = true := by
  apply checkVal_iff_ty?.mpr
  dsimp only [Val.ty?]
  rw [scalarWf_truncateBits w s x]
  rfl

/-- `u64` specialization of `checkVal_scalar_truncateBits` for 64-bit scalar
proofs. -/
theorem checkVal_u64_truncateBits (x : BitVec 128) :
    checkVal (.scalar ⟨.i64, false, truncateBits .i64 x⟩) (.int .i64 false) =
      true :=
  checkVal_scalar_truncateBits .i64 false x

/-- Any scalar payload bounded by `intWidthModulus w` satisfies `checkVal` at
`(.int w s)`. -/
theorem checkVal_scalar_of_toNat_lt {w : IntWidth} {s : Bool} {x : BitVec 128}
    (h : x.toNat < intWidthModulus w) :
    checkVal (.scalar ⟨w, s, x⟩) (.int w s) = true := by
  rw [← truncateBits_of_toNat_lt h]
  exact checkVal_scalar_truncateBits w s x

/-- Exact inversion and introduction law for `checkVal` at integer types. -/
theorem checkVal_int_iff {v : Val} {w : IntWidth} {s : Bool} :
    checkVal v (.int w s) = true ↔
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ truncateBits w bits = bits := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | scalar sv =>
      cases sv with
      | mk sw ss bits =>
        dsimp only [Val.ty?] at h
        cases hWf : ScalarVal.wf ⟨sw, ss, bits⟩ with
        | false => rw [hWf] at h; cases h
        | true =>
          rw [hWf] at h
          change some (MirTy.int sw ss) = some (MirTy.int w s) at h
          injection h with hTy
          injection hTy with hw hs
          subst hw; subst hs
          exact ⟨bits, rfl, eq_of_beq hWf⟩
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | tuple fields =>
      let ⟨_, _, hEq⟩ := ty?_tuple_inv h
      cases hEq
    | ptr _ | bool _ | unit | bytes _ => cases h
  · intro h
    let ⟨bits, hv, hTrunc⟩ := h
    subst hv
    have hWf : ScalarVal.wf ⟨w, s, bits⟩ = true := by
      unfold ScalarVal.wf
      dsimp only
      rw [hTrunc]
      exact beq_self_eq_true bits
    dsimp only [Val.ty?]
    rw [ite_bool_true hWf]

/-- Exact inversion and introduction law for `checkVal` at `.bool`. -/
theorem checkVal_bool_iff {v : Val} :
    checkVal v .bool = true ↔ ∃ b : Bool, v = .bool b := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | bool b => exact ⟨b, rfl⟩
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | tuple fields =>
      let ⟨_, _, hEq⟩ := ty?_tuple_inv h
      cases hEq
    | ptr _ | unit | bytes _ => cases h
  · intro h
    let ⟨b, hb⟩ := h
    subst hb
    rfl

/-- Exact inversion and introduction law for `checkVal` at `.unit`. -/
theorem checkVal_unit_iff {v : Val} :
    checkVal v .unit = true ↔ v = .unit := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | unit => rfl
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | tuple fields =>
      let ⟨_, _, hEq⟩ := ty?_tuple_inv h
      cases hEq
    | ptr _ | bool _ | bytes _ => cases h
  · intro h
    subst h
    rfl

/-- No runtime `Val` inhabits `MirTy.never` (`!`). -/
theorem checkVal_never_false (v : Val) : checkVal v .never = false := by
  cases h : checkVal v .never with
  | false => rfl
  | true =>
    have hTy := checkVal_iff_ty?.mp h
    cases v with
    | scalar sv =>
      dsimp only [Val.ty?] at hTy
      cases hWf : sv.wf <;> rw [hWf] at hTy <;> cases hTy
    | enumVal ety idx =>
      dsimp only [Val.ty?] at hTy
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at hTy <;> cases hTy
    | tuple fields =>
      let ⟨_, _, hEq⟩ := ty?_tuple_inv hTy
      cases hEq
    | ptr _ | bool _ | unit | bytes _ => cases hTy

/-- Exact inversion and introduction law for `checkVal` at fieldless `.enum ety`
for arbitrary `EnumTy` and arbitrary variant count `ety.discriminants.length`.
-/
theorem checkVal_enum_iff {v : Val} {ety : EnumTy} :
    checkVal v (.enum ety) = true ↔
    enumAdmitted ety = true ∧
    ∃ idx : Fin ety.discriminants.length, v = .enumVal ety idx.val := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | enumVal ety' var =>
      dsimp only [Val.ty?] at h
      cases hAdm : enumAdmitted ety' with
      | false => rw [hAdm] at h; cases h
      | true =>
        rw [hAdm] at h
        cases hBlt : Nat.blt var ety'.discriminants.length with
        | false => rw [hBlt] at h; cases h
        | true =>
          rw [hBlt] at h
          change some (MirTy.enum ety') = some (MirTy.enum ety) at h
          injection h with hTy
          injection hTy with hEty
          subst hEty
          exact ⟨hAdm, ⟨⟨var, Nat.le_of_ble_eq_true hBlt⟩, rfl⟩⟩
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | tuple fields =>
      let ⟨_, _, hEq⟩ := ty?_tuple_inv h
      cases hEq
    | ptr _ | bool _ | unit | bytes _ => cases h
  · intro h
    let ⟨hAdm, ⟨idx, hEq⟩⟩ := h
    subst hEq
    have hBlt : Nat.blt idx.val ety.discriminants.length = true :=
      Nat.ble_eq_true_of_le idx.isLt
    dsimp only [Val.ty?]
    rw [hAdm, hBlt]
    rfl

/-- Empty-parameter inversion law for `checkArgsMatch`. -/
theorem checkArgsMatch_nil_iff {args : List Val} :
    checkArgsMatch args [] = true ↔ args = [] := by
  cases args with
  | nil =>
    constructor <;> intro _ <;> rfl
  | cons _ _ =>
    constructor <;> intro h <;> cases h

/-- Cons-parameter peeling law for `checkArgsMatch` at arbitrary arity. -/
theorem checkArgsMatch_cons_iff {args : List Val} {ty : MirTy}
    {tys : List MirTy} :
    checkArgsMatch args (ty :: tys) = true ↔
    ∃ v rest,
      args = v :: rest ∧
      checkVal v ty = true ∧
      checkArgsMatch rest tys = true := by
  cases args with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; let ⟨_, _, hEq, _, _⟩ := h; cases hEq
  | cons v rest =>
    change (checkVal v ty && checkArgsMatch rest tys) = true ↔ _
    constructor
    · intro h
      cases hv : checkVal v ty with
      | false => rw [hv] at h; cases h
      | true =>
        rw [hv] at h
        exact ⟨v, rest, rfl, hv, h⟩
    · intro h
      let ⟨v', rest', hEq, hv, hRest⟩ := h
      injection hEq with hvEq hRestEq
      subst hvEq; subst hRestEq
      rw [hv, hRest]
      rfl

/-- `checkArgsMatch` enforces equal argument and parameter-type lengths. -/
theorem checkArgsMatch_length {args : List Val} {tys : List MirTy}
    (h : checkArgsMatch args tys = true) :
    args.length = tys.length := by
  induction tys generalizing args with
  | nil =>
    rw [checkArgsMatch_nil_iff.mp h]
    rfl
  | cons ty rest ih =>
    let ⟨_, argsRest, hEq, _, hRest⟩ := checkArgsMatch_cons_iff.mp h
    subst hEq
    exact congrArg Nat.succ (ih hRest)

/-- Any parameter type list containing `MirTy.never` admits zero matching
argument lists. -/
theorem not_checkArgsMatch_of_never {args : List Val} {tys : List MirTy}
    (hMem : .never ∈ tys) :
    checkArgsMatch args tys ≠ true := by
  induction hMem generalizing args with
  | head _ =>
    intro h
    let ⟨v, _, _, hv, _⟩ := checkArgsMatch_cons_iff.mp h
    rw [checkVal_never_false v] at hv
    cases hv
  | tail _ _ ih =>
    intro h
    let ⟨_, rest, _, _, hRest⟩ := checkArgsMatch_cons_iff.mp h
    exact ih hRest

/-- Any body with an uninhabited `MirTy.never` parameter has vacuously
uninhabited `ValidEntryArgs`. -/
theorem not_validEntryArgs_of_never {body : Body} {args : List Val}
    (hMem : .never ∈ (body.locals.drop 1).take body.argumentCount) :
    ¬ ValidEntryArgs body args :=
  not_checkArgsMatch_of_never hMem

/-- Exact boolean-to-propositional equality law for `CastKind.beq`. -/
theorem CastKind.beq_iff {k₁ k₂ : CastKind} :
    CastKind.beq k₁ k₂ = true ↔ k₁ = k₂ := by
  constructor
  · intro h
    cases k₁ <;> cases k₂ <;> first | rfl | cases h
  · intro h
    subst h
    cases k₁ <;> rfl

/-! ### `Val` / `SlotVal` Bijection

`Val.toSlotVal` embeds values into slot contents and `SlotVal.toVal?` reads
them back: the two are inverse on fully initialized slots, so a slot has one
representation for each value it can hold. -/

mutual
  /-- Reading back an embedded value recovers that value. -/
  theorem toVal?_toSlotVal :
      ∀ (v : Val), (Val.toSlotVal v).toVal? = some v
    | .scalar _ => rfl
    | .ptr _ => rfl
    | .bool _ => rfl
    | .unit => rfl
    | .enumVal _ _ => rfl
    | .tuple fields => by
      dsimp only [Val.toSlotVal, SlotVal.toVal?]
      rw [toVals?_toSlotVals fields]
    | .bytes _ => rfl

  /-- Reading back a list of embedded values recovers that list. -/
  theorem toVals?_toSlotVals :
      ∀ (vs : List Val), SlotVal.toVals? (Val.toSlotVals vs) = some vs
    | [] => rfl
    | v :: vs => by
      dsimp only [Val.toSlotVals, SlotVal.toVals?]
      rw [toVal?_toSlotVal v, toVals?_toSlotVals vs]
end

mutual
  /-- A slot that reads as `v` is exactly the embedding of `v`. -/
  theorem toSlotVal_of_toVal? :
      ∀ (sv : SlotVal) (v : Val), sv.toVal? = some v → Val.toSlotVal v = sv
    | .uninit, _, h => by cases h
    | .scalar _, _, h => by injection h with h; subst h; rfl
    | .ptr _, _, h => by injection h with h; subst h; rfl
    | .bool _, _, h => by injection h with h; subst h; rfl
    | .unit, _, h => by injection h with h; subst h; rfl
    | .enumVal _ _, _, h => by injection h with h; subst h; rfl
    | .tuple fields, v, h => by
      dsimp only [SlotVal.toVal?] at h
      cases hVs : SlotVal.toVals? fields with
      | none =>
        rw [hVs] at h
        cases h
      | some vs =>
        rw [hVs] at h
        injection h with h
        subst h
        dsimp only [Val.toSlotVal]
        rw [toSlotVals_of_toVals? fields vs hVs]
    | .bytes _, _, h => by injection h with h; subst h; rfl

  /-- A slot list that reads as `vs` is exactly the embedding of `vs`. -/
  theorem toSlotVals_of_toVals? :
      ∀ (svs : List SlotVal) (vs : List Val),
        SlotVal.toVals? svs = some vs → Val.toSlotVals vs = svs
    | [], _, h => by injection h with h; subst h; rfl
    | sv :: svs, vs, h => by
      dsimp only [SlotVal.toVals?] at h
      cases hV : sv.toVal? with
      | none =>
        rw [hV] at h
        cases h
      | some v =>
        cases hVs : SlotVal.toVals? svs with
        | none =>
          rw [hV, hVs] at h
          cases h
        | some vs' =>
          rw [hV, hVs] at h
          injection h with h
          subst h
          dsimp only [Val.toSlotVals]
          rw [toSlotVal_of_toVal? sv v hV, toSlotVals_of_toVals? svs vs' hVs]
end

/-- `SlotVal.toVal?` and `Val.toSlotVal` are inverse: a slot reads as `v`
exactly when it is the embedding of `v`. -/
theorem toVal?_eq_some_iff {sv : SlotVal} {v : Val} :
    sv.toVal? = some v ↔ Val.toSlotVal v = sv :=
  ⟨toSlotVal_of_toVal? sv v, fun h => by rw [← h]; exact toVal?_toSlotVal v⟩

/-! ### Entry Initialization (`initState`) -/

/-- Single-frame running state in body `defId` (default `0`) with empty
`callerMem`. -/
def mkState (blockIdx stmtIdx : Nat) (locals : List LocalSlot)
    (defId : DefId := 0) : State :=
  {
    frames := [{
      defId := defId
      blockIdx := blockIdx
      stmtIdx := stmtIdx
      locals := locals
    }]
    callerMem := ⟨[]⟩
  }

/-- Entry initialization equation for `initState p { args := args }` when the
entry body satisfies `BodyStaticAdmitted` and `ValidEntryArgs`: the entry state
is one frame of body `p.entryDefId` at block `0` and statement `0`, holding the
locals that `initLocalsLoop` builds. -/
theorem initState_eq_ok {p : Program} {body : Body} {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args) :
    initState p { args := args } =
      .ok (mkState 0 0 (initLocalsLoop body args 0 body.locals)
        p.entryDefId) := by
  unfold BodyStaticAdmitted at h_adm
  unfold ValidEntryArgs at h_args
  unfold initState bodyEntryAdmitted mkState
  dsimp only
  rw [h_body]
  dsimp only
  rw [h_args]
  cases h1 : Nat.beq p.pointerWidthBits 64 <;>
    cases h2 : Nat.beq p.mirProfileVersion 1 <;>
    cases hid : stringBeq body.identity "" <;>
    cases h3 : body.basicBlocks.isEmpty <;>
    cases h4 : Nat.blt body.argumentCount body.locals.length <;>
    cases h5 : storageAnnotationsInBounds body <;>
    cases h6 : body.locals.all isSupportedScalarOrUnitTy <;>
    rw [h1, h2, hid, h3, h4, h5, h6] at h_adm <;>
    cases h_adm
  rfl

/-! ### Width- and Signedness-Parametric Operator Adequacy -/

theorem and_isUnchecked_false {b : Bool} {op : BinOp}
    (h : op.isUnchecked = false) : (b && op.isUnchecked) = false := by
  rw [h]
  exact Bool.and_false b

/-- Wrapping binary arithmetic (`.add`, `.sub`, `.mul`) succeeds and produces a
well-typed `Val` across all six `IntWidth`s and both signedness modes. -/
theorem evalBinOp_wrapping_arith_ok {op : BinOp}
    (hOp : op = .add ∨ op = .sub ∨ op = .mul)
    (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128) :
    ∃ out : Val,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  have hEqW : IntWidth.beq w w = true := IntWidth.beq_iff.mpr rfl
  have hEqS : (s == s) = true := beq_self_eq_true s
  have hGuard : (!(IntWidth.beq w w && (s == s))) = false := by
    rw [hEqW, hEqS]
    rfl
  have hDiv2 :
      (s && false &&
        (decodeScalar ⟨w, s, b₁⟩ == signedMinInt w &&
          decodeScalar ⟨w, s, b₂⟩ == Neg.neg 1)) = false := by
    cases s <;> rfl
  cases hOp with
  | inl hAdd =>
    subst hAdd
    let ⟨sv, lossy, hTr, hw, hs, hWf⟩ :=
      truncateScalar_ok w s
        (decodeScalar ⟨w, s, b₁⟩ + decodeScalar ⟨w, s, b₂⟩)
    refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
    · unfold evalBinOp evalArithOp
      dsimp only
      rw [ite_bool_false (rfl : BinOp.add.isShift = false)]
      rw [ite_bool_false hGuard]
      rw [ite_bool_false hDiv2]
      rw [hTr]
      dsimp only
      exact ite_bool_false (and_isUnchecked_false rfl)
    · dsimp only [Val.ty?]
      rw [hWf, hw, hs]
      rfl
  | inr hRest =>
    cases hRest with
    | inl hSub =>
      subst hSub
      let ⟨sv, lossy, hTr, hw, hs, hWf⟩ :=
        truncateScalar_ok w s
          (decodeScalar ⟨w, s, b₁⟩ - decodeScalar ⟨w, s, b₂⟩)
      refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
      · unfold evalBinOp evalArithOp
        dsimp only
        rw [ite_bool_false (rfl : BinOp.sub.isShift = false)]
        rw [ite_bool_false hGuard]
        rw [ite_bool_false hDiv2]
        rw [hTr]
        dsimp only
        exact ite_bool_false (and_isUnchecked_false rfl)
      · dsimp only [Val.ty?]
        rw [hWf, hw, hs]
        rfl
    | inr hMul =>
      subst hMul
      let ⟨sv, lossy, hTr, hw, hs, hWf⟩ :=
        truncateScalar_ok w s
          (decodeScalar ⟨w, s, b₁⟩ * decodeScalar ⟨w, s, b₂⟩)
      refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
      · unfold evalBinOp evalArithOp
        dsimp only
        rw [ite_bool_false (rfl : BinOp.mul.isShift = false)]
        rw [ite_bool_false hGuard]
        rw [ite_bool_false hDiv2]
        rw [hTr]
        dsimp only
        exact ite_bool_false (and_isUnchecked_false rfl)
      · dsimp only [Val.ty?]
        rw [hWf, hw, hs]
        rfl

/-- Explicit closed-form equation for unsigned wrapping `.add` across all six
`IntWidth` variants. -/
theorem evalBinOp_unsigned_add (w : IntWidth) (b₁ b₂ : BitVec 128) :
    evalBinOp .add (.scalar ⟨w, false, b₁⟩) (.scalar ⟨w, false, b₂⟩) =
      .ok (.scalar ⟨w, false,
        truncateBits w (bvOfInt 128
          (decodeScalar ⟨w, false, b₁⟩ + decodeScalar ⟨w, false, b₂⟩))⟩) := by
  have hGuard : (!(IntWidth.beq w w && (false == false))) = false := by
    rw [IntWidth.beq_iff.mpr rfl]
    rfl
  unfold evalBinOp evalArithOp truncateScalar
  dsimp only
  rw [ite_bool_false (rfl : BinOp.add.isShift = false)]
  rw [ite_bool_false hGuard]
  exact ite_bool_false (and_isUnchecked_false rfl)

/-- Bitwise binary operators (`.bitAnd`, `.bitOr`, `.bitXor`) succeed and
produce a well-typed `Val` across all six `IntWidth`s and both signednesses. -/
theorem evalBinOp_bitwise_ok {op : BinOp}
    (hOp : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128) :
    ∃ out : Val,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  have hEqW : IntWidth.beq w w = true := IntWidth.beq_iff.mpr rfl
  have hEqS : (s == s) = true := beq_self_eq_true s
  cases hOp with
  | inl hAnd =>
    subst hAnd
    unfold evalBinOp
    dsimp only [BinOp.isShift]
    rw [hEqW, hEqS]
    exact ⟨_, rfl,
      checkVal_scalar_truncateBits w s
        (bvAnd (truncateBits w b₁) (truncateBits w b₂))⟩
  | inr hRest =>
    cases hRest with
    | inl hOr =>
      subst hOr
      unfold evalBinOp
      dsimp only [BinOp.isShift]
      rw [hEqW, hEqS]
      exact ⟨_, rfl,
        checkVal_scalar_truncateBits w s
          (bvOr (truncateBits w b₁) (truncateBits w b₂))⟩
    | inr hXor =>
      subst hXor
      unfold evalBinOp
      dsimp only [BinOp.isShift]
      rw [hEqW, hEqS]
      exact ⟨_, rfl,
        checkVal_scalar_truncateBits w s
          (bvXor (truncateBits w b₁) (truncateBits w b₂))⟩

/-- Wrapping shifts (`.shl`, `.shr`) succeed and produce a well-typed `Val` for
any LHS `(w, s)` and any RHS `(rw, rs)`. -/
theorem evalBinOp_wrapping_shift_ok {op : BinOp}
    (hOp : op = .shl ∨ op = .shr)
    (w rw : IntWidth) (s rs : Bool) (b₁ b₂ : BitVec 128) :
    ∃ out : Val,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨rw, rs, b₂⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  cases hOp with
  | inl hShl =>
    subst hShl
    let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
      truncateScalar_ok w s
        (intShiftLeft (decodeScalar ⟨w, s, b₁⟩)
          (intEmod (decodeScalar ⟨rw, rs, b₂⟩) (Int.ofNat w.bitWidth)).toNat)
    refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
    · unfold evalBinOp evalShiftOp
      dsimp only
      rw [ite_bool_true (rfl : BinOp.shl.isShift = true)]
      rw [hTr]
      dsimp only
      exact ite_bool_false (and_isUnchecked_false rfl)
    · dsimp only [Val.ty?]
      rw [hWf, hw, hs]
      rfl
  | inr hShr =>
    subst hShr
    let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
      truncateScalar_ok w s
        (intShiftRight (decodeScalar ⟨w, s, b₁⟩)
          (intEmod (decodeScalar ⟨rw, rs, b₂⟩) (Int.ofNat w.bitWidth)).toNat)
    refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
    · unfold evalBinOp evalShiftOp
      dsimp only
      rw [ite_bool_true (rfl : BinOp.shr.isShift = true)]
      rw [hTr]
      dsimp only
      exact ite_bool_false (and_isUnchecked_false rfl)
    · dsimp only [Val.ty?]
      rw [hWf, hw, hs]
      rfl

/-- Scalar comparisons (`.eq`, `.ne`, `.lt`, `.le`, `.gt`, `.ge`) succeed and
produce a `.bool` value across all six `IntWidth`s and both signedness modes. -/
theorem evalBinOp_cmp_ok {op : BinOp}
    (hOp : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128) :
    ∃ b : Bool,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) = .ok (.bool b) :=
  by
  have hEqW : IntWidth.beq w w = true := IntWidth.beq_iff.mpr rfl
  have hEqS : (s == s) = true := beq_self_eq_true s
  cases hOp with
  | inl h =>
    subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
    rw [hEqW, hEqS]; exact ⟨_, rfl⟩
  | inr h => cases h with
    | inl h =>
      subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
      rw [hEqW, hEqS]; exact ⟨_, rfl⟩
    | inr h => cases h with
      | inl h =>
        subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
        rw [hEqW, hEqS]; exact ⟨_, rfl⟩
      | inr h => cases h with
        | inl h =>
          subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
          rw [hEqW, hEqS]; exact ⟨_, rfl⟩
        | inr h => cases h with
          | inl h =>
            subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
            rw [hEqW, hEqS]; exact ⟨_, rfl⟩
          | inr h =>
            subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
            rw [hEqW, hEqS]; exact ⟨_, rfl⟩

/-- `UnOp.not` on scalars succeeds and preserves `checkVal` across all six
`IntWidth`s and both signedness modes. -/
theorem evalUnOp_not_scalar_ok (w : IntWidth) (s : Bool) (b : BitVec 128) :
    ∃ out : Val,
      evalUnOp .not (.scalar ⟨w, s, b⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  unfold evalUnOp
  dsimp only
  let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
    truncateScalar_ok w s (intNot (decodeScalar ⟨w, s, b⟩))
  rw [hTr]
  refine ⟨.scalar sv, rfl, checkVal_iff_ty?.mpr ?_⟩
  dsimp only [Val.ty?]
  rw [hWf, hw, hs]
  rfl

/-- Signed `UnOp.neg` succeeds and preserves `checkVal` across all six
`IntWidth`s (including wrapping `-INT_MIN == INT_MIN`). -/
theorem evalUnOp_signed_neg_ok (w : IntWidth) (b : BitVec 128) :
    ∃ out : Val,
      evalUnOp .neg (.scalar ⟨w, true, b⟩) = .ok out ∧
      checkVal out (.int w true) = true := by
  unfold evalUnOp
  dsimp only
  let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
    truncateScalar_ok w true (Neg.neg (decodeScalar ⟨w, true, b⟩))
  rw [hTr]
  refine ⟨.scalar sv, rfl, checkVal_iff_ty?.mpr ?_⟩
  dsimp only [Val.ty?]
  rw [hWf, hw, hs]
  rfl

/-! ### Compositional Multi-Body Crate Dispatch -/

/-- Right-nested conjunction of `BodyVerified` obligations for a slice of
`p.bodies` starting at `DefId` index `idx`. Reduces definitionally on concrete
body lists without manual `Nat` index splitting or `Option.some.inj`.

The definition folds over the list with `List.foldr` instead of recursing by
pattern matching: equation-compiler recursion makes Lean emit an `unsafe`
`BodiesVerified._unsafe_rec` helper even for a `Prop`, and `anneal-audit`
rejects every `unsafe` constant. -/
def BodiesVerified (p : Program) (specs : Specs) (idx : Nat)
    (bs : List Body) : Prop :=
  bs.foldr
    (fun body ih curIdx =>
      BodyVerified p curIdx body (specs.safety body.identity) ∧
      ih (curIdx + 1))
    (fun _ => True)
    idx

/-- Soundness of `BodiesVerified`: discharges the universal `getElem? p.bodies`
body-verification obligation in `ProgramVerified` (`CrateTheorem` /
`UnitTheorem`). -/
theorem bodiesVerified_getElem {p : Program} {specs : Specs} :
    ∀ {idx : Nat} {bs : List Body},
      BodiesVerified p specs idx bs →
      ∀ (k : Nat) (b : Body),
        Trusted.MirSemantics.getElem? bs k = some b →
        BodyVerified p (idx + k) b (specs.safety b.identity)
  | _, [], _, _, _, hGet => by cases hGet
  | idx, b₀ :: rest, hBs, 0, b, hGet => by
    injection hGet with hEq
    subst hEq
    rw [Nat.add_zero]
    exact hBs.1
  | idx, _ :: rest, hBs, k + 1, b, hGet => by
    have hSub := bodiesVerified_getElem hBs.2 k b hGet
    have hIdx : idx + 1 + k = idx + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [← hIdx]
    exact hSub

/-! ## Part III: Single-Body Execution, WP Bridge, Productive Invariants, and
Multi-Body Retagging

This part runs one body as the single-body unit program `bodyProg body`. One
step is the trusted transition `evalStep (bodyProg body) 0`, and the entry state
on `args` is `mkState 0 0 (initLocalsLoop body args 0 body.locals)`: one frame
at `defId := 0`, block `0`, and statement `0`, holding the locals that
`initState` builds. Every notion below is a proposition over these trusted
terms. The trusted semantics has no executable code, so a definition that
computed a step or a run would have to be exempted from code generation, which
`theory/` never does. Concrete runs therefore state the fuel-bounded weakest
precondition `RunsFrom` and prove it by `rfl`. -/

/-- Single-body program wrapper for unit-level execution of `body`. -/
def bodyProg (body : Body) : Program :=
  { scope := .unit, pointerWidthBits := 64, mirProfileVersion := 1,
    bodies := [body] }

/-- Finite-step reachability in `body` under `evalStep (bodyProg body) 0`. -/
inductive Reach (body : Body) : State → State → Prop where
  | refl {state : State} : Reach body state state
  | next {start mid next : State} :
      Reach body start mid →
      evalStep (bodyProg body) 0 mid = .step next →
      Reach body start next

/-- Prefix fault-freedom of `body` starting from `start`. -/
def SafeFrom (body : Body) (start : State) : Prop :=
  ∀ state kind, Reach body start state →
    evalStep (bodyProg body) 0 state ≠ .fault kind

/-- Prefix fault-freedom of `body` from its entry state on `args`. -/
def Safe (body : Body) (args : List Val) : Prop :=
  SafeFrom body (mkState 0 0 (initLocalsLoop body args 0 body.locals))

/-- Normal return of `output` from `start` in `body`. -/
def ReturnsFrom (body : Body) (start : State) (output : Val) : Prop :=
  ∃ state, Reach body start state ∧
    evalStep (bodyProg body) 0 state = .done (.returned ⟨output, ⟨[]⟩⟩)

/-- Normal return of `output` from the entry state of `body` on `args`. -/
def Returns (body : Body) (args : List Val) (output : Val) : Prop :=
  ReturnsFrom body (mkState 0 0 (initLocalsLoop body args 0 body.locals))
    output

/-- Fuel-bounded run certificate: from `start`, `body` returns `output` within
`fuel` steps and never faults. It is the deterministic `c = 0` execution
predicate of `bodyProg body` with an exact return postcondition, so a concrete
run reduces by `rfl`. -/
abbrev RunsFrom (body : Body) (fuel : Nat) (start : State) (output : Val) :
    Prop :=
  execState (bodyProg body) fuel start
    (fun out => out = .returned ⟨output, ⟨[]⟩⟩)

/-- Fuel-bounded run certificate from the entry state of `body` on `args`. -/
abbrev Runs (body : Body) (fuel : Nat) (args : List Val) (output : Val) :
    Prop :=
  RunsFrom body fuel (mkState 0 0 (initLocalsLoop body args 0 body.locals))
    output

/-- Step-by-step normal-return certificate for `body`. Each constructor records
one rewritten transition, so long symbolic runs never accumulate an unnormalized
`whnf` term. -/
inductive Executes (body : Body) : State → Val → Prop where
  | ret {start : State} {value : Val} :
      evalStep (bodyProg body) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩) →
      Executes body start value
  | next {start next : State} {value : Val} :
      evalStep (bodyProg body) 0 start = .step next →
      Executes body next value →
      Executes body start value

/-- Exact equivalence between program-level `Reaches (bodyProg body)` and
single-body `Reach body`. -/
theorem reaches_bodyProg_iff_reach {body : Body} {s₁ s₂ : State} :
    Reaches (bodyProg body) s₁ s₂ ↔ Reach body s₁ s₂ := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hStep ih =>
      let ⟨c, hc, hEval⟩ := hStep
      subst hc
      exact .next ih hEval
  · intro h
    induction h with
    | refl => exact .refl _
    | next _ hStep ih => exact .tail ih ⟨0, rfl, hStep⟩

/-- Prepend a single transition onto a `Reach` chain. -/
theorem reach_prepend {body : Body} {start next finish : State}
    (first : evalStep (bodyProg body) 0 start = .step next)
    (rest : Reach body next finish) :
    Reach body start finish :=
  reaches_bodyProg_iff_reach.mp
    (Reaches.head ⟨0, rfl, first⟩ (reaches_bodyProg_iff_reach.mpr rest))

/-- Case-split a `Reach` chain whose start state steps to `next`. -/
theorem reach_cases {body : Body} {start next finish : State}
    (first : evalStep (bodyProg body) 0 start = .step next)
    (reached : Reach body start finish) :
    finish = start ∨ Reach body next finish := by
  induction reached with
  | refl => exact .inl rfl
  | @next before after _ transition ih =>
    cases ih with
    | inl equal =>
      subst before
      have same : StepResult.step next = .step after :=
        first.symm.trans transition
      injection same with h_eq
      subst h_eq
      exact .inr .refl
    | inr rest => exact .inr (.next rest transition)

/-- No further states are reachable after a `.done (.returned ...)` step. -/
theorem reachable_after_return {body : Body} {start finish : State}
    {value : Val}
    (returned :
      evalStep (bodyProg body) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩))
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [returned] at transition
    cases transition

/-- No further states are reachable after a `.fault` step. -/
theorem reachable_after_fault {body : Body} {start finish : State}
    {reason : FaultKind}
    (faulted : evalStep (bodyProg body) 0 start = .fault reason)
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [faulted] at transition
    cases transition

/-- A state that immediately returns is prefix-safe (`SafeFrom`). -/
theorem safeFrom_return {body : Body} {start : State} {value : Val}
    (returned :
      evalStep (bodyProg body) 0 start = .done (.returned ⟨value, ⟨[]⟩⟩)) :
    SafeFrom body start := by
  intro finish reason reached
  have same := reachable_after_return returned reached
  subst finish
  rw [returned]
  intro h
  cases h

/-- Prefix safety steps backward across a deterministic `.step` transition. -/
theorem safeFrom_next {body : Body} {start next : State}
    (first : evalStep (bodyProg body) 0 start = .step next)
    (rest : SafeFrom body next) :
    SafeFrom body start := by
  intro finish reason reached
  cases reach_cases first reached with
  | inl equal =>
    subst finish
    rw [first]
    intro h
    cases h
  | inr tail => exact rest finish reason tail

/-- Prefix safety composes backward across any finite `Reach` prefix. -/
theorem safeFrom_of_reach {body : Body} {start checkpoint : State}
    (segment : Reach body start checkpoint)
    (suffix : SafeFrom body checkpoint) :
    SafeFrom body start := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (safeFrom_next transition suffix)

/-- Bridge from fuel-bounded `wpState (bodyProg body)` to `SafeFrom`: holds even
when symbolic branches return distinct values. -/
theorem safeFrom_of_wpState {body : Body} {fuel : Nat} {start : State}
    {post : TerminalOut → Prop}
    (hWp : wpState (bodyProg body) fuel start post) :
    SafeFrom body start := by
  intro state kind hReach hFault
  let ⟨fuel', hWp'⟩ :=
    wpOutcomeState_of_reaches hWp (reaches_bodyProg_iff_reach.mpr hReach)
  cases fuel' with
  | zero => exact hWp'
  | succ _ =>
    have hBranch := hWp'.2 0 rfl
    rw [hFault] at hBranch
    exact hBranch

/-- Exact equivalence between the step-by-step `Executes` certificate and the
fuel-bounded `RunsFrom` certificate (unifying single-body certificates with the
core WP calculus). -/
theorem executes_iff_wpState {body : Body} {start : State} {value : Val} :
    Executes body start value ↔ ∃ fuel, RunsFrom body fuel start value := by
  constructor
  · intro execution
    induction execution with
    | @ret s val hRet =>
      refine ⟨1, ?_⟩
      change (match evalStep (bodyProg body) 0 s with
        | .step st' => False
        | .done out => out = .returned ⟨val, ⟨[]⟩⟩
        | .fault _ => False)
      rw [hRet]
    | @next s next val hStep _ ih =>
      let ⟨fuel, hExec⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      change (match evalStep (bodyProg body) 0 s with
        | .step st' =>
          execState (bodyProg body) fuel st'
            (fun out => out = .returned ⟨val, ⟨[]⟩⟩)
        | .done out => out = .returned ⟨val, ⟨[]⟩⟩
        | .fault _ => False)
      rw [hStep]
      exact hExec
  · intro hEx
    cases hEx with
    | intro fuel hExec =>
      induction fuel generalizing start with
      | zero => exact False.elim hExec
      | succ fuel ih =>
        change (match evalStep (bodyProg body) 0 start with
          | .step st' =>
            execState (bodyProg body) fuel st'
              (fun out => out = .returned ⟨value, ⟨[]⟩⟩)
          | .done out => out = .returned ⟨value, ⟨[]⟩⟩
          | .fault _ => False) at hExec
        cases hStep : evalStep (bodyProg body) 0 start with
        | step next =>
          rw [hStep] at hExec
          exact .next hStep (ih hExec)
        | done out =>
          rw [hStep] at hExec
          dsimp only at hExec
          subst hExec
          exact .ret hStep
        | fault k =>
          rw [hStep] at hExec
          exact False.elim hExec

/-- Prepend a `Reach` segment onto an `Executes` suffix. -/
theorem executes_prepend {body : Body} {start checkpoint : State} {value : Val}
    (segment : Reach body start checkpoint)
    (suffix : Executes body checkpoint value) :
    Executes body start value := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (.next transition suffix)

/-- Every `Executes` certificate establishes `SafeFrom` (derived directly from
`executes_iff_wpState` and `safeFrom_of_wpState`). -/
theorem executes_safe {body : Body} {start : State} {value : Val}
    (execution : Executes body start value) :
    SafeFrom body start :=
  let ⟨_, hExec⟩ := executes_iff_wpState.mp execution
  safeFrom_of_wpState (wpOutcomeState_of_execOutcomeState hExec)

/-- Every `Executes` certificate establishes `ReturnsFrom` (derived directly
from `executes_iff_wpState` and `exists_terminal_of_wpOutcomeState`). -/
theorem executes_returns {body : Body} {start : State} {value : Val}
    (execution : Executes body start value) :
    ReturnsFrom body start value := by
  let ⟨_, hExec⟩ := executes_iff_wpState.mp execution
  let ⟨sEnd, res, hReach, hTerm, hRes⟩ :=
    exists_terminal_of_wpOutcomeState
      (wpOutcomeState_of_execOutcomeState hExec)
  cases res with
  | step _ => exact False.elim hRes
  | fault _ => exact False.elim hRes
  | done out =>
    dsimp only at hRes
    subst hRes
    let ⟨c, hc, hEval⟩ := hTerm
    subst hc
    exact ⟨sEnd, reaches_bodyProg_iff_reach.mp hReach, hEval⟩

/-- Determinism of `Executes` against any `ReturnsFrom` witness (derived
directly from `wpOutcomeState_of_reaches`). -/
theorem executes_unique {body : Body} {start : State} {left right : Val}
    (execution : Executes body start left)
    (returned : ReturnsFrom body start right) :
    left = right := by
  let ⟨_, hExec⟩ := executes_iff_wpState.mp execution
  let ⟨finish, hReach, hRet⟩ := returned
  let ⟨fuel', hWp'⟩ :=
    wpOutcomeState_of_reaches (wpOutcomeState_of_execOutcomeState hExec)
      (reaches_bodyProg_iff_reach.mpr hReach)
  cases fuel' with
  | zero => exact False.elim hWp'
  | succ _ =>
    have hBranch := hWp'.2 0 rfl
    rw [hRet] at hBranch
    injection hBranch with hOut
    injection hOut with hVal _
    exact hVal.symm

/-- Every fuel-bounded run certificate yields an `Executes` certificate. -/
theorem run_executes {body : Body} {fuel : Nat} {start : State} {value : Val}
    (success : RunsFrom body fuel start value) :
    Executes body start value :=
  executes_iff_wpState.mpr ⟨fuel, success⟩

/-- A run certificate establishes prefix safety and normal return. -/
theorem run_success {body : Body} {fuel : Nat} {start : State} {value : Val}
    (success : RunsFrom body fuel start value) :
    SafeFrom body start ∧ ReturnsFrom body start value :=
  ⟨executes_safe (run_executes success),
    executes_returns (run_executes success)⟩

/-- A run certificate from the entry state establishes `Safe` and `Returns`. -/
theorem run_initial_success {body : Body} {fuel : Nat} {args : List Val}
    {value : Val} (success : Runs body fuel args value) :
    Safe body args ∧ Returns body args value :=
  run_success success

/-- A run certificate determines the only value that `body` can return. -/
theorem run_result_unique {body : Body} {fuel : Nat} {start : State}
    {left right : Val}
    (success : RunsFrom body fuel start left)
    (returned : ReturnsFrom body start right) :
    left = right :=
  executes_unique (run_executes success) returned

/-- Inductive preservation of `invariant` across all `Reach` states. -/
theorem invariant_reachable {body : Body} {start finish : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      evalStep (bodyProg body) 0 before = .step after → invariant after)
    (reached : Reach body start finish) :
    invariant finish := by
  induction reached with
  | refl => exact entry
  | next _ transition ih => exact closed _ _ ih transition

/-- Inductive invariant rule for `SafeFrom` (supporting non-terminating loops).
-/
theorem safeFrom_invariant {body : Body} {start : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      evalStep (bodyProg body) 0 before = .step after → invariant after)
    (noFault : ∀ state, invariant state → ∀ reason,
      evalStep (bodyProg body) 0 state ≠ .fault reason) :
    SafeFrom body start := by
  intro finish reason reached
  have preserved := invariant_reachable invariant entry closed reached
  exact noFault finish preserved reason

/-- A state self-loop reaches only itself. -/
theorem reachable_selfLoop {body : Body} {start finish : State}
    (loop : evalStep (bodyProg body) 0 start = .step start)
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    have equal := loop.symm.trans transition
    injection equal with h_eq
    exact h_eq.symm

/-- Any immediate self-loop is prefix-safe. -/
theorem safeFrom_selfLoop {body : Body} {start : State}
    (loop : evalStep (bodyProg body) 0 start = .step start) :
    SafeFrom body start := by
  intro finish reason reached
  have same := reachable_selfLoop loop reached
  subst finish
  rw [loop]
  intro h
  cases h

/-- A productive state invariant holds at `start`, is closed under `.step`, and
ensures every invariant state takes a `.step` transition (ruling out both
`.fault` and `.done` simultaneously). -/
def ProductiveInvariant (body : Body) (start : State)
    (invariant : State → Prop) : Prop :=
  invariant start ∧
  (∀ before after, invariant before →
    evalStep (bodyProg body) 0 before = .step after → invariant after) ∧
  (∀ state, invariant state →
    ∃ next, evalStep (bodyProg body) 0 state = .step next)

/-- Every `ProductiveInvariant` simultaneously establishes `SafeFrom` and
absence of normal `.done` termination from `start`. -/
theorem safeFrom_and_no_done_of_productiveInvariant
    {body : Body} {start : State} {invariant : State → Prop}
    (hInv : ProductiveInvariant body start invariant) :
    SafeFrom body start ∧
    ∀ s out, Reach body start s →
      evalStep (bodyProg body) 0 s ≠ .done out := by
  refine ⟨safeFrom_invariant invariant hInv.1 hInv.2.1 ?_, ?_⟩
  · intro s hs reason hFault
    let ⟨_, hStep⟩ := hInv.2.2 s hs
    rw [hStep] at hFault
    cases hFault
  · intro s out hReach hDone
    have hs := invariant_reachable invariant hInv.1 hInv.2.1 hReach
    let ⟨_, hStep⟩ := hInv.2.2 s hs
    rw [hStep] at hDone
    cases hDone

/-! ### Single-Pass Frame Retagging Between `bodyProg` and `entryProgForBody` -/

/-- True iff `bb.terminator` is not a direct crate-local `.call`. -/
def blockCallFree (bb : BasicBlock) : Bool :=
  match bb.terminator with
  | .call _ _ _ _ _ => false
  | _ => true

/-- True iff no basic block in `body` terminates with `.call`. Single-body
`bodyProg body` retagging to `entryProgForBody p defId` is sound for every
call-free body (including bodies using `.callBuiltin`). -/
def bodyCallFree (body : Body) : Bool :=
  body.basicBlocks.all blockCallFree

/-- Lookup in a call-free basic-block list yields a call-free basic block. -/
theorem blockCallFree_of_getElem? {bs : List BasicBlock} {idx : Nat}
    {bb : BasicBlock} (hAll : bs.all blockCallFree = true)
    (hGet : Trusted.MirSemantics.getElem? bs idx = some bb) :
    blockCallFree bb = true := by
  induction bs generalizing idx with
  | nil => cases hGet
  | cons b rest ih =>
    cases idx with
    | zero =>
      injection hGet with hEq
      subst hEq
      change (blockCallFree b && rest.all blockCallFree) = true at hAll
      cases hb : blockCallFree b with
      | true => rfl
      | false => rw [hb] at hAll; cases hAll
    | succ k =>
      change (blockCallFree b && rest.all blockCallFree) = true at hAll
      cases hb : blockCallFree b with
      | false => rw [hb] at hAll; cases hAll
      | true =>
        rw [hb] at hAll
        exact ih hAll hGet

/-- Rewrite the active single-frame `defId` of `s` to `d`. -/
def retagDefId (d : DefId) (s : State) : State :=
  match s.frames with
  | [f] => { s with frames := [{ f with defId := d }] }
  | _ => s

/-- True iff `s` has a single active stack frame at `defId = 0`. -/
def IsSingleFrame0 (s : State) : Prop :=
  ∃ f : FrameState, s.frames = [f] ∧ f.defId = 0

/-- Every `mkState` at the default `defId` is a single frame at `defId = 0`. -/
theorem isSingleFrame0_mkState (blockIdx stmtIdx : Nat)
    (locals : List LocalSlot) :
    IsSingleFrame0 (mkState blockIdx stmtIdx locals) :=
  ⟨_, rfl, rfl⟩

/-- Single-pass `evalStatement` frame invariant and `retagDefId` commutation. -/
theorem evalStatement_frame_retag (body : Body) (defId : DefId)
    (f : FrameState) (cm : CallerMemory) (stmt : StatementKind)
    (h_id : f.defId = 0) :
    (∀ s', evalStatement body f [] cm stmt = .step s' → IsSingleFrame0 s') ∧
    evalStatement body { f with defId := defId } [] cm stmt =
      match evalStatement body f [] cm stmt with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  unfold evalStatement retagDefId
  cases stmt with
  | nop =>
    refine ⟨?_, rfl⟩
    intro s' hStep
    injection hStep with hEq; subst hEq
    exact ⟨_, rfl, h_id⟩
  | storageLive lid =>
    dsimp only
    cases Trusted.MirSemantics.getElem? body.locals lid with
    | none => exact ⟨(fun _ h => by cases h), rfl⟩
    | some ty =>
      dsimp only
      cases setElem? f.locals lid (liveUninitSlot ty) with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some l' =>
        refine ⟨?_, rfl⟩
        intro s' hStep
        injection hStep with hEq; subst hEq
        exact ⟨_, rfl, h_id⟩
  | storageDead lid =>
    dsimp only
    cases Nat.beq lid 0 with
    | true => exact ⟨(fun _ h => by cases h), rfl⟩
    | false =>
      cases setElem? f.locals lid .dead with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some l' =>
        refine ⟨?_, rfl⟩
        intro s' hStep
        injection hStep with hEq; subst hEq
        exact ⟨_, rfl, h_id⟩
  | assign dst rv =>
    dsimp only
    cases Trusted.MirSemantics.getElem? body.locals dst.localId with
    | none => exact ⟨(fun _ h => by cases h), rfl⟩
    | some localTy =>
      dsimp only
      cases projectTy? localTy dst.projection with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some dstTy =>
        dsimp only
        cases assignHasUnsupportedOverlap dst dstTy rv with
        | true => exact ⟨(fun _ h => by cases h), rfl⟩
        | false =>
          cases rv with
          | aggregateTuple ops =>
            dsimp only
            cases writeAggregateTuple body.locals f.locals dst dstTy ops with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok l' =>
              refine ⟨?_, rfl⟩
              intro s' hStep
              injection hStep with hEq; subst hEq
              exact ⟨_, rfl, h_id⟩
          | use opnd =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy (.use opnd) with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dstTy pair.1 with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, rfl, h_id⟩
          | binaryOp op lhs rhs =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy (.binaryOp op lhs rhs)
              with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dstTy pair.1 with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, rfl, h_id⟩
          | unaryOp op opnd =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy (.unaryOp op opnd) with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dstTy pair.1 with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, rfl, h_id⟩
          | discriminant p =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy (.discriminant p) with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dstTy pair.1 with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, rfl, h_id⟩
          | ref m p =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy (.ref m p) with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dstTy pair.1 with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, rfl, h_id⟩
          | addressOf m p =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy (.addressOf m p) with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dstTy pair.1 with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, rfl, h_id⟩
          | cast kind opnd castTy =>
            dsimp only
            cases evalRvalue body.locals f.locals dstTy
                (.cast kind opnd castTy) with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dstTy pair.1 with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep
                injection hStep with hEq; subst hEq
                exact ⟨_, rfl, h_id⟩
          | unsupported => exact ⟨(fun _ h => by cases h), rfl⟩
  | unsupported => exact ⟨(fun _ h => by cases h), rfl⟩

/-- Single-pass `evalTerminator` frame invariant and `retagDefId` commutation
for call-free blocks (`blockCallFree bb = true`). -/
theorem evalTerminator_frame_retag (p : Program) (body : Body)
    (bb : BasicBlock) (defId : DefId) (f : FrameState) (cm : CallerMemory)
    (h_id : f.defId = 0) (h_cf : blockCallFree bb = true) :
    (∀ s', evalTerminator (bodyProg body) body bb f [] cm = .step s' →
      IsSingleFrame0 s') ∧
    evalTerminator p body bb { f with defId := defId } [] cm =
      match evalTerminator (bodyProg body) body bb f [] cm with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  unfold evalTerminator jumpToBlock unwindFrame retagDefId
  unfold blockCallFree at h_cf
  cases hT : bb.terminator with
  | goto target =>
    refine ⟨?_, rfl⟩
    intro s' hStep
    injection hStep with hEq; subst hEq
    exact ⟨_, rfl, h_id⟩
  | return_ =>
    dsimp only
    cases bb.cleanup with
    | true => exact ⟨(fun _ h => by cases h), rfl⟩
    | false =>
      cases Trusted.MirSemantics.getElem? f.locals 0 with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some slot =>
        cases slot with
        | dead => exact ⟨(fun _ h => by cases h), rfl⟩
        | live sv =>
          dsimp only
          cases sv.toVal? with
          | none => exact ⟨(fun _ h => by cases h), rfl⟩
          | some _ =>
            cases f.returnCont <;> exact ⟨(fun _ h => by cases h), rfl⟩
  | unreachable => exact ⟨(fun _ h => by cases h), rfl⟩
  | switchInt discr targets =>
    dsimp only
    cases evalPrimitiveOperand body.locals f.locals discr with
    | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
    | ok pair =>
      dsimp only
      cases pair.1 with
      | scalar sv =>
        dsimp only
        cases evalSwitchBranches sv.width sv.bits targets.otherwise
            targets.branches with
        | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
        | ok tgt =>
          refine ⟨?_, rfl⟩
          intro s' hStep
          injection hStep with hEq; subst hEq
          exact ⟨_, rfl, h_id⟩
      | bool b =>
        dsimp only
        cases evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
        | ok tgt =>
          refine ⟨?_, rfl⟩
          intro s' hStep
          injection hStep with hEq; subst hEq
          exact ⟨_, rfl, h_id⟩
      | ptr _ | unit | tuple _ | bytes _ | enumVal _ _ =>
        exact ⟨(fun _ h => by cases h), rfl⟩
  | assert cond expected msg target unwind =>
    dsimp only
    cases evalPrimitiveOperand body.locals f.locals cond with
    | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
    | ok pair =>
      dsimp only
      cases pair.1 with
      | bool b =>
        dsimp only
        cases (expected == b) with
        | true =>
          refine ⟨?_, rfl⟩
          intro s' hStep
          injection hStep with hEq; subst hEq
          exact ⟨_, rfl, h_id⟩
        | false =>
          cases (!isOperandFreeAssertKind msg) with
          | true => exact ⟨(fun _ h => by cases h), rfl⟩
          | false =>
            cases unwind with
            | cleanup block =>
              refine ⟨?_, rfl⟩
              intro s' hStep
              injection hStep with hEq; subst hEq
              exact ⟨_, rfl, h_id⟩
            | continue_ =>
              cases f.returnCont <;> exact ⟨(fun _ h => by cases h), rfl⟩
            | unreachable | terminate =>
              exact ⟨(fun _ h => by cases h), rfl⟩
      | scalar _ | ptr _ | unit | tuple _ | bytes _ | enumVal _ _ =>
        exact ⟨(fun _ h => by cases h), rfl⟩
  | unwindResume =>
    dsimp only
    cases bb.cleanup with
    | false => exact ⟨(fun _ h => by cases h), rfl⟩
    | true =>
      cases f.returnCont <;> exact ⟨(fun _ h => by cases h), rfl⟩
  | call _ _ _ _ _ =>
    rw [hT] at h_cf
    cases h_cf
  | callBuiltin builtin args dst target _ =>
    dsimp only
    cases anyMoveOperandMayOverlapPlace dst args with
    | true => exact ⟨(fun _ h => by cases h), rfl⟩
    | false =>
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some localTy =>
        dsimp only
        cases projectTy? localTy dst.projection with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some dstTy =>
          dsimp only
          cases evalCallArgs body.locals f.locals args with
          | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
          | ok pair =>
            dsimp only
            cases readPrimitiveArgs pair.1 with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok argVals =>
              dsimp only
              cases evalCoreBuiltin builtin argVals with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok resVal =>
                dsimp only
                cases writePlace pair.2 dst dstTy resVal with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  cases target with
                  | none => exact ⟨(fun _ h => by cases h), rfl⟩
                  | some nextBb =>
                    refine ⟨?_, rfl⟩
                    intro s' hStep
                    injection hStep with hEq; subst hEq
                    exact ⟨_, rfl, h_id⟩
  | unsupported =>
    exact ⟨(fun _ h => by cases h), rfl⟩

/-- Combined single-step `IsSingleFrame0` preservation and `retagDefId`
simulation between `evalStep (bodyProg body) 0` and
`evalStep (entryProgForBody p defId) 0` for call-free bodies. -/
theorem evalStep_entryProg_frame {p : Program} {defId : DefId} {body : Body}
    {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_f0 : IsSingleFrame0 s)
    (h_callFree : bodyCallFree body = true := by rfl) :
    (∀ s', evalStep (bodyProg body) 0 s = .step s' → IsSingleFrame0 s') ∧
    evalStep (entryProgForBody p defId) 0 (retagDefId defId s) =
      match evalStep (bodyProg body) 0 s with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  let ⟨f, hf, h_id⟩ := h_f0
  cases s with
  | mk frames cm =>
    dsimp only at hf
    subst hf
    unfold bodyProg evalStep retagDefId entryProgForBody
    dsimp only
    rw [h_body, h_id]
    dsimp only [Trusted.MirSemantics.getElem?]
    cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none => exact ⟨(fun _ h => by cases h), rfl⟩
    | some bb =>
      dsimp only
      cases Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        exact evalStatement_frame_retag body defId f cm stmt h_id
      | none =>
        dsimp only
        cases Nat.beq f.stmtIdx bb.statements.length with
        | false => exact ⟨(fun _ h => by cases h), rfl⟩
        | true =>
          exact evalTerminator_frame_retag (entryProgForBody p defId) body bb
            defId f cm h_id (blockCallFree_of_getElem? h_callFree hBb)

/-- `IsSingleFrame0` is preserved by a single-body step in a call-free body. -/
theorem isSingleFrame0_of_step {body : Body} {s s' : State}
    (h_f0 : IsSingleFrame0 s)
    (h_step : evalStep (bodyProg body) 0 s = .step s')
    (h_callFree : bodyCallFree body = true := by rfl) :
    IsSingleFrame0 s' :=
  (evalStep_entryProg_frame (p := bodyProg body) (defId := 0) rfl h_f0
    h_callFree).1 s' h_step

/-- Every state reachable from a single-frame `defId = 0` state in a call-free
body is again a single frame at `defId = 0`. -/
theorem isSingleFrame0_of_reach {body : Body} {start s : State}
    (h_start : IsSingleFrame0 start)
    (h_reach : Reach body start s)
    (h_callFree : bodyCallFree body = true := by rfl) :
    IsSingleFrame0 s := by
  induction h_reach with
  | refl => exact h_start
  | next _ h_step ih => exact isSingleFrame0_of_step ih h_step h_callFree

/-- `evalStep (entryProgForBody p defId) 0` commutes with `retagDefId defId` on
single-frame `defId = 0` states of a call-free body. -/
theorem evalStep_retagDefId {p : Program} {defId : DefId} {body : Body}
    {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_f0 : IsSingleFrame0 s)
    (h_callFree : bodyCallFree body = true := by rfl) :
    evalStep (entryProgForBody p defId) 0 (retagDefId defId s) =
      match evalStep (bodyProg body) 0 s with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k :=
  (evalStep_entryProg_frame h_body h_f0 h_callFree).2

/-- Exact equivalence of `execOutcomeState` across `retagDefId` between
`entryProgForBody p defId` and `bodyProg body` for a call-free body. -/
theorem execOutcomeState_entryProg_iff {p : Program} {defId : DefId}
    {body : Body} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_callFree : bodyCallFree body = true := by rfl) :
    ∀ {fuel : Nat} {s : State},
      IsSingleFrame0 s →
      (execOutcomeState (entryProgForBody p defId) onDone onFault fuel
        (retagDefId defId s) ↔
       execOutcomeState (bodyProg body) onDone onFault fuel s)
  | 0, _, _ => Iff.rfl
  | fuel + 1, s, h_f0 => by
    have hFrame := evalStep_entryProg_frame h_body h_f0 h_callFree
    change (match evalStep (entryProgForBody p defId) 0
          (retagDefId defId s) with
        | .step st' =>
          execOutcomeState (entryProgForBody p defId) onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k) ↔
      (match evalStep (bodyProg body) 0 s with
        | .step st' => execOutcomeState (bodyProg body) onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k)
    rw [hFrame.2]
    cases hSt : evalStep (bodyProg body) 0 s with
    | step next =>
      exact execOutcomeState_entryProg_iff h_body h_callFree (hFrame.1 next hSt)
    | done out => exact Iff.rfl
    | fault k => exact Iff.rfl

/-- Exact equivalence of `wpOutcomeState` across `retagDefId` between
`entryProgForBody p defId` and `bodyProg body` for a call-free body. -/
theorem wpOutcomeState_entryProg_iff {p : Program} {defId : DefId}
    {body : Body} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    {fuel : Nat} {s : State} (h_f0 : IsSingleFrame0 s)
    (h_callFree : bodyCallFree body = true := by rfl) :
    wpOutcomeState (entryProgForBody p defId) onDone onFault fuel
      (retagDefId defId s) ↔
    wpOutcomeState (bodyProg body) onDone onFault fuel s :=
  wpOutcomeState_iff_execOutcomeState.trans
    ((execOutcomeState_entryProg_iff h_body h_callFree h_f0).trans
      wpOutcomeState_iff_execOutcomeState.symm)

/-- Entry initialization equation specialized to `entryProgForBody p defId`,
stated as the retagged entry state of `bodyProg body`. -/
theorem initState_entryProgForBody {p : Program} {defId : DefId} {body : Body}
    {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args) :
    initState (entryProgForBody p defId) { args := args } =
      .ok (retagDefId defId
        (mkState 0 0 (initLocalsLoop body args 0 body.locals))) :=
  initState_eq_ok (p := entryProgForBody p defId) h_body h_adm h_args

/-- Project a state of `entryProgForBody p defId` reachable from a retagged
single-frame state back to `Reach body` via `retagDefId` (call-free `body`). -/
theorem reach_of_reaches_entryProg {p : Program} {defId : DefId} {body : Body}
    {start s_d : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_start : IsSingleFrame0 start)
    (h_reaches :
      Reaches (entryProgForBody p defId) (retagDefId defId start) s_d)
    (h_callFree : bodyCallFree body = true := by rfl) :
    ∃ s : State, s_d = retagDefId defId s ∧ Reach body start s := by
  induction h_reaches with
  | refl => exact ⟨start, rfl, .refl⟩
  | tail _ h_step ih =>
    let ⟨s, hs, h_reach_s⟩ := ih
    let ⟨c, hc, h_eval⟩ := h_step
    subst hc
    subst hs
    have h_f0 := isSingleFrame0_of_reach h_start h_reach_s h_callFree
    rw [evalStep_retagDefId h_body h_f0 h_callFree] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step next =>
      rw [h_st] at h_eval
      injection h_eval with h_eq
      exact ⟨next, h_eq.symm, .next h_reach_s h_st⟩
    | done _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval

/-- Lift a single-body `Reach` trace from a single-frame state to
`Reaches (entryProgForBody p defId)` via `retagDefId` (call-free `body`). -/
theorem reaches_entryProg_of_reach {p : Program} {defId : DefId} {body : Body}
    {start s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_start : IsSingleFrame0 start)
    (h_reach : Reach body start s)
    (h_callFree : bodyCallFree body = true := by rfl) :
    Reaches (entryProgForBody p defId) (retagDefId defId start)
      (retagDefId defId s) := by
  induction h_reach with
  | refl => exact .refl _
  | next h_prev h_st ih =>
    have h_f0 := isSingleFrame0_of_reach h_start h_prev h_callFree
    refine .tail ih ⟨0, rfl, ?_⟩
    rw [evalStep_retagDefId h_body h_f0 h_callFree, h_st]

/-- Establish per-invocation `WellFormed (entryProgForBody p defId)` from
single-body `Safe body args` for a call-free body. -/
theorem wellFormed_entryProg_of_safe {p : Program} {defId : DefId}
    {body : Body} {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_safe : Safe body args)
    (h_callFree : bodyCallFree body = true := by rfl) :
    WellFormed (entryProgForBody p defId) { args := args } := by
  have h_init := initState_entryProgForBody h_body h_adm h_args
  refine ⟨⟨_, h_init, ?_⟩, ?_⟩
  · intro _ _
    exact ⟨0, rfl⟩
  · intro k h_fault
    unfold ReachesResult at h_fault
    rw [h_init] at h_fault
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_fault
    subst hc
    let ⟨s, hs, h_reach_s⟩ :=
      reach_of_reaches_entryProg h_body (isSingleFrame0_mkState 0 0 _)
        h_reaches h_callFree
    subst hs
    have h_f0 :=
      isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _)
        h_reach_s h_callFree
    rw [evalStep_retagDefId h_body h_f0 h_callFree] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | done _ => rw [h_st] at h_eval; cases h_eval
    | fault k' =>
      rw [h_st] at h_eval
      injection h_eval with h_k
      subst h_k
      exact h_safe s k' h_reach_s h_st

/-- Establish `BodyVerified p defId body safetyPre` from single-body `Safe` for
a call-free body. -/
theorem bodyVerified_of_safe {p : Program} {defId : DefId} {body : Body}
    {safetyPre : List Val → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_safe : ∀ args : List Val,
      ValidEntryArgs body args →
      (body.isUnsafe = true → safetyPre args) →
      Safe body args)
    (h_callFree : bodyCallFree body = true := by rfl) :
    BodyVerified p defId body safetyPre :=
  ⟨h_body, h_adm, fun args h_args h_req =>
    wellFormed_entryProg_of_safe h_body h_adm h_args (h_safe args h_args h_req)
      h_callFree⟩

/-- Establish `Behavior (entryProgForBody p defId)` from single-body `Returns`
for a call-free body. -/
theorem behavior_of_returns {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_ret : Returns body args ret)
    (h_callFree : bodyCallFree body = true := by rfl) :
    Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩) := by
  let ⟨s, h_reach, h_done⟩ := h_ret
  unfold Behavior ReachesResult
  rw [initState_entryProgForBody h_body h_adm h_args]
  refine ⟨retagDefId defId s,
    reaches_entryProg_of_reach h_body (isSingleFrame0_mkState 0 0 _) h_reach
      h_callFree,
    0, rfl, ?_⟩
  have h_f0 :=
    isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach h_callFree
  rw [evalStep_retagDefId h_body h_f0 h_callFree, h_done]

/-- Invert `initState (entryProgForBody p defId) { args := args } = .ok s₀` into
`ValidEntryArgs body args` and the retagged entry state of `body` on `args`. -/
theorem initState_entryProgForBody_ok {p : Program} {defId : DefId}
    {body : Body} {args : List Val} {s₀ : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_init : initState (entryProgForBody p defId) { args := args } = .ok s₀) :
    ValidEntryArgs body args ∧
      s₀ = retagDefId defId
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) := by
  unfold initState bodyEntryAdmitted entryProgForBody at h_init
  unfold ValidEntryArgs mkState retagDefId
  dsimp only at h_init
  dsimp only
  rw [h_body] at h_init
  dsimp only at h_init
  cases h1 : Nat.beq p.pointerWidthBits 64 <;>
    cases h2 : Nat.beq p.mirProfileVersion 1 <;>
    cases h3 : body.basicBlocks.isEmpty <;>
    cases h4 : Nat.blt body.argumentCount body.locals.length <;>
    cases h5 : storageAnnotationsInBounds body <;>
    cases h6 : body.locals.all isSupportedScalarOrUnitTy <;>
    cases h7 : checkArgsMatch args
      ((body.locals.drop 1).take body.argumentCount) <;>
    rw [h1, h2, h3, h4, h5, h6, h7] at h_init <;>
    cases h_init
  exact ⟨rfl, rfl⟩

/-- Invert `Behavior (entryProgForBody p defId)` into `ValidEntryArgs` and
single-body `Returns` for a call-free body. -/
theorem returns_of_behavior {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_beh : Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩))
    (h_callFree : bodyCallFree body = true := by rfl) :
    ValidEntryArgs body args ∧ Returns body args ret := by
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState (entryProgForBody p defId) { args := args } with
  | error _ => rw [h_init] at h_beh; cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨h_args, hs₀⟩ := initState_entryProgForBody_ok h_body h_init
    subst hs₀
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_beh
    subst hc
    let ⟨s, hs, h_reach⟩ :=
      reach_of_reaches_entryProg h_body (isSingleFrame0_mkState 0 0 _)
        h_reaches h_callFree
    subst hs
    have h_f0 :=
      isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach h_callFree
    rw [evalStep_retagDefId h_body h_f0 h_callFree] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval
    | done out =>
      rw [h_st] at h_eval
      injection h_eval with h_out
      subst h_out
      exact ⟨h_args, s, h_reach, h_st⟩

/-- Refute `Behavior (entryProgForBody p defId) { args := args } out` when no
state reachable from the entry state of call-free `body` on `args` steps to
`.done out`. -/
theorem not_behavior_of_no_done {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {out : TerminalOut}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_no_done : ∀ s,
      Reach body (mkState 0 0 (initLocalsLoop body args 0 body.locals)) s →
      evalStep (bodyProg body) 0 s ≠ .done out)
    (h_callFree : bodyCallFree body = true := by rfl) :
    ¬ Behavior (entryProgForBody p defId) { args := args } out := by
  intro h_beh
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState (entryProgForBody p defId) { args := args } with
  | error _ => rw [h_init] at h_beh; cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨_, hs₀⟩ := initState_entryProgForBody_ok h_body h_init
    subst hs₀
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_beh
    subst hc
    let ⟨s, hs, h_reach⟩ :=
      reach_of_reaches_entryProg h_body (isSingleFrame0_mkState 0 0 _)
        h_reaches h_callFree
    subst hs
    have h_f0 :=
      isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) h_reach h_callFree
    rw [evalStep_retagDefId h_body h_f0 h_callFree] at h_eval
    cases h_st : evalStep (bodyProg body) 0 s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval
    | done out' =>
      rw [h_st] at h_eval
      injection h_eval with h_out
      subst h_out
      exact h_no_done s h_reach h_st

/-- Constructively establish `Diverges (entryProgForBody p defId)` and absence
of normal `Behavior` from a single-body `ProductiveInvariant` at the entry
state of a call-free body, with zero `Classical.choice` axioms: the infinite
trace iterates the deterministic successor selector `next`. -/
theorem diverges_of_productiveInvariant {p : Program} {defId : DefId}
    {body : Body} {args : List Val} {invariant : State → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_inv : ProductiveInvariant body
      (mkState 0 0 (initLocalsLoop body args 0 body.locals)) invariant)
    (h_callFree : bodyCallFree body = true := by rfl) :
    Diverges (entryProgForBody p defId) { args := args } ∧
    ∀ out, ¬ Behavior (entryProgForBody p defId) { args := args } out := by
  let next : State → State := fun s =>
    match evalStep (bodyProg body) 0 s with
    | .step s' => s'
    | _ => s
  have hNext : ∀ s s', evalStep (bodyProg body) 0 s = .step s' →
      evalStep (bodyProg body) 0 s = .step (next s) := by
    intro s s' hs
    change evalStep (bodyProg body) 0 s =
      .step (match evalStep (bodyProg body) 0 s with
        | .step s' => s'
        | _ => s)
    rw [hs]
  let iter : Nat → State :=
    Nat.rec (mkState 0 0 (initLocalsLoop body args 0 body.locals))
      (fun _ s => next s)
  have hIter : ∀ n : Nat,
      invariant (iter n) ∧
      Reach body (mkState 0 0 (initLocalsLoop body args 0 body.locals))
        (iter n) ∧
      evalStep (bodyProg body) 0 (iter n) = .step (iter (n + 1)) := by
    intro n
    induction n with
    | zero =>
      let ⟨s', hs'⟩ := h_inv.2.2 _ h_inv.1
      exact ⟨h_inv.1, .refl, hNext _ s' hs'⟩
    | succ n ih =>
      have hNextInv : invariant (iter (n + 1)) := h_inv.2.1 _ _ ih.1 ih.2.2
      let ⟨s'', hs''⟩ := h_inv.2.2 (iter (n + 1)) hNextInv
      exact ⟨hNextInv, .next ih.2.1 ih.2.2, hNext _ s'' hs''⟩
  refine ⟨?_, fun out => not_behavior_of_no_done h_body
    (fun s hReach =>
      (safeFrom_and_no_done_of_productiveInvariant h_inv).2 s out hReach)
    h_callFree⟩
  refine ⟨_, initState_entryProgForBody h_body h_adm h_args,
    fun n => retagDefId defId (iter n), rfl, ?_⟩
  intro n
  refine ⟨0, rfl, ?_⟩
  have hStepN := hIter n
  have hF0 :=
    isSingleFrame0_of_reach (isSingleFrame0_mkState 0 0 _) hStepN.2.1 h_callFree
  rw [evalStep_retagDefId h_body hF0 h_callFree, hStepN.2.2]

/-! ## Part IV: 64-Bit Scalar / Bitwise Assignment Steps and Range Indexing -/

private theorem nat_mod_mod_mul_left (n a b : Nat) :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a := by
  have hDiv : Nat.mod n (a * b) + a * (b * Nat.div n (a * b)) = n := by
    rw [← Nat.mul_assoc]
    exact Nat.mod_add_div n (a * b)
  exact (Nat.add_mul_mod_self_left (Nat.mod n (a * b)) a
    (b * Nat.div n (a * b))).symm.trans (congrArg (fun k => Nat.mod k a) hDiv)

private theorem nat_bitwise_lt_two_pow (f : Bool → Bool → Bool) :
    ∀ (n a b : Nat), a < Nat.pow 2 n → b < Nat.pow 2 n →
      Nat.bitwise f a b < Nat.pow 2 n :=
  Anneal.NatBitwise.lt_two_pow f

/-- Zero-extending a 64-bit bitvector to 128 bits preserves `.toNat`. -/
theorem bvZeroExtend_128_toNat (w : BitVec 64) :
    (bvZeroExtend 128 w).toNat = w.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by decide))

/-- Truncating `BitVec.ofNat 128 n` to `.i64` agrees with zero-extending
`BitVec.ofNat 64 n`. -/
theorem truncateBits_i64_ofNat (n : Nat) :
    truncateBits .i64 (BitVec.ofNat 128 n) =
      bvZeroExtend 128 (BitVec.ofNat 64 n) := by
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, bvZeroExtend_128_toNat]
  have hPow : Nat.pow 2 128 = Nat.pow 2 64 * Nat.pow 2 64 := by decide
  change Nat.mod (Nat.mod n (Nat.pow 2 128)) (Nat.pow 2 64) =
    Nat.mod n (Nat.pow 2 64)
  rw [hPow]
  exact nat_mod_mod_mul_left n (Nat.pow 2 64) (Nat.pow 2 64)

/-- Zero-extending a 64-bit bitvector to 128 bits is fixed by `truncateBits
.i64`. -/
theorem truncateBits_i64_bvZeroExtend (w : BitVec 64) :
    truncateBits .i64 (bvZeroExtend 128 w) = bvZeroExtend 128 w :=
  truncateBits_of_toNat_lt (by
    rw [bvZeroExtend_128_toNat]
    exact w.isLt)

/-- Zero-extended 64-bit scalars satisfy `checkVal` at `(.int .i64 false)`. -/
theorem checkVal_u64_bvZeroExtend (w : BitVec 64) :
    checkVal (.scalar ⟨.i64, false, bvZeroExtend 128 w⟩) (.int .i64 false) =
      true := by
  rw [← truncateBits_i64_bvZeroExtend w]
  exact checkVal_u64_truncateBits (bvZeroExtend 128 w)

/-- Semantic result value of 64-bit unsigned bitwise AND. -/
noncomputable def u64BitAndVal (x y : BitVec 64) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvAnd (truncateBits .i64 (bvZeroExtend 128 x))
      (truncateBits .i64 (bvZeroExtend 128 y)))⟩

/-- Semantic result value of 64-bit unsigned bitwise OR. -/
noncomputable def u64BitOrVal (x y : BitVec 64) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvOr (truncateBits .i64 (bvZeroExtend 128 x))
      (truncateBits .i64 (bvZeroExtend 128 y)))⟩

/-- Semantic result value of 64-bit unsigned left shift by `k`. -/
noncomputable def u64ShlVal (x : BitVec 64) (k : Nat) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvOfInt 128
      (.ofNat (Nat.shiftLeft
        (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩

/-- Semantic result value of 64-bit unsigned logical right shift by `k`. -/
noncomputable def u64ShrVal (x : BitVec 64) (k : Nat) : Val :=
  .scalar ⟨.i64, false,
    truncateBits .i64 (bvOfInt 128
      (.ofNat (Nat.shiftRight
        (truncateBits .i64 (bvZeroExtend 128 x)).toNat k)))⟩

private theorem truncateBits_i64_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    truncateBits .i64 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  apply truncateBits_of_toNat_lt
  change Nat.mod n (Nat.pow 2 128) < Nat.pow 2 IntWidth.i64.bitWidth
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-- Closed form for `u64BitAndVal x y` over `Nat.land x.toNat y.toNat`. -/
theorem u64BitAndVal_eq (x y : BitVec 64) :
    u64BitAndVal x y =
      .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.land x.toNat y.toNat)⟩ := by
  unfold u64BitAndVal bvAnd
  rw [truncateBits_i64_bvZeroExtend x, truncateBits_i64_bvZeroExtend y,
      bvZeroExtend_128_toNat x, bvZeroExtend_128_toNat y]
  exact congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
    (truncateBits_i64_ofNat_lt
      (nat_bitwise_lt_two_pow and 64 x.toNat y.toNat x.isLt y.isLt))

/-- Closed form for `u64BitOrVal x y` over `Nat.lor x.toNat y.toNat`. -/
theorem u64BitOrVal_eq (x y : BitVec 64) :
    u64BitOrVal x y =
      .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)⟩ := by
  unfold u64BitOrVal bvOr
  rw [truncateBits_i64_bvZeroExtend x, truncateBits_i64_bvZeroExtend y,
      bvZeroExtend_128_toNat x, bvZeroExtend_128_toNat y]
  exact congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
    (truncateBits_i64_ofNat_lt
      (nat_bitwise_lt_two_pow or 64 x.toNat y.toNat x.isLt y.isLt))

/-- Closed form for `u64ShlVal x k` over zero-extended `BitVec.ofNat 64`. -/
theorem u64ShlVal_eq (x : BitVec 64) (k : Nat) :
    u64ShlVal x k =
      .scalar ⟨.i64, false,
        bvZeroExtend 128 (BitVec.ofNat 64 (Nat.shiftLeft x.toNat k))⟩ := by
  unfold u64ShlVal bvOfInt intEmod
  rw [truncateBits_i64_bvZeroExtend x, bvZeroExtend_128_toNat x]
  dsimp only [Int.natAbs, Int.toNat]
  rw [truncateBits_i64_ofNat]
  have hMod :
      BitVec.ofNat 64
        (Nat.mod (Nat.shiftLeft x.toNat k) (Nat.pow 2 128)) =
      BitVec.ofNat 64 (Nat.shiftLeft x.toNat k) := by
    apply bitVec_eq_of_toNat_eq
    have hPow : Nat.pow 2 128 = Nat.pow 2 64 * Nat.pow 2 64 := by decide
    change Nat.mod (Nat.mod (Nat.shiftLeft x.toNat k) (Nat.pow 2 128))
        (Nat.pow 2 64) =
      Nat.mod (Nat.shiftLeft x.toNat k) (Nat.pow 2 64)
    rw [hPow]
    exact nat_mod_mod_mul_left _ (Nat.pow 2 64) (Nat.pow 2 64)
  rw [hMod]

/-- Closed form for `u64ShrVal x k` over `Nat.shiftRight x.toNat k`. -/
theorem u64ShrVal_eq (x : BitVec 64) (k : Nat) :
    u64ShrVal x k =
      .scalar ⟨.i64, false,
        BitVec.ofNat 128 (Nat.shiftRight x.toNat k)⟩ := by
  unfold u64ShrVal bvOfInt intEmod
  rw [truncateBits_i64_bvZeroExtend x, bvZeroExtend_128_toNat x]
  dsimp only [Int.natAbs, Int.toNat]
  have hLt : Nat.shiftRight x.toNat k < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt
  have hMod :
      Nat.mod (Nat.shiftRight x.toNat k) (Nat.pow 2 128) =
      Nat.shiftRight x.toNat k :=
    Nat.mod_eq_of_lt (Nat.lt_trans hLt (by decide))
  rw [hMod]
  exact congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
    (truncateBits_i64_ofNat_lt hLt)

/-- Evaluate the RHS value of an `.assign` statement at the active frame. -/
noncomputable def evalAssignVal (body : Body) (s : State) : Option Val :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
      | some (.assign dst rvalue) =>
        match Trusted.MirSemantics.getElem? body.locals dst.localId with
        | some dstTy =>
          match evalRvalue body.locals frame.locals dstTy rvalue with
          | .ok (val, _) => some val
          | .error _ => none
        | none => none
      | _ => none
    | none => none
  | _ => none

/-- Step an `.assign` statement to an unprojected `u64` local while overriding
the written value with `overrideVal`. -/
noncomputable def evalAssignWith (body : Body) (s : State)
    (overrideVal : Val) : StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    match Nat.beq frame.defId 0 with
    | false => .fault .unsupported
    | true =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some (.assign dst rvalue) =>
          match dst.projection with
          | _ :: _ => .fault .unsupported
          | [] =>
            match Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => .fault .unsupported
            | some dstTy =>
              match MirTy.beq dstTy (.int .i64 false) with
              | false => .fault .unsupported
              | true =>
                match evalRvalue body.locals frame.locals dstTy rvalue with
                | .error k => .fault k
                | .ok (_, localsAfterRval) =>
                  match Trusted.MirSemantics.getElem?
                      localsAfterRval dst.localId with
                  | none => .fault .unsupported
                  | some .dead => .fault .undefined
                  | some (.live _) =>
                    match setElem? localsAfterRval dst.localId
                        (.live overrideVal.toSlotVal) with
                    | some localsAfterWrite =>
                      .step {
                        frames := [{
                          frame with
                          stmtIdx := frame.stmtIdx + 1
                          locals := localsAfterWrite
                        }]
                        callerMem := s.callerMem
                      }
                    | none => .fault .unsupported
        | _ => .fault .unsupported
  | _ => .fault .unsupported

private theorem step_eq_evalAssignWith_of_truncate {body : Body}
    {s next : State} {val : Val} {bits : BitVec 128}
    (h_trunc : truncateBits .i64 bits = bits)
    (h_val : evalAssignVal body s = some val)
    (h_eq : val = .scalar ⟨.i64, false, bits⟩)
    (h_next : evalAssignWith body s (.scalar ⟨.i64, false, bits⟩) =
      .step next) :
    evalStep (bodyProg body) 0 s = .step next := by
  unfold evalAssignVal at h_val
  unfold evalAssignWith at h_next
  unfold bodyProg evalStep
  cases h_fr : s.frames with
  | nil => rw [h_fr] at h_next; cases h_next
  | cons frame rest =>
    cases rest with
    | cons _ _ => rw [h_fr] at h_next; cases h_next
    | nil =>
      rw [h_fr] at h_val h_next
      dsimp only at h_val h_next
      dsimp only
      cases h_def : Nat.beq frame.defId 0 with
      | false => rw [h_def] at h_next; cases h_next
      | true =>
        rw [h_def] at h_next
        dsimp only at h_next
        have h_def0 : frame.defId = 0 := Nat.eq_of_beq_eq_true h_def
        rw [h_def0]
        rw [show Trusted.MirSemantics.getElem? [body] 0 = some body from rfl]
        dsimp only
        cases h_bb :
            Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [h_bb] at h_next; cases h_next
        | some bb =>
          rw [h_bb] at h_val h_next
          dsimp only at h_val h_next
          dsimp only
          cases h_st :
              Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | none => rw [h_st] at h_next; cases h_next
          | some stmt =>
            rw [h_st] at h_val h_next
            dsimp only
            cases stmt with
            | nop | storageLive _ | storageDead _ | unsupported =>
              cases h_next
            | assign dst rvalue =>
              dsimp only at h_val h_next
              unfold evalStatement
              dsimp only
              cases h_proj : dst.projection with
              | cons _ _ => rw [h_proj] at h_next; cases h_next
              | nil =>
                rw [h_proj] at h_next
                dsimp only at h_next
                cases h_dst :
                    Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rw [h_dst] at h_next; cases h_next
                | some dstTy =>
                  rw [h_dst] at h_val h_next
                  dsimp only at h_val h_next
                  dsimp only
                  dsimp only [projectTy?]
                  cases h_ty : MirTy.beq dstTy (.int .i64 false) with
                  | false => rw [h_ty] at h_next; cases h_next
                  | true =>
                    rw [h_ty] at h_next
                    dsimp only at h_next
                    have h_ty_eq := MirTy.beq_iff.mp h_ty
                    subst h_ty_eq
                    cases h_rv : evalRvalue body.locals frame.locals
                        (.int .i64 false) rvalue with
                    | error k => rw [h_rv] at h_val; cases h_val
                    | ok pair =>
                      rw [h_rv] at h_val h_next
                      dsimp only at h_val h_next
                      have h_no_ov :
                          assignHasUnsupportedOverlap dst (.int .i64 false)
                            rvalue = false := by
                        cases rvalue with
                        | use _ => rfl
                        | aggregateTuple _ => cases h_rv
                        | _ => rfl
                      rw [ite_bool_false h_no_ov]
                      have h_goal :
                          (match writePlace pair.2 dst (.int .i64 false)
                              pair.1 with
                           | .error k => StepResult.fault k
                           | .ok localsAfterWrite =>
                             StepResult.step {
                               frames := [{
                                 frame with
                                 stmtIdx := frame.stmtIdx + 1
                                 locals := localsAfterWrite
                               }]
                               callerMem := s.callerMem
                             }) = (StepResult.step next :
                               StepResult State TerminalOut) := by
                        injection h_val with h_v
                        have h_vw :
                            pair.1 = .scalar ⟨.i64, false, bits⟩ :=
                          h_v.trans h_eq
                        rw [h_vw]
                        unfold writePlace
                        rw [ite_bool_false (by
                          rw [checkVal_int_iff.mpr ⟨bits, rfl, h_trunc⟩]
                          rfl)]
                        cases h_slot :
                            Trusted.MirSemantics.getElem? pair.2
                              dst.localId with
                        | none => rw [h_slot] at h_next; cases h_next
                        | some slot =>
                          rw [h_slot] at h_next
                          cases slot with
                          | dead => cases h_next
                          | live _ =>
                            dsimp only at h_next
                            dsimp only
                            rw [h_proj]
                            dsimp only [writeSlotPath?, Val.toSlotVal]
                            dsimp only [Val.toSlotVal] at h_next
                            cases h_set : setElem? pair.2 dst.localId
                                (.live (.scalar ⟨.i64, false, bits⟩)) with
                            | none => rw [h_set] at h_next; cases h_next
                            | some localsAfterWrite =>
                              rw [h_set] at h_next
                              exact h_next
                      cases rvalue with
                      | aggregateTuple _ => cases h_rv
                      | _ => exact h_goal

/-- Rewrite a symbolic `evalStep` for a `u64` assignment using an equivalent
normalized `BitVec 64` result. -/
theorem step_eq_evalAssignWith {body : Body} {s next : State} {val : Val}
    {w : BitVec 64}
    (h_val : evalAssignVal body s = some val)
    (h_eq : val = .scalar ⟨.i64, false, bvZeroExtend 128 w⟩)
    (h_next : evalAssignWith body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 w⟩) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate (truncateBits_i64_bvZeroExtend w)
    h_val h_eq h_next

/-- Step an assignment whose RHS evaluates to `BitVec 64` value `x`. -/
theorem step_u64Use {body : Body} {s next : State} (x : BitVec 64)
    (h_val : evalAssignVal body s =
      some (.scalar ⟨.i64, false, bvZeroExtend 128 x⟩))
    (h_next : evalAssignWith body s
      (.scalar ⟨.i64, false, bvZeroExtend 128 x⟩) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val rfl h_next

/-- Step an assignment whose RHS evaluates to 64-bit bitwise AND of `x` and
`y`. -/
theorem step_u64And {body : Body} {s next : State} (x y : BitVec 64)
    (h_val : evalAssignVal body s = some (u64BitAndVal x y))
    (h_next : evalAssignWith body s
      (.scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.land x.toNat y.toNat)⟩) =
      .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (nat_bitwise_lt_two_pow and 64 x.toNat y.toNat x.isLt y.isLt))
    h_val (u64BitAndVal_eq x y) h_next

/-- Step an assignment whose RHS evaluates to 64-bit bitwise OR of `x` and
`y`. -/
theorem step_u64Or {body : Body} {s next : State} (x y : BitVec 64)
    (h_val : evalAssignVal body s = some (u64BitOrVal x y))
    (h_next : evalAssignWith body s
      (.scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)⟩) =
      .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (nat_bitwise_lt_two_pow or 64 x.toNat y.toNat x.isLt y.isLt))
    h_val (u64BitOrVal_eq x y) h_next

/-- Step an assignment whose RHS evaluates to 64-bit left shift of `x` by
`k`. -/
theorem step_u64Shl {body : Body} {s next : State} (x : BitVec 64) (k : Nat)
    (h_val : evalAssignVal body s = some (u64ShlVal x k))
    (h_next : evalAssignWith body s
      (.scalar ⟨.i64, false,
        bvZeroExtend 128 (BitVec.ofNat 64 (Nat.shiftLeft x.toNat k))⟩) =
      .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith h_val (u64ShlVal_eq x k) h_next

/-- Step an assignment whose RHS evaluates to 64-bit logical right shift of
`x` by `k`. -/
theorem step_u64Shr {body : Body} {s next : State} (x : BitVec 64) (k : Nat)
    (h_val : evalAssignVal body s = some (u64ShrVal x k))
    (h_next : evalAssignWith body s
      (.scalar ⟨.i64, false,
        BitVec.ofNat 128 (Nat.shiftRight x.toNat k)⟩) = .step next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith_of_truncate
    (truncateBits_i64_ofNat_lt
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt))
    h_val (u64ShrVal_eq x k) h_next

/-- A finite conjunction supplies one checked proposition for each index. -/
def CheckRange (n : Nat) : (Nat → Prop) → Prop :=
  Nat.rec (fun _ => True) (fun _ ih p => p 0 ∧ ih (fun i => p (i + 1))) n

/-- Unfold `CheckRange` at `0`. -/
theorem checkRange_zero (p : Nat → Prop) : CheckRange 0 p = True := rfl

/-- Unfold `CheckRange` at `n + 1`. -/
theorem checkRange_succ (n : Nat) (p : Nat → Prop) :
    CheckRange (n + 1) p = (p 0 ∧ CheckRange n (fun i => p (i + 1))) := rfl

/-- Every index `i < n` satisfies `p i` when `CheckRange n p` holds. -/
theorem checkRange_sound (n : Nat) (p : Nat → Prop)
    (checked : CheckRange n p) : ∀ i, i < n → p i := by
  induction n generalizing p with
  | zero =>
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    intro i hi
    cases i with
    | zero => exact checked.1
    | succ i => exact ih _ checked.2 i (Nat.lt_of_succ_lt_succ hi)

/-! ## Part V: Interprocedural Modular Call Summaries & Core Builtin Stepping

This part provides stack-composition simulation (`attachCallers`,
`StackWellShaped`, `evalStep_attachState`, `wpOutcomeState_attachState`) and
reusable modular call-summary combinators (`CallSpec`, `wpCallStep`,
`wpCallSummary`, `execCallStep`, `execCallSummary`, `wpCallBuiltin`,
`execCallBuiltin`) so caller proofs can step across direct crate-local
`TerminatorKind.call` and `TerminatorKind.callBuiltin` terminators without
re-symbolically-executing the callee body. -/

/-- Fuel weakening for deterministic `execOutcomeState`. -/
theorem execOutcomeState_fuel_mono {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel₁ fuel₂ : Nat} {s : State}
    (hLe : fuel₁ ≤ fuel₂)
    (h : execOutcomeState p onDone onFault fuel₁ s) :
    execOutcomeState p onDone onFault fuel₂ s :=
  wpOutcomeState_iff_execOutcomeState.mp
    (wpOutcomeState_fuel_mono hLe (wpOutcomeState_iff_execOutcomeState.mpr h))

/-- `evalStep` ignores `Program.entryDefId`, so stepping in
`entryProgForBody p defId` is definitionally identical to stepping in `p`. -/
theorem evalStep_entryProgForBody (p : Program) (defId : DefId)
    (c : Choice) (s : State) :
    evalStep (entryProgForBody p defId) c s = evalStep p c s :=
  rfl

/-- Extract `bodyEntryAdmitted body = true` from `BodyStaticAdmitted p body`. -/
theorem bodyEntryAdmitted_of_static {p : Program} {body : Body}
    (h : BodyStaticAdmitted p body = true) :
    bodyEntryAdmitted body = true := by
  unfold BodyStaticAdmitted at h
  unfold bodyEntryAdmitted
  cases h1 : Nat.beq p.pointerWidthBits 64 <;>
    cases h2 : Nat.beq p.mirProfileVersion 1 <;>
    cases h3 : stringBeq body.identity "" <;>
    cases h4 : body.basicBlocks.isEmpty <;>
    cases h5 : Nat.blt body.argumentCount body.locals.length <;>
    cases h6 : storageAnnotationsInBounds body <;>
    cases h7 : body.locals.all isSupportedScalarOrUnitTy <;>
    rw [h1, h2, h3, h4, h5, h6, h7] at h <;>
    cases h
  rfl

private theorem length_take_of_le {α : Type} :
    ∀ (n : Nat) (xs : List α), n ≤ xs.length → (xs.take n).length = n
  | 0, _, _ => rfl
  | _ + 1, [], h => False.elim (Nat.not_succ_le_zero _ h)
  | n + 1, _ :: xs, h =>
    congrArg Nat.succ (length_take_of_le n xs (Nat.le_of_succ_le_succ h))

private theorem length_paramTys_of_blt {xs : List MirTy} {n : Nat}
    (h : Nat.blt n xs.length = true) :
    ((xs.drop 1).take n).length = n := by
  cases xs with
  | nil => cases h
  | cons _ rest =>
    exact length_take_of_le n rest
      (Nat.le_of_succ_le_succ (Nat.le_of_ble_eq_true h))

/-- Successful `validateCallArgs` implies `checkArgsMatch` and equal argument
and parameter-type lengths. -/
theorem validateCallArgs_spec :
    ∀ {pairs : List (MirTy × SlotVal)} {tys : List MirTy} {vs : List Val},
      validateCallArgs pairs tys = .ok vs →
      checkArgsMatch vs tys = true ∧ pairs.length = tys.length
  | [], [], _, h => by
    injection h with hEq; subst hEq
    exact ⟨rfl, rfl⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | (argTy, sv) :: restPairs, paramTy :: restTys, vs, h => by
    unfold validateCallArgs at h
    cases hTy : MirTy.beq argTy paramTy with
    | false => rw [hTy] at h; cases h
    | true =>
      rw [ite_bool_false (by rw [hTy]; rfl)] at h
      cases hVal : sv.toVal? with
      | none => rw [hVal] at h; cases h
      | some v =>
        rw [hVal] at h
        dsimp only at h
        cases hChk : checkVal v paramTy with
        | false => rw [hChk] at h; cases h
        | true =>
          rw [ite_bool_false (by rw [hChk]; rfl)] at h
          cases hRest : validateCallArgs restPairs restTys with
          | error _ => rw [hRest] at h; cases h
          | ok restVs =>
            rw [hRest] at h
            injection h with hEq; subst hEq
            have ih := validateCallArgs_spec hRest
            refine ⟨?_, congrArg Nat.succ ih.2⟩
            change (checkVal v paramTy && checkArgsMatch restVs restTys) = true
            rw [hChk, ih.1]
            rfl

/-- Structural helper for `attachCallers` with definitional reduction on
singleton and multi-frame stacks (uses `@List.rec` + `noncomputable` to avoid
generating an `_unsafe_rec` compiler helper). -/
noncomputable def attachCallersAux (cont : ReturnContinuation)
    (callers : List FrameState) (head : FrameState) (tail : List FrameState) :
    List FrameState :=
  @List.rec FrameState (fun _ => FrameState → List FrameState)
    (fun h => { h with returnCont := some cont } :: callers)
    (fun g _ ih h => h :: ih g)
    tail head

/-- Attach caller continuation `cont` and caller stack `callers` beneath a
callee stack `fs`, replacing the bottom callee frame's `returnCont` with
`some cont`. -/
noncomputable def attachCallers (cont : ReturnContinuation)
    (callers : List FrameState) : List FrameState → List FrameState
  | [] => callers
  | f :: rest => attachCallersAux cont callers f rest

/-- Lift a callee `State` onto caller continuation `cont` and `callers`. -/
noncomputable def attachState (cont : ReturnContinuation)
    (callers : List FrameState) (s : State) : State :=
  { frames := attachCallers cont callers s.frames, callerMem := s.callerMem }

/-- Well-shaped stack invariant for a root-anchored call stack: non-empty,
every non-bottom frame carries `returnCont = some _`, and the bottom frame
carries `returnCont = none`. -/
def StackWellShaped (fs : List FrameState) : Prop :=
  @List.rec FrameState (fun _ => Prop)
    False
    (fun f rest ih =>
      match rest with
      | [] => f.returnCont = none
      | _ :: _ => f.returnCont.isSome = true ∧ ih)
    fs

/-- Effect of returning `retVal` into caller `(caller, rest)` along `cont`
(mirrors the non-root `.return_` arm of `Trusted.MirSemantics.evalTerminator`).
-/
noncomputable def applyCallReturn (p : Program) (cont : ReturnContinuation)
    (caller : FrameState) (rest : List FrameState) (retVal : Val)
    (callerMem : CallerMemory) : StepResult State TerminalOut :=
  match Trusted.MirSemantics.getElem? p.bodies caller.defId with
  | none => .fault .unsupported
  | some callerBody =>
    match Trusted.MirSemantics.getElem? callerBody.locals cont.dst.localId with
    | none => .fault .unsupported
    | some localTy =>
      match projectTy? localTy cont.dst.projection with
      | none => .fault .unsupported
      | some dstTy =>
        match writePlace caller.locals cont.dst dstTy retVal with
        | .error k => .fault k
        | .ok callerLocals' =>
          match cont.target with
          | some nextBb =>
            jumpToBlock { caller with locals := callerLocals' } rest callerMem
              nextBb
          | none => .fault .undefined

private theorem stackWellShaped_update_head {f f' : FrameState}
    {inner : List FrameState}
    (hrc : f'.returnCont = f.returnCont)
    (hShape : StackWellShaped (f :: inner)) :
    StackWellShaped (f' :: inner) := by
  cases inner with
  | nil =>
    change f'.returnCont = none
    rw [hrc]
    exact hShape
  | cons g tail =>
    refine ⟨?_, hShape.2⟩
    rw [hrc]
    exact hShape.1

private theorem attachCallers_cons_cons (cont : ReturnContinuation)
    (callers : List FrameState) (f g : FrameState) (tail : List FrameState) :
    attachCallers cont callers (f :: g :: tail) =
      f :: attachCallers cont callers (g :: tail) :=
  rfl

private theorem attachCallers_singleton (cont : ReturnContinuation)
    (callers : List FrameState) (f : FrameState) :
    attachCallers cont callers [f] =
      { f with returnCont := some cont } :: callers :=
  rfl

private theorem unwindFrame_cleanup (cm : CallerMemory) (f : FrameState)
    (cs : List FrameState) (block : BasicBlockId) :
    unwindFrame cm f cs (.cleanup block) = jumpToBlock f cs cm block := by
  cases cs <;> rfl

private theorem unwindFrame_unreachable (cm : CallerMemory) (f : FrameState)
    (cs : List FrameState) :
    unwindFrame cm f cs .unreachable = .fault .undefined := by
  cases cs <;> rfl

private theorem unwindFrame_terminate (cm : CallerMemory) (f : FrameState)
    (cs : List FrameState) :
    unwindFrame cm f cs .terminate = .fault .unsupported := by
  cases cs <;> rfl

private theorem unwindFrame_ne_returned (cm : CallerMemory) (r : Out) :
    ∀ (ls : List FrameState) (fr : FrameState) (ua : UnwindAction),
      unwindFrame cm fr ls ua ≠ .done (.returned r)
  | [], fr, ua, hR => by
    cases ua with
    | cleanup _ | unreachable | terminate => cases hR
    | continue_ =>
      unfold unwindFrame at hR
      cases hRc : fr.returnCont with
      | none => rw [hRc] at hR; cases hR
      | some _ => rw [hRc] at hR; cases hR
  | hd :: tl, fr, ua, hR => by
    cases ua with
    | cleanup _ | unreachable | terminate => cases hR
    | continue_ =>
      change (match fr.returnCont with
        | some c => unwindFrame cm hd tl c.unwind
        | none => .fault .unsupported) = .done (.returned r) at hR
      cases hFr : fr.returnCont with
      | none => rw [hFr] at hR; cases hR
      | some c =>
        rw [hFr] at hR
        exact unwindFrame_ne_returned cm r tl hd c.unwind hR

/-- Unwind simulation across `attachCallers`: unwinding a well-shaped callee
stack `(f, inner)` commutes with attaching `(cont, caller :: rest)`, and when
the callee unwinds out of its root frame (`.done (.unwound cm)`) the attached
stack continues unwinding in `(caller, rest)` along `cont.unwind`. -/
theorem unwindFrame_attachCallers (cont : ReturnContinuation)
    (caller : FrameState) (rest : List FrameState) (cm : CallerMemory) :
    ∀ (inner : List FrameState) (f : FrameState) (u : UnwindAction),
      StackWellShaped (f :: inner) →
      (∀ s', unwindFrame cm f inner u = .step s' →
        StackWellShaped s'.frames) ∧
      (match attachCallers cont (caller :: rest) (f :: inner) with
       | [] => StepResult.fault .unsupported
       | f' :: inner' => unwindFrame cm f' inner' u) =
        match unwindFrame cm f inner u with
        | .step next => .step (attachState cont (caller :: rest) next)
        | .done (.unwound cm') => unwindFrame cm' caller rest cont.unwind
        | .done out => .done out
        | .fault k => .fault k := by
  intro inner
  induction inner with
  | nil =>
    intro f u hShape
    have hNone : f.returnCont = none := hShape
    cases u with
    | cleanup block =>
      refine ⟨?_, rfl⟩
      intro s' hStep
      injection hStep with hEq; subst hEq
      exact hNone
    | unreachable =>
      exact ⟨(fun _ h => by cases h), rfl⟩
    | terminate =>
      exact ⟨(fun _ h => by cases h), rfl⟩
    | continue_ =>
      have hLhs : unwindFrame cm f [] .continue_ = .done (.unwound cm) := by
        change (match f.returnCont with
          | none => StepResult.done (TerminalOut.unwound cm)
          | some _ => StepResult.fault .unsupported) = _
        rw [hNone]
      refine ⟨(fun _ h => by rw [hLhs] at h; cases h), ?_⟩
      rw [hLhs]
      rfl
  | cons g tail ih =>
    intro f u hShape
    cases u with
    | cleanup block =>
      dsimp only [attachCallers, attachCallersAux]
      rw [unwindFrame_cleanup, unwindFrame_cleanup]
      refine ⟨?_, rfl⟩
      intro s' hStep
      injection hStep with hEq; subst hEq
      exact hShape
    | unreachable =>
      dsimp only [attachCallers, attachCallersAux]
      rw [unwindFrame_unreachable, unwindFrame_unreachable]
      exact ⟨(fun _ h => by cases h), rfl⟩
    | terminate =>
      dsimp only [attachCallers, attachCallersAux]
      rw [unwindFrame_terminate, unwindFrame_terminate]
      exact ⟨(fun _ h => by cases h), rfl⟩
    | continue_ =>
      cases hRc : f.returnCont with
      | none =>
        have hSome := hShape.1
        rw [hRc] at hSome
        cases hSome
      | some fCont =>
        have hSub := ih g fCont.unwind hShape.2
        have hEq1 : unwindFrame cm f (g :: tail) .continue_ =
            unwindFrame cm g tail fCont.unwind := by
          change (match f.returnCont with
            | some c => unwindFrame cm g tail c.unwind
            | none => .fault .unsupported) = _
          rw [hRc]
        cases hTail : tail with
        | nil =>
          subst hTail
          refine ⟨fun s' hStep => hSub.1 s' (hEq1.symm.trans hStep), ?_⟩
          have hLhs :
              (match attachCallers cont (caller :: rest) [f, g] with
               | [] => StepResult.fault .unsupported
               | f' :: inner' => unwindFrame cm f' inner' .continue_) =
              unwindFrame cm { g with returnCont := some cont }
                (caller :: rest) fCont.unwind := by
            change (match f.returnCont with
              | some c =>
                unwindFrame cm { g with returnCont := some cont }
                  (caller :: rest) c.unwind
              | none => .fault .unsupported) = _
            rw [hRc]
          rw [hLhs, hEq1]
          exact hSub.2
        | cons h tail' =>
          subst hTail
          refine ⟨fun s' hStep => hSub.1 s' (hEq1.symm.trans hStep), ?_⟩
          have hLhs :
              (match attachCallers cont (caller :: rest)
                  (f :: g :: h :: tail') with
               | [] => StepResult.fault .unsupported
               | f' :: inner' => unwindFrame cm f' inner' .continue_) =
              unwindFrame cm g
                (attachCallers cont (caller :: rest) (h :: tail'))
                fCont.unwind := by
            change (match f.returnCont with
              | some c =>
                unwindFrame cm g
                  (attachCallers cont (caller :: rest) (h :: tail')) c.unwind
              | none => .fault .unsupported) = _
            rw [hRc]
          rw [hLhs, hEq1]
          exact hSub.2

private theorem evalStatement_ne_done (body : Body) (f : FrameState)
    (callers : List FrameState) (cm : CallerMemory) (stmt : StatementKind)
    (out : TerminalOut) :
    evalStatement body f callers cm stmt ≠ .done out := by
  unfold evalStatement
  cases stmt with
  | nop | unsupported => intro h; cases h
  | storageLive lid =>
    dsimp only
    cases Trusted.MirSemantics.getElem? body.locals lid with
    | none => intro h; cases h
    | some ty =>
      dsimp only
      cases setElem? f.locals lid (liveUninitSlot ty) <;> intro h <;> cases h
  | storageDead lid =>
    dsimp only
    cases Nat.beq lid 0 with
    | true => intro h; cases h
    | false =>
      cases setElem? f.locals lid .dead <;> intro h <;> cases h
  | assign dst rv =>
    dsimp only
    cases Trusted.MirSemantics.getElem? body.locals dst.localId with
    | none => intro h; cases h
    | some lTy =>
      dsimp only
      cases projectTy? lTy dst.projection with
      | none => intro h; cases h
      | some dTy =>
        dsimp only
        cases assignHasUnsupportedOverlap dst dTy rv with
        | true => intro h; cases h
        | false =>
          cases rv with
          | aggregateTuple ops =>
            dsimp only
            cases writeAggregateTuple body.locals f.locals dst dTy ops <;>
              intro h <;> cases h
          | unsupported => intro h; cases h
          | use _ | binaryOp _ _ _ | unaryOp _ _ | discriminant _
          | ref _ _ | addressOf _ _ | cast _ _ _ =>
            dsimp only
            cases evalRvalue body.locals f.locals dTy _ with
            | error _ => intro h; cases h
            | ok pair =>
              dsimp only
              cases writePlace pair.2 dst dTy pair.1 <;> intro h <;> cases h

private theorem evalStatement_attachCallers (cont : ReturnContinuation)
    (caller : FrameState) (rest : List FrameState) (body : Body)
    (f : FrameState) (inner : List FrameState) (cm : CallerMemory)
    (stmt : StatementKind) (hShape : StackWellShaped (f :: inner)) :
    (∀ s', evalStatement body f inner cm stmt = .step s' →
      StackWellShaped s'.frames) ∧
    (match attachCallers cont (caller :: rest) (f :: inner) with
     | [] => StepResult.fault .unsupported
     | f' :: inner' => evalStatement body f' inner' cm stmt) =
      match evalStatement body f inner cm stmt with
      | .step next => .step (attachState cont (caller :: rest) next)
      | .done out => .done out
      | .fault k => .fault k := by
  cases inner with
  | nil =>
    have hNone : f.returnCont = none := hShape
    unfold evalStatement attachCallers attachCallersAux attachState
    dsimp only
    cases stmt with
    | nop =>
      refine ⟨?_, rfl⟩
      intro s' hStep; injection hStep with hEq; subst hEq; exact hNone
    | storageLive lid =>
      dsimp only
      cases Trusted.MirSemantics.getElem? body.locals lid with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some ty =>
        dsimp only
        cases setElem? f.locals lid (liveUninitSlot ty) with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some l' =>
          refine ⟨?_, rfl⟩
          intro s' hStep; injection hStep with hEq; subst hEq; exact hNone
    | storageDead lid =>
      dsimp only
      cases Nat.beq lid 0 with
      | true => exact ⟨(fun _ h => by cases h), rfl⟩
      | false =>
        cases setElem? f.locals lid .dead with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some l' =>
          refine ⟨?_, rfl⟩
          intro s' hStep; injection hStep with hEq; subst hEq; exact hNone
    | assign dst rv =>
      dsimp only
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some localTy =>
        dsimp only
        cases projectTy? localTy dst.projection with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some dstTy =>
          dsimp only
          cases assignHasUnsupportedOverlap dst dstTy rv with
          | true => exact ⟨(fun _ h => by cases h), rfl⟩
          | false =>
            cases rv with
            | aggregateTuple ops =>
              dsimp only
              cases writeAggregateTuple body.locals f.locals dst dstTy ops with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep; injection hStep with hEq; subst hEq
                exact hNone
            | use opnd =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.use opnd) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hNone
            | binaryOp op l r =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.binaryOp op l r)
                with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hNone
            | unaryOp op opnd =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.unaryOp op opnd)
                with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hNone
            | discriminant p =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.discriminant p) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hNone
            | ref m p =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.ref m p) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hNone
            | addressOf m p =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.addressOf m p) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hNone
            | cast k opnd ty =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.cast k opnd ty) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hNone
            | unsupported => exact ⟨(fun _ h => by cases h), rfl⟩
    | unsupported => exact ⟨(fun _ h => by cases h), rfl⟩
  | cons g tail =>
    unfold evalStatement attachCallers attachCallersAux attachState
    dsimp only
    cases stmt with
    | nop =>
      refine ⟨?_, rfl⟩
      intro s' hStep; injection hStep with hEq; subst hEq; exact hShape
    | storageLive lid =>
      dsimp only
      cases Trusted.MirSemantics.getElem? body.locals lid with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some ty =>
        dsimp only
        cases setElem? f.locals lid (liveUninitSlot ty) with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some l' =>
          refine ⟨?_, rfl⟩
          intro s' hStep; injection hStep with hEq; subst hEq; exact hShape
    | storageDead lid =>
      dsimp only
      cases Nat.beq lid 0 with
      | true => exact ⟨(fun _ h => by cases h), rfl⟩
      | false =>
        cases setElem? f.locals lid .dead with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some l' =>
          refine ⟨?_, rfl⟩
          intro s' hStep; injection hStep with hEq; subst hEq; exact hShape
    | assign dst rv =>
      dsimp only
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => exact ⟨(fun _ h => by cases h), rfl⟩
      | some localTy =>
        dsimp only
        cases projectTy? localTy dst.projection with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some dstTy =>
          dsimp only
          cases assignHasUnsupportedOverlap dst dstTy rv with
          | true => exact ⟨(fun _ h => by cases h), rfl⟩
          | false =>
            cases rv with
            | aggregateTuple ops =>
              dsimp only
              cases writeAggregateTuple body.locals f.locals dst dstTy ops with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok l' =>
                refine ⟨?_, rfl⟩
                intro s' hStep; injection hStep with hEq; subst hEq
                exact hShape
            | use opnd =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.use opnd) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
            | binaryOp op l r =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.binaryOp op l r)
                with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
            | unaryOp op opnd =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.unaryOp op opnd)
                with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
            | discriminant p =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.discriminant p) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
            | ref m p =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.ref m p) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
            | addressOf m p =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.addressOf m p) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
            | cast k opnd ty =>
              dsimp only
              cases evalRvalue body.locals f.locals dstTy (.cast k opnd ty) with
              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
              | ok pair =>
                dsimp only
                cases writePlace pair.2 dst dstTy pair.1 with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok l' =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
            | unsupported => exact ⟨(fun _ h => by cases h), rfl⟩
    | unsupported => exact ⟨(fun _ h => by cases h), rfl⟩

/-- Single-step simulation of `evalStep p 0` across `attachState`: any
well-shaped callee state `s` executes identically atop `(cont, caller :: rest)`
until it returns (`.done (.returned r)` -> `applyCallReturn`) or unwinds
(`.done (.unwound cm)` -> `unwindFrame cm caller rest cont.unwind`). -/
theorem evalStep_attachState (p : Program) (cont : ReturnContinuation)
    (caller : FrameState) (rest : List FrameState) (s : State)
    (hShape : StackWellShaped s.frames) :
    (∀ s', evalStep p 0 s = .step s' → StackWellShaped s'.frames) ∧
    evalStep p 0 (attachState cont (caller :: rest) s) =
      match evalStep p 0 s with
      | .step next => .step (attachState cont (caller :: rest) next)
      | .done (.returned r) =>
        applyCallReturn p cont caller rest r.ret r.callerMem
      | .done (.unwound cm) => unwindFrame cm caller rest cont.unwind
      | .fault k => .fault k := by
  cases s with
  | mk frames cm =>
    cases frames with
    | nil => exact False.elim hShape
    | cons f inner =>
      have hStepHead : ∀ body bb,
          Trusted.MirSemantics.getElem? p.bodies f.defId = some body →
          Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb →
          Trusted.MirSemantics.getElem? bb.statements f.stmtIdx = none →
          Nat.beq f.stmtIdx bb.statements.length = true →
          (∀ s', evalTerminator p body bb f inner cm = .step s' →
            StackWellShaped s'.frames) ∧
          (match attachCallers cont (caller :: rest) (f :: inner) with
           | [] => StepResult.fault .unsupported
           | f' :: inner' => evalTerminator p body bb f' inner' cm) =
            match evalTerminator p body bb f inner cm with
            | .step next => .step (attachState cont (caller :: rest) next)
            | .done (.returned r) =>
              applyCallReturn p cont caller rest r.ret r.callerMem
            | .done (.unwound cm') => unwindFrame cm' caller rest cont.unwind
            | .fault k => .fault k := by
        intro body bb _ _ _ _
        cases hT : bb.terminator with
        | goto target =>
          unfold evalTerminator jumpToBlock
          rw [hT]
          cases inner with
          | nil =>
            refine ⟨?_, rfl⟩
            intro s' hStep; injection hStep with hEq; subst hEq; exact hShape
          | cons g tail =>
            refine ⟨?_, rfl⟩
            intro s' hStep; injection hStep with hEq; subst hEq; exact hShape
        | return_ =>
          unfold evalTerminator applyCallReturn
          rw [hT]
          dsimp only
          cases inner with
          | nil =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases bb.cleanup with
            | true => exact ⟨(fun _ h => by cases h), rfl⟩
            | false =>
              cases Trusted.MirSemantics.getElem? f.locals 0 with
              | none => exact ⟨(fun _ h => by cases h), rfl⟩
              | some slot =>
                cases slot with
                | dead => exact ⟨(fun _ h => by cases h), rfl⟩
                | live sv =>
                  dsimp only
                  cases sv.toVal? with
                  | none => exact ⟨(fun _ h => by cases h), rfl⟩
                  | some retVal =>
                    have hNone : f.returnCont = none := hShape
                    rw [hNone]
                    exact ⟨(fun _ h => by cases h), rfl⟩
          | cons g tail =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases bb.cleanup with
            | true => exact ⟨(fun _ h => by cases h), rfl⟩
            | false =>
              cases Trusted.MirSemantics.getElem? f.locals 0 with
              | none => exact ⟨(fun _ h => by cases h), rfl⟩
              | some slot =>
                cases slot with
                | dead => exact ⟨(fun _ h => by cases h), rfl⟩
                | live sv =>
                  dsimp only
                  cases sv.toVal? with
                  | none => exact ⟨(fun _ h => by cases h), rfl⟩
                  | some retVal =>
                    cases hRc : f.returnCont with
                    | none =>
                      have hSome := hShape.1
                      rw [hRc] at hSome; cases hSome
                    | some fCont =>
                      cases hTail : tail with
                      | nil =>
                        subst hTail
                        dsimp only [attachCallersAux]
                        cases Trusted.MirSemantics.getElem? p.bodies g.defId
                          with
                        | none => exact ⟨(fun _ h => by cases h), rfl⟩
                        | some cBody =>
                          dsimp only
                          cases Trusted.MirSemantics.getElem? cBody.locals
                              fCont.dst.localId with
                          | none => exact ⟨(fun _ h => by cases h), rfl⟩
                          | some lTy =>
                            dsimp only
                            cases projectTy? lTy fCont.dst.projection with
                            | none => exact ⟨(fun _ h => by cases h), rfl⟩
                            | some dTy =>
                              dsimp only
                              cases writePlace g.locals fCont.dst dTy retVal
                                with
                              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                              | ok l' =>
                                cases fCont.target with
                                | none => exact ⟨(fun _ h => by cases h), rfl⟩
                                | some nextBb =>
                                  refine ⟨?_, rfl⟩
                                  intro s' hStep
                                  injection hStep with hEq; subst hEq
                                  exact hShape.2
                      | cons h tail' =>
                        subst hTail
                        dsimp only [attachCallersAux]
                        cases Trusted.MirSemantics.getElem? p.bodies g.defId
                          with
                        | none => exact ⟨(fun _ h => by cases h), rfl⟩
                        | some cBody =>
                          dsimp only
                          cases Trusted.MirSemantics.getElem? cBody.locals
                              fCont.dst.localId with
                          | none => exact ⟨(fun _ h => by cases h), rfl⟩
                          | some lTy =>
                            dsimp only
                            cases projectTy? lTy fCont.dst.projection with
                            | none => exact ⟨(fun _ h => by cases h), rfl⟩
                            | some dTy =>
                              dsimp only
                              cases writePlace g.locals fCont.dst dTy retVal
                                with
                              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                              | ok l' =>
                                cases fCont.target with
                                | none => exact ⟨(fun _ h => by cases h), rfl⟩
                                | some nextBb =>
                                  refine ⟨?_, rfl⟩
                                  intro s' hStep
                                  injection hStep with hEq; subst hEq
                                  exact hShape.2
        | unreachable =>
          unfold evalTerminator
          rw [hT]
          cases inner <;> exact ⟨(fun _ h => by cases h), rfl⟩
        | switchInt discr targets =>
          unfold evalTerminator jumpToBlock
          rw [hT]
          dsimp only
          cases inner with
          | nil =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases evalPrimitiveOperand body.locals f.locals discr with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases pair.1 with
              | scalar sv =>
                dsimp only
                cases evalSwitchBranches sv.width sv.bits targets.otherwise
                    targets.branches with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok tgt =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
              | bool b =>
                dsimp only
                cases evalBoolSwitchBranches b targets.otherwise
                    targets.branches with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok tgt =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
              | ptr _ | unit | tuple _ | bytes _ | enumVal _ _ =>
                exact ⟨(fun _ h => by cases h), rfl⟩
          | cons g tail =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases evalPrimitiveOperand body.locals f.locals discr with
            | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
            | ok pair =>
              dsimp only
              cases pair.1 with
              | scalar sv =>
                dsimp only
                cases evalSwitchBranches sv.width sv.bits targets.otherwise
                    targets.branches with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok tgt =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
              | bool b =>
                dsimp only
                cases evalBoolSwitchBranches b targets.otherwise
                    targets.branches with
                | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                | ok tgt =>
                  refine ⟨?_, rfl⟩
                  intro s' hStep; injection hStep with hEq; subst hEq
                  exact hShape
              | ptr _ | unit | tuple _ | bytes _ | enumVal _ _ =>
                exact ⟨(fun _ h => by cases h), rfl⟩
        | assert cond expected msg target unwind =>
          unfold evalTerminator jumpToBlock
          rw [hT]
          dsimp only
          cases hOp : evalPrimitiveOperand body.locals f.locals cond with
          | error _ =>
            cases inner <;>
              (dsimp only [attachCallers, attachCallersAux]; rw [hOp];
               exact ⟨(fun _ h => by cases h), rfl⟩)
          | ok pair =>
            cases pair with
            | mk condVal localsAfterCond =>
              cases condVal with
              | bool b =>
                cases hEqB : (expected == b) with
                | true =>
                  cases inner with
                  | nil =>
                    dsimp only [attachCallers, attachCallersAux, attachState]
                    rw [hOp]; dsimp only; rw [hEqB]
                    refine ⟨?_, rfl⟩
                    intro s' hStep; injection hStep with hEq; subst hEq
                    exact hShape
                  | cons g tail =>
                    dsimp only [attachCallers, attachCallersAux, attachState]
                    rw [hOp]; dsimp only; rw [hEqB]
                    refine ⟨?_, rfl⟩
                    intro s' hStep; injection hStep with hEq; subst hEq
                    exact hShape
                | false =>
                  cases hMsg : isOperandFreeAssertKind msg with
                  | false =>
                    cases inner <;>
                      (dsimp only [attachCallers, attachCallersAux];
                       rw [hOp]; dsimp only; rw [hEqB];
                       exact ⟨(fun _ h => by cases h), rfl⟩)
                  | true =>
                    have hUnw := unwindFrame_attachCallers cont caller rest cm
                      inner { f with locals := localsAfterCond } unwind
                      (stackWellShaped_update_head rfl hShape)
                    cases hInner : inner with
                    | nil =>
                      subst hInner
                      dsimp only [attachCallers, attachCallersAux] at hUnw
                      dsimp only [attachCallers, attachCallersAux]
                      rw [hOp]; dsimp only; rw [hEqB]
                      refine ⟨hUnw.1, ?_⟩
                      rw [hUnw.2]
                      cases hU : unwindFrame cm
                          { f with locals := localsAfterCond } [] unwind with
                      | step _ | fault _ => rfl
                      | done out =>
                        cases out with
                        | unwound _ => rfl
                        | returned r =>
                          exact False.elim
                            (unwindFrame_ne_returned cm r [] _ unwind hU)
                    | cons g tail =>
                      subst hInner
                      dsimp only [attachCallers, attachCallersAux] at hUnw
                      dsimp only [attachCallers, attachCallersAux]
                      rw [hOp]; dsimp only; rw [hEqB]
                      refine ⟨hUnw.1, ?_⟩
                      rw [hUnw.2]
                      cases hU : unwindFrame cm
                          { f with locals := localsAfterCond } (g :: tail)
                          unwind with
                      | step _ | fault _ => rfl
                      | done out =>
                        cases out with
                        | unwound _ => rfl
                        | returned r =>
                          exact False.elim
                            (unwindFrame_ne_returned cm r (g :: tail) _ unwind
                              hU)
              | scalar _ | ptr _ | unit | tuple _ | bytes _ | enumVal _ _ =>
                cases inner <;>
                  (dsimp only [attachCallers, attachCallersAux]; rw [hOp];
                   exact ⟨(fun _ h => by cases h), rfl⟩)
        | unwindResume =>
          unfold evalTerminator
          rw [hT]
          dsimp only
          cases bb.cleanup with
          | false =>
            cases inner <;> exact ⟨(fun _ h => by cases h), rfl⟩
          | true =>
            have hUnw := unwindFrame_attachCallers cont caller rest cm
              inner f .continue_ hShape
            refine ⟨hUnw.1, ?_⟩
            have hEq := hUnw.2
            cases hInner : inner with
            | nil =>
              subst hInner
              dsimp only [attachCallers, attachCallersAux] at hEq
              dsimp only [attachCallers, attachCallersAux]
              rw [hEq]
              cases hU : unwindFrame cm f [] .continue_ with
              | step _ | fault _ => rfl
              | done out =>
                cases out with
                | unwound _ => rfl
                | returned r =>
                  exact False.elim
                    (unwindFrame_ne_returned cm r [] f .continue_ hU)
            | cons g tail =>
              subst hInner
              dsimp only [attachCallers, attachCallersAux] at hEq
              dsimp only [attachCallers, attachCallersAux]
              rw [hEq]
              cases hU : unwindFrame cm f (g :: tail) .continue_ with
              | step _ | fault _ => rfl
              | done out =>
                cases out with
                | unwound _ => rfl
                | returned r =>
                  exact False.elim
                    (unwindFrame_ne_returned cm r (g :: tail) f .continue_ hU)
        | call callee args dst target unwind =>
          unfold evalTerminator
          rw [hT]
          dsimp only
          cases inner with
          | nil =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases anyMoveOperandMayOverlapPlace dst args with
            | true => exact ⟨(fun _ h => by cases h), rfl⟩
            | false =>
              cases Trusted.MirSemantics.getElem? body.locals dst.localId with
              | none => exact ⟨(fun _ h => by cases h), rfl⟩
              | some lTy =>
                dsimp only
                cases projectTy? lTy dst.projection with
                | none => exact ⟨(fun _ h => by cases h), rfl⟩
                | some dTy =>
                  dsimp only
                  cases evalCallArgs body.locals f.locals args with
                  | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                  | ok ap =>
                    dsimp only
                    cases Trusted.MirSemantics.getElem? p.bodies callee with
                    | none => exact ⟨(fun _ h => by cases h), rfl⟩
                    | some cBody =>
                      dsimp only
                      cases bodyEntryAdmitted cBody with
                      | false => exact ⟨(fun _ h => by cases h), rfl⟩
                      | true =>
                        cases Nat.beq ap.1.length cBody.argumentCount with
                        | false => exact ⟨(fun _ h => by cases h), rfl⟩
                        | true =>
                          cases Trusted.MirSemantics.getElem? cBody.locals 0
                            with
                          | none => exact ⟨(fun _ h => by cases h), rfl⟩
                          | some cRetTy =>
                            dsimp only
                            cases MirTy.beq cRetTy dTy with
                            | false => exact ⟨(fun _ h => by cases h), rfl⟩
                            | true =>
                              cases deinitPlace ap.2 dst dTy with
                              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                              | ok localsAfterDeinit =>
                                dsimp only
                                cases validateCallArgs ap.1
                                    ((cBody.locals.drop 1).take
                                      cBody.argumentCount) with
                                | error _ =>
                                  exact ⟨(fun _ h => by cases h), rfl⟩
                                | ok argVals =>
                                  refine ⟨?_, rfl⟩
                                  intro s' hStep
                                  injection hStep with hEq; subst hEq
                                  exact ⟨rfl, hShape⟩
          | cons g tail =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases anyMoveOperandMayOverlapPlace dst args with
            | true => exact ⟨(fun _ h => by cases h), rfl⟩
            | false =>
              cases Trusted.MirSemantics.getElem? body.locals dst.localId with
              | none => exact ⟨(fun _ h => by cases h), rfl⟩
              | some lTy =>
                dsimp only
                cases projectTy? lTy dst.projection with
                | none => exact ⟨(fun _ h => by cases h), rfl⟩
                | some dTy =>
                  dsimp only
                  cases evalCallArgs body.locals f.locals args with
                  | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                  | ok ap =>
                    dsimp only
                    cases Trusted.MirSemantics.getElem? p.bodies callee with
                    | none => exact ⟨(fun _ h => by cases h), rfl⟩
                    | some cBody =>
                      dsimp only
                      cases bodyEntryAdmitted cBody with
                      | false => exact ⟨(fun _ h => by cases h), rfl⟩
                      | true =>
                        cases Nat.beq ap.1.length cBody.argumentCount with
                        | false => exact ⟨(fun _ h => by cases h), rfl⟩
                        | true =>
                          cases Trusted.MirSemantics.getElem? cBody.locals 0
                            with
                          | none => exact ⟨(fun _ h => by cases h), rfl⟩
                          | some cRetTy =>
                            dsimp only
                            cases MirTy.beq cRetTy dTy with
                            | false => exact ⟨(fun _ h => by cases h), rfl⟩
                            | true =>
                              cases deinitPlace ap.2 dst dTy with
                              | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                              | ok localsAfterDeinit =>
                                dsimp only
                                cases validateCallArgs ap.1
                                    ((cBody.locals.drop 1).take
                                      cBody.argumentCount) with
                                | error _ =>
                                  exact ⟨(fun _ h => by cases h), rfl⟩
                                | ok argVals =>
                                  refine ⟨?_, rfl⟩
                                  intro s' hStep
                                  injection hStep with hEq; subst hEq
                                  exact ⟨rfl, hShape⟩
        | callBuiltin builtin args dst target _ =>
          unfold evalTerminator jumpToBlock
          rw [hT]
          dsimp only
          cases inner with
          | nil =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases anyMoveOperandMayOverlapPlace dst args with
            | true => exact ⟨(fun _ h => by cases h), rfl⟩
            | false =>
              cases Trusted.MirSemantics.getElem? body.locals dst.localId with
              | none => exact ⟨(fun _ h => by cases h), rfl⟩
              | some lTy =>
                dsimp only
                cases projectTy? lTy dst.projection with
                | none => exact ⟨(fun _ h => by cases h), rfl⟩
                | some dTy =>
                  dsimp only
                  cases evalCallArgs body.locals f.locals args with
                  | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                  | ok ap =>
                    dsimp only
                    cases readPrimitiveArgs ap.1 with
                    | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                    | ok argVals =>
                      dsimp only
                      cases evalCoreBuiltin builtin argVals with
                      | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                      | ok resVal =>
                        dsimp only
                        cases writePlace ap.2 dst dTy resVal with
                        | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                        | ok l' =>
                          cases target with
                          | none => exact ⟨(fun _ h => by cases h), rfl⟩
                          | some nextBb =>
                            refine ⟨?_, rfl⟩
                            intro s' hStep
                            injection hStep with hEq; subst hEq
                            exact hShape
          | cons g tail =>
            dsimp only [attachCallers, attachCallersAux, attachState]
            cases anyMoveOperandMayOverlapPlace dst args with
            | true => exact ⟨(fun _ h => by cases h), rfl⟩
            | false =>
              cases Trusted.MirSemantics.getElem? body.locals dst.localId with
              | none => exact ⟨(fun _ h => by cases h), rfl⟩
              | some lTy =>
                dsimp only
                cases projectTy? lTy dst.projection with
                | none => exact ⟨(fun _ h => by cases h), rfl⟩
                | some dTy =>
                  dsimp only
                  cases evalCallArgs body.locals f.locals args with
                  | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                  | ok ap =>
                    dsimp only
                    cases readPrimitiveArgs ap.1 with
                    | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                    | ok argVals =>
                      dsimp only
                      cases evalCoreBuiltin builtin argVals with
                      | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                      | ok resVal =>
                        dsimp only
                        cases writePlace ap.2 dst dTy resVal with
                        | error _ => exact ⟨(fun _ h => by cases h), rfl⟩
                        | ok l' =>
                          cases target with
                          | none => exact ⟨(fun _ h => by cases h), rfl⟩
                          | some nextBb =>
                            refine ⟨?_, rfl⟩
                            intro s' hStep
                            injection hStep with hEq; subst hEq
                            exact hShape
        | unsupported =>
          unfold evalTerminator
          rw [hT]
          cases inner <;> exact ⟨(fun _ h => by cases h), rfl⟩
      unfold evalStep attachState
      cases hInner : inner with
      | nil =>
        subst hInner
        dsimp only [attachCallers, attachCallersAux]
        cases hBody : Trusted.MirSemantics.getElem? p.bodies f.defId with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some body =>
          dsimp only
          cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx
            with
          | none => exact ⟨(fun _ h => by cases h), rfl⟩
          | some bb =>
            dsimp only
            cases hSt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx
              with
            | some stmt =>
              have hS := evalStatement_attachCallers cont caller rest body f []
                cm stmt hShape
              refine ⟨hS.1, ?_⟩
              dsimp only [attachCallers, attachCallersAux] at hS
              dsimp only [attachCallers, attachCallersAux]
              rw [hS.2]
              cases hEv : evalStatement body f [] cm stmt with
              | step _ | fault _ => rfl
              | done out =>
                exact False.elim
                  (evalStatement_ne_done body f [] cm stmt out hEv)
            | none =>
              dsimp only
              cases hLen : Nat.beq f.stmtIdx bb.statements.length with
              | false => exact ⟨(fun _ h => by cases h), rfl⟩
              | true =>
                exact hStepHead body bb hBody hBb hSt hLen
      | cons g tail =>
        subst hInner
        dsimp only [attachCallers, attachCallersAux]
        cases hBody : Trusted.MirSemantics.getElem? p.bodies f.defId with
        | none => exact ⟨(fun _ h => by cases h), rfl⟩
        | some body =>
          dsimp only
          cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx
            with
          | none => exact ⟨(fun _ h => by cases h), rfl⟩
          | some bb =>
            dsimp only
            cases hSt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx
              with
            | some stmt =>
              have hS := evalStatement_attachCallers cont caller rest body f
                (g :: tail) cm stmt hShape
              refine ⟨hS.1, ?_⟩
              dsimp only [attachCallers, attachCallersAux] at hS
              dsimp only [attachCallers, attachCallersAux]
              rw [hS.2]
              cases hEv : evalStatement body f (g :: tail) cm stmt with
              | step _ | fault _ => rfl
              | done out =>
                exact False.elim
                  (evalStatement_ne_done body f (g :: tail) cm stmt out hEv)
            | none =>
              dsimp only
              cases hLen : Nat.beq f.stmtIdx bb.statements.length with
              | false => exact ⟨(fun _ h => by cases h), rfl⟩
              | true =>
                exact hStepHead body bb hBody hBb hSt hLen

/-- Frame-composition theorem for `execOutcomeState`: a callee proven within
`calleeFuel` steps composes directly with caller continuations of budget
`contFuel`, consuming at most `calleeFuel + contFuel` steps in total. -/
theorem execOutcomeState_attachState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {post : Val → CallerMemory → Prop} {unwindPost : CallerMemory → Prop}
    {cont : ReturnContinuation} {caller : FrameState} {rest : List FrameState}
    {contFuel : Nat}
    (hRet : ∀ retVal cm, post retVal cm →
      match applyCallReturn p cont caller rest retVal cm with
      | .step s' => execOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k)
    (hUnw : ∀ cm, unwindPost cm →
      match unwindFrame cm caller rest cont.unwind with
      | .step s' => execOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k) :
    ∀ {calleeFuel : Nat} {s : State},
      StackWellShaped s.frames →
      execState p calleeFuel s
        (fun out =>
          match out with
          | .returned r => post r.ret r.callerMem
          | .unwound cm => unwindPost cm) →
      execOutcomeState p onDone onFault (calleeFuel + contFuel)
        (attachState cont (caller :: rest) s)
  | 0, _, _, hCallee => False.elim hCallee
  | f + 1, s, hShape, hCallee => by
    rw [Nat.succ_add]
    have hSim := evalStep_attachState p cont caller rest s hShape
    change (match evalStep p 0 (attachState cont (caller :: rest) s) with
      | .step st' => execOutcomeState p onDone onFault (f + contFuel) st'
      | .done out => onDone out
      | .fault k => onFault k)
    rw [hSim.2]
    change (match evalStep p 0 s with
      | .step st' =>
        execState p f st'
          (fun out =>
            match out with
            | .returned r => post r.ret r.callerMem
            | .unwound cm => unwindPost cm)
      | .done out =>
        match out with
        | .returned r => post r.ret r.callerMem
        | .unwound cm => unwindPost cm
      | .fault _ => False) at hCallee
    cases hSt : evalStep p 0 s with
    | step next =>
      rw [hSt] at hCallee
      exact execOutcomeState_attachState hRet hUnw (hSim.1 next hSt) hCallee
    | done out =>
      rw [hSt] at hCallee
      cases out with
      | returned r =>
        dsimp only
        have hR := hRet r.ret r.callerMem hCallee
        cases hApp : applyCallReturn p cont caller rest r.ret r.callerMem with
        | step s' =>
          rw [hApp] at hR
          exact execOutcomeState_fuel_mono (Nat.le_add_left contFuel f) hR
        | done out' => rw [hApp] at hR; exact hR
        | fault k => rw [hApp] at hR; exact hR
      | unwound cm =>
        dsimp only
        have hU := hUnw cm hCallee
        cases hUnwStep : unwindFrame cm caller rest cont.unwind with
        | step s' =>
          rw [hUnwStep] at hU
          exact execOutcomeState_fuel_mono (Nat.le_add_left contFuel f) hU
        | done out' => rw [hUnwStep] at hU; exact hU
        | fault k => rw [hUnwStep] at hU; exact hU
    | fault _ =>
      rw [hSt] at hCallee
      exact False.elim hCallee

/-- Frame-composition theorem for `wpOutcomeState`. -/
theorem wpOutcomeState_attachState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {post : Val → CallerMemory → Prop} {unwindPost : CallerMemory → Prop}
    {cont : ReturnContinuation} {caller : FrameState} {rest : List FrameState}
    {calleeFuel contFuel : Nat} {s : State}
    (hShape : StackWellShaped s.frames)
    (hCallee : wpState p calleeFuel s
      (fun out =>
        match out with
        | .returned r => post r.ret r.callerMem
        | .unwound cm => unwindPost cm))
    (hRet : ∀ retVal cm, post retVal cm →
      match applyCallReturn p cont caller rest retVal cm with
      | .step s' => wpOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k)
    (hUnw : ∀ cm, unwindPost cm →
      match unwindFrame cm caller rest cont.unwind with
      | .step s' => wpOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k) :
    wpOutcomeState p onDone onFault (calleeFuel + contFuel)
      (attachState cont (caller :: rest) s) := by
  refine wpOutcomeState_of_execOutcomeState
    (execOutcomeState_attachState ?_ ?_ hShape
      (execOutcomeState_of_wpOutcomeState hCallee))
  · intro retVal cm hPost
    have hR := hRet retVal cm hPost
    cases hApp : applyCallReturn p cont caller rest retVal cm with
    | step s' =>
      rw [hApp] at hR
      exact execOutcomeState_of_wpOutcomeState hR
    | done _ => rw [hApp] at hR; exact hR
    | fault _ => rw [hApp] at hR; exact hR
  · intro cm hPost
    have hU := hUnw cm hPost
    cases hUnwStep : unwindFrame cm caller rest cont.unwind with
    | step s' =>
      rw [hUnwStep] at hU
      exact execOutcomeState_of_wpOutcomeState hU
    | done _ => rw [hUnwStep] at hU; exact hU
    | fault _ => rw [hUnwStep] at hU; exact hU

/-- Modular interprocedural summary contract for a crate-local callee `callee`
in program `p`: for every argument vector satisfying `ValidEntryArgs` and
`pre`, executing `callee` from its root frame with any `callerMem` terminates
within `fuel` steps without faulting, satisfying `post` on normal return or
`unwindPost` on unwinding. -/
structure CallSpec (p : Program) (callee : DefId) where
  calleeBody : Body
  h_body : Trusted.MirSemantics.getElem? p.bodies callee = some calleeBody
  h_admitted : bodyEntryAdmitted calleeBody = true
  fuel : Nat
  pre : List Val → Prop
  post : List Val → Val → CallerMemory → Prop
  unwindPost : List Val → CallerMemory → Prop
  sound :
    ∀ (args : List Val) (callerMem : CallerMemory),
      ValidEntryArgs calleeBody args →
      pre args →
      wpState p fuel
        {
          frames := [{
            defId := callee
            blockIdx := 0
            stmtIdx := 0
            locals := initLocalsLoop calleeBody args 0 calleeBody.locals
          }]
          callerMem := callerMem
        }
        (fun out =>
          match out with
          | .returned r => post args r.ret r.callerMem
          | .unwound cm => unwindPost args cm)

/-- Build a `CallSpec` from a deterministic `execState` callee proof. -/
def CallSpec.ofExec {p : Program} {callee : DefId}
    (calleeBody : Body)
    (h_body : Trusted.MirSemantics.getElem? p.bodies callee = some calleeBody)
    (h_admitted : bodyEntryAdmitted calleeBody = true)
    (fuel : Nat)
    (pre : List Val → Prop)
    (post : List Val → Val → CallerMemory → Prop)
    (unwindPost : List Val → CallerMemory → Prop)
    (sound :
      ∀ (args : List Val) (callerMem : CallerMemory),
        ValidEntryArgs calleeBody args →
        pre args →
        execState p fuel
          {
            frames := [{
              defId := callee
              blockIdx := 0
              stmtIdx := 0
              locals := initLocalsLoop calleeBody args 0 calleeBody.locals
            }]
            callerMem := callerMem
          }
          (fun out =>
            match out with
            | .returned r => post args r.ret r.callerMem
            | .unwound cm => unwindPost args cm)) :
    CallSpec p callee :=
  {
    calleeBody
    h_body
    h_admitted
    fuel
    pre
    post
    unwindPost
    sound := fun args cm hValid hPre =>
      wpOutcomeState_of_execOutcomeState (sound args cm hValid hPre)
  }

/-- Lift a single-body `bodyProg calleeBody` proof for a call-free callee into
a modular `CallSpec p callee`. -/
def CallSpec.ofSingleBody {p : Program} {callee : DefId}
    (calleeBody : Body)
    (h_body : Trusted.MirSemantics.getElem? p.bodies callee = some calleeBody)
    (h_admitted : bodyEntryAdmitted calleeBody = true)
    (fuel : Nat)
    (pre : List Val → Prop)
    (post : List Val → Val → CallerMemory → Prop)
    (unwindPost : List Val → CallerMemory → Prop)
    (sound :
      ∀ (args : List Val) (callerMem : CallerMemory),
        ValidEntryArgs calleeBody args →
        pre args →
        execState (bodyProg calleeBody) fuel
          {
            frames := [{
              defId := 0
              blockIdx := 0
              stmtIdx := 0
              locals := initLocalsLoop calleeBody args 0 calleeBody.locals
            }]
            callerMem := callerMem
          }
          (fun out =>
            match out with
            | .returned r => post args r.ret r.callerMem
            | .unwound cm => unwindPost args cm))
    (h_callFree : bodyCallFree calleeBody = true := by rfl) :
    CallSpec p callee :=
  CallSpec.ofExec calleeBody h_body h_admitted fuel pre post unwindPost
    (fun args cm hValid hPre =>
      (execOutcomeState_entryProg_iff h_body h_callFree ⟨_, rfl, rfl⟩).mpr
        (sound args cm hValid hPre))

/-- One-step reduction equation for a valid `TerminatorKind.call` site. -/
theorem evalStep_call {p : Program} {callerBody calleeBody : Body}
    {bb : BasicBlock} {frame : FrameState} {callers : List FrameState}
    {callerMem : CallerMemory} {callee : DefId} {args : List Operand}
    {dst : Place} {target : Option BasicBlockId} {unwind : UnwindAction}
    {localTy dstTy calleeRetTy : MirTy}
    {argPairs : List (MirTy × SlotVal)}
    {localsAfterArgs localsAfterDeinit : List LocalSlot}
    {argVals : List Val}
    (h_caller : Trusted.MirSemantics.getElem? p.bodies frame.defId =
      some callerBody)
    (h_bb : Trusted.MirSemantics.getElem? callerBody.basicBlocks
      frame.blockIdx = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator = .call callee args dst target unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? callerBody.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs callerBody.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_callee : Trusted.MirSemantics.getElem? p.bodies callee = some calleeBody)
    (h_adm : bodyEntryAdmitted calleeBody = true)
    (h_retTy : Trusted.MirSemantics.getElem? calleeBody.locals 0 =
      some calleeRetTy)
    (h_retEq : calleeRetTy = dstTy)
    (h_deinit : deinitPlace localsAfterArgs dst dstTy = .ok localsAfterDeinit)
    (h_val : validateCallArgs argPairs
      ((calleeBody.locals.drop 1).take calleeBody.argumentCount) =
      .ok argVals) :
    evalStep p 0 { frames := frame :: callers, callerMem := callerMem } =
      .step (attachState ⟨dst, target, unwind⟩
        ({ frame with locals := localsAfterDeinit } :: callers)
        {
          frames := [{
            defId := callee
            blockIdx := 0
            stmtIdx := 0
            locals := initLocalsLoop calleeBody argVals 0 calleeBody.locals
          }]
          callerMem := callerMem
        }) := by
  have hBlt :
      Nat.blt calleeBody.argumentCount calleeBody.locals.length = true := by
    unfold bodyEntryAdmitted at h_adm
    cases h1 : calleeBody.basicBlocks.isEmpty <;>
      cases h2 : Nat.blt calleeBody.argumentCount calleeBody.locals.length <;>
      cases h3 : storageAnnotationsInBounds calleeBody <;>
      cases h4 : calleeBody.locals.all isSupportedScalarOrUnitTy <;>
      rw [h1, h2, h3, h4] at h_adm <;>
      first | rfl | cases h_adm
  have hArity : Nat.beq argPairs.length calleeBody.argumentCount = true := by
    have hLenEq : argPairs.length = calleeBody.argumentCount :=
      (validateCallArgs_spec h_val).2.trans (length_paramTys_of_blt hBlt)
    rw [hLenEq]
    exact Nat.beq_refl _
  unfold evalStep evalTerminator attachState attachCallers
  dsimp only
  rw [h_caller]
  dsimp only
  rw [h_bb]
  dsimp only
  rw [h_stmt]
  dsimp only
  rw [ite_bool_true h_len]
  rw [h_term]
  dsimp only
  rw [ite_bool_false h_noOverlap]
  rw [h_dstLocal]
  dsimp only
  rw [h_dstTy]
  dsimp only
  rw [h_args]
  dsimp only
  rw [h_callee]
  dsimp only
  rw [ite_bool_false (by rw [h_adm]; rfl)]
  rw [ite_bool_false (by rw [hArity]; rfl)]
  rw [h_retTy]
  dsimp only
  subst h_retEq
  rw [ite_bool_false (by rw [MirTy.beq_iff.mpr rfl]; rfl)]
  rw [h_deinit]
  dsimp only
  rw [h_val]
  rfl

/-- Modular interprocedural call-step rule for `wpOutcomeState`: steps across a
direct crate-local `TerminatorKind.call` using `spec : CallSpec p callee`
without re-symbolically-executing `callee`'s body. -/
theorem wpCallStep {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {callerBody : Body} {bb : BasicBlock}
    {frame : FrameState} {callers : List FrameState} {callerMem : CallerMemory}
    {callee : DefId} {args : List Operand} {dst : Place}
    {target : Option BasicBlockId} {unwind : UnwindAction}
    {localTy dstTy calleeRetTy : MirTy}
    {argPairs : List (MirTy × SlotVal)}
    {localsAfterArgs localsAfterDeinit : List LocalSlot}
    {argVals : List Val} {contFuel : Nat}
    (spec : CallSpec p callee)
    (h_caller : Trusted.MirSemantics.getElem? p.bodies frame.defId =
      some callerBody)
    (h_bb : Trusted.MirSemantics.getElem? callerBody.basicBlocks
      frame.blockIdx = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator = .call callee args dst target unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? callerBody.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs callerBody.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_retTy : Trusted.MirSemantics.getElem? spec.calleeBody.locals 0 =
      some calleeRetTy)
    (h_retEq : calleeRetTy = dstTy)
    (h_deinit : deinitPlace localsAfterArgs dst dstTy = .ok localsAfterDeinit)
    (h_val : validateCallArgs argPairs
      ((spec.calleeBody.locals.drop 1).take spec.calleeBody.argumentCount) =
        .ok argVals)
    (h_pre : spec.pre argVals)
    (h_ret : ∀ retVal cm, spec.post argVals retVal cm →
      match applyCallReturn p ⟨dst, target, unwind⟩
          { frame with locals := localsAfterDeinit } callers retVal cm with
      | .step s' => wpOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k)
    (h_unw : ∀ cm, spec.unwindPost argVals cm →
      match unwindFrame cm { frame with locals := localsAfterDeinit } callers
          unwind with
      | .step s' => wpOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k) :
    wpOutcomeState p onDone onFault (spec.fuel + contFuel + 1)
      { frames := frame :: callers, callerMem := callerMem } := by
  refine wpOutcomeState_of_execOutcomeState ?_
  change (match evalStep p 0
      { frames := frame :: callers, callerMem := callerMem } with
    | .step st' => execOutcomeState p onDone onFault (spec.fuel + contFuel) st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [evalStep_call h_caller h_bb h_stmt h_len h_term h_noOverlap h_dstLocal
    h_dstTy h_args spec.h_body spec.h_admitted h_retTy h_retEq h_deinit h_val]
  exact execOutcomeState_of_wpOutcomeState
    (wpOutcomeState_attachState rfl
      (spec.sound argVals callerMem (validateCallArgs_spec h_val).1 h_pre)
      h_ret h_unw)

/-- Deterministic `execOutcomeState` version of `wpCallStep`. -/
theorem execCallStep {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {callerBody : Body} {bb : BasicBlock}
    {frame : FrameState} {callers : List FrameState} {callerMem : CallerMemory}
    {callee : DefId} {args : List Operand} {dst : Place}
    {target : Option BasicBlockId} {unwind : UnwindAction}
    {localTy dstTy calleeRetTy : MirTy}
    {argPairs : List (MirTy × SlotVal)}
    {localsAfterArgs localsAfterDeinit : List LocalSlot}
    {argVals : List Val} {contFuel : Nat}
    (spec : CallSpec p callee)
    (h_caller : Trusted.MirSemantics.getElem? p.bodies frame.defId =
      some callerBody)
    (h_bb : Trusted.MirSemantics.getElem? callerBody.basicBlocks
      frame.blockIdx = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator = .call callee args dst target unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? callerBody.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs callerBody.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_retTy : Trusted.MirSemantics.getElem? spec.calleeBody.locals 0 =
      some calleeRetTy)
    (h_retEq : calleeRetTy = dstTy)
    (h_deinit : deinitPlace localsAfterArgs dst dstTy = .ok localsAfterDeinit)
    (h_val : validateCallArgs argPairs
      ((spec.calleeBody.locals.drop 1).take spec.calleeBody.argumentCount) =
        .ok argVals)
    (h_pre : spec.pre argVals)
    (h_ret : ∀ retVal cm, spec.post argVals retVal cm →
      match applyCallReturn p ⟨dst, target, unwind⟩
          { frame with locals := localsAfterDeinit } callers retVal cm with
      | .step s' => execOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k)
    (h_unw : ∀ cm, spec.unwindPost argVals cm →
      match unwindFrame cm { frame with locals := localsAfterDeinit } callers
          unwind with
      | .step s' => execOutcomeState p onDone onFault contFuel s'
      | .done out => onDone out
      | .fault k => onFault k) :
    execOutcomeState p onDone onFault (spec.fuel + contFuel + 1)
      { frames := frame :: callers, callerMem := callerMem } := by
  refine execOutcomeState_of_wpOutcomeState
    (wpCallStep spec h_caller h_bb h_stmt h_len h_term h_noOverlap h_dstLocal
      h_dstTy h_args h_retTy h_retEq h_deinit h_val h_pre ?_ ?_)
  · intro retVal cm hPost
    have hR := h_ret retVal cm hPost
    cases hApp : applyCallReturn p ⟨dst, target, unwind⟩
        { frame with locals := localsAfterDeinit } callers retVal cm with
    | step s' =>
      rw [hApp] at hR
      exact wpOutcomeState_of_execOutcomeState hR
    | done _ => rw [hApp] at hR; exact hR
    | fault _ => rw [hApp] at hR; exact hR
  · intro cm hPost
    have hU := h_unw cm hPost
    cases hUnwStep : unwindFrame cm { frame with locals := localsAfterDeinit }
        callers unwind with
    | step s' =>
      rw [hUnwStep] at hU
      exact wpOutcomeState_of_execOutcomeState hU
    | done _ => rw [hUnwStep] at hU; exact hU
    | fault _ => rw [hUnwStep] at hU; exact hU

/-- Ergonomic `wpState` call-summary combinator for non-diverging calls
(`target = some nextBb`): after writing `retVal` into `dst` (for any `retVal`
satisfying `spec.post`), continues at `nextBb`, and handles any unwind path via
`h_unw`. -/
theorem wpCallSummary {p : Program} {post : TerminalOut → Prop}
    {callerBody : Body} {bb : BasicBlock} {frame : FrameState}
    {callers : List FrameState} {callerMem : CallerMemory} {callee : DefId}
    {args : List Operand} {dst : Place} {nextBb : BasicBlockId}
    {unwind : UnwindAction} {localTy dstTy calleeRetTy : MirTy}
    {argPairs : List (MirTy × SlotVal)}
    {localsAfterArgs localsAfterDeinit : List LocalSlot}
    {argVals : List Val} {contFuel : Nat}
    (spec : CallSpec p callee)
    (h_caller : Trusted.MirSemantics.getElem? p.bodies frame.defId =
      some callerBody)
    (h_bb : Trusted.MirSemantics.getElem? callerBody.basicBlocks
      frame.blockIdx = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator = .call callee args dst (some nextBb) unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? callerBody.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs callerBody.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_retTy : Trusted.MirSemantics.getElem? spec.calleeBody.locals 0 =
      some calleeRetTy)
    (h_retEq : calleeRetTy = dstTy)
    (h_deinit : deinitPlace localsAfterArgs dst dstTy = .ok localsAfterDeinit)
    (h_val : validateCallArgs argPairs
      ((spec.calleeBody.locals.drop 1).take spec.calleeBody.argumentCount) =
        .ok argVals)
    (h_pre : spec.pre argVals)
    (h_ret : ∀ retVal cm, spec.post argVals retVal cm →
      ∃ localsAfterWrite,
        writePlace localsAfterDeinit dst dstTy retVal = .ok localsAfterWrite ∧
        wpState p contFuel
          {
            frames := {
              frame with
              blockIdx := nextBb
              stmtIdx := 0
              locals := localsAfterWrite
            } :: callers
            callerMem := cm
          }
          post)
    (h_unw : ∀ cm, spec.unwindPost argVals cm →
      match unwindFrame cm { frame with locals := localsAfterDeinit } callers
          unwind with
      | .step s' => wpState p contFuel s' post
      | .done out => post out
      | .fault _ => False) :
    wpState p (spec.fuel + contFuel + 1)
      { frames := frame :: callers, callerMem := callerMem } post := by
  refine wpCallStep spec h_caller h_bb h_stmt h_len h_term h_noOverlap
    h_dstLocal h_dstTy h_args h_retTy h_retEq h_deinit h_val h_pre ?_ h_unw
  intro retVal cm hPost
  let ⟨localsAfterWrite, hWrite, hCont⟩ := h_ret retVal cm hPost
  unfold applyCallReturn
  dsimp only
  rw [h_caller]
  dsimp only
  rw [h_dstLocal]
  dsimp only
  rw [h_dstTy]
  dsimp only
  rw [hWrite]
  exact hCont

/-- Deterministic `execState` version of `wpCallSummary`. -/
theorem execCallSummary {p : Program} {post : TerminalOut → Prop}
    {callerBody : Body} {bb : BasicBlock} {frame : FrameState}
    {callers : List FrameState} {callerMem : CallerMemory} {callee : DefId}
    {args : List Operand} {dst : Place} {nextBb : BasicBlockId}
    {unwind : UnwindAction} {localTy dstTy calleeRetTy : MirTy}
    {argPairs : List (MirTy × SlotVal)}
    {localsAfterArgs localsAfterDeinit : List LocalSlot}
    {argVals : List Val} {contFuel : Nat}
    (spec : CallSpec p callee)
    (h_caller : Trusted.MirSemantics.getElem? p.bodies frame.defId =
      some callerBody)
    (h_bb : Trusted.MirSemantics.getElem? callerBody.basicBlocks
      frame.blockIdx = some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator = .call callee args dst (some nextBb) unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? callerBody.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs callerBody.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_retTy : Trusted.MirSemantics.getElem? spec.calleeBody.locals 0 =
      some calleeRetTy)
    (h_retEq : calleeRetTy = dstTy)
    (h_deinit : deinitPlace localsAfterArgs dst dstTy = .ok localsAfterDeinit)
    (h_val : validateCallArgs argPairs
      ((spec.calleeBody.locals.drop 1).take spec.calleeBody.argumentCount) =
        .ok argVals)
    (h_pre : spec.pre argVals)
    (h_ret : ∀ retVal cm, spec.post argVals retVal cm →
      ∃ localsAfterWrite,
        writePlace localsAfterDeinit dst dstTy retVal = .ok localsAfterWrite ∧
        execState p contFuel
          {
            frames := {
              frame with
              blockIdx := nextBb
              stmtIdx := 0
              locals := localsAfterWrite
            } :: callers
            callerMem := cm
          }
          post)
    (h_unw : ∀ cm, spec.unwindPost argVals cm →
      match unwindFrame cm { frame with locals := localsAfterDeinit } callers
          unwind with
      | .step s' => execState p contFuel s' post
      | .done out => post out
      | .fault _ => False) :
    execState p (spec.fuel + contFuel + 1)
      { frames := frame :: callers, callerMem := callerMem } post := by
  refine execOutcomeState_of_wpOutcomeState
    (wpCallSummary spec h_caller h_bb h_stmt h_len h_term h_noOverlap
      h_dstLocal h_dstTy h_args h_retTy h_retEq h_deinit h_val h_pre ?_ ?_)
  · intro retVal cm hPost
    let ⟨l', hW, hC⟩ := h_ret retVal cm hPost
    exact ⟨l', hW, wpOutcomeState_of_execOutcomeState hC⟩
  · intro cm hPost
    have hU := h_unw cm hPost
    cases hUnwStep : unwindFrame cm { frame with locals := localsAfterDeinit }
        callers unwind with
    | step s' =>
      rw [hUnwStep] at hU
      exact wpOutcomeState_of_execOutcomeState hU
    | done _ => rw [hUnwStep] at hU; exact hU
    | fault _ => rw [hUnwStep] at hU; exact hU

/-- One-step reduction equation for `TerminatorKind.callBuiltin`. -/
theorem evalStep_callBuiltin {p : Program} {body : Body} {bb : BasicBlock}
    {frame : FrameState} {callers : List FrameState} {callerMem : CallerMemory}
    {builtin : CoreBuiltin} {args : List Operand} {dst : Place}
    {nextBb : BasicBlockId} {unwind : UnwindAction} {localTy dstTy : MirTy}
    {argPairs : List (MirTy × SlotVal)} {localsAfterArgs : List LocalSlot}
    {argVals : List Val} {resVal : Val} {localsAfterWrite : List LocalSlot}
    (h_body : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator =
      .callBuiltin builtin args dst (some nextBb) unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs body.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_prim : readPrimitiveArgs argPairs = .ok argVals)
    (h_eval : evalCoreBuiltin builtin argVals = .ok resVal)
    (h_write : writePlace localsAfterArgs dst dstTy resVal =
      .ok localsAfterWrite) :
    evalStep p 0 { frames := frame :: callers, callerMem := callerMem } =
      .step {
        frames := {
          frame with
          blockIdx := nextBb
          stmtIdx := 0
          locals := localsAfterWrite
        } :: callers
        callerMem := callerMem
      } := by
  unfold evalStep evalTerminator jumpToBlock
  dsimp only
  rw [h_body]
  dsimp only
  rw [h_bb]
  dsimp only
  rw [h_stmt]
  dsimp only
  rw [ite_bool_true h_len]
  rw [h_term]
  dsimp only
  rw [ite_bool_false h_noOverlap]
  rw [h_dstLocal]
  dsimp only
  rw [h_dstTy]
  dsimp only
  rw [h_args]
  dsimp only
  rw [h_prim]
  dsimp only
  rw [h_eval]
  dsimp only
  rw [h_write]

/-- Single-step `wpOutcomeState` combinator for `TerminatorKind.callBuiltin`. -/
theorem wpCallBuiltin {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {body : Body} {bb : BasicBlock}
    {frame : FrameState} {callers : List FrameState} {callerMem : CallerMemory}
    {builtin : CoreBuiltin} {args : List Operand} {dst : Place}
    {nextBb : BasicBlockId} {unwind : UnwindAction} {localTy dstTy : MirTy}
    {argPairs : List (MirTy × SlotVal)} {localsAfterArgs : List LocalSlot}
    {argVals : List Val} {resVal : Val} {localsAfterWrite : List LocalSlot}
    {fuel : Nat}
    (h_body : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator =
      .callBuiltin builtin args dst (some nextBb) unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs body.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_prim : readPrimitiveArgs argPairs = .ok argVals)
    (h_eval : evalCoreBuiltin builtin argVals = .ok resVal)
    (h_write : writePlace localsAfterArgs dst dstTy resVal =
      .ok localsAfterWrite)
    (h_cont : wpOutcomeState p onDone onFault fuel {
      frames := {
        frame with
        blockIdx := nextBb
        stmtIdx := 0
        locals := localsAfterWrite
      } :: callers
      callerMem := callerMem
    }) :
    wpOutcomeState p onDone onFault (fuel + 1)
      { frames := frame :: callers, callerMem := callerMem } := by
  refine wpOutcomeState_of_execOutcomeState ?_
  change (match evalStep p 0
      { frames := frame :: callers, callerMem := callerMem } with
    | .step st' => execOutcomeState p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [evalStep_callBuiltin h_body h_bb h_stmt h_len h_term h_noOverlap
    h_dstLocal h_dstTy h_args h_prim h_eval h_write]
  exact execOutcomeState_of_wpOutcomeState h_cont

/-- Deterministic `execOutcomeState` version of `wpCallBuiltin`. -/
theorem execCallBuiltin {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {body : Body} {bb : BasicBlock}
    {frame : FrameState} {callers : List FrameState} {callerMem : CallerMemory}
    {builtin : CoreBuiltin} {args : List Operand} {dst : Place}
    {nextBb : BasicBlockId} {unwind : UnwindAction} {localTy dstTy : MirTy}
    {argPairs : List (MirTy × SlotVal)} {localsAfterArgs : List LocalSlot}
    {argVals : List Val} {resVal : Val} {localsAfterWrite : List LocalSlot}
    {fuel : Nat}
    (h_body : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (h_bb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (h_stmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (h_len : Nat.beq frame.stmtIdx bb.statements.length = true)
    (h_term : bb.terminator =
      .callBuiltin builtin args dst (some nextBb) unwind)
    (h_noOverlap : anyMoveOperandMayOverlapPlace dst args = false)
    (h_dstLocal : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some localTy)
    (h_dstTy : projectTy? localTy dst.projection = some dstTy)
    (h_args : evalCallArgs body.locals frame.locals args =
      .ok (argPairs, localsAfterArgs))
    (h_prim : readPrimitiveArgs argPairs = .ok argVals)
    (h_eval : evalCoreBuiltin builtin argVals = .ok resVal)
    (h_write : writePlace localsAfterArgs dst dstTy resVal =
      .ok localsAfterWrite)
    (h_cont : execOutcomeState p onDone onFault fuel {
      frames := {
        frame with
        blockIdx := nextBb
        stmtIdx := 0
        locals := localsAfterWrite
      } :: callers
      callerMem := callerMem
    }) :
    execOutcomeState p onDone onFault (fuel + 1)
      { frames := frame :: callers, callerMem := callerMem } :=
  execOutcomeState_of_wpOutcomeState
    (wpCallBuiltin h_body h_bb h_stmt h_len h_term h_noOverlap h_dstLocal
      h_dstTy h_args h_prim h_eval h_write
      (wpOutcomeState_of_execOutcomeState h_cont))

end Anneal.MirWp
