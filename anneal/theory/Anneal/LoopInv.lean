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

public section

namespace Anneal.LoopInv

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-!
# CFG Loop-Invariant and Simulation Combinators (`Anneal.LoopInv`)

This untrusted `theory/` module extends the fuel-bounded weakest precondition
of `Anneal.MirWp` with reasoning principles for loops in MIR control-flow
graphs. `wpOutcomeState` requires an execution to terminate within its fuel, so
a proof about a loop whose trip count depends on an input cannot unroll it
step by step. The combinators below prove such loops by induction instead:

1. **Checkpoint Weakest Precondition (`wpUntil`, `execUntil`):** `wpUntil`
   runs a program until it reaches a state satisfying a checkpoint predicate
   `stop`, while still accounting for early termination (`onDone`) and faults
   (`onFault`). Checkpoints compose sequentially (`wpUntil_bind`) and hand over
   to `wpOutcomeState` (`wpUntil_to_wpOutcomeState`), so
   `wellFormed_and_spec_of_wpUntil` derives the trusted `SatisfiesPost` and
   `Behavior` judgments from a checkpoint proof.
2. **Loop-Invariant Induction (`wpLoop_nat`, `wpLoop_nat_exists`,
   `wpLoop_countdown`, `wpLoop_list`, `wpLoop_list_split`,
   `wpLoop_state_exists`):** an invariant that holds at a loop head, together
   with a decreasing `Nat` variant, an index, or a list, yields a checkpoint
   proof for the whole loop. Each iteration may also leave the loop early
   through `onDone`.
3. **Simulation (`wpSim_det`, `wpSim_det_run`, `wpSim_rel`):** a program that
   follows an abstract transition system step by step reaches a state related
   to a final abstract state.
4. **Symbolic Statement Steps and a Countdown Self-Test:** step lemmas that
   expose the stuck `evalBinOp`, `checkVal`, and `evalSwitchBranches` calls of
   a symbolic `evalStep`, closed forms for `u32` increment and decrement, and
   the non-vacuity theorem `countDown_spec`, which proves that a MIR countdown
   loop returns its argument for every `n < 2^32`.
-/

/-! ## Part I: Checkpoint Weakest Precondition (`wpUntil`, `execUntil`) -/

/-- Fuel-bounded weakest precondition up to a checkpoint.

`wpUntil p stop onDone onFault fuel s` holds when every execution of `p` from
`s` reaches a state satisfying `stop` after at most `fuel` steps, unless it
first terminates with an outcome satisfying `onDone` or first faults with a
kind satisfying `onFault`. Running out of fuel is accepted only in a state
that satisfies `stop`.

Like `wpOutcomeState`, the definition uses `@Nat.rec` into `Prop` and keeps the
`ValidChoice`-quantified shape of each step. -/
@[expose] def wpUntil (p : Program) (stop : State → Prop)
    (onDone : TerminalOut → Prop) (onFault : FaultKind → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun st => stop st)
    (fun _ ih st =>
      stop st ∨
      ((∃ c₀ : Choice, ValidChoice p st c₀) ∧
        ∀ c : Choice, ValidChoice p st c →
          match evalStep p c st with
          | .step st' => ih st'
          | .done out => onDone out
          | .fault k => onFault k))
    fuel s

/-- Checkpoint weakest precondition that forbids every fault. -/
abbrev wpUntilOk (p : Program) (stop : State → Prop)
    (onDone : TerminalOut → Prop) (fuel : Nat) (s : State) : Prop :=
  wpUntil p stop onDone (fun _ => False) fuel s

/-- Checkpoint weakest precondition that forbids both early termination and
faults: every execution from `s` reaches a state satisfying `stop` after at
most `fuel` steps. -/
abbrev wpReach (p : Program) (stop : State → Prop) (fuel : Nat)
    (s : State) : Prop :=
  wpUntil p stop (fun _ => False) (fun _ => False) fuel s

/-- Deterministic `c = 0` counterpart of `wpUntil` over `evalStep p 0`. On a
concrete state each step reduces by `rfl`, and `wpUntil_of_execUntil` lifts the
result into `wpUntil`. -/
@[expose] def execUntil (p : Program) (stop : State → Prop)
    (onDone : TerminalOut → Prop) (onFault : FaultKind → Prop)
    (fuel : Nat) (s : State) : Prop :=
  @Nat.rec (fun _ => State → Prop)
    (fun st => stop st)
    (fun _ ih st =>
      stop st ∨
      (match evalStep p 0 st with
        | .step st' => ih st'
        | .done out => onDone out
        | .fault k => onFault k))
    fuel s

/-- Deterministic counterpart of `wpUntilOk`. -/
abbrev execUntilOk (p : Program) (stop : State → Prop)
    (onDone : TerminalOut → Prop) (fuel : Nat) (s : State) : Prop :=
  execUntil p stop onDone (fun _ => False) fuel s

/-- Deterministic counterpart of `wpReach`. -/
abbrev execReach (p : Program) (stop : State → Prop) (fuel : Nat)
    (s : State) : Prop :=
  execUntil p stop (fun _ => False) (fun _ => False) fuel s

/-- Unfold `wpUntil` at fuel `0`: the current state must satisfy `stop`. -/
theorem wpUntil_zero_iff {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s : State} :
    wpUntil p stop onDone onFault 0 s ↔ stop s :=
  Iff.rfl

/-- Unfold `wpUntil` at fuel `fuel + 1`: either the current state satisfies
`stop`, or every admissible step continues, terminates, or faults as allowed. -/
theorem wpUntil_succ_iff {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} :
    wpUntil p stop onDone onFault (fuel + 1) s ↔
      (stop s ∨
        ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
          ∀ c : Choice, ValidChoice p s c →
            match evalStep p c s with
            | .step s' => wpUntil p stop onDone onFault fuel s'
            | .done out => onDone out
            | .fault k => onFault k)) :=
  Iff.rfl

/-- Unfold `execUntil` at fuel `0`. -/
theorem execUntil_zero_iff {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s : State} :
    execUntil p stop onDone onFault 0 s ↔ stop s :=
  Iff.rfl

/-- Unfold `execUntil` at fuel `fuel + 1`. -/
theorem execUntil_succ_iff {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} :
    execUntil p stop onDone onFault (fuel + 1) s ↔
      (stop s ∨
        (match evalStep p 0 s with
          | .step s' => execUntil p stop onDone onFault fuel s'
          | .done out => onDone out
          | .fault k => onFault k)) :=
  Iff.rfl

/-- Unfold `wpOutcomeState` at fuel `fuel + 1`. -/
theorem wpOutcomeState_succ_iff {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} :
    wpOutcomeState p onDone onFault (fuel + 1) s ↔
      ((∃ c₀ : Choice, ValidChoice p s c₀) ∧
        ∀ c : Choice, ValidChoice p s c →
          match evalStep p c s with
          | .step s' => wpOutcomeState p onDone onFault fuel s'
          | .done out => onDone out
          | .fault k => onFault k) :=
  Iff.rfl

/-- Transport `wpUntil` along an equation between fuel budgets. -/
theorem wpUntil_fuel_cast {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {a b : Nat} {s : State} (hEq : a = b)
    (h : wpUntil p stop onDone onFault a s) :
    wpUntil p stop onDone onFault b s := by
  subst hEq
  exact h

/-- Transport `wpOutcomeState` along an equation between fuel budgets. -/
theorem wpOutcomeState_fuel_cast {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {a b : Nat} {s : State} (hEq : a = b)
    (h : wpOutcomeState p onDone onFault a s) :
    wpOutcomeState p onDone onFault b s := by
  subst hEq
  exact h

/-- A state that already satisfies `stop` satisfies `wpUntil` at every fuel. -/
theorem wpUntil_stop {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} (h : stop s) :
    wpUntil p stop onDone onFault fuel s := by
  cases fuel with
  | zero => exact wpUntil_zero_iff.mpr h
  | succ fuel => exact wpUntil_succ_iff.mpr (Or.inl h)

/-- Single-step introduction rule for `wpUntil`. Because `ValidChoice` admits
only the choice `0`, it suffices to consider the step `evalStep p 0 s`. -/
theorem wpUntil_step {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : match evalStep p 0 s with
      | .step s' => wpUntil p stop onDone onFault fuel s'
      | .done out => onDone out
      | .fault k => onFault k) :
    wpUntil p stop onDone onFault (fuel + 1) s := by
  refine wpUntil_succ_iff.mpr (Or.inr ⟨⟨0, rfl⟩, fun c hc => ?_⟩)
  subst hc
  exact h

/-- Extend `wpUntil` backwards across one step `evalStep p 0 s = .step s'`. -/
theorem wpUntil_step_eq {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStep p 0 s = .step s')
    (h : wpUntil p stop onDone onFault fuel s') :
    wpUntil p stop onDone onFault (fuel + 1) s := by
  refine wpUntil_step ?_
  rw [hStep]
  exact h

/-- A step that terminates with an accepted outcome satisfies `wpUntil`. -/
theorem wpUntil_done_eq {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStep p 0 s = .done out) (h : onDone out) :
    wpUntil p stop onDone onFault (fuel + 1) s := by
  refine wpUntil_step ?_
  rw [hStep]
  exact h

/-- A step that faults with an accepted kind satisfies `wpUntil`. -/
theorem wpUntil_fault_eq {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {k : FaultKind}
    (hStep : evalStep p 0 s = .fault k) (h : onFault k) :
    wpUntil p stop onDone onFault (fuel + 1) s := by
  refine wpUntil_step ?_
  rw [hStep]
  exact h

/-- Single-step introduction rule for `wpOutcomeState` over `evalStep p 0`. -/
theorem wpOutcomeState_step {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : match evalStep p 0 s with
      | .step s' => wpOutcomeState p onDone onFault fuel s'
      | .done out => onDone out
      | .fault k => onFault k) :
    wpOutcomeState p onDone onFault (fuel + 1) s := by
  refine wpOutcomeState_succ_iff.mpr ⟨⟨0, rfl⟩, fun c hc => ?_⟩
  subst hc
  exact h

/-- Extend `wpOutcomeState` backwards across one step
`evalStep p 0 s = .step s'`. -/
theorem wpOutcomeState_step_eq {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStep p 0 s = .step s')
    (h : wpOutcomeState p onDone onFault fuel s') :
    wpOutcomeState p onDone onFault (fuel + 1) s := by
  refine wpOutcomeState_step ?_
  rw [hStep]
  exact h

/-- A step that terminates with an accepted outcome satisfies
`wpOutcomeState`. -/
theorem wpOutcomeState_done_eq {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStep p 0 s = .done out) (h : onDone out) :
    wpOutcomeState p onDone onFault (fuel + 1) s := by
  refine wpOutcomeState_step ?_
  rw [hStep]
  exact h

/-- A step that faults with an accepted kind satisfies `wpOutcomeState`. -/
theorem wpOutcomeState_fault_eq {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {k : FaultKind}
    (hStep : evalStep p 0 s = .fault k) (h : onFault k) :
    wpOutcomeState p onDone onFault (fuel + 1) s := by
  refine wpOutcomeState_step ?_
  rw [hStep]
  exact h

/-- Exact equivalence between `ValidChoice`-quantified `wpUntil` and the
deterministic `c = 0` fast path `execUntil`. As in
`wpOutcomeState_iff_execOutcomeState`, the proof uses that `ValidChoice` admits
exactly the choice `0`. -/
theorem wpUntil_iff_execUntil {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : State},
      wpUntil p stop onDone onFault fuel s ↔
      execUntil p stop onDone onFault fuel s
  | 0, _ => Iff.rfl
  | fuel + 1, s => by
    constructor
    · intro h
      refine execUntil_succ_iff.mpr ?_
      cases wpUntil_succ_iff.mp h with
      | inl hs => exact Or.inl hs
      | inr hr =>
        refine Or.inr ?_
        have h0 := hr.2 0 rfl
        cases hStep : evalStep p 0 s with
        | step st' =>
          rw [hStep] at h0
          exact wpUntil_iff_execUntil.mp h0
        | done out =>
          rw [hStep] at h0
          exact h0
        | fault k =>
          rw [hStep] at h0
          exact h0
    · intro h
      refine wpUntil_succ_iff.mpr ?_
      cases execUntil_succ_iff.mp h with
      | inl hs => exact Or.inl hs
      | inr hr =>
        refine Or.inr ⟨⟨0, rfl⟩, fun c hc => ?_⟩
        subst hc
        cases hStep : evalStep p 0 s with
        | step st' =>
          rw [hStep] at hr
          exact wpUntil_iff_execUntil.mpr hr
        | done out =>
          rw [hStep] at hr
          exact hr
        | fault k =>
          rw [hStep] at hr
          exact hr

/-- Lift a deterministic `execUntil` derivation into `wpUntil`. -/
theorem wpUntil_of_execUntil {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : execUntil p stop onDone onFault fuel s) :
    wpUntil p stop onDone onFault fuel s :=
  wpUntil_iff_execUntil.mpr h

/-- Project `wpUntil` onto the deterministic `c = 0` fast path. -/
theorem execUntil_of_wpUntil {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h : wpUntil p stop onDone onFault fuel s) :
    execUntil p stop onDone onFault fuel s :=
  wpUntil_iff_execUntil.mp h

/-- Lift a deterministic `execUntilOk` derivation into `wpUntilOk`. -/
theorem wpUntilOk_of_execUntilOk {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {fuel : Nat} {s : State}
    (h : execUntilOk p stop onDone fuel s) :
    wpUntilOk p stop onDone fuel s :=
  wpUntil_of_execUntil h

/-- Lift a deterministic `execReach` derivation into `wpReach`. -/
theorem wpReach_of_execReach {p : Program} {stop : State → Prop}
    {fuel : Nat} {s : State}
    (h : execReach p stop fuel s) :
    wpReach p stop fuel s :=
  wpUntil_of_execUntil h

/-- Rule of consequence for `wpUntil`: weaken the checkpoint, the terminal
postcondition, and the set of accepted faults. -/
theorem wpUntil_mono {p : Program} {stop₁ stop₂ : State → Prop}
    {onDone₁ onDone₂ : TerminalOut → Prop}
    {onFault₁ onFault₂ : FaultKind → Prop}
    (hStop : ∀ s, stop₁ s → stop₂ s)
    (hDone : ∀ out, onDone₁ out → onDone₂ out)
    (hFault : ∀ k, onFault₁ k → onFault₂ k) :
    ∀ {fuel : Nat} {s : State},
      wpUntil p stop₁ onDone₁ onFault₁ fuel s →
      wpUntil p stop₂ onDone₂ onFault₂ fuel s
  | 0, s, h => wpUntil_zero_iff.mpr (hStop s (wpUntil_zero_iff.mp h))
  | fuel + 1, s, h => by
    refine wpUntil_succ_iff.mpr ?_
    cases wpUntil_succ_iff.mp h with
    | inl hs => exact Or.inl (hStop s hs)
    | inr hr =>
      refine Or.inr ⟨hr.1, fun c hc => ?_⟩
      have hc' := hr.2 c hc
      cases hStep : evalStep p c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntil_mono hStop hDone hFault hc'
      | done out =>
        rw [hStep] at hc'
        exact hDone out hc'
      | fault k =>
        rw [hStep] at hc'
        exact hFault k hc'

/-- Fuel weakening: reaching the checkpoint within `fuel₁` steps implies
reaching it within any larger budget `fuel₂ ≥ fuel₁`. -/
theorem wpUntil_fuel_mono {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel₁ fuel₂ : Nat} {s : State},
      fuel₁ ≤ fuel₂ →
      wpUntil p stop onDone onFault fuel₁ s →
      wpUntil p stop onDone onFault fuel₂ s
  | 0, _, _, _, h => wpUntil_stop (wpUntil_zero_iff.mp h)
  | fuel₁ + 1, 0, _, hLe, _ =>
    False.elim (Nat.not_succ_le_zero fuel₁ hLe)
  | fuel₁ + 1, fuel₂ + 1, s, hLe, h => by
    have hLe' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hLe
    refine wpUntil_succ_iff.mpr ?_
    cases wpUntil_succ_iff.mp h with
    | inl hs => exact Or.inl hs
    | inr hr =>
      refine Or.inr ⟨hr.1, fun c hc => ?_⟩
      have hc' := hr.2 c hc
      cases hStep : evalStep p c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntil_fuel_mono hLe' hc'
      | done out =>
        rw [hStep] at hc'
        exact hc'
      | fault k =>
        rw [hStep] at hc'
        exact hc'

/-- Sequential composition of checkpoints with the budget written as
`f₂ + f₁`, the form in which the fuel of the first segment recurses
structurally. `wpUntil_bind` states the same rule with budget `f₁ + f₂`. -/
theorem wpUntil_bind_rev {p : Program} {mid stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {f₂ : Nat}
    (hK : ∀ s', mid s' → wpUntil p stop onDone onFault f₂ s') :
    ∀ {f₁ : Nat} {s : State},
      wpUntil p mid onDone onFault f₁ s →
      wpUntil p stop onDone onFault (f₂ + f₁) s
  | 0, s, h =>
    wpUntil_fuel_cast (Nat.add_zero f₂).symm
      (hK s (wpUntil_zero_iff.mp h))
  | f₁ + 1, s, h => by
    cases wpUntil_succ_iff.mp h with
    | inl hm =>
      exact wpUntil_fuel_mono (Nat.le_add_right f₂ (f₁ + 1)) (hK s hm)
    | inr hr =>
      refine wpUntil_fuel_cast (Nat.add_assoc f₂ f₁ 1)
        (wpUntil_succ_iff.mpr (Or.inr ⟨hr.1, fun c hc => ?_⟩))
      have hc' := hr.2 c hc
      cases hStep : evalStep p c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntil_bind_rev hK hc'
      | done out =>
        rw [hStep] at hc'
        exact hc'
      | fault k =>
        rw [hStep] at hc'
        exact hc'

/-- Sequential composition of checkpoints: if `s` reaches `mid` within `f₁`
steps and every `mid` state reaches `stop` within `f₂` steps, then `s` reaches
`stop` within `f₁ + f₂` steps. -/
theorem wpUntil_bind {p : Program} {mid stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {f₁ f₂ : Nat} {s : State}
    (h : wpUntil p mid onDone onFault f₁ s)
    (hK : ∀ s', mid s' → wpUntil p stop onDone onFault f₂ s') :
    wpUntil p stop onDone onFault (f₁ + f₂) s :=
  wpUntil_fuel_cast (Nat.add_comm f₂ f₁) (wpUntil_bind_rev hK h)

private theorem wpUntil_bind_exists_aux {p : Program}
    {mid stop : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop}
    (hK : ∀ s', mid s' → ∃ f₂, wpUntil p stop onDone onFault f₂ s')
    {f₁ : Nat} {s : State}
    (h : wpUntil p mid onDone onFault f₁ s) :
    ∃ F, wpUntil p stop onDone onFault F s := by
  induction f₁ generalizing s with
  | zero => exact hK s (wpUntil_zero_iff.mp h)
  | succ f ih =>
    cases wpUntil_succ_iff.mp h with
    | inl hm => exact hK s hm
    | inr hr =>
      have h0 := hr.2 0 rfl
      cases hStep : evalStep p 0 s with
      | step st' =>
        rw [hStep] at h0
        let ⟨F, hF⟩ := ih h0
        exact ⟨F + 1, wpUntil_step_eq hStep hF⟩
      | done out =>
        rw [hStep] at h0
        exact ⟨0 + 1, wpUntil_done_eq hStep h0⟩
      | fault k =>
        rw [hStep] at h0
        exact ⟨0 + 1, wpUntil_fault_eq hStep h0⟩

/-- Sequential composition of checkpoints with existential fuel: the budget of
the second segment may depend on the intermediate state. The proof follows the
single execution from `s`, which is unique because `ValidChoice` admits only
the choice `0`. -/
theorem wpUntil_bind_exists {p : Program} {mid stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s : State}
    (h : ∃ f₁, wpUntil p mid onDone onFault f₁ s)
    (hK : ∀ s', mid s' → ∃ f₂, wpUntil p stop onDone onFault f₂ s') :
    ∃ F, wpUntil p stop onDone onFault F s := by
  let ⟨_, h₁⟩ := h
  exact wpUntil_bind_exists_aux hK h₁

/-- Hand a checkpoint proof over to `wpOutcomeState`, with the budget written
as `f₂ + f₁` (see `wpUntil_bind_rev`). -/
theorem wpUntil_to_wpOutcomeState_rev {p : Program}
    {stop : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {f₂ : Nat}
    (hK : ∀ s', stop s' → wpOutcomeState p onDone onFault f₂ s') :
    ∀ {f₁ : Nat} {s : State},
      wpUntil p stop onDone onFault f₁ s →
      wpOutcomeState p onDone onFault (f₂ + f₁) s
  | 0, s, h =>
    wpOutcomeState_fuel_cast (Nat.add_zero f₂).symm
      (hK s (wpUntil_zero_iff.mp h))
  | f₁ + 1, s, h => by
    cases wpUntil_succ_iff.mp h with
    | inl hs =>
      exact wpOutcomeState_fuel_mono (Nat.le_add_right f₂ (f₁ + 1))
        (hK s hs)
    | inr hr =>
      refine wpOutcomeState_fuel_cast (Nat.add_assoc f₂ f₁ 1)
        (wpOutcomeState_succ_iff.mpr ⟨hr.1, fun c hc => ?_⟩)
      have hc' := hr.2 c hc
      cases hStep : evalStep p c s with
      | step st' =>
        rw [hStep] at hc'
        exact wpUntil_to_wpOutcomeState_rev hK hc'
      | done out =>
        rw [hStep] at hc'
        exact hc'
      | fault k =>
        rw [hStep] at hc'
        exact hc'

/-- Hand a checkpoint proof over to `wpOutcomeState`: if `s` reaches `stop`
within `f₁` steps and every `stop` state terminates within `f₂` steps, then
`s` terminates within `f₁ + f₂` steps. -/
theorem wpUntil_to_wpOutcomeState {p : Program} {stop : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {f₁ f₂ : Nat} {s : State}
    (h : wpUntil p stop onDone onFault f₁ s)
    (hK : ∀ s', stop s' → wpOutcomeState p onDone onFault f₂ s') :
    wpOutcomeState p onDone onFault (f₁ + f₂) s :=
  wpOutcomeState_fuel_cast (Nat.add_comm f₂ f₁)
    (wpUntil_to_wpOutcomeState_rev hK h)

private theorem wpUntil_to_wpOutcomeState_exists_aux {p : Program}
    {stop : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop}
    (hK : ∀ s', stop s' → ∃ f₂, wpOutcomeState p onDone onFault f₂ s')
    {f₁ : Nat} {s : State}
    (h : wpUntil p stop onDone onFault f₁ s) :
    ∃ F, wpOutcomeState p onDone onFault F s := by
  induction f₁ generalizing s with
  | zero => exact hK s (wpUntil_zero_iff.mp h)
  | succ f ih =>
    cases wpUntil_succ_iff.mp h with
    | inl hs => exact hK s hs
    | inr hr =>
      have h0 := hr.2 0 rfl
      cases hStep : evalStep p 0 s with
      | step st' =>
        rw [hStep] at h0
        let ⟨F, hF⟩ := ih h0
        exact ⟨F + 1, wpOutcomeState_step_eq hStep hF⟩
      | done out =>
        rw [hStep] at h0
        exact ⟨0 + 1, wpOutcomeState_done_eq hStep h0⟩
      | fault k =>
        rw [hStep] at h0
        exact ⟨0 + 1, wpOutcomeState_fault_eq hStep h0⟩

/-- Hand a checkpoint proof over to `wpOutcomeState` with existential fuel:
the termination budget may depend on the checkpoint state. -/
theorem wpUntil_to_wpOutcomeState_exists {p : Program}
    {stop : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {s : State}
    (h : ∃ f₁, wpUntil p stop onDone onFault f₁ s)
    (hK : ∀ s', stop s' → ∃ f₂, wpOutcomeState p onDone onFault f₂ s') :
    ∃ F, wpOutcomeState p onDone onFault F s := by
  let ⟨_, h₁⟩ := h
  exact wpUntil_to_wpOutcomeState_exists_aux hK h₁

/-- Hand a fault-free checkpoint proof over to `wpState` with existential
fuel. -/
theorem wpUntil_to_wpState_exists {p : Program} {stop : State → Prop}
    {post : TerminalOut → Prop} {s : State}
    (h : ∃ f₁, wpUntilOk p stop post f₁ s)
    (hK : ∀ s', stop s' → ∃ f₂, wpState p f₂ s' post) :
    ∃ F, wpState p F s post :=
  wpUntil_to_wpOutcomeState_exists h hK

/-- Adequacy of the checkpoint weakest precondition. If `initState p q`
succeeds with `s₀`, every execution from `s₀` reaches the checkpoint `stop`
(or returns an outcome satisfying `post`) without faulting, and every `stop`
state terminates with an outcome satisfying `post`, then `(p, q)` satisfies
the trusted contract `SatisfiesPost p q post` (which includes `WellFormed p q`)
and has a terminating behavior that satisfies `post`. -/
theorem wellFormed_and_spec_of_wpUntil {p : Program} {q : Query}
    {stop : State → Prop} {post : TerminalOut → Prop} {f₁ : Nat}
    {s₀ : State}
    (hInit : initState p q = .ok s₀)
    (hWp : wpUntilOk p stop post f₁ s₀)
    (hK : ∀ s', stop s' → ∃ f₂, wpState p f₂ s' post) :
    SatisfiesPost p q post ∧ ∃ out, Behavior p q out ∧ post out := by
  let ⟨F, hF⟩ :=
    wpUntil_to_wpState_exists (p := p) (stop := stop) (post := post)
      (s := s₀) ⟨f₁, hWp⟩ hK
  let ⟨hSat, _, hEx⟩ := wellFormed_and_spec_of_wp p q F post (by
    unfold wpProg
    rw [hInit]
    exact hF)
  exact ⟨hSat, hEx⟩

/-- `WellFormed` corollary of `wellFormed_and_spec_of_wpUntil`. -/
theorem wellFormed_of_wpUntil {p : Program} {q : Query}
    {stop : State → Prop} {post : TerminalOut → Prop} {f₁ : Nat}
    {s₀ : State}
    (hInit : initState p q = .ok s₀)
    (hWp : wpUntilOk p stop post f₁ s₀)
    (hK : ∀ s', stop s' → ∃ f₂, wpState p f₂ s' post) :
    WellFormed p q :=
  (wellFormed_and_spec_of_wpUntil hInit hWp hK).1.1

/-! ## Part II: Loop-Invariant Induction Combinators -/

/-- Fixed-budget `Nat`-variant loop rule for any bound `n` on the variant.

`Inv` holds at the loop head, `rank` is the variant, and `Exit` describes the
states that leave the loop. Each iteration starts in an `Inv` state that is
not yet an `Exit` state, has a positive variant, and within `stepFuel` steps
reaches either an `Inv` state with a strictly smaller variant or an `Exit`
state. Then every `Inv` state with `rank s ≤ n` reaches `Exit` within
`n * stepFuel` steps. -/
theorem wpLoop_nat_le {p : Program} {Inv Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {rank : State → Nat} {stepFuel : Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧
        wpUntil p (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault stepFuel s)) :
    ∀ (n : Nat) (s : State), Inv s → rank s ≤ n →
      wpUntil p Exit onDone onFault (n * stepFuel) s := by
  intro n
  induction n with
  | zero =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact wpUntil_stop hExit
    | inr hIter =>
      exact False.elim
        (Nat.not_lt_zero 0 (Nat.lt_of_lt_of_le hIter.1 hLe))
  | succ n ih =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact wpUntil_stop hExit
    | inr hIter =>
      have hK : ∀ s', ((Inv s' ∧ rank s' < rank s) ∨ Exit s') →
          wpUntil p Exit onDone onFault (n * stepFuel) s' := by
        intro s' hMid
        cases hMid with
        | inl hCont =>
          exact ih s' hCont.1
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hCont.2 hLe))
        | inr hExit' => exact wpUntil_stop hExit'
      exact wpUntil_fuel_cast (Nat.succ_mul n stepFuel).symm
        (wpUntil_bind_rev
          (mid := fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          hK hIter.2)

/-- Fixed-budget `Nat`-variant loop rule: under the hypotheses of
`wpLoop_nat_le`, every `Inv` state `s` reaches `Exit` within
`rank s * stepFuel` steps. -/
theorem wpLoop_nat {p : Program} {Inv Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {rank : State → Nat} {stepFuel : Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧
        wpUntil p (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault stepFuel s))
    (s : State) (hInv : Inv s) :
    wpUntil p Exit onDone onFault (rank s * stepFuel) s :=
  wpLoop_nat_le hStep (rank s) s hInv (Nat.le_refl (rank s))

private theorem wpLoop_nat_exists_aux {p : Program}
    {Inv Exit : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rank : State → Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧ ∃ f,
        wpUntil p (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault f s)) :
    ∀ (n : Nat) (s : State), Inv s → rank s ≤ n →
      ∃ F, wpUntil p Exit onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact ⟨0, wpUntil_stop hExit⟩
    | inr hIter =>
      exact False.elim
        (Nat.not_lt_zero 0 (Nat.lt_of_lt_of_le hIter.1 hLe))
  | succ n ih =>
    intro s hInv hLe
    cases hStep s hInv with
    | inl hExit => exact ⟨0, wpUntil_stop hExit⟩
    | inr hIter =>
      refine wpUntil_bind_exists
        (mid := fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
        hIter.2 ?_
      intro s' hMid
      cases hMid with
      | inl hCont =>
        exact ih s' hCont.1
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hCont.2 hLe))
      | inr hExit' => exact ⟨0, wpUntil_stop hExit'⟩

/-- Variable-budget `Nat`-variant loop rule: as `wpLoop_nat`, but each
iteration may take a different number of steps, so the conclusion provides
some total budget `F`. -/
theorem wpLoop_nat_exists {p : Program} {Inv Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {rank : State → Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧ ∃ f,
        wpUntil p (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault f s))
    (s : State) (hInv : Inv s) :
    ∃ F, wpUntil p Exit onDone onFault F s :=
  wpLoop_nat_exists_aux hStep (rank s) s hInv (Nat.le_refl (rank s))

/-- Exact countdown loop rule with variable budget. The invariant `Inv n`
records that exactly `n` iterations remain: `Inv 0` implies `Exit`, and one
iteration from `Inv (n + 1)` reaches `Inv n` or `Exit`. -/
theorem wpLoop_countdown {p : Program} {Inv : Nat → State → Prop}
    {Exit : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop}
    (hBase : ∀ s, Inv 0 s → Exit s)
    (hStep : ∀ n s, Inv (n + 1) s →
      ∃ f, wpUntil p (fun s' => Inv n s' ∨ Exit s') onDone onFault f s) :
    ∀ (n : Nat) (s : State), Inv n s →
      ∃ F, wpUntil p Exit onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro s hInv
    exact ⟨0, wpUntil_stop (hBase s hInv)⟩
  | succ n ih =>
    intro s hInv
    refine wpUntil_bind_exists
      (mid := fun s' => Inv n s' ∨ Exit s') (hStep n s hInv) ?_
    intro s' hMid
    cases hMid with
    | inl hCont => exact ih s' hCont
    | inr hExit => exact ⟨0, wpUntil_stop hExit⟩

/-- Exact countdown loop rule with a fixed budget of `stepFuel` steps per
iteration: an `Inv n` state reaches `Exit` within `n * stepFuel` steps. -/
theorem wpLoop_countdown_fuel {p : Program} {Inv : Nat → State → Prop}
    {Exit : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {stepFuel : Nat}
    (hBase : ∀ s, Inv 0 s → Exit s)
    (hStep : ∀ n s, Inv (n + 1) s →
      wpUntil p (fun s' => Inv n s' ∨ Exit s') onDone onFault stepFuel s) :
    ∀ (n : Nat) (s : State), Inv n s →
      wpUntil p Exit onDone onFault (n * stepFuel) s := by
  intro n
  induction n with
  | zero =>
    intro s hInv
    exact wpUntil_stop (hBase s hInv)
  | succ n ih =>
    intro s hInv
    have hK : ∀ s', (Inv n s' ∨ Exit s') →
        wpUntil p Exit onDone onFault (n * stepFuel) s' := by
      intro s' hMid
      cases hMid with
      | inl hCont => exact ih s' hCont
      | inr hExit => exact wpUntil_stop hExit
    exact wpUntil_fuel_cast (Nat.succ_mul n stepFuel).symm
      (wpUntil_bind_rev (mid := fun s' => Inv n s' ∨ Exit s') hK
        (hStep n s hInv))

/-- List-traversal loop rule. The invariant `Inv xs` records the elements that
remain to be processed: `Inv []` implies `Exit`, and one iteration from
`Inv (x :: xs)` reaches `Inv xs` or `Exit`. -/
theorem wpLoop_list {α : Type} {p : Program}
    {Inv : List α → State → Prop} {Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ x xs s, Inv (x :: xs) s →
      ∃ f, wpUntil p (fun s' => Inv xs s' ∨ Exit s') onDone onFault f s) :
    ∀ (xs : List α) (s : State), Inv xs s →
      ∃ F, wpUntil p Exit onDone onFault F s := by
  intro xs
  induction xs with
  | nil =>
    intro s hInv
    exact ⟨0, wpUntil_stop (hBase s hInv)⟩
  | cons x xs ih =>
    intro s hInv
    refine wpUntil_bind_exists
      (mid := fun s' => Inv xs s' ∨ Exit s') (hStep x xs s hInv) ?_
    intro s' hMid
    cases hMid with
    | inl hCont => exact ih s' hCont
    | inr hExit => exact ⟨0, wpUntil_stop hExit⟩

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

private theorem wpLoop_list_measure_aux {α : Type} {p : Program}
    {Inv : List α → State → Prop} {Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      ∃ f, wpUntil p
        (fun s' => (∃ ys, ys.length < xs.length ∧ Inv ys s') ∨ Exit s')
        onDone onFault f s) :
    ∀ (n : Nat) (xs : List α) (s : State), Inv xs s → xs.length ≤ n →
      ∃ F, wpUntil p Exit onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro xs s hInv hLe
    cases xs with
    | nil => exact ⟨0, wpUntil_stop (hBase s hInv)⟩
    | cons x rest =>
      exact False.elim (Nat.not_succ_le_zero rest.length hLe)
  | succ n ih =>
    intro xs s hInv hLe
    cases xs with
    | nil => exact ⟨0, wpUntil_stop (hBase s hInv)⟩
    | cons x rest =>
      have hNe : x :: rest ≠ [] := by
        intro hEq
        cases hEq
      refine wpUntil_bind_exists
        (mid := fun s' =>
          (∃ ys, ys.length < (x :: rest).length ∧ Inv ys s') ∨ Exit s')
        (hStep (x :: rest) s hInv hNe) ?_
      intro s' hMid
      cases hMid with
      | inl hCont =>
        let ⟨ys, hLt, hInvYs⟩ := hCont
        exact ih ys s' hInvYs
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hLe))
      | inr hExit => exact ⟨0, wpUntil_stop hExit⟩

/-- List loop rule by length: each iteration from a non-empty `Inv xs` state
reaches an `Inv ys` state for some strictly shorter list `ys`, or `Exit`. -/
theorem wpLoop_list_measure {α : Type} {p : Program}
    {Inv : List α → State → Prop} {Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      ∃ f, wpUntil p
        (fun s' => (∃ ys, ys.length < xs.length ∧ Inv ys s') ∨ Exit s')
        onDone onFault f s)
    (xs : List α) (s : State) (hInv : Inv xs s) :
    ∃ F, wpUntil p Exit onDone onFault F s :=
  wpLoop_list_measure_aux (Inv := Inv) (Exit := Exit) hBase hStep
    xs.length xs s hInv (Nat.le_refl xs.length)

/-- Chunked list-traversal loop rule: each iteration from a non-empty `Inv xs`
state consumes some non-empty prefix `pre` of `xs = pre ++ rest` and reaches
`Inv rest`, or reaches `Exit`. This covers loops that process a variable
number of elements per iteration. -/
theorem wpLoop_list_split {α : Type} {p : Program}
    {Inv : List α → State → Prop} {Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    (hBase : ∀ s, Inv [] s → Exit s)
    (hStep : ∀ xs s, Inv xs s → xs ≠ [] →
      ∃ f, wpUntil p
        (fun s' =>
          (∃ pre rest, xs = pre ++ rest ∧ pre ≠ [] ∧ Inv rest s') ∨
            Exit s')
        onDone onFault f s)
    (xs : List α) (s : State) (hInv : Inv xs s) :
    ∃ F, wpUntil p Exit onDone onFault F s := by
  refine wpLoop_list_measure (Inv := Inv) (Exit := Exit) hBase ?_ xs s hInv
  intro ys t hInvYs hNe
  let ⟨f, hf⟩ := hStep ys t hInvYs hNe
  refine ⟨f, wpUntil_mono ?_ (fun _ h => h) (fun _ h => h) hf⟩
  intro t' hMid
  cases hMid with
  | inl hSplit =>
    let ⟨pre, rest, hEq, hPre, hInvRest⟩ := hSplit
    subst hEq
    have hGoal :
        (∃ zs, zs.length < (pre ++ rest).length ∧ Inv zs t') ∨ Exit t' :=
      Or.inl ⟨rest, length_lt_append_of_ne_nil pre rest hPre, hInvRest⟩
    exact hGoal
  | inr hExit =>
    have hGoal :
        (∃ zs, zs.length < ys.length ∧ Inv zs t') ∨ Exit t' :=
      Or.inr hExit
    exact hGoal

/-- Breakable `Nat`-variant loop rule: the loop of `wpLoop_nat_exists`,
followed by a terminating continuation from every `Exit` state, terminates.
An iteration may also end the execution directly through `onDone` (for
example an early `return` inside a validation loop). -/
theorem wpLoop_nat_or_done {p : Program} {Inv Exit : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {rank : State → Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧ ∃ f,
        wpUntil p (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          onDone onFault f s))
    (hExit : ∀ s, Exit s → ∃ f, wpOutcomeState p onDone onFault f s)
    (s : State) (hInv : Inv s) :
    ∃ F, wpOutcomeState p onDone onFault F s :=
  wpUntil_to_wpOutcomeState_exists (wpLoop_nat_exists hStep s hInv) hExit

/-- Fault-free specialization of `wpLoop_nat_or_done` that returns a `wpState`
proof with postcondition `post`. -/
theorem wpLoop_state_exists {p : Program} {Inv Exit : State → Prop}
    {post : TerminalOut → Prop} {rank : State → Nat}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (0 < rank s ∧ ∃ f,
        wpUntilOk p (fun s' => (Inv s' ∧ rank s' < rank s) ∨ Exit s')
          post f s))
    (hExit : ∀ s, Exit s → ∃ f, wpState p f s post)
    (s : State) (hInv : Inv s) :
    ∃ F, wpState p F s post :=
  wpLoop_nat_or_done hStep hExit s hInv

/-! ## Part III: Simulation Combinators -/

/-- Reflexive-transitive closure of an abstract step relation. -/
inductive ReflTrans {α : Type} (step : α → α → Prop) : α → α → Prop where
  | refl (a : α) : ReflTrans step a a
  | head {a b c : α} :
      step a b → ReflTrans step b c → ReflTrans step a c

private theorem wpSim_rel_aux {α : Type} {p : Program}
    {StepAbs : α → α → Prop} {DoneAbs : α → Prop}
    {R : α → State → Prop} {Exit : α → State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (DoneAbs a ∧ Exit a s) ∨
      (∃ a', StepAbs a a' ∧ rank a' < rank a ∧
        ∃ f, wpUntil p (fun s' => R a' s') onDone onFault f s)) :
    ∀ (n : Nat) (a : α) (s : State), R a s → rank a ≤ n →
      ∃ F, wpUntil p
        (fun s' => ∃ a', ReflTrans StepAbs a a' ∧ DoneAbs a' ∧ Exit a' s')
        onDone onFault F s := by
  intro n
  induction n with
  | zero =>
    intro a s hR hLe
    cases hSim a s hR with
    | inl hDone =>
      have hStop :
          ∃ a', ReflTrans StepAbs a a' ∧ DoneAbs a' ∧ Exit a' s :=
        ⟨a, ReflTrans.refl a, hDone.1, hDone.2⟩
      exact ⟨0, wpUntil_stop hStop⟩
    | inr hNext =>
      let ⟨a', _, hLt, _⟩ := hNext
      exact False.elim
        (Nat.not_lt_zero (rank a') (Nat.lt_of_lt_of_le hLt hLe))
  | succ n ih =>
    intro a s hR hLe
    cases hSim a s hR with
    | inl hDone =>
      have hStop :
          ∃ a', ReflTrans StepAbs a a' ∧ DoneAbs a' ∧ Exit a' s :=
        ⟨a, ReflTrans.refl a, hDone.1, hDone.2⟩
      exact ⟨0, wpUntil_stop hStop⟩
    | inr hNext =>
      let ⟨a', hAbs, hLt, hIter⟩ := hNext
      refine wpUntil_bind_exists (mid := fun s' => R a' s') hIter ?_
      intro s' hR'
      let ⟨F, hF⟩ := ih a' s' hR'
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hLe))
      refine ⟨F, wpUntil_mono ?_ (fun _ h => h) (fun _ h => h) hF⟩
      intro t hStop
      let ⟨aF, hRT, hD, hE⟩ := hStop
      have hGoal :
          ∃ a'', ReflTrans StepAbs a a'' ∧ DoneAbs a'' ∧ Exit a'' t :=
        ⟨aF, ReflTrans.head hAbs hRT, hD, hE⟩
      exact hGoal

/-- Relational simulation rule. `R` relates abstract states to program states
and `rank` decreases along abstract steps. If every related pair is either
finished (`DoneAbs` and `Exit`) or admits an abstract step whose target the
program reaches again in relation `R`, then the program reaches an `Exit`
state for some finished abstract state reachable from the initial one. -/
theorem wpSim_rel {α : Type} {p : Program}
    {StepAbs : α → α → Prop} {DoneAbs : α → Prop}
    {R : α → State → Prop} {Exit : α → State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (DoneAbs a ∧ Exit a s) ∨
      (∃ a', StepAbs a a' ∧ rank a' < rank a ∧
        ∃ f, wpUntil p (fun s' => R a' s') onDone onFault f s))
    (a : α) (s : State) (hR : R a s) :
    ∃ F, wpUntil p
      (fun s' => ∃ a', ReflTrans StepAbs a a' ∧ DoneAbs a' ∧ Exit a' s')
      onDone onFault F s :=
  wpSim_rel_aux hSim (rank a) a s hR (Nat.le_refl (rank a))

/-- Iterate the abstract step function `stepAbs` at most `k` times, stopping
at the first state where it returns `none`. -/
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

private theorem wpSim_det_aux {α : Type} {p : Program}
    {stepAbs : α → Option α} {R : α → State → Prop}
    {Exit : α → State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        ∃ f, wpUntil p (fun s' => R a' s') onDone onFault f s)) :
    ∀ (n : Nat) (a : α) (s : State), R a s → rank a ≤ n →
      ∃ F, wpUntil p
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
      have hStop : ∃ k, k ≤ 0 ∧
          stepAbs (runAbsFuel stepAbs k a) = none ∧
          R (runAbsFuel stepAbs k a) s ∧
          Exit (runAbsFuel stepAbs k a) s :=
        ⟨0, Nat.le_refl 0, hOpt, hR, (hSim a s hR).1 hOpt⟩
      exact ⟨0, wpUntil_stop hStop⟩
    | some a' =>
      exact False.elim
        (Nat.not_lt_zero (rank a')
          (Nat.lt_of_lt_of_le ((hSim a s hR).2 a' hOpt).1 hLe))
  | succ n ih =>
    intro a s hR hLe
    cases hOpt : stepAbs a with
    | none =>
      have hStop : ∃ k, k ≤ n + 1 ∧
          stepAbs (runAbsFuel stepAbs k a) = none ∧
          R (runAbsFuel stepAbs k a) s ∧
          Exit (runAbsFuel stepAbs k a) s :=
        ⟨0, Nat.zero_le (n + 1), hOpt, hR, (hSim a s hR).1 hOpt⟩
      exact ⟨0, wpUntil_stop hStop⟩
    | some a' =>
      have hNext := (hSim a s hR).2 a' hOpt
      refine wpUntil_bind_exists (mid := fun s' => R a' s') hNext.2 ?_
      intro s' hR'
      let ⟨F, hF⟩ := ih a' s' hR'
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hNext.1 hLe))
      refine ⟨F, wpUntil_mono ?_ (fun _ h => h) (fun _ h => h) hF⟩
      intro t hStop
      let ⟨k, hk, hNone, hRk, hEk⟩ := hStop
      have hRun :
          runAbsFuel stepAbs (k + 1) a = runAbsFuel stepAbs k a' :=
        runAbsFuel_succ_of_some hOpt k
      have hGoal : ∃ j, j ≤ n + 1 ∧
          stepAbs (runAbsFuel stepAbs j a) = none ∧
          R (runAbsFuel stepAbs j a) t ∧
          Exit (runAbsFuel stepAbs j a) t := by
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_, ?_, ?_⟩
        · rw [hRun]
          exact hNone
        · rw [hRun]
          exact hRk
        · rw [hRun]
          exact hEk
      exact hGoal

/-- Deterministic simulation rule with an exact abstract run. `stepAbs` is an
abstract step function whose result `none` means that the abstract machine has
halted, `R` relates abstract states to program states, and `rank` decreases
along abstract steps. If a halted related pair satisfies `Exit` and the
program follows every abstract step, then from any related pair the program
reaches a state related to `runAbsFuel stepAbs k a` for some `k ≤ rank a` at
which the abstract machine has halted. -/
theorem wpSim_det_run {α : Type} {p : Program}
    {stepAbs : α → Option α} {R : α → State → Prop}
    {Exit : α → State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        ∃ f, wpUntil p (fun s' => R a' s') onDone onFault f s))
    (a : α) (s : State) (hR : R a s) :
    ∃ F, wpUntil p
      (fun s' => ∃ k, k ≤ rank a ∧
        stepAbs (runAbsFuel stepAbs k a) = none ∧
        R (runAbsFuel stepAbs k a) s' ∧
        Exit (runAbsFuel stepAbs k a) s')
      onDone onFault F s :=
  wpSim_det_aux hSim (rank a) a s hR (Nat.le_refl (rank a))

/-- Deterministic simulation rule: under the hypotheses of `wpSim_det_run`,
the program reaches a state related to some halted abstract state. -/
theorem wpSim_det {α : Type} {p : Program}
    {stepAbs : α → Option α} {R : α → State → Prop}
    {Exit : α → State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rank : α → Nat}
    (hSim : ∀ a s, R a s →
      (stepAbs a = none → Exit a s) ∧
      (∀ a', stepAbs a = some a' →
        rank a' < rank a ∧
        ∃ f, wpUntil p (fun s' => R a' s') onDone onFault f s))
    (a : α) (s : State) (hR : R a s) :
    ∃ F, wpUntil p
      (fun s' => ∃ aFinal,
        stepAbs aFinal = none ∧ R aFinal s' ∧ Exit aFinal s')
      onDone onFault F s := by
  let ⟨F, hF⟩ := wpSim_det_run hSim a s hR
  refine ⟨F, wpUntil_mono ?_ (fun _ h => h) (fun _ h => h) hF⟩
  intro t hStop
  let ⟨k, _, hNone, hRk, hEk⟩ := hStop
  have hGoal :
      ∃ aFinal, stepAbs aFinal = none ∧ R aFinal t ∧ Exit aFinal t :=
    ⟨runAbsFuel stepAbs k a, hNone, hRk, hEk⟩
  exact hGoal

/-! ## Part IV: Symbolic Statement Steps and a Countdown Self-Test

On a state that holds a symbolic scalar, `evalStep` does not reduce by `rfl`:
it is stuck on the overflow test inside `evalBinOp`, on the `checkVal` guard of
`writePlace`, and on the comparison inside `evalSwitchBranches`. The lemmas in
this part take the results of exactly these calls as hypotheses, so that every
other part of a step still reduces by `rfl`. -/

/-- Evaluate `Rvalue.binaryOp` from the values of its operands and the result
of `evalBinOp`. -/
theorem evalRvalue_binaryOp {tys : List MirTy}
    {ls ls₁ ls₂ : List LocalSlot} {m m₁ m₂ : MemoryState} {dstTy : MirTy}
    {op : BinOp} {lhs rhs : Operand} {lVal rVal res : Val}
    (hL : evalPrimitiveOperand tys ls m lhs = .ok (lVal, ls₁, m₁))
    (hR : evalPrimitiveOperand tys ls₁ m₁ rhs = .ok (rVal, ls₂, m₂))
    (hOp : evalBinOp op lVal rVal = .ok res) :
    evalRvalue tys ls m dstTy (.binaryOp op lhs rhs) =
      .ok (res, ls₂, m₂) := by
  unfold evalRvalue
  dsimp only
  rw [hL]
  dsimp only
  rw [hR]
  dsimp only
  rw [hOp]

/-- Step an assignment of a binary operation from the result of `evalRvalue`
and the result of `writePlace`. -/
theorem evalStatement_assign_binaryOp {body : Body} {frame : FrameState}
    {m m₁ m₂ : MemoryState} {cm : CallerMemory} {dst : Place} {op : BinOp}
    {lhs rhs : Operand} {dstTy : MirTy} {val : Val}
    {ls ls' : List LocalSlot}
    (hProj : dst.projection.isEmpty = true)
    (hLoc : Trusted.MirSemantics.getElem? body.locals dst.localId =
      some dstTy)
    (hRv : evalRvalue body.locals frame.locals m dstTy
      (.binaryOp op lhs rhs) = .ok (val, ls, m₁))
    (hW : writePlace ls m₁ dst.localId dstTy val = .ok (ls', m₂)) :
    evalStatement body frame m cm (.assign dst (.binaryOp op lhs rhs)) =
      .step {
        frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := ls' }]
        callerMem := cm
        mem := m₂
      } := by
  have hNotProj : (!dst.projection.isEmpty) = false := by
    rw [hProj]
    rfl
  unfold evalStatement
  dsimp only
  rw [ite_bool_false hNotProj, hLoc]
  dsimp only
  rw [hRv]
  dsimp only
  rw [hW]

/-- Step a `switchInt` terminator on a scalar discriminant from the result of
`evalSwitchBranches`. -/
theorem evalTerminator_switchInt_scalar {body : Body} {bb : BasicBlock}
    {frame : FrameState} {m m₁ : MemoryState} {cm : CallerMemory}
    {discr : Operand} {targets : SwitchTargets} {sv : ScalarVal}
    {ls : List LocalSlot} {target : BasicBlockId}
    (hTerm : bb.terminator = .switchInt discr targets)
    (hDiscr : evalPrimitiveOperand body.locals frame.locals m discr =
      .ok (.scalar sv, ls, m₁))
    (hSw : evalSwitchBranches sv.width sv.bits targets.otherwise
      targets.branches = .ok target) :
    evalTerminator body bb frame m cm =
      jumpToBlock { frame with locals := ls } m₁ cm target := by
  unfold evalTerminator
  rw [hTerm]
  dsimp only
  rw [hDiscr]
  dsimp only
  rw [hSw]

/-- A single-branch `switchInt` takes the `otherwise` target when the
discriminant differs from the branch value. -/
theorem evalSwitchBranches_single_ne {w : IntWidth}
    {discr caseBits : BitVec 128} {target otherwise : BasicBlockId}
    (hCase : (truncateBits w caseBits != caseBits) = false)
    (hNe : (truncateBits w discr == truncateBits w caseBits) = false) :
    evalSwitchBranches w discr otherwise [(caseBits, target)] =
      .ok otherwise := by
  first
    | exact (ite_bool_false hCase).trans
        ((ite_bool_false hNe).trans rfl)
    | (unfold evalSwitchBranches
       repeat (dsimp only)
       exact (ite_bool_false hCase).trans
         ((ite_bool_false hNe).trans rfl))
    | (unfold evalSwitchBranches
       exact (ite_bool_false hCase).trans
         ((ite_bool_false hNe).trans rfl))

/-- Explicit closed-form equation for unsigned wrapping `.sub` across all six
`IntWidth` variants, the counterpart of `evalBinOp_unsigned_add`. -/
theorem evalBinOp_unsigned_sub (w : IntWidth) (b₁ b₂ : BitVec 128) :
    evalBinOp .sub (.scalar ⟨w, false, b₁⟩) (.scalar ⟨w, false, b₂⟩) =
      .ok (.scalar ⟨w, false,
        truncateBits w (bvOfInt 128
          (decodeScalar ⟨w, false, b₁⟩ - decodeScalar ⟨w, false, b₂⟩))⟩) := by
  have hGuard : (!(IntWidth.beq w w && (false == false))) = false := by
    rw [IntWidth.beq_iff.mpr rfl]
    rfl
  unfold evalBinOp evalArithOp truncateScalar
  dsimp only
  rw [ite_bool_false (rfl : BinOp.sub.isShift = false)]
  rw [ite_bool_false hGuard]
  exact ite_bool_false (and_isUnchecked_false rfl)

/-- `BitVec.ofNat 128 m` lies below the `u32` modulus when `m` does. -/
theorem toNat_ofNat_lt_u32 {m : Nat} (hm : m < Nat.pow 2 32) :
    (BitVec.ofNat 128 m).toNat < Nat.pow 2 IntWidth.i32.bitWidth := by
  change Nat.mod m (Nat.pow 2 128) < Nat.pow 2 IntWidth.i32.bitWidth
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hm

/-- `BitVec.ofNat 128 m` has value `m` when `m` fits in 32 bits. -/
theorem toNat_ofNat_u32 {m : Nat} (hm : m < Nat.pow 2 32) :
    (BitVec.ofNat 128 m).toNat = m :=
  Nat.mod_eq_of_lt (Nat.lt_trans hm (by decide))

/-- `truncateBits .i32` fixes `BitVec.ofNat 128 m` when `m` fits in 32 bits. -/
theorem truncateBits_u32_ofNat {m : Nat} (hm : m < Nat.pow 2 32) :
    truncateBits .i32 (BitVec.ofNat 128 m) = BitVec.ofNat 128 m :=
  truncateBits_of_toNat_lt (toNat_ofNat_lt_u32 hm)

/-- `u32Val m` is a well-typed `u32` value when `m` fits in 32 bits. -/
theorem checkVal_u32Val {m : Nat} (hm : m < Nat.pow 2 32) :
    checkVal (u32Val m) u32Ty = true :=
  checkVal_scalar_of_toNat_lt (w := .i32) (s := false)
    (x := BitVec.ofNat 128 m) (toNat_ofNat_lt_u32 hm)

/-- The `u32` scalar with payload `BitVec.ofNat 128 m` decodes to `m`. -/
theorem decodeScalar_u32_ofNat {m : Nat} (hm : m < Nat.pow 2 32) :
    decodeScalar ⟨.i32, false, BitVec.ofNat 128 m⟩ = Int.ofNat m := by
  change Int.ofNat (truncateBits .i32 (BitVec.ofNat 128 m)).toNat =
    Int.ofNat m
  rw [truncateBits_u32_ofNat hm, toNat_ofNat_u32 hm]

/-- Wrapping a natural number that fits in 32 bits to `u32` is the identity. -/
theorem truncateBits_u32_bvOfInt {t : Nat} (ht : t < Nat.pow 2 32) :
    truncateBits .i32 (bvOfInt 128 (Int.ofNat t)) = BitVec.ofNat 128 t := by
  have hMod : Nat.mod t (Nat.pow 2 128) = t :=
    Nat.mod_eq_of_lt (Nat.lt_trans ht (by decide))
  first
    | (unfold bvOfInt intEmod
       dsimp only [Int.natAbs, Int.toNat]
       rw [hMod]
       exact truncateBits_u32_ofNat ht)
    | (change truncateBits .i32
         (BitVec.ofNat 128 (Nat.mod t (Nat.pow 2 128))) =
         BitVec.ofNat 128 t
       rw [hMod]
       exact truncateBits_u32_ofNat ht)

/-- Subtracting one from a positive natural number, computed in `Int`. -/
theorem int_ofNat_succ_sub_one (k : Nat) :
    Int.ofNat (k + 1) - Int.ofNat 1 = Int.ofNat k := by
  have hZero : 1 - (k + 1) = 0 :=
    (@Nat.succ_sub_succ 0 k).trans
      (Nat.eq_zero_of_le_zero (Nat.sub_le 0 k))
  change Int.subNatNat (k + 1) 1 = Int.ofNat k
  unfold Int.subNatNat
  cases hRem : 1 - (k + 1) with
  | zero =>
    first
      | rfl
      | exact congrArg Int.ofNat (@Nat.add_sub_cancel k 1)
  | succ r =>
    rw [hZero] at hRem
    first
      | cases hRem
      | exact Nat.noConfusion hRem

/-- Decrementing a positive `u32` value does not wrap. -/
theorem evalBinOp_sub_u32 {k : Nat} (hk : k + 1 < Nat.pow 2 32) :
    evalBinOp .sub (u32Val (k + 1)) (u32Val 1) = .ok (u32Val k) := by
  have hk' : k < Nat.pow 2 32 := Nat.lt_trans (Nat.lt_succ_self k) hk
  have h1 : (1 : Nat) < Nat.pow 2 32 := by decide
  have hBits :
      truncateBits .i32 (bvOfInt 128
        (decodeScalar ⟨.i32, false, BitVec.ofNat 128 (k + 1)⟩ -
          decodeScalar ⟨.i32, false, BitVec.ofNat 128 1⟩)) =
        BitVec.ofNat 128 k := by
    rw [decodeScalar_u32_ofNat hk, decodeScalar_u32_ofNat h1,
      int_ofNat_succ_sub_one k]
    exact truncateBits_u32_bvOfInt hk'
  exact (evalBinOp_unsigned_sub .i32 (BitVec.ofNat 128 (k + 1))
    (BitVec.ofNat 128 1)).trans
    (congrArg
      (fun (b : BitVec 128) =>
        (Except.ok (Val.scalar ⟨.i32, false, b⟩) : Except FaultKind Val))
      hBits)

/-- Incrementing a `u32` value below `u32::MAX` does not wrap. -/
theorem evalBinOp_add_u32 {a : Nat} (ha : a + 1 < Nat.pow 2 32) :
    evalBinOp .add (u32Val a) (u32Val 1) = .ok (u32Val (a + 1)) := by
  have ha' : a < Nat.pow 2 32 := Nat.lt_trans (Nat.lt_succ_self a) ha
  have h1 : (1 : Nat) < Nat.pow 2 32 := by decide
  have hBits :
      truncateBits .i32 (bvOfInt 128
        (decodeScalar ⟨.i32, false, BitVec.ofNat 128 a⟩ +
          decodeScalar ⟨.i32, false, BitVec.ofNat 128 1⟩)) =
        BitVec.ofNat 128 (a + 1) := by
    rw [decodeScalar_u32_ofNat ha', decodeScalar_u32_ofNat h1]
    exact truncateBits_u32_bvOfInt ha
  exact (evalBinOp_unsigned_add .i32 (BitVec.ofNat 128 a)
    (BitVec.ofNat 128 1)).trans
    (congrArg
      (fun (b : BitVec 128) =>
        (Except.ok (Val.scalar ⟨.i32, false, b⟩) : Except FaultKind Val))
      hBits)

/-- A positive `u32` payload differs from the zero payload. -/
theorem ofNat_succ_ne_zero_u32 {k : Nat} (hk : k + 1 < Nat.pow 2 32) :
    ¬ BitVec.ofNat 128 (k + 1) = BitVec.ofNat 128 0 := by
  intro hEq
  have hNat :
      (BitVec.ofNat 128 (k + 1)).toNat = (BitVec.ofNat 128 0).toNat :=
    congrArg BitVec.toNat hEq
  have hR : (BitVec.ofNat 128 0).toNat = 0 := rfl
  rw [toNat_ofNat_u32 hk, hR] at hNat
  first
    | cases hNat
    | exact Nat.noConfusion hNat

/-- The `switchInt` comparison of a positive `u32` payload against zero is
`false`. -/
theorem switch_beq_false_u32 {k : Nat} (hk : k + 1 < Nat.pow 2 32) :
    (truncateBits .i32 (BitVec.ofNat 128 (k + 1)) ==
      truncateBits .i32 (BitVec.ofNat 128 0)) = false := by
  rw [truncateBits_u32_ofNat hk,
    truncateBits_u32_ofNat (by decide : 0 < Nat.pow 2 32)]
  exact decide_eq_false (ofNat_succ_ne_zero_u32 hk)

/-! ### Countdown Self-Test

The program below is the MIR of

```
fn count_down(mut n: u32) -> u32 {
    let mut acc = 0;
    while n != 0 { n -= 1; acc += 1; }
    acc
}
```

with `_0` as the accumulator and `_1` as the counter. Its loop consists of the
header `bb1` and the body `bb2`. `countDown_spec` proves for every `n < 2^32`
that the program is well-formed and returns `n`. The proof applies
`wpLoop_countdown` to the loop and `wellFormed_and_spec_of_wpUntil` to the
whole execution, which shows that the combinators of this module apply to a
`Trusted.MirAst.Program` with a symbolic trip count. -/

/-- Computable alias for `Trusted.MirSemantics.u32Ty`. -/
abbrev countDownU32Ty : MirTy := .int .i32 false

/-- Immediate `u32` local slot holding `m`. -/
@[expose] def u32Slot (m : Nat) : LocalSlot :=
  .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 m⟩))

/-- Frame of body `0` at block `b` and statement `i` with locals `ls`. -/
@[expose] def frameAt (b i : Nat) (ls : List LocalSlot) : FrameState :=
  { defId := 0, blockIdx := b, stmtIdx := i, locals := ls }

/-- Entry block `bb0`: `_0 = const 0_u32; goto bb1`. -/
@[expose] def countDownEntry : BasicBlock := {
  statements := [
    .assign ⟨0, []⟩
      (.use (.constant ⟨countDownU32Ty, .scalar (BitVec.ofNat 128 0)⟩))
  ]
  terminator := .goto 1
}

/-- Loop header `bb1`: `switchInt(copy _1) -> [0: bb3, otherwise: bb2]`. -/
@[expose] def countDownHeader : BasicBlock := {
  statements := []
  terminator := .switchInt (.copy ⟨1, []⟩) {
    branches := [(BitVec.ofNat 128 0, 3)]
    otherwise := 2
  }
}

/-- Decrement statement `_1 = Sub(copy _1, const 1_u32)`. -/
@[expose] def countDownDec : StatementKind :=
  .assign ⟨1, []⟩
    (.binaryOp .sub (.copy ⟨1, []⟩)
      (.constant ⟨countDownU32Ty, .scalar (BitVec.ofNat 128 1)⟩))

/-- Increment statement `_0 = Add(copy _0, const 1_u32)`. -/
@[expose] def countDownInc : StatementKind :=
  .assign ⟨0, []⟩
    (.binaryOp .add (.copy ⟨0, []⟩)
      (.constant ⟨countDownU32Ty, .scalar (BitVec.ofNat 128 1)⟩))

/-- Loop body `bb2`: decrement `_1`, increment `_0`, and `goto bb1`. -/
@[expose] def countDownLoop : BasicBlock := {
  statements := [countDownDec, countDownInc]
  terminator := .goto 1
}

/-- Exit block `bb3`: `return`. -/
@[expose] def countDownExit : BasicBlock := {
  statements := []
  terminator := .return_
}

/-- Body of `fn count_down(n: u32) -> u32`. -/
@[expose] def countDownBody : Body := {
  argumentCount := 1
  locals := [countDownU32Ty, countDownU32Ty]
  basicBlocks :=
    [countDownEntry, countDownHeader, countDownLoop, countDownExit]
  identity := "count_down"
}

/-- Single-body program for `count_down`. -/
@[expose] def countDownProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [countDownBody]
}

/-- Loop-header state with accumulator `acc` and counter `k`. Uses the
computable literal `{ nextAllocId := 2, allocations := [] }` (definitionally
equal to `entryMemory`) so `countDownAt` remains computable. -/
@[expose] def countDownAt (acc k : Nat) : State :=
  mkState 1 0 [u32Slot acc, u32Slot k] 0
    { nextAllocId := 2, allocations := [] }

/-- Loop invariant for argument `n` with `k` iterations remaining: the
execution is at the loop header and the accumulator and the counter sum to
`n`. -/
@[expose] def countDownInv (n k : Nat) (s : State) : Prop :=
  ∃ acc, acc + k = n ∧ s = countDownAt acc k

/-- Loop exit for argument `n`: the loop header with counter `0` and
accumulator `n`. -/
@[expose] def countDownDone (n : Nat) (s : State) : Prop :=
  s = countDownAt n 0

/-- Postcondition for argument `n`: the program returns `n`. -/
@[expose] def countDownPost (n : Nat) (out : TerminalOut) : Prop :=
  out = .returned ⟨u32Val n, ⟨[]⟩⟩

/-- A `u32` argument below `2^32` is a valid entry argument. -/
theorem countDown_validArgs {n : Nat} (hn : n < Nat.pow 2 32) :
    ValidEntryArgs countDownBody [u32Val n] :=
  (checkArgsMatch_cons_iff (args := [u32Val n]) (ty := u32Ty)
    (tys := [])).mpr ⟨u32Val n, [], rfl, checkVal_u32Val hn, rfl⟩

/-- Entry state of `count_down` on argument `n`. -/
theorem countDown_initState {n : Nat} (hn : n < Nat.pow 2 32) :
    initState countDownProg { args := [u32Val n] } =
      .ok (mkState 0 0 [.immediate none, u32Slot n]) :=
  initState_eq_ok (body := countDownBody) rfl rfl (countDown_validArgs hn)

/-- Entry step: `_0 = const 0_u32`. -/
theorem countDown_step_init (n : Nat) :
    evalStep countDownProg 0 (mkState 0 0 [.immediate none, u32Slot n]) =
      .step (mkState 0 1 [u32Slot 0, u32Slot n]) :=
  rfl

/-- Entry step: `goto bb1`. -/
theorem countDown_step_enter (n : Nat) :
    evalStep countDownProg 0 (mkState 0 1 [u32Slot 0, u32Slot n]) =
      .step (countDownAt 0 n) :=
  rfl

/-- Header step with a positive counter: `switchInt` enters the loop body. -/
theorem countDown_step_switch (acc : Nat) {k : Nat}
    (hk : k + 1 < Nat.pow 2 32) :
    evalStep countDownProg 0 (countDownAt acc (k + 1)) =
      .step (mkState 2 0 [u32Slot acc, u32Slot (k + 1)]) := by
  have hSw : evalSwitchBranches .i32 (BitVec.ofNat 128 (k + 1)) 2
      [(BitVec.ofNat 128 0, 3)] = .ok 2 :=
    evalSwitchBranches_single_ne rfl (switch_beq_false_u32 hk)
  have hTerm : evalTerminator countDownBody countDownHeader
      (frameAt 1 0 [u32Slot acc, u32Slot (k + 1)]) entryMemory ⟨[]⟩ =
      jumpToBlock (frameAt 1 0 [u32Slot acc, u32Slot (k + 1)])
        entryMemory ⟨[]⟩ 2 :=
    evalTerminator_switchInt_scalar
      (discr := .copy ⟨1, []⟩)
      (targets := { branches := [(BitVec.ofNat 128 0, 3)], otherwise := 2 })
      (sv := ⟨.i32, false, BitVec.ofNat 128 (k + 1)⟩)
      (ls := [u32Slot acc, u32Slot (k + 1)])
      (m₁ := entryMemory) rfl rfl hSw
  exact hTerm

/-- Body step: `_1 = Sub(copy _1, const 1_u32)` on a positive counter. -/
theorem countDown_step_dec (acc : Nat) {k : Nat}
    (hk : k + 1 < Nat.pow 2 32) :
    evalStep countDownProg 0
        (mkState 2 0 [u32Slot acc, u32Slot (k + 1)]) =
      .step (mkState 2 1 [u32Slot acc, u32Slot k]) := by
  have hk' : k < Nat.pow 2 32 := Nat.lt_trans (Nat.lt_succ_self k) hk
  have hChk : checkVal (u32Val k) u32Ty = true := checkVal_u32Val hk'
  have hRv : evalRvalue countDownBody.locals
      [u32Slot acc, u32Slot (k + 1)] entryMemory u32Ty
      (.binaryOp .sub (.copy ⟨1, []⟩)
        (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)) =
      .ok (u32Val k, [u32Slot acc, u32Slot (k + 1)], entryMemory) :=
    evalRvalue_binaryOp (lVal := u32Val (k + 1)) (rVal := u32Val 1)
      (ls₁ := [u32Slot acc, u32Slot (k + 1)])
      (m₁ := entryMemory) rfl rfl
      (evalBinOp_sub_u32 hk)
  have hW : writePlace [u32Slot acc, u32Slot (k + 1)] entryMemory 1 u32Ty
      (u32Val k) = .ok ([u32Slot acc, u32Slot k], entryMemory) := by
    unfold writePlace
    cases hC : checkVal (u32Val k) u32Ty with
    | false =>
      rw [hC] at hChk
      cases hChk
    | true => rfl
  have hStmt : evalStatement countDownBody
      (frameAt 2 0 [u32Slot acc, u32Slot (k + 1)]) entryMemory ⟨[]⟩
      countDownDec =
      .step (mkState 2 1 [u32Slot acc, u32Slot k]) :=
    evalStatement_assign_binaryOp (dstTy := u32Ty) rfl rfl hRv hW
  exact hStmt

/-- Body step: `_0 = Add(copy _0, const 1_u32)` below `u32::MAX`. -/
theorem countDown_step_inc (acc k : Nat) (hAcc : acc + 1 < Nat.pow 2 32) :
    evalStep countDownProg 0 (mkState 2 1 [u32Slot acc, u32Slot k]) =
      .step (mkState 2 2 [u32Slot (acc + 1), u32Slot k]) := by
  have hChk : checkVal (u32Val (acc + 1)) u32Ty = true :=
    checkVal_u32Val hAcc
  have hRv : evalRvalue countDownBody.locals
      [u32Slot acc, u32Slot k] entryMemory u32Ty
      (.binaryOp .add (.copy ⟨0, []⟩)
        (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩)) =
      .ok (u32Val (acc + 1), [u32Slot acc, u32Slot k], entryMemory) :=
    evalRvalue_binaryOp (lVal := u32Val acc) (rVal := u32Val 1)
      (ls₁ := [u32Slot acc, u32Slot k])
      (m₁ := entryMemory) rfl rfl
      (evalBinOp_add_u32 hAcc)
  have hW : writePlace [u32Slot acc, u32Slot k] entryMemory 0 u32Ty
      (u32Val (acc + 1)) =
      .ok ([u32Slot (acc + 1), u32Slot k], entryMemory) := by
    unfold writePlace
    cases hC : checkVal (u32Val (acc + 1)) u32Ty with
    | false =>
      rw [hC] at hChk
      cases hChk
    | true => rfl
  have hStmt : evalStatement countDownBody
      (frameAt 2 1 [u32Slot acc, u32Slot k]) entryMemory ⟨[]⟩ countDownInc =
      .step (mkState 2 2 [u32Slot (acc + 1), u32Slot k]) :=
    evalStatement_assign_binaryOp (dstTy := u32Ty) rfl rfl hRv hW
  exact hStmt

/-- Body step: `goto bb1` returns to the loop header. -/
theorem countDown_step_goto (acc k : Nat) :
    evalStep countDownProg 0 (mkState 2 2 [u32Slot acc, u32Slot k]) =
      .step (countDownAt acc k) :=
  rfl

/-- With no iterations remaining, the invariant is the loop exit. -/
theorem countDown_base (n : Nat) (s : State) (h : countDownInv n 0 s) :
    countDownDone n s := by
  let ⟨acc, hAcc, hs⟩ := h
  subst hs
  subst hAcc
  exact rfl

/-- One loop iteration: from the invariant with `k + 1` iterations remaining,
four steps reach the invariant with `k` iterations remaining. -/
theorem countDown_iter {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} (n : Nat) (hn : n < Nat.pow 2 32)
    (k : Nat) (s : State) (h : countDownInv n (k + 1) s) :
    ∃ f, wpUntil countDownProg
      (fun s' => countDownInv n k s' ∨ countDownDone n s')
      onDone onFault f s := by
  let ⟨acc, hAcc, hs⟩ := h
  subst hs
  subst hAcc
  have hk : k + 1 < Nat.pow 2 32 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left (k + 1) acc) hn
  have hAcc1 : acc + 1 < Nat.pow 2 32 :=
    Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) acc) hn
  have hNext :
      countDownInv (acc + (k + 1)) k (countDownAt (acc + 1) k) :=
    ⟨acc + 1,
      (Nat.add_assoc acc 1 k).trans
        (congrArg (fun m => acc + m) (Nat.add_comm 1 k)),
      rfl⟩
  exact ⟨0 + 1 + 1 + 1 + 1,
    wpUntil_step_eq (countDown_step_switch acc hk)
      (wpUntil_step_eq (countDown_step_dec acc hk)
        (wpUntil_step_eq (countDown_step_inc acc k hAcc1)
          (wpUntil_step_eq (countDown_step_goto (acc + 1) k)
            (wpUntil_stop (Or.inl hNext)))))⟩

/-- From the loop exit, `switchInt` leaves the loop and `return` yields `n`. -/
theorem countDown_exit (n : Nat) (s : State) (h : countDownDone n s) :
    ∃ f, wpState countDownProg f s (countDownPost n) := by
  subst h
  exact ⟨2, wpOutcomeState_of_execOutcomeState rfl⟩

/-- Non-vacuity self-test: for every `n < 2^32`, `count_down` on argument `n`
satisfies the postcondition "returns `n`" and has a terminating behavior that
returns `n`. The trip count of the loop is the symbolic `n`. -/
theorem countDown_spec (n : Nat) (hn : n < Nat.pow 2 32) :
    SatisfiesPost countDownProg { args := [u32Val n] } (countDownPost n) ∧
      ∃ out, Behavior countDownProg { args := [u32Val n] } out ∧
        countDownPost n out := by
  let ⟨F, hF⟩ :=
    wpLoop_countdown (p := countDownProg) (Inv := countDownInv n)
      (Exit := countDownDone n) (onDone := countDownPost n)
      (onFault := fun _ => False) (countDown_base n)
      (countDown_iter n hn) n (countDownAt 0 n)
      ⟨0, Nat.zero_add n, rfl⟩
  exact wellFormed_and_spec_of_wpUntil (countDown_initState hn)
    (wpUntil_step_eq (countDown_step_init n)
      (wpUntil_step_eq (countDown_step_enter n) hF))
    (countDown_exit n)

/-- Non-vacuity self-test in `PositiveCanaryClaim` form: for every `n < 2^32`,
`count_down` on argument `n` is `WellFormed` and returns `n`. -/
theorem countDown_returns (n : Nat) (hn : n < Nat.pow 2 32) :
    PositiveCanaryClaim countDownProg { args := [u32Val n] } (u32Val n) := by
  let ⟨hSat, _, hBeh, hOut⟩ := countDown_spec n hn
  subst hOut
  exact ⟨hSat.1, hBeh⟩

end Anneal.LoopInv

end
