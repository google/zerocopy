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
public import Anneal.InitLemmas
public import Anneal.MirWp.Core
public import Anneal.CnfOrd.Ord
public import Anneal.CnfOrd.Worklist
public import Anneal.StepBound.Core

public section

/-!
# Ordinal (`CnfOrd`) & Reactive Step-Budget Bridges (`CnfOrdBridge`)

Bridges `Anneal.CnfOrd` (`< ω^ω` Cantor Normal Form ordinals and admissible
worklists) to Profile v2 quantitative step bounds in `Anneal.StepBound`:

- **Two-tier bounded-reset `ω^1 · outer + ω^0 · inner` (`cnfLex2`,
  `lex2Bound`, `v2_loop_lex2_bounded_reset`):** Exact closed-form quadratic
  step ceiling `o * (resetCap * kInner + kOuter) + i * kInner + kExit` for
  nested outer/inner loops where outer decrements reset the inner loop counter
  up to `resetCap`, paired with `CnfOrd` ordinal descent proofs.
- **Constructive `< ω^ω` step-budget extraction (`v2_loop_cnfOrd_exists`,
  `execWithinStepsV2_of_cnfOrd`):** Structural recursion over `CnfAcc` yields an
  explicit `Nat` step-bound `B` satisfying `ExecWithinStepsV2`, `WellFormedV2`,
  `¬ DivergesV2`, and `SatisfiesPostV2` for any well-ranked loop.
- **Abstract transition & worklist bridges (`v2_steps_of_cnfStepConverges`,
  `v2_steps_of_cnfStep_terminates`, `v2_steps_of_worklist_converges`,
  `v2_steps_of_worklist_terminates`):** Lift `CnfStepConverges` and
  `PolicyAdmissible` `WorklistPool` traces to MIR `ReachesDoneWithinV2`.
- **Reactive prefix contracts (`ReactiveStepContractV2`):** Step-bounded
  per-frame / per-event progress (`1 ≤ k ≤ frameBound` per tick or clean exit)
  for streaming / event-loop MIR kernels.
-/

namespace Anneal.StepBound

open Trusted.MirAst Trusted.MirSemantics
open Anneal.InitLemmas Anneal.MirWp Anneal.CnfOrd

/-! ## 1. Canonical Two-Term Ordinals (`ω^1 · outer + ω^0 · inner`) -/

/-- Canonical `CnfOrd` encoding `ω^1 * outer + ω^0 * inner`. -/
@[expose] def cnfLex2 (outer inner : Nat) : CnfOrd :=
  cnfNorm [(1, outer), (0, inner)]

/-- `cnfLex2 outer inner` is always canonical. -/
theorem cnfLex2_canonical (outer inner : Nat) :
    isCanonicalCnf (cnfLex2 outer inner) = true :=
  isCanonicalCnf_cnfNorm [(1, outer), (0, inner)]

/-- Coefficient at degree `0` of `cnfLex2 outer inner` is `inner`. -/
theorem cnfCoeffAt_cnfLex2_zero (outer inner : Nat) :
    cnfCoeffAt 0 (cnfLex2 outer inner) = inner := by
  unfold cnfLex2
  rw [cnfCoeffAt_cnfNorm]
  rfl

/-- Coefficient at degree `1` of `cnfLex2 outer inner` is `outer`. -/
theorem cnfCoeffAt_cnfLex2_one (outer inner : Nat) :
    cnfCoeffAt 1 (cnfLex2 outer inner) = outer := by
  unfold cnfLex2
  rw [cnfCoeffAt_cnfNorm]
  rfl

/-- All coefficients above degree `1` in `cnfLex2 outer inner` vanish. -/
theorem cnfCoeffAt_cnfLex2_gt_one (outer inner q : Nat)
    (hGt : natLt 1 q = true) :
    cnfCoeffAt q (cnfLex2 outer inner) = 0 := by
  unfold cnfLex2
  rw [cnfCoeffAt_cnfNorm]
  cases q with
  | zero => cases hGt
  | succ q₁ =>
    cases q₁ with
    | zero => cases hGt
    | succ q₂ => rfl

/-- Inner counter decrement strictly drops `cnfLex2 o i < cnfLex2 o (i + 1)`. -/
theorem cnfLex2_drop_inner (o i : Nat) :
    cnfLt (cnfLex2 o i) (cnfLex2 o (i + 1)) = true := by
  refine cnfLt_of_coeff_drop (cnfLex2 o i) (cnfLex2 o (i + 1))
    (cnfLex2_canonical o i) (cnfLex2_canonical o (i + 1)) 0 ?_ ?_
  · rw [cnfCoeffAt_cnfLex2_zero, cnfCoeffAt_cnfLex2_zero]
    exact (nat_ble_iff (i + 1) (i + 1)).mpr (Nat.le_refl (i + 1))
  · intro q hGt
    cases q with
    | zero => cases hGt
    | succ q₁ =>
      cases q₁ with
      | zero =>
        rw [cnfCoeffAt_cnfLex2_one, cnfCoeffAt_cnfLex2_one]
      | succ q₂ =>
        have hGt₁ : natLt 1 (q₂ + 2) = true :=
          (nat_ble_iff 2 (q₂ + 2)).mpr
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le q₂)))
        rw [cnfCoeffAt_cnfLex2_gt_one o i (q₂ + 2) hGt₁,
          cnfCoeffAt_cnfLex2_gt_one o (i + 1) (q₂ + 2) hGt₁]

/-- Outer counter decrement drops `cnfLex2 o i' < cnfLex2 (o + 1) i` regardless
of arbitrary finite inner reset `i'`. -/
theorem cnfLex2_drop_outer (o i i' : Nat) :
    cnfLt (cnfLex2 o i') (cnfLex2 (o + 1) i) = true := by
  refine cnfLt_of_coeff_drop (cnfLex2 o i') (cnfLex2 (o + 1) i)
    (cnfLex2_canonical o i') (cnfLex2_canonical (o + 1) i) 1 ?_ ?_
  · rw [cnfCoeffAt_cnfLex2_one, cnfCoeffAt_cnfLex2_one]
    exact (nat_ble_iff (o + 1) (o + 1)).mpr (Nat.le_refl (o + 1))
  · intro q hGt
    rw [cnfCoeffAt_cnfLex2_gt_one o i' q hGt,
      cnfCoeffAt_cnfLex2_gt_one (o + 1) i q hGt]

/-! ## 2. Closed-Form Bounded-Reset Two-Tier Step Ceiling (`lex2Bound`) -/

/-- Exact closed-form step budget for an `ω^1 * outer + ω^0 * inner` nested
loop whose outer back-edges reset the inner counter to at most `resetCap`:
`outer * (resetCap * kInner + kOuter) + inner * kInner + kExit`. -/
@[expose] def lex2Bound (resetCap kInner kOuter kExit outer inner : Nat) : Nat :=
  outer * (resetCap * kInner + kOuter) + inner * kInner + kExit

private theorem lex2Bound_inner_step (resetCap kInner kOuter kExit o i : Nat) :
    kInner + lex2Bound resetCap kInner kOuter kExit o i =
      lex2Bound resetCap kInner kOuter kExit o (i + 1) := by
  unfold lex2Bound
  rw [Nat.succ_mul]
  rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) (i * kInner) kExit]
  rw [← Nat.add_assoc kInner (o * (resetCap * kInner + kOuter))
    (i * kInner + kExit)]
  rw [Nat.add_comm kInner (o * (resetCap * kInner + kOuter))]
  rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) kInner (i * kInner + kExit)]
  rw [← Nat.add_assoc kInner (i * kInner) kExit]
  rw [Nat.add_comm kInner (i * kInner)]
  rw [← Nat.add_assoc (o * (resetCap * kInner + kOuter))
    (i * kInner + kInner) kExit]

private theorem lex2Bound_outer_step
    (resetCap kInner kOuter kExit o i' : Nat) (hi : i' ≤ resetCap) :
    kOuter + lex2Bound resetCap kInner kOuter kExit o i' ≤
      lex2Bound resetCap kInner kOuter kExit (o + 1) 0 := by
  unfold lex2Bound
  have hMul : i' * kInner ≤ resetCap * kInner :=
    Nat.mul_le_mul_right kInner hi
  have hInnerLe :
      kOuter + (o * (resetCap * kInner + kOuter) + i' * kInner + kExit) ≤
        kOuter +
          (o * (resetCap * kInner + kOuter) + resetCap * kInner + kExit) :=
    Nat.add_le_add_left
      (Nat.add_le_add_right
        (Nat.add_le_add_left hMul (o * (resetCap * kInner + kOuter))) kExit)
      kOuter
  have hEq :
      kOuter +
          (o * (resetCap * kInner + kOuter) + resetCap * kInner + kExit) =
        (o + 1) * (resetCap * kInner + kOuter) + 0 * kInner + kExit := by
    rw [Nat.zero_mul, Nat.add_zero]
    rw [Nat.succ_mul]
    rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) (resetCap * kInner) kExit]
    rw [← Nat.add_assoc kOuter (o * (resetCap * kInner + kOuter))
      (resetCap * kInner + kExit)]
    rw [Nat.add_comm kOuter (o * (resetCap * kInner + kOuter))]
    rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) kOuter
      (resetCap * kInner + kExit)]
    rw [← Nat.add_assoc kOuter (resetCap * kInner) kExit]
    rw [Nat.add_comm kOuter (resetCap * kInner)]
    rw [← Nat.add_assoc (o * (resetCap * kInner + kOuter))
      (resetCap * kInner + kOuter) kExit]
  rw [hEq] at hInnerLe
  exact hInnerLe

private theorem lex2_kExit_le_bound (resetCap kInner kOuter kExit o i : Nat) :
    kExit ≤ lex2Bound resetCap kInner kOuter kExit o i := by
  unfold lex2Bound
  exact Nat.le_add_left kExit
    (o * (resetCap * kInner + kOuter) + i * kInner)

private theorem v2_loop_lex2_zero_aux {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → Nat → State → Prop)
    (resetCap kInner kOuter kExit : Nat)
    (hBase : ∀ s, Inv 0 0 s → ReachesDoneWithinV2 p post kExit s)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2 p post kExit s ∨
      BoundedReachV2 p (Inv o i) kInner s) :
    ∀ (i : Nat) (s : State),
      Inv 0 i s →
      ReachesDoneWithinV2 p post
        (lex2Bound resetCap kInner kOuter kExit 0 i) s
  | 0, s, hInv => by
    unfold lex2Bound
    rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add]
    exact hBase s hInv
  | i + 1, s, hInv => by
    cases hInner 0 i s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2.mono
        (lex2_kExit_le_bound resetCap kInner kOuter kExit 0 (i + 1)) hEarly
    | inr hStep =>
      have hJoin :
          ReachesDoneWithinV2 p post
            (kInner + lex2Bound resetCap kInner kOuter kExit 0 i) s :=
        BoundedReachV2.bind_done hStep (fun s' hs' =>
          v2_loop_lex2_zero_aux Inv resetCap kInner kOuter kExit hBase hInner
            i s' hs')
      rw [lex2Bound_inner_step] at hJoin
      exact hJoin

private theorem v2_loop_lex2_succ_aux {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → Nat → State → Prop)
    (resetCap kInner kOuter kExit oPrev : Nat)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2 p post kExit s ∨
      BoundedReachV2 p (Inv o i) kInner s)
    (hOuter : ∀ o s, Inv (o + 1) 0 s →
      ReachesDoneWithinV2 p post kExit s ∨
      ∃ i', i' ≤ resetCap ∧ BoundedReachV2 p (Inv o i') kOuter s)
    (hPrev : ∀ i' s, i' ≤ resetCap → Inv oPrev i' s →
      ReachesDoneWithinV2 p post
        (lex2Bound resetCap kInner kOuter kExit oPrev i') s) :
    ∀ (i : Nat) (s : State),
      Inv (oPrev + 1) i s →
      ReachesDoneWithinV2 p post
        (lex2Bound resetCap kInner kOuter kExit (oPrev + 1) i) s
  | 0, s, hInv => by
    cases hOuter oPrev s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2.mono
        (lex2_kExit_le_bound resetCap kInner kOuter kExit (oPrev + 1) 0) hEarly
    | inr hNext =>
      let ⟨i', hi', hStep⟩ := hNext
      have hJoin :
          ReachesDoneWithinV2 p post
            (kOuter + lex2Bound resetCap kInner kOuter kExit oPrev i') s :=
        BoundedReachV2.bind_done hStep (fun s' hs' => hPrev i' s' hi' hs')
      exact ReachesDoneWithinV2.mono
        (lex2Bound_outer_step resetCap kInner kOuter kExit oPrev i' hi') hJoin
  | i + 1, s, hInv => by
    cases hInner (oPrev + 1) i s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2.mono
        (lex2_kExit_le_bound resetCap kInner kOuter kExit (oPrev + 1) (i + 1))
        hEarly
    | inr hStep =>
      have hJoin :
          ReachesDoneWithinV2 p post
            (kInner +
              lex2Bound resetCap kInner kOuter kExit (oPrev + 1) i) s :=
        BoundedReachV2.bind_done hStep (fun s' hs' =>
          v2_loop_lex2_succ_aux Inv resetCap kInner kOuter kExit oPrev
            hInner hOuter hPrev i s' hs')
      rw [lex2Bound_inner_step] at hJoin
      exact hJoin

/-- Nested bounded-reset loop combinator for `(outer, inner)` with ordinal rank
`cnfLex2 outer inner`: proves exact explicit `Nat` step bound
`lex2Bound resetCap kInner kOuter kExit outer inner` without existential
quantifiers or banned tactics. -/
theorem v2_loop_lex2_bounded_reset {p : Program} {post : TerminalOut → Prop}
    (Inv : Nat → Nat → State → Prop)
    (resetCap kInner kOuter kExit : Nat)
    (hBase : ∀ s, Inv 0 0 s → ReachesDoneWithinV2 p post kExit s)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2 p post kExit s ∨
      BoundedReachV2 p (Inv o i) kInner s)
    (hOuter : ∀ o s, Inv (o + 1) 0 s →
      ReachesDoneWithinV2 p post kExit s ∨
      ∃ i', i' ≤ resetCap ∧ BoundedReachV2 p (Inv o i') kOuter s) :
    ∀ (o i : Nat) (s : State),
      Inv o i s →
      ReachesDoneWithinV2 p post
        (lex2Bound resetCap kInner kOuter kExit o i) s := by
  intro o
  induction o with
  | zero =>
    intro i s hInv
    exact v2_loop_lex2_zero_aux Inv resetCap kInner kOuter kExit hBase hInner
      i s hInv
  | succ oPrev ih =>
    intro i s hInv
    exact v2_loop_lex2_succ_aux Inv resetCap kInner kOuter kExit oPrev
      hInner hOuter (fun i' st _ hSt => ih i' st hSt) i s hInv

/-- End-to-end Profile v2 adequacy wrapper combining `initStateV2`, setup prefix
`setupBound`, and closed-form `lex2Bound`. -/
theorem execWithinStepsV2_of_lex2_bounded_reset {p : Program} {q : Query}
    {s₀ : State} {post : TerminalOut → Prop}
    (Inv : Nat → Nat → State → Prop)
    (setupBound resetCap kInner kOuter kExit outer inner : Nat)
    (hInit : initStateV2 p q = .ok s₀)
    (hSetup : BoundedReachV2 p (Inv outer inner) setupBound s₀)
    (hBase : ∀ s, Inv 0 0 s → ReachesDoneWithinV2 p post kExit s)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2 p post kExit s ∨
      BoundedReachV2 p (Inv o i) kInner s)
    (hOuter : ∀ o s, Inv (o + 1) 0 s →
      ReachesDoneWithinV2 p post kExit s ∨
      ∃ i', i' ≤ resetCap ∧ BoundedReachV2 p (Inv o i') kOuter s) :
    ExecWithinStepsV2 p q
      (setupBound + lex2Bound resetCap kInner kOuter kExit outer inner) post ∧
    WellFormedV2 p q ∧
    ¬ DivergesV2 p q ∧
    SatisfiesPostV2 p q post ∧
    (∃ out : TerminalOut, BehaviorV2 p q out ∧ post out) := by
  have hLoop := v2_loop_lex2_bounded_reset Inv resetCap kInner kOuter kExit
    hBase hInner hOuter outer inner
  have hReach :
      ReachesDoneWithinV2 p post
        (setupBound + lex2Bound resetCap kInner kOuter kExit outer inner) s₀ :=
    BoundedReachV2.bind_done hSetup (fun s₁ hInv => hLoop s₁ hInv)
  exact v2_adequacy_bounded_post hInit hReach

/-! ## 3. Constructive `< ω^ω` Step-Budget Extraction via `CnfAcc` -/

/-- Well-founded `< ω^ω` descent extraction over `ReachesDoneWithinV2`:
if every `Inv s` state either exits within `exitBound` steps or advances in
`BoundedReachV2` (`≤ iterBound`) to `s'` strictly lowering
`cnfNorm (measure s')`, then `ReachesDoneWithinV2 p post B s` holds for an
extracted concrete bound `B : Nat`. -/
theorem v2_loop_cnfOrd_exists {p : Program} {post : TerminalOut → Prop}
    (Inv : State → Prop) (measure : State → CnfOrd)
    (iterBound exitBound : Nat)
    (hStep : ∀ s : State, Inv s →
      ReachesDoneWithinV2 p post exitBound s ∨
      BoundedReachV2 p
        (fun s' =>
          Inv s' ∧ cnfLt (cnfNorm (measure s')) (cnfNorm (measure s)) = true)
        iterBound s) :
    ∀ s : State, Inv s → ∃ B : Nat, ReachesDoneWithinV2 p post B s := by
  have hAux :
      ∀ (ord : CnfOrd), CnfAcc ord →
      ∀ s : State, Inv s → cnfNorm (measure s) = ord →
        ∃ B : Nat, ReachesDoneWithinV2 p post B s := by
    intro ord hAcc
    induction hAcc with
    | intro x _ ih =>
      intro s hInv hOrd
      cases hStep s hInv with
      | inl hDone => exact ⟨exitBound, hDone⟩
      | inr hNext =>
        let ⟨k, s', _, hSteps, hInv', hLt⟩ := hNext
        rw [hOrd] at hLt
        let ⟨B', hSub⟩ := ih (cnfNorm (measure s'))
          (isCanonicalCnf_cnfNorm _) hLt s' hInv' rfl
        exact ⟨k + B', reachesDoneWithinV2_of_stepsTo hSteps hSub⟩
  intro s hInv
  exact hAux (cnfNorm (measure s))
    (cnfAcc_all (cnfNorm (measure s)) (isCanonicalCnf_cnfNorm _))
    s hInv rfl

/-- End-to-end Profile v2 adequacy from an arbitrary `< ω^ω` ranking measure:
extracts a finite `Nat` step bound `B` yielding `ExecWithinStepsV2`,
`WellFormedV2`, `¬ DivergesV2`, and `SatisfiesPostV2`. -/
theorem execWithinStepsV2_of_cnfOrd {p : Program} {q : Query} {s₀ : State}
    {post : TerminalOut → Prop} (Inv : State → Prop)
    (measure : State → CnfOrd) (setupBound iterBound exitBound : Nat)
    (hInit : initStateV2 p q = .ok s₀)
    (hSetup : BoundedReachV2 p Inv setupBound s₀)
    (hStep : ∀ s : State, Inv s →
      ReachesDoneWithinV2 p post exitBound s ∨
      BoundedReachV2 p
        (fun s' =>
          Inv s' ∧ cnfLt (cnfNorm (measure s')) (cnfNorm (measure s)) = true)
        iterBound s) :
    ∃ B : Nat,
      ExecWithinStepsV2 p q B post ∧
      WellFormedV2 p q ∧
      ¬ DivergesV2 p q ∧
      SatisfiesPostV2 p q post ∧
      (∃ out : TerminalOut, BehaviorV2 p q out ∧ post out) := by
  let ⟨kSetup, s₁, _, hSetupSteps, hInv₁⟩ := hSetup
  let ⟨B', hLoop⟩ := v2_loop_cnfOrd_exists Inv measure iterBound exitBound hStep
    s₁ hInv₁
  exact ⟨kSetup + B',
    v2_adequacy_bounded_post hInit (reachesDoneWithinV2_of_stepsTo hSetupSteps hLoop)⟩

/-! ## 4. `CnfStepConverges` and `WorklistPool` MIR Simulation Bridges -/

/-- Lift a `CnfStepConverges` abstract termination derivation under simulation
`sim` into a MIR step budget `steps * iterBound + exitBound`. -/
theorem v2_steps_of_cnfStepConverges {α : Type} {p : Program}
    {post : TerminalOut → Prop}
    (stepAbs : α → Option α) (measure : α → CnfOrd)
    (sim : α → State → Prop) (iterBound exitBound : Nat)
    (hDone : ∀ a s, stepAbs a = none → sim a s →
      ReachesDoneWithinV2 p post exitBound s)
    (hStep : ∀ a a' s, stepAbs a = some a' → sim a s →
      BoundedReachV2 p (sim a') iterBound s)
    {a₀ aFinal : α}
    (hConv : CnfStepConverges stepAbs measure a₀ aFinal) :
    ∀ s₀ : State, sim a₀ s₀ →
      ∃ steps : Nat,
        ReachesDoneWithinV2 p post (steps * iterBound + exitBound) s₀ := by
  induction hConv with
  | quiescent a hNone =>
    intro s₀ hSim
    refine ⟨0, ?_⟩
    rw [Nat.zero_mul, Nat.zero_add]
    exact hDone a s₀ hNone hSim
  | step a a' _ hSome _ _ ih =>
    intro s₀ hSim
    have hReach : BoundedReachV2 p (sim a') iterBound s₀ :=
      hStep a a' s₀ hSome hSim
    let ⟨k, s₁, hk, hSteps, hSim'⟩ := hReach
    let ⟨steps, hRest⟩ := ih s₁ hSim'
    refine ⟨steps + 1, ?_⟩
    have hJoin : ReachesDoneWithinV2 p post (k + (steps * iterBound + exitBound)) s₀ :=
      reachesDoneWithinV2_of_stepsTo hSteps hRest
    have hMono := ReachesDoneWithinV2.mono
      (Nat.add_le_add_right hk (steps * iterBound + exitBound)) hJoin
    have hArith :
        iterBound + (steps * iterBound + exitBound) =
          (steps + 1) * iterBound + exitBound := by
      rw [Nat.succ_mul, Nat.add_comm (steps * iterBound) iterBound, Nat.add_assoc]
    rw [hArith] at hMono
    exact hMono

/-- Lift any `< ω^ω`-ranked `stepAbs : α → Option α` via
`cnfStep_terminates_all` and simulation `sim` into a Profile v2 step bound. -/
theorem v2_steps_of_cnfStep_terminates {α : Type} {p : Program}
    {post : TerminalOut → Prop}
    (stepAbs : α → Option α) (measure : α → CnfOrd)
    (InvAbs : α → Prop) (sim : α → State → Prop)
    (iterBound exitBound : Nat)
    (hDesc : ∀ (a a' : α), InvAbs a → stepAbs a = some a' →
      InvAbs a' ∧ cnfLt (cnfNorm (measure a')) (cnfNorm (measure a)) = true)
    (hDone : ∀ a s, stepAbs a = none → sim a s →
      ReachesDoneWithinV2 p post exitBound s)
    (hStep : ∀ a a' s, stepAbs a = some a' → sim a s →
      BoundedReachV2 p (sim a') iterBound s)
    {a₀ : α} {s₀ : State} (hInv₀ : InvAbs a₀) (hSim₀ : sim a₀ s₀) :
    ∃ steps : Nat,
      ReachesDoneWithinV2 p post (steps * iterBound + exitBound) s₀ := by
  let ⟨_, _, hConv, _, _⟩ := cnfStep_terminates_all stepAbs measure InvAbs hDesc
    a₀ hInv₀
  exact v2_steps_of_cnfStepConverges stepAbs measure sim iterBound exitBound
    hDone hStep hConv s₀ hSim₀

/-- Lift a `WorklistConverges` proof into a MIR step budget
`steps * iterBound + exitBound`. -/
theorem v2_steps_of_worklist_converges {p : Program}
    {post : TerminalOut → Prop}
    (pol : SpawnPolicy) (sim : WorklistPool → State → Prop)
    (iterBound exitBound : Nat)
    (hDone : ∀ w s, poolIsNonEmpty w = false → sim w s →
      ReachesDoneWithinV2 p post exitBound s)
    (hStep : ∀ w w' s, poolIsNonEmpty w = true →
      worklistStep pol w = .returned w' → sim w s →
      BoundedReachV2 p (sim w') iterBound s)
    {w₀ wFinal : WorklistPool}
    (hConv : WorklistConverges pol w₀ wFinal) :
    ∀ s₀ : State, sim w₀ s₀ →
      ∃ steps : Nat,
        ReachesDoneWithinV2 p post (steps * iterBound + exitBound) s₀ := by
  induction hConv with
  | quiescent w hEmp =>
    intro s₀ hSim
    refine ⟨0, ?_⟩
    rw [Nat.zero_mul, Nat.zero_add]
    exact hDone w s₀ hEmp hSim
  | step w wNext _ hNonEmp hWork _ _ ih =>
    intro s₀ hSim
    have hReach : BoundedReachV2 p (sim wNext) iterBound s₀ :=
      hStep w wNext s₀ hNonEmp hWork hSim
    let ⟨k, s₁, hk, hSteps, hSim'⟩ := hReach
    let ⟨steps, hRest⟩ := ih s₁ hSim'
    refine ⟨steps + 1, ?_⟩
    have hJoin : ReachesDoneWithinV2 p post (k + (steps * iterBound + exitBound)) s₀ :=
      reachesDoneWithinV2_of_stepsTo hSteps hRest
    have hMono := ReachesDoneWithinV2.mono
      (Nat.add_le_add_right hk (steps * iterBound + exitBound)) hJoin
    have hArith :
        iterBound + (steps * iterBound + exitBound) =
          (steps + 1) * iterBound + exitBound := by
      rw [Nat.succ_mul, Nat.add_comm (steps * iterBound) iterBound, Nat.add_assoc]
    rw [hArith] at hMono
    exact hMono

/-- Lift any `PolicyAdmissible` worklist simulator (such as
`towerLookupNext_admissible`) via `worklist_terminates_all` into a Profile v2
step bound. -/
theorem v2_steps_of_worklist_terminates {p : Program}
    {post : TerminalOut → Prop}
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (sim : WorklistPool → State → Prop) (iterBound exitBound : Nat)
    (hDone : ∀ w s, poolIsNonEmpty w = false → sim w s →
      ReachesDoneWithinV2 p post exitBound s)
    (hStep : ∀ w w' s, poolIsNonEmpty w = true →
      worklistStep pol w = .returned w' → sim w s →
      BoundedReachV2 p (sim w') iterBound s)
    (w₀ : WorklistPool) (s₀ : State) (hSim₀ : sim w₀ s₀) :
    ∃ steps : Nat,
      ReachesDoneWithinV2 p post (steps * iterBound + exitBound) s₀ := by
  let ⟨_, hConv, _, _, _, _⟩ := worklist_terminates_all pol hPol w₀
  exact v2_steps_of_worklist_converges pol sim iterBound exitBound hDone hStep
    hConv s₀ hSim₀

/-! ## 5. Step-Bounded Reactive Prefix Contracts (`ReactiveStepContractV2`) -/

/-- Non-stuttering bounded Profile v2 reachability (`1 ≤ k ≤ bound`): requires
at least one real MIR `.step` transition before reaching `stopPred`. -/
@[expose] def StrictBoundedReachV2 (p : Program) (stopPred : State → Prop)
    (bound : Nat) (s : State) : Prop :=
  ∃ k : Nat, ∃ s' : State,
    1 ≤ k ∧ k ≤ bound ∧ StepsToV2 p k s s' ∧ stopPred s'

/-- Sequential composition (`b₁ + b₂`) for `StrictBoundedReachV2`, accumulating
at least `2` steps (`1 + 1 ≤ k₁ + k₂`). -/
theorem StrictBoundedReachV2.trans {p : Program} {P Q : State → Prop}
    {b₁ b₂ : Nat} {s₀ : State}
    (h₁ : StrictBoundedReachV2 p P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → StrictBoundedReachV2 p Q b₂ s₁) :
    StrictBoundedReachV2 p Q (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hPos₁, hk₁, hSteps₁, hP⟩ := h₁
  let ⟨k₂, s₂, hPos₂, hk₂, hSteps₂, hQ⟩ := h₂ s₁ hP
  exact ⟨k₁ + k₂, s₂, Nat.le_trans hPos₁ (Nat.le_add_right k₁ k₂),
    Nat.add_le_add hk₁ hk₂, StepsToV2.trans hSteps₁ hSteps₂, hQ⟩

/-- Budget monotonicity for `StrictBoundedReachV2`. -/
theorem StrictBoundedReachV2.mono {p : Program} {stopPred : State → Prop}
    {b₁ b₂ : Nat} {s : State} (hLe : b₁ ≤ b₂)
    (h : StrictBoundedReachV2 p stopPred b₁ s) :
    StrictBoundedReachV2 p stopPred b₂ s := by
  let ⟨k, s', hPos, hk, hSteps, hP⟩ := h
  exact ⟨k, s', hPos, Nat.le_trans hk hLe, hSteps, hP⟩

/-- Per-tick / per-frame reactive Profile v2 latency contract: starting from any
`inv s`, execution within `frameBound` MIR steps either terminates cleanly in
`post` or advances strictly (`1 ≤ k ≤ frameBound` steps) to the next observable
`yieldPred` checkpoint preserving `inv`. -/
@[expose] def ReactiveStepContractV2 (p : Program)
    (inv yieldPred : State → Prop) (post : TerminalOut → Prop)
    (frameBound : Nat) : Prop :=
  ∀ s : State, inv s →
    ReachesDoneWithinV2 p post frameBound s ∨
    StrictBoundedReachV2 p (fun s' => inv s' ∧ yieldPred s') frameBound s

/-- Iterate a `ReactiveStepContractV2` over any finite prefix of `frames` ticks:
within at most `frames * frameBound` MIR steps, execution either finishes
cleanly in `post` or completes `frames` non-stuttering checkpoints
(`frames ≤ k` steps). -/
theorem ReactiveStepContractV2.iterate_prefix {p : Program}
    {inv yieldPred : State → Prop} {post : TerminalOut → Prop}
    {frameBound : Nat}
    (hContract : ReactiveStepContractV2 p inv yieldPred post frameBound) :
    ∀ (frames : Nat) (s₀ : State), inv s₀ →
      ReachesDoneWithinV2 p post (frames * frameBound) s₀ ∨
      ∃ (k : Nat) (s' : State),
        frames ≤ k ∧ k ≤ frames * frameBound ∧ StepsToV2 p k s₀ s' ∧
          inv s' ∧ (0 < frames → yieldPred s')
  | 0, s₀, hInv => by
    rw [Nat.zero_mul]
    refine Or.inr ⟨0, s₀, Nat.le_refl 0, Nat.le_refl 0, StepsToV2.refl s₀,
      hInv, fun hLt => False.elim (Nat.not_lt_zero 0 hLt)⟩
  | n + 1, s₀, hInv => by
    have hPrev := ReactiveStepContractV2.iterate_prefix hContract n s₀ hInv
    have hArith : n * frameBound + frameBound = (n + 1) * frameBound := by
      rw [Nat.succ_mul]
    cases hPrev with
    | inl hDone =>
      have hLe : n * frameBound ≤ (n + 1) * frameBound := by
        rw [Nat.succ_mul]
        exact Nat.le_add_right _ _
      exact Or.inl (ReachesDoneWithinV2.mono hLe hDone)
    | inr hPrefix =>
      let ⟨k, s₁, hMin, hk, hSteps, hInv₁, _⟩ := hPrefix
      cases hContract s₁ hInv₁ with
      | inl hDoneNext =>
        have hTotal :
            ReachesDoneWithinV2 p post (k + frameBound) s₀ :=
          reachesDoneWithinV2_of_stepsTo hSteps hDoneNext
        have hLe : k + frameBound ≤ (n + 1) * frameBound := by
          rw [← hArith]
          exact Nat.add_le_add_right hk frameBound
        exact Or.inl (ReachesDoneWithinV2.mono hLe hTotal)
      | inr hTick =>
        let ⟨kTick, s₂, hkMin, hkMax, hStepsTick, hInv₂, hYield₂⟩ := hTick
        refine Or.inr ⟨k + kTick, s₂, ?_, ?_,
          StepsToV2.trans hSteps hStepsTick, hInv₂, fun _ => hYield₂⟩
        · exact Nat.add_le_add hMin hkMin
        · rw [← hArith]
          exact Nat.add_le_add hk hkMax

end Anneal.StepBound

end
