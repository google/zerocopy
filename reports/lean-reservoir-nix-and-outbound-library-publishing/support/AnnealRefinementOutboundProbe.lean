-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module

import Lean.Linter.Extra

/-!
# Standalone Outbound Packaging Probe for `anneal-refinement` (Layers 1A and 1B)

Synthesizes the three modules of `probe1-anneal-refinement` into a single,
self-contained Lean `v4.34.1` artifact:

1. **Layer 1A (`Refinement.lean`):** Language-independent partial-behavior
   preorders (`Preorder`, `Monotone`), languages (`Lang`), meaning preservation
   (`PreservesMeaning`), compiler passes (`Pass`, `CorrectPass`, `Pass.id`,
   `Pass.comp`, `Pass.verified_preserves_spec`), and TCB trust-policy receipts
   (`TrustPolicy`, `VerificationResult`, `verify_with_pass`).
2. **Layer 1B (`StepResult.lean`):** Small-step operational execution outcomes
   (`StepResult`, `FuelOutcome`, `runFuel`), prefix trace observations
   (`PartialObs`, `PartialObs.Refines`, `partialObsPreorder`), and fuel
   monotonicity (`runFuel_done_mono`, `runFuel_trap_mono`,
   `runFuel_toPartialObs_refines`).
3. **Verification & Linter Suite (`Test/Basic.lean`):** Validates positive and
   negative `#guard_msgs` checks, built-in Verso docstring role elaboration
   (`set_option doc.verso true`), core linters (`linter.missingDocs`,
   `linter.unusedSimpArgs`, `linter.extra`), and kernel axiom footprints via
   `#print axioms`.
-/

set_option linter.missingDocs true
set_option linter.unusedSimpArgs true
set_option linter.extra true

@[expose] public section

namespace AnnealRefinement

/-!
## Layer 1A: Partial-Behavior Ordering, Languages, Passes, and Receipts
-/

/-- All propositions in `xs` hold (`List.foldr And True xs`). -/
def AllHold : List Prop → Prop
  | [] => True
  | p :: ps => p ∧ AllHold ps

/-- Soundness of `AllHold`: if `AllHold ps` holds and `p ∈ ps`, then `p`
holds. -/
theorem allHold_mem {ps : List Prop} {p : Prop}
    (hAll : AllHold ps) (hMem : p ∈ ps) : p := by
  induction ps with
  | nil => cases hMem
  | cons q qs ih =>
    rcases hAll with ⟨hq, hqs⟩
    cases hMem with
    | head => exact hq
    | tail _ hTail => exact ih hqs hTail

/-- Soundness of `AllHold` over mapped lists (`List.map`). -/
theorem allHold_map {α : Type u} {P : α → Prop} {xs : List α}
    (hAll : AllHold (xs.map P)) {x : α} (hMem : x ∈ xs) : P x := by
  induction xs with
  | nil => cases hMem
  | cons y ys ih =>
    rcases hAll with ⟨hy, hys⟩
    cases hMem with
    | head => exact hy
    | tail _ hTail => exact ih hys hTail

/-- `AllHold` distributes over list concatenation (`++`). -/
theorem allHold_append {xs ys : List Prop} :
    AllHold (xs ++ ys) ↔ AllHold xs ∧ AllHold ys := by
  induction xs with
  | nil =>
    simp [AllHold]
  | cons x xs ih =>
    simp only [List.cons_append, AllHold, ih]
    exact ⟨fun ⟨hx, hxs, hys⟩ => ⟨⟨hx, hxs⟩, hys⟩,
           fun ⟨⟨hx, hxs⟩, hys⟩ => ⟨hx, hxs, hys⟩⟩

/-- Reflexive and transitive partial-behavior refinement ordering `le b₁ b₂`. -/
structure Preorder (B : Type u) where
  /-- Binary refinement relation `b₁ ⊑ b₂`. -/
  le : B → B → Prop
  /-- Reflexivity of `le`. -/
  refl : ∀ b, le b b
  /-- Transitivity of `le`. -/
  trans : ∀ {b₁ b₂ b₃}, le b₁ b₂ → le b₂ b₃ → le b₁ b₃

/-- A monotone function between preorders preserves `le`. -/
def Monotone {B₁ : Type u} {B₂ : Type v}
    (O₁ : Preorder B₁) (O₂ : Preorder B₂) (f : B₁ → B₂) : Prop :=
  ∀ {b b'}, O₁.le b b' → O₂.le (f b) (f b')

/-- Identity is monotone with respect to any preorder. -/
theorem monotone_id {B : Type u} (O : Preorder B) :
    Monotone O O (fun b => b) :=
  fun h => h

/-- Composition of monotone maps is monotone. -/
theorem monotone_comp {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    {O₁ : Preorder B₁} {O₂ : Preorder B₂} {O₃ : Preorder B₃}
    {g : B₂ → B₃} {f : B₁ → B₂}
    (hg : Monotone O₂ O₃ g) (hf : Monotone O₁ O₂ f) :
    Monotone O₁ O₃ (fun b => g (f b)) :=
  fun h => hg (hf h)

/-- A language packages syntax `Prog`, an observation domain `Obs` with a
partial-behavior preorder `order`, a well-formedness predicate `WellFormed`, and
a semantics assigning sets of partial behaviors to programs. -/
structure Lang where
  /-- Program syntax representation. -/
  Prog : Type u
  /-- Partial-behavior observation domain. -/
  Obs : Type v
  /-- Refinement preorder on `Obs`. -/
  order : Preorder Obs
  /-- Static well-formedness predicate on `Prog`. -/
  WellFormed : Prog → Prop
  /-- Operational or denotational behavior relation on `Prog` and `Obs`. -/
  Beh : Prog → Obs → Prop

/-- Target partial behaviors `T` preserve the meaning of source partial
behaviors `S` along a monotone observation map `project` when every target
behavior refines the projection of some source behavior
(`project bₛ ⊑ bₜ`). -/
def PreservesMeaning {ObsS : Type u} {ObsT : Type v}
    (orderS : Preorder ObsS) (orderT : Preorder ObsT)
    (project : ObsS → ObsT) (S : ObsS → Prop) (T : ObsT → Prop) : Prop :=
  Monotone orderS orderT project ∧
  ∀ bₜ, T bₜ → ∃ bₛ, S bₛ ∧ orderT.le (project bₛ) bₜ

/-- `PreservesMeaning` is reflexive along the identity observation map. -/
theorem preservesMeaning_refl {Obs : Type u}
    (order : Preorder Obs) (S : Obs → Prop) :
    PreservesMeaning order order (fun b => b) S S :=
  ⟨monotone_id order, fun bₜ hT => ⟨bₜ, hT, order.refl bₜ⟩⟩

/-- `PreservesMeaning` composes transitively across observation maps. -/
theorem preservesMeaning_trans {Obs₁ : Type u} {Obs₂ : Type v} {Obs₃ : Type w}
    {O₁ : Preorder Obs₁} {O₂ : Preorder Obs₂} {O₃ : Preorder Obs₃}
    {proj₁₂ : Obs₁ → Obs₂} {proj₂₃ : Obs₂ → Obs₃}
    {S₁ : Obs₁ → Prop} {S₂ : Obs₂ → Prop} {S₃ : Obs₃ → Prop}
    (h₁₂ : PreservesMeaning O₁ O₂ proj₁₂ S₁ S₂)
    (h₂₃ : PreservesMeaning O₂ O₃ proj₂₃ S₂ S₃) :
    PreservesMeaning O₁ O₃ (fun b => proj₂₃ (proj₁₂ b)) S₁ S₃ := by
  rcases h₁₂ with ⟨hMono₁₂, hRef₁₂⟩
  rcases h₂₃ with ⟨hMono₂₃, hRef₂₃⟩
  refine ⟨monotone_comp hMono₂₃ hMono₁₂, ?_⟩
  intro b₃ hS₃
  rcases hRef₂₃ b₃ hS₃ with ⟨b₂, hS₂, hLe₂₃⟩
  rcases hRef₁₂ b₂ hS₂ with ⟨b₁, hS₁, hLe₁₂⟩
  exact ⟨b₁, hS₁, O₃.trans (hMono₂₃ hLe₁₂) hLe₂₃⟩

/-- A compiler pass from source language `S` to target language `T`. -/
structure Pass (S : Lang) (T : Lang) where
  /-- Relational compilation judgment from `S.Prog` to `T.Prog`. -/
  compile : S.Prog → T.Prog → Prop
  /-- Observation projection from source observations to target observations. -/
  project : S.Obs → T.Obs

/-- Forward simulation / meaning-preservation contract for a compiler pass. -/
def Pass.Correct {S : Lang} {T : Lang} (P : Pass S T) : Prop :=
  ∀ s t, S.WellFormed s → P.compile s t →
    T.WellFormed t ∧
    PreservesMeaning S.order T.order P.project (S.Beh s) (T.Beh t)

/-- A verified (or assumed-correct) compiler pass bundling `Pass` with a proof
of `Pass.Correct`. -/
structure CorrectPass (S : Lang) (T : Lang) extends Pass S T where
  /-- Proof that the underlying pass preserves well-formedness and meaning. -/
  correct : toPass.Correct

/-- Target-level verification holds for source program `s` across pass `P` when
`s` is well-formed and every target program `t` produced by `P.compile s t` is
well-formed and preserves the meaning of `s`. -/
def Pass.Verified {S : Lang} {T : Lang} (P : Pass S T) (s : S.Prog) : Prop :=
  S.WellFormed s ∧
  ∀ t, P.compile s t →
    T.WellFormed t ∧
    PreservesMeaning S.order T.order P.project (S.Beh s) (T.Beh t)

/-- The identity compiler pass on language `L`. -/
def Pass.id (L : Lang) : Pass L L where
  compile s t := s = t
  project b := b

/-- The identity pass is unconditionally correct. -/
theorem Pass.id_correct (L : Lang) : (Pass.id L).Correct := by
  intro s t hWF hEq
  subst hEq
  exact ⟨hWF, preservesMeaning_refl L.order (L.Beh s)⟩

/-- Sequential composition of compiler passes `P₁ : Pass L₁ L₂` and
`P₂ : Pass L₂ L₃`. -/
def Pass.comp {L₁ L₂ L₃ : Lang} (P₁ : Pass L₁ L₂) (P₂ : Pass L₂ L₃) :
    Pass L₁ L₃ where
  compile p₁ p₃ := ∃ p₂, P₁.compile p₁ p₂ ∧ P₂.compile p₂ p₃
  project b₁ := P₂.project (P₁.project b₁)

/-- Sequential composition of correct compiler passes is correct. -/
theorem Pass.comp_correct {L₁ L₂ L₃ : Lang}
    {P₁ : Pass L₁ L₂} {P₂ : Pass L₂ L₃}
    (h₁ : P₁.Correct) (h₂ : P₂.Correct) :
    (Pass.comp P₁ P₂).Correct := by
  intro p₁ p₃ hWF₁ ⟨p₂, hComp₁, hComp₂⟩
  rcases h₁ p₁ p₂ hWF₁ hComp₁ with ⟨hWF₂, hPres₁₂⟩
  rcases h₂ p₂ p₃ hWF₂ hComp₂ with ⟨hWF₃, hPres₂₃⟩
  refine ⟨hWF₃, ?_⟩
  change PreservesMeaning L₁.order L₃.order
    (fun b => P₂.project (P₁.project b)) (L₁.Beh p₁) (L₃.Beh p₃)
  exact preservesMeaning_trans hPres₁₂ hPres₂₃

/-- Transport a source specification `Spec : S.Obs → Prop` to a target program
across any pass satisfying `Pass.Verified`. -/
theorem Pass.verified_preserves_spec {S : Lang} {T : Lang}
    {P : Pass S T} {s : S.Prog} {t : T.Prog}
    {Spec : S.Obs → Prop}
    (hVer : P.Verified s)
    (hSpec : ∀ bₛ, S.Beh s bₛ → Spec bₛ)
    (hComp : P.compile s t) :
    T.WellFormed t ∧
    ∀ bₜ, T.Beh t bₜ → ∃ bₛ, Spec bₛ ∧ T.order.le (P.project bₛ) bₜ := by
  rcases hVer with ⟨_, hTargets⟩
  rcases hTargets t hComp with ⟨hWFt, _, hRef⟩
  refine ⟨hWFt, fun bₜ hBt => ?_⟩
  rcases hRef bₜ hBt with ⟨bₛ, hBs, hLe⟩
  exact ⟨bₛ, hSpec bₛ hBs, hLe⟩

/-- A trust policy over a type `Item` of TCB assumptions. -/
structure TrustPolicy (Item : Type u) where
  /-- Predicate determining whether a given TCB assumption is allowed. -/
  isAllowed : Item → Prop

/-- A verification receipt asserting that every item in `tcb` is allowed by
`policy` and that `claim` holds when all assumptions in `assumptions` hold. -/
def VerificationResult {Item : Type u}
    (policy : TrustPolicy Item)
    (tcb : List Item)
    (assumptions : List Prop)
    (claim : Prop) : Prop :=
  AllHold (tcb.map policy.isAllowed) ∧ (AllHold assumptions → claim)

/-- Produce a `VerificationResult` for `P.Verified s` given a proof that `s` is
well-formed, that the TCB satisfies `policy`, and that `P.Correct` follows from
`assumptions`. -/
theorem verify_with_pass {Item : Type u} {S : Lang} {T : Lang}
    (policy : TrustPolicy Item)
    (tcb : List Item)
    (assumptions : List Prop)
    (P : Pass S T)
    (s : S.Prog)
    (hPolicy : AllHold (tcb.map policy.isAllowed))
    (hPassCorrect : AllHold assumptions → P.Correct)
    (hWF : S.WellFormed s) :
    VerificationResult policy tcb assumptions (P.Verified s) := by
  refine ⟨hPolicy, fun hAssump => ⟨hWF, fun t hComp => ?_⟩⟩
  exact hPassCorrect hAssump s t hWF hComp

/-!
## Layer 1B: Small-Step Prefix Semantics and Fuel-Indexed Evaluation
-/

/-- One-step outcome of a small-step operational semantics. -/
inductive StepResult (State : Type u) (Val : Type v) where
  /-- Step to successor state `s'`. -/
  | next (s' : State)
  /-- Terminate normally with value `v`. -/
  | done (v : Val)
  /-- Terminate with a defined trap / panic. -/
  | trap

/-- Fuel-indexed outcome of iterating a small-step function. -/
inductive FuelOutcome (Val : Type v) where
  /-- Fuel exhausted before reaching a terminal state. -/
  | timeout
  /-- Reached normal termination with value `v`. -/
  | done (v : Val)
  /-- Reached a defined trap / panic. -/
  | trap

/-- Run `step` for at most `fuel` steps starting from `s`. -/
def runFuel {State : Type u} {Val : Type v}
    (step : State → StepResult State Val) : Nat → State → FuelOutcome Val
  | 0, _ => .timeout
  | fuel + 1, s =>
    match step s with
    | .next s' => runFuel step fuel s'
    | .done v => .done v
    | .trap => .trap

/-- Prefix observations over trace events `Ev` and terminal values `Val`. -/
inductive PartialObs (Ev : Type u) (Val : Type v) where
  /-- Finite event prefix observed along an ongoing execution. -/
  | prefixObs (events : List Ev)
  /-- Complete execution returning `val` after emitting `events`. -/
  | returns (events : List Ev) (val : Val)
  /-- Complete execution trapping after emitting `events`. -/
  | traps (events : List Ev)
  /-- Execution reaching undefined behavior after emitting `events`. -/
  | goesWrong (events : List Ev)

/-- Prefix-refinement relation `b₁ ⊑ b₂` on `PartialObs`.

A prefix observation `prefixObs ev₁` is refined by any longer prefix or terminal
observation extending `ev₁`, and `goesWrong ev₁` is refined by any observation
extending `ev₁`. -/
def PartialObs.Refines {Ev : Type u} {Val : Type v} :
    PartialObs Ev Val → PartialObs Ev Val → Prop
  | .prefixObs ev₁, .prefixObs ev₂ => ∃ sfx, ev₂ = ev₁ ++ sfx
  | .prefixObs ev₁, .returns ev₂ _ => ∃ sfx, ev₂ = ev₁ ++ sfx
  | .prefixObs ev₁, .traps ev₂ => ∃ sfx, ev₂ = ev₁ ++ sfx
  | .returns ev₁ v₁, .returns ev₂ v₂ => ev₁ = ev₂ ∧ v₁ = v₂
  | .traps ev₁, .traps ev₂ => ev₁ = ev₂
  | .goesWrong ev₁, .prefixObs ev₂ => ∃ sfx, ev₂ = ev₁ ++ sfx
  | .goesWrong ev₁, .returns ev₂ _ => ∃ sfx, ev₂ = ev₁ ++ sfx
  | .goesWrong ev₁, .traps ev₂ => ∃ sfx, ev₂ = ev₁ ++ sfx
  | .goesWrong ev₁, .goesWrong ev₂ => ∃ sfx, ev₂ = ev₁ ++ sfx
  | _, _ => False

/-- Reflexivity of `PartialObs.Refines`. -/
theorem PartialObs.refines_refl {Ev : Type u} {Val : Type v}
    (b : PartialObs Ev Val) : PartialObs.Refines b b := by
  cases b with
  | prefixObs ev => exact ⟨[], (List.append_nil ev).symm⟩
  | returns ev v => exact ⟨rfl, rfl⟩
  | traps ev => rfl
  | goesWrong ev => exact ⟨[], (List.append_nil ev).symm⟩

/-- Transitivity of `PartialObs.Refines`. -/
theorem PartialObs.refines_trans {Ev : Type u} {Val : Type v}
    {b₁ b₂ b₃ : PartialObs Ev Val}
    (h₁₂ : PartialObs.Refines b₁ b₂) (h₂₃ : PartialObs.Refines b₂ b₃) :
    PartialObs.Refines b₁ b₃ := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;>
    simp only [PartialObs.Refines] at h₁₂ h₂₃ ⊢
  all_goals try contradiction
  all_goals (
    try (rcases h₁₂ with ⟨sfx₁, rfl⟩; rcases h₂₃ with ⟨sfx₂, rfl⟩
         exact ⟨sfx₁ ++ sfx₂, List.append_assoc _ _ _⟩)
    try (rcases h₁₂ with ⟨sfx₁, rfl⟩; rcases h₂₃ with ⟨rfl, rfl⟩
         exact ⟨sfx₁, rfl⟩)
    try (rcases h₁₂ with ⟨sfx₁, rfl⟩; subst h₂₃; exact ⟨sfx₁, rfl⟩)
    try (rcases h₁₂ with ⟨rfl, rfl⟩; rcases h₂₃ with ⟨rfl, rfl⟩
         exact ⟨rfl, rfl⟩)
    try (subst h₁₂; subst h₂₃; rfl)
  )

/-- Canonical `Preorder` on `PartialObs`. -/
def partialObsPreorder (Ev : Type u) (Val : Type v) :
    Preorder (PartialObs Ev Val) where
  le := PartialObs.Refines
  refl := PartialObs.refines_refl
  trans := PartialObs.refines_trans

/-- Convert a `FuelOutcome` into an eventless `PartialObs Unit Val`. -/
def FuelOutcome.toPartialObs {Val : Type v} :
    FuelOutcome Val → PartialObs Unit Val
  | .timeout => .prefixObs []
  | .done v => .returns [] v
  | .trap => .traps []

/-- Determinism of `runFuel`: once `runFuel step fuel s` reaches `.done v`, any
larger fuel `fuel + extra` produces the same `.done v`. -/
theorem runFuel_done_mono {State : Type u} {Val : Type v}
    (step : State → StepResult State Val)
    {fuel : Nat} {s : State} {v : Val}
    (h : runFuel step fuel s = .done v) (extra : Nat) :
    runFuel step (fuel + extra) s = .done v := by
  induction fuel generalizing s with
  | zero => cases h
  | succ n ih =>
    simp only [runFuel, Nat.succ_add] at h ⊢
    cases hStep : step s with
    | next s' =>
      rw [hStep] at h
      exact ih h
    | done v' =>
      rw [hStep] at h
      exact h
    | trap =>
      rw [hStep] at h
      cases h

/-- Determinism of `runFuel` for `.trap`: once `runFuel step fuel s` reaches
`.trap`, any larger fuel `fuel + extra` also produces `.trap`. -/
theorem runFuel_trap_mono {State : Type u} {Val : Type v}
    (step : State → StepResult State Val)
    {fuel : Nat} {s : State}
    (h : runFuel step fuel s = .trap) (extra : Nat) :
    runFuel step (fuel + extra) s = .trap := by
  induction fuel generalizing s with
  | zero => cases h
  | succ n ih =>
    simp only [runFuel, Nat.succ_add] at h ⊢
    cases hStep : step s with
    | next s' =>
      rw [hStep] at h
      exact ih h
    | done v' =>
      rw [hStep] at h
      cases h
    | trap =>
      rfl

/-- Increasing fuel produces a refining `PartialObs`. -/
theorem runFuel_toPartialObs_refines {State : Type u} {Val : Type v}
    (step : State → StepResult State Val)
    (fuel extra : Nat) (s : State) :
    PartialObs.Refines
      (FuelOutcome.toPartialObs (runFuel step fuel s))
      (FuelOutcome.toPartialObs (runFuel step (fuel + extra) s)) := by
  cases hOut : runFuel step fuel s with
  | timeout =>
    simp only [FuelOutcome.toPartialObs]
    cases runFuel step (fuel + extra) s <;> exact ⟨[], rfl⟩
  | done v =>
    have hMore := runFuel_done_mono step hOut extra
    rw [hMore]
    exact ⟨rfl, rfl⟩
  | trap =>
    have hMore := runFuel_trap_mono step hOut extra
    rw [hMore]
    rfl

/-!
## Verification, Verso Docstring Roles, and `#guard_msgs` Suite (`Test/Basic`)
-/

namespace Tests

/--
info: @Pass.comp_correct : ∀ {L₁ : Lang} {L₂ : Lang} {L₃ : Lang} {P₁ : Pass L₁ L₂} {P₂ : Pass L₂ L₃},
  P₁.Correct → P₂.Correct → (P₁.comp P₂).Correct
-/
#guard_msgs in
#check @Pass.comp_correct

/--
info: @runFuel_toPartialObs_refines : ∀ {State : Type u_1} {Val : Type u_2} (step : State → StepResult State Val)
  (fuel extra : Nat) (s : State),
  (runFuel step fuel s).toPartialObs.Refines (runFuel step (fuel + extra) s).toPartialObs
-/
#guard_msgs in
#check @runFuel_toPartialObs_refines

/-- Two-step counter state machine that reaches `.done 0` from `2` in 3 fuel
steps. -/
def countdownStep (n : Nat) : StepResult Nat Nat :=
  match n with
  | 0 => .done 0
  | k + 1 => .next k

set_option doc.verso true in
/-- Verified Verso docstring using roles:
{name}`countdownStep` steps from {lean}`2` to {lean}`StepResult.done 0` under
{name}`runFuel` in {lit}`3` steps. -/
theorem countdownStep_done : runFuel countdownStep 3 2 = .done 0 := rfl

/-- Witness that 1 step of `countdownStep` from `2` times out. -/
theorem countdownStep_timeout_1 : runFuel countdownStep 1 2 = .timeout := rfl

/-- Witness that 1-step timeout refines 3-step normal return. -/
theorem countdownStep_refines_1_3 :
    PartialObs.Refines
      (FuelOutcome.toPartialObs (runFuel countdownStep 1 2))
      (FuelOutcome.toPartialObs (runFuel countdownStep 3 2)) :=
  runFuel_toPartialObs_refines countdownStep 1 2 2

/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.20 = ?m.20
but is expected to have type
  1 = 2
in the application
  ⟨rfl, rfl⟩
-/
#guard_msgs in
example : PartialObs.Refines (.returns ([] : List Unit) 1) (.returns [] 2) := by
  exact ⟨rfl, rfl⟩

/--
info: 'AnnealRefinement.Pass.comp_correct' does not depend on any axioms
-/
#guard_msgs in
#print axioms Pass.comp_correct

/--
info: 'AnnealRefinement.verify_with_pass' does not depend on any axioms
-/
#guard_msgs in
#print axioms verify_with_pass

/--
info: 'AnnealRefinement.runFuel_toPartialObs_refines' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms runFuel_toPartialObs_refines

end Tests

end AnnealRefinement

end
