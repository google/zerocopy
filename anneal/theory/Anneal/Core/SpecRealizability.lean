-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Trusted
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Anneal.ClassicalEm
import Anneal.MirTotal.Ops

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.ClassicalEm Anneal.MirTotal

/-!
# Realizability, Dichotomy, and Vacuity Calculus (`Core.SpecRealizability`)

Pure-kernel specification realizability, postcondition dichotomy, mutant-kill,
and observation-fibre calculus over Pass-1 foundation-locked Lean:

1. **Frozen 5-Class Cross-Language Vacuity Taxonomy (`VacuityClass`):**
   Canonical wire diagnostics (`canonicalName`, `all`, `mem_all`,
   `canonicalName_injective`, `ofCanonicalName?`) matching the frozen
   wire taxonomy for Rust contract checkers.
2. **Generic Relational Obligations (`PreconditionSatisfiable` through
   `MutantKilledBySpec`):** Full hierarchy, mutant-kill equivalence,
   observational determinism, vacuity-refutation rules (including
   `ForwardOutputInsensitive`, `Subsingleton`, and fibre insensitivity),
   disjunctive precondition splitting, monotonicity, and product composition.
3. **Specializations for `Trusted.MirModel` and `Trusted.MirSemantics`:**
   `NonVacuousPre`, `NonVacuousStatefulPre`, `NonVacuousQueryPre`,
   `NonVacuousBodySafetyPre`, stateless and stateful return-value dichotomy
   modulo `CallerMemory`, `Query`/`TerminalOut` outcome-fibre dichotomy, and
   direct realizability/dichotomy/vacuity bridges to `SatisfiesPost` and
   `BodyVerified` (zero `MetaM`, zero `sorry`, `0` `._unsafe_rec`, axioms
   strictly within `{propext, Classical.choice, Quot.sound}`).
-/

/-! ## Frozen 5-Class Cross-Language Vacuity Taxonomy -/

/-- Frozen 5-class cross-language specification vacuity taxonomy for
Lean static realizability checks and aligned Rust contract checks. -/
inductive VacuityClass : Type where
  | deadPrecondition
  | specViolation
  | trivialPostcondition
  | unboundReturnOutput
  | survivedAllMutants

/-- Structural equality on `VacuityClass`. -/
def VacuityClass.beq : VacuityClass → VacuityClass → Bool
  | .deadPrecondition, .deadPrecondition => true
  | .specViolation, .specViolation => true
  | .trivialPostcondition, .trivialPostcondition => true
  | .unboundReturnOutput, .unboundReturnOutput => true
  | .survivedAllMutants, .survivedAllMutants => true
  | _, _ => false

/-- Decidable equality on `VacuityClass`. -/
def VacuityClass.decEq (a b : VacuityClass) : Decidable (a = b) :=
  match a, b with
  | .deadPrecondition, .deadPrecondition => isTrue rfl
  | .specViolation, .specViolation => isTrue rfl
  | .trivialPostcondition, .trivialPostcondition => isTrue rfl
  | .unboundReturnOutput, .unboundReturnOutput => isTrue rfl
  | .survivedAllMutants, .survivedAllMutants => isTrue rfl
  | .deadPrecondition, .specViolation => isFalse (fun h => by cases h)
  | .deadPrecondition, .trivialPostcondition => isFalse (fun h => by cases h)
  | .deadPrecondition, .unboundReturnOutput => isFalse (fun h => by cases h)
  | .deadPrecondition, .survivedAllMutants => isFalse (fun h => by cases h)
  | .specViolation, .deadPrecondition => isFalse (fun h => by cases h)
  | .specViolation, .trivialPostcondition => isFalse (fun h => by cases h)
  | .specViolation, .unboundReturnOutput => isFalse (fun h => by cases h)
  | .specViolation, .survivedAllMutants => isFalse (fun h => by cases h)
  | .trivialPostcondition, .deadPrecondition => isFalse (fun h => by cases h)
  | .trivialPostcondition, .specViolation => isFalse (fun h => by cases h)
  | .trivialPostcondition, .unboundReturnOutput => isFalse (fun h => by cases h)
  | .trivialPostcondition, .survivedAllMutants => isFalse (fun h => by cases h)
  | .unboundReturnOutput, .deadPrecondition => isFalse (fun h => by cases h)
  | .unboundReturnOutput, .specViolation => isFalse (fun h => by cases h)
  | .unboundReturnOutput, .trivialPostcondition => isFalse (fun h => by cases h)
  | .unboundReturnOutput, .survivedAllMutants => isFalse (fun h => by cases h)
  | .survivedAllMutants, .deadPrecondition => isFalse (fun h => by cases h)
  | .survivedAllMutants, .specViolation => isFalse (fun h => by cases h)
  | .survivedAllMutants, .trivialPostcondition => isFalse (fun h => by cases h)
  | .survivedAllMutants, .unboundReturnOutput => isFalse (fun h => by cases h)

instance : BEq VacuityClass := ⟨VacuityClass.beq⟩

instance : DecidableEq VacuityClass := VacuityClass.decEq

instance : Inhabited VacuityClass := ⟨.deadPrecondition⟩

/-- Canonical wire and diagnostic name for each `VacuityClass`. -/
def VacuityClass.canonicalName : VacuityClass → String
  | .deadPrecondition => "DeadPrecondition"
  | .specViolation => "SpecViolation"
  | .trivialPostcondition => "TrivialPostcondition"
  | .unboundReturnOutput => "UnboundReturnOutput"
  | .survivedAllMutants => "SurvivedAllMutants"

private theorem listBeqUInt8Comp_refl (xs : List UInt8) :
    listBeqUInt8Comp xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    change (uint8BeqComp x x && listBeqUInt8Comp tl tl) = true
    have hx : uint8BeqComp x x = true := Nat.beq_refl x.toNat
    rw [hx, ih]
    rfl

/-- `VacuityClass.canonicalName` is injective across all 5 variants. -/
theorem VacuityClass.canonicalName_injective {a b : VacuityClass}
    (h : a.canonicalName = b.canonicalName) : a = b := by
  have hBytes : stringBeqComp a.canonicalName b.canonicalName = true := by
    rw [h]
    unfold stringBeqComp
    exact listBeqUInt8Comp_refl _
  cases a <;> cases b <;>
    first | rfl | exact False.elim (Bool.noConfusion hBytes)

/-- All five `VacuityClass` variants in their frozen cross-language wire
order. -/
def VacuityClass.all : List VacuityClass :=
  [.deadPrecondition, .specViolation, .trivialPostcondition,
    .unboundReturnOutput, .survivedAllMutants]

/-- `VacuityClass.all` enumerates every variant. -/
theorem VacuityClass.mem_all (c : VacuityClass) : c ∈ VacuityClass.all := by
  cases c
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · exact List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- Parse a canonical wire name back into its `VacuityClass` (`none` for any
other string), matching `VacuityClass.canonicalName` via pure UTF-8 equality. -/
def VacuityClass.ofCanonicalName? (name : String) : Option VacuityClass :=
  VacuityClass.all.find? (fun c => stringBeqComp c.canonicalName name)

/-- `VacuityClass.ofCanonicalName?` recovers any `VacuityClass` from its
canonical wire name. -/
theorem VacuityClass.ofCanonicalName?_canonicalName (c : VacuityClass) :
    VacuityClass.ofCanonicalName? c.canonicalName = some c := by
  cases c <;> rfl

/-! ## Part I — Pure Kernel Realizability and Observation Calculus -/

section PureCalculus

universe u v w u₁ u₂ v₁ v₂

/-! ### 1. Generic Relational Obligations -/

/-- Precondition `pre` admits at least one valid input witness. -/
def PreconditionSatisfiable {X : Type u} (pre : X → Prop) : Prop :=
  ∃ x, pre x

/-- Contract `(pre, post)` admits at least one valid input and satisfying
output. -/
def ContractRealizable {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∃ x, pre x ∧ ∃ y, post x y

/-- Contract `(pre, post)` has a satisfiable precondition and every valid input
admits at least one satisfying output. -/
def UniversalContractRealizable {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  PreconditionSatisfiable pre ∧ ∀ x, pre x → ∃ y, post x y

/-- Contract `(pre, post)` is nontrivial: some valid input admits both an
accepted output `y_ok` and a rejected output `y_bad`. -/
def PostconditionDichotomy {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∃ x, pre x ∧ (∃ y_ok, post x y_ok) ∧ (∃ y_bad, ¬ post x y_bad)

/-- Contract `(pre, post)` has a satisfiable precondition and every valid input
admits both an accepted output and a rejected output. -/
def PointwisePostconditionDichotomy {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  PreconditionSatisfiable pre ∧
    ∀ x, pre x → (∃ y_ok, post x y_ok) ∧ (∃ y_bad, ¬ post x y_bad)

/-- Postcondition `post` uniquely determines observation `obs y` for every
input satisfying `pre`. -/
def ContractDeterministicOn {X : Type u} {Y : Type v} {Z : Type w}
    (obs : Y → Z) (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∀ x y₁ y₂, pre x → post x y₁ → post x y₂ → obs y₁ = obs y₂

/-- Postcondition `post` uniquely determines the output value `y` on every
input satisfying `pre`. -/
def ContractDeterministic {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ContractDeterministicOn id pre post

/-- Postcondition `post` cannot distinguish any two outputs under `pre`. -/
def OutputInsensitive {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∀ x, pre x → ∀ y₁ y₂, post x y₁ ↔ post x y₂

/-- One-directional form of `OutputInsensitive`: under `pre`, accepting one
output forces accepting every other output. -/
def ForwardOutputInsensitive {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∀ x, pre x → ∀ y₁ y₂, post x y₁ → post x y₂

/-- Postcondition `post` achieves dichotomy within a single observation fibre
of `obs`, ruling out vacuous dichotomy caused solely by differing `obs`
boilerplate values. -/
def DichotomyModuloObservation {X : Type u} {Y : Type v} {Z : Type w}
    (obs : X → Y → Z) (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∃ x, pre x ∧ ∃ y_ok y_bad,
    obs x y_ok = obs x y_bad ∧ post x y_ok ∧ ¬ post x y_bad

/-- Concrete mutant witness: on valid input `x`, `y_ok` satisfies `post`,
while the distinct mutant output `y_bad ≠ y_ok` is rejected by `post`. -/
def MutantKilledBySpec {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) (x : X) (y_ok y_bad : Y) : Prop :=
  pre x ∧ y_bad ≠ y_ok ∧ post x y_ok ∧ ¬ post x y_bad

/-! ### 2. Core Hierarchy, Mutant-Kill, and Determinism Theorems -/

theorem ContractRealizable.preconditionSatisfiable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : ContractRealizable pre post) : PreconditionSatisfiable pre := by
  let ⟨x, hPre, _⟩ := h
  exact ⟨x, hPre⟩

theorem UniversalContractRealizable.preconditionSatisfiable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : UniversalContractRealizable pre post) : PreconditionSatisfiable pre :=
  h.1

theorem UniversalContractRealizable.contractRealizable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : UniversalContractRealizable pre post) :
    ContractRealizable pre post := by
  let ⟨⟨x, hPre⟩, hAll⟩ := h
  exact ⟨x, hPre, hAll x hPre⟩

theorem PostconditionDichotomy.contractRealizable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PostconditionDichotomy pre post) : ContractRealizable pre post := by
  let ⟨x, hPre, hOk, _⟩ := h
  exact ⟨x, hPre, hOk⟩

theorem PostconditionDichotomy.preconditionSatisfiable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PostconditionDichotomy pre post) : PreconditionSatisfiable pre :=
  h.contractRealizable.preconditionSatisfiable

theorem PointwisePostconditionDichotomy.universalContractRealizable
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PointwisePostconditionDichotomy pre post) :
    UniversalContractRealizable pre post :=
  ⟨h.1, fun x hPre => (h.2 x hPre).1⟩

theorem PointwisePostconditionDichotomy.postconditionDichotomy
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (h : PointwisePostconditionDichotomy pre post) :
    PostconditionDichotomy pre post := by
  let ⟨⟨x, hPre⟩, hAll⟩ := h
  exact ⟨x, hPre, hAll x hPre⟩

theorem DichotomyModuloObservation.postconditionDichotomy
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : X → Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (h : DichotomyModuloObservation obs pre post) :
    PostconditionDichotomy pre post := by
  let ⟨x, hPre, y_ok, y_bad, _, hOk, hBad⟩ := h
  exact ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩

theorem postconditionDichotomy_iff_dichotomyModuloObservation_const
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop} :
    PostconditionDichotomy pre post ↔
      DichotomyModuloObservation (fun (_ : X) (_ : Y) => PUnit.unit)
        pre post := by
  constructor
  · intro h
    let ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩ := h
    exact ⟨x, hPre, y_ok, y_bad, rfl, hOk, hBad⟩
  · exact DichotomyModuloObservation.postconditionDichotomy

/-- Postcondition dichotomy is equivalent to the existence of at least one
killed mutant. -/
theorem postconditionDichotomy_iff_exists_killed_mutant
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop} :
    PostconditionDichotomy pre post ↔
      ∃ x y_ok y_bad, MutantKilledBySpec pre post x y_ok y_bad := by
  constructor
  · intro h
    let ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩ := h
    refine ⟨x, y_ok, y_bad, hPre, ?_, hOk, hBad⟩
    intro hEq
    subst hEq
    exact hBad hOk
  · intro h
    let ⟨x, y_ok, y_bad, hPre, _, hOk, hBad⟩ := h
    exact ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩

/-- Observational determinism holds iff the postcondition kills every mutant
whose observation differs from an accepted output. -/
theorem contractDeterministicOn_iff_kills_every_obs_nonequivalent_mutant
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : Y → Z} {pre : X → Prop} {post : X → Y → Prop} :
    ContractDeterministicOn obs pre post ↔
      ∀ x y_ok y_bad,
        pre x → post x y_ok → obs y_bad ≠ obs y_ok → ¬ post x y_bad := by
  constructor
  · intro hDet x y_ok y_bad hPre hOk hNe hBad
    exact hNe (hDet x y_bad y_ok hPre hBad hOk)
  · intro hKill x y₁ y₂ hPre h1 h2
    exact Anneal.ClassicalEm.by_contra fun hNe =>
      hKill x y₁ y₂ hPre h1 (fun hEq => hNe hEq.symm) h2

/-- A universally realizable contract that is deterministic on an observation
with no isolated values satisfies pointwise postcondition dichotomy. -/
theorem pointwisePostconditionDichotomy_of_deterministicOn
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (hReal : UniversalContractRealizable pre post)
    (hDet : ContractDeterministicOn obs pre post)
    (hNontriv : ∀ y : Y, ∃ y' : Y, obs y' ≠ obs y) :
    PointwisePostconditionDichotomy pre post := by
  refine ⟨hReal.1, fun x hPre => ?_⟩
  let ⟨y_ok, hOk⟩ := hReal.2 x hPre
  let ⟨y_bad, hNe⟩ := hNontriv y_ok
  refine ⟨⟨y_ok, hOk⟩, ⟨y_bad, ?_⟩⟩
  intro hBad
  exact hNe (hDet x y_bad y_ok hPre hBad hOk)

/-- Functional specifications `post x y := y = f x` are always deterministic.
-/
theorem contractDeterministic_of_function
    {X : Type u} {Y : Type v} (pre : X → Prop) (f : X → Y) :
    ContractDeterministic pre (fun x y => y = f x) := by
  intro x y₁ y₂ _ h1 h2
  exact h1.trans h2.symm

/-- Functional specifications `post x y := y = f x` satisfy dichotomy whenever
`pre` is satisfiable and `Y` has at least two distinct elements. -/
theorem postconditionDichotomy_of_function
    {X : Type u} {Y : Type v} {pre : X → Prop} (f : X → Y)
    (hPre : PreconditionSatisfiable pre)
    (hTwo : ∃ y₁ y₂ : Y, y₁ ≠ y₂) :
    PostconditionDichotomy pre (fun x y => y = f x) := by
  let ⟨x, hx⟩ := hPre
  let ⟨y₁, y₂, hNe⟩ := hTwo
  refine ⟨x, hx, ⟨f x, rfl⟩, ?_⟩
  cases prop_em (y₁ = f x) with
  | inl h1 =>
    refine ⟨y₂, ?_⟩
    intro h2
    exact hNe (h1.trans h2.symm)
  | inr h1 =>
    exact ⟨y₁, h1⟩

/-! ### 3. Vacuity Refutations -/

theorem not_contractRealizable_of_unsat_pre
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hUnsat : ¬ PreconditionSatisfiable pre) :
    ¬ ContractRealizable pre post :=
  fun hReal => hUnsat hReal.preconditionSatisfiable

theorem not_postconditionDichotomy_of_unsat_pre
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hUnsat : ¬ PreconditionSatisfiable pre) :
    ¬ PostconditionDichotomy pre post :=
  fun hDich => hUnsat hDich.preconditionSatisfiable

theorem not_postconditionDichotomy_of_trivial
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hTriv : ∀ x y, pre x → post x y) :
    ¬ PostconditionDichotomy pre post := by
  intro h
  let ⟨x, hPre, _, ⟨y_bad, hNot⟩⟩ := h
  exact hNot (hTriv x y_bad hPre)

theorem not_postconditionDichotomy_of_impossible
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hImp : ∀ x y, pre x → ¬ post x y) :
    ¬ PostconditionDichotomy pre post := by
  intro h
  let ⟨x, hPre, ⟨y_ok, hOk⟩, _⟩ := h
  exact hImp x y_ok hPre hOk

theorem not_postconditionDichotomy_of_outputInsensitive
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : OutputInsensitive pre post) :
    ¬ PostconditionDichotomy pre post := by
  intro h
  let ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩ := h
  exact hBad ((hInsens x hPre y_ok y_bad).mp hOk)

theorem outputInsensitive_iff_forwardOutputInsensitive
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop} :
    OutputInsensitive pre post ↔ ForwardOutputInsensitive pre post := by
  constructor
  · intro h x hPre y₁ y₂ h1
    exact (h x hPre y₁ y₂).mp h1
  · intro h x hPre y₁ y₂
    exact ⟨h x hPre y₁ y₂, h x hPre y₂ y₁⟩

/-- A contract whose postcondition is forward output-insensitive under `pre`
can never satisfy `PostconditionDichotomy`, so flagging it is never a false
positive. -/
theorem not_postconditionDichotomy_of_forwardOutputInsensitive
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : ForwardOutputInsensitive pre post) :
    ¬ PostconditionDichotomy pre post := by
  intro h
  let ⟨x, hPre, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩ := h
  exact hBad (hInsens x hPre y_ok y_bad hOk)

/-- A tautological-under-`pre` postcondition is forward output-insensitive. -/
theorem forwardOutputInsensitive_of_trivial
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hTriv : ∀ x y, pre x → post x y) :
    ForwardOutputInsensitive pre post :=
  fun x hPre _ y₂ _ => hTriv x y₂ hPre

/-- An unrealizable-under-`pre` postcondition is forward output-insensitive. -/
theorem forwardOutputInsensitive_of_impossible
    {X : Type u} {Y : Type v} {pre : X → Prop} {post : X → Y → Prop}
    (hImp : ∀ x y, pre x → ¬ post x y) :
    ForwardOutputInsensitive pre post :=
  fun x hPre y₁ _ h1 => absurd h1 (hImp x y₁ hPre)

theorem not_postconditionDichotomy_of_subsingleton
    {X : Type u} {Y : Type v} [Subsingleton Y]
    {pre : X → Prop} {post : X → Y → Prop} :
    ¬ PostconditionDichotomy pre post := by
  intro h
  let ⟨_, _, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩ := h
  exact hBad (Eq.subst (Subsingleton.elim y_ok y_bad) hOk)

theorem not_dichotomyModuloObservation_of_fibre_insensitive
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : X → Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : ∀ x y₁ y₂,
      pre x → obs x y₁ = obs x y₂ → (post x y₁ ↔ post x y₂)) :
    ¬ DichotomyModuloObservation obs pre post := by
  intro h
  let ⟨x, hPre, y_ok, y_bad, hObsEq, hOk, hBad⟩ := h
  exact hBad ((hInsens x y_ok y_bad hPre hObsEq).mp hOk)

/-- One-directional form of
`not_dichotomyModuloObservation_of_fibre_insensitive`:
a postcondition that cannot tell apart two outputs sharing an observation has
no dichotomy modulo that observation. -/
theorem not_dichotomyModuloObservation_of_fibre_forwardInsensitive
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : X → Y → Z} {pre : X → Prop} {post : X → Y → Prop}
    (hInsens : ∀ x y₁ y₂, pre x → obs x y₁ = obs x y₂ → post x y₁ → post x y₂) :
    ¬ DichotomyModuloObservation obs pre post := by
  intro h
  let ⟨x, hPre, y_ok, y_bad, hObsEq, hOk, hBad⟩ := h
  exact hBad (hInsens x y_ok y_bad hPre hObsEq hOk)

theorem not_postconditionDichotomy_of_post_true
    {X : Type u} {Y : Type v} (pre : X → Prop) :
    ¬ PostconditionDichotomy pre (fun (_ : X) (_ : Y) => True) :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => True.intro)

theorem not_contractRealizable_of_post_false
    {X : Type u} {Y : Type v} (pre : X → Prop) :
    ¬ ContractRealizable pre (fun (_ : X) (_ : Y) => False) := by
  intro h
  let ⟨_, _, _, hFalse⟩ := h
  exact hFalse

/-! ### 4. Monotonicity, Weakening, and Product Composition -/

theorem PreconditionSatisfiable.mono
    {X : Type u} {pre₁ pre₂ : X → Prop}
    (hImp : ∀ x, pre₁ x → pre₂ x)
    (h : PreconditionSatisfiable pre₁) :
    PreconditionSatisfiable pre₂ := by
  let ⟨x, h1⟩ := h
  exact ⟨x, hImp x h1⟩

theorem ContractRealizable.mono
    {X : Type u} {Y : Type v} {pre₁ pre₂ : X → Prop}
    {post₁ post₂ : X → Y → Prop}
    (hPre : ∀ x, pre₁ x → pre₂ x)
    (hPost : ∀ x y, pre₁ x → post₁ x y → post₂ x y)
    (h : ContractRealizable pre₁ post₁) :
    ContractRealizable pre₂ post₂ := by
  let ⟨x, hx, y, hy⟩ := h
  exact ⟨x, hPre x hx, y, hPost x y hx hy⟩

theorem ContractDeterministicOn.anti
    {X : Type u} {Y : Type v} {Z : Type w}
    {obs : Y → Z} {pre₁ pre₂ : X → Prop} {post₁ post₂ : X → Y → Prop}
    (hPre : ∀ x, pre₂ x → pre₁ x)
    (hPost : ∀ x y, pre₂ x → post₂ x y → post₁ x y)
    (hDet : ContractDeterministicOn obs pre₁ post₁) :
    ContractDeterministicOn obs pre₂ post₂ := by
  intro x y₁ y₂ hx h1 h2
  exact hDet x y₁ y₂ (hPre x hx) (hPost x y₁ hx h1) (hPost x y₂ hx h2)

theorem DichotomyModuloObservation.of_refining_obs
    {X : Type u} {Y : Type v} {Z₁ : Type w} {Z₂ : Type u₁}
    {obs₁ : X → Y → Z₁} {obs₂ : X → Y → Z₂}
    {pre : X → Prop} {post : X → Y → Prop}
    (hRef : ∀ x y₁ y₂, obs₁ x y₁ = obs₁ x y₂ → obs₂ x y₁ = obs₂ x y₂)
    (h : DichotomyModuloObservation obs₁ pre post) :
    DichotomyModuloObservation obs₂ pre post := by
  let ⟨x, hPre, y_ok, y_bad, hObsEq, hOk, hBad⟩ := h
  exact ⟨x, hPre, y_ok, y_bad, hRef x y_ok y_bad hObsEq, hOk, hBad⟩

/-- Disjunctive preconditions satisfy `PostconditionDichotomy` iff at least
one branch satisfies dichotomy: a multi-branch contract that genuinely binds
its output on one valid branch is not vacuous merely because another branch is
weaker. -/
theorem postconditionDichotomy_or_pre_iff
    {X : Type u} {Y : Type v} {pre₁ pre₂ : X → Prop} {post : X → Y → Prop} :
    PostconditionDichotomy (fun x => pre₁ x ∨ pre₂ x) post ↔
      PostconditionDichotomy pre₁ post ∨ PostconditionDichotomy pre₂ post := by
  constructor
  · intro h
    let ⟨x, hPre, hOk, hBad⟩ := h
    cases hPre with
    | inl h1 => exact Or.inl ⟨x, h1, hOk, hBad⟩
    | inr h2 => exact Or.inr ⟨x, h2, hOk, hBad⟩
  · intro hOr
    cases hOr with
    | inl h =>
      let ⟨x, h1, hOk, hBad⟩ := h
      exact ⟨x, Or.inl h1, hOk, hBad⟩
    | inr h =>
      let ⟨x, h2, hOk, hBad⟩ := h
      exact ⟨x, Or.inr h2, hOk, hBad⟩

/-- A disjunctive precondition refutes `PostconditionDichotomy` iff every
branch fails dichotomy (for example, one branch is unsatisfiable and the other
makes `post` output-insensitive). -/
theorem not_postconditionDichotomy_or_pre_iff
    {X : Type u} {Y : Type v} {pre₁ pre₂ : X → Prop} {post : X → Y → Prop} :
    ¬ PostconditionDichotomy (fun x => pre₁ x ∨ pre₂ x) post ↔
      ¬ PostconditionDichotomy pre₁ post ∧
        ¬ PostconditionDichotomy pre₂ post := by
  constructor
  · intro hNot
    exact ⟨
      fun h1 => hNot
        ((postconditionDichotomy_or_pre_iff (pre₁ := pre₁) (pre₂ := pre₂)).mpr
          (Or.inl h1)),
      fun h2 => hNot
        ((postconditionDichotomy_or_pre_iff (pre₁ := pre₁) (pre₂ := pre₂)).mpr
          (Or.inr h2))⟩
  · intro hPair hOr
    let ⟨hNot1, hNot2⟩ := hPair
    cases (postconditionDichotomy_or_pre_iff
        (pre₁ := pre₁) (pre₂ := pre₂)).mp hOr with
    | inl h1 => exact hNot1 h1
    | inr h2 => exact hNot2 h2

theorem preconditionSatisfiable_prod
    {X₁ : Type u₁} {X₂ : Type u₂} {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    (h₁ : PreconditionSatisfiable pre₁) (h₂ : PreconditionSatisfiable pre₂) :
    PreconditionSatisfiable (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2) := by
  let ⟨x₁, hx₁⟩ := h₁
  let ⟨x₂, hx₂⟩ := h₂
  exact ⟨(x₁, x₂), hx₁, hx₂⟩

theorem contractRealizable_prod
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : ContractRealizable pre₁ post₁)
    (h₂ : ContractRealizable pre₂ post₂) :
    ContractRealizable
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  let ⟨x₁, hx₁, y₁, hy₁⟩ := h₁
  let ⟨x₂, hx₂, y₂, hy₂⟩ := h₂
  exact ⟨(x₁, x₂), ⟨hx₁, hx₂⟩, (y₁, y₂), ⟨hy₁, hy₂⟩⟩

theorem postconditionDichotomy_prod_left
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : PostconditionDichotomy pre₁ post₁)
    (h₂ : ContractRealizable pre₂ post₂) :
    PostconditionDichotomy
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  let ⟨x₁, hx₁, ⟨y₁_ok, hy₁_ok⟩, ⟨y₁_bad, hy₁_bad⟩⟩ := h₁
  let ⟨x₂, hx₂, y₂_ok, hy₂_ok⟩ := h₂
  refine ⟨(x₁, x₂), ⟨hx₁, hx₂⟩, ⟨(y₁_ok, y₂_ok), hy₁_ok, hy₂_ok⟩,
    ⟨(y₁_bad, y₂_ok), ?_⟩⟩
  intro hBad
  exact hy₁_bad hBad.1

theorem postconditionDichotomy_prod_right
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : ContractRealizable pre₁ post₁)
    (h₂ : PostconditionDichotomy pre₂ post₂) :
    PostconditionDichotomy
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  let ⟨x₁, hx₁, y₁_ok, hy₁_ok⟩ := h₁
  let ⟨x₂, hx₂, ⟨y₂_ok, hy₂_ok⟩, ⟨y₂_bad, hy₂_bad⟩⟩ := h₂
  refine ⟨(x₁, x₂), ⟨hx₁, hx₂⟩, ⟨(y₁_ok, y₂_ok), hy₁_ok, hy₂_ok⟩,
    ⟨(y₁_ok, y₂_bad), ?_⟩⟩
  intro hBad
  exact hy₂_bad hBad.2

theorem contractDeterministic_prod
    {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
    {pre₁ : X₁ → Prop} {pre₂ : X₂ → Prop}
    {post₁ : X₁ → Y₁ → Prop} {post₂ : X₂ → Y₂ → Prop}
    (h₁ : ContractDeterministic pre₁ post₁)
    (h₂ : ContractDeterministic pre₂ post₂) :
    ContractDeterministic
      (fun p : X₁ × X₂ => pre₁ p.1 ∧ pre₂ p.2)
      (fun (p : X₁ × X₂) (q : Y₁ × Y₂) => post₁ p.1 q.1 ∧ post₂ p.2 q.2) := by
  intro p q q' hp hq hq'
  let ⟨x₁, x₂⟩ := p
  let ⟨y₁, y₂⟩ := q
  let ⟨y₁', y₂'⟩ := q'
  let ⟨hx₁, hx₂⟩ := hp
  let ⟨h1, h2⟩ := hq
  let ⟨h1', h2'⟩ := hq'
  have eq1 : y₁ = y₁' := h₁ x₁ y₁ y₁' hx₁ h1 h1'
  have eq2 : y₂ = y₂' := h₂ x₂ y₂ y₂' hx₂ h2 h2'
  cases eq1
  cases eq2
  rfl

end PureCalculus

/-! ### 5. Specializations for `Trusted.MirModel` and `Trusted.MirSemantics` -/

section MirSpecializations

/-! #### Non-Vacuity Obligations -/

/-- Witness obligation asserting that a value-level precondition `pre` is
satisfiable. -/
def NonVacuousPre (pre : List Val → Prop) : Prop :=
  ∃ args, pre args

/-- Witness obligation asserting that a caller-memory-aware precondition `pre`
is satisfiable. -/
def NonVacuousStatefulPre (pre : List Val → CallerMemory → Prop) : Prop :=
  ∃ args mem, pre args mem

/-- Witness obligation asserting that a `Query`-level precondition `pre` is
satisfiable. -/
def NonVacuousQueryPre (pre : Query → Prop) : Prop :=
  ∃ q, pre q

/-- Witness obligation asserting that an `unsafe` body's `BodyVerified` safety
precondition admits at least one `ValidEntryArgs`-compatible argument list. -/
def NonVacuousBodySafetyPre (body : Body) (safetyPre : List Val → Prop) :
    Prop :=
  ∃ args, ValidEntryArgs body args ∧ safetyPre args

theorem preconditionSatisfiable_iff_nonVacuousPre (pre : List Val → Prop) :
    PreconditionSatisfiable pre ↔ NonVacuousPre pre :=
  Iff.rfl

theorem preconditionSatisfiable_iff_nonVacuousStatefulPre
    (pre : List Val → CallerMemory → Prop) :
    PreconditionSatisfiable
        (fun p : List Val × CallerMemory => pre p.1 p.2) ↔
      NonVacuousStatefulPre pre := by
  constructor
  · intro h
    let ⟨⟨args, mem⟩, hPre⟩ := h
    exact ⟨args, mem, hPre⟩
  · intro h
    let ⟨args, mem, hPre⟩ := h
    exact ⟨(args, mem), hPre⟩

theorem preconditionSatisfiable_iff_nonVacuousQueryPre (pre : Query → Prop) :
    PreconditionSatisfiable pre ↔ NonVacuousQueryPre pre :=
  Iff.rfl

theorem nonVacuousBodySafetyPre_iff_preconditionSatisfiable
    (body : Body) (safetyPre : List Val → Prop) :
    NonVacuousBodySafetyPre body safetyPre ↔
      PreconditionSatisfiable
        (fun args => ValidEntryArgs body args ∧ safetyPre args) :=
  Iff.rfl

/-- If an `unsafe` body's `safetyPre` admits no `ValidEntryArgs`-compatible
argument list, the safety proof obligation in `BodyVerified` holds vacuously
regardless of what `body` executes. -/
theorem bodyVerified_vacuous_safety_of_unsat
    {p : Program} {defId : DefId} {body : Body} {safetyPre : List Val → Prop}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true)
    (hUnsafe : body.isUnsafe = true)
    (hUnsat : ¬ NonVacuousBodySafetyPre body safetyPre) :
    BodyVerified p defId body safetyPre := by
  refine ⟨hBody, hAdm, fun args hValid hSafe => ?_⟩
  exact False.elim (hUnsat ⟨args, hValid, hSafe hUnsafe⟩)

/-! #### Stateless `List Val → Val` Contracts -/

def StatelessPreSatisfiable (pre : List Val → Prop) : Prop :=
  PreconditionSatisfiable pre

def StatelessRealizable (pre : List Val → Prop)
    (post : List Val → Val → Prop) : Prop :=
  ContractRealizable pre post

def StatelessUniversalRealizable (pre : List Val → Prop)
    (post : List Val → Val → Prop) : Prop :=
  UniversalContractRealizable pre post

def StatelessDichotomy (pre : List Val → Prop)
    (post : List Val → Val → Prop) : Prop :=
  PostconditionDichotomy pre post

def StatelessDeterministic (pre : List Val → Prop)
    (post : List Val → Val → Prop) : Prop :=
  ContractDeterministic pre post

theorem statelessPreSatisfiable_iff_nonVacuousPre (pre : List Val → Prop) :
    StatelessPreSatisfiable pre ↔ NonVacuousPre pre :=
  Iff.rfl

theorem StatelessDichotomy.toRealizable
    {pre : List Val → Prop} {post : List Val → Val → Prop}
    (h : StatelessDichotomy pre post) : StatelessRealizable pre post :=
  PostconditionDichotomy.contractRealizable h

theorem StatelessRealizable.toPreSatisfiable
    {pre : List Val → Prop} {post : List Val → Val → Prop}
    (h : StatelessRealizable pre post) : StatelessPreSatisfiable pre :=
  ContractRealizable.preconditionSatisfiable h

/-! #### Stateful `(List Val, CallerMemory)` Contracts -/

def StatefulPreSatisfiable (pre : List Val → CallerMemory → Prop) : Prop :=
  PreconditionSatisfiable (fun p : List Val × CallerMemory => pre p.1 p.2)

def StatefulRealizable (pre : List Val → CallerMemory → Prop)
    (post : List Val → CallerMemory → Val → CallerMemory → Prop) : Prop :=
  ContractRealizable
    (fun p : List Val × CallerMemory => pre p.1 p.2)
    (fun (p : List Val × CallerMemory) (q : Val × CallerMemory) =>
      post p.1 p.2 q.1 q.2)

def StatefulDichotomy (pre : List Val → CallerMemory → Prop)
    (post : List Val → CallerMemory → Val → CallerMemory → Prop) : Prop :=
  PostconditionDichotomy
    (fun p : List Val × CallerMemory => pre p.1 p.2)
    (fun (p : List Val × CallerMemory) (q : Val × CallerMemory) =>
      post p.1 p.2 q.1 q.2)

/-- Strict return-value dichotomy for a stateful contract: holds the post-call
`CallerMemory` fixed so that a spec constraining only `mem'` while leaving the
return value unconstrained cannot pass. -/
def StatefulReturnDichotomy (pre : List Val → CallerMemory → Prop)
    (post : List Val → CallerMemory → Val → CallerMemory → Prop) : Prop :=
  ∃ args mem mem' v_ok v_bad,
    pre args mem ∧ post args mem v_ok mem' ∧ ¬ post args mem v_bad mem'

def StatefulDeterministic (pre : List Val → CallerMemory → Prop)
    (post : List Val → CallerMemory → Val → CallerMemory → Prop) : Prop :=
  ContractDeterministic
    (fun p : List Val × CallerMemory => pre p.1 p.2)
    (fun (p : List Val × CallerMemory) (q : Val × CallerMemory) =>
      post p.1 p.2 q.1 q.2)

theorem statefulPreSatisfiable_iff_nonVacuousStatefulPre
    (pre : List Val → CallerMemory → Prop) :
    StatefulPreSatisfiable pre ↔ NonVacuousStatefulPre pre :=
  preconditionSatisfiable_iff_nonVacuousStatefulPre pre

theorem statefulReturnDichotomy_iff_moduloMemory
    (pre : List Val → CallerMemory → Prop)
    (post : List Val → CallerMemory → Val → CallerMemory → Prop) :
    StatefulReturnDichotomy pre post ↔
      DichotomyModuloObservation
        (fun (_ : List Val × CallerMemory) (q : Val × CallerMemory) => q.2)
        (fun p : List Val × CallerMemory => pre p.1 p.2)
        (fun (p : List Val × CallerMemory) (q : Val × CallerMemory) =>
          post p.1 p.2 q.1 q.2) := by
  constructor
  · intro h
    let ⟨args, mem, mem', v_ok, v_bad, hPre, hOk, hBad⟩ := h
    exact ⟨(args, mem), hPre, (v_ok, mem'), (v_bad, mem'), rfl, hOk, hBad⟩
  · intro h
    let ⟨⟨args, mem⟩, hPre, ⟨v_ok, m_ok⟩, ⟨v_bad, m_bad⟩,
        hMemEq, hOk, hBad⟩ := h
    dsimp only at hMemEq
    subst hMemEq
    exact ⟨args, mem, m_ok, v_ok, v_bad, hPre, hOk, hBad⟩

theorem StatefulReturnDichotomy.toDichotomy
    {pre : List Val → CallerMemory → Prop}
    {post : List Val → CallerMemory → Val → CallerMemory → Prop}
    (h : StatefulReturnDichotomy pre post) :
    StatefulDichotomy pre post :=
  ((statefulReturnDichotomy_iff_moduloMemory pre post).mp
    h).postconditionDichotomy

/-- A stateful postcondition that cannot tell two return values apart once
`(args, mem, mem')` are fixed has no strict return-value dichotomy, however
tightly it constrains `mem'`. -/
theorem not_statefulReturnDichotomy_of_returnInsensitive
    {pre : List Val → CallerMemory → Prop}
    {post : List Val → CallerMemory → Val → CallerMemory → Prop}
    (hInsens : ∀ args mem mem' v₁ v₂,
      pre args mem → post args mem v₁ mem' → post args mem v₂ mem') :
    ¬ StatefulReturnDichotomy pre post := by
  intro h
  let ⟨args, mem, mem', v_ok, v_bad, hPre, hOk, hBad⟩ := h
  exact hBad (hInsens args mem mem' v_ok v_bad hPre hOk)

theorem StatefulDichotomy.toRealizable
    {pre : List Val → CallerMemory → Prop}
    {post : List Val → CallerMemory → Val → CallerMemory → Prop}
    (h : StatefulDichotomy pre post) : StatefulRealizable pre post :=
  PostconditionDichotomy.contractRealizable h

theorem StatefulRealizable.toPreSatisfiable
    {pre : List Val → CallerMemory → Prop}
    {post : List Val → CallerMemory → Val → CallerMemory → Prop}
    (h : StatefulRealizable pre post) : StatefulPreSatisfiable pre :=
  ContractRealizable.preconditionSatisfiable h

/-! #### `Query` / `Out` and `SatisfiesPost` (`TerminalOut`) Contracts -/

/-- Strict return-value dichotomy for `(Query, Out)` contracts: holds
`out.callerMem` fixed so specs constraining only caller-visible memory do not
qualify as binding the returned `Val`. -/
def QueryOutReturnDichotomy (pre : Query → Prop)
    (post : Query → Out → Prop) : Prop :=
  ∃ q callerMem' v_ok v_bad,
    pre q ∧ post q ⟨v_ok, callerMem'⟩ ∧ ¬ post q ⟨v_bad, callerMem'⟩

theorem queryOutReturnDichotomy_iff_moduloCallerMem
    (pre : Query → Prop) (post : Query → Out → Prop) :
    QueryOutReturnDichotomy pre post ↔
      DichotomyModuloObservation
        (fun (_ : Query) (out : Out) => out.callerMem) pre post := by
  constructor
  · intro h
    let ⟨q, callerMem', v_ok, v_bad, hPre, hOk, hBad⟩ := h
    exact ⟨q, hPre, ⟨v_ok, callerMem'⟩, ⟨v_bad, callerMem'⟩, rfl, hOk, hBad⟩
  · intro h
    let ⟨q, hPre, ⟨v_ok, m_ok⟩, ⟨v_bad, m_bad⟩, hMemEq, hOk, hBad⟩ := h
    dsimp only at hMemEq
    subst hMemEq
    exact ⟨q, m_ok, v_ok, v_bad, hPre, hOk, hBad⟩

theorem QueryOutReturnDichotomy.toDichotomy
    {pre : Query → Prop} {post : Query → Out → Prop}
    (h : QueryOutReturnDichotomy pre post) :
    PostconditionDichotomy pre post :=
  ((queryOutReturnDichotomy_iff_moduloCallerMem pre post).mp
    h).postconditionDichotomy

theorem not_queryOutReturnDichotomy_of_returnInsensitive
    {pre : Query → Prop} {post : Query → Out → Prop}
    (hInsens : ∀ q callerMem' v₁ v₂,
      pre q → post q ⟨v₁, callerMem'⟩ → post q ⟨v₂, callerMem'⟩) :
    ¬ QueryOutReturnDichotomy pre post := by
  intro h
  let ⟨q, callerMem', v_ok, v_bad, hPre, hOk, hBad⟩ := h
  exact hBad (hInsens q callerMem' v_ok v_bad hPre hOk)

/-- Observation projection on `TerminalOut` isolating normal-return caller
memory (`Sum.inl out.callerMem`) from unwind caller memory (`Sum.inr mem`),
so dichotomy within one fibre must distinguish normal return values `out.ret`.
-/
def terminalReturnObs (_q : Query) :
    TerminalOut → Sum CallerMemory CallerMemory
  | .returned out => .inl out.callerMem
  | .unwound mem => .inr mem

/-- Strict normal-return dichotomy for `(Query, TerminalOut)` contracts: rules
out vacuous dichotomies that only distinguish `.returned` from `.unwound` or
only constrain `out.callerMem`. -/
def TerminalReturnDichotomy (pre : Query → Prop)
    (post : Query → TerminalOut → Prop) : Prop :=
  ∃ q callerMem' v_ok v_bad,
    pre q ∧
      post q (.returned ⟨v_ok, callerMem'⟩) ∧
      ¬ post q (.returned ⟨v_bad, callerMem'⟩)

theorem terminalReturnDichotomy_iff_moduloObs
    (pre : Query → Prop) (post : Query → TerminalOut → Prop) :
    TerminalReturnDichotomy pre post ↔
      DichotomyModuloObservation terminalReturnObs pre post := by
  constructor
  · intro h
    let ⟨q, callerMem', v_ok, v_bad, hPre, hOk, hBad⟩ := h
    exact ⟨q, hPre, .returned ⟨v_ok, callerMem'⟩,
      .returned ⟨v_bad, callerMem'⟩, rfl, hOk, hBad⟩
  · intro h
    let ⟨q, hPre, y_ok, y_bad, hObsEq, hOk, hBad⟩ := h
    cases y_ok with
    | returned o_ok =>
      cases y_bad with
      | returned o_bad =>
        dsimp only [terminalReturnObs] at hObsEq
        injection hObsEq with hMemEq
        let ⟨v_ok, m_ok⟩ := o_ok
        let ⟨v_bad, m_bad⟩ := o_bad
        dsimp only at hMemEq
        subst hMemEq
        exact ⟨q, m_ok, v_ok, v_bad, hPre, hOk, hBad⟩
      | unwound _ =>
        dsimp only [terminalReturnObs] at hObsEq
        cases hObsEq
    | unwound m_ok =>
      cases y_bad with
      | returned _ =>
        dsimp only [terminalReturnObs] at hObsEq
        cases hObsEq
      | unwound m_bad =>
        dsimp only [terminalReturnObs] at hObsEq
        injection hObsEq with hMemEq
        subst hMemEq
        exact False.elim (hBad hOk)

theorem TerminalReturnDichotomy.toDichotomy
    {pre : Query → Prop} {post : Query → TerminalOut → Prop}
    (h : TerminalReturnDichotomy pre post) :
    PostconditionDichotomy pre post :=
  ((terminalReturnDichotomy_iff_moduloObs pre post).mp h).postconditionDichotomy

theorem not_terminalReturnDichotomy_of_returnInsensitive
    {pre : Query → Prop} {post : Query → TerminalOut → Prop}
    (hInsens : ∀ q callerMem' v₁ v₂,
      pre q →
      post q (.returned ⟨v₁, callerMem'⟩) →
      post q (.returned ⟨v₂, callerMem'⟩)) :
    ¬ TerminalReturnDichotomy pre post := by
  intro h
  let ⟨q, callerMem', v_ok, v_bad, hPre, hOk, hBad⟩ := h
  exact hBad (hInsens q callerMem' v_ok v_bad hPre hOk)

/-- A concrete behavior witness `Behavior p q out` together with `pre q` and
`SatisfiesPost p q (post q)` witnesses `ContractRealizable pre post`. -/
theorem satisfiesPost_contractRealizable
    {p : Program} {pre : Query → Prop} {post : Query → TerminalOut → Prop}
    {q : Query} {out : TerminalOut}
    (hPre : pre q) (hBeh : Behavior p q out)
    (hSat : SatisfiesPost p q (post q)) :
    ContractRealizable pre post :=
  ⟨q, hPre, out, hSat.2 out hBeh⟩

/-- Total termination on a satisfiable precondition `pre` paired with
`SatisfiesPost p q (post q)` yields `UniversalContractRealizable pre post`. -/
theorem satisfiesPost_universalRealizable_of_terminates
    {p : Program} {pre : Query → Prop} {post : Query → TerminalOut → Prop}
    (hPreSat : PreconditionSatisfiable pre)
    (hTerm : ∀ q, pre q → ∃ out, Behavior p q out)
    (hSat : ∀ q, pre q → SatisfiesPost p q (post q)) :
    UniversalContractRealizable pre post := by
  refine ⟨hPreSat, fun q hPre => ?_⟩
  let ⟨out, hBeh⟩ := hTerm q hPre
  exact ⟨out, (hSat q hPre).2 out hBeh⟩

/-- A `Behavior p q out` witness plus a refuted mutant outcome
`¬ post q out_bad` establishes `PostconditionDichotomy pre post` from
`SatisfiesPost p q (post q)`. -/
theorem satisfiesPost_postconditionDichotomy
    {p : Program} {pre : Query → Prop} {post : Query → TerminalOut → Prop}
    {q : Query} {out out_bad : TerminalOut}
    (hPre : pre q) (hBeh : Behavior p q out)
    (hSat : SatisfiesPost p q (post q)) (hBad : ¬ post q out_bad) :
    PostconditionDichotomy pre post :=
  ⟨q, hPre, ⟨out, hSat.2 out hBeh⟩, ⟨out_bad, hBad⟩⟩

/-- A normal-return behavior witness plus a refuted return value mutant in the
same post-call `CallerMemory` establishes `TerminalReturnDichotomy pre post`
from `SatisfiesPost p q (post q)`. -/
theorem satisfiesPost_terminalReturnDichotomy
    {p : Program} {pre : Query → Prop} {post : Query → TerminalOut → Prop}
    {q : Query} {callerMem' : CallerMemory} {v_ok v_bad : Val}
    (hPre : pre q)
    (hBeh : Behavior p q (.returned ⟨v_ok, callerMem'⟩))
    (hSat : SatisfiesPost p q (post q))
    (hBad : ¬ post q (.returned ⟨v_bad, callerMem'⟩)) :
    TerminalReturnDichotomy pre post :=
  ⟨q, callerMem', v_ok, v_bad, hPre,
    hSat.2 (.returned ⟨v_ok, callerMem'⟩) hBeh, hBad⟩

end MirSpecializations

end Anneal.Core
