-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Core

/-!
# Specification Adequacy, Vacuity Detection, and Mutation Testing: Specification Adequacy, Polarity Vacuity, and Mutation Adequacy

This standalone Lean 4 (`v4.34.1`, `prelude` + `Init.Core`) module mechanizes
the formal foundations of Vacuity and Mutation Adequacy for Anneal's Ground-Up Verification
Framework:

1. **Core Refinement Kernel (`Trusted`):**
   Embeds the core definitions from `Trusted/Refinement.lean` (`Preorder`,
   `Partial`, `Behavior`, `Language`, `SpecOn`, `SpineSpecOn`, `NonVacuousOn`,
   `ProductiveOn`, `VerifiedOn`, `VerifiedSpine`, `RefutedOn`,
   `RefutedProductiveOn`, `VerifiedWithCanariesOn`, `VerifiedSpineWithCanaries`,
   `Obligation`, `TrustPolicy`, `EmittedArtifact`, `NoDupIds`,
   `VerificationResult`, `VerificationUnit`, `UnitTheorem`, and
   `StrictUnitTheorem`).
2. **Elementary Ground-Level Predicates (`SafeAt`, `Produces`) and Equivalence
   to `VerifiedSpine`:**
   Proves that a software engineer's elementary ground intuition—every valid
   input is safe (`SafeAt`), produces at least one observable outcome
   (`Produces`), and every produced outcome satisfies `obsPost`—is
   constructively equivalent (`↔`) to `Language.VerifiedSpine` on any inhabited
   precondition (`ground_spec_iff_verifiedSpine`).
3. **Kupferman-Vardi Polarity Vacuity Formalization:**
   Formalizes Kupferman and Vardi's (CHARME 1999 / STTT 2003) polarity-based
   subformula replacement on Hoare/refinement triples:
   - Replacing positive-polarity `post` with `⊥ := fun _ _ => False` yields
     `KVAntecedentVacuous`, which is strictly refuted by `ProductiveOn` +
     `∃ q, pre q` (`kv_non_vacuous_antecedent`).
   - Replacing `obsPost` with `⊤ := fun _ _ => True` yields consequent
     triviality (`KVConsequentVacuous`), which passes single-model
     Kupferman-Vardi vacuity (`kv_single_model_blind_to_trivial_consequent`)
     but is strictly refuted by `VerifiedSpineWithCanaries` with a productive
     mutant (`kv_non_vacuous_consequent`).
4. **Budd-Angluin Mutation Adequacy & The Five-Way Anti-Pathology Squeeze:**
   Formalizes `GroundTwoSidedWitness` using only `pre`, `SafeAt`, `Produces`,
   and `obsPost`, proves that it constructively implies
   `VerifiedSpineWithCanaries`
   (`groundTwoSidedWitness_implies_verifiedSpineWithCanaries`), and proves
   `groundTwoSidedWitness_five_way_anti_pathology`, which simultaneously forces:
   - `(a)` `v_good ≠ v_bad` (distinct ground observable values),
   - `(b)` `∃ q, pre q` (inhabited precondition),
   - `(c)` `¬ (∀ q v, pre q → obsPost q v)` (non-trivial postcondition),
   - `(d)` `¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂)` and
     `Subsingleton SemObs → False` (non-constant observable spine), and
   - `(e)` `L.sem p_good ≠ L.sem p_bad` (AST-sensitive semantics).
5. **Verifier/Judge Tool Bi-Discrimination (`check : L.Prog → Bool`):**
   Formalizes `SoundAndNonTrivialVerifier` and proves that any sound boolean
   verifier accepting `p_good` where `p_bad` is refuted must reject `p_bad`
   (`verifier_rejects_mutant`), cannot be a dead verifier (`check ≠ fun _ =>
   false`), and cannot be a rubber-stamp verifier (`check ≠ fun _ => true`).
6. **Mechanized Replay of the Anneal V1 `abs` Mutation Matrix:**
   Models the contract-mutation cases from the empirical probe
   `anneal-v1-contract-mutation-adequacy-2026-09-28` (`false_precondition`,
   `weak_relation_zero_body`, and complete `abs` specification with negative
   canaries `zeroBody` and `identityBody`).

All theorems in this file are 100% constructive and depend on zero axioms
(`sorryAx`, `Classical.choice`, and `Lean.ofReduceBool` are completely absent).
-/

namespace Trusted

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`), read "`b₁` is at
    least as defined as `b₂` and permits no more observable outcomes than
    `b₂`." -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever `B` is a `Preorder`. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partiality carrier representing `B ∪ {UB}` without
    `Classical.choice`. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

/-- The Undefined Behavior top element (`⊤`, `defined := False`) of
    `Partial B`. -/
def Partial.ub {B : Type u} : Partial B :=
  ⟨False, False.elim⟩

/-- The bottom predicate element (`⊥`, `defined := True`, `val := fun _ _ =>
    False`) of `Partial (Out → Prop)`, representing an empty outcome set
    ("Dijkstra's miracle"). -/
def Partial.bot {Out : Type u} : Partial (Out → Prop) :=
  ⟨True, fun _ _ => False⟩

/-- Directional demonic refinement on `Partial B`: whenever `p₂` is defined,
    `p₁` must also be defined and its value must refine `p₂`'s value. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Query-indexed partial behaviors `Query → Partial (Out → Prop)`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language parameterized by its representation-invariant observable
    spine `SemObs`. -/
structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out
  dom   : Query → Prop := fun _ => True

/-- Construct a `Language` whose concrete outcomes `Out` coincide with its
    observable spine (`SemObs := Out`, `obs := id`). -/
abbrev Language.mkSimple (Prog Query Out : Type)
    (sem : Prog → Behavior Query Out) : Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := fun o => o
  sem   := sem

/-- Specialize a language's intrinsic structural query domain `L.dom` to
    `dom'`. -/
abbrev Language.withDom {SemObs : Type} (L : Language SemObs)
    (dom' : L.Query → Prop) : Language SemObs :=
  { L with dom := dom' }

/-- Post-compose `f : SemObs₁ → SemObs₂` onto the observable spine of `L`. -/
abbrev Language.mapObs {SemObs₁ SemObs₂ : Type}
    (f : SemObs₁ → SemObs₂) (L : Language SemObs₁) : Language SemObs₂ where
  Prog  := L.Prog
  Query := L.Query
  Out   := L.Out
  obs   := fun o => f (L.obs o)
  sem   := L.sem
  dom   := L.dom

/-- Behavior domain of `L`. -/
abbrev Language.Behavior {SemObs : Type} (L : Language SemObs) : Type :=
  Trusted.Behavior L.Query L.Out

/-- Query-indexed specification on `L` requiring definedness on `pre q` and
    restricting outcomes at `q` to `post q`. -/
def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Spine-anchored specification on `L` whose postcondition `obsPost` inspects
    only the observable spine `L.obs o : SemObs`. -/
def Language.SpineSpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop) : L.Behavior :=
  L.SpecOn pre (fun q o => obsPost q (L.obs o))

/-- Precondition non-vacuity relative to structural domain `dom`: either `pre`
    is inhabited (`∃ q, pre q`), or the structural domain `dom` is itself
    provably uninhabited (`∀ q, ¬ dom q`). -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  (∃ q, pre q) ∨ (∀ q, ¬ dom q)

/-- Parameterless precondition non-vacuity (`dom := fun _ => True`). -/
abbrev NonVacuousPre {Query : Type} (pre : Query → Prop) : Prop :=
  NonVacuousOn (fun _ => True) pre

/-- Unconditional precondition inhabitation (`∃ q, pre q`). -/
abbrev InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

/-- Dijkstra's Law of the Excluded Miracle on `L`: at every query `q` satisfying
    `pre q`, `prog` is both defined (UB-free) and produces at least one valid
    outcome (`∃ o, (L.sem prog q).val h o`). -/
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog : L.Prog` on `pre`
    (within structural domain `dom`) against postcondition `post`. -/
def Language.VerifiedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Canonical 3-argument verification judgment fixing `dom := fun _ => True`. -/
abbrev Language.VerifiedInhabitedOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn (fun _ => True) pre post prog

/-- Canonical 3-argument domain-intrinsic verification judgment locking `dom`
    to `L.dom`. -/
abbrev Language.Verified {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn L.dom pre post prog

/-- Explicit-domain spine-anchored verification judgment inspecting only the
    observable spine `L.obs o : SemObs`. -/
abbrev Language.VerifiedSpineOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn dom pre (fun q o => obsPost q (L.obs o)) prog

/-- Canonical 3-argument spine-anchored verification judgment locking `dom` to
    `L.dom` and `post` to `L.obs`. -/
abbrev Language.VerifiedSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedSpineOn L.dom pre obsPost prog

/-- Explicit-domain negative canary (`¬ L.VerifiedOn dom pre post badProg`). -/
abbrev Language.RefutedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  ¬ L.VerifiedOn dom pre post badProg

/-- Canonical 3-argument negative canary judgment locked to `L.dom`. -/
abbrev Language.Refuted {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.RefutedOn L.dom pre post badProg

/-- Productive negative-canary judgment: `badProg` is defined and productive on
    `pre` yet fails `L.VerifiedOn dom pre post badProg` because it produces an
    outcome violating `post`. -/
def Language.RefutedProductiveOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.ProductiveOn pre badProg ∧ ¬ L.VerifiedOn dom pre post badProg

/-- Canonical 3-argument productive negative-canary judgment locked to
    `L.dom`. -/
abbrev Language.RefutedProductive {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.RefutedProductiveOn L.dom pre post badProg

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Two-sided verification judgment with explicit `dom` and non-empty negative
    canary list `badProgs`. -/
def Language.VerifiedWithCanariesOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedOn dom pre post goodProg ∧
  badProgs ≠ [] ∧
  AllHold (badProgs.map (L.RefutedOn dom pre post))

/-- Canonical 3-argument two-sided verification judgment with paired negative
    canaries `badProgs` locked to `L.dom`. -/
abbrev Language.VerifiedWithCanaries {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedWithCanariesOn L.dom pre post goodProg badProgs

/-- Two-sided spine-anchored verification judgment with explicit `dom` and
    paired negative canaries `badProgs`. -/
abbrev Language.VerifiedSpineWithCanariesOn {SemObs : Type}
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedWithCanariesOn dom pre (fun q o => obsPost q (L.obs o))
    goodProg badProgs

/-- Canonical 3-argument spine-anchored two-sided verification judgment with
    paired negative canaries `badProgs` locked to `L.dom` and `L.obs`. -/
abbrev Language.VerifiedSpineWithCanaries {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedSpineWithCanariesOn L.dom pre obsPost goodProg badProgs

/-- Constructor-gated named proof obligation with identifier `id : Id` and
    proposition `prop : Prop`. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

/-- Smart constructor for 3-argument spine-anchored `L.VerifiedSpine`. -/
abbrev Obligation.verifiedSpine {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedSpine pre obsPost prog⟩

/-- Smart constructor for 3-argument spine-anchored two-sided
    `L.VerifiedSpineWithCanaries`. -/
abbrev Obligation.verifiedSpineWithCanaries {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedSpineWithCanaries pre obsPost goodProg badProgs⟩

/-- Policy governing which obligation identifiers `Id` may be waived. -/
structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

/-- Default strict policy forbidding all waivers (`isAllowed _ := False`). -/
def TrustPolicy.strict {Id : Type} : TrustPolicy Id :=
  ⟨fun _ => False⟩

/-- Single-source `.olean`-bound external artifact binding. -/
structure EmittedArtifact where
  path     : String
  contents : String
  expected : String := contents

/-- Kernel-checked equality verifying that `a.contents` equals `a.expected`. -/
def EmittedArtifact.holds (a : EmittedArtifact) : Prop :=
  a.contents = a.expected

/-- Pairwise distinctness of obligation identifiers in `ids`. -/
def NoDupIds {Id : Type} : List Id → Prop
  | []        => True
  | id :: ids => AllHold (ids.map (fun id' => id ≠ id')) ∧ NoDupIds ids

/-- Positive per-obligation verification judgment. -/
def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

/-- Universal verification target checked by `anneal-audit`. -/
structure VerificationUnit (Id : Type) where
  policy      : TrustPolicy Id := TrustPolicy.strict
  waived      : List Id := []
  obligations : List (Obligation Id)
  artifacts   : List EmittedArtifact := []

/-- Incremental verification unit theorem allowing explicit waivers permitted by
    `u.policy`. -/
def UnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  VerificationResult u.policy u.waived u.obligations

/-- Hardened zero-debt root theorem bundling `UnitTheorem u` with kernel-checked
    `u.waived = []`, `NoDupIds`, and `EmittedArtifact.holds`. -/
def StrictUnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  UnitTheorem u ∧
  u.waived = [] ∧
  NoDupIds (u.obligations.map Obligation.id) ∧
  AllHold (u.artifacts.map EmittedArtifact.holds)

end Trusted

namespace Anneal.VacuityAndMutationAdequacy

open Trusted

/-!
## 1. Elementary Ground-Level Predicates (`SafeAt`, `Produces`) and Equivalence
to `VerifiedSpine`

A non-FV software engineer thinks about program correctness in terms of two
elementary ground-level predicates over inputs `q : L.Query` and observable
outputs `v : SemObs`:
- `SafeAt L p q`: executing program `p` on input `q` does not trigger Undefined
  Behavior.
- `Produces L p q v`: executing program `p` on input `q` is safe and can yield
  observable value `v`.

We prove that on any inhabited precondition (`∃ q₀, pre q₀`), the engineer's
ground-level universal contract is constructively equivalent (`↔`) to
`L.VerifiedSpine pre obsPost p`.
-/

/-- Program `p` is free of Undefined Behavior at query `q`. -/
def SafeAt {SemObs : Type} (L : Language SemObs)
    (p : L.Prog) (q : L.Query) : Prop :=
  (L.sem p q).defined

/-- Program `p` is safe at query `q` and can produce concrete outcome `o` whose
    observable spine projection is `L.obs o = v`. -/
def Produces {SemObs : Type} (L : Language SemObs)
    (p : L.Prog) (q : L.Query) (v : SemObs) : Prop :=
  ∃ h : (L.sem p q).defined, ∃ o : L.Out, (L.sem p q).val h o ∧ L.obs o = v

/-- Ground-level positive contract at every valid input `q` (`pre q`):
    1. `SafeAt L p q` (no Undefined Behavior),
    2. `∃ v, Produces L p q v` (produces at least one observable outcome), and
    3. `∀ v, Produces L p q v → obsPost q v` (every produced observable outcome
       satisfies `obsPost q`). -/
def GroundPositiveSpec {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (p : L.Prog) : Prop :=
  ∀ q, pre q →
    SafeAt L p q ∧
    (∃ v, Produces L p q v) ∧
    (∀ v, Produces L p q v → obsPost q v)

/-- **Theorem 1 (`ground_spec_iff_verifiedSpine`):**
    For any inhabited precondition (`∃ q₀, pre q₀`), the elementary ground-level
    specification `(∀ q, pre q → SafeAt L p q ∧ (∃ v, Produces L p q v) ∧
    (∀ v, Produces L p q v → obsPost q v))` is constructively equivalent (`↔`)
    to `L.VerifiedSpine pre obsPost p`. -/
theorem ground_spec_iff_verifiedSpine {SemObs : Type}
    (L : Language SemObs)
    (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop)
    (p : L.Prog)
    (h_inhab : ∃ q₀, pre q₀) :
    (∀ q, pre q →
      SafeAt L p q ∧
      (∃ v, Produces L p q v) ∧
      (∀ v, Produces L p q v → obsPost q v)) ↔
    L.VerifiedSpine pre obsPost p := by
  constructor
  · intro h_ground
    refine ⟨Or.inl h_inhab, ?_, ?_⟩
    · intro q hq
      cases (h_ground q hq).2.1 with
      | intro v hv =>
        cases hv with
        | intro hdef ho =>
          cases ho with
          | intro o ho_and =>
            exact ⟨hdef, o, ho_and.1⟩
    · intro q hq
      have h_q := h_ground q hq
      refine ⟨h_q.1, ?_⟩
      intro o ho
      exact h_q.2.2 (L.obs o) ⟨h_q.1, o, ho, rfl⟩
  · intro h_ver q hq
    cases h_ver.2.1 q hq with
    | intro hdef hout =>
      cases hout with
      | intro o₀ ho₀ =>
        refine ⟨hdef, ⟨L.obs o₀, hdef, o₀, ho₀, rfl⟩, ?_⟩
        intro v hv
        cases hv with
        | intro hdef' ho =>
          cases ho with
          | intro o ho_and =>
            cases h_ver.2.2 q hq with
            | intro _ hpost =>
              have h_obs_o : obsPost q (L.obs o) := hpost o ho_and.1
              rw [ho_and.2] at h_obs_o
              exact h_obs_o

/-- **Corollary 1A (`inhabited_ground_spec_iff_verifiedSpine`):**
    On any language with an inhabited structural domain (`∃ q_dom,
    L.dom q_dom`), bundling `(∃ q₀, pre q₀)` with
    `GroundPositiveSpec L pre obsPost p` is constructively equivalent (`↔`) to
    `L.VerifiedSpine pre obsPost p` without assuming `∃ q₀, pre q₀` as an
    external hypothesis. -/
theorem inhabited_ground_spec_iff_verifiedSpine {SemObs : Type}
    (L : Language SemObs)
    (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop)
    (p : L.Prog)
    (h_dom : ∃ q_dom, L.dom q_dom) :
    ((∃ q₀, pre q₀) ∧ GroundPositiveSpec L pre obsPost p) ↔
    L.VerifiedSpine pre obsPost p := by
  constructor
  · intro ⟨h_inhab, h_ground⟩
    exact (ground_spec_iff_verifiedSpine L pre obsPost p h_inhab).mp h_ground
  · intro h_ver
    have h_inhab : ∃ q₀, pre q₀ := by
      cases h_ver.1 with
      | inl hex => exact hex
      | inr h_no_dom =>
        cases h_dom with
        | intro q_dom hq_dom => exact False.elim (h_no_dom q_dom hq_dom)
    exact ⟨h_inhab,
      (ground_spec_iff_verifiedSpine L pre obsPost p h_inhab).mpr h_ver⟩

/-!
## 2. Kupferman-Vardi Polarity Vacuity Formalization

In Beer et al. (CAV 1997 / FMSD 2001) and Kupferman & Vardi (CHARME 1999 /
STTT 2003), a model $M$ satisfies a specification $\varphi$ *vacuously* with
respect to a subformula occurrence $\psi$ if $M$ still satisfies
$\varphi[\psi \leftarrow \bot(\psi)]$, where $\bot(\psi) = \text{False}$ when
$\psi$ has positive polarity in $\varphi$ and $\bot(\psi) = \text{True}$ when
$\psi$ has negative polarity in $\varphi$.

In a Hoare/refinement triple
$$\varphi(p) \equiv \forall q,\, \text{pre}(q) \to
  \bigl(\text{defined}(p, q) \wedge \forall o,\, \text{val}(p, q, o) \to
  \text{post}(q, o)\bigr),$$
`pre` occurs in negative polarity while `post` occurs in positive polarity:

1. **Antecedent / Miracle Vacuity (`KVAntecedentVacuous`):**
   Replacing the positive-polarity consequent `post` with its worst-case
   strengthening `⊥ := fun _ _ => False` yields
   `L.sem p ≤ L.SpecOn pre (fun _ _ => False)`. By Kupferman-Vardi, if this
   strengthened formula still holds, then `post` does not affect the validity of
   `L.sem p ≤ L.SpecOn pre post` (either because `pre` is empty or because `p`
   is an empty-outcome miracle `Partial.bot` on `pre`).
   We prove in `kv_non_vacuous_antecedent` that `L.ProductiveOn pre p` paired
   with `(∃ q, pre q)` strictly refutes `KVAntecedentVacuous`.
2. **Consequent Triviality (`KVConsequentVacuous`) and the Single-Model
   Blindness Theorem:**
   Conversely, suppose an author writes a trivial postcondition
   `obsPost := fun _ _ => True` (so `KVConsequentVacuous L pre obsPost` holds).
   Replacing `obsPost ← False` *does* falsify `L.sem p ≤ L.SpecOn pre False`
   on any productive program `p`, so Kupferman-Vardi single-model vacuity
   falsely declares `obsPost := True` to be "non-vacuous"
   (`kv_single_model_blind_to_trivial_consequent`)!
   We prove in `kv_non_vacuous_consequent` that two-sided verification with a
   productive mutant (`L.VerifiedSpineWithCanaries`) strictly refutes
   `KVConsequentVacuous`.
-/

/-- Kupferman-Vardi positive-subformula vacuity of the refinement triple
    `L.sem p ≤ L.SpecOn pre post`: the refinement still holds when the
    positive-polarity subformula `post` is replaced by `⊥ := fun _ _ =>
    False`. -/
def KVAntecedentVacuous {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (_post : L.Query → L.Out → Prop)
    (p : L.Prog) : Prop :=
  L.sem p ≤ L.SpecOn pre (fun _ _ => False)

/-- **Theorem 2A (`kv_non_vacuous_antecedent`):**
    Dijkstra's Law of the Excluded Miracle (`L.ProductiveOn pre p`) together
    with precondition inhabitation (`∃ q, pre q`) strictly refutes
    Kupferman-Vardi antecedent/miracle vacuity
    (`¬ KVAntecedentVacuous L pre post p`). -/
theorem kv_non_vacuous_antecedent {SemObs : Type}
    (L : Language SemObs)
    (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop)
    (p : L.Prog)
    (h_prod : L.ProductiveOn pre p)
    (h_inhab : ∃ q, pre q) :
    ¬ KVAntecedentVacuous L pre post p := by
  intro h_kv
  cases h_inhab with
  | intro q₀ hq₀ =>
    cases h_prod q₀ hq₀ with
    | intro hdef hout =>
      cases hout with
      | intro o₀ ho₀ =>
        cases h_kv q₀ hq₀ with
        | intro _ hbot =>
          exact hbot o₀ ho₀

/-- Corollary: any `L.VerifiedOn dom pre post p` on an inhabited structural
    domain (`∃ q, dom q`) strictly refutes `KVAntecedentVacuous`. -/
theorem verifiedOn_refutes_kvAntecedentVacuous {SemObs : Type}
    (L : Language SemObs)
    (dom pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop)
    (p : L.Prog)
    (h_ver : L.VerifiedOn dom pre post p)
    (h_dom : ∃ q, dom q) :
    ¬ KVAntecedentVacuous L pre post p := by
  have h_inhab : ∃ q, pre q := by
    cases h_ver.1 with
    | inl hex => exact hex
    | inr h_no_dom =>
      cases h_dom with
      | intro q hq => exact False.elim (h_no_dom q hq)
  exact kv_non_vacuous_antecedent L pre post p h_ver.2.1 h_inhab

/-- Consequent triviality (replacing `obsPost` by `⊤ := fun _ _ => True` does
    not restrict any concrete outcome on `pre`). -/
def KVConsequentVacuous {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop) : Prop :=
  ∀ q o, pre q → obsPost q (L.obs o)

/-- **Theorem 2B (`kv_single_model_blind_to_trivial_consequent`):**
    Single-model Kupferman-Vardi vacuity cannot detect `obsPost := fun _ _ =>
    True`: for any productive program `p` on an inhabited precondition `pre`,
    the trivial postcondition `fun _ _ => True` satisfies both
    `L.VerifiedSpine pre (fun _ _ => True) p` and
    `¬ KVAntecedentVacuous L pre (fun _ _ => True) p`, even though
    `KVConsequentVacuous L pre (fun _ _ => True)` holds! -/
theorem kv_single_model_blind_to_trivial_consequent {SemObs : Type}
    (L : Language SemObs)
    (pre : L.Query → Prop)
    (p : L.Prog)
    (h_prod : L.ProductiveOn pre p)
    (h_inhab : ∃ q, pre q) :
    L.VerifiedSpine pre (fun _ _ => True) p ∧
    ¬ KVAntecedentVacuous L pre (fun _ _ => True) p ∧
    KVConsequentVacuous L pre (fun _ _ => True) := by
  refine ⟨⟨Or.inl h_inhab, h_prod, ?_⟩,
    kv_non_vacuous_antecedent L pre (fun _ _ => True) p h_prod h_inhab,
    fun _ _ _ => trivial⟩
  intro q hq
  cases h_prod q hq with
  | intro hdef _ =>
    exact ⟨hdef, fun _ _ => trivial⟩

/-- **Theorem 2C (`kv_non_vacuous_consequent`):**
    Two-sided verification (`L.VerifiedSpineWithCanaries`) with any productive
    negative canary `badProg` (`L.ProductiveOn pre badProg`) strictly refutes
    `KVConsequentVacuous L pre obsPost`. -/
theorem kv_non_vacuous_consequent {SemObs : Type}
    (L : Language SemObs)
    (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop)
    (goodProg badProg : L.Prog)
    (rest : List L.Prog)
    (h_can : L.VerifiedSpineWithCanaries pre obsPost goodProg (badProg :: rest))
    (h_bad_prod : L.ProductiveOn pre badProg) :
    ¬ KVConsequentVacuous L pre obsPost := by
  intro h_triv
  have h_bad_spec :
      L.sem badProg ≤ L.SpecOn pre (fun q o => obsPost q (L.obs o)) := by
    intro q hq
    cases h_bad_prod q hq with
    | intro hdef _ =>
      exact ⟨hdef, fun o _ => h_triv q o hq⟩
  have h_bad_ver :
      L.VerifiedOn L.dom pre (fun q o => obsPost q (L.obs o)) badProg :=
    ⟨h_can.1.1, h_bad_prod, h_bad_spec⟩
  exact h_can.2.2.1 h_bad_ver

/-!
## 3. Budd-Angluin Mutation Adequacy & The Two-Sided Ground Equivalence Theorem

Budd and Angluin (*Acta Informatica* 18(1):31–45, 1982) formalized program
correctness via two dual obligations:
1. Universal correctness of $P_{\text{good}}$ against specification $S$ across
   the input domain, and
2. Distinguishing $P_{\text{good}}$ from every non-equivalent mutant
   $P_{\text{bad}} \in \Phi(P_{\text{good}})$ at a concrete test point $q_0$.

We formalize `GroundTwoSidedWitness` using **only** `pre`, `SafeAt`, `Produces`,
and `obsPost`, and prove that it both implies `VerifiedSpineWithCanaries` and
simultaneously blocks all five lattice-collapse and spine-erasure pathologies.
-/

/-- Two-sided ground-level correctness and mutation-distinguishing witness
    stated exclusively in terms of `pre`, `SafeAt`, `Produces`, and `obsPost`:
    - `positive`: at every query `q` satisfying `pre q`, `p_good` is safe,
      produces at least one observable value, and every observable value it
      produces satisfies `obsPost q`.
    - `hq₀`: `q₀` is a concrete valid input (`pre q₀`).
    - `prod_good`: `p_good` produces observable value `v_good` at `q₀`.
    - `prod_bad`: the mutant `p_bad` produces observable value `v_bad` at `q₀`.
    - `post_good`: `v_good` satisfies `obsPost q₀`.
    - `not_post_bad`: `v_bad` violates `obsPost q₀` (`¬ obsPost q₀ v_bad`). -/
structure GroundTwoSidedWitness {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (p_good p_bad : L.Prog) (q₀ : L.Query) (v_good v_bad : SemObs) : Prop where
  positive :
    ∀ q, pre q →
      SafeAt L p_good q ∧
      (∃ v, Produces L p_good q v) ∧
      (∀ v, Produces L p_good q v → obsPost q v)
  hq₀          : pre q₀
  prod_good    : Produces L p_good q₀ v_good
  prod_bad     : Produces L p_bad q₀ v_bad
  post_good    : obsPost q₀ v_good
  not_post_bad : ¬ obsPost q₀ v_bad

/-- **Theorem 3A (`groundTwoSidedWitness_implies_verifiedSpineWithCanaries`):**
    Any `GroundTwoSidedWitness L pre obsPost p_good p_bad q₀ v_good v_bad`
    constructively proves
    `L.VerifiedSpineWithCanaries pre obsPost p_good [p_bad]`. -/
theorem groundTwoSidedWitness_implies_verifiedSpineWithCanaries {SemObs : Type}
    {L : Language SemObs}
    {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {p_good p_bad : L.Prog}
    {q₀ : L.Query}
    {v_good v_bad : SemObs}
    (w : GroundTwoSidedWitness L pre obsPost p_good p_bad q₀ v_good v_bad) :
    L.VerifiedSpineWithCanaries pre obsPost p_good [p_bad] := by
  have h_good_ver : L.VerifiedSpine pre obsPost p_good :=
    (ground_spec_iff_verifiedSpine L pre obsPost p_good ⟨q₀, w.hq₀⟩).mp
      w.positive
  refine ⟨h_good_ver, (by intro h; cases h), ⟨?_, trivial⟩⟩
  intro h_bad_ver
  cases w.prod_bad with
  | intro hdef_bad ho_bad =>
    cases ho_bad with
    | intro o_bad ho_bad_and =>
      cases h_bad_ver.2.2 q₀ w.hq₀ with
      | intro _ hpost_bad =>
        have h_obs_bad : obsPost q₀ (L.obs o_bad) :=
          hpost_bad o_bad ho_bad_and.1
        rw [ho_bad_and.2] at h_obs_bad
        exact w.not_post_bad h_obs_bad

/-- **Theorem 3B (`verifiedSpineWithCanaries_at_witness_implies_ground`):**
    Conversely, if `L.VerifiedSpine pre obsPost p_good` holds and at a valid
    input `q₀` (`pre q₀`) the mutant `p_bad` produces an observable value
    `v_bad` (`Produces L p_bad q₀ v_bad`) that violates `obsPost q₀`
    (`¬ obsPost q₀ v_bad`), then there constructively exists `v_good : SemObs`
    forming a
    `GroundTwoSidedWitness L pre obsPost p_good p_bad q₀ v_good v_bad`. -/
theorem verifiedSpineWithCanaries_at_witness_implies_groundTwoSidedWitness
    {SemObs : Type}
    {L : Language SemObs}
    {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {p_good p_bad : L.Prog}
    {q₀ : L.Query}
    {v_bad : SemObs}
    (h_good : L.VerifiedSpine pre obsPost p_good)
    (hq₀ : pre q₀)
    (h_prod_bad : Produces L p_bad q₀ v_bad)
    (h_not_post_bad : ¬ obsPost q₀ v_bad) :
    ∃ v_good : SemObs,
      GroundTwoSidedWitness L pre obsPost p_good p_bad q₀ v_good v_bad := by
  have h_pos :=
    (ground_spec_iff_verifiedSpine L pre obsPost p_good ⟨q₀, hq₀⟩).mpr h_good
  cases (h_pos q₀ hq₀).2.1 with
  | intro v_good hv_good =>
    have h_post_good : obsPost q₀ v_good :=
      (h_pos q₀ hq₀).2.2 v_good hv_good
    exact ⟨v_good,
      ⟨h_pos, hq₀, hv_good, h_prod_bad, h_post_good, h_not_post_bad⟩⟩

/-- **Theorem 3C (`groundTwoSidedWitness_five_way_anti_pathology`):**
    A `GroundTwoSidedWitness` simultaneously and constructively proves all five
    anti-pathology properties:
    1. `(a)` `v_good ≠ v_bad` (distinct ground observable values),
    2. `(b)` `∃ q, pre q` (inhabited precondition, refuting `pre = False`),
    3. `(c)` `¬ (∀ q v, pre q → obsPost q v)` (non-trivial postcondition,
       refuting `obsPost = True`),
    4. `(d)` `¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂) ∧ (Subsingleton SemObs →
       False)` (non-constant observable spine / non-unit `SemObs`), and
    5. `(e)` `L.sem p_good ≠ L.sem p_bad` (AST-sensitive semantics, refuting
       program-ignoring semantics). -/
theorem groundTwoSidedWitness_five_way_anti_pathology {SemObs : Type}
    {L : Language SemObs}
    {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {p_good p_bad : L.Prog}
    {q₀ : L.Query}
    {v_good v_bad : SemObs}
    (w : GroundTwoSidedWitness L pre obsPost p_good p_bad q₀ v_good v_bad) :
    v_good ≠ v_bad ∧
    (∃ q, pre q) ∧
    ¬ (∀ q v, pre q → obsPost q v) ∧
    (¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂) ∧ (Subsingleton SemObs → False)) ∧
    L.sem p_good ≠ L.sem p_bad := by
  have h_neq_val : v_good ≠ v_bad := by
    intro h_eq
    have h_bad_holds : obsPost q₀ v_bad := h_eq ▸ w.post_good
    exact w.not_post_bad h_bad_holds
  have h_inhab : ∃ q, pre q := ⟨q₀, w.hq₀⟩
  have h_nontriv_post : ¬ (∀ q v, pre q → obsPost q v) := by
    intro h_all
    exact w.not_post_bad (h_all q₀ v_bad w.hq₀)
  have h_nonconst_obs : ¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂) := by
    intro h_const
    cases w.prod_good with
    | intro _ ho_good =>
      cases ho_good with
      | intro o_good ho_good_and =>
        cases w.prod_bad with
        | intro _ ho_bad =>
          cases ho_bad with
          | intro o_bad ho_bad_and =>
            have h_eq : v_good = v_bad := by
              rw [← ho_good_and.2, ← ho_bad_and.2]
              exact h_const o_good o_bad
            exact h_neq_val h_eq
  have h_not_subsingleton : Subsingleton SemObs → False := by
    intro h_sub
    exact h_neq_val (@Subsingleton.elim SemObs h_sub v_good v_bad)
  have h_sem_neq : L.sem p_good ≠ L.sem p_bad := by
    intro h_sem_eq
    have h_prod_bad_as_good : Produces L p_good q₀ v_bad := by
      unfold Produces
      rw [h_sem_eq]
      exact w.prod_bad
    have h_bad_obs_holds : obsPost q₀ v_bad :=
      (w.positive q₀ w.hq₀).2.2 v_bad h_prod_bad_as_good
    exact w.not_post_bad h_bad_obs_holds
  exact ⟨h_neq_val, h_inhab, h_nontriv_post,
    ⟨h_nonconst_obs, h_not_subsingleton⟩, h_sem_neq⟩

/-!
## 4. Verifier / Judge Tool Bi-Discrimination (`check : L.Prog → Bool`)

When an AI agent vibe-codes a formal verification tool, static analyzer, or
proof checker `check : L.Prog → Bool`, one-sided soundness
(`∀ p, check p = true → L.VerifiedSpine pre obsPost p`) is trivially satisfied
by the dead verifier `check := fun _ => false`. Conversely, requiring only
`check p_good = true` without soundness or with a vacuous specification is
satisfied by the rubber-stamp verifier `check := fun _ => true`.

We formalize `SoundAndNonTrivialVerifier` and prove that pairing verifier
soundness with positive acceptance `check p_good = true` and negative canary
refutation `L.Refuted pre (fun q o => obsPost q (L.obs o)) p_bad` forces
`check p_bad = false` and strictly refutes both dead and rubber-stamp verifiers.
-/

/-- A boolean verification tool `check : L.Prog → Bool` that is:
    1. `sound`: every program accepted by `check` satisfies `VerifiedSpine`,
    2. `accepts_good`: accepts the intended implementation `p_good`, and
    3. `refutes_bad`: paired with a mutant `p_bad` that violates the
       specification. -/
structure SoundAndNonTrivialVerifier {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (check : L.Prog → Bool) (p_good p_bad : L.Prog) : Prop where
  sound        : ∀ p, check p = true → L.VerifiedSpine pre obsPost p
  accepts_good : check p_good = true
  refutes_bad  : L.Refuted pre (fun q o => obsPost q (L.obs o)) p_bad

/-- **Theorem 4A (`verifier_rejects_mutant`):**
    Any `SoundAndNonTrivialVerifier` must evaluate `check p_bad = false` on the
    refuted mutant `p_bad`. -/
theorem verifier_rejects_mutant {SemObs : Type}
    {L : Language SemObs}
    {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {check : L.Prog → Bool}
    {p_good p_bad : L.Prog}
    (v : SoundAndNonTrivialVerifier L pre obsPost check p_good p_bad) :
    check p_bad = false := by
  cases h_eval : check p_bad with
  | false => rfl
  | true =>
    exact False.elim (v.refutes_bad (v.sound p_bad h_eval))

/-- **Theorem 4B (`verifier_bi_discrimination`):**
    Any `SoundAndNonTrivialVerifier` simultaneously proves:
    1. `check p_bad = false` (rejects the mutant),
    2. `check ≠ (fun _ => false)` (refutes the dead verifier),
    3. `check ≠ (fun _ => true)` (refutes the rubber-stamp verifier), and
    4. `p_good ≠ p_bad` (distinguishes the programs). -/
theorem verifier_bi_discrimination {SemObs : Type}
    {L : Language SemObs}
    {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {check : L.Prog → Bool}
    {p_good p_bad : L.Prog}
    (v : SoundAndNonTrivialVerifier L pre obsPost check p_good p_bad) :
    check p_bad = false ∧
    check ≠ (fun _ => false) ∧
    check ≠ (fun _ => true) ∧
    p_good ≠ p_bad := by
  have h_rej : check p_bad = false := verifier_rejects_mutant v
  refine ⟨h_rej, ?_, ?_, ?_⟩
  · intro h_dead
    have h_false : check p_good = false := congrFun h_dead p_good
    rw [v.accepts_good] at h_false
    cases h_false
  · intro h_rubber
    have h_true : check p_bad = true := congrFun h_rubber p_bad
    rw [h_rej] at h_true
    cases h_true
  · intro h_eq
    have h_same : check p_good = check p_bad := congrArg check h_eq
    rw [v.accepts_good, h_rej] at h_same
    cases h_same

/-!
## 5. Mechanized Replay of the Anneal V1 `abs` Mutation Adequacy Matrix

In the empirical study `anneal-v1-contract-mutation-adequacy-2026-09-28`, six
contract/implementation variants of `abs(x: Int) -> Int` were tested against
Anneal V1:
1. `correctAbs`: returns `-x` if `x < 0` else `x`.
2. `zeroBody`: mutant `fn abs(_x: i32) -> i32 { 0 }` that always returns `0`.
3. `identityBody`: mutant `fn identity(x: i32) -> i32 { x }`.

Under unhardened V1:
- **Pathology A (`false_precondition.rs`):** `requires: False`,
  `ensures: ret < 0` passed verification (`Exit 0`) by eliminating `False`.
- **Pathology B (`weak_relation_zero_body.rs`):** Weakening the postcondition to
  `ret >= 0` allowed `zeroBody` to pass verification (`Exit 0`).

We replay this exact matrix in `AbsLang` and prove:
1. `v1_false_precondition_rejected_by_verifiedSpine`: `L.VerifiedSpine`
   unconditionally rejects the `requires: False` contract on `AbsLang`.
2. `v1_weak_nonneg_post_rejected_by_canary`: `L.VerifiedSpineWithCanaries` with
   `[zeroBody]` unconditionally rejects the weakened `ret >= 0` contract.
3. `abs_full_contract_ground_witness_and_strict_unit`: the complete `abs`
   contract (`ret ≥ 0 ∧ (x ≥ 0 → ret = x) ∧ (x < 0 → ret = -x)`) constructs a
   `GroundTwoSidedWitness` against both `zeroBody` (at `x = 1`) and
   `identityBody` (at `x = -1`) and satisfies `StrictUnitTheorem`.
-/

/-- Sign-magnitude integer representation in pure `Init.Core` (`prelude`) for
    the Anneal V1 `abs` mutation adequacy probe:
    - `⟨false, n⟩` represents `+n`,
    - `⟨true, n⟩` represents `-n`. -/
structure SignedInt where
  isNeg : Bool
  mag   : Nat
  deriving DecidableEq

/-- Canonical `+0` value. -/
def SignedInt.zero : SignedInt := ⟨false, 0⟩

/-- Canonical `+1` value. -/
def SignedInt.one : SignedInt := ⟨false, 1⟩

/-- Canonical `-1` value. -/
def SignedInt.negOne : SignedInt := ⟨true, 1⟩

/-- A `SignedInt` is nonnegative (`x ≥ 0`) iff its sign bit is `false` or its
    magnitude is `0`. -/
def SignedInt.isNonneg (x : SignedInt) : Prop :=
  x.isNeg = false

/-- A `SignedInt` is strictly negative (`x < 0`) iff its sign bit is `true` and
    its magnitude is positive (`mag > 0`). -/
def SignedInt.isNegVal (x : SignedInt) : Prop :=
  x.isNeg = true

/-- Arithmetic negation on `SignedInt` normalizing magnitude onto the
    nonnegative axis when negating a negative input. -/
def SignedInt.negate (x : SignedInt) : SignedInt :=
  ⟨!x.isNeg, x.mag⟩

/-- The three candidate programs from
    `anneal-v1-contract-mutation-adequacy-2026-09-28`. -/
inductive AbsProg where
  | correctAbs
  | zeroBody
  | identityBody
  deriving DecidableEq

/-- Operational evaluation of the three `abs` candidate bodies. -/
def evalAbsProg (p : AbsProg) (x : SignedInt) : SignedInt :=
  match p with
  | .correctAbs   => ⟨false, x.mag⟩
  | .zeroBody     => SignedInt.zero
  | .identityBody => x

/-- Semantic language for the `abs` mutation adequacy probe. -/
abbrev AbsLang : Language SignedInt :=
  Language.mkSimple AbsProg SignedInt SignedInt (fun p x =>
    Partial.pure (fun ret => ret = evalAbsProg p x))

/-- Admissible signed input domain (`x.mag < 2147483648`, excluding
    `i32::MIN`). -/
abbrev absPre (x : SignedInt) : Prop :=
  x.mag < 2147483648

/-- Falsity postcondition from `satisfiable_pre_false_post.rs` /
    `false_precondition.rs` (`ret < 0`). -/
abbrev absNegPost (_x ret : SignedInt) : Prop :=
  ret.isNegVal

/-- Weakened postcondition from `weak_relation_zero_body.rs` (`ret ≥ 0`
    only). -/
abbrev absWeakNonnegPost (_x ret : SignedInt) : Prop :=
  ret.isNonneg

/-- Complete specification from `baseline.rs`: nonnegativity plus both
    nonnegative (`x.isNeg = false → ret = x`) and negative (`x.isNeg = true →
    ret = SignedInt.negate x`) input-output equations. -/
def absFullPost (x ret : SignedInt) : Prop :=
  ret.isNonneg ∧
  (x.isNeg = false → ret = x) ∧
  (x.isNeg = true → ret = SignedInt.negate x)

/-- **Replay 5A (`v1_false_precondition_rejected_by_verifiedSpine`):**
    The `false_precondition.rs` pathology (`requires: False`,
    `ensures: ret < 0`) that exited `0` in Anneal V1 is unconditionally
    rejected by `AbsLang.VerifiedSpine`. -/
theorem v1_false_precondition_rejected_by_verifiedSpine (p : AbsProg) :
    ¬ AbsLang.VerifiedSpine (fun _ => False) absNegPost p := by
  intro ⟨h_nonvac, _, _⟩
  cases h_nonvac with
  | inl hex =>
    cases hex with
    | intro _ hfalse => exact hfalse
  | inr h_no_dom =>
    exact h_no_dom SignedInt.zero trivial

/-- **Replay 5B (`v1_weak_nonneg_post_rejected_by_canary`):**
    The `weak_relation_zero_body.rs` pathology (`ensures: ret ≥ 0`) passes
    single-program `AbsLang.VerifiedSpine` for both `correctAbs` and `zeroBody`,
    but is unconditionally rejected by `AbsLang.VerifiedSpineWithCanaries` when
    paired with the `zeroBody` mutant! -/
theorem v1_weak_nonneg_post_rejected_by_canary :
    AbsLang.VerifiedSpine absPre absWeakNonnegPost .correctAbs ∧
    AbsLang.VerifiedSpine absPre absWeakNonnegPost .zeroBody ∧
    ¬ AbsLang.VerifiedSpineWithCanaries absPre absWeakNonnegPost
        .correctAbs [.zeroBody] := by
  have h0_pre : absPre SignedInt.zero := by decide
  have h_zero_ver :
      AbsLang.VerifiedSpine absPre absWeakNonnegPost .zeroBody := by
    refine ⟨Or.inl ⟨SignedInt.zero, h0_pre⟩, ?_, ?_⟩
    · intro x _
      exact ⟨trivial, SignedInt.zero, rfl⟩
    · intro x _
      refine ⟨trivial, ?_⟩
      intro ret hret
      rw [hret]
      rfl
  refine ⟨?_, h_zero_ver, ?_⟩
  · refine ⟨Or.inl ⟨SignedInt.zero, h0_pre⟩, ?_, ?_⟩
    · intro x _
      exact ⟨trivial, evalAbsProg .correctAbs x, rfl⟩
    · intro x _
      refine ⟨trivial, ?_⟩
      intro ret hret
      rw [hret]
      rfl
  · intro h_can
    exact h_can.2.2.1 h_zero_ver

/-- Helper: `correctAbs` satisfies `GroundPositiveSpec` for `absFullPost`. -/
theorem correctAbs_groundPositiveSpec :
    GroundPositiveSpec AbsLang absPre absFullPost .correctAbs := by
  intro x _
  refine ⟨trivial,
    ⟨evalAbsProg .correctAbs x, trivial, evalAbsProg .correctAbs x, rfl, rfl⟩,
    ?_⟩
  intro v ⟨_, o, ho_val, ho_obs⟩
  rw [← ho_obs, ho_val]
  cases x with
  | mk isNeg mag =>
    cases isNeg with
    | false =>
      exact ⟨rfl, fun _ => rfl, fun h => Bool.noConfusion h⟩
    | true =>
      exact ⟨rfl, fun h => Bool.noConfusion h, fun _ => rfl⟩

/-- **Replay 5C (`abs_ground_witness_against_zeroBody`):**
    At `q₀ = +1` (`SignedInt.one`), `correctAbs` produces `v_good = +1` while
    `zeroBody` produces `v_bad = +0`, forming a constructive
    `GroundTwoSidedWitness` for `absFullPost`. -/
theorem abs_ground_witness_against_zeroBody :
    GroundTwoSidedWitness AbsLang absPre absFullPost
      .correctAbs .zeroBody SignedInt.one SignedInt.one SignedInt.zero := by
  refine {
    positive     := correctAbs_groundPositiveSpec
    hq₀          := by decide
    prod_good    := ⟨trivial, SignedInt.one, rfl, rfl⟩
    prod_bad     := ⟨trivial, SignedInt.zero, rfl, rfl⟩
    post_good    := ⟨rfl, fun _ => rfl, fun h => Bool.noConfusion h⟩
    not_post_bad := by
      intro ⟨_, hpos, _⟩
      have h01 : SignedInt.zero = SignedInt.one := hpos rfl
      cases h01
  }

/-- **Replay 5D (`abs_ground_witness_against_identityBody`):**
    At `q₀ = -1` (`SignedInt.negOne`), `correctAbs` produces `v_good = +1`
    while `identityBody` produces `v_bad = -1`, forming a constructive
    `GroundTwoSidedWitness` for `absFullPost`. -/
theorem abs_ground_witness_against_identityBody :
    GroundTwoSidedWitness AbsLang absPre absFullPost
      .correctAbs .identityBody
      SignedInt.negOne SignedInt.one SignedInt.negOne := by
  refine {
    positive     := correctAbs_groundPositiveSpec
    hq₀          := by decide
    prod_good    := ⟨trivial, SignedInt.one, rfl, rfl⟩
    prod_bad     := ⟨trivial, SignedInt.negOne, rfl, rfl⟩
    post_good    := ⟨rfl, fun h => Bool.noConfusion h, fun _ => rfl⟩
    not_post_bad := by
      intro ⟨h_nonneg, _, _⟩
      cases h_nonneg
  }

/-- Complete `VerificationUnit` for `abs` bundling both negative canaries
    (`.zeroBody` and `.identityBody`) inside
    `Obligation.verifiedSpineWithCanaries`. -/
def absVerificationUnit : VerificationUnit String where
  policy      := TrustPolicy.strict
  waived      := []
  obligations := [
    Obligation.verifiedSpineWithCanaries
      "abs_full_spec_with_canaries"
      AbsLang
      absPre
      absFullPost
      .correctAbs
      [.zeroBody, .identityBody]
  ]
  artifacts   := []

/-- **Replay 5E (`absVerificationUnit_strict`):**
    The complete `abs` contract with paired negative canaries
    `[.zeroBody, .identityBody]` satisfies `StrictUnitTheorem`. -/
theorem absVerificationUnit_strict : StrictUnitTheorem absVerificationUnit := by
  have h_can_zero :=
    groundTwoSidedWitness_implies_verifiedSpineWithCanaries
      abs_ground_witness_against_zeroBody
  have h_can_id :=
    groundTwoSidedWitness_implies_verifiedSpineWithCanaries
      abs_ground_witness_against_identityBody
  refine ⟨⟨(by intro h; cases h), trivial, ⟨Or.inr ?_, trivial⟩⟩,
    rfl, ⟨trivial, trivial⟩, trivial⟩
  exact ⟨h_can_zero.1, (by intro h; cases h),
    ⟨h_can_zero.2.2.1, h_can_id.2.2.1, trivial⟩⟩

/-!
## 6. Kernel Axiom Verification (`#print axioms`)
-/

#print axioms ground_spec_iff_verifiedSpine
#print axioms inhabited_ground_spec_iff_verifiedSpine
#print axioms kv_non_vacuous_antecedent
#print axioms verifiedOn_refutes_kvAntecedentVacuous
#print axioms kv_single_model_blind_to_trivial_consequent
#print axioms kv_non_vacuous_consequent
#print axioms groundTwoSidedWitness_implies_verifiedSpineWithCanaries
#print axioms verifiedSpineWithCanaries_at_witness_implies_groundTwoSidedWitness
#print axioms groundTwoSidedWitness_five_way_anti_pathology
#print axioms verifier_rejects_mutant
#print axioms verifier_bi_discrimination
#print axioms v1_false_precondition_rejected_by_verifiedSpine
#print axioms v1_weak_nonneg_post_rejected_by_canary
#print axioms correctAbs_groundPositiveSpec
#print axioms abs_ground_witness_against_zeroBody
#print axioms abs_ground_witness_against_identityBody
#print axioms absVerificationUnit_strict

end Anneal.VacuityAndMutationAdequacy
