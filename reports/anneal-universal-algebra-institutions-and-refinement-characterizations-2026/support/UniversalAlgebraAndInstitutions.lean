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
# Universal Algebra and Institutions: Universal Characterizations from Model Theory, Universal Algebra,
# Category Theory, and Programming Language Theory

This standalone, zero-axiom Lean `v4.34.1` module (`prelude` + `Init.Core`)
mechanizes the universal mathematical characterizations underlying Anneal's
`Trusted/Refinement.lean` kernel:

1. **Universal Two-Point Separation Factorization (`TwoPointFactorization`):**
   Formalizes the Stone-Birkhoff-Lawvere two-point separation principle (`0 ≠ 1`
   in the two-element algebra `Bool`). When a pair of programs (`goodProg` and
   `badProg`) evaluated at a query `q₀`, projected onto the observable spine
   `SemObs`, and tested against `obsPost q₀` separates `true ↦ True` from
   `false ↦ False`:
   `Bool →[pick] P →[eval] O →[obs] S →[pred] Prop`,
   categorical functoriality implies in a single theorem
   (`twoPointFactorization_nondegeneracy`) that:
   - `pick true ≠ pick false`, `eval (pick true) ≠ eval (pick false)`, and
     `obs (eval (pick true)) ≠ obs (eval (pick false))`,
   - none of `P`, `O`, or `S` is a `Subsingleton`,
   - none of `eval`, `obs`, or `pred` is a constant function, and
   - `pred` is neither universally `True` (`⊤`) nor universally `False` (`⊥`).
   Instantiating this factorization on `Language.VerifiedSpineWithCanariesOn`
   recovers all four Anneal canary squeeze theorems as corollaries of a single
   universal-algebraic factorization lemma.

2. **The Bounded Refinement Sandwich (`BoundedRefinementSandwich`):**
   Formalizes Dijkstra's Law of the Excluded Miracle (1976), Nelson's partial
   guarded commands (1989), and Back-von Wright's predicate transformer duality
   (1998) inside the pointed demonic refinement lattice `Partial (Out → Prop)`:
   - `Partial.bot` (`defined := True, val := ∅`) is the miraculous bottom (`⊥`),
   - `Partial.chaosDef` (`defined := True, val := Univ`) is the chaotic defined
     top (`⊤_def`), and
   - `Partial.ub` (`defined := False`) is the undefined top (`⊤_ub`).
   Proves that two-sided verification with a productive negative canary at `q₀`
   is equivalent to the strict two-sided refinement sandwich:
   `⊥ <_{q₀} L.sem goodProg ≤ L.SpineSpecOn pre obsPost <_{q₀} ⊤_def < ⊤_ub`.

3. **Plotkin Ground Adequacy & Final Observable Quotient (`ObsEquiv`):**
   Formalizes Plotkin's (1977) ground-type computational adequacy and Milner's
   (1977) ground observable equivalence via the kernel equivalence relation
   `ObsEquiv L o₁ o₂ := (L.obs o₁ = L.obs o₂)`. Proves that `ObsEquiv L` is an
   equivalence relation, that `L.SpineSpecOn pre obsPost` is invariant under
   `ObsEquiv L` (factoring uniquely through the final observable quotient
   `SemObs`), and that any specification distinguishing `goodProg` from a
   productive `badProg` forces `L.obs` to separate their concrete outcomes at
   ground sort `SemObs`.

4. **Goguen-Burstall Institution Satisfaction & Two-Point Separation Transfer
   (`BehaviorCodec`):**
   Formalizes `BehaviorCodec L₁ L₂` as a spine-preserving institution morphism
   (Goguen & Burstall 1984/1992) and Galois retraction pair (Cousot & Cousot
   1977/1979) over the shared observable coalgebra `SemObs` (Rutten 2000).
   Proves the **Institution Satisfaction Condition**
   (`institution_satisfaction_iff`) and the **Two-Point Separation Transfer
   Theorem** (`codec_transfers_two_point_separation` and
   `codec_transfers_verifiedSpineWithCanaries`), showing that
   `ProductiveCompiles` transfers both universal positive specification
   satisfaction and existential two-point Stone separation (`v_good ≠ v_bad` in
   `SemObs`) from source language `L₁` to target language `L₂`.
-/

namespace Anneal.UniversalAlgebraAndInstitutions

/-!
## 0. Core Definitions from `Trusted/Refinement.lean`
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

/-- Order-preserving mapping between preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Constructive partiality carrier representing `B ∪ {UB}` without
    `Classical.choice`. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

/-- The Undefined Behavior top element (`⊤_ub`, `defined := False`) of
    `Partial B`. -/
def Partial.ub {B : Type u} : Partial B :=
  ⟨False, False.elim⟩

/-- The bottom predicate element (`⊥`, `defined := True`,
    `val := fun _ _ => False`) of `Partial (Out → Prop)`, representing an empty
    outcome set (Dijkstra's miracle). -/
def Partial.bot {Out : Type u} : Partial (Out → Prop) :=
  ⟨True, fun _ _ => False⟩

/-- The chaotic defined predicate element (`⊤_def`, `defined := True`,
    `val := fun _ _ => True`) of `Partial (Out → Prop)`, representing an
    unconstrained defined outcome set. -/
def Partial.chaosDef {Out : Type u} : Partial (Out → Prop) :=
  ⟨True, fun _ _ => True⟩

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

/-- Precondition non-vacuity relative to structural domain `dom`. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  (∃ q, pre q) ∨ (∀ q, ¬ dom q)

/-- Dijkstra's Law of the Excluded Miracle on `L`: at every query `q` satisfying
    `pre q`, `prog` is both defined (UB-free) and produces at least one valid
    outcome. -/
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

/-- Productive negative-canary judgment: `badProg` is defined and productive on
    `pre` yet fails `L.VerifiedOn dom pre post badProg`. -/
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
abbrev Language.VerifiedSpineWithCanariesOn {SemObs : Type} (L : Language SemObs)
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

/-- Representation codec between two languages `L₁` and `L₂` sharing observable
    spine `SemObs`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Canonical monotone behavior morphism induced by
    `c : BehaviorCodec L₁ L₂`. -/
def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
  fun q₂ => {
    defined := (b (c.decodeQuery q₂)).defined
    val     := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b (c.decodeQuery q₂)).val h o₁
  }

/-- Downward/horizontal compilation
    (`L_tgt.sem t ≤ c.toMorphism (L_src.sem s)`). -/
abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Miracle-free downward/horizontal compilation: pairs `Compiles` with forward
    productivity preservation from `s` to `t`. -/
def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₁,
    (∃ h₁ : (L_src.sem s q₁).defined, ∃ o₁, (L_src.sem s q₁).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t (c.encodeQuery q₁)).defined,
      ∃ o₂, (L_tgt.sem t (c.encodeQuery q₁)).val h₂ o₂)

/-- Upward abstraction (`L_src.sem s ≤ c.toMorphism (L_v.sem v)`). -/
abbrev Abstracts {SemObs : Type} (L_v L_src : Language SemObs)
    (c : BehaviorCodec L_v L_src) (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ c.toMorphism (L_v.sem v)

end Trusted

open Trusted

/-!
## 1. Universal Two-Point Separation Factorization (`TwoPointFactorization`)

In universal algebra (Birkhoff 1935, 1944; Stone 1936, 1937) and category
theory (Lawvere 1964), a bounded lattice or algebraic structure is
non-degenerate (`0 ≠ 1`) if and only if it admits a separating morphism from the
two-element object `2 = Bool` to `Prop` that factors through the carriers of
interest:

`Bool →[pick] P →[eval] O →[obs] S →[pred] Prop`

such that `true` maps to a true proposition (`pred (obs (eval (pick true)))`)
and `false` maps to a false proposition (`¬ pred (obs (eval (pick false)))`).
Because any factorization of a separating map is separating on every prefix and
non-constant on every suffix, a single structure `TwoPointFactorization P O S`
witnesses non-degeneracy of all three carriers `P`, `O`, `S` and all four
morphisms `pick`, `eval`, `obs`, `pred` simultaneously.
-/

/-- A factorized two-point separation chain across program carrier `P`, concrete
    outcome carrier `O`, observable spine carrier `S`, and specification
    predicate `pred : S → Prop`:
    `Bool →[pick] P →[eval] O →[obs] S →[pred] Prop`
    sending `true ↦ True` and `false ↦ False`. -/
structure TwoPointFactorization (P O S : Type) where
  pick       : Bool → P
  eval       : P → O
  obs        : O → S
  pred       : S → Prop
  true_holds : pred (obs (eval (pick true)))
  false_ref  : ¬ pred (obs (eval (pick false)))

/-- Convenience projection for the positive program (`pick true`). -/
abbrev TwoPointFactorization.goodProg {P O S : Type}
    (F : TwoPointFactorization P O S) : P :=
  F.pick true

/-- Convenience projection for the negative canary program (`pick false`). -/
abbrev TwoPointFactorization.badProg {P O S : Type}
    (F : TwoPointFactorization P O S) : P :=
  F.pick false

/-- Convenience projection for the positive concrete outcome
    (`eval (pick true)`). -/
abbrev TwoPointFactorization.goodOut {P O S : Type}
    (F : TwoPointFactorization P O S) : O :=
  F.eval (F.pick true)

/-- Convenience projection for the negative concrete outcome
    (`eval (pick false)`). -/
abbrev TwoPointFactorization.badOut {P O S : Type}
    (F : TwoPointFactorization P O S) : O :=
  F.eval (F.pick false)

/-- Convenience projection for the positive observable spine value
    (`obs (eval (pick true))`). -/
abbrev TwoPointFactorization.goodObs {P O S : Type}
    (F : TwoPointFactorization P O S) : S :=
  F.obs (F.eval (F.pick true))

/-- Convenience projection for the negative observable spine value
    (`obs (eval (pick false))`). -/
abbrev TwoPointFactorization.badObs {P O S : Type}
    (F : TwoPointFactorization P O S) : S :=
  F.obs (F.eval (F.pick false))

/-- **Universal Two-Point Separation Non-Degeneracy Theorem
    (`twoPointFactorization_nondegeneracy`):**
    Every `F : TwoPointFactorization P O S` constructively establishes:
    1. **Pointwise separation at every stage:**
       `F.pick true ≠ F.pick false`,
       `F.eval (F.pick true) ≠ F.eval (F.pick false)`, and
       `F.obs (F.eval (F.pick true)) ≠ F.obs (F.eval (F.pick false))`.
    2. **Carrier non-triviality (anti-`Subsingleton`):**
       None of `P`, `O`, or `S` is a `Subsingleton`.
    3. **Morphism non-constancy:**
       None of `F.eval`, `F.obs`, or `F.pred` is constant.
    4. **Predicate two-sided non-triviality (`⊥ < pred < ⊤`):**
       `F.pred` is neither universally `True` (`¬ ∀ s, F.pred s`) nor
       universally `False` (`¬ ∀ s, ¬ F.pred s`). -/
theorem twoPointFactorization_nondegeneracy {P O S : Type}
    (F : TwoPointFactorization P O S) :
    -- (a) Stage-wise distinctness
    (F.pick true ≠ F.pick false ∧
     F.eval (F.pick true) ≠ F.eval (F.pick false) ∧
     F.obs (F.eval (F.pick true)) ≠ F.obs (F.eval (F.pick false))) ∧
    -- (b) Carrier non-subsingleton guarantees
    (¬ Subsingleton P ∧ ¬ Subsingleton O ∧ ¬ Subsingleton S) ∧
    -- (c) Non-constancy of every intermediate morphism
    (¬ (∀ p₁ p₂ : P, F.eval p₁ = F.eval p₂) ∧
     ¬ (∀ o₁ o₂ : O, F.obs o₁ = F.obs o₂) ∧
     ¬ (∀ s₁ s₂ : S, F.pred s₁ ↔ F.pred s₂)) ∧
    -- (d) Predicate is neither universally True nor universally False
    (¬ (∀ s : S, F.pred s) ∧ ¬ (∀ s : S, ¬ F.pred s)) := by
  have h_obs_ne :
      F.obs (F.eval (F.pick true)) ≠ F.obs (F.eval (F.pick false)) := by
    intro h_eq
    have h_false : F.pred (F.obs (F.eval (F.pick false))) :=
      Eq.mp (congrArg F.pred h_eq) F.true_holds
    exact F.false_ref h_false
  have h_eval_ne : F.eval (F.pick true) ≠ F.eval (F.pick false) := by
    intro h_eq
    exact h_obs_ne (congrArg F.obs h_eq)
  have h_pick_ne : F.pick true ≠ F.pick false := by
    intro h_eq
    exact h_eval_ne (congrArg F.eval h_eq)
  refine ⟨⟨h_pick_ne, h_eval_ne, h_obs_ne⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro h_subP
      exact h_pick_ne (@Subsingleton.elim P h_subP (F.pick true) (F.pick false))
    · intro h_subO
      exact h_eval_ne (@Subsingleton.elim O h_subO
        (F.eval (F.pick true)) (F.eval (F.pick false)))
    · intro h_subS
      exact h_obs_ne (@Subsingleton.elim S h_subS
        (F.obs (F.eval (F.pick true))) (F.obs (F.eval (F.pick false))))
  · refine ⟨?_, ?_, ?_⟩
    · intro h_const_eval
      exact h_eval_ne (h_const_eval (F.pick true) (F.pick false))
    · intro h_const_obs
      exact h_obs_ne (h_const_obs (F.eval (F.pick true)) (F.eval (F.pick false)))
    · intro h_const_pred
      exact F.false_ref
        ((h_const_pred (F.obs (F.eval (F.pick true)))
          (F.obs (F.eval (F.pick false)))).mp F.true_holds)
  · refine ⟨?_, ?_⟩
    · intro h_all_true
      exact F.false_ref (h_all_true (F.obs (F.eval (F.pick false))))
    · intro h_all_false
      exact h_all_false (F.obs (F.eval (F.pick true))) F.true_holds

/-- Any semantics map `sem : P → B` through which `F.eval` factors (`eval =
    proj ∘ sem`) separates `F.pick true` and `F.pick false` (`sem (pick true) ≠
    sem (pick false)`). -/
theorem TwoPointFactorization.sem_ne_of_factors {P O S B : Type}
    (F : TwoPointFactorization P O S) (sem : P → B) (proj : B → O)
    (h_fac : ∀ p, F.eval p = proj (sem p)) :
    sem (F.pick true) ≠ sem (F.pick false) := by
  intro h_eq
  have h_eval_eq : F.eval (F.pick true) = F.eval (F.pick false) := by
    rw [h_fac (F.pick true), h_fac (F.pick false), h_eq]
  exact (twoPointFactorization_nondegeneracy F).1.2.1 h_eval_eq

/-- Construct a `TwoPointFactorization L.Prog L.Out SemObs` from a positive
    spine verification `L.VerifiedSpineOn dom pre obsPost goodProg` together
    with a witnessed violating outcome `o_bad` of `badProg` at query `q₀`
    (`pre q₀`). -/
def TwoPointFactorization.ofVerifiedSpineWitness {SemObs : Type}
    (L : Language SemObs)
    {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg badProg : L.Prog}
    (q₀ : L.Query) (_hq₀ : pre q₀)
    (o_good o_bad : L.Out)
    (h_good_obs : obsPost q₀ (L.obs o_good))
    (h_bad_obs  : ¬ obsPost q₀ (L.obs o_bad))
    (h_prog_ne  : goodProg ≠ badProg)
    [inst : DecidableEq L.Prog] :
    TwoPointFactorization L.Prog L.Out SemObs where
  pick b := if b then goodProg else badProg
  eval p :=
    match inst p goodProg with
    | isTrue _  => o_good
    | isFalse _ => o_bad
  obs    := L.obs
  pred   := obsPost q₀
  true_holds := by
    dsimp
    cases inst goodProg goodProg with
    | isTrue _  => exact h_good_obs
    | isFalse h => exact False.elim (h rfl)
  false_ref := by
    dsimp
    cases inst badProg goodProg with
    | isTrue h  => exact False.elim (h_prog_ne (Eq.symm h))
    | isFalse _ => exact h_bad_obs

/-- Construct a `TwoPointFactorization L.Prog L.Out SemObs` with **zero**
    `DecidableEq` or `Classical` assumptions whenever an outcome selector
    `evalAt : L.Prog → L.Out` at `q₀` selects a valid outcome of `goodProg` and
    a violating outcome of `badProg`. -/
def TwoPointFactorization.ofOutcomeSelector {SemObs : Type}
    (L : Language SemObs)
    {dom pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg : L.Prog} (badProg : L.Prog)
    (h_good : L.VerifiedSpineOn dom pre obsPost goodProg)
    (q₀ : L.Query) (hq₀ : pre q₀)
    (evalAt : L.Prog → L.Out)
    (h_eval_good : ∀ h : (L.sem goodProg q₀).defined,
      (L.sem goodProg q₀).val h (evalAt goodProg))
    (h_eval_bad : ¬ obsPost q₀ (L.obs (evalAt badProg))) :
    TwoPointFactorization L.Prog L.Out SemObs where
  pick b := if b then goodProg else badProg
  eval   := evalAt
  obs    := L.obs
  pred   := obsPost q₀
  true_holds := by
    cases h_good.2.2 q₀ hq₀ with
    | intro hdef_good hpost_good =>
      exact hpost_good (evalAt goodProg) (h_eval_good hdef_good)
  false_ref := h_eval_bad

/-- **Four-Way Canary Squeeze via Universal Two-Point Factorization
    (`verifiedSpineWithCanariesOn_four_way_squeeze`):**
    For any
    `L.VerifiedSpineWithCanariesOn dom pre obsPost goodProg (badProg :: rest)`
    where `badProg` is productive on `pre` (`L.ProductiveOn pre badProg`) and
    `∀ q, pre q → dom q`, the universal two-point contradiction principle
    simultaneously proves in pure constructive logic (`0` axioms):
    1. **Strictly inhabited precondition:** `∃ q, pre q`,
    2. **Non-trivial spine postcondition:**
       `¬ (∀ q o, pre q → obsPost q (L.obs o))`,
    3. **Non-constant observable projection and non-subsingleton spine:**
       `¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂)` and `¬ Subsingleton SemObs`,
    4. **Non-ignoring program semantics and program distinctness:**
       `L.sem goodProg ≠ L.sem badProg` and `goodProg ≠ badProg`. -/
theorem verifiedSpineWithCanariesOn_four_way_squeeze {SemObs : Type}
    {L : Language SemObs}
    {dom pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg badProg : L.Prog} {rest : List L.Prog}
    (h_can : L.VerifiedSpineWithCanariesOn dom pre obsPost goodProg (badProg :: rest))
    (h_sub : ∀ q, pre q → dom q)
    (h_bad_prod : L.ProductiveOn pre badProg) :
    (∃ q, pre q) ∧
    ¬ (∀ q o, pre q → obsPost q (L.obs o)) ∧
    ¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂) ∧
    ¬ Subsingleton SemObs ∧
    L.sem goodProg ≠ L.sem badProg ∧
    goodProg ≠ badProg := by
  have h_good : L.VerifiedSpineOn dom pre obsPost goodProg := h_can.1
  have h_bad_ref : ¬ L.VerifiedSpineOn dom pre obsPost badProg := h_can.2.2.1
  -- 1. Strictly inhabited precondition:
  have h_inhab : ∃ q, pre q := by
    cases h_good.1 with
    | inl hex => exact hex
    | inr h_no_dom =>
      have h_bad_ver : L.VerifiedSpineOn dom pre obsPost badProg :=
        ⟨Or.inr h_no_dom,
         fun q hpre => False.elim (h_no_dom q (h_sub q hpre)),
         fun q hpre => False.elim (h_no_dom q (h_sub q hpre))⟩
      exact False.elim (h_bad_ref h_bad_ver)
  -- 2. Non-trivial spine postcondition:
  have h_nontriv : ¬ (∀ q o, pre q → obsPost q (L.obs o)) := by
    intro h_triv
    apply h_bad_ref
    refine ⟨h_good.1, h_bad_prod, ?_⟩
    intro q hpre
    cases h_bad_prod q hpre with
    | intro hdef_bad _ =>
      exact ⟨hdef_bad, fun o _ => h_triv q o hpre⟩
  -- 3. Non-constant observable projection:
  have h_nonconst_obs : ¬ (∀ o₁ o₂ : L.Out, L.obs o₁ = L.obs o₂) := by
    intro h_const
    apply h_bad_ref
    refine ⟨h_good.1, h_bad_prod, ?_⟩
    intro q hpre
    cases h_good.2.1 q hpre with
    | intro _ hout_good =>
      cases hout_good with
      | intro o_good ho_good =>
        cases h_good.2.2 q hpre with
        | intro _ hpost_good =>
          have h_obs_good : obsPost q (L.obs o_good) :=
            hpost_good o_good ho_good
          cases h_bad_prod q hpre with
          | intro hdef_bad _ =>
            refine ⟨hdef_bad, fun o_bad _ => ?_⟩
            dsimp [Language.SpecOn]
            rw [h_const o_bad o_good]
            exact h_obs_good
  -- 4. Non-subsingleton SemObs:
  have h_nonsub_semObs : ¬ Subsingleton SemObs := by
    intro h_subS
    exact h_nonconst_obs (fun o₁ o₂ =>
      @Subsingleton.elim SemObs h_subS (L.obs o₁) (L.obs o₂))
  -- 5. Distinct program semantics and distinct programs:
  have h_sem_ne : L.sem goodProg ≠ L.sem badProg := by
    intro h_eq
    apply h_bad_ref
    refine ⟨h_good.1, h_bad_prod, ?_⟩
    rw [← h_eq]
    exact h_good.2.2
  have h_prog_ne : goodProg ≠ badProg := by
    intro h_eq
    exact h_sem_ne (congrArg L.sem h_eq)
  exact ⟨h_inhab, h_nontriv, h_nonconst_obs, h_nonsub_semObs, h_sem_ne, h_prog_ne⟩

/-- When a productive mutant `badProg` has a witnessed violating outcome `o_bad`
    at `q₀` (`pre q₀`), we obtain an explicit `TwoPointFactorization` on the
    Concrete Outcome and Observable Spine carriers (`TwoPointFactorization Bool
    L.Out SemObs`), recovering `o_good ≠ o_bad`, `L.obs o_good ≠ L.obs o_bad`,
    `¬ Subsingleton L.Out`, and `¬ Subsingleton SemObs` directly from
    `twoPointFactorization_nondegeneracy`. -/
theorem verifiedSpine_witness_induces_twoPointFactorization {SemObs : Type}
    {L : Language SemObs}
    {dom pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg badProg : L.Prog}
    (h_good : L.VerifiedSpineOn dom pre obsPost goodProg)
    (q₀ : L.Query) (hq₀ : pre q₀)
    (o_bad : L.Out)
    (h_bad_val : ∃ h : (L.sem badProg q₀).defined, (L.sem badProg q₀).val h o_bad)
    (h_bad_viol : ¬ obsPost q₀ (L.obs o_bad)) :
    ∃ (o_good : L.Out) (F : TwoPointFactorization Bool L.Out SemObs),
      (∃ h : (L.sem goodProg q₀).defined, (L.sem goodProg q₀).val h o_good) ∧
      F.eval true = o_good ∧
      F.eval false = o_bad ∧
      F.obs = L.obs ∧
      F.pred = obsPost q₀ ∧
      o_good ≠ o_bad ∧
      L.obs o_good ≠ L.obs o_bad ∧
      ¬ Subsingleton L.Out ∧
      ¬ Subsingleton SemObs ∧
      L.sem goodProg ≠ L.sem badProg := by
  cases h_good.2.1 q₀ hq₀ with
  | intro hdef_good hout_good =>
    cases hout_good with
    | intro o_good ho_good =>
      cases h_good.2.2 q₀ hq₀ with
      | intro _ hpost_good =>
        have h_good_obs : obsPost q₀ (L.obs o_good) := hpost_good o_good ho_good
        let F : TwoPointFactorization Bool L.Out SemObs := {
          pick       := fun b => b
          eval       := fun b => if b then o_good else o_bad
          obs        := L.obs
          pred       := obsPost q₀
          true_holds := h_good_obs
          false_ref  := h_bad_viol
        }
        have h_nondeg := twoPointFactorization_nondegeneracy F
        have h_sem_ne : L.sem goodProg ≠ L.sem badProg := by
          intro h_eq
          cases h_bad_val with
          | intro hdef_bad ho_bad =>
            have h_good_at_bad : (L.sem goodProg q₀).val hdef_good o_bad := by
              have h_eq_q₀ : L.sem goodProg q₀ = L.sem badProg q₀ :=
                congrFun h_eq q₀
              exact Eq.mpr
                (congrArg (fun p => ∀ h : p.defined, p.val h o_bad) h_eq_q₀)
                (fun _ => ho_bad)
                hdef_good
            exact h_bad_viol (hpost_good o_bad h_good_at_bad)
        exact ⟨o_good, F, ⟨hdef_good, ho_good⟩, rfl, rfl, rfl, rfl,
          h_nondeg.1.2.1, h_nondeg.1.2.2, h_nondeg.2.1.2.1, h_nondeg.2.1.2.2,
          h_sem_ne⟩

/-!
## 2. The Bounded Refinement Sandwich (`BoundedRefinementSandwich`)

In refinement calculus (Dijkstra 1976; Nelson 1989; Morgan 1988, 1990; Back &
von Wright 1998), the predicate-transformer lattice has two dual extremes:
- **Bottom (`⊥ = Partial.bot`):** The unguarded miracle (`wp(S, false) = true`,
  or outcome set `∅`), which refines every defined specification vacuously.
  Dijkstra's **Law 1 (Law of the Excluded Miracle)** requires `b` to lie
  strictly above `⊥` (`¬ (b ≤ Partial.bot)`).
- **Top (`⊤_ub = Partial.ub` and `⊤_def = Partial.chaosDef`):** Abort/chaos,
  which every program refines vacuously. A non-trivial specification at an
  inhabited query `q₀` must be both defined (`¬ (Partial.ub ≤ spec)`) and
  strictly below defined chaos (`¬ (Partial.chaosDef ≤ spec)`).

We prove the exact algebraic characterizations of all three boundaries and
combine them into the **Bounded Refinement Sandwich Theorem**.
-/

/-- Strict refinement (`a < b`) in a `Preorder`: `a ≤ b` and `¬ (b ≤ a)`. -/
def StrictlyRefines {B : Type u} [Preorder B] (a b : B) : Prop :=
  a ≤ b ∧ ¬ (b ≤ a)

infix:50 " <ᵣ " => StrictlyRefines

/-- `Partial.bot` is the bottom element (`⊥`) of `Partial (Out → Prop)`: it
    refines every `p : Partial (Out → Prop)`. -/
theorem Partial.bot_le {Out : Type u} (p : Partial (Out → Prop)) :
    (Partial.bot : Partial (Out → Prop)) ≤ p :=
  fun _ => ⟨trivial, fun _ h => False.elim h⟩

/-- `Partial.ub` is the top element (`⊤_ub`) of `Partial B`: every
    `p : Partial B` refines `Partial.ub`. -/
theorem Partial.le_ub {B : Type u} [Preorder B] (p : Partial B) :
    p ≤ (Partial.ub : Partial B) :=
  fun h => False.elim h

/-- `Partial.chaosDef` refines `Partial.ub`, and every defined `p : Partial (Out
    → Prop)` refines `Partial.chaosDef`. -/
theorem Partial.le_chaosDef_of_defined {Out : Type u}
    {p : Partial (Out → Prop)} (h : p.defined) :
    p ≤ (Partial.chaosDef : Partial (Out → Prop)) :=
  fun _ => ⟨h, fun _ _ => trivial⟩

/-- `Partial.chaosDef` is strictly below `Partial.ub` (`⊤_def <ᵣ ⊤_ub`). -/
theorem Partial.chaosDef_strictlyRefines_ub {Out : Type u} :
    (Partial.chaosDef : Partial (Out → Prop)) <ᵣ Partial.ub :=
  ⟨Partial.le_ub Partial.chaosDef, fun h =>
    let ⟨h_false, _⟩ := h trivial
    h_false⟩

/-- Characterization of collapse to `Partial.bot` (`b ≤ ⊥`): `b` refines
    `Partial.bot` if and only if `b` is defined and its outcome set is empty
    (`∀ h o, ¬ b.val h o`). -/
theorem Partial.le_bot_iff {Out : Type u} (b : Partial (Out → Prop)) :
    b ≤ (Partial.bot : Partial (Out → Prop)) ↔
      (b.defined ∧ ∀ (h : b.defined) (o : Out), ¬ b.val h o) := by
  constructor
  · intro hle
    cases hle trivial with
    | intro hdef hsub =>
      exact ⟨hdef, fun _ o ho => hsub o ho⟩
  · intro ⟨hdef, hempty⟩ _
    exact ⟨hdef, fun o ho => hempty hdef o ho⟩

/-- **Dijkstra's Law of the Excluded Miracle
    (`excluded_miracle_imp_not_le_bot`):**
    Any defined, outcome-inhabited behavior `b`
    (`∃ h : b.defined, ∃ o, b.val h o`) lies strictly above `Partial.bot`
    (`Partial.bot <ᵣ b`, i.e., `Partial.bot ≤ b ∧ ¬ (b ≤ Partial.bot)`).
    Conversely, whenever `b.defined` and `∃ o, b.val h o` are decidable (or
    under `b.defined` with decidable outcome inhabitation),
    `¬ (b ≤ Partial.bot)` is equivalent to `∃ h : b.defined, ∃ o, b.val h o`. -/
theorem Partial.excluded_miracle_imp_not_le_bot {Out : Type u}
    {b : Partial (Out → Prop)}
    (h_prod : ∃ h : b.defined, ∃ o : Out, b.val h o) :
    ¬ (b ≤ (Partial.bot : Partial (Out → Prop))) := by
  intro hle
  cases h_prod with
  | intro hdef hout =>
    cases hout with
    | intro o ho =>
      exact (Partial.le_bot_iff b).mp hle |>.2 hdef o ho

theorem Partial.strictly_above_bot_of_productive {Out : Type u}
    {b : Partial (Out → Prop)}
    (h_prod : ∃ h : b.defined, ∃ o : Out, b.val h o) :
    (Partial.bot : Partial (Out → Prop)) <ᵣ b :=
  ⟨Partial.bot_le b, Partial.excluded_miracle_imp_not_le_bot h_prod⟩

theorem Partial.not_le_bot_and_defined_iff_productive {Out : Type u}
    (b : Partial (Out → Prop))
    [∀ h : b.defined, Decidable (∃ o : Out, b.val h o)] :
    (b.defined ∧ ¬ (b ≤ (Partial.bot : Partial (Out → Prop)))) ↔
      (∃ h : b.defined, ∃ o : Out, b.val h o) := by
  constructor
  · intro ⟨hdef, h_not_bot⟩
    refine ⟨hdef, ?_⟩
    cases Decidable.em (∃ o : Out, b.val hdef o) with
    | inl hex => exact hex
    | inr hno =>
      have h_le_bot : b ≤ Partial.bot :=
        (Partial.le_bot_iff b).mpr ⟨hdef, fun _ o ho => hno ⟨o, ho⟩⟩
      exact False.elim (h_not_bot h_le_bot)
  · intro ⟨hdef, o, ho⟩
    exact ⟨hdef, Partial.excluded_miracle_imp_not_le_bot ⟨hdef, o, ho⟩⟩

/-- **Undefined Top Characterization (`ub_le_iff_not_defined` and
    `not_ub_le_iff_defined`):**
    1. `Partial.ub ≤ spec ↔ ¬ spec.defined` (holds unconditionally with zero
       decidability assumptions).
    2. `spec.defined → ¬ (Partial.ub ≤ spec)` (and is an `↔` whenever
       `[Decidable spec.defined]`). -/
theorem Partial.ub_le_iff_not_defined {B : Type u} [Preorder B]
    (spec : Partial B) :
    (Partial.ub : Partial B) ≤ spec ↔ ¬ spec.defined := by
  constructor
  · intro hle hdef
    cases hle hdef with
    | intro h_false _ => exact h_false
  · intro h_not_def hdef
    exact False.elim (h_not_def hdef)

theorem Partial.defined_imp_not_ub_le {B : Type u} [Preorder B]
    {spec : Partial B} (hdef : spec.defined) :
    ¬ ((Partial.ub : Partial B) ≤ spec) :=
  fun hle => (Partial.ub_le_iff_not_defined spec).mp hle hdef

theorem Partial.not_ub_le_iff_defined {B : Type u} [Preorder B]
    (spec : Partial B) [Decidable spec.defined] :
    ¬ ((Partial.ub : Partial B) ≤ spec) ↔ spec.defined := by
  constructor
  · intro h_not_le
    cases Decidable.em spec.defined with
    | inl hdef => exact hdef
    | inr hnot =>
      exact False.elim (h_not_le ((Partial.ub_le_iff_not_defined spec).mpr hnot))
  · exact Partial.defined_imp_not_ub_le

/-- **Chaotic Defined Top Characterization (`chaosDef_le_iff` and
    `strictly_below_chaosDef_of_refuted_outcome`):**
    1. `Partial.chaosDef ≤ spec ↔ ∀ h : spec.defined, ∀ o : Out, spec.val h o`.
    2. Whenever `spec.defined` holds and there exists an outcome `o_bad : Out`
       rejected by `spec` (`¬ spec.val h o_bad`), `spec` is strictly below
       `Partial.chaosDef` (`spec <ᵣ Partial.chaosDef`). -/
theorem Partial.chaosDef_le_iff {Out : Type u}
    (spec : Partial (Out → Prop)) :
    (Partial.chaosDef : Partial (Out → Prop)) ≤ spec ↔
      ∀ (h : spec.defined) (o : Out), spec.val h o := by
  constructor
  · intro hle hdef o
    cases hle hdef with
    | intro _ hsub => exact hsub o trivial
  · intro hall hdef
    exact ⟨trivial, fun o _ => hall hdef o⟩

theorem Partial.strictly_below_chaosDef_of_refuted_outcome {Out : Type u}
    {spec : Partial (Out → Prop)}
    (hdef : spec.defined) (o_bad : Out) (h_reject : ¬ spec.val hdef o_bad) :
    spec <ᵣ (Partial.chaosDef : Partial (Out → Prop)) := by
  refine ⟨Partial.le_chaosDef_of_defined hdef, ?_⟩
  intro hle
  exact h_reject ((Partial.chaosDef_le_iff spec).mp hle hdef o_bad)

theorem Partial.strictly_below_chaosDef_iff {Out : Type u}
    (spec : Partial (Out → Prop))
    [∀ h : spec.defined, ∀ o : Out, Decidable (spec.val h o)]
    [∀ h : spec.defined, Decidable (∃ o : Out, ¬ spec.val h o)] :
    (spec <ᵣ (Partial.chaosDef : Partial (Out → Prop))) ↔
      ∃ h : spec.defined, ∃ o : Out, ¬ spec.val h o := by
  constructor
  · intro ⟨hle_chaos, h_not_chaos_le⟩
    cases hle_chaos trivial with
    | intro hdef _ =>
      refine ⟨hdef, ?_⟩
      cases Decidable.em (∃ o : Out, ¬ spec.val hdef o) with
      | inl hex => exact hex
      | inr hno =>
        have h_all : ∀ (h : spec.defined) (o : Out), spec.val h o := by
          intro _ o
          cases Decidable.em (spec.val hdef o) with
          | inl hyes => exact hyes
          | inr hnot => exact False.elim (hno ⟨o, hnot⟩)
        exact False.elim (h_not_chaos_le ((Partial.chaosDef_le_iff spec).mpr h_all))
  · intro ⟨hdef, o_bad, h_reject⟩
    exact Partial.strictly_below_chaosDef_of_refuted_outcome hdef o_bad h_reject

/-- Mutual refinement (`a ≈ b := a ≤ b ∧ b ≤ a`) in a `Preorder`. -/
def RefinesEquiv {B : Type u} [Preorder B] (a b : B) : Prop :=
  a ≤ b ∧ b ≤ a

infix:50 " ≈ᵣ " => RefinesEquiv

/-- Strict refinement `a <ᵣ b` implies `¬ (a ≈ᵣ b)`. -/
theorem StrictlyRefines.not_equiv {B : Type u} [Preorder B] {a b : B}
    (h : a <ᵣ b) : ¬ (a ≈ᵣ b) :=
  fun heq => h.2 heq.2

/-- Transitivity of `StrictlyRefines` with `≤` on the left (`a <ᵣ b → b ≤ c →
    a <ᵣ c`). -/
theorem StrictlyRefines.trans_le {B : Type u} [Preorder B] {a b c : B}
    (hab : a <ᵣ b) (hbc : b ≤ c) : a <ᵣ c :=
  ⟨Preorder.le_trans hab.1 hbc, fun hca => hab.2 (Preorder.le_trans hbc hca)⟩

/-- Transitivity of `≤` with `StrictlyRefines` on the right (`a ≤ b → b <ᵣ c →
    a <ᵣ c`). -/
theorem StrictlyRefines.le_trans {B : Type u} [Preorder B] {a b c : B}
    (hab : a ≤ b) (hbc : b <ᵣ c) : a <ᵣ c :=
  ⟨Preorder.le_trans hab hbc.1, fun hca => hbc.2 (Preorder.le_trans hca hab)⟩

/-- Transitivity of `StrictlyRefines` (`a <ᵣ b → b <ᵣ c → a <ᵣ c`). -/
theorem StrictlyRefines.trans {B : Type u} [Preorder B] {a b c : B}
    (hab : a <ᵣ b) (hbc : b <ᵣ c) : a <ᵣ c :=
  StrictlyRefines.trans_le hab hbc.1

/-- Pointed two-sided refinement sandwich at a query `q₀`:
    `⊥ <ᵣ impl ≤ spec <ᵣ ⊤_def <ᵣ ⊤_ub`. -/
def BoundedRefinementSandwich {Out : Type u}
    (impl spec : Partial (Out → Prop)) : Prop :=
  (Partial.bot : Partial (Out → Prop)) <ᵣ impl ∧
  impl ≤ spec ∧
  spec <ᵣ (Partial.chaosDef : Partial (Out → Prop)) ∧
  (Partial.chaosDef : Partial (Out → Prop)) <ᵣ Partial.ub

/-- **Four-Level Non-Collapse Theorem
    (`boundedRefinementSandwich_separates_levels`):**
    Under `BoundedRefinementSandwich impl spec`, all six strict refinement
    inequalities across `⊥`, `impl`/`spec`, `⊤_def`, and `⊤_ub` hold
    simultaneously, blocking:
    1. Miracle collapse (`¬ (impl ≈ᵣ Partial.bot)` and
       `¬ (spec ≈ᵣ Partial.bot)`),
    2. Chaotic postcondition collapse (`¬ (impl ≈ᵣ Partial.chaosDef)` and
       `¬ (spec ≈ᵣ Partial.chaosDef)`),
    3. Undefined / false-precondition collapse (`¬ (impl ≈ᵣ Partial.ub)` and
       `¬ (spec ≈ᵣ Partial.ub)`), and
    4. Global lattice degeneracy (`¬ (Partial.bot ≈ᵣ Partial.chaosDef)` and
       `¬ (Partial.bot ≈ᵣ Partial.ub)`). -/
theorem boundedRefinementSandwich_separates_levels {Out : Type u}
    {impl spec : Partial (Out → Prop)}
    (h : BoundedRefinementSandwich impl spec) :
    (Partial.bot <ᵣ impl ∧
     Partial.bot <ᵣ spec ∧
     impl <ᵣ Partial.chaosDef ∧
     spec <ᵣ Partial.chaosDef ∧
     impl <ᵣ Partial.ub ∧
     spec <ᵣ Partial.ub ∧
     (Partial.bot : Partial (Out → Prop)) <ᵣ Partial.chaosDef ∧
     (Partial.bot : Partial (Out → Prop)) <ᵣ Partial.ub) ∧
    (¬ (impl ≈ᵣ Partial.bot) ∧
     ¬ (spec ≈ᵣ Partial.chaosDef) ∧
     ¬ (spec ≈ᵣ Partial.ub) ∧
     ¬ ((Partial.bot : Partial (Out → Prop)) ≈ᵣ Partial.chaosDef)) := by
  have ⟨h_bot_impl, h_impl_spec, h_spec_chaos, h_chaos_ub⟩ := h
  have h_bot_spec : Partial.bot <ᵣ spec :=
    StrictlyRefines.trans_le h_bot_impl h_impl_spec
  have h_impl_chaos : impl <ᵣ Partial.chaosDef :=
    StrictlyRefines.le_trans h_impl_spec h_spec_chaos
  have h_spec_ub : spec <ᵣ Partial.ub :=
    StrictlyRefines.trans h_spec_chaos h_chaos_ub
  have h_impl_ub : impl <ᵣ Partial.ub :=
    StrictlyRefines.le_trans h_impl_spec h_spec_ub
  have h_bot_chaos : (Partial.bot : Partial (Out → Prop)) <ᵣ Partial.chaosDef :=
    StrictlyRefines.trans h_bot_spec h_spec_chaos
  have h_bot_ub : (Partial.bot : Partial (Out → Prop)) <ᵣ Partial.ub :=
    StrictlyRefines.trans h_bot_chaos h_chaos_ub
  refine ⟨⟨h_bot_impl, h_bot_spec, h_impl_chaos, h_spec_chaos,
      h_impl_ub, h_spec_ub, h_bot_chaos, h_bot_ub⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    exact h_bot_impl.2 heq.1
  · exact StrictlyRefines.not_equiv h_spec_chaos
  · exact StrictlyRefines.not_equiv h_spec_ub
  · exact StrictlyRefines.not_equiv h_bot_chaos

/-- **The Bounded Refinement Sandwich Theorem
    (`boundedRefinementSandwich_of_verifiedSpine_witness`):**
    If `goodProg` satisfies `L.VerifiedSpineOn dom pre obsPost goodProg` and a
    productive mutant `badProg` produces an outcome `o_bad` at `q₀` (`pre q₀`)
    violating `obsPost q₀ (L.obs o_bad)`, then at `q₀` the implementation
    behavior `L.sem goodProg q₀` and specification
    `L.SpineSpecOn pre obsPost q₀` form a strict four-level refinement chain:
    `⊥ <ᵣ L.sem goodProg q₀ ≤ L.SpineSpecOn pre obsPost q₀ <ᵣ ⊤_def <ᵣ ⊤_ub`.
    Conversely, any `BoundedRefinementSandwich (L.sem goodProg q₀)
    (L.SpineSpecOn pre obsPost q₀)` guarantees that `pre q₀` holds (`spec ≠
    ⊤_ub`), `goodProg` is UB-free at `q₀`, `goodProg` is non-miraculous at `q₀`
    (`impl ≠ ⊥`), and `obsPost q₀` is non-trivial (`spec ≠ ⊤_def`). -/
theorem boundedRefinementSandwich_of_verifiedSpine_witness {SemObs : Type}
    {L : Language SemObs}
    {dom pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg : L.Prog}
    (h_good : L.VerifiedSpineOn dom pre obsPost goodProg)
    (q₀ : L.Query) (hq₀ : pre q₀)
    (o_bad : L.Out) (h_bad_viol : ¬ obsPost q₀ (L.obs o_bad)) :
    BoundedRefinementSandwich
      (L.sem goodProg q₀)
      (L.SpineSpecOn pre obsPost q₀) := by
  have h_prod_q₀ :
      ∃ h : (L.sem goodProg q₀).defined, ∃ o, (L.sem goodProg q₀).val h o :=
    h_good.2.1 q₀ hq₀
  have h_above_bot :
      (Partial.bot : Partial (L.Out → Prop)) <ᵣ L.sem goodProg q₀ :=
    Partial.strictly_above_bot_of_productive h_prod_q₀
  have h_impl_le_spec :
      L.sem goodProg q₀ ≤ L.SpineSpecOn pre obsPost q₀ :=
    h_good.2.2 q₀
  have h_below_chaos :
      L.SpineSpecOn pre obsPost q₀ <ᵣ Partial.chaosDef :=
    Partial.strictly_below_chaosDef_of_refuted_outcome hq₀ o_bad h_bad_viol
  exact ⟨h_above_bot, h_impl_le_spec, h_below_chaos,
    Partial.chaosDef_strictlyRefines_ub⟩

/-- Converse extraction from `BoundedRefinementSandwich`: any strict refinement
    sandwich at `q₀` forces `pre q₀` to hold, `(L.sem goodProg q₀).defined` to
    hold, `¬ (L.sem goodProg q₀ ≤ Partial.bot)`, and
    `¬ (∀ o, obsPost q₀ (L.obs o))`. -/
theorem boundedRefinementSandwich_converse {SemObs : Type}
    {L : Language SemObs}
    {pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop}
    {goodProg : L.Prog} {q₀ : L.Query}
    (h_sand : BoundedRefinementSandwich
      (L.sem goodProg q₀)
      (L.SpineSpecOn pre obsPost q₀)) :
    pre q₀ ∧
    (L.sem goodProg q₀).defined ∧
    ¬ (L.sem goodProg q₀ ≤ Partial.bot) ∧
    ¬ (∀ o : L.Out, obsPost q₀ (L.obs o)) := by
  have ⟨⟨_, h_not_bot⟩, h_le_spec, ⟨h_le_chaos, h_not_chaos_le⟩, _⟩ := h_sand
  cases h_le_chaos trivial with
  | intro hpre _ =>
    cases h_le_spec hpre with
    | intro hdef_good _ =>
      refine ⟨hpre, hdef_good, h_not_bot, ?_⟩
      intro h_all_obs
      exact h_not_chaos_le
        ((Partial.chaosDef_le_iff (L.SpineSpecOn pre obsPost q₀)).mpr
          (fun _ o => h_all_obs o))

/-!
## 3. Plotkin Ground Adequacy & Final Observable Quotient (`ObsEquiv`)

In Plotkin's *"LCF Considered as a Programming Language"* (1977) and Milner's
*"Fully Abstract Models of Typed λ-Calculi"* (1977), contextual equivalence of
programs is tested by plugging programs into ground-type contexts `C[·] : ι`
(where `ι` is a ground observable type such as `Bool` or `Nat`).
In Anneal, `SemObs` is the ground observation sort and `L.obs : L.Out → SemObs`
is the ground observation projection that quotients concrete outcomes `L.Out` by
unobservable representation slack (scratch registers, dead flags, padding
bytes).
-/

/-- Kernel equivalence relation induced by the ground observable projection
    `L.obs : L.Out → SemObs`. Two concrete outcomes `o₁, o₂ : L.Out` are
    observably equivalent (`ObsEquiv L o₁ o₂`) if and only if they have the same
    ground observable spine in `SemObs`. -/
def ObsEquiv {SemObs : Type} (L : Language SemObs) (o₁ o₂ : L.Out) : Prop :=
  L.obs o₁ = L.obs o₂

theorem ObsEquiv.refl {SemObs : Type} (L : Language SemObs) (o : L.Out) :
    ObsEquiv L o o :=
  rfl

theorem ObsEquiv.symm {SemObs : Type} {L : Language SemObs} {o₁ o₂ : L.Out}
    (h : ObsEquiv L o₁ o₂) : ObsEquiv L o₂ o₁ :=
  Eq.symm h

theorem ObsEquiv.trans {SemObs : Type} {L : Language SemObs} {o₁ o₂ o₃ : L.Out}
    (h₁₂ : ObsEquiv L o₁ o₂) (h₂₃ : ObsEquiv L o₂ o₃) : ObsEquiv L o₁ o₃ :=
  Eq.trans h₁₂ h₂₃

/-- `ObsEquiv L` is a standard Lean `Equivalence` relation on `L.Out`. -/
theorem ObsEquiv.equivalence {SemObs : Type} (L : Language SemObs) :
    Equivalence (ObsEquiv L) where
  refl  := ObsEquiv.refl L
  symm  := ObsEquiv.symm
  trans := ObsEquiv.trans

/-- **Invariance of `SpineSpecOn` under `ObsEquiv`
    (`spineSpecOn_invariant_under_obsEquiv`):**
    Every spine-anchored specification `L.SpineSpecOn pre obsPost` respects
    `ObsEquiv L`: if `o₁` and `o₂` differ only on unobservable representation
    slack (`ObsEquiv L o₁ o₂`), then `o₁` satisfies `L.SpineSpecOn` at `q` if
    and only if `o₂` does. -/
theorem spineSpecOn_invariant_under_obsEquiv {SemObs : Type}
    (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (q : L.Query) (h : (L.SpineSpecOn pre obsPost q).defined)
    {o₁ o₂ : L.Out} (heq : ObsEquiv L o₁ o₂) :
    (L.SpineSpecOn pre obsPost q).val h o₁ ↔
      (L.SpineSpecOn pre obsPost q).val h o₂ := by
  dsimp [Language.SpineSpecOn, Language.SpecOn]
  unfold ObsEquiv at heq
  rw [heq]

/-- **Universal Quotient Factorization Property of `SpineSpecOn`
    (`spineSpecOn_unique_factorization`):**
    If two spine predicates `obsPost₁, obsPost₂ : L.Query → SemObs → Prop`
    induce equivalent outcome predicates on `L.Out` at query `q` (`∀ o,
    obsPost₁ q (L.obs o) ↔ obsPost₂ q (L.obs o)`), then `obsPost₁ q v ↔
    obsPost₂ q v` holds for every reachable ground observable `v` in the image
    of `L.obs` (`∃ o, L.obs o = v`). -/
theorem spineSpecOn_unique_factorization {SemObs : Type}
    (L : Language SemObs)
    (obsPost₁ obsPost₂ : L.Query → SemObs → Prop)
    (q : L.Query)
    (h_ext : ∀ o : L.Out, obsPost₁ q (L.obs o) ↔ obsPost₂ q (L.obs o))
    (v : SemObs) (h_surj : ∃ o : L.Out, L.obs o = v) :
    obsPost₁ q v ↔ obsPost₂ q v := by
  cases h_surj with
  | intro o ho =>
    rw [← ho]
    exact h_ext o

/-- **Plotkin Ground Adequacy Necessity Theorem
    (`plotkin_inadequate_obs_collapses_verification`):**
    If a language's observation map `L.obs` fails ground computational adequacy
    by mapping all outcomes of `goodProg` and `badProg` at `q` to the same
    ground observation (`∀ o₁ o₂, ObsEquiv L o₁ o₂`), then NO spine-anchored
    specification `L.SpineSpecOn pre obsPost` can simultaneously verify
    `goodProg` and refute a productive `badProg`! -/
theorem plotkin_inadequate_obs_collapses_verification {SemObs : Type}
    (L : Language SemObs)
    (dom pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop)
    (goodProg badProg : L.Prog)
    (h_collapse : ∀ o₁ o₂ : L.Out, ObsEquiv L o₁ o₂)
    (h_good : L.VerifiedSpineOn dom pre obsPost goodProg)
    (h_bad_prod : L.ProductiveOn pre badProg) :
    L.VerifiedSpineOn dom pre obsPost badProg := by
  refine ⟨h_good.1, h_bad_prod, ?_⟩
  intro q hpre
  cases h_good.2.1 q hpre with
  | intro _ hout_good =>
    cases hout_good with
    | intro o_good ho_good =>
      cases h_good.2.2 q hpre with
      | intro _ hpost_good =>
        have h_obs_good : obsPost q (L.obs o_good) :=
          hpost_good o_good ho_good
        cases h_bad_prod q hpre with
        | intro hdef_bad _ =>
          refine ⟨hdef_bad, fun o_bad _ => ?_⟩
          exact (spineSpecOn_invariant_under_obsEquiv L pre obsPost q hpre
            (h_collapse o_good o_bad)).mp h_obs_good

/-!
## 4. Goguen-Burstall Institution Satisfaction & Two-Point Separation Transfer
   across `BehaviorCodec`

In Goguen & Burstall's theory of **Institutions** (1984, 1992), a specification
framework consists of signatures `Σ`, `Σ`-sentences `Sen(Σ)`, `Σ`-models
`Mod(Σ)`, and a satisfaction relation `M ⊨_Σ φ` such that for any morphism
`σ : Σ → Σ'`, the **Satisfaction Condition** holds:
`M' ⊨_{Σ'} Sen(σ)(φ) ↔ Mod(σ)(M') ⊨_Σ φ`.

In Anneal, a `BehaviorCodec L₁ L₂` over a shared observable spine `SemObs` is
simultaneously:
1. A **Galois retraction / section pair** (Cousot & Cousot 1977, 1979) on
   queries (`decodeQuery ∘ encodeQuery = id`) and outcomes
   (`decodeOut ∘ encodeOut = some`),
2. A **coalgebra homomorphism** (Rutten 2000) preserving the final observable
   projection `SemObs` (`L₂.obs o₂ = L₁.obs o₁` whenever `decodeOut o₂ =
   some o₁`), and
3. An **Institution Morphism** translating source spine specifications
   `φ = (pre, obsPost)` to target spine specifications
   `σ(φ) = (pre ∘ c.decodeQuery, fun q₂ v => obsPost (c.decodeQuery q₂) v)`.
-/

/-- In any `BehaviorCodec L₁ L₂`, `encodeQuery` is injective and `decodeQuery`
    is surjective (`decodeQuery ∘ encodeQuery = id`). -/
theorem Trusted.BehaviorCodec.encodeQuery_injective {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂) :
    ∀ {q₁ q₁' : L₁.Query}, c.encodeQuery q₁ = c.encodeQuery q₁' → q₁ = q₁' := by
  intro q₁ q₁' h_eq
  have h := congrArg c.decodeQuery h_eq
  rw [c.decodeQuery_encodeQuery q₁, c.decodeQuery_encodeQuery q₁'] at h
  exact h

theorem Trusted.BehaviorCodec.decodeQuery_surjective {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂) (q₁ : L₁.Query) :
    ∃ q₂ : L₂.Query, c.decodeQuery q₂ = q₁ :=
  ⟨c.encodeQuery q₁, c.decodeQuery_encodeQuery q₁⟩

/-- In any `BehaviorCodec L₁ L₂`, `encodeOut` is injective and preserves the
    observable spine `SemObs` (`L₂.obs (c.encodeOut o₁) = L₁.obs o₁`). -/
theorem Trusted.BehaviorCodec.encodeOut_injective {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂) :
    ∀ {o₁ o₁' : L₁.Out}, c.encodeOut o₁ = c.encodeOut o₁' → o₁ = o₁' := by
  intro o₁ o₁' h_eq
  have h := congrArg c.decodeOut h_eq
  rw [c.decodeOut_encodeOut o₁, c.decodeOut_encodeOut o₁'] at h
  injection h

theorem Trusted.BehaviorCodec.obs_encodeOut {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂) (o₁ : L₁.Out) :
    L₂.obs (c.encodeOut o₁) = L₁.obs o₁ :=
  c.obs_decodeOut (c.encodeOut o₁) o₁ (c.decodeOut_encodeOut o₁)

/-- Every target outcome `o₂` that decodes to `some o₁` is `ObsEquiv L₂` to the
    canonical encoding `c.encodeOut o₁`. -/
theorem Trusted.BehaviorCodec.obsEquiv_encodeOut_of_decodeOut {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    {o₂ : L₂.Out} {o₁ : L₁.Out} (h : c.decodeOut o₂ = some o₁) :
    ObsEquiv L₂ o₂ (c.encodeOut o₁) := by
  unfold ObsEquiv
  rw [c.obs_decodeOut o₂ o₁ h, c.obs_encodeOut o₁]

/-- Sentence translation functor `Sen(c)` for spine specifications along
    `c : BehaviorCodec L₁ L₂`. -/
def Trusted.BehaviorCodec.translateSpineSpec {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    (pre : L₁.Query → Prop) (obsPost : L₁.Query → SemObs → Prop) :
    L₂.Behavior :=
  L₂.SpineSpecOn
    (fun q₂ => pre (c.decodeQuery q₂))
    (fun q₂ v => obsPost (c.decodeQuery q₂) v)

/-- **Goguen-Burstall Institution Satisfaction Condition for `BehaviorCodec`
    (`institution_satisfaction_iff`):**
    For any `c : BehaviorCodec L₁ L₂`, target query `q₂ : L₂.Query`, and target
    outcome `o₂ : L₂.Out` with `c.decodeOut o₂ = some o₁`:
    1. **Precondition/definedness satisfaction:**
       `(c.translateSpineSpec pre obsPost q₂).defined ↔
        (L₁.SpineSpecOn pre obsPost (c.decodeQuery q₂)).defined` (by `rfl`).
    2. **Outcome satisfaction (`o₂ ⊨_{L₂} Sen(c)(φ) ↔ o₁ ⊨_{L₁} φ`):**
       `(c.translateSpineSpec pre obsPost q₂).val h₂ o₂ ↔
        (L₁.SpineSpecOn pre obsPost (c.decodeQuery q₂)).val h₁ o₁`. -/
theorem institution_satisfaction_iff {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    (pre : L₁.Query → Prop) (obsPost : L₁.Query → SemObs → Prop)
    (q₂ : L₂.Query) {o₂ : L₂.Out} {o₁ : L₁.Out}
    (h_dec : c.decodeOut o₂ = some o₁) :
    ((c.translateSpineSpec pre obsPost q₂).defined ↔
      (L₁.SpineSpecOn pre obsPost (c.decodeQuery q₂)).defined) ∧
    (∀ (h₂ : (c.translateSpineSpec pre obsPost q₂).defined)
       (h₁ : (L₁.SpineSpecOn pre obsPost (c.decodeQuery q₂)).defined),
      (c.translateSpineSpec pre obsPost q₂).val h₂ o₂ ↔
        (L₁.SpineSpecOn pre obsPost (c.decodeQuery q₂)).val h₁ o₁) := by
  refine ⟨Iff.rfl, fun _ _ => ?_⟩
  dsimp [BehaviorCodec.translateSpineSpec, Language.SpineSpecOn, Language.SpecOn]
  rw [c.obs_decodeOut o₂ o₁ h_dec]

/-- **Institution Satisfaction at Encoded Source Queries
    (`institution_satisfaction_at_encodeQuery_iff`):**
    At `q₂ = c.encodeQuery q₁`, the translated specification's definedness and
    outcome satisfaction coincide with `pre q₁` and `obsPost q₁ (L₁.obs o₁)`. -/
theorem institution_satisfaction_at_encodeQuery_iff {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    (pre : L₁.Query → Prop) (obsPost : L₁.Query → SemObs → Prop)
    (q₁ : L₁.Query) {o₂ : L₂.Out} {o₁ : L₁.Out}
    (h_dec : c.decodeOut o₂ = some o₁) :
    ((c.translateSpineSpec pre obsPost (c.encodeQuery q₁)).defined ↔ pre q₁) ∧
    (∀ (h₂ : (c.translateSpineSpec pre obsPost (c.encodeQuery q₁)).defined),
      (c.translateSpineSpec pre obsPost (c.encodeQuery q₁)).val h₂ o₂ ↔
        obsPost q₁ (L₁.obs o₁)) := by
  refine ⟨?_, ?_⟩
  · dsimp [BehaviorCodec.translateSpineSpec, Language.SpineSpecOn, Language.SpecOn]
    rw [c.decodeQuery_encodeQuery q₁]
  · intro _
    dsimp [BehaviorCodec.translateSpineSpec, Language.SpineSpecOn, Language.SpecOn]
    rw [c.decodeQuery_encodeQuery q₁, c.obs_decodeOut o₂ o₁ h_dec]

/-- Forward spine specification transfer across `Compiles` as an immediate
    corollary of the Institution Satisfaction Condition. -/
theorem compiles_transfers_spineSpecOn {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    {s : L₁.Prog} {t : L₂.Prog}
    {pre : L₁.Query → Prop} {obsPost : L₁.Query → SemObs → Prop}
    (h_spec : L₁.sem s ≤ L₁.SpineSpecOn pre obsPost)
    (h_comp : Compiles L₁ L₂ c s t) :
    L₂.sem t ≤ c.translateSpineSpec pre obsPost := by
  intro q₂ hdef_tgt_spec
  cases h_spec (c.decodeQuery q₂) hdef_tgt_spec with
  | intro hdef₁ hpost₁ =>
    cases h_comp q₂ hdef₁ with
    | intro hdef₂ hval₂ =>
      refine ⟨hdef₂, fun o₂ ho₂ => ?_⟩
      cases hval₂ o₂ ho₂ with
      | intro o₁ h₁ =>
        cases h₁ with
        | intro h_dec ho₁ =>
          exact (institution_satisfaction_iff c pre obsPost q₂ h_dec).2
            hdef_tgt_spec hdef_tgt_spec |>.mpr (hpost₁ o₁ ho₁)

/-- **Two-Point Separation Transfer Theorem across `BehaviorCodec`
    (`codec_transfers_two_point_separation`):**
    Suppose:
    1. `good₁ : L₁.Prog` satisfies `L₁.VerifiedSpineOn dom₁ pre obsPost good₁`,
    2. `bad₁ : L₁.Prog` is defined at `q₁` (`pre q₁`) and every concrete outcome
       `o_bad₁` of `bad₁` at `q₁` violates `obsPost q₁ (L₁.obs o_bad₁)` (for
       example, when `bad₁` is a deterministic off-by-one or wrong-value mutant
       at `q₁`), and
    3. `good₂, bad₂ : L₂.Prog` compile `good₁, bad₁` via
       `ProductiveCompiles L₁ L₂ c good₁ good₂` and
       `ProductiveCompiles L₁ L₂ c bad₁ bad₂`, where `bad₁` is productive at
       `q₁`.
    Then at the encoded target query `q₂ := c.encodeQuery q₁`:
    - `good₂` and `bad₂` produce concrete target outcomes `o_good₂` and `o_bad₂`
      decoding to `o_good₁` and `o_bad₁`,
    - `(good₂, bad₂)` induces a target
      `TwoPointFactorization Bool L₂.Out SemObs` at `q₂`,
    - **Exact Ground Observable Preservation:**
      `L₂.obs o_good₂ = L₁.obs o_good₁`, `L₂.obs o_bad₂ = L₁.obs o_bad₁`, and
      `L₂.obs o_good₂ ≠ L₂.obs o_bad₂` in `SemObs`,
    - `o_good₂ ≠ o_bad₂`, `L₂.sem good₂ ≠ L₂.sem bad₂`, and `good₂ ≠ bad₂`, and
    - `bad₂` is refuted on the translated target spine specification (`¬
      L₂.VerifiedSpineOn dom₂ (pre ∘ c.decodeQuery) (fun q₂ v => obsPost
      (c.decodeQuery q₂) v) bad₂` for every `dom₂`). -/
theorem codec_transfers_two_point_separation {SemObs : Type}
    {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂)
    {dom₁ pre : L₁.Query → Prop}
    {obsPost : L₁.Query → SemObs → Prop}
    {good₁ bad₁ : L₁.Prog}
    {good₂ bad₂ : L₂.Prog}
    (h_good₁ : L₁.VerifiedSpineOn dom₁ pre obsPost good₁)
    (q₁ : L₁.Query) (hq₁ : pre q₁)
    (h_bad₁_prod_q₁ :
      ∃ h₁ : (L₁.sem bad₁ q₁).defined, ∃ o₁, (L₁.sem bad₁ q₁).val h₁ o₁)
    (h_bad₁_viol_all :
      ∀ (h₁ : (L₁.sem bad₁ q₁).defined) (o₁ : L₁.Out),
        (L₁.sem bad₁ q₁).val h₁ o₁ → ¬ obsPost q₁ (L₁.obs o₁))
    (h_pcomp_good : ProductiveCompiles L₁ L₂ c good₁ good₂)
    (h_pcomp_bad  : ProductiveCompiles L₁ L₂ c bad₁ bad₂) :
    ∃ (o_good₁ o_bad₁ : L₁.Out) (o_good₂ o_bad₂ : L₂.Out)
      (F₂ : TwoPointFactorization Bool L₂.Out SemObs),
      c.decodeOut o_good₂ = some o_good₁ ∧
      c.decodeOut o_bad₂ = some o_bad₁ ∧
      L₂.obs o_good₂ = L₁.obs o_good₁ ∧
      L₂.obs o_bad₂ = L₁.obs o_bad₁ ∧
      obsPost q₁ (L₂.obs o_good₂) ∧
      ¬ obsPost q₁ (L₂.obs o_bad₂) ∧
      L₂.obs o_good₂ ≠ L₂.obs o_bad₂ ∧
      o_good₂ ≠ o_bad₂ ∧
      F₂.eval true = o_good₂ ∧
      F₂.eval false = o_bad₂ ∧
      L₂.sem good₂ ≠ L₂.sem bad₂ ∧
      good₂ ≠ bad₂ ∧
      (∀ dom₂ : L₂.Query → Prop,
        ¬ L₂.VerifiedSpineOn dom₂
            (fun q₂ => pre (c.decodeQuery q₂))
            (fun q₂ v => obsPost (c.decodeQuery q₂) v)
            bad₂) := by
  let q₂ := c.encodeQuery q₁
  have h_dec_q₂ : c.decodeQuery q₂ = q₁ := c.decodeQuery_encodeQuery q₁
  have h_pre₂ : pre (c.decodeQuery q₂) :=
    Eq.mpr (congrArg pre h_dec_q₂) hq₁
  -- 1. Extract target outcome `o_good₂` of `good₂` at `q₂` and its source
  --    decoding `o_good₁`:
  have h_good₁_prod_q₁ :
      ∃ h₁ : (L₁.sem good₁ q₁).defined, ∃ o₁, (L₁.sem good₁ q₁).val h₁ o₁ :=
    h_good₁.2.1 q₁ hq₁
  cases h_pcomp_good.2 q₁ h_good₁_prod_q₁ with
  | intro hdef_good₂ hout_good₂ =>
    cases hout_good₂ with
    | intro o_good₂ ho_good₂ =>
      cases h_good₁_prod_q₁ with
      | intro hdef_good₁ _ =>
        have hdef_good₁_map : (L₁.sem good₁ (c.decodeQuery q₂)).defined :=
          Eq.mpr (congrArg (fun q => (L₁.sem good₁ q).defined) h_dec_q₂)
            hdef_good₁
        cases h_pcomp_good.1 q₂ hdef_good₁_map with
        | intro _ hval_good₂ =>
          cases hval_good₂ o_good₂ ho_good₂ with
          | intro o_good₁ h_good_pair =>
            cases h_good_pair with
            | intro hdec_good ho_good₁_map =>
              -- 2. Extract target outcome `o_bad₂` of `bad₂` at `q₂` and its
              --    source decoding `o_bad₁`:
              cases h_pcomp_bad.2 q₁ h_bad₁_prod_q₁ with
              | intro hdef_bad₂ hout_bad₂ =>
                cases hout_bad₂ with
                | intro o_bad₂ ho_bad₂ =>
                  cases h_bad₁_prod_q₁ with
                  | intro hdef_bad₁ _ =>
                    have hdef_bad₁_map :
                        (L₁.sem bad₁ (c.decodeQuery q₂)).defined :=
                      Eq.mpr
                        (congrArg (fun q => (L₁.sem bad₁ q).defined) h_dec_q₂)
                        hdef_bad₁
                    cases h_pcomp_bad.1 q₂ hdef_bad₁_map with
                    | intro _ hval_bad₂ =>
                      cases hval_bad₂ o_bad₂ ho_bad₂ with
                      | intro o_bad₁ h_bad_pair =>
                        cases h_bad_pair with
                        | intro hdec_bad ho_bad₁_map =>
                          -- 3. Establish `obsPost` satisfaction for `o_good₁`
                          --    and violation for `o_bad₁`:
                          cases h_good₁.2.2 (c.decodeQuery q₂) h_pre₂ with
                          | intro _ hpost_good₁_map =>
                            have h_obs_good₁_map :
                                obsPost (c.decodeQuery q₂) (L₁.obs o_good₁) :=
                              hpost_good₁_map o_good₁ ho_good₁_map
                            have h_obs_good₁ : obsPost q₁ (L₁.obs o_good₁) :=
                              Eq.mp
                                (congrArg (fun q => obsPost q (L₁.obs o_good₁))
                                  h_dec_q₂)
                                h_obs_good₁_map
                            have ho_bad₁_q₁ :
                                ∃ h₁ : (L₁.sem bad₁ q₁).defined,
                                  (L₁.sem bad₁ q₁).val h₁ o_bad₁ := by
                              have hex_map :
                                  ∃ h₁ : (L₁.sem bad₁ (c.decodeQuery q₂)).defined,
                                    (L₁.sem bad₁ (c.decodeQuery q₂)).val h₁ o_bad₁ :=
                                ⟨hdef_bad₁_map, ho_bad₁_map⟩
                              exact Eq.mp
                                (congrArg
                                  (fun q =>
                                    ∃ h₁ : (L₁.sem bad₁ q).defined,
                                      (L₁.sem bad₁ q).val h₁ o_bad₁)
                                  h_dec_q₂)
                                hex_map
                            cases ho_bad₁_q₁ with
                            | intro hdef_bad₁' ho_bad₁' =>
                              have h_not_obs_bad₁ :
                                  ¬ obsPost q₁ (L₁.obs o_bad₁) :=
                                h_bad₁_viol_all hdef_bad₁' o_bad₁ ho_bad₁'
                              -- 4. Spine preservation across `c`:
                              have h_obs_eq_good :
                                  L₂.obs o_good₂ = L₁.obs o_good₁ :=
                                c.obs_decodeOut o_good₂ o_good₁ hdec_good
                              have h_obs_eq_bad :
                                  L₂.obs o_bad₂ = L₁.obs o_bad₁ :=
                                c.obs_decodeOut o_bad₂ o_bad₁ hdec_bad
                              have h_obs_good₂ : obsPost q₁ (L₂.obs o_good₂) := by
                                rw [h_obs_eq_good]
                                exact h_obs_good₁
                              have h_not_obs_bad₂ :
                                  ¬ obsPost q₁ (L₂.obs o_bad₂) := by
                                rw [h_obs_eq_bad]
                                exact h_not_obs_bad₁
                              -- 5. Target TwoPointFactorization:
                              let F₂ : TwoPointFactorization Bool L₂.Out SemObs := {
                                pick       := fun b => b
                                eval       := fun b => if b then o_good₂ else o_bad₂
                                obs        := L₂.obs
                                pred       := obsPost q₁
                                true_holds := h_obs_good₂
                                false_ref  := h_not_obs_bad₂
                              }
                              have h_nondeg₂ :=
                                twoPointFactorization_nondegeneracy F₂
                              -- 6. Target refutation of `bad₂`:
                              have h_ref_bad₂ :
                                  ∀ dom₂ : L₂.Query → Prop,
                                    ¬ L₂.VerifiedSpineOn dom₂
                                        (fun q₂ => pre (c.decodeQuery q₂))
                                        (fun q₂ v => obsPost (c.decodeQuery q₂) v)
                                        bad₂ := by
                                intro dom₂ h_ver_bad₂
                                cases h_ver_bad₂.2.2 q₂ h_pre₂ with
                                | intro _ hpost_bad₂ =>
                                  have h_sat :
                                      obsPost (c.decodeQuery q₂) (L₂.obs o_bad₂) :=
                                    hpost_bad₂ o_bad₂ ho_bad₂
                                  rw [h_dec_q₂] at h_sat
                                  exact h_not_obs_bad₂ h_sat
                              -- 7. Target semantic separation
                              --    `L₂.sem good₂ ≠ L₂.sem bad₂`:
                              have h_tgt_good_spec :
                                  L₂.sem good₂ ≤ c.translateSpineSpec pre obsPost :=
                                compiles_transfers_spineSpecOn c h_good₁.2.2
                                  h_pcomp_good.1
                              have h_sem_ne₂ : L₂.sem good₂ ≠ L₂.sem bad₂ := by
                                intro h_eq_sem
                                cases h_tgt_good_spec q₂ h_pre₂ with
                                | intro hdef_g₂ hpost_g₂ =>
                                  have ho_good_at_bad :
                                      (L₂.sem good₂ q₂).val hdef_g₂ o_bad₂ := by
                                    have h_eq_q₂ :
                                        L₂.sem good₂ q₂ = L₂.sem bad₂ q₂ :=
                                      congrFun h_eq_sem q₂
                                    exact Eq.mpr
                                      (congrArg
                                        (fun p => ∀ h : p.defined, p.val h o_bad₂)
                                        h_eq_q₂)
                                      (fun _ => ho_bad₂)
                                      hdef_g₂
                                  have h_sat :
                                      obsPost (c.decodeQuery q₂) (L₂.obs o_bad₂) :=
                                    hpost_g₂ o_bad₂ ho_good_at_bad
                                  rw [h_dec_q₂] at h_sat
                                  exact h_not_obs_bad₂ h_sat
                              have h_prog_ne₂ : good₂ ≠ bad₂ :=
                                fun h_eq => h_sem_ne₂ (congrArg L₂.sem h_eq)
                              exact ⟨o_good₁, o_bad₁, o_good₂, o_bad₂, F₂,
                                hdec_good, hdec_bad,
                                h_obs_eq_good, h_obs_eq_bad,
                                h_obs_good₂, h_not_obs_bad₂,
                                h_nondeg₂.1.2.2, h_nondeg₂.1.2.1,
                                rfl, rfl,
                                h_sem_ne₂, h_prog_ne₂,
                                h_ref_bad₂⟩

/-- **Full Two-Sided Institution Transfer
    (`codec_transfers_verifiedSpineWithCanaries`):**
    When `c.encodeQuery (c.decodeQuery q₂) = q₂` holds on `pre` (or when target
    productivity on `pre ∘ c.decodeQuery` holds), `ProductiveCompiles` transfers
    the entire two-sided `VerifiedSpineWithCanariesOn` obligation from
    `(good₁, [bad₁])` in `L₁` to `(good₂, [bad₂])` in `L₂`! -/
theorem codec_transfers_verifiedSpineWithCanaries {SemObs : Type}
    {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂)
    {dom₁ pre : L₁.Query → Prop}
    {obsPost : L₁.Query → SemObs → Prop}
    {good₁ bad₁ : L₁.Prog}
    {good₂ bad₂ : L₂.Prog}
    (h_good₁ : L₁.VerifiedSpineOn dom₁ pre obsPost good₁)
    (q₁ : L₁.Query) (hq₁ : pre q₁)
    (h_bad₁_prod_q₁ :
      ∃ h₁ : (L₁.sem bad₁ q₁).defined, ∃ o₁, (L₁.sem bad₁ q₁).val h₁ o₁)
    (h_bad₁_viol_all :
      ∀ (h₁ : (L₁.sem bad₁ q₁).defined) (o₁ : L₁.Out),
        (L₁.sem bad₁ q₁).val h₁ o₁ → ¬ obsPost q₁ (L₁.obs o₁))
    (h_pcomp_good : ProductiveCompiles L₁ L₂ c good₁ good₂)
    (h_pcomp_bad  : ProductiveCompiles L₁ L₂ c bad₁ bad₂)
    (h_enc_dec : ∀ q₂, pre (c.decodeQuery q₂) →
      c.encodeQuery (c.decodeQuery q₂) = q₂)
    (dom₂ : L₂.Query → Prop) :
    L₂.VerifiedSpineWithCanariesOn dom₂
      (fun q₂ => pre (c.decodeQuery q₂))
      (fun q₂ v => obsPost (c.decodeQuery q₂) v)
      good₂ [bad₂] := by
  have h_trans :=
    codec_transfers_two_point_separation c h_good₁ q₁ hq₁ h_bad₁_prod_q₁
      h_bad₁_viol_all h_pcomp_good h_pcomp_bad
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_ref_bad₂⟩ := h_trans
  have h_nonvac₂ : NonVacuousOn dom₂ (fun q₂ => pre (c.decodeQuery q₂)) := by
    refine Or.inl ⟨c.encodeQuery q₁, ?_⟩
    dsimp
    rw [c.decodeQuery_encodeQuery q₁]
    exact hq₁
  have h_prod_good₂ :
      L₂.ProductiveOn (fun q₂ => pre (c.decodeQuery q₂)) good₂ := by
    intro q₂ hpre₂
    have hex₂ :=
      h_pcomp_good.2 (c.decodeQuery q₂)
        (h_good₁.2.1 (c.decodeQuery q₂) hpre₂)
    rw [h_enc_dec q₂ hpre₂] at hex₂
    exact hex₂
  have h_spec_good₂ : L₂.sem good₂ ≤ c.translateSpineSpec pre obsPost :=
    compiles_transfers_spineSpecOn c h_good₁.2.2 h_pcomp_good.1
  exact ⟨⟨h_nonvac₂, h_prod_good₂, h_spec_good₂⟩,
    (by intro h; cases h),
    ⟨h_ref_bad₂ dom₂, trivial⟩⟩

/-- **Witnessed Two-Point Separation Transfer for Nondeterministic Canaries
    (`codec_transfers_two_point_separation_of_witness`):**
    Even if `bad₁` is nondeterministic at `q₁` (so some outcomes satisfy
    `obsPost` while a witnessed outcome `o_bad₁` violates `obsPost`), as long as
    `bad₂` compiles `bad₁` via `Compiles L₁ L₂ c bad₁ bad₂` and produces a
    target outcome `o_bad₂` at `c.encodeQuery q₁` whose decoded source outcome
    violates `obsPost q₁` (or `o_bad₂` violates `obsPost q₁ (L₂.obs o_bad₂)`),
    `good₂` and `bad₂` inherit a `TwoPointFactorization Bool L₂.Out SemObs` at
    `c.encodeQuery q₁` with `L₂.obs o_good₂ = L₁.obs o_good₁`, `L₂.obs o_bad₂ =
    L₁.obs o_bad₁`, and `L₂.obs o_good₂ ≠ L₂.obs o_bad₂` in `SemObs`! -/
theorem codec_transfers_two_point_separation_of_witness {SemObs : Type}
    {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂)
    {dom₁ pre : L₁.Query → Prop}
    {obsPost : L₁.Query → SemObs → Prop}
    {good₁ bad₁ : L₁.Prog}
    {good₂ bad₂ : L₂.Prog}
    (h_good₁ : L₁.VerifiedSpineOn dom₁ pre obsPost good₁)
    (q₁ : L₁.Query) (hq₁ : pre q₁)
    (h_pcomp_good : ProductiveCompiles L₁ L₂ c good₁ good₂)
    (h_comp_bad   : Compiles L₁ L₂ c bad₁ bad₂)
    (h_bad₁_def   : (L₁.sem bad₁ q₁).defined)
    (o_bad₂ : L₂.Out)
    (ho_bad₂ : ∀ h₂ : (L₂.sem bad₂ (c.encodeQuery q₁)).defined,
      (L₂.sem bad₂ (c.encodeQuery q₁)).val h₂ o_bad₂)
    (h_bad₂_viol : ¬ obsPost q₁ (L₂.obs o_bad₂)) :
    ∃ (o_good₁ o_bad₁ : L₁.Out) (o_good₂ : L₂.Out)
      (F₂ : TwoPointFactorization Bool L₂.Out SemObs),
      c.decodeOut o_good₂ = some o_good₁ ∧
      c.decodeOut o_bad₂ = some o_bad₁ ∧
      L₂.obs o_good₂ = L₁.obs o_good₁ ∧
      L₂.obs o_bad₂ = L₁.obs o_bad₁ ∧
      obsPost q₁ (L₂.obs o_good₂) ∧
      ¬ obsPost q₁ (L₁.obs o_bad₁) ∧
      L₂.obs o_good₂ ≠ L₂.obs o_bad₂ ∧
      o_good₂ ≠ o_bad₂ ∧
      F₂.eval true = o_good₂ ∧
      F₂.eval false = o_bad₂ ∧
      L₂.sem good₂ ≠ L₂.sem bad₂ := by
  let q₂ := c.encodeQuery q₁
  have h_dec_q₂ : c.decodeQuery q₂ = q₁ := c.decodeQuery_encodeQuery q₁
  have h_pre₂ : pre (c.decodeQuery q₂) :=
    Eq.mpr (congrArg pre h_dec_q₂) hq₁
  have h_good₁_prod_q₁ := h_good₁.2.1 q₁ hq₁
  cases h_pcomp_good.2 q₁ h_good₁_prod_q₁ with
  | intro hdef_good₂ hout_good₂ =>
    cases hout_good₂ with
    | intro o_good₂ ho_good₂ =>
      cases h_good₁_prod_q₁ with
      | intro hdef_good₁ _ =>
        have hdef_good₁_map : (L₁.sem good₁ (c.decodeQuery q₂)).defined :=
          Eq.mpr (congrArg (fun q => (L₁.sem good₁ q).defined) h_dec_q₂)
            hdef_good₁
        cases h_pcomp_good.1 q₂ hdef_good₁_map with
        | intro _ hval_good₂ =>
          cases hval_good₂ o_good₂ ho_good₂ with
          | intro o_good₁ h_good_pair =>
            cases h_good_pair with
            | intro hdec_good ho_good₁_map =>
              have hdef_bad₁_map : (L₁.sem bad₁ (c.decodeQuery q₂)).defined :=
                Eq.mpr (congrArg (fun q => (L₁.sem bad₁ q).defined) h_dec_q₂)
                  h_bad₁_def
              cases h_comp_bad q₂ hdef_bad₁_map with
              | intro hdef_bad₂ hval_bad₂ =>
                cases hval_bad₂ o_bad₂ (ho_bad₂ hdef_bad₂) with
                | intro o_bad₁ h_bad_pair =>
                  cases h_bad_pair with
                  | intro hdec_bad _ =>
                    cases h_good₁.2.2 (c.decodeQuery q₂) h_pre₂ with
                    | intro _ hpost_good₁_map =>
                      have h_obs_good₁_map :
                          obsPost (c.decodeQuery q₂) (L₁.obs o_good₁) :=
                        hpost_good₁_map o_good₁ ho_good₁_map
                      have h_obs_good₁ : obsPost q₁ (L₁.obs o_good₁) :=
                        Eq.mp
                          (congrArg (fun q => obsPost q (L₁.obs o_good₁))
                            h_dec_q₂)
                          h_obs_good₁_map
                      have h_obs_eq_good : L₂.obs o_good₂ = L₁.obs o_good₁ :=
                        c.obs_decodeOut o_good₂ o_good₁ hdec_good
                      have h_obs_eq_bad : L₂.obs o_bad₂ = L₁.obs o_bad₁ :=
                        c.obs_decodeOut o_bad₂ o_bad₁ hdec_bad
                      have h_obs_good₂ : obsPost q₁ (L₂.obs o_good₂) := by
                        rw [h_obs_eq_good]
                        exact h_obs_good₁
                      have h_not_obs_bad₁ : ¬ obsPost q₁ (L₁.obs o_bad₁) := by
                        rw [← h_obs_eq_bad]
                        exact h_bad₂_viol
                      let F₂ : TwoPointFactorization Bool L₂.Out SemObs := {
                        pick       := fun b => b
                        eval       := fun b => if b then o_good₂ else o_bad₂
                        obs        := L₂.obs
                        pred       := obsPost q₁
                        true_holds := h_obs_good₂
                        false_ref  := h_bad₂_viol
                      }
                      have h_nondeg₂ := twoPointFactorization_nondegeneracy F₂
                      have h_tgt_good_spec :
                          L₂.sem good₂ ≤ c.translateSpineSpec pre obsPost :=
                        compiles_transfers_spineSpecOn c h_good₁.2.2
                          h_pcomp_good.1
                      have h_sem_ne₂ : L₂.sem good₂ ≠ L₂.sem bad₂ := by
                        intro h_eq_sem
                        cases h_tgt_good_spec q₂ h_pre₂ with
                        | intro hdef_g₂ hpost_g₂ =>
                          have ho_good_at_bad :
                              (L₂.sem good₂ q₂).val hdef_g₂ o_bad₂ := by
                            have h_eq_q₂ :
                                L₂.sem good₂ q₂ = L₂.sem bad₂ q₂ :=
                              congrFun h_eq_sem q₂
                            exact Eq.mpr
                              (congrArg
                                (fun p => ∀ h : p.defined, p.val h o_bad₂)
                                h_eq_q₂)
                              (fun _ => ho_bad₂ hdef_bad₂)
                              hdef_g₂
                          have h_sat :
                              obsPost (c.decodeQuery q₂) (L₂.obs o_bad₂) :=
                            hpost_g₂ o_bad₂ ho_good_at_bad
                          rw [h_dec_q₂] at h_sat
                          exact h_bad₂_viol h_sat
                      exact ⟨o_good₁, o_bad₁, o_good₂, F₂,
                        hdec_good, hdec_bad,
                        h_obs_eq_good, h_obs_eq_bad,
                        h_obs_good₂, h_not_obs_bad₁,
                        h_nondeg₂.1.2.2, h_nondeg₂.1.2.1,
                        rfl, rfl,
                        h_sem_ne₂⟩

/-!
## 5. Concrete End-to-End Instantiation & Kernel Axiom Audit

We instantiate all four universal characterizations on a concrete
source-to-target compilation example with target representation slack:
- `MirDemoLang`: source language (`SemObs = Nat`) where `true` (`good₁`)
  computes `q + 1` and `false` (`bad₁`) is an off-by-one mutant computing `q`.
- `X86SlackDemoLang`: target language (`Out = Nat × Nat`, representing
  `(rax, rcx_scratch)`) where `obs (rax, _) := rax` projects out caller-saved
  scratch register `rcx` (`ObsEquiv` quotients out `rcx`).
- `mirToX86SlackCodec`: spine-preserving `BehaviorCodec MirDemoLang
  X86SlackDemoLang` where `decodeOut (rax, _rcx) := some rax` maps arbitrary
  scratch-register states many-to-one onto `rax` while preserving
  `SemObs = Nat`.
-/

/-- Source language (`SemObs = Nat`, `obs = id`): `true` computes `q + 1`,
    `false` computes `q`. -/
abbrev MirDemoLang : Language Nat :=
  Language.mkSimple Bool Nat Nat (fun isGood q =>
    Partial.pure (fun o => o = if isGood then q + 1 else q))

/-- Target language (`Out = Nat × Nat` for `(rax, rcx_scratch)`, `SemObs = Nat`,
    `obs := Prod.fst`): `true` leaves scratch `rcx = 99` and returns
    `rax = q + 1`; `false` leaves scratch `rcx = 77` and returns `rax = q`. -/
abbrev X86SlackDemoLang : Language Nat where
  Prog  := Bool
  Query := Nat
  Out   := Nat × Nat
  obs o := o.1
  sem isGood q :=
    Partial.pure (fun o =>
      if isGood then o = (q + 1, 99) else o = (q, 77))

/-- Spine-preserving `BehaviorCodec` from `MirDemoLang` to `X86SlackDemoLang`
    that erases target caller-saved scratch register `rcx` (`o.2`) while
    preserving the return value spine `rax` (`o.1`). -/
def mirToX86SlackCodec : BehaviorCodec MirDemoLang X86SlackDemoLang where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut rax := (rax, 0)
  decodeOut o   := some o.1
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := by
    injection h with h_eq

/-- Two concrete target outcomes `(42, 0)` and `(42, 99)` with distinct scratch
    registers (`(42, 0) ≠ (42, 99)`) are `ObsEquiv X86SlackDemoLang`-equivalent
    and therefore indistinguishable to every `SpineSpecOn` specification. -/
theorem demo_obsEquiv_scratch_slack :
    (42, 0) ≠ (42, 99) ∧
    ObsEquiv X86SlackDemoLang (42, 0) (42, 99) :=
  ⟨by decide, rfl⟩

/-- `MirDemoLang` verifies `true` with negative canary `[false]` on
    `q < 100`. -/
theorem demo_mir_verifiedSpineWithCanaries :
    MirDemoLang.VerifiedSpineWithCanaries
      (fun q => q < 100) (fun q v => v = q + 1) true [false] := by
  refine ⟨⟨Or.inl ⟨0, by decide⟩, ?_, ?_⟩, (by intro h; cases h), ⟨?_, trivial⟩⟩
  · intro q _
    exact ⟨trivial, q + 1, rfl⟩
  · intro q _
    exact ⟨trivial, fun _ ho => ho⟩
  · intro h_bad
    have h0 : (0 : Nat) < 100 := by decide
    cases h_bad.2.2 0 h0 with
    | intro _ hpost =>
      have h_eq : (0 : Nat) = 0 + 1 := hpost 0 rfl
      cases h_eq

/-- Both `true` and `false` compile productively from `MirDemoLang` to
    `X86SlackDemoLang` under `mirToX86SlackCodec` (even though `true` sets
    `rcx = 99 ≠ 0` and `false` sets `rcx = 77 ≠ 0`). -/
theorem demo_mir_to_x86_productiveCompiles :
    ProductiveCompiles MirDemoLang X86SlackDemoLang mirToX86SlackCodec true true ∧
    ProductiveCompiles MirDemoLang X86SlackDemoLang mirToX86SlackCodec false false := by
  constructor
  · refine ⟨?_, ?_⟩
    · intro q _
      refine ⟨trivial, ?_⟩
      intro o ho
      dsimp [X86SlackDemoLang] at ho
      subst ho
      exact ⟨q + 1, rfl, rfl⟩
    · intro q _
      exact ⟨trivial, (q + 1, 99), rfl⟩
  · refine ⟨?_, ?_⟩
    · intro q _
      refine ⟨trivial, ?_⟩
      intro o ho
      dsimp [X86SlackDemoLang] at ho
      subst ho
      exact ⟨q, rfl, rfl⟩
    · intro q _
      exact ⟨trivial, (q, 77), rfl⟩

/-- End-to-end instantiation of `codec_transfers_verifiedSpineWithCanaries` and
    `boundedRefinementSandwich_of_verifiedSpine_witness` on
    `X86SlackDemoLang`. -/
theorem demo_x86_inherits_canaries_and_sandwich :
    X86SlackDemoLang.VerifiedSpineWithCanaries
      (fun q => q < 100) (fun q v => v = q + 1) true [false] ∧
    BoundedRefinementSandwich
      (X86SlackDemoLang.sem true 0)
      (X86SlackDemoLang.SpineSpecOn (fun q => q < 100) (fun q v => v = q + 1) 0) := by
  have h_mir := demo_mir_verifiedSpineWithCanaries
  have h_comp := demo_mir_to_x86_productiveCompiles
  have h_x86_can :
      X86SlackDemoLang.VerifiedSpineWithCanaries
        (fun q => q < 100) (fun q v => v = q + 1) true [false] :=
    @codec_transfers_verifiedSpineWithCanaries Nat MirDemoLang X86SlackDemoLang
      mirToX86SlackCodec
      MirDemoLang.dom (fun q => q < 100) (fun q v => v = q + 1)
      true false true false
      h_mir.1
      0 (by decide)
      ⟨trivial, 0, rfl⟩
      (fun _ o ho => by
        dsimp [MirDemoLang] at ho
        subst ho
        decide)
      h_comp.1
      h_comp.2
      (fun _ _ => rfl)
      X86SlackDemoLang.dom
  have h_sand :
      BoundedRefinementSandwich
        (X86SlackDemoLang.sem true 0)
        (X86SlackDemoLang.SpineSpecOn (fun q => q < 100) (fun q v => v = q + 1) 0) :=
    @boundedRefinementSandwich_of_verifiedSpine_witness Nat X86SlackDemoLang
      X86SlackDemoLang.dom (fun q => q < 100) (fun q v => v = q + 1) true
      h_x86_can.1 0 (by decide) (0, 77) (by decide)
  exact ⟨h_x86_can, h_sand⟩

end Anneal.UniversalAlgebraAndInstitutions

#print axioms Anneal.UniversalAlgebraAndInstitutions.twoPointFactorization_nondegeneracy
#print axioms Anneal.UniversalAlgebraAndInstitutions.verifiedSpineWithCanariesOn_four_way_squeeze
#print axioms Anneal.UniversalAlgebraAndInstitutions.verifiedSpine_witness_induces_twoPointFactorization
#print axioms Anneal.UniversalAlgebraAndInstitutions.boundedRefinementSandwich_separates_levels
#print axioms Anneal.UniversalAlgebraAndInstitutions.boundedRefinementSandwich_of_verifiedSpine_witness
#print axioms Anneal.UniversalAlgebraAndInstitutions.boundedRefinementSandwich_converse
#print axioms Anneal.UniversalAlgebraAndInstitutions.spineSpecOn_invariant_under_obsEquiv
#print axioms Anneal.UniversalAlgebraAndInstitutions.plotkin_inadequate_obs_collapses_verification
#print axioms Anneal.UniversalAlgebraAndInstitutions.institution_satisfaction_iff
#print axioms Anneal.UniversalAlgebraAndInstitutions.codec_transfers_two_point_separation
#print axioms Anneal.UniversalAlgebraAndInstitutions.codec_transfers_two_point_separation_of_witness
#print axioms Anneal.UniversalAlgebraAndInstitutions.codec_transfers_verifiedSpineWithCanaries
#print axioms Anneal.UniversalAlgebraAndInstitutions.demo_x86_inherits_canaries_and_sandwich
