-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Partial `compile` Refinement Algebra (`PartialCompileAlgebra.lean`)

This standalone module mechanizes and compares candidate representations of
partial compilation (`compile`) and conditional verification in Anneal's Layer
1A refinement framework (`Trusted/Refinement.lean` and
`theory/Anneal/Refinement.lean`):

1. **Candidate Representations of Partial `compile`:**
   - **Design A (`Partial L_tgt.Prog`):**
     `compile : L_src.Prog → Partial L_tgt.Prog` reuses the foundational
     `Partial` structure (`defined : Prop`, `val : defined → B`) already
     present in `Trusted/Refinement.lean`, adding `Partial.bind` for sequential
     pass composition and `Option.toPartial` for computable passes.
   - **Design B (`Option L_tgt.Prog`):**
     `compile : L_src.Prog → Option L_tgt.Prog` embeds homomorphically into
     `Partial L_tgt.Prog` via `Option.toPartial`, and is isomorphic to
     `Partial L_tgt.Prog` whenever `.defined` is decidable
     (`Partial.toOption`).
   - **Design C (Dual Liftings of `Language.sem` to `Partial L.Prog`):**
     - **Angelic / Conditional Lifting (`Language.semIfCompiled`):** Maps
       compile-time rejection (`defined = False`) to the bottom behavior
       `Partial.bot` (empty execution set), satisfying the universal property
       `L.semIfCompiled p? ≤ B ↔ ∀ h : p?.defined, L.sem (p?.val h) ≤ B`.
     - **Demonic / Total Lifting (`Language.semPartial`):** Maps compile-time
       rejection (`defined = False`) to the top behavior `Partial.ub`,
       satisfying
       `L.semPartial p? ≤ B ↔ (∀ q, (B q).defined → p?.defined) ∧`
       `∀ h : p?.defined, L.sem (p?.val h) ≤ B`.

2. **Three Modes of `Compiler.Verified` under Partial Compilation:**
   - **Mode 1 (`Compiler.Verified` / `VerifiedIfCompiled`):** Requires
     unconditional source correctness (`L_src.sem s ≤ spec`) and conditional
     target compilation and correctness (`∀ h : (C.compile s).defined, ...`).
   - **Mode 2 (`Compiler.VerifiedWhenCompiled`):** Conditions both source and
     target obligations on `h : (C.compile s).defined`. We prove the unification
     theorem `verifiedWhenCompiled_iff_verified_when`: under `Monotone C.π`,
     Mode 2 is equivalent to Mode 1 applied to the compilation-conditioned
     specification `Behavior.when (C.compile s).defined spec` (which specializes
     to `L.SpecOn (fun q => (C.compile s).defined ∧ pre q) post`).
   - **Mode 3 (`Compiler.VerifiedTotal`):** Requires `(C.compile s).defined`
     alongside Mode 1 (equivalently, `(C.compile s).defined` alongside Mode 2).
   - **Discriminating Canaries:** Mechanized counterexamples demonstrating the
     vacuity hazard of unguarded Mode 2 when `(C.compile s).defined` is `False`
     on a program with source UB, and showing how PME-guarded programs behave
     across all three modes.

3. **Multi-Pass Composition (`Compiler.comp`, `SoundOn.comp`, `Verified.comp`,
   `verify_through_passes`, `Compiler.Verified.mono`):**
   Generalizes all pass-composition and Y-diagram bridge theorems from
   `theory/Anneal/Refinement.lean` to partial compilers, and proves exact
   equivalence with the total-compiler definitions when `compile` is lifted via
   `Partial.pure`.
-/

namespace PartialCompileAlgebra

/-!
## 1. Core Refinement Preorder and `Partial` Algebra
-/

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder in which
    stronger propositions refine weaker ones. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever the codomain `B` is a `Preorder`. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- A partially defined value of type `B`, constructively representing a value
    gated by a propositional definedness condition `defined : Prop`:
    - In `Behavior`, `defined` records whether execution at query `q` is free
      of Undefined Behavior (UB), with `defined = False` representing the top
      element `Partial.ub`.
    - In `Compiler.compile`, `defined` records whether compilation of source
      program `s` succeeds without a compile-time error or Post-Monomorphization
      Error (PME), with `val : defined → L_tgt.Prog` yielding the compiled
      target artifact whenever `defined` holds. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`
    (`defined := True`). -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element of `Partial B` (`defined := False`), which acts as
    the top element ($\mathsf{UB}$) under `instPreorderPartial`. -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- The bottom predicate element of `Partial (Out → Prop)` (`defined := True`,
    `val := fun _ _ => False`), representing an empty set of outcomes (such as
    an inapplicable query or a program rejected before runtime execution). -/
def Partial.bot {Out : Type u} : Partial (Out → Prop) :=
  Partial.pure (fun _ => False)

/-- Map a function `f : B₁ → B₂` over the defined payload of a `Partial B₁`,
    preserving `.defined`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Monadic bind on `Partial`: `Partial.bind p f` is defined when `p` is
    defined (`h : p.defined`) and `f (p.val h)` is defined, yielding the value
    of `f (p.val h)`. Used to compose partial compiler passes and to define
    demonic partial semantics (`Language.semPartial`). -/
def Partial.bind {B₁ : Type u} {B₂ : Type v}
    (p : Partial B₁) (f : B₁ → Partial B₂) : Partial B₂ where
  defined := ∃ h : p.defined, (f (p.val h)).defined
  val h := (f (p.val h.1)).val h.2

/-- Refinement preorder on `Partial B`: `p₁ ≤ p₂` holds when, whenever `p₂` is
    defined (`h₂ : p₂.defined`), `p₁` is also defined (`h₁ : p₁.defined`) and
    its value refines `p₂`'s value (`p₁.val h₁ ≤ p₂.val h₂`). -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Mutual refinement equivalence (`x ≤ y ∧ y ≤ x`) in a `Preorder`. -/
def RefinesEquiv {B : Type u} [Preorder B] (x y : B) : Prop :=
  x ≤ y ∧ y ≤ x

/-- Structural equivalence of two `Partial B` values (`p₁.defined ↔ p₂.defined`
    with identical `.val` outputs whenever defined), which does not require a
    `Preorder` on `B`. -/
def Partial.Equiv {B : Type u} (p₁ p₂ : Partial B) : Prop :=
  (p₁.defined ↔ p₂.defined) ∧
  ∀ (h₁ : p₁.defined) (h₂ : p₂.defined), p₁.val h₁ = p₂.val h₂

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Identity mapping on any behavior domain is monotone. -/
theorem monotone_id {B : Type u} [Preorder B] : Monotone (fun b : B => b) :=
  fun _ _ h => h

/-- Composition of two monotone mappings is monotone. -/
theorem monotone_comp {A : Type u} {B : Type v} {C : Type w}
    [Preorder A] [Preorder B] [Preorder C]
    {g : B → C} {f : A → B}
    (hg : Monotone g) (hf : Monotone f) :
    Monotone (fun a => g (f a)) :=
  fun _ _ h => hg (hf h)

/-- Lifting a monotone map `f : B₁ → B₂` via `Partial.map` yields a monotone
    map `Partial B₁ → Partial B₂`. -/
theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v}
    [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp hdef₂
  cases hp hdef₂ with
  | intro hdef₁ hle =>
    exact ⟨hdef₁, hf hle⟩

/-- `Partial.ub` (`defined := False`) is the top element of `Partial B`: every
    partial value `p : Partial B` refines `Partial.ub`. -/
theorem ub_top {B : Type u} [Preorder B] (p : Partial B) :
    p ≤ Partial.ub :=
  fun h => False.elim h

/-- `Partial.ub` refines a partial value `p : Partial B` if and only if `p` is
    undefined (`¬ p.defined`). -/
theorem ub_le_iff {B : Type u} [Preorder B] (p : Partial B) :
    Partial.ub ≤ p ↔ ¬ p.defined :=
  ⟨fun h hdef => (h hdef).1, fun hnot hdef => False.elim (hnot hdef)⟩

/-- On unconditionally defined values (`Partial.pure`), the `Partial B`
    refinement preorder coincides with the underlying preorder on `B`. -/
theorem pure_le_pure_iff {B : Type u} [Preorder B] (b₁ b₂ : B) :
    Partial.pure b₁ ≤ Partial.pure b₂ ↔ b₁ ≤ b₂ := by
  constructor
  · intro h
    cases h True.intro with
    | intro _ hle => exact hle
  · intro hle _
    exact ⟨True.intro, hle⟩

/-- Undefined behavior (`Partial.ub`) never refines a defined specification
    (`Partial.pure b`). -/
theorem not_ub_le_pure {B : Type u} [Preorder B] (b : B) :
    ¬ ((@Partial.ub B) ≤ Partial.pure b) :=
  fun h => (ub_le_iff (Partial.pure b)).mp h True.intro

/-- `Partial.bot` is the bottom element of `Partial (Out → Prop)`: it refines
    every `p : Partial (Out → Prop)`. -/
theorem bot_le {Out : Type u} (p : Partial (Out → Prop)) :
    Partial.bot ≤ p :=
  fun _ => ⟨True.intro, fun _ hfalse => False.elim hfalse⟩

/-- A partial predicate `p : Partial (Out → Prop)` refines `Partial.bot` if and
    only if `p` is defined and its outcome set is empty (`∀ o, ¬ p.val h o`). -/
theorem le_bot_iff {Out : Type u} (p : Partial (Out → Prop)) :
    p ≤ Partial.bot ↔ ∃ h : p.defined, ∀ o, ¬ p.val h o := by
  constructor
  · intro h
    exact h True.intro
  · intro h _
    exact h

/-- Left identity law for `Partial.bind`: `Partial.bind (Partial.pure b) f` is
    structurally equivalent to `f b`. -/
theorem Partial.bind_pure_left {B₁ : Type u} {B₂ : Type v}
    (b : B₁) (f : B₁ → Partial B₂) :
    Partial.Equiv (Partial.bind (Partial.pure b) f) (f b) := by
  refine ⟨⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩, ?_⟩
  intro _ _
  rfl

/-- Right identity law for `Partial.bind`: `Partial.bind p Partial.pure` is
    structurally equivalent to `p`. -/
theorem Partial.bind_pure_right {B : Type u} (p : Partial B) :
    Partial.Equiv (Partial.bind p Partial.pure) p := by
  refine ⟨⟨fun h => h.1, fun h => ⟨h, True.intro⟩⟩, ?_⟩
  intro _ _
  rfl

/-- Associativity law for `Partial.bind`: nesting `Partial.bind` on the left or
    right yields structurally equivalent `Partial` values. -/
theorem Partial.bind_assoc {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    (p : Partial B₁) (f : B₁ → Partial B₂) (g : B₂ → Partial B₃) :
    Partial.Equiv
      (Partial.bind (Partial.bind p f) g)
      (Partial.bind p (fun x => Partial.bind (f x) g)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    exact ⟨h.1.1, ⟨h.1.2, h.2⟩⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · intro _ _
    rfl

/-!
## 2. Design A (`Partial`) vs. Design B (`Option`) Embedding and Isomorphism
-/

/-- Canonical embedding of a computable `Option B` into `Partial B`:
    - `some b` maps to `Partial.pure b` (`defined = True`, `val _ = b`), and
    - `none` maps to `Partial.ub` (`defined = False`, `val = False.elim`). -/
def Option.toPartial {B : Type u} : Option B → Partial B
  | some b => Partial.pure b
  | none => Partial.ub

/-- Extract an `Option B` from a `Partial B` when `p.defined` is decidable. -/
def Partial.toOption {B : Type u} (p : Partial B) [Decidable p.defined] :
    Option B :=
  if h : p.defined then some (p.val h) else none

@[simp]
theorem Option.toPartial_some {B : Type u} (b : B) :
    Option.toPartial (some b) = Partial.pure b :=
  rfl

@[simp]
theorem Option.toPartial_none {B : Type u} :
    Option.toPartial (@none B) = Partial.ub :=
  rfl

/-- `Option.toPartial o` is defined if and only if `o = some b` for some
    `b : B`. -/
theorem Option.toPartial_defined_iff {B : Type u} (o : Option B) :
    (Option.toPartial o).defined ↔ ∃ b, o = some b := by
  cases o with
  | none =>
    exact ⟨fun h => False.elim h, fun ⟨_, h⟩ => by cases h⟩
  | some b =>
    exact ⟨fun _ => ⟨b, rfl⟩, fun _ => True.intro⟩

/-- Exact correspondence between `o = some b` and the definedness and payload
    of `Option.toPartial o`. -/
theorem Option.eq_some_iff_toPartial {B : Type u} (o : Option B) (b : B) :
    o = some b ↔
      ∃ h : (Option.toPartial o).defined, (Option.toPartial o).val h = b := by
  cases o with
  | none =>
    constructor
    · intro h; cases h
    · intro ⟨h, _⟩; exact False.elim h
  | some b' =>
    constructor
    · intro h
      injection h with heq
      exact ⟨True.intro, heq⟩
    · intro ⟨_, heq⟩
      exact congrArg some heq

/-- Homomorphism law: `Option.toPartial` maps `Option.bind` to `Partial.bind`
    up to `Partial.Equiv`. -/
theorem Option.toPartial_bind {B₁ : Type u} {B₂ : Type v}
    (o : Option B₁) (f : B₁ → Option B₂) :
    Partial.Equiv
      (Option.toPartial (o.bind f))
      (Partial.bind (Option.toPartial o) (fun x => Option.toPartial (f x))) := by
  cases o with
  | none =>
    refine ⟨⟨fun h => False.elim h, fun ⟨h, _⟩ => False.elim h⟩, ?_⟩
    intro h _; exact False.elim h
  | some b =>
    dsimp [Option.toPartial, Partial.bind, Partial.pure]
    refine ⟨⟨fun h => ⟨True.intro, h⟩, fun ⟨_, h⟩ => h⟩, ?_⟩
    intro _ _
    rfl

/-- Round-trip identity on `Option B`: converting `o : Option B` to `Partial B`
    and back via `Partial.toOption` recovers `o`. -/
theorem Option.toOption_toPartial {B : Type u} (o : Option B)
    [inst : Decidable (Option.toPartial o).defined] :
    (Option.toPartial o).toOption = o := by
  cases o with
  | none =>
    cases inst with
    | isFalse _ => rfl
    | isTrue h => exact False.elim h
  | some b =>
    cases inst with
    | isFalse h => exact False.elim (h True.intro)
    | isTrue _ => rfl

/-- Round-trip equivalence on `Partial B` when `p.defined` is decidable:
    `Option.toPartial p.toOption` is structurally equivalent to `p`. -/
theorem Partial.toPartial_toOption {B : Type u} (p : Partial B)
    [inst : Decidable p.defined] :
    Partial.Equiv (Option.toPartial p.toOption) p := by
  cases inst with
  | isFalse hp =>
    dsimp [Partial.toOption, Option.toPartial, Partial.ub]
    refine ⟨⟨fun h => False.elim h, fun h => hp h⟩, ?_⟩
    intro h _
    exact False.elim h
  | isTrue hp =>
    dsimp [Partial.toOption, Option.toPartial, Partial.pure]
    refine ⟨⟨fun _ => hp, fun _ => True.intro⟩, ?_⟩
    intro _ _
    rfl

/-!
## 3. Design C: Dual Liftings of `Language.sem` to `Partial L.Prog`
-/

/-- The canonical domain of query-indexed partial behaviors over `Query` and
    `Out` (`Query → Partial (Out → Prop)`). -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Condition a behavior `b : Behavior Query Out` on a proposition `P : Prop`:
    at each query `q`, `Behavior.when P b` requires `(b q)` to be defined and
    satisfy `(b q).val` only when `P` holds (`defined := P ∧ (b q).defined`).
    When `¬ P`, `Behavior.when P b` evaluates to `Partial.ub` at every query. -/
def Behavior.when {Query Out : Type} (P : Prop) (b : Behavior Query Out) :
    Behavior Query Out :=
  fun q => {
    defined := P ∧ (b q).defined
    val := fun h => (b q).val h.2
  }

/-- Universal property of `Behavior.when`: refining `Behavior.when P b₂` is
    equivalent to refining `b₂` under the assumption `P`. -/
theorem le_when_iff {Query Out : Type} (P : Prop)
    (b₁ b₂ : Behavior Query Out) :
    b₁ ≤ Behavior.when P b₂ ↔ (P → b₁ ≤ b₂) := by
  constructor
  · intro hle hP q hq
    exact hle q ⟨hP, hq⟩
  · intro h q ⟨hP, hq⟩
    exact h hP q hq

/-- Whenever `P` holds, `Behavior.when P b` and `b` mutually refine each
    other. -/
theorem when_equiv_of_true {Query Out : Type} {P : Prop} (hP : P)
    (b : Behavior Query Out) :
    RefinesEquiv (Behavior.when P b) b := by
  constructor
  · intro q hq
    exact ⟨⟨hP, hq⟩, fun _ hout => hout⟩
  · intro q ⟨_, hq⟩
    exact ⟨hq, fun _ hout => hout⟩

/-- A language bundling a program type `Prog`, a query domain `Query`, an
    outcome domain `Out`, and a semantic function
    `sem : Prog → Behavior Query Out`. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- The behavior domain of a `Language` (`Behavior L.Query L.Out`). -/
abbrev Language.Behavior (L : Language) : Type :=
  PartialCompileAlgebra.Behavior L.Query L.Out

/-- Query-indexed specification on `L` with domain precondition
    `pre : L.Query → Prop` and outcome postcondition
    `post : L.Query → L.Out → Prop`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification on `L` (`L.SpecOn (fun _ => True) post`). -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `L` under query precondition
    `pre : L.Query → Prop` (`L.SpecOn pre (fun _ _ => True)`). -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`
    (`L.WellFormedOn (fun _ => True)`). -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Conjoining a program-level proposition `P` onto the precondition `pre` of
    `L.SpecOn` is definitionally equal to
    `Behavior.when P (L.SpecOn pre post)`. -/
theorem specOn_and_eq_when (L : Language) (P : Prop)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn (fun q => P ∧ pre q) post =
      Behavior.when P (L.SpecOn pre post) :=
  rfl

/-- Conjoining a program-level proposition `P` onto the precondition `pre` of
    `L.WellFormedOn` is definitionally equal to
    `Behavior.when P (L.WellFormedOn pre)`. -/
theorem wellFormedOn_and_eq_when (L : Language) (P : Prop)
    (pre : L.Query → Prop) :
    L.WellFormedOn (fun q => P ∧ pre q) =
      Behavior.when P (L.WellFormedOn pre) :=
  rfl

/-- **Lifting 1 (Angelic / Conditional-on-Compilation, $\bot$-on-rejection):**
    Lifts `L.sem` to a partial program `p? : Partial L.Prog` so that:
    - When `p?` is defined (`h : p?.defined`), `L.semIfCompiled p?` behaves as
      `L.sem (p?.val h)`.
    - When `p?` is rejected at compile time (`¬ p?.defined`),
      `L.semIfCompiled p?` has `defined = True` and empty outcome set
      (`Partial.bot`), because a program rejected at compile time never
      executes at runtime. -/
def Language.semIfCompiled (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => {
    defined := ∀ h : p?.defined, (L.sem (p?.val h) q).defined
    val := fun hdef o => ∃ h : p?.defined, (L.sem (p?.val h) q).val (hdef h) o
  }

/-- **Lifting 2 (Demonic / Total-Compilation Lifting, $\top$-on-rejection):**
    Lifts `L.sem` to a partial program `p? : Partial L.Prog` via `Partial.bind`
    at each query `q`:
    - When `p?` is defined (`h : p?.defined`), `L.semPartial p?` behaves as
      `L.sem (p?.val h)`.
    - When `p?` is rejected at compile time (`¬ p?.defined`), `L.semPartial p?`
      has `defined = False` (`Partial.ub`) at every query `q`, treating
      compile-time rejection demonically as failure. -/
def Language.semPartial (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => Partial.bind p? (fun p => L.sem p q)

/-- Fundamental universal property of `Language.semIfCompiled`:
    `L.semIfCompiled p?` refines `B` if and only if `L.sem (p?.val h)` refines
    `B` for every proof `h : p?.defined` that compilation succeeds. -/
theorem semIfCompiled_le_iff (L : Language) (p? : Partial L.Prog)
    (B : L.Behavior) :
    L.semIfCompiled p? ≤ B ↔ ∀ h : p?.defined, L.sem (p?.val h) ≤ B := by
  constructor
  · intro hle h q hBq
    cases hle q hBq with
    | intro hdef hval =>
      exact ⟨hdef h, fun o ho => hval o ⟨h, ho⟩⟩
  · intro h q hBq
    exact ⟨fun hp => (h hp q hBq).1, fun o ⟨hp, ho⟩ => (h hp q hBq).2 o ho⟩

/-- On an uncompilable program (`Partial.ub`), `L.semIfCompiled` refines the
    bottom behavior `fun _ => Partial.bot` (and hence refines every behavior
    `B`). -/
theorem semIfCompiled_ub_le_bot (L : Language) :
    L.semIfCompiled Partial.ub ≤ (fun _ => Partial.bot) :=
  fun _ _ => ⟨fun h => False.elim h, fun _ ⟨h, _⟩ => False.elim h⟩

/-- On an unconditionally defined program (`Partial.pure p`),
    `L.semIfCompiled (Partial.pure p)` is refinement-equivalent to `L.sem p`. -/
theorem semIfCompiled_pure_equiv (L : Language) (p : L.Prog) :
    RefinesEquiv (L.semIfCompiled (Partial.pure p)) (L.sem p) := by
  constructor
  · exact (semIfCompiled_le_iff L (Partial.pure p) (L.sem p)).mpr
      (fun _ => Preorder.le_refl (L.sem p))
  · intro q hdef
    exact ⟨hdef True.intro, fun o ho => ⟨True.intro, ho⟩⟩

/-- Fundamental universal property of `Language.semPartial`:
    `L.semPartial p?` refines `B` if and only if:
    1. `p?.defined` holds whenever `B` is defined at any query `q`, and
    2. `L.sem (p?.val h) ≤ B` holds for every `h : p?.defined`. -/
theorem semPartial_le_iff (L : Language) (p? : Partial L.Prog)
    (B : L.Behavior) :
    L.semPartial p? ≤ B ↔
      (∀ q, (B q).defined → p?.defined) ∧
      (∀ h : p?.defined, L.sem (p?.val h) ≤ B) := by
  constructor
  · intro hle
    refine ⟨?_, ?_⟩
    · intro q hBq
      exact (hle q hBq).1.1
    · intro h q hBq
      cases hle q hBq with
      | intro hdef hval =>
        exact ⟨hdef.2, hval⟩
  · intro ⟨himp, hsem⟩ q hBq
    have hp : p?.defined := himp q hBq
    cases hsem hp q hBq with
    | intro hq hval =>
      exact ⟨⟨hp, hq⟩, hval⟩

/-- Corollary: if `L.semPartial p? ≤ B` and `B` is defined at some query `q`,
    then `p?` must be defined (`p?.defined`). -/
theorem semPartial_le_imp_defined {L : Language} {p? : Partial L.Prog}
    {B : L.Behavior} (hle : L.semPartial p? ≤ B)
    {q : L.Query} (hBq : (B q).defined) :
    p?.defined :=
  (semPartial_le_iff L p? B).mp hle |>.1 q hBq

/-- When `B` is defined at some query `q`, `L.semPartial p? ≤ B` is equivalent
    to `∃ h : p?.defined, L.sem (p?.val h) ≤ B`. -/
theorem semPartial_le_iff_exists_of_defined {L : Language}
    (p? : Partial L.Prog) (B : L.Behavior)
    {q₀ : L.Query} (hBq₀ : (B q₀).defined) :
    L.semPartial p? ≤ B ↔ ∃ h : p?.defined, L.sem (p?.val h) ≤ B := by
  constructor
  · intro hle
    have hp : p?.defined := semPartial_le_imp_defined hle hBq₀
    exact ⟨hp, (semPartial_le_iff L p? B).mp hle |>.2 hp⟩
  · intro ⟨hp, hsem⟩
    exact (semPartial_le_iff L p? B).mpr ⟨fun _ _ => hp, fun _ => hsem⟩

/-- Duality ordering: `L.semIfCompiled p?` always refines `L.semPartial p?`. -/
theorem semIfCompiled_le_semPartial (L : Language) (p? : Partial L.Prog) :
    L.semIfCompiled p? ≤ L.semPartial p? := by
  intro q ⟨hp, hq⟩
  exact ⟨fun _ => hq, fun o ⟨_, ho⟩ => ho⟩

/-- When `p?` is defined (`h : p?.defined`), `L.semIfCompiled p?` and
    `L.semPartial p?` mutually refine each other (and `L.sem (p?.val h)`). -/
theorem semPartial_le_semIfCompiled_of_defined (L : Language)
    {p? : Partial L.Prog} (h : p?.defined) :
    L.semPartial p? ≤ L.semIfCompiled p? := by
  intro q hdef
  exact ⟨⟨h, hdef h⟩, fun o ho => ⟨h, ho⟩⟩

/-!
## 4. Partial `Compiler`, `SoundOn`, and the Three Modes of `Compiler.Verified`
-/

/-- Compilation (refinement) pass from `L_src` to `L_tgt` for a concrete target
    program `t : L_tgt.Prog`. -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Conditional compilation pass from `L_src` to `L_tgt` for a partial target
    program `t? : Partial L_tgt.Prog`: whenever `t?` is defined
    (`h : t?.defined`), `t?.val h` compiles `s`. -/
def CompilesPartial (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t? : Partial L_tgt.Prog) : Prop :=
  ∀ h : t?.defined, Compiles L_src L_tgt π_c s (t?.val h)

/-- `CompilesPartial` is equivalent to the single refinement inequality
    `L_tgt.semIfCompiled t? ≤ π_c (L_src.sem s)`. -/
theorem compilesPartial_iff_semIfCompiled_le
    (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t? : Partial L_tgt.Prog) :
    CompilesPartial L_src L_tgt π_c s t? ↔
      L_tgt.semIfCompiled t? ≤ π_c (L_src.sem s) :=
  (semIfCompiled_le_iff L_tgt t? (π_c (L_src.sem s))).symm

/-- Verification (abstraction) pass from `L_src` to verifier language `L_v`. -/
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- A compiler lowering programs from `L_src` to `Partial L_tgt.Prog` with
    behavior mapping `π : L_src.Behavior → L_tgt.Behavior`. -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → Partial L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Construct a `Compiler` from a total compilation function
    `compile : L_src.Prog → L_tgt.Prog` via `Partial.pure`. -/
def Compiler.ofTotal {L_src L_tgt : Language}
    (compile : L_src.Prog → L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior) : Compiler L_src L_tgt where
  compile s := Partial.pure (compile s)
  π := π

/-- Construct a `Compiler` from a computable `Option`-returning compilation
    function `compile : L_src.Prog → Option L_tgt.Prog` via
    `Option.toPartial`. -/
def Compiler.ofOption {L_src L_tgt : Language}
    (compile : L_src.Prog → Option L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior) : Compiler L_src L_tgt where
  compile s := Option.toPartial (compile s)
  π := π

/-- Soundness of partial compiler `C` on an individual source program `s`:
    `C.π` is monotone and whenever `C.compile s` is defined
    (`h : (C.compile s).defined`), `(C.compile s).val h` refines `s` under
    `C.π`. -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧
  ∀ h : (C.compile s).defined, Compiles L_src L_tgt C.π s ((C.compile s).val h)

/-- Conditional soundness variant in which `Monotone C.π` is also scoped under
    `∀ h : (C.compile s).defined`. Used to compare composition of `SoundOn`
    when `Monotone C₂.π` is only supplied conditionally on compilation of the
    first stage succeeding. -/
def Compiler.SoundOnWhenCompiled {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  ∀ h : (C.compile s).defined,
    Monotone C.π ∧ Compiles L_src L_tgt C.π s ((C.compile s).val h)

theorem Compiler.SoundOn.to_soundOnWhenCompiled {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt} {s : L_src.Prog}
    (h : C.SoundOn s) : C.SoundOnWhenCompiled s :=
  fun hdef => ⟨h.1, h.2 hdef⟩

theorem Compiler.soundOn_iff_semIfCompiled {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) :
    C.SoundOn s ↔
      Monotone C.π ∧ L_tgt.semIfCompiled (C.compile s) ≤ C.π (L_src.sem s) :=
  ⟨fun ⟨hm, hc⟩ => ⟨hm, (semIfCompiled_le_iff L_tgt (C.compile s) _).mpr hc⟩,
   fun ⟨hm, hc⟩ => ⟨hm, (semIfCompiled_le_iff L_tgt (C.compile s) _).mp hc⟩⟩

/-- **Mode 1 (`Compiler.Verified` / `VerifiedIfCompiled` — Unconditional Source,
    Conditional Target):**
    1. `s` unconditionally satisfies `spec` in `L_src` (`L_src.sem s ≤ spec`),
       and
    2. Whenever compilation of `s` succeeds (`h : (C.compile s).defined`), the
       compiled target `(C.compile s).val h` compiles `s` and satisfies
       `C.π spec`. -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  ∀ h : (C.compile s).defined,
    Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
    L_tgt.sem ((C.compile s).val h) ≤ C.π spec

abbrev Compiler.VerifiedIfCompiled {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  C.Verified s spec

/-- **Mode 2 (`Compiler.VerifiedWhenCompiled` — Both Source and Target
    Conditional on Compilation Succeeding):**
    Whenever compilation of `s` succeeds (`h : (C.compile s).defined`):
    1. `s` satisfies `spec` in `L_src` (`L_src.sem s ≤ spec`),
    2. `(C.compile s).val h` compiles `s`, and
    3. `(C.compile s).val h` satisfies `C.π spec`. -/
def Compiler.VerifiedWhenCompiled {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  ∀ h : (C.compile s).defined,
    L_src.sem s ≤ spec ∧
    Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
    L_tgt.sem ((C.compile s).val h) ≤ C.π spec

/-- **Mode 3 (`Compiler.VerifiedTotal` — Proving Compilation Succeeds and
    Verifies):**
    Compilation of `s` succeeds (`(C.compile s).defined`) and `s` satisfies
    `C.Verified s spec`. -/
def Compiler.VerifiedTotal {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  (C.compile s).defined ∧ C.Verified s spec

/-- Mode 1 (`C.Verified`) is equivalent to the 3-inequality conjunction using
    `L_tgt.semIfCompiled`. -/
theorem Compiler.verified_iff_semIfCompiled {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) :
    C.Verified s spec ↔
      L_src.sem s ≤ spec ∧
      L_tgt.semIfCompiled (C.compile s) ≤ C.π (L_src.sem s) ∧
      L_tgt.semIfCompiled (C.compile s) ≤ C.π spec := by
  constructor
  · intro ⟨hsrc, hcomp⟩
    refine ⟨hsrc, ?_, ?_⟩
    · exact (semIfCompiled_le_iff L_tgt (C.compile s) _).mpr (fun h => (hcomp h).1)
    · exact (semIfCompiled_le_iff L_tgt (C.compile s) _).mpr (fun h => (hcomp h).2)
  · intro ⟨hsrc, hcomp, hspec⟩
    refine ⟨hsrc, fun h => ⟨?_, ?_⟩⟩
    · exact (semIfCompiled_le_iff L_tgt (C.compile s) _).mp hcomp h
    · exact (semIfCompiled_le_iff L_tgt (C.compile s) _).mp hspec h

/-- Mode 3 implies Mode 1. -/
theorem Compiler.VerifiedTotal.to_verified {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt} {s : L_src.Prog} {spec : L_src.Behavior}
    (h : C.VerifiedTotal s spec) : C.Verified s spec :=
  h.2

/-- Mode 1 implies Mode 2. -/
theorem Compiler.Verified.to_verifiedWhenCompiled {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt} {s : L_src.Prog} {spec : L_src.Behavior}
    (h : C.Verified s spec) : C.VerifiedWhenCompiled s spec :=
  fun hdef => ⟨h.1, (h.2 hdef).1, (h.2 hdef).2⟩

/-- Mode 1 is equivalent to unconditional source correctness
    (`L_src.sem s ≤ spec`) conjoined with Mode 2
    (`C.VerifiedWhenCompiled s spec`). -/
theorem Compiler.verified_iff_src_and_verifiedWhenCompiled
    {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) :
    C.Verified s spec ↔
      L_src.sem s ≤ spec ∧ C.VerifiedWhenCompiled s spec :=
  ⟨fun h => ⟨h.1, h.to_verifiedWhenCompiled⟩,
   fun ⟨hsrc, hwhen⟩ => ⟨hsrc, fun hdef => ⟨(hwhen hdef).2.1, (hwhen hdef).2.2⟩⟩⟩

/-- Mode 3 (`VerifiedTotal`) is equivalent to `(C.compile s).defined` conjoined
    with Mode 2 (`VerifiedWhenCompiled`): once `(C.compile s).defined` is
    established, Mode 1 and Mode 2 coincide. -/
theorem Compiler.verifiedTotal_iff_defined_and_verifiedWhenCompiled
    {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) :
    C.VerifiedTotal s spec ↔
      (C.compile s).defined ∧ C.VerifiedWhenCompiled s spec := by
  constructor
  · intro ⟨hdef, hver⟩
    exact ⟨hdef, hver.to_verifiedWhenCompiled⟩
  · intro ⟨hdef, hwhen⟩
    exact ⟨hdef, (hwhen hdef).1, fun h => ⟨(hwhen h).2.1, (hwhen h).2.2⟩⟩

/-- Mode 3 (`VerifiedTotal`) is equivalent to the existential statement
    `∃ h : (C.compile s).defined, L_src.sem s ≤ spec ∧ Compiles ... ∧`
    `L_tgt.sem ... ≤ C.π spec`. -/
theorem Compiler.verifiedTotal_iff_exists
    {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) :
    C.VerifiedTotal s spec ↔
      ∃ h : (C.compile s).defined,
        L_src.sem s ≤ spec ∧
        Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
        L_tgt.sem ((C.compile s).val h) ≤ C.π spec := by
  constructor
  · intro ⟨hdef, hsrc, hcomp⟩
    exact ⟨hdef, hsrc, (hcomp hdef).1, (hcomp hdef).2⟩
  · intro ⟨hdef, hsrc, hcomp, hspec⟩
    exact ⟨hdef, hsrc, fun _ => ⟨hcomp, hspec⟩⟩

/-- Mode 3 (`VerifiedTotal`) is also equivalent to the 3-inequality formulation
    using demonic `L_tgt.semPartial` together with `(C.compile s).defined`. -/
theorem Compiler.verifiedTotal_iff_semPartial
    {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) :
    C.VerifiedTotal s spec ↔
      (C.compile s).defined ∧
      L_src.sem s ≤ spec ∧
      L_tgt.semPartial (C.compile s) ≤ C.π (L_src.sem s) ∧
      L_tgt.semPartial (C.compile s) ≤ C.π spec := by
  constructor
  · intro ⟨hdef, hsrc, hcomp⟩
    refine ⟨hdef, hsrc, ?_, ?_⟩
    · exact (semPartial_le_iff L_tgt (C.compile s) _).mpr
        ⟨fun _ _ => hdef, fun h => (hcomp h).1⟩
    · exact (semPartial_le_iff L_tgt (C.compile s) _).mpr
        ⟨fun _ _ => hdef, fun h => (hcomp h).2⟩
  · intro ⟨hdef, hsrc, hcomp, hspec⟩
    refine ⟨hdef, hsrc, fun h => ⟨?_, ?_⟩⟩
    · exact (semPartial_le_iff L_tgt (C.compile s) _).mp hcomp |>.2 h
    · exact (semPartial_le_iff L_tgt (C.compile s) _).mp hspec |>.2 h

/-- **Unification Theorem (`verifiedWhenCompiled_iff_verified_when`):**
    Whenever `C.π` is monotone, Mode 2 (`C.VerifiedWhenCompiled s spec`) is
    logically equivalent to Mode 1 (`C.Verified`) instantiated at the
    compilation-conditioned specification
    `Behavior.when (C.compile s).defined spec`.

    Consequently, `Trusted/Refinement.lean` does not need a separate
    `VerifiedWhenCompiled` primitive: Mode 1 (`C.Verified`) expresses both
    unconditional source verification (`spec`) and compilation-conditioned
    verification (`Behavior.when (C.compile s).defined spec` or
    `L_src.SpecOn (fun q => (C.compile s).defined ∧ pre q) post`). -/
theorem Compiler.verifiedWhenCompiled_iff_verified_when
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt} (h_mono : Monotone C.π)
    (s : L_src.Prog) (spec : L_src.Behavior) :
    C.VerifiedWhenCompiled s spec ↔
      C.Verified s (Behavior.when (C.compile s).defined spec) := by
  constructor
  · intro hwhen
    refine ⟨(le_when_iff (C.compile s).defined (L_src.sem s) spec).mpr (fun hdef => (hwhen hdef).1), ?_⟩
    intro hdef
    have h_eq := when_equiv_of_true hdef spec
    exact ⟨(hwhen hdef).2.1,
      Preorder.le_trans (hwhen hdef).2.2 (h_mono h_eq.2)⟩
  · intro ⟨hsrc, hcomp⟩ hdef
    have h_eq := when_equiv_of_true hdef spec
    exact ⟨(le_when_iff (C.compile s).defined (L_src.sem s) spec).mp hsrc hdef,
      (hcomp hdef).1,
      Preorder.le_trans (hcomp hdef).2 (h_mono h_eq.1)⟩

/-!
## 5. Discriminating Canaries: Mode 2 Vacuity Hazard vs. PME Conditioning
-/

/-- Minimal test language with two programs (`safeProg` and `ubProg`) and a
    single `Unit` query/outcome. -/
inductive CanaryProg where
  | safeProg
  | ubProg

def CanaryLang : Language where
  Prog := CanaryProg
  Query := Unit
  Out := Unit
  sem
    | .safeProg, _ => Partial.pure (fun _ => True)
    | .ubProg, _ => Partial.ub

/-- A partial compiler on `CanaryLang` that accepts `safeProg` and rejects
    `ubProg` at compile time (`defined := False`). -/
def rejectingCompiler : Compiler CanaryLang CanaryLang where
  compile
    | .safeProg => Partial.pure .safeProg
    | .ubProg => Partial.ub
  π b := b

/-- **Canary 1A (Mode 2 Vacuity on Rejected UB):**
    Because `(rejectingCompiler.compile .ubProg).defined` is `False`, Mode 2
    (`VerifiedWhenCompiled`) holds vacuously on `.ubProg` even for
    `CanaryLang.WellFormed`. If a compiler model erroneously assigns
    `defined = False` to a program with runtime UB, unguarded Mode 2 silently
    passes. -/
theorem canary_mode2_vacuous_on_rejected_ub :
    rejectingCompiler.VerifiedWhenCompiled .ubProg CanaryLang.WellFormed :=
  fun h => False.elim h

/-- **Canary 1B (Mode 1 Rejects Source UB Regardless of Compiler Partiality):**
    Under Mode 1 (`Compiler.Verified`), `.ubProg` is still rejected against
    `CanaryLang.WellFormed` even though `rejectingCompiler.compile .ubProg` is
    undefined (`Partial.ub`), because `L_src.sem s ≤ spec` is checked outside
    `∀ h : (C.compile s).defined`. -/
theorem canary_mode1_rejects_source_ub_even_when_uncompilable :
    ¬ rejectingCompiler.Verified .ubProg CanaryLang.WellFormed := by
  intro ⟨hsrc, _⟩
  exact (hsrc () True.intro).1

/-- **Canary 1C (Mode 3 Rejects Uncompilable Programs):**
    Under Mode 3 (`Compiler.VerifiedTotal`), `.ubProg` is rejected both because
    it fails to compile and because it exhibits source UB. -/
theorem canary_mode3_rejects_uncompilable :
    ¬ rejectingCompiler.VerifiedTotal .ubProg CanaryLang.WellFormed :=
  fun ⟨hdef, _⟩ => hdef

/-- Parameterized PME canary language: program `n : Nat` represents a generic
    function `fn first_elem<const N: usize>()` whose runtime execution is
    well-defined if and only if `N > 0` (`0 < n`), and whose
    post-monomorphization check (`const { assert!(N > 0); }`) succeeds at
    compile time if and only if `0 < n`. -/
abbrev PmeLang : Language where
  Prog := Nat
  Query := Unit
  Out := Nat
  sem n _ := {
    defined := 0 < n
    val := fun _ out => out = n
  }

/-- Compiler for `PmeLang` whose compilation succeeds (`defined := 0 < n`) if
    and only if the post-monomorphization check `0 < n` passes. -/
abbrev pmeCompiler : Compiler PmeLang PmeLang where
  compile n := {
    defined := 0 < n
    val := fun _ => n
  }
  π b := b

theorem pmeCompiler_soundOn (n : Nat) : pmeCompiler.SoundOn n :=
  ⟨monotone_id, fun _ => Preorder.le_refl (PmeLang.sem n)⟩

/-- **Canary 2A (PME Satisfaction across All `n : Nat`):**
    For every monomorphization `n : Nat`, `n` satisfies `pmeCompiler.Verified`
    under the PME-guarded specification
    `PmeLang.WellFormedOn (fun _ => 0 < n)` (and equivalently satisfies
    `pmeCompiler.VerifiedWhenCompiled n PmeLang.WellFormed`). -/
theorem canary_pme_verified_with_pme_pre (n : Nat) :
    pmeCompiler.Verified n (PmeLang.WellFormedOn (fun _ => 0 < n)) := by
  refine ⟨fun _ hpos => ⟨hpos, fun _ _ => True.intro⟩, ?_⟩
  intro hpos
  exact ⟨Preorder.le_refl _, fun _ _ => ⟨hpos, fun _ _ => True.intro⟩⟩

theorem canary_pme_verifiedWhenCompiled (n : Nat) :
    pmeCompiler.VerifiedWhenCompiled n PmeLang.WellFormed :=
  (Compiler.verifiedWhenCompiled_iff_verified_when monotone_id n PmeLang.WellFormed).mpr
    (by
      refine ⟨fun _ ⟨hpos, _⟩ => ⟨hpos, fun _ _ => True.intro⟩, ?_⟩
      intro hpos
      exact ⟨Preorder.le_refl _, fun _ ⟨_, _⟩ => ⟨hpos, fun _ _ => True.intro⟩⟩)

/-- **Canary 2B (Invalid Monomorphization `n = 0` Refutes `VerifiedTotal`):**
    At `n = 0`, the PME fails (`¬ (pmeCompiler.compile 0).defined`), so
    `VerifiedTotal 0 PmeLang.WellFormed` is refuted. -/
theorem canary_pme_zero_not_verifiedTotal :
    ¬ pmeCompiler.VerifiedTotal (0 : Nat) PmeLang.WellFormed :=
  fun ⟨hpos, _⟩ => Nat.lt_irrefl 0 hpos

/-- **Canary 2C (Valid Monomorphization `n = k + 1` Satisfies
    `VerifiedTotal`):**
    At `n = k + 1`, the PME succeeds (`0 < k + 1`) and `VerifiedTotal` holds
    for unconditional `PmeLang.WellFormed`. -/
theorem canary_pme_succ_verifiedTotal (k : Nat) :
    pmeCompiler.VerifiedTotal (k + 1) PmeLang.WellFormed := by
  have hpos : 0 < k + 1 := Nat.zero_lt_succ k
  refine ⟨hpos, ?_, ?_⟩
  · intro _ _
    exact ⟨hpos, fun _ _ => True.intro⟩
  · intro _
    exact ⟨Preorder.le_refl _, fun _ _ => ⟨hpos, fun _ _ => True.intro⟩⟩

/-!
## 6. Pass Composition (`Compiler.comp`, `pass_trans`, `verify_through_passes`,
   `Compiler.Verified.mono`)
-/

/-- Sequential composition of two partial compilers `C₁ : Compiler L₁ L₂` and
    `C₂ : Compiler L₂ L₃` via `Partial.bind`. -/
def Compiler.comp {L₁ L₂ L₃ : Language}
    (C₁ : Compiler L₁ L₂) (C₂ : Compiler L₂ L₃) : Compiler L₁ L₃ where
  compile s := Partial.bind (C₁.compile s) C₂.compile
  π b := C₂.π (C₁.π b)

/-- Transitive composition of two pass refinements (`Compiles` or
    `Abstracts`). -/
theorem pass_trans
    {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    [Preorder B₁] [Preorder B₂] [Preorder B₃]
    {π₂ : B₁ → B₂} {π₁ : B₂ → B₃}
    (h_mono₁ : Monotone π₁)
    {b₁ : B₁} {b₂ : B₂} {b₃ : B₃}
    (h₂₃ : b₃ ≤ π₁ b₂)
    (h₁₂ : b₂ ≤ π₂ b₁) :
    b₃ ≤ π₁ (π₂ b₁) :=
  Preorder.le_trans h₂₃ (h_mono₁ h₁₂)

/-- Pipeline-ordered composition of two concrete compilation passes. -/
theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono₂ : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  pass_trans h_mono₂ h₂₃ h₁₂

/-- Pipeline-ordered composition of two partial compilation passes via
    `Partial.bind`. -/
theorem CompilesPartial.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂? : Partial L₂.Prog} {f₂ : L₂.Prog → Partial L₃.Prog}
    (h₁₂ : CompilesPartial L₁ L₂ π₁ p₁ p₂?)
    (h₂₃ : ∀ h : p₂?.defined, CompilesPartial L₂ L₃ π₂ (p₂?.val h) (f₂ (p₂?.val h)))
    (h_mono₂ : Monotone π₂) :
    CompilesPartial L₁ L₃ (fun b => π₂ (π₁ b)) p₁ (Partial.bind p₂? f₂) :=
  fun ⟨h₁, h₂⟩ => Compiles.comp (h₁₂ h₁) (h₂₃ h₁ h₂) h_mono₂

/-- Pipeline-ordered composition of two verification abstraction passes. -/
theorem Abstracts.comp
    {L₂ L₁ L_src : Language}
    {π₂ : L₂.Behavior → L₁.Behavior} {π₁ : L₁.Behavior → L_src.Behavior}
    {v₂ : L₂.Prog} {v₁ : L₁.Prog} {s : L_src.Prog}
    (h₁ : Abstracts L₁ L_src π₁ v₁ s)
    (h₂ : Abstracts L₂ L₁ π₂ v₂ v₁)
    (h_mono₁ : Monotone π₁) :
    Abstracts L₂ L_src (fun b => π₁ (π₂ b)) v₂ s :=
  pass_trans h_mono₁ h₁ h₂

/-- Composition of `Compiler.SoundOnWhenCompiled`: if `C₁` is sound when
    compiled on `s` and `C₂` is sound when compiled on `(C₁.compile s).val h`
    for every `h : (C₁.compile s).defined`, then `C₁.comp C₂` is sound when
    compiled on `s` (requiring no unconditional `Monotone C₂.π` hypothesis when
    `C₁.compile s` is undefined). -/
theorem Compiler.SoundOnWhenCompiled.comp
    {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
    {s : L₁.Prog}
    (h₁ : C₁.SoundOnWhenCompiled s)
    (h₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOnWhenCompiled ((C₁.compile s).val h)) :
    (C₁.comp C₂).SoundOnWhenCompiled s := by
  intro ⟨hdef₁, hdef₂⟩
  have ⟨hmono₁, hcomp₁⟩ := h₁ hdef₁
  have ⟨hmono₂, hcomp₂⟩ := h₂ hdef₁ hdef₂
  exact ⟨monotone_comp (B := L₂.Behavior) hmono₂ hmono₁,
    Compiles.comp (L₂ := L₂) hcomp₁ hcomp₂ hmono₂⟩

/-- Composition of `Compiler.SoundOn` given `Monotone C₂.π`. -/
theorem Compiler.SoundOn.comp
    {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
    {s : L₁.Prog}
    (h₁ : C₁.SoundOn s)
    (h_mono₂ : Monotone C₂.π)
    (h₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₁.comp C₂).SoundOn s :=
  ⟨monotone_comp (B := L₂.Behavior) h_mono₂ h₁.1,
   fun ⟨hdef₁, hdef₂⟩ =>
     Compiles.comp (L₂ := L₂) (h₁.2 hdef₁) ((h₂ hdef₁).2 hdef₂) h_mono₂⟩

/-- Composition of `Compiler.SoundOn` when `(C₁.compile s).defined` holds
    (extracting `Monotone C₂.π` directly from `h₂ hdef₁`). -/
theorem Compiler.SoundOn.comp_of_defined
    {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
    {s : L₁.Prog}
    (h₁ : C₁.SoundOn s)
    (hdef₁ : (C₁.compile s).defined)
    (h₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₁.comp C₂).SoundOn s :=
  Compiler.SoundOn.comp h₁ (h₂ hdef₁).1 h₂

/-- Discharge `C.Verified s spec` (Mode 1) directly from `C.SoundOn s` and a
    source-level refinement proof `L_src.sem s ≤ spec`.
    Notice that the theorem signature is identical to the total-compiler
    `Compiler.SoundOn.verify` in `theory/Anneal/Refinement.lean`. -/
theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, fun h => ⟨h_comp.2 h, Preorder.le_trans (h_comp.2 h) (h_comp.1 h_src)⟩⟩

/-- Discharge `C.Verified s spec` (Mode 1) from the weaker
    `C.SoundOnWhenCompiled s` and `L_src.sem s ≤ spec`. -/
theorem Compiler.SoundOnWhenCompiled.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOnWhenCompiled s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, fun h => ⟨(h_comp h).2, Preorder.le_trans (h_comp h).2 ((h_comp h).1 h_src)⟩⟩

/-- Discharge `C.VerifiedWhenCompiled s spec` (Mode 2) from `C.SoundOn s` and a
    compilation-conditioned source refinement proof
    `(C.compile s).defined → L_src.sem s ≤ spec`. -/
theorem Compiler.SoundOn.verifyWhenCompiled
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : (C.compile s).defined → L_src.sem s ≤ spec) :
    C.VerifiedWhenCompiled s spec :=
  fun h => ⟨h_src h, h_comp.2 h, Preorder.le_trans (h_comp.2 h) (h_comp.1 (h_src h))⟩

/-- Discharge `C.VerifiedTotal s spec` (Mode 3) from `(C.compile s).defined`,
    `C.SoundOn s`, and `L_src.sem s ≤ spec`. -/
theorem Compiler.SoundOn.verifyTotal
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_def : (C.compile s).defined)
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.VerifiedTotal s spec :=
  ⟨h_def, Compiler.SoundOn.verify h_comp h_src⟩

/-- Multi-stage verification composition (`Compiler.Verified.comp`):
    If `s` is verified under `C₁` (`C₁.Verified s spec`) and `C₂` is sound on
    `(C₁.compile s).val h` whenever `C₁.compile s` is defined, then `s` is
    verified under the composite compiler `C₁.comp C₂`—with no extra
    monotonicity side condition required when `C₁.compile s` is undefined. -/
theorem Compiler.Verified.comp
    {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
    {s : L₁.Prog} {spec : L₁.Behavior}
    (h_ver₁ : C₁.Verified s spec)
    (h_sound₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₁.comp C₂).Verified s spec := by
  refine ⟨h_ver₁.1, ?_⟩
  intro ⟨hdef₁, hdef₂⟩
  have ⟨hcomp₁, hspec₁⟩ := h_ver₁.2 hdef₁
  have ⟨hmono₂, hcomp₂⟩ := h_sound₂ hdef₁
  exact ⟨Compiles.comp (L₂ := L₂) hcomp₁ (hcomp₂ hdef₂) hmono₂,
    Preorder.le_trans (hcomp₂ hdef₂) (hmono₂ hspec₁)⟩

/-- Multi-stage verification composition for Mode 2
    (`VerifiedWhenCompiled.comp`). -/
theorem Compiler.VerifiedWhenCompiled.comp
    {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
    {s : L₁.Prog} {spec : L₁.Behavior}
    (h_ver₁ : C₁.VerifiedWhenCompiled s spec)
    (h_sound₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₁.comp C₂).VerifiedWhenCompiled s spec := by
  intro ⟨hdef₁, hdef₂⟩
  have ⟨hsrc, hcomp₁, hspec₁⟩ := h_ver₁ hdef₁
  have ⟨hmono₂, hcomp₂⟩ := h_sound₂ hdef₁
  exact ⟨hsrc,
    Compiles.comp (L₂ := L₂) hcomp₁ (hcomp₂ hdef₂) hmono₂,
    Preorder.le_trans (hcomp₂ hdef₂) (hmono₂ hspec₁)⟩

/-- Multi-stage verification composition for Mode 3 (`VerifiedTotal.comp`). -/
theorem Compiler.VerifiedTotal.comp
    {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
    {s : L₁.Prog} {spec : L₁.Behavior}
    (h_ver₁ : C₁.VerifiedTotal s spec)
    (h_def₂ : (C₂.compile ((C₁.compile s).val h_ver₁.1)).defined)
    (h_sound₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₁.comp C₂).VerifiedTotal s spec :=
  ⟨⟨h_ver₁.1, h_def₂⟩, Compiler.Verified.comp h_ver₁.2 h_sound₂⟩

/-- Y-diagram bridge theorem (`verify_through_passes`) for partial compilers:
    discharges `C.Verified s (π_v spec)` from:
    1. A proof on the verifier's model (`L_v.sem v ≤ spec`),
    2. An `Abstracts` pass relating `v` and `s` under `π_v`,
    3. Monotonicity of `π_v`, and
    4. Partial compiler soundness on `s` (`C.SoundOn s`).
    Notice that the statement and proof are identical to the total-compiler
    version in `theory/Anneal/Refinement.lean`. -/
theorem verify_through_passes
    {L_v L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {π_v : L_v.Behavior → L_src.Behavior} {spec : L_v.Behavior}
    {v : L_v.Prog} {s : L_src.Prog}
    (h_proof : L_v.sem v ≤ spec)
    (h_abs : Abstracts L_v L_src π_v v s)
    (h_mono_v : Monotone π_v)
    (h_comp : C.SoundOn s) :
    C.Verified s (π_v spec) :=
  Compiler.SoundOn.verify h_comp (Preorder.le_trans h_abs (h_mono_v h_proof))

/-- Y-diagram bridge theorem for Mode 2 (`verifyWhenCompiled_through_passes`):
    allows both the verifier proof `L_v.sem v ≤ spec` and/or the abstraction
    proof `Abstracts L_v L_src π_v v s` to depend on `(C.compile s).defined`. -/
theorem verifyWhenCompiled_through_passes
    {L_v L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {π_v : L_v.Behavior → L_src.Behavior} {spec : L_v.Behavior}
    {v : L_v.Prog} {s : L_src.Prog}
    (h_proof : (C.compile s).defined → L_v.sem v ≤ spec)
    (h_abs : (C.compile s).defined → Abstracts L_v L_src π_v v s)
    (h_mono_v : Monotone π_v)
    (h_comp : C.SoundOn s) :
    C.VerifiedWhenCompiled s (π_v spec) :=
  Compiler.SoundOn.verifyWhenCompiled h_comp
    (fun hdef => Preorder.le_trans (h_abs hdef) (h_mono_v (h_proof hdef)))

/-- Monotonicity of `Compiler.Verified` (Mode 1) in the specification argument.
    Statement is identical to `Compiler.Verified.mono` in
    `theory/Anneal/Refinement.lean`. -/
theorem Compiler.Verified.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.Verified s spec₁)
    (h_le : spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.Verified s spec₂ :=
  ⟨Preorder.le_trans h_ver.1 h_le,
   fun h => ⟨(h_ver.2 h).1, Preorder.le_trans (h_ver.2 h).2 (h_mono h_le)⟩⟩

/-- Monotonicity of `Compiler.VerifiedWhenCompiled` (Mode 2) in the
    specification argument. -/
theorem Compiler.VerifiedWhenCompiled.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.VerifiedWhenCompiled s spec₁)
    (h_le : (C.compile s).defined → spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.VerifiedWhenCompiled s spec₂ :=
  fun h => ⟨Preorder.le_trans (h_ver h).1 (h_le h),
    (h_ver h).2.1,
    Preorder.le_trans (h_ver h).2.2 (h_mono (h_le h))⟩

/-- Monotonicity of `Compiler.VerifiedTotal` (Mode 3) in the specification
    argument. -/
theorem Compiler.VerifiedTotal.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.VerifiedTotal s spec₁)
    (h_le : spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.VerifiedTotal s spec₂ :=
  ⟨h_ver.1, Compiler.Verified.mono h_ver.2 h_le h_mono⟩

/-- An assumption recorded in a verification unit's Trusted Computing Base. -/
class TrustedAssumption (A : Type) where
  meaning : A → Prop

/-- A policy governing which trusted assumptions of type `A` are permitted. -/
structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

/-- Conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Combine a proof of `C.Verified s spec` with `spec ≤ L_src.WellFormedOn pre`
    to discharge
    `AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s))`
    in `VerificationResultOn`. Statement and proof are identical to
    `theory/Anneal/Refinement.lean`. -/
theorem Compiler.Verified.with_wellFormedOn
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {pre : L_src.Query → Prop} {spec : L_src.Behavior}
    (h_ver : C.Verified s spec)
    (h_wf : spec ≤ L_src.WellFormedOn pre)
    (h_mono : Monotone C.π) :
    AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s)) :=
  ⟨Compiler.Verified.mono h_ver h_wf h_mono, h_ver, True.intro⟩

/-- Top-level verification envelope for a source program `prog : L_src.Prog`,
    safety precondition `pre : L_src.Query → Prop`, and additional
    specifications `specs : List L_src.Behavior` under partial compiler
    `C : Compiler L_src L_tgt`. -/
def VerificationResultOn
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List L_src.Behavior) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog)))

/-- Top-level verification envelope with unconditional baseline `WellFormed`
    (`pre := fun _ => True`). -/
abbrev VerificationResult
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (specs : List L_src.Behavior := []) : Prop :=
  VerificationResultOn C policy assumptions prog (fun _ => True) specs

/-- Mode 2 top-level verification envelope (`VerificationResultWhenCompiledOn`),
    replacing `C.Verified` with `C.VerifiedWhenCompiled`. -/
def VerificationResultWhenCompiledOn
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List L_src.Behavior) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map
      (C.VerifiedWhenCompiled prog)))

/-- Helper lemma: `AllHold` over `specs.map (C.VerifiedWhenCompiled prog)` is
    equivalent to `AllHold` over
    `(specs.map (Behavior.when (C.compile prog).defined)).map (C.Verified prog)`
    whenever `Monotone C.π` holds. -/
theorem allHold_verifiedWhenCompiled_iff_when
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt} (h_mono : Monotone C.π)
    (prog : L_src.Prog) (specs : List L_src.Behavior) :
    AllHold (specs.map (C.VerifiedWhenCompiled prog)) ↔
      AllHold ((specs.map (Behavior.when (C.compile prog).defined)).map
        (C.Verified prog)) := by
  induction specs with
  | nil =>
    exact ⟨fun h => h, fun h => h⟩
  | cons hd tl ih =>
    dsimp [AllHold]
    have h_hd :=
      Compiler.verifiedWhenCompiled_iff_verified_when h_mono prog hd
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h_hd.mp h₁, ih.mp h₂⟩,
           fun ⟨h₁, h₂⟩ => ⟨h_hd.mpr h₁, ih.mpr h₂⟩⟩

/-- **Envelope Unification Theorem (`verificationResultWhenCompiledOn_iff`):**
    Under `Monotone C.π`, `VerificationResultWhenCompiledOn` is logically
    equivalent to the standard `VerificationResultOn` with precondition
    `fun q => (C.compile prog).defined ∧ pre q` and specifications
    `specs.map (Behavior.when (C.compile prog).defined)`. -/
theorem verificationResultWhenCompiledOn_iff
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    {C : Compiler L_src L_tgt} (h_mono : Monotone C.π)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List L_src.Behavior) :
    VerificationResultWhenCompiledOn C policy assumptions prog pre specs ↔
      VerificationResultOn C policy assumptions prog
        (fun q => (C.compile prog).defined ∧ pre q)
        (specs.map (Behavior.when (C.compile prog).defined)) := by
  unfold VerificationResultWhenCompiledOn VerificationResultOn
  rw [wellFormedOn_and_eq_when]
  have h_list :=
    allHold_verifiedWhenCompiled_iff_when h_mono prog
      (L_src.WellFormedOn pre :: specs)
  exact ⟨fun ⟨hpol, himp⟩ => ⟨hpol, fun hass => h_list.mp (himp hass)⟩,
         fun ⟨hpol, himp⟩ => ⟨hpol, fun hass => h_list.mpr (himp hass)⟩⟩

/-!
## 7. Conservative Extension over Total Compilers (`Compiler.ofTotal`)
-/

/-- For a total compiler lifted via `Compiler.ofTotal compile π`, `SoundOn` is
    equivalent to the original total-compiler definition
    `Monotone π ∧ Compiles L_src L_tgt π s (compile s)`. -/
theorem Compiler.ofTotal_soundOn_iff
    {L_src L_tgt : Language}
    (compile : L_src.Prog → L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) :
    (Compiler.ofTotal compile π).SoundOn s ↔
      Monotone π ∧ Compiles L_src L_tgt π s (compile s) :=
  ⟨fun ⟨hm, hc⟩ => ⟨hm, hc True.intro⟩,
   fun ⟨hm, hc⟩ => ⟨hm, fun _ => hc⟩⟩

/-- For a total compiler lifted via `Compiler.ofTotal compile π`, Modes 1, 2,
    and 3 all collapse to the original total-compiler `Verified` obligation. -/
theorem Compiler.ofTotal_verified_iff
    {L_src L_tgt : Language}
    (compile : L_src.Prog → L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (spec : L_src.Behavior) :
    (Compiler.ofTotal compile π).Verified s spec ↔
      L_src.sem s ≤ spec ∧
      Compiles L_src L_tgt π s (compile s) ∧
      L_tgt.sem (compile s) ≤ π spec :=
  ⟨fun ⟨hsrc, hc⟩ => ⟨hsrc, (hc True.intro).1, (hc True.intro).2⟩,
   fun ⟨hsrc, hc, hspec⟩ => ⟨hsrc, fun _ => ⟨hc, hspec⟩⟩⟩

theorem Compiler.ofTotal_verifiedWhenCompiled_iff
    {L_src L_tgt : Language}
    (compile : L_src.Prog → L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (spec : L_src.Behavior) :
    (Compiler.ofTotal compile π).VerifiedWhenCompiled s spec ↔
      (Compiler.ofTotal compile π).Verified s spec :=
  ⟨fun h => ⟨(h True.intro).1, fun _ => ⟨(h True.intro).2.1, (h True.intro).2.2⟩⟩,
   fun h => h.to_verifiedWhenCompiled⟩

theorem Compiler.ofTotal_verifiedTotal_iff
    {L_src L_tgt : Language}
    (compile : L_src.Prog → L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (spec : L_src.Behavior) :
    (Compiler.ofTotal compile π).VerifiedTotal s spec ↔
      (Compiler.ofTotal compile π).Verified s spec :=
  ⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩

/-- For a computable `Option`-returning compiler `Compiler.ofOption compile π`,
    `SoundOn` unfolds directly to `∀ t, compile s = some t → Compiles ...`. -/
theorem Compiler.ofOption_soundOn_iff
    {L_src L_tgt : Language}
    (compile : L_src.Prog → Option L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) :
    (Compiler.ofOption compile π).SoundOn s ↔
      Monotone π ∧ ∀ t, compile s = some t → Compiles L_src L_tgt π s t := by
  constructor
  · intro ⟨hm, hc⟩
    refine ⟨hm, fun t heq => ?_⟩
    have ⟨hdef, hval⟩ := (Option.eq_some_iff_toPartial (compile s) t).mp heq
    rw [← hval]
    exact hc hdef
  · intro ⟨hm, hc⟩
    refine ⟨hm, fun hdef => ?_⟩
    exact hc ((Option.toPartial (compile s)).val hdef)
      ((Option.eq_some_iff_toPartial (compile s) _).mpr ⟨hdef, rfl⟩)

/-- For a computable `Option`-returning compiler `Compiler.ofOption compile π`,
    `Verified` unfolds directly to `L_src.sem s ≤ spec` and
    `∀ t, compile s = some t → Compiles ... ∧ L_tgt.sem t ≤ π spec`. -/
theorem Compiler.ofOption_verified_iff
    {L_src L_tgt : Language}
    (compile : L_src.Prog → Option L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (spec : L_src.Behavior) :
    (Compiler.ofOption compile π).Verified s spec ↔
      L_src.sem s ≤ spec ∧
      ∀ t, compile s = some t →
        Compiles L_src L_tgt π s t ∧ L_tgt.sem t ≤ π spec := by
  constructor
  · intro ⟨hsrc, hc⟩
    refine ⟨hsrc, fun t heq => ?_⟩
    have ⟨hdef, hval⟩ := (Option.eq_some_iff_toPartial (compile s) t).mp heq
    rw [← hval]
    exact hc hdef
  · intro ⟨hsrc, hc⟩
    refine ⟨hsrc, fun hdef => ?_⟩
    exact hc ((Option.toPartial (compile s)).val hdef)
      ((Option.eq_some_iff_toPartial (compile s) _).mpr ⟨hdef, rfl⟩)

end PartialCompileAlgebra
