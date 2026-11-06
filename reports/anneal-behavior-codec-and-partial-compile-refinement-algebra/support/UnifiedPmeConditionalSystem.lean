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
# Unified Post-Monomorphization Error (PME) & Conditional Refinement System

This standalone Lean 4 file (`prelude` + `Init.NotationExtra` only, matching
`Trusted/Refinement.lean`) mechanizes the unified conditioning algebra and
compiler-correctness bridge for Round 2 Workstream 3
(`r2_ws3_unified_algebra_and_trusted_boundary`).

## Architectural Summary

1. **The Harmonized Conditioning Triad (`Behavior.when`, `Behavior.given`,
   `Behavior.require`):**
   Round 1 surfaced a naming and polarity collision across WS2, WS3, and WS6
   around conditioning a `Behavior` on a proposition `P : Prop`. This file
   resolves that collision into a three-operator triad with distinct,
   mnemonic names and exact algebraic laws:
   - `Behavior.when P b` (angelic program gating, left-hand side of `≤`):
     `defined := P → (b q).defined`,
     `val := fun h o => ∃ hp : P, (b q).val (h hp) o`.
     When `¬ P`, `Behavior.when P b` collapses to `Partial.bot` ($\bot$), the
     vacuously refining behavior.
   - `Behavior.given P spec` (precondition specification gating, right-hand
     side of `≤`):
     `defined := P ∧ (spec q).defined`, `val := fun h => (spec q).val h.2`.
     When `¬ P`, `Behavior.given P spec` collapses to `Partial.ub` ($\top$),
     the vacuously satisfied specification. Definitionally,
     `L.SpecOn (fun q => P ∧ pre q) post = Behavior.given P (L.SpecOn pre post)`
     by `rfl`.
   - `Behavior.require P b` (demonic program gating, left-hand side of `≤`):
     `defined := P ∧ (b q).defined`, `val := fun h => (b q).val h.2`.
     When `¬ P`, `Behavior.require P b` collapses to `Partial.ub` ($\top$),
     requiring `P` to hold whenever the specification on the right-hand side is
     defined.
   - **Galois Connection (`behavior_when_given_adjunction`):**
     `Behavior.when P b ≤ spec ↔ (P → b ≤ spec) ↔ b ≤ Behavior.given P spec`.
   - **Dependent Liftings (`semIfCompiled` and `semPartial`):**
     For a partial program `p? : Partial L.Prog`, `L.semIfCompiled p?` is the
     dependent generalization of `Behavior.when`, and `L.semPartial p?`
     (`fun q => Partial.bind p? (fun p => L.sem p q)`) is the dependent
     generalization of `Behavior.require`.

2. **Unified `TCBItem.rustcLowering`, `Compiler.SoundOn`, and `CompileAdmitted`
   (Target-Level Discharge Bridge):**
   For the partial compiler `rustc : MirBody → Partial TargetArtifact`,
   `TCBItem.rustcLowering fnName body` has meaning `RustcLoweringSound body`:
   `RustcMirCompiler.SoundOn body ∧`
   `((rustc body).defined → body.CompileAdmitted)`.
   When a function `body` is verified at the source level under the gated
   precondition `fun q => body.CompileAdmitted ∧ pre q` (equivalently, under
   `body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post`),
   `target_discharges_compileAdmitted` proves that for **any compiled target
   artifact** `h_comp : (rustc body).defined`:
   - `body.CompileAdmitted` holds automatically via `h_lowering.2 h_comp`,
   - the un-gated source specification `MirSem body ≤ MirLang.SpecOn pre post`
     holds, and
   - the compiled target artifact `(rustc body).val h_comp` satisfies
     `TargetLang.sem ((rustc body).val h_comp) ≤`
     `RustcMirCompiler.π (MirLang.SpecOn pre post)`
     under the runtime precondition `pre` alone, with `CompileAdmitted`
     completely discharged!

3. **Reconciliation with WS6's `MonoMirSem` and `unifiedTotalPre`:**
   We prove `MonoMirSem u = Behavior.require u.pmeOk (MirSem u.body)` by `rfl`
   and show how WS6's `unifiedTotalPre pre q := q.steps = 0 ∨ pre q` interacts
   with `Behavior.require` at `q.steps = 0` (`behaviorOf_defined_at_zero`) to
   extract `u.pmeOk` from the refinement relation.
-/

namespace Anneal.UnifiedPme

-- ============================================================================
-- Section 1: Core Refinement Preorder, `Partial`, `Partial.bind`, and `Option`
-- ============================================================================

/-- A reflexive and transitive relation `≤` on a type `α`. -/
class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

/-- Mutual refinement (`a ≤ b ∧ b ≤ a`) in a `Preorder`. -/
def Equiv {α : Type u} [Preorder α] (a b : α) : Prop :=
  a ≤ b ∧ b ≤ a

infix:50 " ≈ " => Equiv

theorem Equiv.refl {α : Type u} [Preorder α] (a : α) : a ≈ a :=
  ⟨Preorder.le_refl a, Preorder.le_refl a⟩

theorem Equiv.symm {α : Type u} [Preorder α] {a b : α} (h : a ≈ b) : b ≈ a :=
  ⟨h.2, h.1⟩

theorem Equiv.trans {α : Type u} [Preorder α] {a b c : α}
    (h1 : a ≈ b) (h2 : b ≈ c) : a ≈ c :=
  ⟨Preorder.le_trans h1.1 h2.1, Preorder.le_trans h2.2 h1.2⟩

/-- Monotonicity of a map between preorders. -/
def Monotone {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (f : α → β) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → f a ≤ f b

theorem Monotone.id {α : Type u} [Preorder α] : Monotone (fun x : α => x) :=
  fun _ _ h => h

theorem Monotone.comp {α : Type u} {β : Type v} {γ : Type w}
    [Preorder α] [Preorder β] [Preorder γ]
    {g : β → γ} {f : α → β} (hg : Monotone g) (hf : Monotone f) :
    Monotone (fun x => g (f x)) :=
  fun _ _ h => hg (hf h)

instance propPreorder : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h1 h2 hp := h2 (h1 hp)

instance funPreorder (α : Type u) (β : Type v) [Preorder β] :
    Preorder (α → β) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h1 h2 a := Preorder.le_trans (h1 a) (h2 a)

/-- The refinement container modeling partiality and undefined behavior (UB).
A value `x : Partial α` is defined when `x.defined` holds, in which case
`x.val h` yields the underlying `α`. -/
structure Partial (α : Type u) where
  defined : Prop
  val : defined → α

namespace Partial

/-- Embeds a total value into `Partial α`. -/
def pure {α : Type u} (a : α) : Partial α where
  defined := True
  val := fun _ => a

/-- Undefined behavior ($\top$ in the refinement lattice): vacuously satisfied
as a specification on the right-hand side of `≤`, and the worst (demonic)
element as a program on the left-hand side of `≤`. -/
def ub {α : Type u} : Partial α where
  defined := False
  val := False.elim

/-- When `α` is a family of propositions `β → Prop`, `bot` ($\bot$ in the
refinement lattice) is the miraculous / angelic element: always defined, with
an empty observation set. It refines every specification. -/
def bot {β : Type u} : Partial (β → Prop) where
  defined := True
  val := fun _ _ => False

/-- Functorial map over `Partial`. -/
def map {α : Type u} {β : Type v} (f : α → β) (x : Partial α) : Partial β where
  defined := x.defined
  val := fun h => f (x.val h)

/-- Dependent monadic bind over `Partial`. A sequenced computation is defined
iff the first stage is defined (`h₁ : x.defined`) and the continuation
`f (x.val h₁)` is defined. Uses `h.1` (`Exists.fst`) and `h.2` (`Exists.snd`)
relying on proof irrelevance of `x.defined : Prop`. -/
def bind {α : Type u} {β : Type v}
    (x : Partial α) (f : α → Partial β) : Partial β where
  defined := ∃ h : x.defined, (f (x.val h)).defined
  val h := (f (x.val h.1)).val h.2

/-- Structural equivalence on `Partial α` without requiring a `Preorder`
on `α`. -/
def StructEquiv {α : Type u} (x y : Partial α) : Prop :=
  (x.defined ↔ y.defined) ∧
  ∀ (hx : x.defined) (hy : y.defined), x.val hx = y.val hy

/-- Forward-simulation / behavioral refinement on `Partial α`:
`p ≤ q` means that whenever the specification `q` is defined (`hq : q.defined`),
the implementation `p` is also defined (`hp : p.defined`) and its value refines
`q`'s value (`p.val hp ≤ q.val hq`). -/
instance partialPreorder (α : Type u) [Preorder α] : Preorder (Partial α) where
  le p q := ∀ hq : q.defined, ∃ hp : p.defined, p.val hp ≤ q.val hq
  le_refl p hp := ⟨hp, Preorder.le_refl (p.val hp)⟩
  le_trans h1 h2 hq :=
    let ⟨hb, hbc⟩ := h2 hq
    let ⟨ha, hab⟩ := h1 hb
    ⟨ha, Preorder.le_trans hab hbc⟩

/-- `Partial.ub` is the top element ($\top$) of the refinement preorder. -/
theorem ub_top {α : Type u} [Preorder α] (x : Partial α) :
    x ≤ (Partial.ub : Partial α) :=
  fun h => False.elim h

/-- `Partial.bot` is the bottom element ($\bot$) of `Partial (β → Prop)`. -/
theorem bot_le {β : Type u} (x : Partial (β → Prop)) :
    (Partial.bot : Partial (β → Prop)) ≤ x :=
  fun _ => ⟨trivial, fun _ h => False.elim h⟩

/-- Left identity law for `Partial.bind`. -/
theorem bind_pure_left {α : Type u} {β : Type v}
    (a : α) (f : α → Partial β) :
    StructEquiv (Partial.bind (Partial.pure a) f) (f a) := by
  refine ⟨⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩, ?_⟩
  intro _ _
  rfl

/-- Right identity law for `Partial.bind`. -/
theorem bind_pure_right {α : Type u} (x : Partial α) :
    StructEquiv (Partial.bind x Partial.pure) x := by
  refine ⟨⟨fun h => h.1, fun h => ⟨h, True.intro⟩⟩, ?_⟩
  intro _ _
  rfl

/-- Associativity law for `Partial.bind`. -/
theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (x : Partial α) (f : α → Partial β) (g : β → Partial γ) :
    StructEquiv
      (Partial.bind (Partial.bind x f) g)
      (Partial.bind x (fun a => Partial.bind (f a) g)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    exact ⟨h.1.1, ⟨h.1.2, h.2⟩⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · intro _ _
    rfl

/-- Monotonicity of `Partial.bind` in its continuation argument. -/
theorem bind_mono_right {α : Type u} {β : Type v} [Preorder β]
    (x : Partial α) {f g : α → Partial β}
    (hfg : ∀ a, f a ≤ g a) :
    Partial.bind x f ≤ Partial.bind x g := by
  intro hxg
  cases hfg (x.val hxg.1) hxg.2 with
  | intro hf hle =>
    exact ⟨⟨hxg.1, hf⟩, hle⟩

end Partial

/-- Canonical embedding of `Option α` into `Partial α`.
Used to bridge executable partial evaluators (`Option`) into the relational
refinement domain (`Partial`) without axioms. -/
def Option.toPartial {α : Type u} : Option α → Partial α
  | some a => Partial.pure a
  | none   => Partial.ub

theorem Option.toPartial_some {α : Type u} (a : α) :
    Option.toPartial (some a) = Partial.pure a := rfl

theorem Option.toPartial_none {α : Type u} :
    Option.toPartial (@none α) = Partial.ub := rfl

theorem Option.toPartial_defined_iff {α : Type u} (o : Option α) :
    (Option.toPartial o).defined ↔ ∃ a, o = some a := by
  cases o with
  | none =>
    exact ⟨fun h => False.elim h, fun ⟨_, h⟩ => by cases h⟩
  | some a =>
    exact ⟨fun _ => ⟨a, rfl⟩, fun _ => True.intro⟩

-- ============================================================================
-- Section 2: The Harmonized Conditioning Triad (`when`, `given`, `require`)
--            and Dependent Liftings (`semIfCompiled`, `semPartial`)
-- ============================================================================

/-- The semantic behavior domain over query type `Query` and observation type
`Obs`: a query-indexed family of partial observation predicates. -/
abbrev Behavior (Query Obs : Type) : Type :=
  Query → Partial (Obs → Prop)

/-- A language with program syntax `Prog`, execution query `Query`, execution
observation `Obs`, and denotational semantics `sem`. -/
structure Language where
  Prog : Type
  Query : Type
  Obs : Type
  sem : Prog → Behavior Query Obs

namespace Language

/-- The semantic domain of a language `L`. -/
abbrev Behavior (L : Language) : Type :=
  Anneal.UnifiedPme.Behavior L.Query L.Obs

/-- A Hoare-style specification over a query precondition `pre` and a
query-indexed postcondition `post`. -/
def SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Obs → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Well-formedness (absence of UB) on all queries satisfying `pre`. -/
abbrev WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

theorem wellFormedOn_eq_specOn_true (L : Language) (pre : L.Query → Prop) :
    L.WellFormedOn pre = L.SpecOn pre (fun _ _ => True) := rfl

end Language

namespace Behavior

/-- **1. Angelic / Conditional Program Gating (`Behavior.when`):**
Conditions a program behavior `b` on a proposition `P` on the **left-hand side**
of `≤`.
- When `P` holds, `Behavior.when P b` behaves identically to `b`.
- When `¬ P` holds, `(Behavior.when P b q).defined` is vacuously `True` and its
  observation set is empty (`Partial.bot`, $\bot$), so it vacuously refines any
  specification. -/
def when {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P → (b q).defined
    val := fun h o => ∃ hp : P, (b q).val (h hp) o
  }

/-- **2. Precondition Specification Gating (`Behavior.given`):**
Conditions a specification `spec` on a proposition `P` on the **right-hand
side** of `≤`.
- When `P` holds, `Behavior.given P spec` requires the same definedness and
  observations as `spec`.
- When `¬ P` holds, `(Behavior.given P spec q).defined` is `False`
  (`Partial.ub`, $\top$), so any program vacuously refines it. -/
def given {Query Obs : Type} (P : Prop) (spec : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P ∧ (spec q).defined
    val := fun h => (spec q).val h.2
  }

/-- **3. Demonic Program Gating (`Behavior.require`):**
Asserts a proposition `P` alongside a program behavior `b` on the **left-hand
side** of `≤`.
- When `P` holds, `Behavior.require P b` behaves identically to `b`.
- When `¬ P` holds, `(Behavior.require P b q).defined` is `False`
  (`Partial.ub`, $\top$), so refining any specification `spec` that is defined
  at some query `q₀` forces `P` to hold! -/
def require {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P ∧ (b q).defined
    val := fun h => (b q).val h.2
  }

/-- Definitional identity: adding a proposition `P` to the query precondition of
`L.SpecOn` is definitionally equal to `Behavior.given P`. -/
theorem specOn_and_eq_given (L : Language) (P : Prop)
    (pre : L.Query → Prop) (post : L.Query → L.Obs → Prop) :
    L.SpecOn (fun q => P ∧ pre q) post =
      Behavior.given P (L.SpecOn pre post) := rfl

/-- Definitional identity: adding a proposition `P` to the query precondition of
`L.WellFormedOn` is definitionally equal to `Behavior.given P`. -/
theorem wellFormedOn_and_eq_given (L : Language) (P : Prop)
    (pre : L.Query → Prop) :
    L.WellFormedOn (fun q => P ∧ pre q) =
      Behavior.given P (L.WellFormedOn pre) := rfl

/-- Universal property of `Behavior.when` on the left-hand side of `≤`.
Constructive (zero axioms). -/
theorem behavior_when_le_iff {Query Obs : Type} {P : Prop}
    {b spec : Behavior Query Obs} :
    Behavior.when P b ≤ spec ↔ (P → b ≤ spec) := by
  constructor
  · intro h hp q hspec
    cases h q hspec with
    | intro hdef hval =>
      exact ⟨hdef hp, fun o ho => hval o ⟨hp, ho⟩⟩
  · intro h q hspec
    refine ⟨fun hp => (h hp q hspec).1, ?_⟩
    intro o hex
    cases hex with
    | intro hp ho =>
      exact (h hp q hspec).2 o ho

/-- Universal property of `Behavior.given` on the right-hand side of `≤`.
Constructive (zero axioms). -/
theorem behavior_le_given_iff {Query Obs : Type} {P : Prop}
    {b spec : Behavior Query Obs} :
    b ≤ Behavior.given P spec ↔ (P → b ≤ spec) := by
  constructor
  · intro h hp q hspec
    exact h q ⟨hp, hspec⟩
  · intro h q hgiven
    exact h hgiven.1 q hgiven.2

/-- **The Fundamental Galois Connection (`when` $\dashv$ `given`):**
Conditioning the program on `P` via `Behavior.when P b` on the left of `≤` is
equivalent to the meta-level implication `P → b ≤ spec`, which in turn is
equivalent to conditioning the specification on `P` via `Behavior.given P spec`
on the right of `≤`. -/
theorem behavior_when_given_adjunction {Query Obs : Type} (P : Prop)
    (b spec : Behavior Query Obs) :
    (Behavior.when P b ≤ spec ↔ (P → b ≤ spec)) ∧
    ((P → b ≤ spec) ↔ b ≤ Behavior.given P spec) :=
  ⟨behavior_when_le_iff, behavior_le_given_iff.symm⟩

/-- Direct equivalence between `Behavior.when P b ≤ spec` and
`b ≤ Behavior.given P spec`. -/
theorem behavior_when_le_iff_le_given {Query Obs : Type} (P : Prop)
    (b spec : Behavior Query Obs) :
    Behavior.when P b ≤ spec ↔ b ≤ Behavior.given P spec :=
  behavior_when_le_iff.trans behavior_le_given_iff.symm

/-- Discharging `Behavior.given P spec` once `P` is proven. -/
theorem le_of_le_given_of_true {Query Obs : Type} {P : Prop}
    {b spec : Behavior Query Obs} (hle : b ≤ Behavior.given P spec) (hp : P) :
    b ≤ spec :=
  behavior_le_given_iff.mp hle hp

/-- Universal property of `Behavior.require` on the left-hand side of `≤`.
`Behavior.require P b ≤ spec` holds iff:
1. Every query `q` where `spec q` is defined forces `P` to hold, and
2. Whenever `P` holds, `b ≤ spec`. -/
theorem behavior_require_le_iff {Query Obs : Type} {P : Prop}
    {b spec : Behavior Query Obs} :
    Behavior.require P b ≤ spec ↔
      (∀ q, (spec q).defined → P) ∧ (P → b ≤ spec) := by
  constructor
  · intro h
    refine ⟨fun q hspec => (h q hspec).1.1, fun hp q hspec => ?_⟩
    cases h q hspec with
    | intro hreq hval =>
      exact ⟨hreq.2, hval⟩
  · intro h q hspec
    have hp : P := h.1 q hspec
    cases h.2 hp q hspec with
    | intro hb_def hval =>
      exact ⟨⟨hp, hb_def⟩, hval⟩

/-- If `Behavior.require P b ≤ spec`, then `P → b ≤ spec`. -/
theorem behavior_require_le_imp {Query Obs : Type} {P : Prop}
    {b spec : Behavior Query Obs} (h : Behavior.require P b ≤ spec) :
    P → b ≤ spec :=
  (behavior_require_le_iff.mp h).2

/-- When `spec` is defined at even a single witness query `q₀`,
`Behavior.require P b ≤ spec` simplifies to the conjunction `P ∧ b ≤ spec`! -/
theorem behavior_require_le_iff_of_defined {Query Obs : Type} {P : Prop}
    {b spec : Behavior Query Obs} {q₀ : Query} (hq₀ : (spec q₀).defined) :
    Behavior.require P b ≤ spec ↔ P ∧ b ≤ spec := by
  rw [behavior_require_le_iff]
  constructor
  · intro h
    have hp : P := h.1 q₀ hq₀
    exact ⟨hp, h.2 hp⟩
  · intro h
    exact ⟨fun _ _ => h.1, fun _ => h.2⟩

/-- When `P` holds, `Behavior.when P b ≈ b`. -/
theorem when_equiv_of_true {Query Obs : Type} {P : Prop} (hp : P)
    (b : Behavior Query Obs) :
    Behavior.when P b ≈ b := by
  constructor
  · intro q hdef
    refine ⟨fun _ => hdef, ?_⟩
    intro o hex
    exact hex.2
  · intro q hdef
    exact ⟨hdef hp, fun o ho => ⟨hp, ho⟩⟩

/-- When `P` holds, `Behavior.given P spec ≈ spec`. -/
theorem given_equiv_of_true {Query Obs : Type} {P : Prop} (hp : P)
    (spec : Behavior Query Obs) :
    Behavior.given P spec ≈ spec := by
  constructor
  · intro q hdef
    exact ⟨⟨hp, hdef⟩, fun _ ho => ho⟩
  · intro q hgiven
    exact ⟨hgiven.2, fun _ ho => ho⟩

/-- When `P` holds, `Behavior.require P b ≈ b`. -/
theorem require_equiv_of_true {Query Obs : Type} {P : Prop} (hp : P)
    (b : Behavior Query Obs) :
    Behavior.require P b ≈ b :=
  given_equiv_of_true hp b

/-- Lattice ordering across the conditioning triad:
`Behavior.when P b ≤ b ≤ Behavior.given P b = Behavior.require P b`. -/
theorem when_le_self {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior.when P b ≤ b :=
  behavior_when_le_iff.mpr (fun _ => Preorder.le_refl b)

theorem self_le_given {Query Obs : Type} (P : Prop)
    (spec : Behavior Query Obs) :
    spec ≤ Behavior.given P spec :=
  behavior_le_given_iff.mpr (fun _ => Preorder.le_refl spec)

theorem self_le_require {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    b ≤ Behavior.require P b :=
  self_le_given P b

theorem when_le_require {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior.when P b ≤ Behavior.require P b :=
  Preorder.le_trans (when_le_self P b) (self_le_require P b)

end Behavior

namespace Language

/-- **Dependent Angelic Lifting (`Language.semIfCompiled`):**
Lifts `L.sem` over a partial program `p? : Partial L.Prog` angelically:
- When `p?.defined` holds (`h : p?.defined`), it behaves like
  `L.sem (p?.val h)`.
- When `¬ p?.defined`, it is vacuously defined with empty observations
  (`Partial.bot`, $\bot$).
This is the dependent generalization of `Behavior.when`. -/
def semIfCompiled (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => {
    defined := ∀ h : p?.defined, (L.sem (p?.val h) q).defined
    val := fun hdef o => ∃ h : p?.defined, (L.sem (p?.val h) q).val (hdef h) o
  }

/-- **Dependent Demonic Lifting (`Language.semPartial`):**
Lifts `L.sem` over a partial program `p? : Partial L.Prog` demonically via
`Partial.bind`:
- A query `q` is defined iff `p?.defined` holds AND `L.sem (p?.val h) q` is
  defined.
- When `¬ p?.defined`, `L.semPartial p? q` is undefined (`Partial.ub`, $\top$).
This is the dependent generalization of `Behavior.require`. -/
def semPartial (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => Partial.bind p? (fun p => L.sem p q)

/-- `semIfCompiled` on a constant partial program
`{ defined := P, val := fun _ => p }` is **definitionally equal** (`rfl`) to
`Behavior.when P (L.sem p)`. -/
theorem semIfCompiled_const_eq_when (L : Language) (P : Prop) (p : L.Prog) :
    L.semIfCompiled { defined := P, val := fun _ => p } =
      Behavior.when P (L.sem p) := rfl

/-- `semPartial` on a constant partial program
`{ defined := P, val := fun _ => p }` is mutually refining (`≈`) with
`Behavior.require P (L.sem p)` (differing only in `∃ _ : P, Q` vs `P ∧ Q`). -/
theorem semPartial_const_equiv_require (L : Language) (P : Prop) (p : L.Prog) :
    L.semPartial { defined := P, val := fun _ => p } ≈
      Behavior.require P (L.sem p) := by
  constructor
  · intro q hreq
    exact ⟨⟨hreq.1, hreq.2⟩, fun _ ho => ho⟩
  · intro q hpart
    exact ⟨⟨hpart.1, hpart.2⟩, fun _ ho => ho⟩

/-- Universal property of `L.semIfCompiled`:
`L.semIfCompiled p? ≤ spec` holds iff for every proof `h : p?.defined`,
`L.sem (p?.val h) ≤ spec`. Constructive (zero axioms). -/
theorem semIfCompiled_le_iff (L : Language) (p? : Partial L.Prog)
    (spec : L.Behavior) :
    L.semIfCompiled p? ≤ spec ↔
      ∀ h : p?.defined, L.sem (p?.val h) ≤ spec := by
  constructor
  · intro hle h q hspec
    cases hle q hspec with
    | intro hdef hval =>
      exact ⟨hdef h, fun o ho => hval o ⟨h, ho⟩⟩
  · intro h q hspec
    refine ⟨fun hp => (h hp q hspec).1, ?_⟩
    intro o hex
    cases hex with
    | intro hp ho =>
      exact (h hp q hspec).2 o ho

/-- Universal property of `L.semPartial`:
`L.semPartial p? ≤ spec` holds iff every query `q` where `spec q` is defined
forces `p?.defined`, and for every `h : p?.defined`,
`L.sem (p?.val h) ≤ spec`. -/
theorem semPartial_le_iff (L : Language) (p? : Partial L.Prog)
    (spec : L.Behavior) :
    L.semPartial p? ≤ spec ↔
      (∀ q, (spec q).defined → p?.defined) ∧
      (∀ h : p?.defined, L.sem (p?.val h) ≤ spec) := by
  constructor
  · intro hle
    refine ⟨fun q hspec => (hle q hspec).1.1, fun hp q hspec => ?_⟩
    cases hle q hspec with
    | intro hpart hval =>
      exact ⟨hpart.2, hval⟩
  · intro h q hspec
    have hp : p?.defined := h.1 q hspec
    cases h.2 hp q hspec with
    | intro hdef hval =>
      exact ⟨⟨hp, hdef⟩, hval⟩

/-- When `spec` is defined at some witness query `q₀`, `L.semPartial p? ≤ spec`
is equivalent to `∃ h : p?.defined, L.sem (p?.val h) ≤ spec`. -/
theorem semPartial_le_iff_of_defined (L : Language) (p? : Partial L.Prog)
    (spec : L.Behavior) {q₀ : L.Query} (hq₀ : (spec q₀).defined) :
    L.semPartial p? ≤ spec ↔
      ∃ h : p?.defined, L.sem (p?.val h) ≤ spec := by
  rw [semPartial_le_iff]
  constructor
  · intro h
    have hp : p?.defined := h.1 q₀ hq₀
    exact ⟨hp, h.2 hp⟩
  · intro hex
    cases hex with
    | intro hp hsem =>
      exact ⟨fun _ _ => hp, fun _ => hsem⟩

/-- `semIfCompiled` always refines `semPartial`. -/
theorem semIfCompiled_le_semPartial (L : Language) (p? : Partial L.Prog) :
    L.semIfCompiled p? ≤ L.semPartial p? := by
  intro q hpart
  refine ⟨fun _ => hpart.2, ?_⟩
  intro o hex
  exact hex.2

/-- When `p?.defined` holds, `semPartial` refines `semIfCompiled` (so the two
coincide up to `≈`). -/
theorem semPartial_le_semIfCompiled_of_defined (L : Language)
    (p? : Partial L.Prog) (h : p?.defined) :
    L.semPartial p? ≤ L.semIfCompiled p? := by
  intro q hdef
  exact ⟨⟨h, hdef h⟩, fun o ho => ⟨h, ho⟩⟩

end Language

-- ============================================================================
-- Section 3: Partial `Compiler` Algebra and Mode Unification
-- ============================================================================

/-- Cross-language behavioral refinement along a behavior map
`π : S.Behavior → T.Behavior`: a target behavior `tb` refines a source behavior
`sb` through `π` when `tb ≤ π sb`. -/
def RefinesWith {S T : Language} (π : S.Behavior → T.Behavior)
    (tb : T.Behavior) (sb : S.Behavior) : Prop :=
  tb ≤ π sb

notation:50 tb " ⊑[" π "] " sb:50 => RefinesWith π tb sb

/-- Pointwise compilation correctness for a concrete source program `s : S.Prog`
and a concrete target program `t : T.Prog`. -/
def Compiles (S T : Language) (π : S.Behavior → T.Behavior)
    (s : S.Prog) (t : T.Prog) : Prop :=
  T.sem t ⊑[π] S.sem s

/-- A (potentially partial) compiler pass from language `S` to language `T`,
packaged with its behavior map `π : S.Behavior → T.Behavior`. -/
structure Compiler (S T : Language) where
  compile : S.Prog → Partial T.Prog
  π : S.Behavior → T.Behavior

namespace Compiler

/-- Identity compiler pass on language `L`. -/
def id (L : Language) : Compiler L L where
  compile p := Partial.pure p
  π b := b

/-- Sequential composition of partial compiler passes `C₁ : Compiler S M` and
`C₂ : Compiler M T` via `Partial.bind`. -/
def comp {S M T : Language}
    (C₂ : Compiler M T) (C₁ : Compiler S M) : Compiler S T where
  compile s := Partial.bind (C₁.compile s) C₂.compile
  π sb := C₂.π (C₁.π sb)

/-- Per-program compiler soundness on `s : S.Prog`: `C.π` is monotone and every
defined compilation artifact `(C.compile s).val h` refines `s` through `C.π`. -/
def SoundOn {S T : Language} (C : Compiler S T) (s : S.Prog) : Prop :=
  Monotone C.π ∧
  ∀ h : (C.compile s).defined, Compiles S T C.π s ((C.compile s).val h)

/-- Global compiler soundness across all programs `s : S.Prog`. -/
def Sound {S T : Language} (C : Compiler S T) : Prop :=
  Monotone C.π ∧
  ∀ (s : S.Prog) (h : (C.compile s).defined),
    Compiles S T C.π s ((C.compile s).val h)

theorem Sound.soundOn {S T : Language} {C : Compiler S T}
    (hC : C.Sound) (s : S.Prog) : C.SoundOn s :=
  ⟨hC.1, hC.2 s⟩

theorem SoundOn.comp {S M T : Language}
    {C₂ : Compiler M T} {C₁ : Compiler S M} {s : S.Prog}
    (h₁ : C₁.SoundOn s)
    (h₂ : Monotone C₂.π ∧
      ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₂.comp C₁).SoundOn s := by
  refine ⟨fun _ _ h => h₂.1 (h₁.1 h), ?_⟩
  intro h12
  have hm : M.sem ((C₁.compile s).val h12.1) ≤ C₁.π (S.sem s) := h₁.2 h12.1
  have ht : T.sem ((C₂.compile ((C₁.compile s).val h12.1)).val h12.2) ≤
      C₂.π (M.sem ((C₁.compile s).val h12.1)) := (h₂.2 h12.1).2 h12.2
  exact Preorder.le_trans ht (h₂.1 hm)

/-- **Mode 1 (`Compiler.Verified`): Source-Unconditional, Target-Conditional.**
The source program `s` unconditionally refines `spec` (`S.sem s ≤ spec`), `C.π`
is monotone, and every compiled artifact `h : (C.compile s).defined` refines
both `S.sem s` and `spec` through `C.π`. -/
def Verified {S T : Language} (C : Compiler S T)
    (s : S.Prog) (spec : S.Behavior) : Prop :=
  S.sem s ≤ spec ∧
  C.SoundOn s ∧
  ∀ h : (C.compile s).defined,
    T.sem ((C.compile s).val h) ⊑[C.π] spec

/-- **Mode 2 (`Compiler.VerifiedWhenCompiled`): Source- and Target-Conditional
on `(C.compile s).defined`.**
Equivalent to `C.Verified s (Behavior.given (C.compile s).defined spec)`. -/
def VerifiedWhenCompiled {S T : Language} (C : Compiler S T)
    (s : S.Prog) (spec : S.Behavior) : Prop :=
  ((C.compile s).defined → S.sem s ≤ spec) ∧
  C.SoundOn s ∧
  ∀ h : (C.compile s).defined,
    T.sem ((C.compile s).val h) ⊑[C.π] spec

/-- **Mode 3 (`Compiler.VerifiedTotal`): Compilation-Guaranteed
(`(C.compile s).defined`) plus `C.Verified s spec`.** -/
def VerifiedTotal {S T : Language} (C : Compiler S T)
    (s : S.Prog) (spec : S.Behavior) : Prop :=
  (C.compile s).defined ∧ C.Verified s spec

/-- Mode 2 (`VerifiedWhenCompiled`) is equivalent to Mode 1 (`Verified`) over
the `Behavior.given (C.compile s).defined spec` specification (with the target
conclusion holding for `spec` directly whenever `h : (C.compile s).defined`). -/
theorem verifiedWhenCompiled_iff_verified_given {S T : Language}
    (C : Compiler S T) (s : S.Prog) (spec : S.Behavior) :
    C.VerifiedWhenCompiled s spec ↔
      (S.sem s ≤ Behavior.given (C.compile s).defined spec ∧
       C.SoundOn s ∧
       ∀ h : (C.compile s).defined,
         T.sem ((C.compile s).val h) ⊑[C.π] spec) := by
  rw [VerifiedWhenCompiled, Behavior.behavior_le_given_iff]

/-- Expressing `C.Verified s spec` via `T.semIfCompiled (C.compile s)`. -/
theorem verified_iff_semIfCompiled {S T : Language}
    (C : Compiler S T) (s : S.Prog) (spec : S.Behavior) :
    C.Verified s spec ↔
      S.sem s ≤ spec ∧
      Monotone C.π ∧
      T.semIfCompiled (C.compile s) ≤ C.π (S.sem s) ∧
      T.semIfCompiled (C.compile s) ≤ C.π spec := by
  simp only [Verified, SoundOn, Compiles, RefinesWith,
    Language.semIfCompiled_le_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.1.1, h.2.1.2, h.2.2⟩
  · intro h
    exact ⟨h.1, ⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩

/-- Expressing `C.VerifiedTotal s spec` when `spec` has a witness query `q₀`
where `(C.π spec q₀).defined` holds: `T.semPartial (C.compile s) ≤ C.π spec`
automatically witnesses `(C.compile s).defined`! -/
theorem verifiedTotal_of_semPartial {S T : Language}
    (C : Compiler S T) (s : S.Prog) (spec : S.Behavior)
    {q₀ : T.Query} (hq₀ : (C.π spec q₀).defined)
    (hsrc : S.sem s ≤ spec)
    (hsound : C.SoundOn s)
    (hpart : T.semPartial (C.compile s) ≤ C.π spec) :
    C.VerifiedTotal s spec := by
  rw [Language.semPartial_le_iff] at hpart
  have hcomp : (C.compile s).defined := hpart.1 q₀ hq₀
  exact ⟨hcomp, hsrc, hsound, hpart.2⟩

/-- Fundamental bridge from `C.SoundOn s` and source refinement `S.sem s ≤ spec`
to `C.Verified s spec`. -/
theorem SoundOn.verify {S T : Language} {C : Compiler S T} {s : S.Prog}
    (hC : C.SoundOn s) {spec : S.Behavior} (hsrc : S.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨hsrc, hC, fun h => Preorder.le_trans (hC.2 h) (hC.1 hsrc)⟩

/-- Consequence / specification weakening for `Compiler.Verified`. -/
theorem Verified.mono {S T : Language} {C : Compiler S T} {s : S.Prog}
    {spec₁ spec₂ : S.Behavior}
    (hv : C.Verified s spec₁) (hle : spec₁ ≤ spec₂) :
    C.Verified s spec₂ :=
  ⟨Preorder.le_trans hv.1 hle, hv.2.1,
   fun h => Preorder.le_trans (hv.2.2 h) (hv.2.1.1 hle)⟩

/-- Extracting `S.WellFormedOn pre` from `C.Verified s (S.SpecOn pre post)`. -/
theorem Verified.with_wellFormedOn {S T : Language} {C : Compiler S T}
    {s : S.Prog} {pre : S.Query → Prop} {post : S.Query → S.Obs → Prop}
    (hv : C.Verified s (S.SpecOn pre post)) :
    C.Verified s (S.WellFormedOn pre) := by
  refine hv.mono ?_
  intro q hpre
  exact ⟨hpre, fun _ _ => trivial⟩

/-- Composing `Compiler.Verified` across a second compiler pass `C₂`. -/
theorem Verified.comp {S M T : Language}
    {C₂ : Compiler M T} {C₁ : Compiler S M} {s : S.Prog} {spec : S.Behavior}
    (hv₁ : C₁.Verified s spec)
    (h₂ : Monotone C₂.π ∧
      ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₂.comp C₁).Verified s spec := by
  have hcomp_sound : (C₂.comp C₁).SoundOn s := hv₁.2.1.comp h₂
  exact hcomp_sound.verify hv₁.1

end Compiler

/-- Multi-pass compiler pipeline verification: if `s` refines `spec` in `S`,
`C₁` is sound on `s`, and `C₂` is sound on the intermediate program produced
by `C₁`, then `(C₂.comp C₁).Verified s spec` holds. -/
theorem verify_through_passes {S M T : Language}
    (C₂ : Compiler M T) (C₁ : Compiler S M) (s : S.Prog) (spec : S.Behavior)
    (hsrc : S.sem s ≤ spec)
    (h₁ : C₁.SoundOn s)
    (h₂ : Monotone C₂.π ∧
      ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)) :
    (C₂.comp C₁).Verified s spec :=
  (h₁.verify hsrc).comp h₂

/-- Trust boundary abstractions matching `Trusted/Refinement.lean`. -/
class TrustedAssumption (Item : Type u) where
  meaning : Item → Prop

def TrustPolicy (Item : Type u) : Type u := Item → Prop

/-- The verified envelope for a function `prog` under precondition `pre` and
specification list `specs`: under all admitted TCB items, `C.Verified prog`
holds for `S.WellFormedOn pre` and for every `spec ∈ specs`. -/
def VerificationResultOn {S T : Language} {Item : Type u}
    [TrustedAssumption Item]
    (C : Compiler S T) (policy : TrustPolicy Item) (tcb : List Item)
    (prog : S.Prog) (pre : S.Query → Prop) (specs : List S.Behavior) : Prop :=
  (∀ item, item ∈ tcb → policy item) ∧
  ((∀ item, item ∈ tcb → TrustedAssumption.meaning item) →
    C.Verified prog (S.WellFormedOn pre) ∧
    ∀ spec, spec ∈ specs → C.Verified prog spec)

/-- Unconditional verification envelope (`pre := fun _ => True`). -/
def VerificationResult {S T : Language} {Item : Type u}
    [TrustedAssumption Item]
    (C : Compiler S T) (policy : TrustPolicy Item) (tcb : List Item)
    (prog : S.Prog) (specs : List S.Behavior) : Prop :=
  VerificationResultOn C policy tcb prog (fun _ => True) specs

-- ============================================================================
-- Section 4: Unifying `TCBItem.rustcLowering`, `Compiler.SoundOn`, and
--            `CompileAdmitted` (The Target-Level Discharge Bridge)
-- ============================================================================

/-- Single-step outcome of a small-step operational machine. -/
inductive StepResult (State Ret : Type) where
  | step (next : State)
  | done (ret : Ret)
  | stuck

/-- Fuel-indexed execution query (`steps : Nat`, `init : Init`). -/
structure ExecQuery (Init : Type) where
  steps : Nat
  init : Init

/-- Execution observation at fuel `steps`: either out-of-fuel or terminated
with a return value `ret : Ret`. -/
inductive ExecObs (Ret : Type) where
  | outOfFuel
  | returned (ret : Ret)

/-- A small-step operational machine with initial input `Init`, state `State`,
and return value `Ret`. -/
structure SmallStepMachine where
  Init : Type
  State : Type
  Ret : Type
  initState : Init → State
  step : State → StepResult State Ret

/-- Relational prefix reachability (`ReachesPrefix M n s m`): from state `s`,
every `k`-step trajectory (`k ≤ n`) stays non-stuck, and `m` records whether
execution finished within `n` steps (`some ret`) or exhausted fuel `n`
(`none`). -/
inductive ReachesPrefix (M : SmallStepMachine) :
    Nat → M.State → Option M.Ret → Prop where
  | zero (s : M.State) :
      ReachesPrefix M 0 s none
  | done (n : Nat) (s : M.State) (ret : M.Ret) :
      M.step s = .done ret →
      ReachesPrefix M (n + 1) s (some ret)
  | step (n : Nat) (s s' : M.State) (out : Option M.Ret) :
      M.step s = .step s' →
      ReachesPrefix M n s' out →
      ReachesPrefix M (n + 1) s out

/-- Canonical behavior of a small-step machine `M`: defined at query `q` iff
some outcome `out` is reached within `q.steps` without getting stuck. -/
def BehaviorOf (M : SmallStepMachine) :
    Behavior (ExecQuery M.Init) (ExecObs M.Ret) :=
  fun q => {
    defined := ∃ out, ReachesPrefix M q.steps (M.initState q.init) out
    val := fun _ obs =>
      match obs with
      | .outOfFuel    => ReachesPrefix M q.steps (M.initState q.init) none
      | .returned ret => ReachesPrefix M q.steps (M.initState q.init) (some ret)
  }

/-- **Key Zero-Step Definedness Property:**
For any small-step machine `M`, `BehaviorOf M q` is **always defined** at
`q.steps = 0` (`ReachesPrefix.zero`), regardless of whether `M` gets stuck at
step 1! This is the exact property that enables WS6's `unifiedTotalPre`
(`q.steps = 0 ∨ pre q`) to extract `CompileAdmitted` via `Behavior.require`. -/
theorem behaviorOf_defined_at_zero (M : SmallStepMachine)
    (q : ExecQuery M.Init) (hq : q.steps = 0) :
    (BehaviorOf M q).defined := by
  cases q with
  | mk steps init =>
    cases hq
    exact ⟨none, ReachesPrefix.zero (M.initState init)⟩

/-- Identifier for an inline `const { ... }` block
(`mir::Const::Unevaluated`). -/
abbrev ConstId := String

/-- Model of a constant-evaluated MIR body (`ConstMirBody`) associated with a
`mir::Const::Unevaluated` block.
In `Trusted/MirSemantics.lean`, `ConstMirMachine cb` executes `cb`'s statements
starting from `Init := Unit`; we model its single-step transition explicitly
here so `ConstMirMachine` is a concrete `SmallStepMachine`. -/
structure ConstMirBody where
  id : ConstId
  /-- Operational outcome of the CTFE body: in a concrete const block (such as
  `const { assert!(N < 1000) }`), `evalOk` holds iff the assertion succeeds
  without panicking (`TerminatorKind::Assert`) and produces `()`. -/
  evalOk : Bool

/-- The operational CTFE machine (`ConstMirMachine cb`) for a `ConstMirBody`.
In 1 step, if `cb.evalOk = true` it terminates with `.done ()`, and if
`cb.evalOk = false` (representing a failed `const { assert!(...) }` panic or
unsupported CTFE operation) it transitions to `.stuck`. -/
def ConstMirMachine (cb : ConstMirBody) : SmallStepMachine where
  Init := Unit
  State := Unit
  Ret := Unit
  initState _ := ()
  step _ := if cb.evalOk then .done () else .stuck

/-- **CTFE Admissibility (`CtfeAdmitted`):**
Following Round 1 WS3 (`PmeMirSemantics.lean`), a `ConstMirBody` is admitted by
CTFE iff `BehaviorOf (ConstMirMachine cb)` is well-formed on all fuel queries
(`WellFormedOn (fun _ => True)`) and eventually terminates with `()` at some
fuel bound `N`. -/
def CtfeAdmitted (cb : ConstMirBody) : Prop :=
  (∀ n : Nat, (BehaviorOf (ConstMirMachine cb) ⟨n, ()⟩).defined) ∧
  ∃ n : Nat,
    ReachesPrefix (ConstMirMachine cb) n () (some ())

/-- Helper lemma: if `ConstMirMachine cb` reaches `some ()` in `n` steps from
state `s`, then `cb.evalOk = true`. -/
theorem reachesPrefix_constMir_some_imp (cb : ConstMirBody)
    {n : Nat} {s : (ConstMirMachine cb).State} {out : Option Unit}
    (hreach : ReachesPrefix (ConstMirMachine cb) n s out)
    (hout : out = some ()) :
    cb.evalOk = true := by
  cases hreach with
  | zero => cases hout
  | done _ _ _ hstep =>
    simp only [ConstMirMachine] at hstep
    cases heq : cb.evalOk
    · rw [heq] at hstep; cases hstep
    · rfl
  | step _ _ _ _ hstep _ =>
    simp only [ConstMirMachine] at hstep
    cases heq : cb.evalOk <;> rw [heq] at hstep <;> cases hstep

/-- Constructive characterization: `CtfeAdmitted cb` holds iff
`cb.evalOk = true`. -/
theorem ctfeAdmitted_iff_evalOk (cb : ConstMirBody) :
    CtfeAdmitted cb ↔ cb.evalOk = true := by
  constructor
  · intro h
    cases h.2 with
    | intro n hreach =>
      exact reachesPrefix_constMir_some_imp cb hreach rfl
  · intro heval
    refine ⟨?_, ⟨1, ReachesPrefix.done (M := ConstMirMachine cb) 0 () () ?_⟩⟩
    · intro n
      cases n with
      | zero => exact ⟨none, ReachesPrefix.zero (M := ConstMirMachine cb) ()⟩
      | succ k =>
        refine ⟨some (),
          ReachesPrefix.done (M := ConstMirMachine cb) k () () ?_⟩
        simp [ConstMirMachine, heval]
    · simp [ConstMirMachine, heval]

/-- Model of a runtime MIR function body (`MirBody`).
Includes `requiredConsts : List ConstMirBody` (all `mir::Const::Unevaluated`
blocks reachable from the body) and `localLayoutOk : Prop` (well-formedness and
`is_sized` / architecture size-bound checks on all local declarations). -/
structure MirBody where
  name : String
  requiredConsts : List ConstMirBody
  localLayoutOk : Prop
  /-- Runtime operational machine for the function body. -/
  runtimeStep : Nat → StepResult Nat Nat

/-- **Compile-Time Admissibility (`MirBody.CompileAdmitted`):**
A `MirBody` is compile-admitted (free of Post-Monomorphization Errors) iff all
locals pass layout/size validation (`localLayoutOk`) and every reachable inline
`const { ... }` block (`cb ∈ body.requiredConsts`) satisfies
`CtfeAdmitted cb`. -/
def MirBody.CompileAdmitted (body : MirBody) : Prop :=
  body.localLayoutOk ∧ ∀ cb, cb ∈ body.requiredConsts → CtfeAdmitted cb

/-- Operational small-step machine for a runtime `MirBody`. -/
def MirRuntimeMachine (body : MirBody) : SmallStepMachine where
  Init := Nat
  State := Nat
  Ret := Nat
  initState x := x
  step s := body.runtimeStep s

/-- The source MIR language (`MirLang`). -/
abbrev MirLang : Language where
  Prog := MirBody
  Query := ExecQuery Nat
  Obs := ExecObs Nat
  sem body := BehaviorOf (MirRuntimeMachine body)

/-- Shorthand for runtime MIR semantics `MirLang.sem`. -/
abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

/-- Abstract target artifact and target language (`TargetLang`), mirroring
`Trusted/MirSemantics.lean`. -/
opaque TargetArtifact : Type

opaque TargetSem :
    TargetArtifact → Behavior (ExecQuery Nat) (ExecObs Nat) :=
  fun _ _ => Partial.ub

abbrev TargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery Nat
  Obs := ExecObs Nat
  sem := TargetSem

/-- **Partial `rustc` Lowering (`rustc : MirBody → Partial TargetArtifact`):**
Because `rustc` rejects functions that trigger Post-Monomorphization Errors
(CTFE `const { assert!(...) }` panics or layout overflows) during codegen,
`rustc` is modeled honestly as a partial map `MirBody → Partial TargetArtifact`
rather than a total function `MirBody → TargetArtifact`. -/
opaque rustc : MirBody → Partial TargetArtifact :=
  fun _ => Partial.ub

/-- Target-to-source behavior projection map `π_c`. -/
opaque π_c : MirLang.Behavior → TargetLang.Behavior :=
  fun _ _ => Partial.ub

/-- The `rustc` compiler pass from `MirLang` to `TargetLang`. -/
abbrev RustcMirCompiler : Compiler MirLang TargetLang where
  compile := rustc
  π := π_c

/-- **Unified `rustc` Lowering Soundness (`RustcLoweringSound`):**
Combines two orthogonal compiler guarantees for `body : MirBody`:
1. `RustcMirCompiler.SoundOn body`: `π_c` is monotone, and for every defined
   target artifact `h : (rustc body).defined`, `(rustc body).val h` refines
   `MirSem body` through `π_c`.
2. `(rustc body).defined → body.CompileAdmitted`: successful compilation by
   `rustc` implies that `body` passed all compile-time PME gates (layout checks
   and `CtfeAdmitted` on all `requiredConsts`). -/
def RustcLoweringSound (body : MirBody) : Prop :=
  RustcMirCompiler.SoundOn body ∧
  ((rustc body).defined → body.CompileAdmitted)

/-- Trust boundary items matching `Trusted/MirSemantics.lean`. -/
inductive TCBItem where
  | rustcLowering (fnName : String) (body : MirBody)
  | coreLibrarySpecs
  | userAxiom (name : String) (fact : Prop)

instance : TrustedAssumption TCBItem where
  meaning
    | .rustcLowering _ body => RustcLoweringSound body
    | .coreLibrarySpecs     => True
    | .userAxiom _ fact     => fact

def defaultTrustPolicy : TrustPolicy TCBItem
  | .rustcLowering _ _ => True
  | .coreLibrarySpecs  => True
  | .userAxiom _ _     => False

/-- **Bridge Lemma 1 (Source Conditional Equivalence via `Behavior.given`):**
Refining the PME-gated specification
`MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post`
is definitionally equal to refining
`Behavior.given body.CompileAdmitted (MirLang.SpecOn pre post)`
and constructively equivalent to the conditional proof obligation
`body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post`. -/
theorem mirSem_le_specOn_compileAdmitted_iff (body : MirBody)
    (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop) :
    MirSem body ≤ MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post ↔
      (body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post) := by
  rw [Behavior.specOn_and_eq_given MirLang]
  exact Behavior.behavior_le_given_iff

/-- **Bridge Lemma 2 (`Compiler.Verified` under `CompileAdmitted`):**
If `RustcLoweringSound body` holds and `body` refines `MirLang.SpecOn pre post`
assuming `body.CompileAdmitted`, then `RustcMirCompiler.Verified` holds for the
PME-gated specification
`MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post`. -/
theorem verified_compileAdmitted_of_cond (body : MirBody)
    (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop)
    (h_lowering : RustcLoweringSound body)
    (h_cond : body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post) :
    RustcMirCompiler.Verified body
      (MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post) := by
  have h_src :
      MirSem body ≤
        MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post :=
    (mirSem_le_specOn_compileAdmitted_iff body pre post).mpr h_cond
  exact h_lowering.1.verify h_src

/-- **Bridge Lemma 3 (`VerificationResultOn` Envelope under
`CompileAdmitted`):**
Packages `verified_compileAdmitted_of_cond` into the `VerificationResultOn`
envelope used by `Trusted.CrateTheorem`. -/
theorem verificationResultOn_compileAdmitted_of_cond (body : MirBody)
    (tcb : List TCBItem)
    (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop)
    (h_policy : ∀ item, item ∈ tcb → defaultTrustPolicy item)
    (h_in_tcb : TCBItem.rustcLowering body.name body ∈ tcb)
    (h_cond : body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post) :
    VerificationResultOn RustcMirCompiler defaultTrustPolicy tcb body
      (fun q => body.CompileAdmitted ∧ pre q)
      [MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post] := by
  refine ⟨h_policy, fun h_tcb => ?_⟩
  have h_lowering : RustcLoweringSound body :=
    h_tcb (TCBItem.rustcLowering body.name body) h_in_tcb
  have hv : RustcMirCompiler.Verified body
      (MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post) :=
    verified_compileAdmitted_of_cond body pre post h_lowering h_cond
  refine ⟨hv.with_wellFormedOn, ?_⟩
  intro spec hmem
  cases hmem with
  | head => exact hv
  | tail _ hnil => cases hnil

/-- **Crown Jewel Bridge Theorem (`target_discharges_compileAdmitted`):**
Suppose `body` is verified at the source level under the PME-gated precondition
`fun q => body.CompileAdmitted ∧ pre q` (equivalently, under the hypothesis
`body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post`), and
`TCBItem.rustcLowering body.name body` (`RustcLoweringSound body`) holds.

Then for **any compiled target artifact** `h_comp : (rustc body).defined`:
1. `body.CompileAdmitted` is **automatically discharged**
   (`h_lowering.2 h_comp`),
2. The **un-gated** source specification `MirSem body ≤ MirLang.SpecOn pre post`
   holds unconditionally,
3. `(rustc body).val h_comp` refines `body` through `RustcMirCompiler.π`, and
4. `(rustc body).val h_comp` satisfies the **un-gated** target specification
   `TargetLang.sem ((rustc body).val h_comp) ≤`
   `RustcMirCompiler.π (MirLang.SpecOn pre post)`,
   requiring only the runtime precondition `pre` and no longer mentioning
   `body.CompileAdmitted`! -/
theorem target_discharges_compileAdmitted (body : MirBody)
    (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop)
    (h_lowering : RustcLoweringSound body)
    (h_src :
      MirSem body ≤
        MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post)
    (h_comp : (rustc body).defined) :
    body.CompileAdmitted ∧
    MirSem body ≤ MirLang.SpecOn pre post ∧
    Compiles MirLang TargetLang RustcMirCompiler.π
      body ((rustc body).val h_comp) ∧
    TargetLang.sem ((rustc body).val h_comp) ≤
      RustcMirCompiler.π (MirLang.SpecOn pre post) := by
  -- Step 1: Extract `body.CompileAdmitted` from `(rustc body).defined`.
  have h_adm : body.CompileAdmitted := h_lowering.2 h_comp
  -- Step 2: Discharge `Behavior.given body.CompileAdmitted` on the source spec.
  have h_src_given :
      MirSem body ≤
        Behavior.given body.CompileAdmitted (MirLang.SpecOn pre post) := by
    rw [← Behavior.specOn_and_eq_given MirLang]
    exact h_src
  have h_src_uncond : MirSem body ≤ MirLang.SpecOn pre post :=
    Behavior.le_of_le_given_of_true h_src_given h_adm
  -- Step 3: Apply `RustcMirCompiler.SoundOn body` at `h_comp`.
  have h_compiles :
      Compiles MirLang TargetLang RustcMirCompiler.π
        body ((rustc body).val h_comp) :=
    h_lowering.1.2 h_comp
  -- Step 4: Push `h_src_uncond` through `Monotone RustcMirCompiler.π`.
  have h_target :
      TargetLang.sem ((rustc body).val h_comp) ≤
        RustcMirCompiler.π (MirLang.SpecOn pre post) :=
    Preorder.le_trans h_compiles (h_lowering.1.1 h_src_uncond)
  exact ⟨h_adm, h_src_uncond, h_compiles, h_target⟩

/-- **Corollary (`target_verifiedTotal_unconditional_of_compiled`):**
Whenever `rustc` succeeds on `body` (`h_comp : (rustc body).defined`), a
PME-conditioned source proof
`body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post`
lifts all the way to
`RustcMirCompiler.VerifiedTotal body (MirLang.SpecOn pre post)`
for the un-gated specification `MirLang.SpecOn pre post`! -/
theorem target_verifiedTotal_unconditional_of_compiled (body : MirBody)
    (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop)
    (h_lowering : RustcLoweringSound body)
    (h_cond : body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post)
    (h_comp : (rustc body).defined) :
    RustcMirCompiler.VerifiedTotal body (MirLang.SpecOn pre post) := by
  have h_src :
      MirSem body ≤
        MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post :=
    (mirSem_le_specOn_compileAdmitted_iff body pre post).mpr h_cond
  have h_dis :=
    target_discharges_compileAdmitted body pre post h_lowering h_src h_comp
  exact ⟨h_comp, h_lowering.1.verify h_dis.2.1⟩

-- ============================================================================
-- Section 5: Reconciliation with WS6's `MonoMirSem` (`Behavior.require`) and
--            `unifiedTotalPre` (`q.steps = 0`)
-- ============================================================================

/-- A monomorphized MIR compilation unit (`MonoMirUnit`) as in Round 1 WS6:
pairs a `body : MirBody` with its compile-time admissibility predicate
`pmeOk := body.CompileAdmitted`. -/
structure MonoMirUnit where
  body : MirBody

/-- The PME admissibility predicate of a `MonoMirUnit`. -/
def MonoMirUnit.pmeOk (u : MonoMirUnit) : Prop :=
  u.body.CompileAdmitted

/-- **WS6's Demonic Monomorphized Semantics (`MonoMirSem`):**
Gates `MirSem u.body` demonically on `u.pmeOk` via `Behavior.require`. -/
def MonoMirSem (u : MonoMirUnit) : MirLang.Behavior :=
  Behavior.require u.pmeOk (MirSem u.body)

/-- Definitional identity: `MonoMirSem u` is
`Behavior.require u.pmeOk (MirSem u.body)`. -/
theorem monoMirSem_eq_require (u : MonoMirUnit) :
    MonoMirSem u = Behavior.require u.pmeOk (MirSem u.body) := rfl

/-- The monomorphized MIR language (`MonoMirLang`) whose program semantics is
`MonoMirSem`. -/
abbrev MonoMirLang : Language where
  Prog := MonoMirUnit
  Query := ExecQuery Nat
  Obs := ExecObs Nat
  sem := MonoMirSem

/-- **WS6's `unifiedTotalPre`:**
Augments a caller runtime precondition `pre` with `q.steps = 0`.
Because `BehaviorOf M q` is **always defined at `q.steps = 0`**
(`behaviorOf_defined_at_zero`), requiring `MonoMirSem u` to refine a
specification over `unifiedTotalPre pre` forces `MonoMirSem u` to be defined at
`q.steps = 0`—which extracts `u.pmeOk` (`u.body.CompileAdmitted`) even if `pre`
is otherwise unsatisfiable! -/
def unifiedTotalPre (pre : ExecQuery Nat → Prop) (q : ExecQuery Nat) : Prop :=
  q.steps = 0 ∨ pre q

/-- Compatibility of a postcondition `post` at 0 steps: at `q.steps = 0`,
execution can only observe `.outOfFuel`, so `post q .outOfFuel` holds. -/
def PostZeroCompatible
    (post : ExecQuery Nat → ExecObs Nat → Prop) : Prop :=
  ∀ init : Nat, post ⟨0, init⟩ .outOfFuel

/-- **Exact Algebraic Characterization of WS6's `MonoMirSem` +
`unifiedTotalPre`:**
When `post` is compatible with 0-step fuel exhaustion
(`PostZeroCompatible post`),
`MonoMirSem u ≤ MirLang.SpecOn (unifiedTotalPre pre) post` holds iff
**both** `u.pmeOk` (`u.body.CompileAdmitted`) holds **and** `MirSem u.body`
refines `MirLang.SpecOn pre post`! -/
theorem monoMirSem_le_unifiedTotalPre_iff (u : MonoMirUnit)
    (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop)
    (hpost₀ : PostZeroCompatible post) :
    MonoMirSem u ≤ MirLang.SpecOn (unifiedTotalPre pre) post ↔
      u.pmeOk ∧ MirSem u.body ≤ MirLang.SpecOn pre post := by
  have hq₀ :
      (MirLang.SpecOn (unifiedTotalPre pre) post ⟨0, 0⟩).defined :=
    Or.inl rfl
  rw [MonoMirSem, Behavior.behavior_require_le_iff_of_defined hq₀]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro q hpre
    exact h.2 q (Or.inr hpre)
  · intro h
    refine ⟨h.1, ?_⟩
    intro q htotal
    cases htotal with
    | inl hzero =>
      cases q with
      | mk steps init =>
        cases hzero
        have hdef₀ :=
          behaviorOf_defined_at_zero (MirRuntimeMachine u.body) ⟨0, init⟩ rfl
        refine ⟨hdef₀, ?_⟩
        intro obs hobs
        cases obs with
        | outOfFuel => exact hpost₀ init
        | returned ret => cases hobs
    | inr hpre =>
      exact h.2 q hpre

/-- **Reconciling WS3 (`Behavior.given`) and WS6 (`Behavior.require`):**
In `MonoMirLang`, gating the specification by `Behavior.given u.pmeOk`
neutralizes the demonic `Behavior.require u.pmeOk` on the left-hand side of `≤`,
yielding the exact same conditional refinement obligation
`u.pmeOk → MirSem u.body ≤ MirLang.SpecOn pre post` as `MirLang`! -/
theorem monoMirSem_le_given_pmeOk_iff_mirSem_le_given (u : MonoMirUnit)
    (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop) :
    MonoMirSem u ≤ Behavior.given u.pmeOk (MirLang.SpecOn pre post) ↔
      MirSem u.body ≤
        MirLang.SpecOn (fun q => u.body.CompileAdmitted ∧ pre q) post := by
  rw [MonoMirSem, Behavior.behavior_le_given_iff,
    Behavior.behavior_require_le_iff,
    mirSem_le_specOn_compileAdmitted_iff, MonoMirUnit.pmeOk]
  constructor
  · intro h hpme
    exact (h hpme).2 hpme
  · intro h hpme
    exact ⟨fun _ _ => hpme, fun _ => h hpme⟩

-- ============================================================================
-- Section 6: End-to-End Concrete Verification & `#print axioms` Audit
-- ============================================================================

/-- Concrete worked example: a monomorphized instance of a generic Rust function
```rust
pub fn const_bounded_add<const N: usize>(x: usize) -> usize {
    const { assert!(N < 1000); }
    x + N
}
```
Here `N` is a generic parameter, the inline `const { assert!(N < 1000) }` block
is captured as `constBlockBoundedN N`, the caller precondition is `x ≤ 500`, and
the postcondition is `ret < 1500`. -/
def constBlockBoundedN (N : Nat) : ConstMirBody where
  id := "const_bounded_add::const_assert_0"
  evalOk := decide (N < 1000)

/-- Constructive proof that `CtfeAdmitted (constBlockBoundedN N)` holds iff
`N < 1000`. -/
theorem ctfeAdmitted_constBlockBoundedN_iff (N : Nat) :
    CtfeAdmitted (constBlockBoundedN N) ↔ N < 1000 := by
  rw [ctfeAdmitted_iff_evalOk, constBlockBoundedN]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- The captured `MirBody` for `const_bounded_add<N>`.
If `x + N < 2000` (modeling absence of arithmetic overflow in the toy machine),
it returns `x + N` in one step; otherwise it gets stuck. -/
def constBoundedAddBody (N : Nat) : MirBody where
  name := "const_bounded_add"
  requiredConsts := [constBlockBoundedN N]
  localLayoutOk := True
  runtimeStep x :=
    if x + N < 2000 then .done (x + N) else .stuck

/-- For `constBoundedAddBody N`, `CompileAdmitted` implies `N < 1000`. -/
theorem compileAdmitted_constBoundedAdd_imp (N : Nat)
    (h_adm : (constBoundedAddBody N).CompileAdmitted) :
    N < 1000 := by
  have h_ctfe : CtfeAdmitted (constBlockBoundedN N) :=
    h_adm.2 (constBlockBoundedN N) (List.Mem.head _)
  exact (ctfeAdmitted_constBlockBoundedN_iff N).mp h_ctfe

/-- Caller precondition `x ≤ 500`. -/
def boundedAddPre (q : ExecQuery Nat) : Prop :=
  q.init ≤ 500

/-- Postcondition: whenever execution returns `ret`, `ret < 1500`. -/
def boundedAddPost (_ : ExecQuery Nat) (obs : ExecObs Nat) : Prop :=
  match obs with
  | .outOfFuel    => True
  | .returned ret => ret < 1500

/-- Elementary arithmetic helper for the concrete example (proved directly from
`Nat.add_le_add` in `Init` without requiring `Init.Omega`). -/
theorem add_lt_1500_of_le_500_of_lt_1000 {x N : Nat}
    (hx : x ≤ 500) (hN : N < 1000) : x + N < 1500 := by
  have h1 : x + N ≤ 500 + N := Nat.add_le_add_right hx N
  have h2 : 500 + N < 500 + 1000 := Nat.add_lt_add_left hN 500
  exact Nat.lt_of_le_of_lt h1 h2

/-- **Source Proof of `constBoundedAddBody N` Conditional on
`CompileAdmitted`:**
For **every** `N : Nat` (even `N ≥ 1000` where `rustc` would fail CTFE),
assuming `(constBoundedAddBody N).CompileAdmitted`, `constBoundedAddBody N`
refines `MirLang.SpecOn boundedAddPre boundedAddPost`! -/
theorem constBoundedAdd_conditional_refines (N : Nat) :
    (constBoundedAddBody N).CompileAdmitted →
      MirSem (constBoundedAddBody N) ≤
        MirLang.SpecOn boundedAddPre boundedAddPost := by
  intro h_adm q h_pre
  have hN : N < 1000 := compileAdmitted_constBoundedAdd_imp N h_adm
  cases q with
  | mk steps x =>
    have hx : x ≤ 500 := h_pre
    have hsum : x + N < 1500 := add_lt_1500_of_le_500_of_lt_1000 hx hN
    have hsum2000 : x + N < 2000 := Nat.lt_trans hsum (by decide)
    cases steps with
    | zero =>
      dsimp [MirSem, MirLang, BehaviorOf, Language.SpecOn]
      have hzero :=
        ReachesPrefix.zero (M := MirRuntimeMachine (constBoundedAddBody N)) x
      refine ⟨⟨none, hzero⟩, ?_⟩
      intro obs hobs
      cases obs with
      | outOfFuel => trivial
      | returned ret => cases hobs
    | succ k =>
      have hstep :
          (MirRuntimeMachine (constBoundedAddBody N)).step
            ((MirRuntimeMachine (constBoundedAddBody N)).initState x) =
            .done (x + N) := by
        simp [MirRuntimeMachine, constBoundedAddBody, hsum2000]
      dsimp [MirSem, MirLang, BehaviorOf, Language.SpecOn]
      refine ⟨⟨some (x + N),
        ReachesPrefix.done (M := MirRuntimeMachine (constBoundedAddBody N))
          k x (x + N) hstep⟩, ?_⟩
      intro obs hobs
      cases obs with
      | outOfFuel => trivial
      | returned ret =>
        cases hobs with
        | done _ _ _ hstep' =>
          rw [hstep] at hstep'
          injection hstep' with hret
          subst hret
          exact hsum
        | step _ _ _ _ hstep' _ =>
          rw [hstep] at hstep'
          cases hstep'

/-- **End-to-End Target Discharge for `constBoundedAddBody N`:**
For any `N : Nat` where `rustc` actually emits a target artifact
(`h_comp : (rustc (constBoundedAddBody N)).defined`), under
`RustcLoweringSound (constBoundedAddBody N)`:
1. `(constBoundedAddBody N).CompileAdmitted` holds (and hence `N < 1000`!), and
2. `TargetLang.sem ((rustc (constBoundedAddBody N)).val h_comp)` refines
   `RustcMirCompiler.π (MirLang.SpecOn boundedAddPre boundedAddPost)` under
   `boundedAddPre` (`x ≤ 500`) alone, with `CompileAdmitted` completely
   discharged! -/
theorem constBoundedAdd_target_discharged (N : Nat)
    (h_lowering : RustcLoweringSound (constBoundedAddBody N))
    (h_comp : (rustc (constBoundedAddBody N)).defined) :
    N < 1000 ∧
    TargetLang.sem ((rustc (constBoundedAddBody N)).val h_comp) ≤
      RustcMirCompiler.π (MirLang.SpecOn boundedAddPre boundedAddPost) := by
  have h_src :
      MirSem (constBoundedAddBody N) ≤
        MirLang.SpecOn
          (fun q => (constBoundedAddBody N).CompileAdmitted ∧ boundedAddPre q)
          boundedAddPost :=
    (mirSem_le_specOn_compileAdmitted_iff
      (constBoundedAddBody N) boundedAddPre boundedAddPost).mpr
      (constBoundedAdd_conditional_refines N)
  have h_dis :=
    target_discharges_compileAdmitted
      (constBoundedAddBody N) boundedAddPre boundedAddPost
      h_lowering h_src h_comp
  exact ⟨compileAdmitted_constBoundedAdd_imp N h_dis.1, h_dis.2.2.2⟩

/-- Captured function entry in `Mir.crate.functions`, mirroring `CapturedFn` in
`Trusted/MirSemantics.lean` and Round 1 WS5 (`isPublic : Bool`). -/
structure CapturedFn where
  name : String
  isPublic : Bool
  prog : MirBody
  pre : ExecQuery Nat → Prop
  specs : List MirLang.Behavior

/-- Captured crate descriptor (`Mir.crate : Trusted.Crate`). -/
structure Crate where
  functions : List CapturedFn
  tcb : List TCBItem

/-- **Crate-Level Verification Obligation (`Trusted.CrateTheorem`):**
Following Round 1 WS5 and `Trusted/MirSemantics.lean`:
- Every public function (`fn.isPublic = true`) must satisfy
  `VerificationResultOn RustcMirCompiler defaultTrustPolicy`
  `c.tcb fn.prog fn.pre fn.specs`.
- Private helper functions (`fn.isPublic = false`) are verified organically at
  their call sites in `Proof.lean` (Statement-Origin Separation). -/
def CrateTheorem (c : Crate) : Prop :=
  ∀ fn, fn ∈ c.functions → fn.isPublic = true →
    VerificationResultOn RustcMirCompiler defaultTrustPolicy c.tcb
      fn.prog fn.pre fn.specs

/-- Concrete captured crate containing the public PME-gated function
`const_bounded_add<N>` (for an arbitrary parameter `N : Nat`). -/
def exampleCrate (N : Nat) : Crate where
  functions := [{
    name := "const_bounded_add"
    isPublic := true
    prog := constBoundedAddBody N
    pre := fun q =>
      (constBoundedAddBody N).CompileAdmitted ∧ boundedAddPre q
    specs := [
      MirLang.SpecOn
        (fun q => (constBoundedAddBody N).CompileAdmitted ∧ boundedAddPre q)
        boundedAddPost
    ]
  }]
  tcb := [
    .rustcLowering "const_bounded_add" (constBoundedAddBody N),
    .coreLibrarySpecs
  ]

/-- **Crate-Level Theorem (`Proof.verify_crate`):**
Proves `CrateTheorem (exampleCrate N)` for all `N : Nat` using our unified
bridge `verificationResultOn_compileAdmitted_of_cond`. -/
theorem verify_exampleCrate (N : Nat) : CrateTheorem (exampleCrate N) := by
  intro fn hmem _
  cases hmem with
  | head =>
    refine verificationResultOn_compileAdmitted_of_cond
      (constBoundedAddBody N) (exampleCrate N).tcb
      boundedAddPre boundedAddPost ?_ ?_
      (constBoundedAdd_conditional_refines N)
    · intro item hitem
      cases hitem with
      | head => trivial
      | tail _ htail =>
        cases htail with
        | head => trivial
        | tail _ hnil => cases hnil
    · exact List.Mem.head _
  | tail _ hnil => cases hnil

-- ============================================================================
-- Axiom Audit (`#print axioms`)
-- ============================================================================

#print axioms Behavior.behavior_when_given_adjunction
#print axioms Behavior.behavior_require_le_iff
#print axioms Behavior.behavior_require_le_iff_of_defined
#print axioms Language.semIfCompiled_le_iff
#print axioms Language.semPartial_le_iff
#print axioms Compiler.verifiedWhenCompiled_iff_verified_given
#print axioms verify_through_passes
#print axioms target_discharges_compileAdmitted
#print axioms target_verifiedTotal_unconditional_of_compiled
#print axioms monoMirSem_le_unifiedTotalPre_iff
#print axioms constBoundedAdd_target_discharged
#print axioms verify_exampleCrate

end Anneal.UnifiedPme
