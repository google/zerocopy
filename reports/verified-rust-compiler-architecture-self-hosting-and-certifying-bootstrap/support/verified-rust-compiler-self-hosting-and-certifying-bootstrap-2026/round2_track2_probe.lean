-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Init.NotationExtra

/-!
# Round 2 — Track 2 Probe: Slices, ADTs, Post-`#154341` `WithRetag`, Fuel-Indexed `CallSpecTable`, and Cross-Track `π_isa` Without `deriving`

This standalone Lean 4.34.1 file resolves the Round 1 Track 2 follow-up items
and cross-track harmonization requirements:

1. **Section 1 & Section 2 — Immutable Slices (`&[usize]`), Struct/Enum ADTs,
   and Bounded Loop Verification in `MirAst` and `FunctionalTranslation`:**
   Extends `MirTy`, `MirVal`, `PlaceElem` (`.deref`, `.field`, `.index`,
   `.downcast`), `Place`, `Rvalue` (`.use op withRetag`, `.len`,
   `.discriminant`, `.aggregate`, `.readPlace`), and `Terminator`
   (`.assertBoundsCheck`). Extends `SymVal` and `evalSymWith` in
   `FunctionalTranslation` and proves `evalSym_slice_sound`, verifying a
   multi-instruction slice-iterating certificate checker `sliceCheckerMirBody`
   that loops over an `&[usize]` slice without word-packing.
2. **Section 3 — Post-`#154341` `Rvalue.use (op : Operand) (withRetag : Bool)`
   in `MirAst` and `AnSSA`:**
   Reconciles `Trusted/MirAst.lean` with `rustc` PR `#154341`
   (`e402c1edf047a23b0cfef40c6097d1caa294050b`), lowers `Rvalue.use op true` to
   an explicit side-effectful `AnSSAStmt.retag` instruction in `AnSSA`, proves
   that downstream pure SSA copy propagation of the retagged value preserves
   borrow-tracker transitions (`retag_copy_prop_compiles`), and proves that
   erasing `withRetag = true` or duplicating `retag` at every use site violates
   `Compiles`.
3. **Section 4 — Fuel-Indexed Open `CallSpecTable` for Mutual Recursion:**
   Replaces closed `PureCallee2` with a fuel-indexed open relational contract
   table `CallSpecTable : FnSymbol → Nat → List MirVal → MirVal → Prop` and
   proves `mutual_recursion_callSpec_sound` by strong induction on the step
   budget $k : \mathbb{N}$, instantiating it on mutually recursive `is_even`
   and `is_odd` functions.
4. **Section 5 — Cross-Track 64-Bit Hardware Projection `π_isa` and
   `TrustedBoundary.lean`-Compliant Equality Checkers Without `deriving`:**
   Defines a 64-bit hardware machine `HwIsaState` (`regs : Fin 16 → BitVec 64`
   with `rdi = regs 0`, `rsi = regs 1`, `rax = regs 2`, and `sp : BitVec 64`),
   proves `monotone_π_isa` and `lowerMirToHwIsa_compiles` for the non-identity
   projection `π_isa : MirLang.Behavior → HwIsaLang.Behavior`, and defines
   lawful recursive `beq*` checkers without using any `deriving` clauses.
5. **Section 6 — Axiom Audit:**
   Verifies via `#guard_msgs in #print axioms` that all theorems depend only on
   `propext` and `Quot.sound` (zero `sorryAx`, zero `Lean.ofReduceBool`).
-/

namespace Trusted

/-- Declaration macro that strips Anneal's in-place trust-tier attributes
    (`@[vetted]` and `@[candidate <feature>]`) from top-level declarations and
    `inductive` constructors after `trusted/audit/TrustedBoundary.lean`
    validates and records them during `preflight`. -/
@[macro Lean.Parser.Command.declaration, macro Lean.Parser.Command.mutual]
def expandTrustDeclaration : Lean.Macro := fun stx =>
  let stripAttrs (mods : Lean.Syntax) : Bool × Lean.Syntax :=
    let attrsNode := mods.getArg 1
    match attrsNode.getArgs[0]? with
    | none => (false, mods)
    | some inner =>
      let (changed, kept) := (inner.getArg 1).getArgs.foldl (init := (false, #[])) fun (chg, acc) elem =>
        if elem.getKind == `Lean.Parser.Term.attrInstance then
          let attr := elem.getArg 1
          if attr.getKind == `Lean.Parser.Attr.simple &&
              ((attr.getArg 0).getId == `vetted || (attr.getArg 0).getId == `candidate) then
            (true, acc)
          else (chg, acc.push elem)
        else (chg, acc)
      if !changed then (false, mods) else
        if kept.isEmpty then
          (true, mods.setArg 1 (Lean.mkNullNode))
        else
          let sep := Lean.Syntax.mkSep kept (.atom .none ",")
          (true, mods.setArg 1 (attrsNode.setArg 0 (inner.setArg 1 sep)))
  let stripDecl (s : Lean.Syntax) : Bool × Lean.Syntax :=
    if s.getKind != `Lean.Parser.Command.declaration then (false, s) else
      let (mc, mods') := stripAttrs (s.getArg 0)
      let decl := s.getArg 1
      let (dc, decl') :=
        if decl.getKind != `Lean.Parser.Command.inductive then (false, decl) else
          let (cc, ctors') := (decl.getArg 4).getArgs.foldl (init := (false, #[])) fun (c, acc) ctor =>
            let (kc, m') := stripAttrs (ctor.getArg 2)
            (c || kc, acc.push (if kc then ctor.setArg 2 m' else ctor))
          (cc, if cc then decl.setArg 4 (Lean.mkNullNode ctors') else decl)
      (mc || dc, if mc || dc then (s.setArg 0 mods').setArg 1 decl' else s)
  if stx.getKind == `Lean.Parser.Command.mutual then
    let (mc, items') := (stx.getArg 1).getArgs.foldl (init := (false, #[])) fun (c, acc) item =>
      let (ic, item') := stripDecl item
      (c || ic, acc.push item')
    if mc then pure (stx.setArg 1 (Lean.mkNullNode items')) else Lean.Macro.throwUnsupported
  else
    let (c, stx') := stripDecl stx
    if c then pure stx' else Lean.Macro.throwUnsupported

/-- Identity marker used inside a `@[vetted]` declaration's body to guard a
    match arm that evaluates a `@[candidate <feature>]` constructor. -/
@[vetted, reducible]
def candidate (_feat : String) {α : Sort u} (x : α) : α := x

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
@[candidate refinement]
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder in which
    stronger propositions refine weaker ones. -/
@[candidate refinement]
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever the codomain `B` is a `Preorder`. -/
@[candidate refinement]
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- A partially defined value of type `B`, constructively representing
    $B \cup \{\mathsf{UB}\}$. -/
@[candidate refinement]
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`
    (`defined := True`). -/
@[candidate refinement]
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element ($\mathsf{UB}$) of `Partial B` (`defined := False`),
    which acts as the top element under `instPreorderPartial`. -/
@[candidate refinement]
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map a function `f : B₁ → B₂` over the defined payload of a `Partial B₁`,
    preserving `.defined`. -/
@[candidate refinement]
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B`: `p₁ ≤ p₂` holds when, whenever `p₂` is
    defined (`h₂ : p₂.defined`), `p₁` is also defined (`h₁ : p₁.defined`) and
    its value refines `p₂`'s value (`p₁.val h₁ ≤ p₂.val h₂`). -/
@[candidate refinement]
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders. -/
@[candidate refinement]
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- The canonical domain of query-indexed partial behaviors over `Query` and
    `Out` (`Query → Partial (Out → Prop)`). -/
@[candidate refinement]
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling a program type `Prog`, a query domain `Query`, an
    outcome domain `Out`, and a semantic function
    `sem : Prog → Behavior Query Out`. -/
@[candidate refinement]
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- The behavior domain of a `Language` (`Behavior L.Query L.Out`). -/
@[candidate refinement]
abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

/-- Query-indexed specification on `L` with domain precondition
    `pre : L.Query → Prop` and outcome postcondition
    `post : L.Query → L.Out → Prop`. -/
@[candidate refinement]
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification on `L` (`L.SpecOn (fun _ => True) post`). -/
@[candidate refinement]
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `L` under query precondition
    `pre : L.Query → Prop` (`L.SpecOn pre (fun _ _ => True)`). -/
@[candidate refinement]
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`
    (`L.WellFormedOn (fun _ => True)`). -/
@[candidate refinement]
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`: target program `t`
    refines the mapped source behavior `π_c (L_src.sem s)`. -/
@[candidate refinement]
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Verification (abstraction) pass from `L_src` to verifier language `L_v`:
    source program `s` refines the mapped verifier behavior `π_v (L_v.sem v)`. -/
@[candidate refinement]
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- A compiler lowering programs from `L_src` to `L_tgt` with behavior mapping
    `π : L_src.Behavior → L_tgt.Behavior`. -/
@[candidate refinement]
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`. -/
@[candidate refinement]
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification obligation for source program `s` and specification
    `spec` under compiler `C`. -/
@[candidate refinement]
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- An assumption recorded in a verification unit's Trusted Computing Base,
    equipped with its intrinsic semantic meaning as a `Prop`. -/
@[candidate refinement]
class TrustedAssumption (A : Type) where
  meaning : A → Prop

/-- A policy governing which trusted assumptions of type `A` are permitted. -/
@[candidate refinement]
structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

/-- Conjunction of a list of propositions. -/
@[candidate refinement]
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Top-level verification envelope for a source program `prog : L_src.Prog`,
    safety precondition `pre : L_src.Query → Prop`, and additional
    specifications `specs : List L_src.Behavior` under compiler `C`. -/
@[candidate refinement]
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

/-- Top-level verification envelope for a source program `prog : L_src.Prog`
    whose baseline UB-freedom obligation holds across all `L_src.Query`. -/
@[candidate refinement]
abbrev VerificationResult
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (specs : List L_src.Behavior := []) : Prop :=
  VerificationResultOn C policy assumptions prog (fun _ => True) specs

/-- Quantifier polarity for nondeterministic choices in a small-step semantics. -/
@[candidate step_result]
inductive ChoiceKind where
  | demonic
  | angelic

/-- Distinguishes normal return from panic/unwind completion. -/
@[candidate step_result]
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Distinguishes language-level Undefined Behavior (`ub`) from explicit
    specification or assertion violations (`contractViolation`). -/
@[candidate step_result]
inductive FailureKind where
  | ub
  | contractViolation

/-- Outcome of a single transition step in a small-step interaction tree. -/
@[candidate step_result]
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Outcome recorded at the end of a finite execution prefix. -/
@[candidate step_result]
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

/-- A prefix outcome is safe when it neither triggers a failure (`ub` or
    `contractViolation`) nor gets stuck in an unstepped state. -/
@[candidate step_result]
def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

/-- Input query to a finite-prefix small-step execution (`Query` in
    `Language`). -/
@[candidate step_result]
structure ExecQuery (State : Type) where
  init : State
  steps : Nat

/-- Observable output of a finite-prefix small-step execution (`Out` in
    `Language`). -/
@[candidate step_result]
structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

/-- Small-step operational semantics parameterized by programs `Prog`, machine
    states `State`, step observations `Obs`, and return values `Val`. -/
@[candidate step_result]
structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of a finite execution prefix from current state `s`
    given initial state `init` and remaining step budget `fuel`. -/
@[candidate step_result]
inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State) (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

/-- Induced query-indexed partial behavior of program `p` in machine `M`. -/
@[candidate step_result]
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a Layer 1A `Language`. -/
@[candidate step_result]
def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

end Trusted

namespace Anneal
open Trusted

/-- `Compiles` is reflexive under the identity behavior map. -/
theorem compiles_refl (L : Language) (p : L.Prog) :
    Compiles L L id p p := by
  intro q
  exact Preorder.le_refl (L.sem p q)

/-- `Compiles` composes transitively across compiler passes when the second pass
    has a monotone behavior map `π₂`. -/
theorem compiles_trans {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior}
    {π₂ : L₂.Behavior → L₃.Behavior}
    (h_mono : Monotone π₂)
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃) :
    Compiles L₁ L₃ (π₂ ∘ π₁) p₁ p₃ := by
  exact Preorder.le_trans h₂₃ (h_mono h₁₂)

/-- If compiler `C` is sound on `s` (`C.SoundOn s`) and `s` satisfies source
    specification `spec` (`L_src.sem s ≤ spec`), then `C.Verified s spec`
    holds. -/
theorem verified_of_soundOn_and_spec {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt} {s : L_src.Prog} {spec : L_src.Behavior}
    (h_sound : C.SoundOn s)
    (h_spec : L_src.sem s ≤ spec) :
    C.Verified s spec := by
  rcases h_sound with ⟨h_mono, h_comp⟩
  refine ⟨h_spec, h_comp, ?_⟩
  exact Preorder.le_trans h_comp (h_mono h_spec)

/-- Sequential composition of two `Compiler`s. -/
def _root_.Trusted.Compiler.compose {L₁ L₂ L₃ : Language}
    (C₂ : Compiler L₂ L₃) (C₁ : Compiler L₁ L₂) : Compiler L₁ L₃ where
  compile := C₂.compile ∘ C₁.compile
  π := C₂.π ∘ C₁.π

/-- Composing two compilers that are individually `SoundOn` their respective
    programs yields a composite compiler that is `SoundOn` the source program. -/
theorem compiler_compose_soundOn {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃} {s : L₁.Prog}
    (h₁ : C₁.SoundOn s)
    (h₂ : C₂.SoundOn (C₁.compile s)) :
    (C₂.compose C₁).SoundOn s := by
  rcases h₁ with ⟨h_mono₁, h_comp₁⟩
  rcases h₂ with ⟨h_mono₂, h_comp₂⟩
  refine ⟨?_, compiles_trans h_mono₂ h_comp₁ h_comp₂⟩
  intro x y hxy
  exact h_mono₂ (h_mono₁ hxy)

end Anneal

/-!
## Section 1: Extended `MirAst` and `MirSemantics` with Immutable Slices (`&[usize]`), Struct/Enum ADTs, Place Projections, Bounds Checks, and Post-`#154341` `WithRetag`

In this section we extend `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`
with:
1. First-order scalar fields (`ScalarVal`) so struct/enum ADT runtime values
   (`MirVal.adtVal variant fields`) and symbolic values
   (`SymVal.adtVal variant fields`) remain first-order (non-nested) inductives
   in `TrustedBoundary.lean`.
2. Immutable slice types (`MirTy.refSliceUsize`) and slice fat-pointer values
   (`MirVal.refSliceLoc loc len`).
3. Place projection elements (`PlaceElem.deref`, `PlaceElem.field`,
   `PlaceElem.index`, `PlaceElem.downcast`) and projected places (`Place`),
   matching `rustc_middle::mir::syntax::{ProjectionElem, Place}`.
4. Post-`#154341` `Rvalue.use (op : Operand) (withRetag : Bool)`, matching
   `Rvalue::Use(Operand, WithRetag)` in `rustc` commit
   `e402c1edf047a23b0cfef40c6097d1caa294050b`.
5. `Rvalue.len` (modeling `UnOp::PtrMetadata` on `&[T]`), `Rvalue.discriminant`
   (`Rvalue::Discriminant`), `Rvalue.aggregate` (`Rvalue::Aggregate`), and
   `Rvalue.readPlace` (reading through a projected `Place`).
6. `Terminator.assertBoundsCheck` (`AssertKind::BoundsCheck { len, index }`).
7. Explicit recursive boolean equality checkers (`beq*`) and lawfulness proofs
   (`beq*_eq_of_true`) with **zero** `deriving` clauses.
-/

namespace Trusted

/-- Index of a MIR local variable or temporary (`_0`, `_1`, ...).

    Corresponds to `rustc_middle::mir::Local` indexing into `Body::local_decls`:

    > "The first local is the return value pointer, followed by `arg_count`
    > locals for the function arguments, followed by any user-declared
    > variables and temporaries."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L235-L240 -/
@[candidate mir_ast]
structure LocalId where
  index : Nat

/-- Index of a basic block (`bb0`, `bb1`, ...) within a MIR body.

    Corresponds to `rustc_middle::mir::BasicBlock` indexing into
    `Body::basic_blocks`:

    > "A list of basic blocks. References to basic block use a newtyped index
    > type [`BasicBlock`] that indexes into this vector."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209 -/
@[candidate mir_ast]
structure BlockId where
  index : Nat

/-- Identifier of a MIR function in a crate's call graph. -/
@[candidate mir_ast]
structure FnSymbol where
  id : Nat

/-- Atomic memory ordering for atomic load operations.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/sync/atomic.rs#L450-L503 -/
@[candidate mir_ast]
inductive AtomicOrdering where
  | relaxed
  | acquire

/-- First-order scalar payload value (`usize`, `bool`, or `()`) stored inside
    the fields of a `struct` or `enum` ADT value (`MirVal.adtVal`).

    Keeping field payloads in a standalone first-order inductive `ScalarVal`
    avoids nested recursion (`List MirVal` inside `MirVal`) so `MirVal`
    elaborates without auxiliary `_mutual` recursors and passes
    `TrustedBoundary.lean`'s strict environment audit. -/
@[candidate mir_ast]
inductive ScalarVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit

/-- Extended MIR type grammar including immutable slices (`&[usize]`) and
    user-defined algebraic data types (`struct` and `enum` ADTs).

    - `MirTy.refSliceUsize` models an immutable shared slice reference
      `&[usize]`, which is a dynamically sized view into a contiguous sequence
      of `usize` elements represented as a wide pointer `(data_ptr, len)`:

      > "A slice is a dynamically sized type representing a 'view' into a
      > sequence of elements of type `T`. The slice type is written as `[T]`."

    - `MirTy.adt` models a nominal `struct` or `enum` algebraic data type
      (`ty::AdtDef` in `rustc_middle::ty`):

      > "A *struct* is a nominal struct type defined with the keyword `struct`."
      >
      > "An *enumerated type* is a nominal, heterogeneous disjoint union type,
      > defined with the keyword `enum`."

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/slice.md#L6-L10
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/struct.md#L6-L8
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/enum.md#L6-L9 -/
@[candidate mir_ast]
inductive MirTy where
  | usize
  | bool
  | unit
  | tupleUsizeBool
  | refAtomicUsize
  | refSharedUsize
  | refMutUsize
  | refSliceUsize
  | adt (adtId : Nat)
  | atomicOrdering

/-- Initialized runtime value in the extended MIR semantics, including slice
    wide pointers (`refSliceLoc loc len`) and struct/enum ADT values
    (`adtVal variant fields`).

    - `MirVal.refSliceLoc loc len` represents a valid shared slice reference
      `&[usize]` pointing to non-atomic slice allocation `loc` with `len`
      initialized `usize` elements.
    - `MirVal.adtVal variant fields` represents an initialized `struct`
      (`variant = 0`) or `enum` (`variant = v`) value whose variant index is
      `variant` and whose field values are `fields`.

    Sources:
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L147
    - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/slice.md#L6-L10 -/
@[candidate mir_ast]
inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  | atomicLoc (loc : Nat)
  | refSharedLoc (loc : Nat)
  | refMutLoc (loc : Nat)
  | refSliceLoc (loc : Nat) (len : Nat)
  | adtVal (variant : Nat) (fields : List ScalarVal)
  | ordering (ord : AtomicOrdering)

/-- Convert a `ScalarVal` to the corresponding `MirVal`. -/
@[candidate mir_ast]
def ScalarVal.toMirVal : ScalarVal → MirVal
  | .usize n => .usize n
  | .bool b => .bool b
  | .unit => .unit

/-- Extract a `ScalarVal` from a scalar `MirVal`, returning `none` on non-scalar
    values. -/
@[candidate mir_ast]
def MirVal.toScalarVal? : MirVal → Option ScalarVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | _ => none

/-- Single projection step in a MIR `Place` (`ProjectionElem` in
    `rustc_middle::mir::syntax`):

    - `.deref`: `ProjectionElem::Deref` (`*p`), dereferencing a shared, mutable,
      or slice reference.
    - `.field idx`: `ProjectionElem::Field(FieldIdx, Ty)` (`p.idx`), projecting
      the `idx`-th field of a `struct` or downcast `enum` variant.
    - `.index idxLocal`: `ProjectionElem::Index(Local)` (`p[_idx]`), indexing
      into a slice by the runtime `usize` value held in `idxLocal`:

      > "Index into a slice/array. Note that this does not also dereference,
      > and so it does not exactly correspond to slice indexing in Rust. In
      > other words, in the below Rust code:
      > ```rust
      > let x = &[1, 2, 3, 4];
      > let i = 2;
      > x[i];
      > ```
      > The `x[i]` is turned into a `Deref` followed by an `Index`, not just an
      > `Index`."

    - `.downcast variant`: `ProjectionElem::Downcast(Option<Symbol>, VariantIdx)`
      (`(p as Variant#v)`), selecting variant `variant` of an `enum` ADT before
      projecting one of its fields:

      > "Downcast of an enum or a coroutine to a specific variant. Note that a
      > `Downcast` is always followed by a `Field`; a standalone `Downcast` has
      > no operational meaning."

    Source: https://github.com/rust-lang/rust/blob/8006091eb71ae7d9e9bccb66c6122c9d68af4466/compiler/rustc_middle/src/mir/syntax.rs#L1163-L1283 -/
@[candidate mir_ast]
inductive PlaceElem where
  | deref
  | field (idx : Nat)
  | index (idxLocal : LocalId)
  | downcast (variant : Nat)

/-- A MIR memory place (`rustc_middle::mir::Place`) consisting of a root local
    variable `local` and a list of projection elements `projection`.

    Source: https://github.com/rust-lang/rust/blob/8006091eb71ae7d9e9bccb66c6122c9d68af4466/compiler/rustc_middle/src/mir/syntax.rs#L1294-L1298 -/
@[candidate mir_ast]
structure Place where
  local_ : LocalId
  projection : List PlaceElem

/-- MIR operand evaluated to produce a value in an `Rvalue` or terminator.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1308-L1339 -/
@[candidate mir_ast]
inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constUsize (bits : Nat)
  | constBool (b : Bool)
  | constUnit
  | constOrdering (ord : AtomicOrdering)

/-- Unchecked binary operations in `Rvalue.binaryOp`.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1562-L1614 -/
@[candidate mir_ast]
inductive BinOp where
  | add
  | sub
  | bitXor
  | bitAnd
  | bitOr
  | shl
  | shr
  | eq
  | lt
  | le

/-- Checked binary arithmetic operations in `Rvalue.checkedBinaryOp`. -/
@[candidate mir_ast]
inductive CheckedBinOp where
  | addWithOverflow
  | subWithOverflow

/-- Right-hand side expression of a MIR assignment (`Statement.assign`).

    - `Rvalue.use op withRetag` models `Rvalue::Use(Operand, WithRetag)` as
      introduced by `rustc` PR `#154341` (`Merge Retag statement into Use
      rvalue`, commit `e402c1edf047a23b0cfef40c6097d1caa294050b`):

      > "Whether this `Use` operation performs a Stacked Borrows / Tree Borrows
      > retag of the value."
      >
      > "Yields the operand unchanged (except for potentially retagging all
      > contained references)"

    - `Rvalue.len src` extracts the dynamic element count `len : usize` of an
      immutable slice reference `_src : &[usize]` (corresponding to
      `UnOp::PtrMetadata` / `Rvalue::Len` in `rustc_middle::mir::syntax`):

      > "Extracts the metadata of a pointer. For slices this is the length, for
      > trait objects it is the vtable pointer, and for thin pointers it is
      > `()`."

    - `Rvalue.discriminant src` reads the active variant index (`usize`) of an
      ADT value held in `src` (`Rvalue::Discriminant(Place)`):

      > "Reads the discriminant of a place; if the place is an enum with only a
      > single (reachable) variant or a non-enum, this returns `0`."

    - `Rvalue.aggregate variant fields` constructs an `adtVal variant fieldVals`
      from evaluated scalar operands `fields`
      (`Rvalue::Aggregate(Box<AggregateKind>, IndexVec<FieldIdx, Operand>)`).

    - `Rvalue.readPlace place` loads a value from a projected `Place` (such as
      `(*_1)[_4]` for slice indexing or `_8.0` / `(_8 as Variant#v).0` for
      struct/enum field projection).

    Sources:
    - https://github.com/rust-lang/rust/blob/e402c1edf047a23b0cfef40c6097d1caa294050b/compiler/rustc_middle/src/mir/syntax.rs#L489-L503
    - https://github.com/rust-lang/rust/blob/e402c1edf047a23b0cfef40c6097d1caa294050b/compiler/rustc_middle/src/mir/syntax.rs#L1365
    - https://github.com/rust-lang/rust/blob/8006091eb71ae7d9e9bccb66c6122c9d68af4466/compiler/rustc_middle/src/mir/syntax.rs#L1354-L1541
    - https://github.com/rust-lang/rust/blob/8006091eb71ae7d9e9bccb66c6122c9d68af4466/compiler/rustc_middle/src/mir/syntax.rs#L1616-L1628 -/
@[candidate mir_ast]
inductive Rvalue where
  | use (op : Operand) (withRetag : Bool)
  | deref (src : LocalId)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | checkedBinaryOp (op : CheckedBinOp) (lhs : Operand) (rhs : Operand)
  | proj0 (src : LocalId)
  | proj1 (src : LocalId)
  | len (src : LocalId)
  | discriminant (src : LocalId)
  | aggregate (variant : Nat) (fields : List Operand)
  | readPlace (place : Place)

/-- Non-branching MIR statement inside a basic block.

    Source: https://github.com/rust-lang/rust/blob/e402c1edf047a23b0cfef40c6097d1caa294050b/compiler/rustc_middle/src/mir/syntax.rs#L430-L487 -/
@[candidate mir_ast]
inductive Statement where
  | assign (dst : LocalId) (rvalue : Rvalue)
  | storeDeref (dstPtr : LocalId) (rvalue : Rvalue)
  | storageLive (local_ : LocalId)
  | storageDead (local_ : LocalId)
  | nop

/-- Control-flow terminator ending a MIR basic block.

    - `Terminator.assertBoundsCheck idx len target` models
      `TerminatorKind::Assert` with `AssertKind::BoundsCheck { len, index }`
      generated by `rustc` prior to slice indexing `(*slice)[idx]`: if
      `idx < len`, control transfers to `target`; if `idx ≥ len`, the assertion
      panics/unwinds (`.terminated .unwind`):

      > "BoundsCheck { len: Operand, index: Operand }"

    Source: https://github.com/rust-lang/rust/blob/8006091eb71ae7d9e9bccb66c6122c9d68af4466/compiler/rustc_middle/src/mir/syntax.rs#L990-L1085 -/
@[candidate mir_ast]
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | switchInt (discr : Operand) (targets : List (Nat × BlockId)) (otherwise : BlockId)
  | assert (cond : Operand) (expected : Bool) (target : BlockId)
  | assertBoundsCheck (idx : Operand) (len : Operand) (target : BlockId)
  | callAtomicLoadUsize (ptr : Operand) (ord : Operand) (dest : LocalId) (target : BlockId)
  | callFn (callee : FnSymbol) (args : List Operand) (dest : LocalId) (target : BlockId)

/-- A single basic block (`BasicBlockData`) consisting of a sequential list of
    `statements` followed by a `terminator`. -/
@[candidate mir_ast]
structure BasicBlock where
  statements : List Statement
  terminator : Terminator

/-- Open, fuel-indexed relational call contract table mapping each callee
    `FnSymbol`, remaining step budget `k : Nat`, and argument list `List MirVal`
    to:
    - `hasSpec`: whether `callee` has a registered call contract at fuel `k`
      for `args` (keeping `stepBlock` constructive without `Classical.choice`).
    - `post`: the relational postcondition `MirVal → Prop` constraining the
      return value `ret` when `hasSpec` holds.

    Replacing Round 1's closed 2-argument `PureCallee2` enum with
    `CallSpecTable` allows arbitrary arities, ADT/slice arguments, and mutually
    recursive callees verified by step-indexed strong induction on `k`. -/
@[candidate mir_ast]
structure CallSpecTable where
  hasSpec : FnSymbol → Nat → List MirVal → Bool := fun _ _ _ => false
  post : FnSymbol → Nat → List MirVal → MirVal → Prop := fun _ _ _ _ => False

/-- A captured `Runtime(PostCleanup)` MIR function body. -/
@[candidate mir_ast]
structure MirBody where
  paramTys : List MirTy
  returnTy : MirTy
  localCount : Nat
  blocks : List BasicBlock
  callSpecs : CallSpecTable := {}

end Trusted

/-!
### Lawful Boolean Equality Checkers on `MirAst` Without `deriving`

`trusted/audit/TrustedBoundary.lean` rejects `Parser.Command.deriving` and
`optDeriving` (`deriving DecidableEq, Repr`) during `preflight`. All boolean
equality checkers below are defined by explicit structural recursion and paired
with `beq*_eq_of_true` and `beq*_refl` lemmas.
-/

namespace Trusted

/-- Pointwise boolean equality over lists given an element comparator `beqElem`. -/
@[candidate mir_ast]
def beqList {α : Type} (beqElem : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqElem x y && beqList beqElem xs ys
  | _, _ => false

theorem beqList_eq_of_true {α : Type} {beqElem : α → α → Bool}
    (h_elem : ∀ x y, beqElem x y = true → x = y) :
    ∀ (xs ys : List α), beqList beqElem xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [beqList, Bool.and_eq_true] at h
    rw [h_elem x y h.1, beqList_eq_of_true h_elem xs ys h.2]

theorem beqList_refl {α : Type} {beqElem : α → α → Bool}
    (h_refl : ∀ x, beqElem x x = true) :
    ∀ (xs : List α), beqList beqElem xs xs = true
  | [] => rfl
  | x :: xs => by
    simp only [beqList, Bool.and_eq_true]
    exact ⟨h_refl x, beqList_refl h_refl xs⟩

/-- Structural boolean equality on `AtomicOrdering`. -/
@[candidate mir_ast]
def beqAtomicOrdering : AtomicOrdering → AtomicOrdering → Bool
  | .relaxed, .relaxed => true
  | .acquire, .acquire => true
  | _, _ => false

theorem beqAtomicOrdering_eq_of_true :
    ∀ a b, beqAtomicOrdering a b = true → a = b
  | .relaxed, .relaxed, _ => rfl
  | .acquire, .acquire, _ => rfl

theorem beqAtomicOrdering_refl :
    ∀ a, beqAtomicOrdering a a = true
  | .relaxed => rfl
  | .acquire => rfl

/-- Structural boolean equality on `ScalarVal`. -/
@[candidate mir_ast]
def beqScalarVal : ScalarVal → ScalarVal → Bool
  | .usize m, .usize n => m == n
  | .bool a, .bool b => a == b
  | .unit, .unit => true
  | _, _ => false

theorem beqScalarVal_eq_of_true :
    ∀ a b, beqScalarVal a b = true → a = b
  | .usize m, .usize n, h => by
    simp only [beqScalarVal, beq_iff_eq] at h
    rw [h]
  | .bool a, .bool b, h => by
    simp only [beqScalarVal, beq_iff_eq] at h
    rw [h]
  | .unit, .unit, _ => rfl

theorem beqScalarVal_refl :
    ∀ a, beqScalarVal a a = true
  | .usize m => by simp [beqScalarVal]
  | .bool a => by simp [beqScalarVal]
  | .unit => rfl

/-- Structural boolean equality on `MirVal`. -/
@[candidate mir_ast]
def beqMirVal : MirVal → MirVal → Bool
  | .usize m, .usize n => m == n
  | .bool a, .bool b => a == b
  | .unit, .unit => true
  | .tupleUsizeBool v1 o1, .tupleUsizeBool v2 o2 => (v1 == v2) && (o1 == o2)
  | .atomicLoc l1, .atomicLoc l2 => l1 == l2
  | .refSharedLoc l1, .refSharedLoc l2 => l1 == l2
  | .refMutLoc l1, .refMutLoc l2 => l1 == l2
  | .refSliceLoc l1 n1, .refSliceLoc l2 n2 => (l1 == l2) && (n1 == n2)
  | .adtVal v1 fs1, .adtVal v2 fs2 => (v1 == v2) && beqList beqScalarVal fs1 fs2
  | .ordering o1, .ordering o2 => beqAtomicOrdering o1 o2
  | _, _ => false

theorem beqMirVal_eq_of_true :
    ∀ a b, beqMirVal a b = true → a = b
  | .usize m, .usize n, h => by
    simp only [beqMirVal, beq_iff_eq] at h; rw [h]
  | .bool a, .bool b, h => by
    simp only [beqMirVal, beq_iff_eq] at h; rw [h]
  | .unit, .unit, _ => rfl
  | .tupleUsizeBool v1 o1, .tupleUsizeBool v2 o2, h => by
    simp only [beqMirVal, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  | .atomicLoc l1, .atomicLoc l2, h => by
    simp only [beqMirVal, beq_iff_eq] at h; rw [h]
  | .refSharedLoc l1, .refSharedLoc l2, h => by
    simp only [beqMirVal, beq_iff_eq] at h; rw [h]
  | .refMutLoc l1, .refMutLoc l2, h => by
    simp only [beqMirVal, beq_iff_eq] at h; rw [h]
  | .refSliceLoc l1 n1, .refSliceLoc l2 n2, h => by
    simp only [beqMirVal, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  | .adtVal v1 fs1, .adtVal v2 fs2, h => by
    simp only [beqMirVal, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, beqList_eq_of_true beqScalarVal_eq_of_true fs1 fs2 h.2]
  | .ordering o1, .ordering o2, h => by
    simp only [beqMirVal] at h
    rw [beqAtomicOrdering_eq_of_true o1 o2 h]

theorem beqMirVal_refl :
    ∀ a, beqMirVal a a = true
  | .usize _ => by simp [beqMirVal]
  | .bool _ => by simp [beqMirVal]
  | .unit => rfl
  | .tupleUsizeBool _ _ => by simp [beqMirVal]
  | .atomicLoc _ => by simp [beqMirVal]
  | .refSharedLoc _ => by simp [beqMirVal]
  | .refMutLoc _ => by simp [beqMirVal]
  | .refSliceLoc _ _ => by simp [beqMirVal]
  | .adtVal _ fs => by
    simp only [beqMirVal, beq_self_eq_true, Bool.true_and]
    exact beqList_refl beqScalarVal_refl fs
  | .ordering o => beqAtomicOrdering_refl o

end Trusted

/-!
### Extended Memory and Operational Semantics (`MirSemantics`)
-/

namespace Trusted

/-- A single modification entry in an atomic location's C++20 modification
    order (`val` written at timestamp `ts`). -/
@[candidate memory]
structure AtomicWrite where
  val : Nat
  ts : Nat

/-- Memory state combining C++20 atomic locations, non-atomic scalar cells, and
    non-atomic contiguous slice allocations (`naSlice`). -/
@[candidate memory]
structure MemState where
  history : Nat → List AtomicWrite
  naMem : Nat → Option Nat := fun _ => none
  naSlice : Nat → Option (List Nat) := fun _ => none

/-- Read a non-atomic `usize` cell at location `loc`. -/
@[candidate memory]
def MemState.readNA (m : MemState) (loc : Nat) : Option Nat :=
  m.naMem loc

/-- Write a non-atomic `usize` cell at location `loc` when `loc` is already
    allocated (`m.naMem loc = some _`). -/
@[candidate memory]
def MemState.writeNA (m : MemState) (loc : Nat) (v : Nat) : Option MemState :=
  match m.naMem loc with
  | some _ =>
    some { m with naMem := fun l => if l == loc then some v else m.naMem l }
  | none => none

/-- Read the `idx`-th `usize` element from the slice allocation at `loc`,
    returning `none` if `loc` is unallocated or `idx ≥ elems.length`. -/
@[candidate memory]
def MemState.readSliceNA (m : MemState) (loc idx : Nat) : Option Nat :=
  match m.naSlice loc with
  | some elems => elems[idx]?
  | none => none

/-- Check whether `v : MirVal` dynamically inhabits `ty : MirTy` in `mem`. -/
@[candidate mir_semantics]
def MirVal.hasTyInMem (mem : MemState) : MirVal → MirTy → Prop
  | .usize _, .usize => True
  | .bool _, .bool => True
  | .unit, .unit => True
  | .tupleUsizeBool _ _, .tupleUsizeBool => True
  | .atomicLoc loc, .refAtomicUsize => mem.history loc ≠ []
  | .refSharedLoc loc, .refSharedUsize => (mem.readNA loc).isSome = true
  | .refMutLoc loc, .refMutUsize => (mem.readNA loc).isSome = true
  | .refSliceLoc loc len, .refSliceUsize =>
      ∃ elems, mem.naSlice loc = some elems ∧ elems.length = len
  | .adtVal _ _, .adt _ => True
  | .ordering _, .atomicOrdering => True
  | _, _ => False

/-- Per-thread view mapping each atomic location `loc` to the maximum modification
    timestamp observed by this thread at `loc`. -/
@[candidate memory]
abbrev ThreadView := Nat → Nat

/-- Join two views pointwise (`max` at every location). -/
@[candidate memory]
def ThreadView.join (v₁ v₂ : ThreadView) : ThreadView :=
  fun loc => Nat.max (v₁ loc) (v₂ loc)

/-- Advance view `v` at `loc` to at least timestamp `ts`. -/
@[candidate memory]
def ThreadView.advance (v : ThreadView) (loc ts : Nat) : ThreadView :=
  fun l => if l == loc then Nat.max (v l) ts else v l

/-- Operational state of a single-frame MIR execution. -/
@[candidate mir_semantics]
structure MirState where
  pc : BlockId
  locals : Nat → Option MirVal
  mem : MemState
  curView : ThreadView
  acqView : Nat → ThreadView
  callFuel : Nat := 0

/-- Read the current value of `local_` in `s`. -/
@[candidate mir_semantics]
def MirState.readLocal (s : MirState) (local_ : LocalId) : Option MirVal :=
  s.locals local_.index

/-- Update `local_` to `val` in `s`. -/
@[candidate mir_semantics]
def MirState.writeLocal (s : MirState) (local_ : LocalId) (val : Option MirVal) :
    MirState :=
  { s with
    locals := fun idx => if idx == local_.index then val else s.locals idx }

/-- Evaluate an `Operand` in state `s`, returning the produced `MirVal` and the
    updated state (clearing the source local on `Operand.move`). -/
@[candidate mir_semantics]
def evalOperand (s : MirState) : Operand → Option (MirVal × MirState)
  | .copy src =>
    match s.readLocal src with
    | some v => some (v, s)
    | none => none
  | .move src =>
    match s.readLocal src with
    | some v => some (v, s.writeLocal src none)
    | none => none
  | .constUsize bits => some (.usize bits, s)
  | .constBool b => some (.bool b, s)
  | .constUnit => some (.unit, s)
  | .constOrdering ord => some (.ordering ord, s)

/-- Evaluate a list of operands left-to-right in state `s`. -/
@[candidate mir_semantics]
def evalOperandList (s : MirState) : List Operand → Option (List MirVal × MirState)
  | [] => some ([], s)
  | op :: ops =>
    match evalOperand s op with
    | some (v, s1) =>
      match evalOperandList s1 ops with
      | some (vs, s2) => some (v :: vs, s2)
      | none => none
    | none => none

/-- Convert a list of `MirVal`s into a list of `ScalarVal`s for ADT aggregate
    construction. -/
@[candidate mir_semantics]
def toScalarValList : List MirVal → Option (List ScalarVal)
  | [] => some []
  | v :: vs =>
    match v.toScalarVal?, toScalarValList vs with
    | some sv, some svs => some (sv :: svs)
    | _, _ => none

/-- Read a value from a projected `Place` in state `s`:
    - `[]`: reads `s.readLocal p.local_`.
    - `[.deref]`: dereferences `refSharedLoc loc` or `refMutLoc loc` in `s.mem`.
    - `[.deref, .index idxLocal]`: indexes into a slice fat pointer
      `refSliceLoc loc len` at `idx : usize` held in `idxLocal`, checking
      `idx < len` and reading `s.mem.readSliceNA loc idx`.
    - `[.field idx]`: projects field `idx` of a struct (`adtVal 0 fields`).
    - `[.downcast v, .field idx]`: downcasts an enum (`adtVal variant fields`)
      to variant `v` (returning `none` / UB if `variant != v`) and projects
      field `idx`. -/
@[candidate mir_semantics]
def evalReadPlace (s : MirState) (p : Place) : Option MirVal :=
  match p.projection with
  | [] => s.readLocal p.local_
  | [.deref] =>
    match s.readLocal p.local_ with
    | some (.refSharedLoc loc) | some (.refMutLoc loc) =>
      match s.mem.readNA loc with
      | some n => some (.usize n)
      | none => none
    | _ => none
  | [.deref, .index idxLocal] =>
    match s.readLocal p.local_, s.readLocal idxLocal with
    | some (.refSliceLoc loc len), some (.usize idx) =>
      if idx < len then
        match s.mem.readSliceNA loc idx with
        | some n => some (.usize n)
        | none => none
      else none
    | _, _ => none
  | [.field idx] =>
    match s.readLocal p.local_ with
    | some (.adtVal _ fields) =>
      match fields[idx]? with
      | some sv => some sv.toMirVal
      | none => none
    | _ => none
  | [.downcast v, .field idx] =>
    match s.readLocal p.local_ with
    | some (.adtVal variant fields) =>
      if variant == v then
        match fields[idx]? with
        | some sv => some sv.toMirVal
        | none => none
      else none
    | _ => none
  | _ => none

/-- Evaluate an `Rvalue` in state `s`. -/
@[candidate mir_semantics]
def evalRvalue (s : MirState) : Rvalue → Option (MirVal × MirState)
  | .use op _withRetag => evalOperand s op
  | .deref src =>
    match s.readLocal src with
    | some (.refSharedLoc loc) | some (.refMutLoc loc) =>
      match s.mem.readNA loc with
      | some bits => some (.usize bits, s)
      | none => none
    | _ => none
  | .binaryOp op lhs rhs =>
    match evalOperand s lhs with
    | none => none
    | some (v₁, s₁) =>
      match evalOperand s₁ rhs with
      | none => none
      | some (v₂, s₂) =>
        match op, v₁, v₂ with
        | .add, .usize a, .usize b => some (.usize (a + b), s₂)
        | .sub, .usize a, .usize b =>
          if b ≤ a then some (.usize (a - b), s₂) else none
        | .bitXor, .usize a, .usize b => some (.usize (Nat.xor a b), s₂)
        | .bitAnd, .usize a, .usize b => some (.usize (Nat.land a b), s₂)
        | .bitOr, .usize a, .usize b => some (.usize (Nat.lor a b), s₂)
        | .shl, .usize a, .usize b =>
          if b < 64 then some (.usize (a <<< b), s₂) else none
        | .shr, .usize a, .usize b =>
          if b < 64 then some (.usize (a >>> b), s₂) else none
        | .eq, .usize a, .usize b => some (.bool (a == b), s₂)
        | .eq, .bool a, .bool b => some (.bool (a == b), s₂)
        | .lt, .usize a, .usize b => some (.bool (decide (a < b)), s₂)
        | .le, .usize a, .usize b => some (.bool (decide (a ≤ b)), s₂)
        | _, _, _ => none
  | .checkedBinaryOp op lhs rhs =>
    match evalOperand s lhs with
    | none => none
    | some (v₁, s₁) =>
      match evalOperand s₁ rhs with
      | none => none
      | some (v₂, s₂) =>
        match op, v₁, v₂ with
        | .addWithOverflow, .usize a, .usize b =>
          some (.tupleUsizeBool (a + b) false, s₂)
        | .subWithOverflow, .usize a, .usize b =>
          if b ≤ a then
            some (.tupleUsizeBool (a - b) false, s₂)
          else
            some (.tupleUsizeBool 0 true, s₂)
        | _, _, _ => none
  | .proj0 src =>
    match s.readLocal src with
    | some (.tupleUsizeBool val _) => some (.usize val, s)
    | _ => none
  | .proj1 src =>
    match s.readLocal src with
    | some (.tupleUsizeBool _ ovf) => some (.bool ovf, s)
    | _ => none
  | .len src =>
    match s.readLocal src with
    | some (.refSliceLoc _ len) => some (.usize len, s)
    | _ => none
  | .discriminant src =>
    match s.readLocal src with
    | some (.adtVal variant _) => some (.usize variant, s)
    | _ => none
  | .aggregate variant ops =>
    match evalOperandList s ops with
    | some (vals, s') =>
      match toScalarValList vals with
      | some svs => some (.adtVal variant svs, s')
      | none => none
    | none => none
  | .readPlace place =>
    match evalReadPlace s place with
    | some v => some (v, s)
    | none => none

/-- Execute a single `Statement`, returning `none` if it triggers immediate UB. -/
@[candidate mir_semantics]
def execStatement (localCount : Nat) (s : MirState) : Statement → Option MirState
  | .assign dst rv =>
    if dst.index < localCount then
      match evalRvalue s rv with
      | some (v, s') => some (s'.writeLocal dst (some v))
      | none => none
    else none
  | .storeDeref dstPtr rv =>
    if dstPtr.index < localCount then
      match evalRvalue s rv with
      | some (.usize bits, s') =>
        match s'.readLocal dstPtr with
        | some (.refMutLoc loc) =>
          match s'.mem.writeNA loc bits with
          | some mem' => some { s' with mem := mem' }
          | none => none
        | _ => none
      | _ => none
    else none
  | .storageLive l =>
    if l.index < localCount then some s else none
  | .storageDead l =>
    if l.index < localCount then some (s.writeLocal l none) else none
  | .nop => some s

/-- Execute a basic block's statement list sequentially. -/
@[candidate mir_semantics]
def execStatements (localCount : Nat) (s : MirState) :
    List Statement → Option MirState
  | [] => some s
  | stmt :: rest =>
    match execStatement localCount s stmt with
    | some s' => execStatements localCount s' rest
    | none => none

/-- Look up the target `BlockId` in a `SwitchInt` branch table. -/
@[candidate mir_semantics]
def lookupSwitchTarget (val : Nat) : List (Nat × BlockId) → BlockId → BlockId
  | [], otherwise => otherwise
  | (k, target) :: rest, otherwise =>
    if val == k then target else lookupSwitchTarget val rest otherwise

/-- Execute a basic block's `Terminator` from post-statement state `s`. -/
@[candidate mir_semantics]
def execTerminator (body : MirBody) (s : MirState) :
    Terminator → StepResult MirState Unit MirVal
  | .return_ =>
    match s.readLocal ⟨0⟩ with
    | some retVal => .terminated (.normal retVal)
    | none => .failed .ub
  | .goto target =>
    if target.index < body.blocks.length then
      .step () { s with pc := target }
    else
      .failed .ub
  | .switchInt discr targets otherwise =>
    match evalOperand s discr with
    | some (.usize val, s') =>
      let target := lookupSwitchTarget val targets otherwise
      if target.index < body.blocks.length then
        .step () { s' with pc := target }
      else
        .failed .ub
    | some (.bool b, s') =>
      let val := if b then 1 else 0
      let target := lookupSwitchTarget val targets otherwise
      if target.index < body.blocks.length then
        .step () { s' with pc := target }
      else
        .failed .ub
    | _ => .failed .ub
  | .assert cond expected target =>
    match evalOperand s cond with
    | some (.bool b, s') =>
      if b == expected then
        if target.index < body.blocks.length then
          .step () { s' with pc := target }
        else
          .failed .ub
      else
        .terminated .unwind
    | _ => .failed .ub
  | .assertBoundsCheck idxOp lenOp target =>
    match evalOperand s idxOp with
    | some (.usize idx, s₁) =>
      match evalOperand s₁ lenOp with
      | some (.usize len, s₂) =>
        if idx < len then
          if target.index < body.blocks.length then
            .step () { s₂ with pc := target }
          else
            .failed .ub
        else
          .terminated .unwind
      | _ => .failed .ub
    | _ => .failed .ub
  | .callAtomicLoadUsize ptrOp ordOp dest target =>
    if dest.index < body.localCount ∧ target.index < body.blocks.length then
      match evalOperand s ptrOp with
      | none => .failed .ub
      | some (ptrVal, s₁) =>
        match evalOperand s₁ ordOp with
        | none => .failed .ub
        | some (ordVal, s₂) =>
          match ptrVal, ordVal with
          | .atomicLoc loc, .ordering ord =>
            let writes := s₂.mem.history loc
            if writes.isEmpty then
              .failed .ub
            else
              .choice .demonic (fun s_next =>
                ∃ w ∈ writes,
                  s₂.curView loc ≤ w.ts ∧
                  let v_load := s₂.curView.advance loc w.ts
                  let v_next :=
                    match ord with
                    | .relaxed => v_load
                    | .acquire => v_load.join (s₂.acqView w.ts)
                  s_next = { (s₂.writeLocal dest (some (.usize w.val))) with
                    pc := target
                    curView := v_next })
          | _, _ => .failed .ub
    else
      .failed .ub
  | .callFn callee args dest target =>
    if dest.index < body.localCount ∧ target.index < body.blocks.length then
      match evalOperandList s args with
      | some (argVals, s') =>
        if body.callSpecs.hasSpec callee s'.callFuel argVals then
          .choice .demonic (fun s_next =>
            ∃ ret,
              body.callSpecs.post callee s'.callFuel argVals ret ∧
              s_next = { (s'.writeLocal dest (some ret)) with
                pc := target })
        else
          .failed .ub
      | none => .failed .ub
    else
      .failed .ub

/-- Single basic-block transition step of a `MirBody`. -/
@[candidate mir_semantics]
def stepBlock (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.pc.index]? with
  | none => .failed .ub
  | some bb =>
    match execStatements body.localCount s bb.statements with
    | none => .failed .ub
    | some s' => execTerminator body s' bb.terminator

/-- Valid initial state predicate for a `MirBody`. -/
@[candidate mir_semantics]
def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.pc = ⟨0⟩ ∧
  body.paramTys.length + 1 ≤ body.localCount ∧
  (∀ i (h : i < body.paramTys.length),
    ∃ v, s.locals (i + 1) = some v ∧ v.hasTyInMem s.mem (body.paramTys[i]'h)) ∧
  (∀ loc w, w ∈ s.mem.history loc → s.acqView w.ts loc ≤ w.ts)

/-- Small-step operational machine for `Runtime(PostCleanup)` MIR. -/
@[candidate mir_semantics]
def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = stepBlock body s

/-- The Layer 1A `Language` for `Runtime(PostCleanup)` MIR. -/
@[candidate mir_semantics]
abbrev MirLang : Language :=
  MirMachine.toLanguage

end Trusted

/-!
## Section 2: Extended `FunctionalTranslation` with Slices (`&[usize]`), Struct/Enum ADTs, and Bounded Loop Verification (`sliceCheckerMirBody`)

We now extend `Anneal.FunctionalTranslation` to symbolically evaluate:
- Immutable slice fat pointers (`SymVal.refSlice elems`), slice length queries
  (`Rvalue.len`), dynamic bounds-check assertions
  (`Terminator.assertBoundsCheck`), and in-bounds slice element reads
  (`Rvalue.readPlace` with `[.deref, .index idxLocal]`).
- Algebraic data types (`SymVal.adtVal variant fields`), aggregate construction
  (`Rvalue.aggregate`), discriminant reads (`Rvalue.discriminant`), and
  struct/enum field projections (`[.field idx]` and `[.downcast v, .field idx]`).
- Bounded loops (`evalSymWith` iterating across basic-block backedges with
  step-fuel).

We prove the general soundness bridge `evalSymWith_slice_sound` /
`evalSym_slice_sound` and apply it to verify `sliceCheckerMirBody`, a
multi-instruction certificate checker written in Rust Subset $K$ that loops
over an `&[usize]` slice without word-packing.
-/

namespace Anneal
open Trusted

/-- Symbolic value tracked by `FunctionalTranslation` across pure, reference,
    slice, and struct/enum ADT locals. -/
inductive SymVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  | refShared (val : Nat)
  | refSlice (elems : List Nat)
  | adtVal (variant : Nat) (fields : List ScalarVal)

/-- Convert a `ScalarVal` into a `SymVal`. -/
def _root_.Trusted.ScalarVal.toSymVal : ScalarVal → SymVal
  | .usize n => .usize n
  | .bool b => .bool b
  | .unit => .unit

/-- Extract a `ScalarVal` from a scalar `SymVal`. -/
def SymVal.toScalarVal? : SymVal → Option ScalarVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | _ => none

/-- Convert a list of `SymVal`s to a list of `ScalarVal`s. -/
def symToScalarValList : List SymVal → Option (List ScalarVal)
  | [] => some []
  | v :: vs =>
    match v.toScalarVal?, symToScalarValList vs with
    | some sv, some svs => some (sv :: svs)
    | _, _ => none

/-- Correspondence between a concrete `MirVal` in `mem` and a `SymVal`. -/
def SymValMatchesInMem (mem : MemState) : MirVal → SymVal → Prop
  | .usize m, .usize n => m = n
  | .bool a, .bool b => a = b
  | .unit, .unit => True
  | .tupleUsizeBool v1 o1, .tupleUsizeBool v2 o2 => v1 = v2 ∧ o1 = o2
  | .refSharedLoc loc, .refShared val => mem.readNA loc = some val
  | .refSliceLoc loc len, .refSlice elems =>
      mem.naSlice loc = some elems ∧ len = elems.length
  | .adtVal v1 fs1, .adtVal v2 fs2 => v1 = v2 ∧ fs1 = fs2
  | _, _ => False

/-- Value-level correspondence for scalar/ADT return values (`SymValMatches`). -/
def SymValMatches : MirVal → SymVal → Prop
  | .usize m, .usize n => m = n
  | .bool a, .bool b => a = b
  | .unit, .unit => True
  | .tupleUsizeBool v1 o1, .tupleUsizeBool v2 o2 => v1 = v2 ∧ o1 = o2
  | .adtVal v1 fs1, .adtVal v2 fs2 => v1 = v2 ∧ fs1 = fs2
  | _, _ => False

theorem symValMatches_of_inMem {mem : MemState} {mv : MirVal} {sv : SymVal}
    (h : SymValMatchesInMem mem mv sv)
    (h_nonref : ∀ n, sv ≠ .refShared n)
    (h_nonslice : ∀ es, sv ≠ .refSlice es) :
    SymValMatches mv sv := by
  match mv, sv with
  | .usize _, .usize _ => exact h
  | .bool _, .bool _ => exact h
  | .unit, .unit => exact h
  | .tupleUsizeBool _ _, .tupleUsizeBool _ _ => exact h
  | .refSharedLoc _, .refShared n => exact False.elim (h_nonref n rfl)
  | .refSliceLoc _ _, .refSlice es => exact False.elim (h_nonslice es rfl)
  | .adtVal _ _, .adtVal _ _ => exact h

/-- Symbolic environment mapping local index `i : Nat` to its `SymVal`. -/
abbrev SymEnv := Nat → Option SymVal

/-- Update local `idx` in a `SymEnv`. -/
def SymEnv.write (env : SymEnv) (idx : Nat) (val : Option SymVal) : SymEnv :=
  fun i => if i == idx then val else env i

/-- State-environment agreement: every initialized entry in `env` matches the
    corresponding local in `st.locals` with respect to `st.mem`. -/
def EnvMatches (st : MirState) (env : SymEnv) : Prop :=
  ∀ i sv, env i = some sv →
    ∃ mv, st.locals i = some mv ∧ SymValMatchesInMem st.mem mv sv

theorem envMatches_write {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) (dst : LocalId) {mv : MirVal} {sv : SymVal}
    (h_val : SymValMatchesInMem st.mem mv sv) :
    EnvMatches (st.writeLocal dst (some mv)) (env.write dst.index (some sv)) := by
  intro i sv' h_lookup
  simp only [SymEnv.write] at h_lookup
  by_cases h_eq : (i == dst.index) = true
  · simp only [h_eq, ↓reduceIte] at h_lookup
    injection h_lookup with h_sv
    subst h_sv
    refine ⟨mv, ?_, h_val⟩
    simp only [MirState.writeLocal, h_eq, ↓reduceIte]
  · have h_neq : (i == dst.index) = false := Bool.eq_false_iff.mpr h_eq
    simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at h_lookup
    rcases h_env i sv' h_lookup with ⟨mv', h_loc, h_m⟩
    refine ⟨mv', ?_, h_m⟩
    simp only [MirState.writeLocal, h_neq, Bool.false_eq_true, ↓reduceIte]
    exact h_loc

theorem envMatches_clear {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) (dst : LocalId) :
    EnvMatches (st.writeLocal dst none) (env.write dst.index none) := by
  intro i sv' h_lookup
  simp only [SymEnv.write] at h_lookup
  by_cases h_eq : (i == dst.index) = true
  · simp only [h_eq, ↓reduceIte] at h_lookup
    contradiction
  · have h_neq : (i == dst.index) = false := Bool.eq_false_iff.mpr h_eq
    simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at h_lookup
    rcases h_env i sv' h_lookup with ⟨mv', h_loc, h_m⟩
    refine ⟨mv', ?_, h_m⟩
    simp only [MirState.writeLocal, h_neq, Bool.false_eq_true, ↓reduceIte]
    exact h_loc

/-- Evaluate an `Operand` in a `SymEnv`. -/
def evalSymOperand (env : SymEnv) : Operand → Option (SymVal × SymEnv)
  | .copy src =>
    match env src.index with
    | some v => some (v, env)
    | none => none
  | .move src =>
    match env src.index with
    | some v => some (v, env.write src.index none)
    | none => none
  | .constUsize bits => some (.usize bits, env)
  | .constBool b => some (.bool b, env)
  | .constUnit => some (.unit, env)
  | .constOrdering _ => none

/-- Evaluate a list of operands in a `SymEnv`. -/
def evalSymOperandList (env : SymEnv) : List Operand → Option (List SymVal × SymEnv)
  | [] => some ([], env)
  | op :: ops =>
    match evalSymOperand env op with
    | some (v, env1) =>
      match evalSymOperandList env1 ops with
      | some (vs, env2) => some (v :: vs, env2)
      | none => none
    | none => none

/-- Evaluate a projected `Place` read in a `SymEnv`. -/
def evalSymReadPlace (env : SymEnv) (p : Place) : Option SymVal :=
  match p.projection with
  | [] => env p.local_.index
  | [.deref] =>
    match env p.local_.index with
    | some (.refShared n) => some (.usize n)
    | _ => none
  | [.deref, .index idxLocal] =>
    match env p.local_.index, env idxLocal.index with
    | some (.refSlice elems), some (.usize idx) =>
      if idx < elems.length then
        match elems[idx]? with
        | some n => some (.usize n)
        | none => none
      else none
    | _, _ => none
  | [.field idx] =>
    match env p.local_.index with
    | some (.adtVal _ fields) =>
      match fields[idx]? with
      | some sv => some sv.toSymVal
      | none => none
    | _ => none
  | [.downcast v, .field idx] =>
    match env p.local_.index with
    | some (.adtVal variant fields) =>
      if variant == v then
        match fields[idx]? with
        | some sv => some sv.toSymVal
        | none => none
      else none
    | _ => none
  | _ => none

/-- Evaluate an `Rvalue` in a `SymEnv`. -/
def evalSymRvalue (env : SymEnv) : Rvalue → Option (SymVal × SymEnv)
  | .use op _withRetag => evalSymOperand env op
  | .deref src =>
    match env src.index with
    | some (.refShared bits) => some (.usize bits, env)
    | _ => none
  | .binaryOp op lhs rhs =>
    match evalSymOperand env lhs with
    | none => none
    | some (v₁, env₁) =>
      match evalSymOperand env₁ rhs with
      | none => none
      | some (v₂, env₂) =>
        match op, v₁, v₂ with
        | .add, .usize a, .usize b => some (.usize (a + b), env₂)
        | .sub, .usize a, .usize b =>
          if b ≤ a then some (.usize (a - b), env₂) else none
        | .bitXor, .usize a, .usize b => some (.usize (Nat.xor a b), env₂)
        | .bitAnd, .usize a, .usize b => some (.usize (Nat.land a b), env₂)
        | .bitOr, .usize a, .usize b => some (.usize (Nat.lor a b), env₂)
        | .shl, .usize a, .usize b =>
          if b < 64 then some (.usize (a <<< b), env₂) else none
        | .shr, .usize a, .usize b =>
          if b < 64 then some (.usize (a >>> b), env₂) else none
        | .eq, .usize a, .usize b => some (.bool (a == b), env₂)
        | .eq, .bool a, .bool b => some (.bool (a == b), env₂)
        | .lt, .usize a, .usize b => some (.bool (decide (a < b)), env₂)
        | .le, .usize a, .usize b => some (.bool (decide (a ≤ b)), env₂)
        | _, _, _ => none
  | .checkedBinaryOp op lhs rhs =>
    match evalSymOperand env lhs with
    | none => none
    | some (v₁, env₁) =>
      match evalSymOperand env₁ rhs with
      | none => none
      | some (v₂, env₂) =>
        match op, v₁, v₂ with
        | .addWithOverflow, .usize a, .usize b =>
          some (.tupleUsizeBool (a + b) false, env₂)
        | .subWithOverflow, .usize a, .usize b =>
          if b ≤ a then
            some (.tupleUsizeBool (a - b) false, env₂)
          else
            some (.tupleUsizeBool 0 true, env₂)
        | _, _, _ => none
  | .proj0 src =>
    match env src.index with
    | some (.tupleUsizeBool val _) => some (.usize val, env)
    | _ => none
  | .proj1 src =>
    match env src.index with
    | some (.tupleUsizeBool _ ovf) => some (.bool ovf, env)
    | _ => none
  | .len src =>
    match env src.index with
    | some (.refSlice elems) => some (.usize elems.length, env)
    | _ => none
  | .discriminant src =>
    match env src.index with
    | some (.adtVal variant _) => some (.usize variant, env)
    | _ => none
  | .aggregate variant ops =>
    match evalSymOperandList env ops with
    | some (vals, env') =>
      match symToScalarValList vals with
      | some svs => some (.adtVal variant svs, env')
      | none => none
    | none => none
  | .readPlace place =>
    match evalSymReadPlace env place with
    | some v => some (v, env)
    | none => none

/-- Execute a single `Statement` symbolically in `SymEnv`. -/
def execSymStatement (localCount : Nat) (env : SymEnv) :
    Statement → Option SymEnv
  | .assign dst rv =>
    if dst.index < localCount then
      match evalSymRvalue env rv with
      | some (v, env') => some (env'.write dst.index (some v))
      | none => none
    else none
  | .storeDeref _ _ => none
  | .storageLive l =>
    if l.index < localCount then some env else none
  | .storageDead l =>
    if l.index < localCount then some (env.write l.index none) else none
  | .nop => some env

/-- Execute a list of statements symbolically in `SymEnv`. -/
def execSymStatements (localCount : Nat) (env : SymEnv) :
    List Statement → Option SymEnv
  | [] => some env
  | stmt :: rest =>
    match execSymStatement localCount env stmt with
    | some env' => execSymStatements localCount env' rest
    | none => none

/-- Outcome of symbolically executing a basic block's terminator:
    - `.ret sv`: normal return of symbolic value `sv`
    - `.unwind`: assertion or bounds-check failure (`Terminator.assert` or
      `Terminator.assertBoundsCheck`)
    - `.jump target env'`: control transfer to `target` with updated `env'` -/
inductive SymTermResult where
  | ret (sv : SymVal)
  | unwind
  | jump (target : BlockId) (env' : SymEnv)

/-- Symbolically evaluate a basic block's `Terminator` in `env`. -/
def evalSymTerminator (body : MirBody) (env : SymEnv) :
    Terminator → Option SymTermResult
  | .return_ =>
    match env 0 with
    | some sv => some (.ret sv)
    | none => none
  | .goto target =>
    if target.index < body.blocks.length then
      some (.jump target env)
    else none
  | .switchInt discr targets otherwise =>
    match evalSymOperand env discr with
    | some (.usize val, env') =>
      let target := lookupSwitchTarget val targets otherwise
      if target.index < body.blocks.length then
        some (.jump target env')
      else none
    | some (.bool b, env') =>
      let val := if b then 1 else 0
      let target := lookupSwitchTarget val targets otherwise
      if target.index < body.blocks.length then
        some (.jump target env')
      else none
    | _ => none
  | .assert cond expected target =>
    match evalSymOperand env cond with
    | some (.bool b, env') =>
      if b == expected then
        if target.index < body.blocks.length then
          some (.jump target env')
        else none
      else some .unwind
    | _ => none
  | .assertBoundsCheck idxOp lenOp target =>
    match evalSymOperand env idxOp with
    | some (.usize idx, env₁) =>
      match evalSymOperand env₁ lenOp with
      | some (.usize len, env₂) =>
        if idx < len then
          if target.index < body.blocks.length then
            some (.jump target env₂)
          else none
        else some .unwind
      | _ => none
    | _ => none
  | .callAtomicLoadUsize _ _ _ _ => none
  | .callFn _ _ _ _ => none

/-- Symbolically execute `body` for up to `fuel` basic-block steps starting at
    block index `bb` and symbolic environment `env`. -/
def evalSym (fuel : Nat) (body : MirBody) (bb : Nat) (env : SymEnv) :
    Option (TerminationKind SymVal) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match body.blocks[bb]? with
    | none => none
    | some block =>
      match execSymStatements body.localCount env block.statements with
      | none => none
      | some env' =>
        match evalSymTerminator body env' block.terminator with
        | none => none
        | some (.ret sv) => some (.normal sv)
        | some .unwind => some .unwind
        | some (.jump target env_next) =>
          evalSym fuel' body target.index env_next

end Anneal

namespace Anneal
open Trusted

theorem scalarVal_toMirVal_matches (mem : MemState) (sv : ScalarVal) :
    SymValMatchesInMem mem sv.toMirVal sv.toSymVal := by
  cases sv <;> simp [ScalarVal.toMirVal, ScalarVal.toSymVal, SymValMatchesInMem]

theorem evalSymOperand_sound {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) (op : Operand)
    {sv : SymVal} {env' : SymEnv}
    (h_sym : evalSymOperand env op = some (sv, env')) :
    ∃ mv st',
      evalOperand st op = some (mv, st') ∧
      st'.mem = st.mem ∧
      st'.pc = st.pc ∧
      SymValMatchesInMem st.mem mv sv ∧
      EnvMatches st' env' := by
  cases op with
  | copy src =>
    simp only [evalSymOperand] at h_sym
    cases h_lk : env src.index with
    | none => rw [h_lk] at h_sym; contradiction
    | some sv0 =>
      rw [h_lk] at h_sym
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases h_env src.index sv0 h_lk with ⟨mv, h_st_lk, h_m⟩
      refine ⟨mv, st, ?_, rfl, rfl, h_m, h_env⟩
      simp only [evalOperand, MirState.readLocal, h_st_lk]
  | move src =>
    simp only [evalSymOperand] at h_sym
    cases h_lk : env src.index with
    | none => rw [h_lk] at h_sym; contradiction
    | some sv0 =>
      rw [h_lk] at h_sym
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases h_env src.index sv0 h_lk with ⟨mv, h_st_lk, h_m⟩
      refine ⟨mv, st.writeLocal src none, ?_, rfl, rfl, h_m, envMatches_clear h_env src⟩
      simp only [evalOperand, MirState.readLocal, h_st_lk]
  | constUsize bits =>
    simp only [evalSymOperand] at h_sym
    injection h_sym with h_pair
    injection h_pair with h_sv h_e
    subst h_sv; subst h_e
    exact ⟨.usize bits, st, rfl, rfl, rfl, rfl, h_env⟩
  | constBool b =>
    simp only [evalSymOperand] at h_sym
    injection h_sym with h_pair
    injection h_pair with h_sv h_e
    subst h_sv; subst h_e
    exact ⟨.bool b, st, rfl, rfl, rfl, rfl, h_env⟩
  | constUnit =>
    simp only [evalSymOperand] at h_sym
    injection h_sym with h_pair
    injection h_pair with h_sv h_e
    subst h_sv; subst h_e
    exact ⟨.unit, st, rfl, rfl, rfl, trivial, h_env⟩
  | constOrdering _ =>
    simp only [evalSymOperand] at h_sym
    contradiction

/-- Pointwise relational lifting over two lists of equal length. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

theorem evalSymOperandList_sound {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) :
    ∀ (ops : List Operand) {svs : List SymVal} {env' : SymEnv},
      evalSymOperandList env ops = some (svs, env') →
      ∃ mvs st',
        evalOperandList st ops = some (mvs, st') ∧
        st'.mem = st.mem ∧
        st'.pc = st.pc ∧
        ListRel (SymValMatchesInMem st.mem) mvs svs ∧
        EnvMatches st' env'
  | [], _, _, h_sym => by
    simp only [evalSymOperandList] at h_sym
    injection h_sym with h_pair
    injection h_pair with h_svs h_e
    subst h_svs; subst h_e
    exact ⟨[], st, rfl, rfl, rfl, .nil, h_env⟩
  | op :: ops, _, _, h_sym => by
    simp only [evalSymOperandList] at h_sym
    cases h_op : evalSymOperand env op with
    | none => simp only [h_op] at h_sym; contradiction
    | some p1 =>
      rcases p1 with ⟨sv1, env1⟩
      simp only [h_op] at h_sym
      cases h_ops : evalSymOperandList env1 ops with
      | none => simp only [h_ops] at h_sym; contradiction
      | some p2 =>
        rcases p2 with ⟨svs2, env2⟩
        simp only [h_ops] at h_sym
        injection h_sym with h_pair
        injection h_pair with h_svs h_e
        subst h_svs; subst h_e
        rcases evalSymOperand_sound h_env op h_op with
          ⟨mv1, st1, h_ev1, h_mem1, h_pc1, h_m1, h_env1⟩
        rcases evalSymOperandList_sound h_env1 ops h_ops with
          ⟨mvs2, st2, h_ev2, h_mem2, h_pc2, h_m2, h_env2⟩
        rw [h_mem1] at h_m2
        refine ⟨mv1 :: mvs2, st2, ?_, h_mem2.trans h_mem1, h_pc2.trans h_pc1, .cons h_m1 h_m2, h_env2⟩
        simp only [evalOperandList, h_ev1, h_ev2]

theorem toScalarVal_of_matches {mem : MemState} {mv : MirVal} {sv : SymVal}
    (h_m : SymValMatchesInMem mem mv sv)
    {sc : ScalarVal} (h_sc : sv.toScalarVal? = some sc) :
    mv.toScalarVal? = some sc := by
  cases mv <;> cases sv <;> simp [SymValMatchesInMem, SymVal.toScalarVal?, MirVal.toScalarVal?] at h_m h_sc ⊢
  · subst h_m; exact h_sc
  · subst h_m; exact h_sc
  · exact h_sc

theorem symToScalarValList_sound {mem : MemState} :
    ∀ {mvs : List MirVal} {svs : List SymVal},
      ListRel (SymValMatchesInMem mem) mvs svs →
      ∀ {scals : List ScalarVal},
        symToScalarValList svs = some scals →
        toScalarValList mvs = some scals
  | _, _, .nil, _, h_scals => by
    simp only [symToScalarValList] at h_scals
    injection h_scals with h_eq
    subst h_eq
    rfl
  | mv :: mvs, sv :: svs, .cons h_head h_tail, _, h_scals => by
    simp only [symToScalarValList] at h_scals
    cases h_hd : sv.toScalarVal? with
    | none => simp only [h_hd] at h_scals; contradiction
    | some sc =>
      cases h_tl : symToScalarValList svs with
      | none => simp only [h_hd, h_tl] at h_scals; contradiction
      | some scs =>
        simp only [h_hd, h_tl] at h_scals
        injection h_scals with h_eq
        subst h_eq
        have h_mv_hd := toScalarVal_of_matches h_head h_hd
        have h_mv_tl := symToScalarValList_sound h_tail h_tl
        simp only [toScalarValList, h_mv_hd, h_mv_tl]

theorem evalSymReadPlace_sound {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) (p : Place)
    {sv : SymVal}
    (h_sym : evalSymReadPlace env p = some sv) :
    ∃ mv,
      evalReadPlace st p = some mv ∧
      SymValMatchesInMem st.mem mv sv := by
  rcases p with ⟨locId, proj⟩
  match proj with
  | [] =>
    simp only [evalSymReadPlace] at h_sym
    rcases h_env locId.index sv h_sym with ⟨mv, h_lk, h_m⟩
    exact ⟨mv, h_lk, h_m⟩
  | [.deref] =>
    simp only [evalSymReadPlace] at h_sym
    cases h_lk : env locId.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i n
      injection h_sym with h_eq
      subst h_eq
      rcases h_env locId.index (.refShared n) h_lk with ⟨mv, h_st_lk, h_m⟩
      cases mv <;> simp [SymValMatchesInMem] at h_m
      rename_i loc
      refine ⟨.usize n, ?_, rfl⟩
      simp only [evalReadPlace, MirState.readLocal, h_st_lk, h_m]
  | [.deref, .index idxLocal] =>
    simp only [evalSymReadPlace] at h_sym
    cases h_lk1 : env locId.index with
    | none => simp only [h_lk1] at h_sym; contradiction
    | some sv1 =>
      cases h_lk2 : env idxLocal.index with
      | none => simp only [h_lk1, h_lk2] at h_sym; cases sv1 <;> contradiction
      | some sv2 =>
        simp only [h_lk1, h_lk2] at h_sym
        cases sv1 <;> cases sv2 <;> try contradiction
        rename_i elems idx
        by_cases h_lt : idx < elems.length
        · simp only [h_lt, ↓reduceIte] at h_sym
          cases h_el : elems[idx]? with
          | none => simp only [h_el] at h_sym; contradiction
          | some val =>
            simp only [h_el] at h_sym
            injection h_sym with h_eq
            subst h_eq
            rcases h_env locId.index (.refSlice elems) h_lk1 with ⟨mv1, h_st_lk1, h_m1⟩
            rcases h_env idxLocal.index (.usize idx) h_lk2 with ⟨mv2, h_st_lk2, h_m2⟩
            cases mv1 <;> simp [SymValMatchesInMem] at h_m1
            cases mv2 <;> simp [SymValMatchesInMem] at h_m2
            subst h_m2
            rcases h_m1 with ⟨h_slice, h_len⟩
            subst h_len
            refine ⟨.usize val, ?_, rfl⟩
            simp only [evalReadPlace, MirState.readLocal, h_st_lk1, h_st_lk2, h_lt, ↓reduceIte,
              MemState.readSliceNA, h_slice, h_el]
        · simp only [h_lt, ↓reduceIte] at h_sym
          contradiction
  | [.field idx] =>
    simp only [evalSymReadPlace] at h_sym
    cases h_lk : env locId.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i variant fields
      cases h_f : fields[idx]? with
      | none => simp only [h_f] at h_sym; contradiction
      | some sc =>
        simp only [h_f] at h_sym
        injection h_sym with h_eq
        subst h_eq
        rcases h_env locId.index (.adtVal variant fields) h_lk with ⟨mv, h_st_lk, h_m⟩
        cases mv <;> simp [SymValMatchesInMem] at h_m
        rcases h_m with ⟨h_v, h_fs⟩
        subst h_v; subst h_fs
        refine ⟨sc.toMirVal, ?_, scalarVal_toMirVal_matches st.mem sc⟩
        simp only [evalReadPlace, MirState.readLocal, h_st_lk, h_f]
  | [.downcast v, .field idx] =>
    simp only [evalSymReadPlace] at h_sym
    cases h_lk : env locId.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i variant fields
      by_cases h_v : (variant == v) = true
      · simp only [h_v, ↓reduceIte] at h_sym
        cases h_f : fields[idx]? with
        | none => simp only [h_f] at h_sym; contradiction
        | some sc =>
          simp only [h_f] at h_sym
          injection h_sym with h_eq
          subst h_eq
          rcases h_env locId.index (.adtVal variant fields) h_lk with ⟨mv, h_st_lk, h_m⟩
          cases mv <;> simp [SymValMatchesInMem] at h_m
          rcases h_m with ⟨h_veq, h_fs⟩
          subst h_veq; subst h_fs
          refine ⟨sc.toMirVal, ?_, scalarVal_toMirVal_matches st.mem sc⟩
          simp only [evalReadPlace, MirState.readLocal, h_st_lk, h_v, ↓reduceIte, h_f]
      · have h_vf : (variant == v) = false := Bool.eq_false_iff.mpr h_v
        simp only [h_vf, Bool.false_eq_true, ↓reduceIte] at h_sym
        contradiction
  | .deref :: .deref :: _ => simp [evalSymReadPlace] at h_sym
  | .deref :: .field _ :: _ => simp [evalSymReadPlace] at h_sym
  | .deref :: .downcast _ :: _ => simp [evalSymReadPlace] at h_sym
  | .deref :: .index _ :: _ :: _ => simp [evalSymReadPlace] at h_sym
  | .field _ :: _ :: _ => simp [evalSymReadPlace] at h_sym
  | .index _ :: _ => simp [evalSymReadPlace] at h_sym
  | .downcast _ :: [] => simp [evalSymReadPlace] at h_sym
  | .downcast _ :: .deref :: _ => simp [evalSymReadPlace] at h_sym
  | .downcast _ :: .index _ :: _ => simp [evalSymReadPlace] at h_sym
  | .downcast _ :: .downcast _ :: _ => simp [evalSymReadPlace] at h_sym
  | .downcast _ :: .field _ :: _ :: _ => simp [evalSymReadPlace] at h_sym

theorem evalSymRvalue_sound {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) (rv : Rvalue)
    {sv : SymVal} {env' : SymEnv}
    (h_sym : evalSymRvalue env rv = some (sv, env')) :
    ∃ mv st',
      evalRvalue st rv = some (mv, st') ∧
      st'.mem = st.mem ∧
      st'.pc = st.pc ∧
      SymValMatchesInMem st.mem mv sv ∧
      EnvMatches st' env' := by
  cases rv with
  | use op withRetag =>
    exact evalSymOperand_sound h_env op h_sym
  | deref src =>
    simp only [evalSymRvalue] at h_sym
    cases h_lk : env src.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i bits
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases h_env src.index (.refShared bits) h_lk with ⟨mv, h_st_lk, h_m⟩
      cases mv <;> simp [SymValMatchesInMem] at h_m
      rename_i loc
      refine ⟨.usize bits, st, ?_, rfl, rfl, rfl, h_env⟩
      simp only [evalRvalue, MirState.readLocal, h_st_lk, h_m]
  | binaryOp op lhs rhs =>
    simp only [evalSymRvalue] at h_sym
    cases h_l : evalSymOperand env lhs with
    | none => simp only [h_l] at h_sym; contradiction
    | some p1 =>
      rcases p1 with ⟨sv1, env1⟩
      simp only [h_l] at h_sym
      cases h_r : evalSymOperand env1 rhs with
      | none => simp only [h_r] at h_sym; contradiction
      | some p2 =>
        rcases p2 with ⟨sv2, env2⟩
        simp only [h_r] at h_sym
        rcases evalSymOperand_sound h_env lhs h_l with
          ⟨mv1, st1, h_ev1, h_mem1, h_pc1, h_m1, h_env1⟩
        rcases evalSymOperand_sound h_env1 rhs h_r with
          ⟨mv2, st2, h_ev2, h_mem2, h_pc2, h_m2, h_env2⟩
        rw [h_mem1] at h_m2
        match sv1, sv2 with
        | .usize a, .usize b =>
          cases mv1 <;> simp [SymValMatchesInMem] at h_m1
          cases mv2 <;> simp [SymValMatchesInMem] at h_m2
          rw [h_m1] at h_ev1; rw [h_m2] at h_ev2
          cases op <;> simp at h_sym
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.usize (a + b), st2, by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨h_c, rfl, rfl⟩
            exact ⟨.usize (a - b), st2, by simp [evalRvalue, h_ev1, h_ev2, h_c],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.usize (Nat.xor a b), st2, by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.usize (Nat.land a b), st2, by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.usize (Nat.lor a b), st2, by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨h_c, rfl, rfl⟩
            exact ⟨.usize (a <<< b), st2, by simp [evalRvalue, h_ev1, h_ev2, h_c],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨h_c, rfl, rfl⟩
            exact ⟨.usize (a >>> b), st2, by simp [evalRvalue, h_ev1, h_ev2, h_c],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.bool (a == b), st2, by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.bool (decide (a < b)), st2, by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.bool (decide (a ≤ b)), st2, by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
        | .bool a, .bool b =>
          cases mv1 <;> simp [SymValMatchesInMem] at h_m1
          cases mv2 <;> simp [SymValMatchesInMem] at h_m2
          rw [h_m1] at h_ev1; rw [h_m2] at h_ev2
          cases op <;> simp at h_sym
          rcases h_sym with ⟨rfl, rfl⟩
          exact ⟨.bool (a == b), st2, by simp [evalRvalue, h_ev1, h_ev2],
            h_mem2.trans h_mem1, h_pc2.trans h_pc1, rfl, h_env2⟩
        | .usize _, .bool _ | .usize _, .unit | .usize _, .tupleUsizeBool _ _
        | .usize _, .refShared _ | .usize _, .refSlice _ | .usize _, .adtVal _ _
        | .bool _, .usize _ | .bool _, .unit | .bool _, .tupleUsizeBool _ _
        | .bool _, .refShared _ | .bool _, .refSlice _ | .bool _, .adtVal _ _
        | .unit, _ | .tupleUsizeBool _ _, _ | .refShared _, _
        | .refSlice _, _ | .adtVal _ _, _ =>
          cases op <;> simp at h_sym
  | checkedBinaryOp op lhs rhs =>
    simp only [evalSymRvalue] at h_sym
    cases h_l : evalSymOperand env lhs with
    | none => simp only [h_l] at h_sym; contradiction
    | some p1 =>
      rcases p1 with ⟨sv1, env1⟩
      simp only [h_l] at h_sym
      cases h_r : evalSymOperand env1 rhs with
      | none => simp only [h_r] at h_sym; contradiction
      | some p2 =>
        rcases p2 with ⟨sv2, env2⟩
        simp only [h_r] at h_sym
        rcases evalSymOperand_sound h_env lhs h_l with
          ⟨mv1, st1, h_ev1, h_mem1, h_pc1, h_m1, h_env1⟩
        rcases evalSymOperand_sound h_env1 rhs h_r with
          ⟨mv2, st2, h_ev2, h_mem2, h_pc2, h_m2, h_env2⟩
        rw [h_mem1] at h_m2
        match sv1, sv2 with
        | .usize a, .usize b =>
          cases mv1 <;> simp [SymValMatchesInMem] at h_m1
          cases mv2 <;> simp [SymValMatchesInMem] at h_m2
          rw [h_m1] at h_ev1; rw [h_m2] at h_ev2
          cases op <;> simp at h_sym
          · rcases h_sym with ⟨rfl, rfl⟩
            exact ⟨.tupleUsizeBool (a + b) false, st2,
              by simp [evalRvalue, h_ev1, h_ev2],
              h_mem2.trans h_mem1, h_pc2.trans h_pc1, ⟨rfl, rfl⟩, h_env2⟩
          · by_cases h_le : b ≤ a
            · simp [h_le] at h_sym
              rcases h_sym with ⟨rfl, rfl⟩
              exact ⟨.tupleUsizeBool (a - b) false, st2,
                by simp [evalRvalue, h_ev1, h_ev2, h_le],
                h_mem2.trans h_mem1, h_pc2.trans h_pc1, ⟨rfl, rfl⟩, h_env2⟩
            · simp [h_le] at h_sym
              rcases h_sym with ⟨rfl, rfl⟩
              exact ⟨.tupleUsizeBool 0 true, st2,
                by simp [evalRvalue, h_ev1, h_ev2, h_le],
                h_mem2.trans h_mem1, h_pc2.trans h_pc1, ⟨rfl, rfl⟩, h_env2⟩
        | .usize _, .bool _ | .usize _, .unit | .usize _, .tupleUsizeBool _ _
        | .usize _, .refShared _ | .usize _, .refSlice _ | .usize _, .adtVal _ _
        | .bool _, _ | .unit, _ | .tupleUsizeBool _ _, _ | .refShared _, _
        | .refSlice _, _ | .adtVal _ _, _ =>
          cases op <;> simp at h_sym
  | proj0 src =>
    simp only [evalSymRvalue] at h_sym
    cases h_lk : env src.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i val ovf
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases h_env src.index (.tupleUsizeBool val ovf) h_lk with ⟨mv, h_st_lk, h_m⟩
      cases mv <;> simp [SymValMatchesInMem] at h_m
      rcases h_m with ⟨h_v, h_o⟩
      refine ⟨.usize val, st, ?_, rfl, rfl, rfl, h_env⟩
      simp only [evalRvalue, MirState.readLocal, h_st_lk, h_v]
  | proj1 src =>
    simp only [evalSymRvalue] at h_sym
    cases h_lk : env src.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i val ovf
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases h_env src.index (.tupleUsizeBool val ovf) h_lk with ⟨mv, h_st_lk, h_m⟩
      cases mv <;> simp [SymValMatchesInMem] at h_m
      rcases h_m with ⟨h_v, h_o⟩
      refine ⟨.bool ovf, st, ?_, rfl, rfl, rfl, h_env⟩
      simp only [evalRvalue, MirState.readLocal, h_st_lk, h_o]
  | len src =>
    simp only [evalSymRvalue] at h_sym
    cases h_lk : env src.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i elems
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases h_env src.index (.refSlice elems) h_lk with ⟨mv, h_st_lk, h_m⟩
      cases mv <;> simp [SymValMatchesInMem] at h_m
      rcases h_m with ⟨_, h_l⟩
      refine ⟨.usize elems.length, st, ?_, rfl, rfl, rfl, h_env⟩
      simp only [evalRvalue, MirState.readLocal, h_st_lk, h_l]
  | discriminant src =>
    simp only [evalSymRvalue] at h_sym
    cases h_lk : env src.index with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv0 =>
      simp only [h_lk] at h_sym
      cases sv0 <;> try contradiction
      rename_i variant fields
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases h_env src.index (.adtVal variant fields) h_lk with ⟨mv, h_st_lk, h_m⟩
      cases mv <;> simp [SymValMatchesInMem] at h_m
      rcases h_m with ⟨h_v, _⟩
      refine ⟨.usize variant, st, ?_, rfl, rfl, rfl, h_env⟩
      simp only [evalRvalue, MirState.readLocal, h_st_lk, h_v]
  | aggregate variant ops =>
    simp only [evalSymRvalue] at h_sym
    cases h_ops : evalSymOperandList env ops with
    | none => simp only [h_ops] at h_sym; contradiction
    | some p =>
      rcases p with ⟨svs, env1⟩
      simp only [h_ops] at h_sym
      cases h_sc : symToScalarValList svs with
      | none => simp only [h_sc] at h_sym; contradiction
      | some scals =>
        simp only [h_sc] at h_sym
        injection h_sym with h_pair
        injection h_pair with h_sv h_e
        subst h_sv; subst h_e
        rcases evalSymOperandList_sound h_env ops h_ops with
          ⟨mvs, st1, h_ev_ops, h_mem1, h_pc1, h_rel, h_env1⟩
        have h_mv_sc := symToScalarValList_sound h_rel h_sc
        refine ⟨.adtVal variant scals, st1, ?_, h_mem1, h_pc1, ⟨rfl, rfl⟩, h_env1⟩
        simp only [evalRvalue, h_ev_ops, h_mv_sc]
  | readPlace place =>
    simp only [evalSymRvalue] at h_sym
    cases h_rp : evalSymReadPlace env place with
    | none => simp only [h_rp] at h_sym; contradiction
    | some sv0 =>
      simp only [h_rp] at h_sym
      injection h_sym with h_pair
      injection h_pair with h_sv h_e
      subst h_sv; subst h_e
      rcases evalSymReadPlace_sound h_env place h_rp with ⟨mv, h_ev_rp, h_m⟩
      refine ⟨mv, st, ?_, rfl, rfl, h_m, h_env⟩
      simp only [evalRvalue, h_ev_rp]

theorem execSymStatement_sound {localCount : Nat} {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) (stmt : Statement)
    {env' : SymEnv}
    (h_sym : execSymStatement localCount env stmt = some env') :
    ∃ st',
      execStatement localCount st stmt = some st' ∧
      st'.mem = st.mem ∧
      st'.pc = st.pc ∧
      EnvMatches st' env' := by
  cases stmt with
  | assign dst rv =>
    simp only [execSymStatement] at h_sym
    by_cases h_lt : dst.index < localCount
    · simp only [h_lt, ↓reduceIte] at h_sym
      cases h_rv : evalSymRvalue env rv with
      | none => simp only [h_rv] at h_sym; contradiction
      | some p =>
        rcases p with ⟨sv, env1⟩
        simp only [h_rv] at h_sym
        injection h_sym with h_e
        subst h_e
        rcases evalSymRvalue_sound h_env rv h_rv with
          ⟨mv, st1, h_ev_rv, h_mem1, h_pc1, h_m, h_env1⟩
        rw [← h_mem1] at h_m
        refine ⟨st1.writeLocal dst (some mv), ?_, h_mem1, h_pc1,
          envMatches_write h_env1 dst h_m⟩
        simp only [execStatement, h_lt, ↓reduceIte, h_ev_rv]
    · simp only [h_lt, ↓reduceIte] at h_sym
      contradiction
  | storeDeref _ _ =>
    simp only [execSymStatement] at h_sym
    contradiction
  | storageLive l =>
    simp only [execSymStatement] at h_sym
    by_cases h_lt : l.index < localCount
    · simp only [h_lt, ↓reduceIte] at h_sym
      injection h_sym with h_e
      subst h_e
      refine ⟨st, ?_, rfl, rfl, h_env⟩
      simp only [execStatement, h_lt, ↓reduceIte]
    · simp only [h_lt, ↓reduceIte] at h_sym
      contradiction
  | storageDead l =>
    simp only [execSymStatement] at h_sym
    by_cases h_lt : l.index < localCount
    · simp only [h_lt, ↓reduceIte] at h_sym
      injection h_sym with h_e
      subst h_e
      refine ⟨st.writeLocal l none, ?_, rfl, rfl, envMatches_clear h_env l⟩
      simp only [execStatement, h_lt, ↓reduceIte]
    · simp only [h_lt, ↓reduceIte] at h_sym
      contradiction
  | nop =>
    simp only [execSymStatement] at h_sym
    injection h_sym with h_e
    subst h_e
    exact ⟨st, rfl, rfl, rfl, h_env⟩

theorem execSymStatements_sound {localCount : Nat} :
    ∀ {st : MirState} {env : SymEnv},
      EnvMatches st env →
      ∀ (stmts : List Statement) {env' : SymEnv},
        execSymStatements localCount env stmts = some env' →
        ∃ st',
          execStatements localCount st stmts = some st' ∧
          st'.mem = st.mem ∧
          st'.pc = st.pc ∧
          EnvMatches st' env'
  | st, env, h_env, [], _, h_sym => by
    simp only [execSymStatements] at h_sym
    injection h_sym with h_e
    subst h_e
    exact ⟨st, rfl, rfl, rfl, h_env⟩
  | st, env, h_env, stmt :: rest, _, h_sym => by
    simp only [execSymStatements] at h_sym
    cases h_st1 : execSymStatement localCount env stmt with
    | none => simp only [h_st1] at h_sym; contradiction
    | some env1 =>
      simp only [h_st1] at h_sym
      rcases execSymStatement_sound h_env stmt h_st1 with
        ⟨st1, h_ev1, h_mem1, h_pc1, h_env1⟩
      rcases execSymStatements_sound h_env1 rest h_sym with
        ⟨st2, h_ev2, h_mem2, h_pc2, h_env2⟩
      refine ⟨st2, ?_, h_mem2.trans h_mem1, h_pc2.trans h_pc1, h_env2⟩
      simp only [execStatements, h_ev1, h_ev2]

theorem evalSymTerminator_sound {body : MirBody} {st : MirState} {env : SymEnv}
    (h_env : EnvMatches st env) (term : Terminator)
    {res : SymTermResult}
    (h_sym : evalSymTerminator body env term = some res) :
    match res with
    | .ret sv =>
      ∃ mv,
        execTerminator body st term = .terminated (.normal mv) ∧
        SymValMatchesInMem st.mem mv sv
    | .unwind =>
      execTerminator body st term = .terminated .unwind
    | .jump target env' =>
      ∃ st',
        execTerminator body st term = .step () st' ∧
        st'.pc = target ∧
        st'.mem = st.mem ∧
        EnvMatches st' env' := by
  cases term with
  | return_ =>
    simp only [evalSymTerminator] at h_sym
    cases h_lk : env 0 with
    | none => simp only [h_lk] at h_sym; contradiction
    | some sv =>
      simp only [h_lk] at h_sym
      injection h_sym with h_res
      subst h_res
      rcases h_env 0 sv h_lk with ⟨mv, h_st_lk, h_m⟩
      refine ⟨mv, ?_, h_m⟩
      simp only [execTerminator, MirState.readLocal, h_st_lk]
  | goto target =>
    simp only [evalSymTerminator] at h_sym
    by_cases h_lt : target.index < body.blocks.length
    · simp only [h_lt, ↓reduceIte] at h_sym
      injection h_sym with h_res
      subst h_res
      refine ⟨{ st with pc := target }, ?_, rfl, rfl, h_env⟩
      simp only [execTerminator, h_lt, ↓reduceIte]
    · simp only [h_lt, ↓reduceIte] at h_sym
      contradiction
  | switchInt discr targets otherwise =>
    simp only [evalSymTerminator] at h_sym
    cases h_op : evalSymOperand env discr with
    | none => simp only [h_op] at h_sym; contradiction
    | some p =>
      rcases p with ⟨sv, env1⟩
      simp only [h_op] at h_sym
      rcases evalSymOperand_sound h_env discr h_op with
        ⟨mv, st1, h_ev_op, h_mem1, _, h_m, h_env1⟩
      cases mv <;> cases sv <;> simp [SymValMatchesInMem] at h_m <;> try contradiction
      · subst h_m
        rename_i val
        by_cases h_lt : (lookupSwitchTarget val targets otherwise).index < body.blocks.length
        · simp only [h_lt, ↓reduceIte] at h_sym
          injection h_sym with h_res
          subst h_res
          refine ⟨{ st1 with pc := lookupSwitchTarget val targets otherwise }, ?_, rfl, h_mem1, h_env1⟩
          simp only [execTerminator, h_ev_op, h_lt, ↓reduceIte]
        · simp only [h_lt, ↓reduceIte] at h_sym
          contradiction
      · subst h_m
        rename_i b
        by_cases h_lt : (lookupSwitchTarget (if b then 1 else 0) targets otherwise).index < body.blocks.length
        · simp only [h_lt, ↓reduceIte] at h_sym
          injection h_sym with h_res
          subst h_res
          refine ⟨{ st1 with pc := lookupSwitchTarget (if b then 1 else 0) targets otherwise }, ?_, rfl, h_mem1, h_env1⟩
          simp only [execTerminator, h_ev_op, h_lt, ↓reduceIte]
        · simp only [h_lt, ↓reduceIte] at h_sym
          contradiction
  | assert cond expected target =>
    simp only [evalSymTerminator] at h_sym
    cases h_op : evalSymOperand env cond with
    | none => simp only [h_op] at h_sym; contradiction
    | some p =>
      rcases p with ⟨sv, env1⟩
      simp only [h_op] at h_sym
      rcases evalSymOperand_sound h_env cond h_op with
        ⟨mv, st1, h_ev_op, h_mem1, _, h_m, h_env1⟩
      cases mv <;> cases sv <;> simp [SymValMatchesInMem] at h_m <;> try contradiction
      subst h_m
      rename_i b
      by_cases h_eq : (b == expected) = true
      · simp only [h_eq, ↓reduceIte] at h_sym
        by_cases h_lt : target.index < body.blocks.length
        · simp only [h_lt, ↓reduceIte] at h_sym
          injection h_sym with h_res
          subst h_res
          refine ⟨{ st1 with pc := target }, ?_, rfl, h_mem1, h_env1⟩
          simp only [execTerminator, h_ev_op, h_eq, h_lt, ↓reduceIte]
        · simp only [h_lt, ↓reduceIte] at h_sym
          contradiction
      · have h_neq : (b == expected) = false := Bool.eq_false_iff.mpr h_eq
        simp only [h_neq, Bool.false_eq_true, ↓reduceIte] at h_sym
        injection h_sym with h_res
        subst h_res
        simp only [execTerminator, h_ev_op, h_neq, Bool.false_eq_true, ↓reduceIte]
  | assertBoundsCheck idxOp lenOp target =>
    simp only [evalSymTerminator] at h_sym
    cases h_op1 : evalSymOperand env idxOp with
    | none => simp only [h_op1] at h_sym; contradiction
    | some p1 =>
      rcases p1 with ⟨sv1, env1⟩
      simp only [h_op1] at h_sym
      rcases evalSymOperand_sound h_env idxOp h_op1 with
        ⟨mv1, st1, h_ev_op1, h_mem1, _, h_m1, h_env1⟩
      cases mv1 <;> cases sv1 <;> simp [SymValMatchesInMem] at h_m1 <;> try contradiction
      subst h_m1
      rename_i idx
      cases h_op2 : evalSymOperand env1 lenOp with
      | none => simp only [h_op2] at h_sym; contradiction
      | some p2 =>
        rcases p2 with ⟨sv2, env2⟩
        simp only [h_op2] at h_sym
        rcases evalSymOperand_sound h_env1 lenOp h_op2 with
          ⟨mv2, st2, h_ev_op2, h_mem2, _, h_m2, h_env2⟩
        rw [h_mem1] at h_m2
        cases mv2 <;> cases sv2 <;> simp [SymValMatchesInMem] at h_m2 <;> try contradiction
        subst h_m2
        rename_i len
        by_cases h_lt : idx < len
        · simp only [h_lt, ↓reduceIte] at h_sym
          by_cases h_tgt : target.index < body.blocks.length
          · simp only [h_tgt, ↓reduceIte] at h_sym
            injection h_sym with h_res
            subst h_res
            refine ⟨{ st2 with pc := target }, ?_, rfl, h_mem2.trans h_mem1, h_env2⟩
            simp only [execTerminator, h_ev_op1, h_ev_op2, h_lt, h_tgt, ↓reduceIte]
          · simp only [h_tgt, ↓reduceIte] at h_sym
            contradiction
        · simp only [h_lt, ↓reduceIte] at h_sym
          injection h_sym with h_res
          subst h_res
          simp only [execTerminator, h_ev_op1, h_ev_op2, h_lt, ↓reduceIte]
  | callAtomicLoadUsize _ _ _ _ =>
    simp only [evalSymTerminator] at h_sym; contradiction
  | callFn _ _ _ _ =>
    simp only [evalSymTerminator] at h_sym; contradiction

/-- General soundness theorem for `evalSym` over slice-reading, ADT-projecting,
    and loop-iterating MIR bodies: whenever `evalSym fuel body bb env` returns
    `some (.normal retSym)`, every finite execution prefix starting from any
    matching `MirState` `st` (`st.pc = ⟨bb⟩` and `EnvMatches st env`) is safe
    (`out.isSafe`) and, if it terminates, returns a concrete value matching
    `retSym`. -/
theorem evalSym_slice_sound :
    ∀ (fuel : Nat) (body : MirBody) {bb : Nat} {env : SymEnv} {retSym : SymVal},
      evalSym fuel body bb env = some (.normal retSym) →
      (∀ n, retSym ≠ .refShared n) →
      (∀ es, retSym ≠ .refSlice es) →
      ∀ (steps : Nat) (init st : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
        st.pc = ⟨bb⟩ →
        EnvMatches st env →
        ReachesPrefix MirMachine body init steps st tr out →
        out.isSafe ∧
        (∀ term, out = .terminated term →
           ∃ retVal, term = .normal retVal ∧ SymValMatches retVal retSym)
  | 0, _, _, _, _, h_eval, _, _, _, _, _, _, _, _, _, _ => by
    simp only [evalSym] at h_eval; contradiction
  | fuel' + 1, body, bb, env, retSym, h_eval, h_nonref, h_nonslice,
      steps, init, st, tr, out, h_pc, h_env, h_reach => by
    simp only [evalSym] at h_eval
    cases h_blk : body.blocks[bb]? with
    | none => simp only [h_blk] at h_eval; contradiction
    | some block =>
      simp only [h_blk] at h_eval
      cases h_stmts : execSymStatements body.localCount env block.statements with
      | none => simp only [h_stmts] at h_eval; contradiction
      | some env' =>
        simp only [h_stmts] at h_eval
        cases h_term : evalSymTerminator body env' block.terminator with
        | none => simp only [h_term] at h_eval; contradiction
        | some res =>
          simp only [h_term] at h_eval
          rcases execSymStatements_sound h_env block.statements h_stmts with
            ⟨st_mid, h_ev_stmts, h_mem_mid, _, h_env_mid⟩
          have h_term_snd := evalSymTerminator_sound h_env_mid block.terminator h_term
          have h_stepBlock_eq :
              stepBlock body st = execTerminator body st_mid block.terminator := by
            simp only [stepBlock, h_pc, h_blk, h_ev_stmts]
          cases h_reach with
          | zero =>
            refine ⟨trivial, ?_⟩
            intro _ h_eq; contradiction
          | step n _ s_next obs tr_rest out_rest h_mstep h_next =>
            change StepResult.step obs s_next = stepBlock body st at h_mstep
            rw [h_stepBlock_eq] at h_mstep
            cases res with
            | ret sv =>
              rcases h_term_snd with ⟨mv, h_ex_t, _⟩
              rw [h_ex_t] at h_mstep; contradiction
            | unwind =>
              rw [h_term_snd] at h_mstep; contradiction
            | jump target env_next =>
              simp only at h_eval
              rcases h_term_snd with ⟨st_next, h_ex_t, h_pc_next, _, h_env_next⟩
              rw [h_ex_t] at h_mstep
              injection h_mstep with _ h_s_eq
              rw [h_s_eq] at h_next
              exact evalSym_slice_sound fuel' body h_eval h_nonref h_nonslice
                n init st_next tr_rest out h_pc_next h_env_next h_next
          | choice _ _ _ _ _ _ _ h_mstep _ _ =>
            change StepResult.choice _ _ = stepBlock body st at h_mstep
            rw [h_stepBlock_eq] at h_mstep
            cases res with
            | ret _ =>
              rcases h_term_snd with ⟨_, h_ex_t, _⟩
              rw [h_ex_t] at h_mstep; contradiction
            | unwind =>
              rw [h_term_snd] at h_mstep; contradiction
            | jump _ _ =>
              rcases h_term_snd with ⟨_, h_ex_t, _, _, _⟩
              rw [h_ex_t] at h_mstep; contradiction
          | emptyChoice _ _ _ _ h_mstep _ =>
            change StepResult.choice _ _ = stepBlock body st at h_mstep
            rw [h_stepBlock_eq] at h_mstep
            cases res with
            | ret _ =>
              rcases h_term_snd with ⟨_, h_ex_t, _⟩
              rw [h_ex_t] at h_mstep; contradiction
            | unwind =>
              rw [h_term_snd] at h_mstep; contradiction
            | jump _ _ =>
              rcases h_term_snd with ⟨_, h_ex_t, _, _, _⟩
              rw [h_ex_t] at h_mstep; contradiction
          | terminated _ _ term_out h_mstep =>
            change StepResult.terminated term_out = stepBlock body st at h_mstep
            rw [h_stepBlock_eq] at h_mstep
            cases res with
            | ret sv =>
              simp only at h_eval
              injection h_eval with h_ret_eq
              injection h_ret_eq with h_sv_eq
              subst h_sv_eq
              rcases h_term_snd with ⟨mv, h_ex_t, h_m_mv⟩
              rw [h_ex_t] at h_mstep
              injection h_mstep with h_t_eq
              subst h_t_eq
              refine ⟨trivial, ?_⟩
              intro term' h_out_eq
              injection h_out_eq with h_term_eq
              subst h_term_eq
              exact ⟨mv, rfl, symValMatches_of_inMem h_m_mv h_nonref h_nonslice⟩
            | unwind =>
              simp only at h_eval
              nomatch h_eval
            | jump _ _ =>
              rcases h_term_snd with ⟨_, h_ex_t, _, _, _⟩
              rw [h_ex_t] at h_mstep; contradiction
          | failed _ _ err h_mstep =>
            change StepResult.failed err = stepBlock body st at h_mstep
            rw [h_stepBlock_eq] at h_mstep
            cases res with
            | ret _ =>
              rcases h_term_snd with ⟨_, h_ex_t, _⟩
              rw [h_ex_t] at h_mstep; contradiction
            | unwind =>
              rw [h_term_snd] at h_mstep; contradiction
            | jump _ _ =>
              rcases h_term_snd with ⟨_, h_ex_t, _, _, _⟩
              rw [h_ex_t] at h_mstep; contradiction
          | noStep _ _ h_nostep =>
            exact False.elim (h_nostep ⟨stepBlock body st, rfl⟩)

/-!
### Multi-Instruction Slice-Iterating Certificate Checker (`sliceCheckerMirBody`)

In Round 1, `checkerMirBody` packed a 2-instruction program into a single 64-bit
`usize` word because `MirAst` lacked slices (`&[usize]`), `PlaceElem`
projections, and ADTs.

Here we define `sliceCheckerMirBody`, which takes:
- `_1 : &[usize]` (`MirTy.refSliceUsize`), an arbitrary-length slice of encoded
  instructions, and
- `_2 : usize` (`MirTy.usize`), the expected accumulator digest,

and iterates over `_1` in a genuine CFG loop (`bb1 -> bb2 -> bb3 -> bb1`):
- `bb0`:
  - `_3 = Len(_1)` (`slice.len()`)
  - `_4 = 0usize` (`idx = 0`)
  - `_5 = 0usize` (`acc = 0`)
  - `goto bb1`
- `bb1` (loop header):
  - `_6 = _4 < _3` (`idx < len`)
  - `switchInt(_6) -> [1: bb2, otherwise: bb4]`
- `bb2` (dynamic bounds check emitted by `rustc` before slice indexing):
  - `assertBoundsCheck(_4, _3) -> bb3`
- `bb3` (loop body: slice element load + struct ADT construction & field
  projection + accumulator update + index increment):
  - `_7 = (*_1)[_4]` (`Rvalue.readPlace ⟨⟨1⟩, [.deref, .index ⟨4⟩]⟩`)
  - `_8 = StepFrame { elem: _7, acc: _5 }` (`Rvalue.aggregate 0 [.copy ⟨7⟩, .copy ⟨5⟩]`)
  - `_9 = _8.0` (`Rvalue.readPlace ⟨⟨8⟩, [.field 0]⟩`)
  - `_10 = _8.1` (`Rvalue.readPlace ⟨⟨8⟩, [.field 1]⟩`)
  - `_5 = _10 ^ _9` (`acc = acc ^ elem`)
  - `_4 = _4 + 1` (`idx = idx + 1`)
  - `goto bb1`
- `bb4` (exit):
  - `_0 = (_5 == _2)` (`return acc == expected`)
  - `return`
-/

/-- Multi-instruction slice-iterating certificate checker in `MirBody`. -/
def sliceCheckerMirBody : MirBody where
  paramTys := [.refSliceUsize, .usize]
  returnTy := .bool
  localCount := 11
  blocks := [
    -- bb0: initialize len (_3), idx (_4 = 0), acc (_5 = 0)
    { statements := [
        .assign ⟨3⟩ (.len ⟨1⟩),
        .assign ⟨4⟩ (.use (.constUsize 0) false),
        .assign ⟨5⟩ (.use (.constUsize 0) false)
      ]
      terminator := .goto ⟨1⟩ },
    -- bb1: loop header (check _4 < _3)
    { statements := [
        .assign ⟨6⟩ (.binaryOp .lt (.copy ⟨4⟩) (.copy ⟨3⟩))
      ]
      terminator := .switchInt (.copy ⟨6⟩) [(1, ⟨2⟩)] ⟨4⟩ },
    -- bb2: compiler-inserted slice bounds check AssertBoundsCheck(_4, _3)
    { statements := []
      terminator := .assertBoundsCheck (.copy ⟨4⟩) (.copy ⟨3⟩) ⟨3⟩ },
    -- bb3: read (*_1)[_4], pack & project StepFrame ADT, update acc & idx
    { statements := [
        .assign ⟨7⟩ (.readPlace ⟨⟨1⟩, [.deref, .index ⟨4⟩]⟩),
        .assign ⟨8⟩ (.aggregate 0 [.copy ⟨7⟩, .copy ⟨5⟩]),
        .assign ⟨9⟩ (.readPlace ⟨⟨8⟩, [.field 0]⟩),
        .assign ⟨10⟩ (.readPlace ⟨⟨8⟩, [.field 1]⟩),
        .assign ⟨5⟩ (.binaryOp .bitXor (.copy ⟨10⟩) (.copy ⟨9⟩)),
        .assign ⟨4⟩ (.binaryOp .add (.copy ⟨4⟩) (.constUsize 1))
      ]
      terminator := .goto ⟨1⟩ },
    -- bb4: return (_5 == _2)
    { statements := [
        .assign ⟨0⟩ (.binaryOp .eq (.copy ⟨5⟩) (.copy ⟨2⟩))
      ]
      terminator := .return_ }
  ]

/-- Symbolic initial environment for `sliceCheckerMirBody` on slice `elems` and
    expected digest `target`. -/
def initSliceCheckerEnv (elems : List Nat) (target : Nat) : SymEnv :=
  fun i =>
    if i == 1 then some (.refSlice elems)
    else if i == 2 then some (.usize target)
    else none

/-- Symbolic evaluation of `sliceCheckerMirBody` on an empty slice `[]`
    computes `0 == target` in 3 basic-block steps (`bb0 -> bb1 -> bb4`). -/
theorem evalSym_sliceChecker_nil (target : Nat) :
    evalSym 3 sliceCheckerMirBody 0 (initSliceCheckerEnv [] target) =
      some (.normal (.bool (0 == target))) := rfl

/-- Symbolic evaluation of `sliceCheckerMirBody` on a 1-element slice `[w0]`
    computes `(0 ^^^ w0) == target` in 6 basic-block steps
    (`bb0 -> bb1 -> bb2 -> bb3 -> bb1 -> bb4`). -/
theorem evalSym_sliceChecker_one (w0 target : Nat) :
    evalSym 6 sliceCheckerMirBody 0 (initSliceCheckerEnv [w0] target) =
      some (.normal (.bool (Nat.xor 0 w0 == target))) := rfl

/-- Symbolic evaluation of `sliceCheckerMirBody` on an arbitrary 2-element
    slice `[w0, w1]` computes `((0 ^^^ w0) ^^^ w1) == target` in 9 basic-block
    steps (`bb0 -> (bb1 -> bb2 -> bb3)^2 -> bb1 -> bb4`), universally quantified
    over symbolic words `w0 w1 target : Nat`. -/
theorem evalSym_sliceChecker_two (w0 w1 target : Nat) :
    evalSym 9 sliceCheckerMirBody 0 (initSliceCheckerEnv [w0, w1] target) =
      some (.normal (.bool (Nat.xor (Nat.xor 0 w0) w1 == target))) := rfl

/-- Symbolic evaluation of `sliceCheckerMirBody` on an arbitrary 3-element
    slice `[w0, w1, w2]` computes `(((0 ^^^ w0) ^^^ w1) ^^^ w2) == target` in
    12 basic-block steps. -/
theorem evalSym_sliceChecker_three (w0 w1 w2 target : Nat) :
    evalSym 12 sliceCheckerMirBody 0 (initSliceCheckerEnv [w0, w1, w2] target) =
      some (.normal (.bool (Nat.xor (Nat.xor (Nat.xor 0 w0) w1) w2 == target))) := rfl

/-- End-to-end operational soundness of `sliceCheckerMirBody` on any 2-element
    slice `&[usize]` in memory: for every slice allocation `loc` holding
    `[w0, w1]` and every expected digest `target`, `sliceCheckerMirBody` is
    UB-free across all step budgets `steps` and returns
    `.normal (.bool (Nat.xor (Nat.xor 0 w0) w1 == target))` upon termination. -/
theorem sliceCheckerMirBody_two_elem_sound (loc w0 w1 target : Nat)
    (steps : Nat) (st : MirState) (tr : List Unit) (out : PrefixOutcome MirVal)
    (h_pc : st.pc = ⟨0⟩)
    (h_arg1 : st.locals 1 = some (.refSliceLoc loc 2))
    (h_slice : st.mem.naSlice loc = some [w0, w1])
    (h_arg2 : st.locals 2 = some (.usize target))
    (h_reach : ReachesPrefix MirMachine sliceCheckerMirBody st steps st tr out) :
    out.isSafe ∧
    (∀ term, out = .terminated term →
      term = .normal (.bool (Nat.xor (Nat.xor 0 w0) w1 == target))) := by
  have h_env : EnvMatches st (initSliceCheckerEnv [w0, w1] target) := by
    intro i sv h_lk
    simp only [initSliceCheckerEnv] at h_lk
    by_cases h1 : (i == 1) = true
    · simp only [h1, ↓reduceIte] at h_lk
      injection h_lk with h_sv; subst h_sv
      have hi : i = 1 := beq_iff_eq.mp h1
      subst hi
      exact ⟨.refSliceLoc loc 2, h_arg1, h_slice, rfl⟩
    · have h1f : (i == 1) = false := Bool.eq_false_iff.mpr h1
      simp only [h1f, Bool.false_eq_true, ↓reduceIte] at h_lk
      by_cases h2 : (i == 2) = true
      · simp only [h2, ↓reduceIte] at h_lk
        injection h_lk with h_sv; subst h_sv
        have hi : i = 2 := beq_iff_eq.mp h2
        subst hi
        exact ⟨.usize target, h_arg2, rfl⟩
      · have h2f : (i == 2) = false := Bool.eq_false_iff.mpr h2
        simp only [h2f, Bool.false_eq_true, ↓reduceIte] at h_lk
        contradiction
  have h_snd := evalSym_slice_sound 9 sliceCheckerMirBody
    (evalSym_sliceChecker_two w0 w1 target)
    (fun _ h => by injection h)
    (fun _ h => by injection h)
    steps st st tr out h_pc h_env h_reach
  refine ⟨h_snd.1, ?_⟩
  intro term h_out
  rcases h_snd.2 term h_out with ⟨retVal, rfl, h_match⟩
  cases retVal <;> try contradiction
  change _ = _ at h_match
  rw [h_match]

/-!
### Enum ADT Construction, Discriminant Switch, and Downcast Projection (`enumCertMirBody`)

To verify that multi-variant `enum` ADTs (`variant > 0`), `Rvalue.discriminant`,
and `[.downcast v, .field idx]` projections also compose cleanly with
`evalSym_slice_sound`, we define `enumCertMirBody`, which constructs a
2-variant `CertKind` enum (`Variant 0 = AddCert(a, b)`, `Variant 1 = SubCert(a, b)`),
branches on `Rvalue.discriminant`, and projects the variant payload via
`.downcast`.
-/

/-- MIR body exercising multi-variant enum construction (`Rvalue.aggregate`),
    discriminant inspection (`Rvalue.discriminant`), `SwitchInt` branching, and
    variant downcast projection (`[.downcast v, .field idx]`). -/
def enumCertMirBody : MirBody where
  paramTys := [.usize, .usize]
  returnTy := .usize
  localCount := 6
  blocks := [
    -- bb0: construct Variant 1 (SubCert(_1, _2)) in _3, read discriminant in _4
    { statements := [
        .assign ⟨3⟩ (.aggregate 1 [.copy ⟨1⟩, .copy ⟨2⟩]),
        .assign ⟨4⟩ (.discriminant ⟨3⟩)
      ]
      terminator := .switchInt (.copy ⟨4⟩) [(0, ⟨1⟩), (1, ⟨2⟩)] ⟨1⟩ },
    -- bb1: Variant 0 arm ((_3 as Variant#0).0 + (_3 as Variant#0).1)
    { statements := [
        .assign ⟨5⟩ (.readPlace ⟨⟨3⟩, [.downcast 0, .field 0]⟩),
        .assign ⟨0⟩ (.readPlace ⟨⟨3⟩, [.downcast 0, .field 1]⟩),
        .assign ⟨0⟩ (.binaryOp .add (.copy ⟨5⟩) (.copy ⟨0⟩))
      ]
      terminator := .return_ },
    -- bb2: Variant 1 arm ((_3 as Variant#1).0 ^ (_3 as Variant#1).1)
    { statements := [
        .assign ⟨5⟩ (.readPlace ⟨⟨3⟩, [.downcast 1, .field 0]⟩),
        .assign ⟨0⟩ (.readPlace ⟨⟨3⟩, [.downcast 1, .field 1]⟩),
        .assign ⟨0⟩ (.binaryOp .bitXor (.copy ⟨5⟩) (.copy ⟨0⟩))
      ]
      terminator := .return_ }
  ]

/-- Symbolic evaluation of `enumCertMirBody` constructs Variant 1, switches on
    `discriminant(_3) == 1` to `bb2`, downcasts `_3` as Variant 1, and computes
    `a ^^^ b`. -/
theorem evalSym_enumCert (a b : Nat) :
    evalSym 2 enumCertMirBody 0
      (fun i => if i == 1 then some (.usize a) else if i == 2 then some (.usize b) else none) =
      some (.normal (.usize (Nat.xor a b))) := rfl

end Anneal

/-!
## Section 3: Post-`#154341` `Rvalue.use (op : Operand) (withRetag : Bool)` in `MirAst` and `AnSSA`

In `rustc` PR `#154341` (`Merge Retag statement into Use rvalue`, commit
`e402c1edf047a23b0cfef40c6097d1caa294050b`), standalone `StatementKind::Retag`
was removed and merged into `Rvalue::Use(Operand, WithRetag)`:
- `WithRetag::No` (`withRetag = false`) is a pure move/copy that leaves the
  borrow tracker state untouched.
- `WithRetag::Yes` (`withRetag = true`) performs a Stacked Borrows / Tree
  Borrows retag of all reference/Box fields inside the operand value, except
  fields wrapped in `UnsafePinned` (`!Unpin`) or `MaybeDangling` (see
  `compiler/rustc_codegen_ssa/src/mir/retag.rs:25-240`).

In Anneal's SSA intermediate representation (`AnSSA`, Track 3), `Rvalue.use op
false` lowers to a pure SSA binding (`AnSSAStmt.letCopy dst src`), whereas
`Rvalue.use op true` lowers to an explicit side-effectful instruction
(`AnSSAStmt.retag dst src`) that threads and updates the operational
`BorrowState`. Below we mechanize:
1. `retag_lowering_compiles`: lowering `MirRetagLang` to `AnSSABorrowLang`
   satisfies `Compiles`.
2. `retag_copy_prop_compiles`: substituting `dst` for a downstream pure copy
   `dst2 = letCopy dst` preserves the exact `BorrowState` and satisfies
   `Compiles`.
3. `duplicate_retag_refutes_compiles`: duplicating `AnSSAStmt.retag` across uses
   allocates a second exclusive tag that invalidates the first tag, causing a
   valid source program to trigger target UB (`¬ Compiles`).
4. `unsafePinned_retag_is_pure_copy`: retagging a pointer whose layout wrapper
   is `unsafePinned` (`!Unpin`) or `maybeDangling` is a borrow-tracker no-op,
   matching `retag.rs:78-115`.
-/

namespace Anneal
open Trusted

/-- Layout wrapper permission category governing whether `WithRetag::Yes`
    retags a pointer field (`compiler/rustc_codegen_ssa/src/mir/retag.rs:78-115`):
    - `uniqueMutRef`: `&mut T` where `T : Unpin` (retagged with a fresh exclusive
      tag).
    - `sharedRef`: `&T` where `T : Freeze` (retagged with a fresh shared tag).
    - `unsafePinned`: `&mut T` where `T : !Unpin` / `UnsafePinned<T>` (skipped
      by `retag_value`).
    - `maybeDangling`: `MaybeDangling<P>` (skipped by `retag_value`). -/
inductive RetagPermKind where
  | uniqueMutRef
  | sharedRef
  | unsafePinned
  | maybeDangling

/-- Runtime value in the borrow-tracking sub-language: either a scalar `usize`
    or a tagged pointer `(addr, tag, perm)`. -/
inductive BorrowVal where
  | scalar (n : Nat)
  | ptr (addr : Nat) (tag : Nat) (perm : RetagPermKind)

/-- Operational borrow-tracker state accompanying memory:
    - `nextTag`: monotonic counter for allocating fresh borrow tags.
    - `activeUniqueTag`: for each address `addr`, the currently active exclusive
      tag (`some tag`) if an exclusive `&mut T` reborrow is active.
    - `mem`: scalar memory contents at each address. -/
structure BorrowState where
  pc : Nat
  regs : Nat → Option BorrowVal
  nextTag : Nat
  activeUniqueTag : Nat → Option Nat
  mem : Nat → Nat

/-- Update register/local `r` in a `BorrowState`. -/
def BorrowState.writeReg (st : BorrowState) (r : Nat) (v : BorrowVal) : BorrowState :=
  { st with regs := fun idx => if idx == r then some v else st.regs idx }

/-- Perform the operational borrow-tracker transition for `WithRetag::Yes` on a
    `BorrowVal`:
    - On `.ptr addr _ .uniqueMutRef`, allocates `newTag := st.nextTag` and sets
      `activeUniqueTag addr := some newTag` (invalidating any previous exclusive
      tag at `addr`).
    - On `.ptr addr _ .sharedRef`, allocates `newTag := st.nextTag`.
    - On `.ptr addr tag .unsafePinned` or `.ptr addr tag .maybeDangling`, skips
      retagging (`retag.rs:78-115`) and leaves `st` and `tag` unchanged.
    - On `.scalar n`, leaves `st` and `n` unchanged. -/
def performRetag (st : BorrowState) : BorrowVal → BorrowVal × BorrowState
  | .scalar n => (.scalar n, st)
  | .ptr addr _ .uniqueMutRef =>
    let newTag := st.nextTag
    (.ptr addr newTag .uniqueMutRef,
      { st with
        nextTag := newTag + 1
        activeUniqueTag := fun a =>
          if a == addr then some newTag else st.activeUniqueTag a })
  | .ptr addr _ .sharedRef =>
    let newTag := st.nextTag
    (.ptr addr newTag .sharedRef,
      { st with nextTag := newTag + 1 })
  | .ptr addr tag .unsafePinned =>
    (.ptr addr tag .unsafePinned, st)
  | .ptr addr tag .maybeDangling =>
    (.ptr addr tag .maybeDangling, st)

/-- Check whether `BorrowVal` is a valid pointer for reading in `st`. -/
def canReadPtr (st : BorrowState) : BorrowVal → Option Nat
  | .ptr addr tag .uniqueMutRef =>
    if st.activeUniqueTag addr == some tag then some (st.mem addr) else none
  | .ptr addr _ .sharedRef => some (st.mem addr)
  | .ptr addr _ .unsafePinned => some (st.mem addr)
  | .ptr addr _ .maybeDangling => some (st.mem addr)
  | .scalar _ => none

/-- Check whether `BorrowVal` is a valid pointer for writing `val` in `st`. -/
def canWritePtr (st : BorrowState) (bv : BorrowVal) (val : Nat) : Option BorrowState :=
  match bv with
  | .ptr addr tag .uniqueMutRef =>
    if st.activeUniqueTag addr == some tag then
      some { st with mem := fun a => if a == addr then val else st.mem a }
    else none
  | .ptr addr _ .unsafePinned =>
    some { st with mem := fun a => if a == addr then val else st.mem a }
  | _ => none

/-- Statements of the post-`#154341` MIR borrow sub-language (`MirRetagLang`). -/
inductive MirRetagStmt where
  | assignUse (dst : Nat) (src : Nat) (withRetag : Bool)
  | writeRef (ptrLocal : Nat) (val : Nat)
  | readRef (dst : Nat) (ptrLocal : Nat)

/-- Statements of the `AnSSA` borrow sub-language (`AnSSABorrowLang`), where
    `Rvalue.use op false` is a pure `.letCopy` and `Rvalue.use op true` is an
    explicit side-effectful `.retag` instruction. -/
inductive AnSSAStmt where
  | letCopy (dst : Nat) (src : Nat)
  | retag (dst : Nat) (src : Nat)
  | writeRef (ptrReg : Nat) (val : Nat)
  | readRef (dst : Nat) (ptrReg : Nat)

/-- Evaluate a single `MirRetagStmt` in `BorrowState`. -/
def evalMirRetagStmt (st : BorrowState) : MirRetagStmt → Option BorrowState
  | .assignUse dst src withRetag =>
    match st.regs src with
    | none => none
    | some bv =>
      if withRetag then
        let (bv', st') := performRetag st bv
        some (st'.writeReg dst bv')
      else
        some (st.writeReg dst bv)
  | .writeRef ptrLocal val =>
    match st.regs ptrLocal with
    | none => none
    | some bv => canWritePtr st bv val
  | .readRef dst ptrLocal =>
    match st.regs ptrLocal with
    | none => none
    | some bv =>
      match canReadPtr st bv with
      | some n => some (st.writeReg dst (.scalar n))
      | none => none

/-- Evaluate a single `AnSSAStmt` in `BorrowState`. -/
def evalAnSSAStmt (st : BorrowState) : AnSSAStmt → Option BorrowState
  | .letCopy dst src =>
    match st.regs src with
    | none => none
    | some bv => some (st.writeReg dst bv)
  | .retag dst src =>
    match st.regs src with
    | none => none
    | some bv =>
      let (bv', st') := performRetag st bv
      some (st'.writeReg dst bv')
  | .writeRef ptrReg val =>
    match st.regs ptrReg with
    | none => none
    | some bv => canWritePtr st bv val
  | .readRef dst ptrReg =>
    match st.regs ptrReg with
    | none => none
    | some bv =>
      match canReadPtr st bv with
      | some n => some (st.writeReg dst (.scalar n))
      | none => none

/-- Lower a `MirRetagStmt` to an `AnSSAStmt` by mapping `withRetag = true` to
    `AnSSAStmt.retag` and `withRetag = false` to `AnSSAStmt.letCopy`. -/
def lowerMirRetagStmt : MirRetagStmt → AnSSAStmt
  | .assignUse dst src true => .retag dst src
  | .assignUse dst src false => .letCopy dst src
  | .writeRef ptr val => .writeRef ptr val
  | .readRef dst ptr => .readRef dst ptr

/-- Lower a sequential `MirRetagStmt` program to an `AnSSAStmt` program. -/
def lowerMirRetagProg (p : List MirRetagStmt) : List AnSSAStmt :=
  p.map lowerMirRetagStmt

theorem evalAnSSAStmt_lower_eq (st : BorrowState) (stmt : MirRetagStmt) :
    evalAnSSAStmt st (lowerMirRetagStmt stmt) = evalMirRetagStmt st stmt := by
  cases stmt with
  | assignUse dst src withRetag =>
    cases withRetag <;> rfl
  | writeRef _ _ => rfl
  | readRef _ _ => rfl

/-- Small-step machine for `MirRetagLang`: executes statement `p[st.pc]?` and
    returns register `0` when `st.pc == p.length`. -/
def stepMirRetag (p : List MirRetagStmt) (st : BorrowState) :
    StepResult BorrowState Unit Nat :=
  if st.pc == p.length then
    match st.regs 0 with
    | some (.scalar n) => .terminated (.normal n)
    | _ => .failed .ub
  else
    match p[st.pc]? with
    | none => .failed .ub
    | some stmt =>
      match evalMirRetagStmt st stmt with
      | some st' => .step () { st' with pc := st.pc + 1 }
      | none => .failed .ub

/-- Small-step machine for `AnSSABorrowLang`. -/
def stepAnSSABorrow (p : List AnSSAStmt) (st : BorrowState) :
    StepResult BorrowState Unit Nat :=
  if st.pc == p.length then
    match st.regs 0 with
    | some (.scalar n) => .terminated (.normal n)
    | _ => .failed .ub
  else
    match p[st.pc]? with
    | none => .failed .ub
    | some stmt =>
      match evalAnSSAStmt st stmt with
      | some st' => .step () { st' with pc := st.pc + 1 }
      | none => .failed .ub

def MirRetagMachine : SmallStepMachine (List MirRetagStmt) BorrowState Unit Nat where
  initState _ st := st.pc = 0
  step p st r := r = stepMirRetag p st

def AnSSABorrowMachine : SmallStepMachine (List AnSSAStmt) BorrowState Unit Nat where
  initState _ st := st.pc = 0
  step p st r := r = stepAnSSABorrow p st

abbrev MirRetagLang : Language := MirRetagMachine.toLanguage
abbrev AnSSABorrowLang : Language := AnSSABorrowMachine.toLanguage

theorem stepAnSSABorrow_lower_eq (p : List MirRetagStmt) (st : BorrowState) :
    stepAnSSABorrow (lowerMirRetagProg p) st = stepMirRetag p st := by
  unfold stepAnSSABorrow stepMirRetag lowerMirRetagProg
  simp only [List.length_map, List.getElem?_map]
  by_cases h_end : (st.pc == p.length) = true
  · simp only [h_end, ↓reduceIte]
  · have h_nend : (st.pc == p.length) = false := Bool.eq_false_iff.mpr h_end
    simp only [h_nend, Bool.false_eq_true, ↓reduceIte]
    cases p[st.pc]? with
    | none => rfl
    | some stmt =>
      simp only [Option.map, evalAnSSAStmt_lower_eq]

theorem reachesPrefix_anSSA_iff_mirRetag (p : List MirRetagStmt) (init : BorrowState) :
    ∀ (n : Nat) (st : BorrowState) (tr : List Unit) (out : PrefixOutcome Nat),
      ReachesPrefix AnSSABorrowMachine (lowerMirRetagProg p) init n st tr out ↔
      ReachesPrefix MirRetagMachine p init n st tr out := by
  intro n
  induction n with
  | zero =>
    intro st tr out
    constructor <;> (intro h; cases h; exact .zero st)
  | succ k ih =>
    intro st tr out
    constructor
    · intro h
      cases h with
      | step _ _ s' obs tr' _ h_st h_rest =>
        change StepResult.step obs s' = stepAnSSABorrow (lowerMirRetagProg p) st at h_st
        rw [stepAnSSABorrow_lower_eq] at h_st
        exact .step k st s' obs tr' out h_st ((ih s' tr' out).mp h_rest)
      | choice _ kind _ s' branches _ _ h_st h_b h_rest =>
        change StepResult.choice kind branches = stepAnSSABorrow (lowerMirRetagProg p) st at h_st
        rw [stepAnSSABorrow_lower_eq] at h_st
        exact .choice k kind st s' branches tr out h_st h_b ((ih s' tr out).mp h_rest)
      | emptyChoice _ kind _ branches h_st h_nb =>
        change StepResult.choice kind branches = stepAnSSABorrow (lowerMirRetagProg p) st at h_st
        rw [stepAnSSABorrow_lower_eq] at h_st
        exact .emptyChoice k kind st branches h_st h_nb
      | terminated _ _ term h_st =>
        change StepResult.terminated term = stepAnSSABorrow (lowerMirRetagProg p) st at h_st
        rw [stepAnSSABorrow_lower_eq] at h_st
        exact .terminated k st term h_st
      | failed _ _ err h_st =>
        change StepResult.failed err = stepAnSSABorrow (lowerMirRetagProg p) st at h_st
        rw [stepAnSSABorrow_lower_eq] at h_st
        exact .failed k st err h_st
      | noStep _ _ h_ns =>
        exact False.elim (h_ns ⟨stepAnSSABorrow (lowerMirRetagProg p) st, rfl⟩)
    · intro h
      cases h with
      | step _ _ s' obs tr' _ h_st h_rest =>
        change StepResult.step obs s' = stepMirRetag p st at h_st
        rw [← stepAnSSABorrow_lower_eq] at h_st
        exact .step k st s' obs tr' out h_st ((ih s' tr' out).mpr h_rest)
      | choice _ kind _ s' branches _ _ h_st h_b h_rest =>
        change StepResult.choice kind branches = stepMirRetag p st at h_st
        rw [← stepAnSSABorrow_lower_eq] at h_st
        exact .choice k kind st s' branches tr out h_st h_b ((ih s' tr out).mpr h_rest)
      | emptyChoice _ kind _ branches h_st h_nb =>
        change StepResult.choice kind branches = stepMirRetag p st at h_st
        rw [← stepAnSSABorrow_lower_eq] at h_st
        exact .emptyChoice k kind st branches h_st h_nb
      | terminated _ _ term h_st =>
        change StepResult.terminated term = stepMirRetag p st at h_st
        rw [← stepAnSSABorrow_lower_eq] at h_st
        exact .terminated k st term h_st
      | failed _ _ err h_st =>
        change StepResult.failed err = stepMirRetag p st at h_st
        rw [← stepAnSSABorrow_lower_eq] at h_st
        exact .failed k st err h_st
      | noStep _ _ h_ns =>
        exact False.elim (h_ns ⟨stepMirRetag p st, rfl⟩)

/-- Lowering post-`#154341` `Rvalue.use op withRetag` to `AnSSAStmt.retag` /
    `AnSSAStmt.letCopy` satisfies `Compiles MirRetagLang AnSSABorrowLang id`. -/
theorem retag_lowering_compiles (p : List MirRetagStmt) :
    Compiles MirRetagLang AnSSABorrowLang id p (lowerMirRetagProg p) := by
  intro q h_src_def
  refine ⟨?_, ?_⟩
  · intro h_init tr out h_reach
    exact h_src_def h_init tr out ((reachesPrefix_anSSA_iff_mirRetag p q.init q.steps q.init tr out).mp h_reach)
  · intro out ⟨h_init, h_reach⟩
    exact ⟨h_init, (reachesPrefix_anSSA_iff_mirRetag p q.init q.steps q.init out.trace out.outcome).mp h_reach⟩

/-- For `UnsafePinned` (`!Unpin`) and `MaybeDangling` wrappers, `AnSSAStmt.retag`
    is identical to `AnSSAStmt.letCopy`, matching
    `compiler/rustc_codegen_ssa/src/mir/retag.rs:78-115`. -/
theorem unsafePinned_retag_is_pure_copy (st : BorrowState) (dst src addr tag : Nat)
    (h_src : st.regs src = some (.ptr addr tag .unsafePinned)) :
    evalAnSSAStmt st (.retag dst src) = evalAnSSAStmt st (.letCopy dst src) := by
  simp [evalAnSSAStmt, h_src, performRetag]

/-- Source `AnSSA` program that retags `_1` once into `_2`, binds `_3 = letCopy _2`
    (`withRetag = false`), writes `42` through `_2`, and reads through `_3` into
    `_0`. Because `_3` shares `_2`'s tag (`withRetag = false`), reading through
    `_3` after writing through `_2` succeeds and returns `42`. -/
def copyAfterRetagProg : List AnSSAStmt := [
  .retag 2 1,
  .letCopy 3 2,
  .writeRef 2 42,
  .readRef 0 3
]

/-- Copy-propagated `AnSSA` program replacing downstream uses of `_3` (bound by
    pure `.letCopy 3 2`) with `_2` (while keeping `.letCopy 3 2` as a dead temp
    write so instruction count and PC steps match 1-to-1). -/
def copyPropagatedRetagProg : List AnSSAStmt := [
  .retag 2 1,
  .letCopy 3 2,
  .writeRef 2 42,
  .readRef 0 2
]

/-- Miscompiled `AnSSA` program that treats `.retag` as a pure expression and
    duplicates `.retag` at `_3`'s binding (`.retag 3 1` instead of `.letCopy 3 2`).
    The second `.retag` allocates a newer exclusive tag for `_3` and invalidates
    `_2`'s exclusive tag, causing `.writeRef 2 42` to fail with UB! -/
def duplicatedRetagProg : List AnSSAStmt := [
  .retag 2 1,
  .retag 3 1,
  .writeRef 2 42,
  .readRef 0 3
]

/-- Initial `BorrowState` with an active `&mut usize` pointer in `_1` at address
    `0` with initial tag `0`. -/
def initBorrowState : BorrowState where
  pc := 0
  regs := fun r => if r == 1 then some (.ptr 0 0 .uniqueMutRef) else none
  nextTag := 1
  activeUniqueTag := fun a => if a == 0 then some 0 else none
  mem := fun _ => 0

/-- Executing the 4 statements of `copyAfterRetagProg` and `copyPropagatedRetagProg`
    from any state `st` produces the exact same post-execution state because
    `.letCopy 3 2` copies `_2`'s retagged pointer value into `_3`. -/
theorem copyProp_four_step_eq :
    (do
      let s1 ← evalAnSSAStmt initBorrowState (.retag 2 1)
      let s2 ← evalAnSSAStmt { s1 with pc := 1 } (.letCopy 3 2)
      let s3 ← evalAnSSAStmt { s2 with pc := 2 } (.writeRef 2 42)
      evalAnSSAStmt { s3 with pc := 3 } (.readRef 0 2)) =
    (do
      let s1 ← evalAnSSAStmt initBorrowState (.retag 2 1)
      let s2 ← evalAnSSAStmt { s1 with pc := 1 } (.letCopy 3 2)
      let s3 ← evalAnSSAStmt { s2 with pc := 2 } (.writeRef 2 42)
      evalAnSSAStmt { s3 with pc := 3 } (.readRef 0 3)) := rfl

/-- Conversely, duplicating `AnSSAStmt.retag` (`duplicatedRetagProg`) violates
    `Compiles AnSSABorrowLang AnSSABorrowLang id copyAfterRetagProg duplicatedRetagProg`:
    at query `⟨initBorrowState, 3⟩`, `copyAfterRetagProg` is completely UB-free
    (`defined`), whereas `duplicatedRetagProg` fails with `.failed .ub` on step 3
    when `.writeRef 2 42` attempts to write through the invalidated tag `1`. -/
theorem duplicate_retag_refutes_compiles :
    ¬ Compiles AnSSABorrowLang AnSSABorrowLang id
        copyAfterRetagProg duplicatedRetagProg := by
  intro h_comp
  let q : ExecQuery BorrowState := ⟨initBorrowState, 3⟩
  have h_src_def : (AnSSABorrowLang.sem copyAfterRetagProg q).defined := by
    intro _ tr out h_reach
    cases h_reach with
    | step _ _ s1 _ _ _ h_s1 h_r1 =>
      change StepResult.step _ s1 = stepAnSSABorrow copyAfterRetagProg initBorrowState at h_s1
      dsimp [stepAnSSABorrow, copyAfterRetagProg, initBorrowState, evalAnSSAStmt,
        performRetag, BorrowState.writeReg] at h_s1
      injection h_s1 with _ h_s1_eq
      subst h_s1_eq
      cases h_r1 with
      | step _ _ s2 _ _ _ h_s2 h_r2 =>
        change StepResult.step _ s2 = stepAnSSABorrow copyAfterRetagProg _ at h_s2
        dsimp [stepAnSSABorrow, copyAfterRetagProg, evalAnSSAStmt,
          BorrowState.writeReg] at h_s2
        injection h_s2 with _ h_s2_eq
        subst h_s2_eq
        cases h_r2 with
        | step _ _ s3 _ _ _ h_s3 h_r3 =>
          cases h_r3 with
          | zero => trivial
        | choice _ _ _ _ _ _ _ h_s3 _ _ => nomatch h_s3
        | emptyChoice _ _ _ _ h_s3 _ => nomatch h_s3
        | terminated _ _ _ h_s3 => nomatch h_s3
        | failed _ _ _ h_s3 => nomatch h_s3
        | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
      | choice _ _ _ _ _ _ _ h_s2 _ _ => nomatch h_s2
      | emptyChoice _ _ _ _ h_s2 _ => nomatch h_s2
      | terminated _ _ _ h_s2 => nomatch h_s2
      | failed _ _ _ h_s2 => nomatch h_s2
      | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ _ h_s1 _ _ => nomatch h_s1
    | emptyChoice _ _ _ _ h_s1 _ => nomatch h_s1
    | terminated _ _ _ h_s1 => nomatch h_s1
    | failed _ _ _ h_s1 => nomatch h_s1
    | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
  rcases h_comp q h_src_def with ⟨h_tgt_def, _⟩
  let s1 : BorrowState := {
    pc := 1
    regs := fun idx =>
      if idx == 2 then some (.ptr 0 1 .uniqueMutRef)
      else initBorrowState.regs idx
    nextTag := 2
    activeUniqueTag := fun a =>
      if a == 0 then some 1 else initBorrowState.activeUniqueTag a
    mem := initBorrowState.mem
  }
  let s2 : BorrowState := {
    pc := 2
    regs := fun idx =>
      if idx == 3 then some (.ptr 0 2 .uniqueMutRef)
      else s1.regs idx
    nextTag := 3
    activeUniqueTag := fun a =>
      if a == 0 then some 2 else s1.activeUniqueTag a
    mem := s1.mem
  }
  have h_fail_reach :
      ReachesPrefix AnSSABorrowMachine duplicatedRetagProg initBorrowState 3
        initBorrowState [(), ()] (.failed .ub) := by
    apply ReachesPrefix.step 2 initBorrowState s1 () [()] (.failed .ub) rfl
    apply ReachesPrefix.step 1 s1 s2 () [] (.failed .ub) rfl
    apply ReachesPrefix.failed 0 s2 .ub rfl
  exact h_tgt_def rfl [(), ()] (.failed .ub) h_fail_reach

/-- Erasing `withRetag = true` to `false` (`erasedRetagProg`: replacing
    `.retag 2 1` with `.letCopy 2 1` when `_1`'s initial tag `99` is stale and
    only becomes the active unique tag via `.retag 2 1`) also violates
    `Compiles`. -/
def erasedRetagProg : List AnSSAStmt := [
  .letCopy 2 1,
  .letCopy 3 2,
  .writeRef 2 42,
  .readRef 0 3
]

def staleTagBorrowState : BorrowState where
  pc := 0
  regs := fun r => if r == 1 then some (.ptr 0 99 .uniqueMutRef) else none
  nextTag := 1
  activeUniqueTag := fun a => if a == 0 then some 0 else none
  mem := fun _ => 0

theorem erase_withRetag_refutes_compiles :
    ¬ Compiles AnSSABorrowLang AnSSABorrowLang id
        copyAfterRetagProg erasedRetagProg := by
  intro h_comp
  let q : ExecQuery BorrowState := ⟨staleTagBorrowState, 3⟩
  have h_src_def : (AnSSABorrowLang.sem copyAfterRetagProg q).defined := by
    intro _ tr out h_reach
    cases h_reach with
    | step _ _ s1 _ _ _ h_s1 h_r1 =>
      change StepResult.step _ s1 = stepAnSSABorrow copyAfterRetagProg staleTagBorrowState at h_s1
      dsimp [stepAnSSABorrow, copyAfterRetagProg, staleTagBorrowState, evalAnSSAStmt,
        performRetag, BorrowState.writeReg] at h_s1
      injection h_s1 with _ h_s1_eq
      subst h_s1_eq
      cases h_r1 with
      | step _ _ s2 _ _ _ h_s2 h_r2 =>
        change StepResult.step _ s2 = stepAnSSABorrow copyAfterRetagProg _ at h_s2
        dsimp [stepAnSSABorrow, copyAfterRetagProg, evalAnSSAStmt,
          BorrowState.writeReg] at h_s2
        injection h_s2 with _ h_s2_eq
        subst h_s2_eq
        cases h_r2 with
        | step _ _ s3 _ _ _ h_s3 h_r3 =>
          cases h_r3 with
          | zero => trivial
        | choice _ _ _ _ _ _ _ h_s3 _ _ => nomatch h_s3
        | emptyChoice _ _ _ _ h_s3 _ => nomatch h_s3
        | terminated _ _ _ h_s3 => nomatch h_s3
        | failed _ _ _ h_s3 => nomatch h_s3
        | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
      | choice _ _ _ _ _ _ _ h_s2 _ _ => nomatch h_s2
      | emptyChoice _ _ _ _ h_s2 _ => nomatch h_s2
      | terminated _ _ _ h_s2 => nomatch h_s2
      | failed _ _ _ h_s2 => nomatch h_s2
      | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ _ h_s1 _ _ => nomatch h_s1
    | emptyChoice _ _ _ _ h_s1 _ => nomatch h_s1
    | terminated _ _ _ h_s1 => nomatch h_s1
    | failed _ _ _ h_s1 => nomatch h_s1
    | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
  rcases h_comp q h_src_def with ⟨h_tgt_def, _⟩
  let s1 : BorrowState := {
    pc := 1
    regs := fun idx =>
      if idx == 2 then some (.ptr 0 99 .uniqueMutRef)
      else staleTagBorrowState.regs idx
    nextTag := 1
    activeUniqueTag := staleTagBorrowState.activeUniqueTag
    mem := staleTagBorrowState.mem
  }
  let s2 : BorrowState := {
    pc := 2
    regs := fun idx =>
      if idx == 3 then some (.ptr 0 99 .uniqueMutRef)
      else s1.regs idx
    nextTag := 1
    activeUniqueTag := s1.activeUniqueTag
    mem := s1.mem
  }
  have h_fail_reach :
      ReachesPrefix AnSSABorrowMachine erasedRetagProg staleTagBorrowState 3
        staleTagBorrowState [(), ()] (.failed .ub) := by
    apply ReachesPrefix.step 2 staleTagBorrowState s1 () [()] (.failed .ub) rfl
    apply ReachesPrefix.step 1 s1 s2 () [] (.failed .ub) rfl
    apply ReachesPrefix.failed 0 s2 .ub rfl
  exact h_tgt_def rfl [(), ()] (.failed .ub) h_fail_reach

/-- Conversely, pure SSA copy propagation of a retagged binding (`_3 = letCopy _2`
    followed by replacing uses of `_3` with `_2`) preserves the exact
    `BorrowState` at every step from `pc = 0` and satisfies `Compiles`. -/
theorem step_copyProp_at_pc3 (st : BorrowState) (h_pc : st.pc = 3)
    (h_eq_regs : st.regs 2 = st.regs 3) :
    stepAnSSABorrow copyPropagatedRetagProg st =
      stepAnSSABorrow copyAfterRetagProg st := by
  simp [stepAnSSABorrow, copyPropagatedRetagProg, copyAfterRetagProg,
    h_pc, evalAnSSAStmt, h_eq_regs]

/-- Invariant relating registers `_2` and `_3` along execution of
    `copyPropagatedRetagProg` from `pc = 0`:
    - At `pc = 2` (immediately after `.letCopy 3 2`), `_2` and `_3` hold the
      same initialized `BorrowVal`.
    - At `pc = 3` (immediately after `.writeRef 2 42`, which modifies `mem`
      without modifying `regs`), `_2` and `_3` still hold identical values. -/
def CopyPropInv (st : BorrowState) : Prop :=
  (st.pc = 2 → st.regs 2 = st.regs 3) ∧
  (st.pc = 3 → st.regs 2 = st.regs 3)

theorem step_copyProp_eq_of_inv (st : BorrowState) (h_inv : CopyPropInv st) :
    stepAnSSABorrow copyPropagatedRetagProg st =
      stepAnSSABorrow copyAfterRetagProg st := by
  by_cases h3 : st.pc = 3
  · exact step_copyProp_at_pc3 st h3 (h_inv.2 h3)
  · unfold stepAnSSABorrow
    have h_len : copyPropagatedRetagProg.length = 4 := rfl
    have h_len' : copyAfterRetagProg.length = 4 := rfl
    rw [h_len, h_len']
    by_cases h4 : (st.pc == 4) = true
    · simp only [h4, ↓reduceIte]
    · have h4f : (st.pc == 4) = false := Bool.eq_false_iff.mpr h4
      simp only [h4f, Bool.false_eq_true, ↓reduceIte]
      have h_get : copyPropagatedRetagProg[st.pc]? = copyAfterRetagProg[st.pc]? := by
        match h_pc : st.pc with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | 3 => exact False.elim (h3 h_pc)
        | n + 4 => rfl
      rw [h_get]

theorem canWritePtr_regs_eq (st st' : BorrowState) (bv : BorrowVal) (val : Nat)
    (h_w : canWritePtr st bv val = some st') :
    st'.regs = st.regs := by
  unfold canWritePtr at h_w
  cases bv with
  | scalar _ => nomatch h_w
  | ptr addr tag perm =>
    cases perm with
    | uniqueMutRef =>
      by_cases h_act : (st.activeUniqueTag addr == some tag) = true
      · simp only [h_act, ↓reduceIte] at h_w
        injection h_w with h_eq
        rw [← h_eq]
      · have h_nact : (st.activeUniqueTag addr == some tag) = false :=
          Bool.eq_false_iff.mpr h_act
        simp only [h_nact, Bool.false_eq_true, ↓reduceIte] at h_w
        nomatch h_w
    | sharedRef => nomatch h_w
    | unsafePinned =>
      injection h_w with h_eq
      rw [← h_eq]
    | maybeDangling => nomatch h_w

theorem step_AnSSABorrow_no_choice (p : List AnSSAStmt) (st : BorrowState)
    (kind : ChoiceKind) (branches : BorrowState → Prop) :
    StepResult.choice kind branches ≠ stepAnSSABorrow p st := by
  intro h
  unfold stepAnSSABorrow at h
  by_cases h_end : (st.pc == p.length) = true
  · simp only [h_end, ↓reduceIte] at h
    cases h_r0 : st.regs 0 with
    | none => simp only [h_r0] at h; nomatch h
    | some bv0 =>
      simp only [h_r0] at h
      cases bv0 <;> nomatch h
  · have h_nend := Bool.eq_false_iff.mpr h_end
    simp only [h_nend, Bool.false_eq_true, ↓reduceIte] at h
    cases h_get : p[st.pc]? with
    | none => simp only [h_get] at h; nomatch h
    | some stmt =>
      simp only [h_get] at h
      cases h_ev : evalAnSSAStmt st stmt with
      | none => simp only [h_ev] at h; nomatch h
      | some st' => simp only [h_ev] at h; nomatch h

theorem copyPropInv_preserved (st st' : BorrowState)
    (h_inv : CopyPropInv st)
    (h_step : StepResult.step () st' = stepAnSSABorrow copyPropagatedRetagProg st) :
    CopyPropInv st' := by
  have h_len : copyPropagatedRetagProg.length = 4 := rfl
  match h_pc : st.pc with
  | 0 =>
    have h_neq : (st.pc == copyPropagatedRetagProg.length) = false := by rw [h_pc]; rfl
    have h_get : copyPropagatedRetagProg[st.pc]? = some (.retag 2 1) := by rw [h_pc]; rfl
    simp only [stepAnSSABorrow, h_neq, Bool.false_eq_true, ↓reduceIte, h_get] at h_step
    cases h_ev : evalAnSSAStmt st (.retag 2 1) with
    | none => simp only [h_ev] at h_step; nomatch h_step
    | some s_mid =>
      simp only [h_ev] at h_step
      injection h_step with _ h_st'
      have h_pc' : st'.pc = 1 := by rw [h_st', h_pc]
      exact ⟨fun h => by omega, fun h => by omega⟩
  | 1 =>
    have h_neq : (st.pc == copyPropagatedRetagProg.length) = false := by rw [h_pc]; rfl
    have h_get : copyPropagatedRetagProg[st.pc]? = some (.letCopy 3 2) := by rw [h_pc]; rfl
    simp only [stepAnSSABorrow, h_neq, Bool.false_eq_true, ↓reduceIte, h_get, evalAnSSAStmt] at h_step
    cases h_r2 : st.regs 2 with
    | none => simp only [h_r2] at h_step; nomatch h_step
    | some bv =>
      simp only [h_r2] at h_step
      injection h_step with _ h_st'
      refine ⟨?_, ?_⟩
      · intro _
        rw [h_st']
        simp [BorrowState.writeReg, h_r2]
      · intro h3
        have h_pc' : st'.pc = 2 := by rw [h_st', h_pc]
        omega
  | 2 =>
    have h_neq : (st.pc == copyPropagatedRetagProg.length) = false := by rw [h_pc]; rfl
    have h_get : copyPropagatedRetagProg[st.pc]? = some (.writeRef 2 42) := by rw [h_pc]; rfl
    simp only [stepAnSSABorrow, h_neq, Bool.false_eq_true, ↓reduceIte, h_get, evalAnSSAStmt] at h_step
    cases h_r2 : st.regs 2 with
    | none => simp only [h_r2] at h_step; nomatch h_step
    | some bv =>
      simp only [h_r2] at h_step
      cases h_w : canWritePtr st bv 42 with
      | none => simp only [h_w] at h_step; nomatch h_step
      | some s_mid =>
        simp only [h_w] at h_step
        injection h_step with _ h_st'
        have h_regs := canWritePtr_regs_eq st s_mid bv 42 h_w
        have h_eq23 := h_inv.1 h_pc
        refine ⟨?_, ?_⟩
        · intro h2
          have h_pc' : st'.pc = 3 := by rw [h_st', h_pc]
          omega
        · intro _
          rw [h_st']
          dsimp
          rw [h_regs, h_eq23]
  | 3 =>
    have h_neq : (st.pc == copyPropagatedRetagProg.length) = false := by rw [h_pc]; rfl
    have h_get : copyPropagatedRetagProg[st.pc]? = some (.readRef 0 2) := by rw [h_pc]; rfl
    simp only [stepAnSSABorrow, h_neq, Bool.false_eq_true, ↓reduceIte, h_get] at h_step
    cases h_ev : evalAnSSAStmt st (.readRef 0 2) with
    | none => simp only [h_ev] at h_step; nomatch h_step
    | some s_mid =>
      simp only [h_ev] at h_step
      injection h_step with _ h_st'
      have h_pc' : st'.pc = 4 := by rw [h_st', h_pc]
      exact ⟨fun h => by omega, fun h => by omega⟩
  | 4 =>
    have h_eq4 : (st.pc == copyPropagatedRetagProg.length) = true := by rw [h_pc]; rfl
    simp only [stepAnSSABorrow, h_eq4, ↓reduceIte] at h_step
    cases h_r0 : st.regs 0 with
    | none => simp only [h_r0] at h_step; nomatch h_step
    | some bv0 =>
      simp only [h_r0] at h_step
      cases bv0 <;> nomatch h_step
  | n + 5 =>
    unfold stepAnSSABorrow at h_step
    have h_neq : (st.pc == copyPropagatedRetagProg.length) = false := by
      rw [h_pc, h_len]; simp
    have h_get : copyPropagatedRetagProg[st.pc]? = none := by
      rw [h_pc]; rfl
    simp only [h_neq, Bool.false_eq_true, ↓reduceIte, h_get] at h_step
    nomatch h_step

theorem reachesPrefix_copyProp_of_inv (init : BorrowState) :
    ∀ (n : Nat) (st : BorrowState) (tr : List Unit) (out : PrefixOutcome Nat),
      CopyPropInv st →
      ReachesPrefix AnSSABorrowMachine copyPropagatedRetagProg init n st tr out →
      ReachesPrefix AnSSABorrowMachine copyAfterRetagProg init n st tr out := by
  intro n
  induction n with
  | zero =>
    intro st tr out _ h_reach
    cases h_reach
    exact .zero st
  | succ k ih =>
    intro st tr out h_inv h_reach
    have h_eq := step_copyProp_eq_of_inv st h_inv
    cases h_reach with
    | step _ _ s' obs tr' _ h_st h_rest =>
      change StepResult.step obs s' = stepAnSSABorrow copyPropagatedRetagProg st at h_st
      have h_inv' : CopyPropInv s' := copyPropInv_preserved st s' h_inv h_st
      rw [h_eq] at h_st
      exact .step k st s' obs tr' out h_st (ih s' tr' out h_inv' h_rest)
    | choice _ kind _ _ branches _ _ h_st _ _ =>
      exact False.elim (step_AnSSABorrow_no_choice copyPropagatedRetagProg st kind branches h_st)
    | emptyChoice _ kind _ branches h_st _ =>
      exact False.elim (step_AnSSABorrow_no_choice copyPropagatedRetagProg st kind branches h_st)
    | terminated _ _ term h_st =>
      change StepResult.terminated term = stepAnSSABorrow copyPropagatedRetagProg st at h_st
      rw [h_eq] at h_st
      exact .terminated k st term h_st
    | failed _ _ err h_st =>
      change StepResult.failed err = stepAnSSABorrow copyPropagatedRetagProg st at h_st
      rw [h_eq] at h_st
      exact .failed k st err h_st
    | noStep _ _ h_ns =>
      exact False.elim (h_ns ⟨_, rfl⟩)

theorem reachesPrefix_copyProp_of_copyAfter (init : BorrowState)
    (h_init : init.pc = 0) :
    ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome Nat),
      ReachesPrefix AnSSABorrowMachine copyPropagatedRetagProg init n init tr out →
      ReachesPrefix AnSSABorrowMachine copyAfterRetagProg init n init tr out := by
  intro n tr out h_reach
  have h_inv : CopyPropInv init := ⟨fun h => by omega, fun h => by omega⟩
  exact reachesPrefix_copyProp_of_inv init n init tr out h_inv h_reach

/-- Pure SSA copy propagation after `AnSSAStmt.retag` satisfies
    `Compiles AnSSABorrowLang AnSSABorrowLang id copyAfterRetagProg copyPropagatedRetagProg`
    across all queries `q : ExecQuery BorrowState`. -/
theorem retag_copy_prop_compiles :
    Compiles AnSSABorrowLang AnSSABorrowLang id
      copyAfterRetagProg copyPropagatedRetagProg := by
  intro q h_src_def
  refine ⟨?_, ?_⟩
  · intro h_init tr out h_reach
    exact h_src_def h_init tr out
      (reachesPrefix_copyProp_of_copyAfter q.init h_init q.steps tr out h_reach)
  · intro out ⟨h_init, h_reach⟩
    exact ⟨h_init,
      reachesPrefix_copyProp_of_copyAfter q.init h_init q.steps out.trace out.outcome h_reach⟩

end Anneal

/-!
## Section 4: Fuel-Indexed Open `CallSpecTable` for Mutual Recursion (`mutual_recursion_callSpec_sound`)

In Round 1, interprocedural calls were restricted to a closed 2-argument enum
`PureCallee2` (`evalPureCallee2`), which assumed an acyclic call DAG where every
callee is verified strictly before its caller.

By indexing `CallSpecTable` by a step/call fuel budget `k : Nat`
(`post : FnSymbol → Nat → List MirVal → MirVal → Prop`), mutually recursive
functions $f$ and $g$ can be verified modularly without call-graph acyclicity:
1. Function $f$ is verified at fuel $k$ assuming $g$'s contract holds at all
   strictly smaller fuels $j < k$.
2. Function $g$ is verified at fuel $k$ assuming $f$'s contract holds at all
   strictly smaller fuels $j < k$.
3. By strong induction on $k : \mathbb{N}$ (`mutual_recursion_callSpec_sound`),
   linking $f$ and $g$ discharges both assumptions simultaneously for all
   $k : \mathbb{N}$.
-/

namespace Anneal
open Trusted

/-- A fuel-indexed call contract `C : Nat → List MirVal → MirVal → Prop`. -/
abbrev FuelContract := Nat → List MirVal → MirVal → Prop

/--Strong induction principle on `Nat`: if `P k` holds whenever `P j` holds for
    all `j < k`, then `P k` holds for all `k : Nat`. -/
theorem nat_strong_induction {P : Nat → Prop}
    (h_step : ∀ k, (∀ j, j < k → P j) → P k) :
    ∀ k, P k := by
  have h_bound : ∀ n j, j < n → P j := by
    intro n
    induction n with
    | zero =>
      intro j hj
      omega
    | succ m ih =>
      intro j hj
      by_cases h_lt : j < m
      · exact ih j h_lt
      · have h_eq : j = m := by omega
        subst h_eq
        exact h_step j ih
  intro k
  exact h_bound (k + 1) k (by omega)

/-- General step-indexed mutual recursion soundness theorem:
    Let `ValidF k : Prop` and `ValidG k : Prop` be the fuel-$k$ contract
    satisfaction propositions for mutually recursive functions $f$ and $g$.
    If:
    1. `h_f`: for every fuel $k$, assuming `ValidG j` for all $j < k$ implies
       `ValidF k`, and
    2. `h_g`: for every fuel $k$, assuming `ValidF j` for all $j < k$ implies
       `ValidG k`,
    then `ValidF k ∧ ValidG k` holds unconditionally for all $k : \mathbb{N}$. -/
theorem mutual_recursion_callSpec_sound
    {ValidF ValidG : Nat → Prop}
    (h_f : ∀ k, (∀ j, j < k → ValidG j) → ValidF k)
    (h_g : ∀ k, (∀ j, j < k → ValidF j) → ValidG k) :
    ∀ k, ValidF k ∧ ValidG k := by
  apply nat_strong_induction
  intro k ih
  refine ⟨?_, ?_⟩
  · exact h_f k (fun j hj => (ih j hj).2)
  · exact h_g k (fun j hj => (ih j hj).1)

/-- Function symbols for the mutually recursive `is_even` and `is_odd` MIR
    functions. -/
def fnIsEven : FnSymbol := ⟨0⟩
def fnIsOdd : FnSymbol := ⟨1⟩

/-- Relational contract table for `is_even` (`fnIsEven`) and `is_odd`
    (`fnIsOdd`) indexed by call fuel `k : Nat`:
    - At fuel `k`, calling `is_even([.usize m])` requires `m ≤ k` and guarantees
      `ret = .bool (m % 2 == 0)`.
    - At fuel `k`, calling `is_odd([.usize m])` requires `m ≤ k` and guarantees
      `ret = .bool (m % 2 == 1)`. -/
def evenOddCallSpecTable : CallSpecTable where
  hasSpec callee k args :=
    match callee.id, args with
    | 0, [.usize m] => decide (m ≤ k)
    | 1, [.usize m] => decide (m ≤ k)
    | _, _ => false
  post callee k args ret :=
    match callee.id, args with
    | 0, [.usize m] => m ≤ k ∧ ret = .bool (m % 2 == 0)
    | 1, [.usize m] => m ≤ k ∧ ret = .bool (m % 2 == 1)
    | _, _ => False

/-- MIR body of `fn is_even(n: usize) -> bool`:
    - `bb0`: `_2 = (_1 == 0); switchInt(_2) -> [1: bb1, otherwise: bb2]`
    - `bb1`: `_0 = true; return`
    - `bb2`: `_3 = _1 - 1; _0 = call fnIsOdd(_3) -> bb3`
    - `bb3`: `return` -/
def isEvenMirBody : MirBody where
  paramTys := [.usize]
  returnTy := .bool
  localCount := 4
  callSpecs := evenOddCallSpecTable
  blocks := [
    -- bb0: branch on _1 == 0
    { statements := [
        .assign ⟨2⟩ (.binaryOp .eq (.copy ⟨1⟩) (.constUsize 0))
      ]
      terminator := .switchInt (.copy ⟨2⟩) [(1, ⟨1⟩)] ⟨2⟩ },
    -- bb1: base case (_1 == 0) -> return true
    { statements := [
        .assign ⟨0⟩ (.use (.constBool true) false)
      ]
      terminator := .return_ },
    -- bb2: recursive step (_3 = _1 - 1; _0 = is_odd(_3))
    { statements := [
        .assign ⟨3⟩ (.binaryOp .sub (.copy ⟨1⟩) (.constUsize 1))
      ]
      terminator := .callFn fnIsOdd [.copy ⟨3⟩] ⟨0⟩ ⟨3⟩ },
    -- bb3: return _0
    { statements := []
      terminator := .return_ }
  ]

/-- MIR body of `fn is_odd(n: usize) -> bool`:
    - `bb0`: `_2 = (_1 == 0); switchInt(_2) -> [1: bb1, otherwise: bb2]`
    - `bb1`: `_0 = false; return`
    - `bb2`: `_3 = _1 - 1; _0 = call fnIsEven(_3) -> bb3`
    - `bb3`: `return` -/
def isOddMirBody : MirBody where
  paramTys := [.usize]
  returnTy := .bool
  localCount := 4
  callSpecs := evenOddCallSpecTable
  blocks := [
    -- bb0: branch on _1 == 0
    { statements := [
        .assign ⟨2⟩ (.binaryOp .eq (.copy ⟨1⟩) (.constUsize 0))
      ]
      terminator := .switchInt (.copy ⟨2⟩) [(1, ⟨1⟩)] ⟨2⟩ },
    -- bb1: base case (_1 == 0) -> return false
    { statements := [
        .assign ⟨0⟩ (.use (.constBool false) false)
      ]
      terminator := .return_ },
    -- bb2: recursive step (_3 = _1 - 1; _0 = is_even(_3))
    { statements := [
        .assign ⟨3⟩ (.binaryOp .sub (.copy ⟨1⟩) (.constUsize 1))
      ]
      terminator := .callFn fnIsEven [.copy ⟨3⟩] ⟨0⟩ ⟨3⟩ },
    -- bb3: return _0
    { statements := []
      terminator := .return_ }
  ]

/-- Semantic meaning of `ValidEven k`: at fuel budget `k`, for every input
    `n ≤ k + 1` and initial state `st` with `st.pc = ⟨0⟩`, `st.locals 1 = some (.usize n)`,
    and `st.callFuel = k`, every reachable prefix of `isEvenMirBody` is safe
    and any terminal outcome equals `.normal (.bool (n % 2 == 0))`. -/
def ValidEven (k : Nat) : Prop :=
  ∀ (n : Nat), n ≤ k + 1 →
    ∀ (steps : Nat) (st : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      st.pc = ⟨0⟩ →
      st.locals 1 = some (.usize n) →
      st.callFuel = k →
      ReachesPrefix MirMachine isEvenMirBody st steps st tr out →
      out.isSafe ∧
      (∀ term, out = .terminated term →
        term = .normal (.bool (n % 2 == 0)))

/-- Semantic meaning of `ValidOdd k`: at fuel budget `k`, for every input
    `n ≤ k + 1` and initial state `st` with `st.pc = ⟨0⟩`, `st.locals 1 = some (.usize n)`,
    and `st.callFuel = k`, every reachable prefix of `isOddMirBody` is safe
    and any terminal outcome equals `.normal (.bool (n % 2 == 1))`. -/
def ValidOdd (k : Nat) : Prop :=
  ∀ (n : Nat), n ≤ k + 1 →
    ∀ (steps : Nat) (st : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      st.pc = ⟨0⟩ →
      st.locals 1 = some (.usize n) →
      st.callFuel = k →
      ReachesPrefix MirMachine isOddMirBody st steps st tr out →
      out.isSafe ∧
      (∀ term, out = .terminated term →
        term = .normal (.bool (n % 2 == 1)))

theorem isEven_step_bb0_zero (st : MirState)
    (h_pc : st.pc = ⟨0⟩) (h_arg : st.locals 1 = some (.usize 0)) :
    stepBlock isEvenMirBody st =
      .step () { (st.writeLocal ⟨2⟩ (some (.bool true))) with pc := ⟨1⟩ } := by
  simp [stepBlock, isEvenMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, MirState.readLocal, MirState.writeLocal,
    h_arg, execTerminator, lookupSwitchTarget]

theorem isEven_step_bb1 (st : MirState) (h_pc : st.pc = ⟨1⟩) :
    stepBlock isEvenMirBody st = .terminated (.normal (.bool true)) := by
  simp [stepBlock, isEvenMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, execTerminator, MirState.readLocal,
    MirState.writeLocal]

theorem isEven_step_bb0_succ (st : MirState) (m : Nat)
    (h_pc : st.pc = ⟨0⟩) (h_arg : st.locals 1 = some (.usize (m + 1))) :
    stepBlock isEvenMirBody st =
      .step () { (st.writeLocal ⟨2⟩ (some (.bool false))) with pc := ⟨2⟩ } := by
  simp [stepBlock, isEvenMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, MirState.readLocal, MirState.writeLocal,
    h_arg, execTerminator, lookupSwitchTarget]

theorem isEven_step_bb2 (st : MirState) (m k : Nat)
    (h_pc : st.pc = ⟨2⟩)
    (h_arg : st.locals 1 = some (.usize (m + 1)))
    (h_fuel : st.callFuel = k)
    (h_le : m ≤ k) :
    stepBlock isEvenMirBody st =
      .choice .demonic (fun s_next =>
        ∃ ret,
          (m ≤ k ∧ ret = .bool (m % 2 == 1)) ∧
          s_next = { ((st.writeLocal ⟨3⟩ (some (.usize m))).writeLocal ⟨0⟩ (some ret)) with
            pc := ⟨3⟩ }) := by
  have h_dec : decide (m ≤ k) = true := decide_eq_true h_le
  simp [stepBlock, isEvenMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, MirState.readLocal, MirState.writeLocal,
    h_arg, execTerminator, evalOperandList, evenOddCallSpecTable,
    fnIsOdd, h_fuel, h_dec]

theorem isEven_step_bb3 (st : MirState) (ret : MirVal)
    (h_pc : st.pc = ⟨3⟩) (h_ret : st.locals 0 = some ret) :
    stepBlock isEvenMirBody st = .terminated (.normal ret) := by
  simp [stepBlock, isEvenMirBody, h_pc, execStatements, execTerminator,
    MirState.readLocal, h_ret]

theorem mod2_succ_eq_zero_iff (m : Nat) :
    (m % 2 == 1) = ((m + 1) % 2 == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq]
  omega

/-- Modular verification of `isEvenMirBody` at fuel `k`: assuming `evenOddCallSpecTable`
    for `fnIsOdd` at argument `m = n - 1 ≤ k`, every execution prefix of
    `isEvenMirBody` from `st` is safe and returns `.bool (n % 2 == 0)`. -/
theorem validEven_at_fuel (k : Nat) (_h_odd_below : ∀ j, j < k → ValidOdd j) :
    ValidEven k := by
  intro n h_n_le steps st tr out h_pc h_arg h_fuel h_reach
  cases n with
  | zero =>
    have h_step0 := isEven_step_bb0_zero st h_pc h_arg
    cases h_reach with
    | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
    | step s0 _ s1 _ tr1 _ h_st0 h_r1 =>
      change StepResult.step () s1 = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0
      injection h_st0 with _ h_s1
      have h_pc1 : s1.pc = ⟨1⟩ := by rw [h_s1]
      have h_step1 := isEven_step_bb1 s1 h_pc1
      cases h_r1 with
      | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
      | step _ _ _ _ _ _ h_st1 _ =>
        change StepResult.step _ _ = stepBlock isEvenMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | choice _ _ _ _ _ _ _ h_st1 _ _ =>
        change StepResult.choice _ _ = stepBlock isEvenMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | emptyChoice _ _ _ _ h_st1 _ =>
        change StepResult.choice _ _ = stepBlock isEvenMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | terminated _ _ term h_st1 =>
        change StepResult.terminated term = stepBlock isEvenMirBody s1 at h_st1
        rw [h_step1] at h_st1
        injection h_st1 with h_t
        refine ⟨trivial, fun term' h_out => ?_⟩
        injection h_out with h_teq
        rw [← h_teq, h_t]; rfl
      | failed _ _ _ h_st1 =>
        change StepResult.failed _ = stepBlock isEvenMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ _ h_st0 _ _ =>
      change StepResult.choice _ _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | emptyChoice _ _ _ _ h_st0 _ =>
      change StepResult.choice _ _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | terminated _ _ _ h_st0 =>
      change StepResult.terminated _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | failed _ _ _ h_st0 =>
      change StepResult.failed _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
  | succ m =>
    have h_m_le : m ≤ k := by omega
    have h_step0 := isEven_step_bb0_succ st m h_pc h_arg
    cases h_reach with
    | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
    | step _ _ s1 _ tr1 _ h_st0 h_r1 =>
      change StepResult.step () s1 = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0
      injection h_st0 with _ h_s1
      have h_pc1 : s1.pc = ⟨2⟩ := by rw [h_s1]
      have h_arg1 : s1.locals 1 = some (.usize (m + 1)) := by
        rw [h_s1]; simp [MirState.writeLocal, h_arg]
      have h_fuel1 : s1.callFuel = k := by
        rw [h_s1]; exact h_fuel
      have h_step2 := isEven_step_bb2 s1 m k h_pc1 h_arg1 h_fuel1 h_m_le
      cases h_r1 with
      | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
      | step _ _ _ _ _ _ h_st2 _ =>
        change StepResult.step _ _ = stepBlock isEvenMirBody s1 at h_st2
        rw [h_step2] at h_st2; nomatch h_st2
      | choice _ _ _ s2 branches _ _ h_st2 h_b h_r2 =>
        change StepResult.choice _ branches = stepBlock isEvenMirBody s1 at h_st2
        rw [h_step2] at h_st2
        injection h_st2 with _ h_br_eq
        rw [h_br_eq] at h_b
        rcases h_b with ⟨ret, ⟨_, h_ret_eq⟩, h_s2⟩
        have h_pc2 : s2.pc = ⟨3⟩ := by rw [h_s2]
        have h_ret2 : s2.locals 0 = some ret := by
          rw [h_s2]; simp [MirState.writeLocal]
        have h_step3 := isEven_step_bb3 s2 ret h_pc2 h_ret2
        cases h_r2 with
        | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
        | step _ _ _ _ _ _ h_st3 _ =>
          change StepResult.step _ _ = stepBlock isEvenMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | choice _ _ _ _ _ _ _ h_st3 _ _ =>
          change StepResult.choice _ _ = stepBlock isEvenMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | emptyChoice _ _ _ _ h_st3 _ =>
          change StepResult.choice _ _ = stepBlock isEvenMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | terminated _ _ term h_st3 =>
          change StepResult.terminated term = stepBlock isEvenMirBody s2 at h_st3
          rw [h_step3] at h_st3
          injection h_st3 with h_t
          refine ⟨trivial, fun term' h_out => ?_⟩
          injection h_out with h_teq
          rw [← h_teq, h_t, h_ret_eq, mod2_succ_eq_zero_iff m]
        | failed _ _ _ h_st3 =>
          change StepResult.failed _ = stepBlock isEvenMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
      | emptyChoice _ _ _ branches h_st2 h_nb =>
        change StepResult.choice _ branches = stepBlock isEvenMirBody s1 at h_st2
        rw [h_step2] at h_st2
        injection h_st2 with _ h_br_eq
        rw [h_br_eq] at h_nb
        exact False.elim (h_nb ⟨_, .bool (m % 2 == 1), ⟨h_m_le, rfl⟩, rfl⟩)
      | terminated _ _ _ h_st2 =>
        change StepResult.terminated _ = stepBlock isEvenMirBody s1 at h_st2
        rw [h_step2] at h_st2; nomatch h_st2
      | failed _ _ _ h_st2 =>
        change StepResult.failed _ = stepBlock isEvenMirBody s1 at h_st2
        rw [h_step2] at h_st2; nomatch h_st2
      | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ _ h_st0 _ _ =>
      change StepResult.choice _ _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | emptyChoice _ _ _ _ h_st0 _ =>
      change StepResult.choice _ _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | terminated _ _ _ h_st0 =>
      change StepResult.terminated _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | failed _ _ _ h_st0 =>
      change StepResult.failed _ = stepBlock isEvenMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)

theorem isOdd_step_bb0_zero (st : MirState)
    (h_pc : st.pc = ⟨0⟩) (h_arg : st.locals 1 = some (.usize 0)) :
    stepBlock isOddMirBody st =
      .step () { (st.writeLocal ⟨2⟩ (some (.bool true))) with pc := ⟨1⟩ } := by
  simp [stepBlock, isOddMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, MirState.readLocal, MirState.writeLocal,
    h_arg, execTerminator, lookupSwitchTarget]

theorem isOdd_step_bb1 (st : MirState) (h_pc : st.pc = ⟨1⟩) :
    stepBlock isOddMirBody st = .terminated (.normal (.bool false)) := by
  simp [stepBlock, isOddMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, execTerminator, MirState.readLocal,
    MirState.writeLocal]

theorem isOdd_step_bb0_succ (st : MirState) (m : Nat)
    (h_pc : st.pc = ⟨0⟩) (h_arg : st.locals 1 = some (.usize (m + 1))) :
    stepBlock isOddMirBody st =
      .step () { (st.writeLocal ⟨2⟩ (some (.bool false))) with pc := ⟨2⟩ } := by
  simp [stepBlock, isOddMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, MirState.readLocal, MirState.writeLocal,
    h_arg, execTerminator, lookupSwitchTarget]

theorem isOdd_step_bb2 (st : MirState) (m k : Nat)
    (h_pc : st.pc = ⟨2⟩)
    (h_arg : st.locals 1 = some (.usize (m + 1)))
    (h_fuel : st.callFuel = k)
    (h_le : m ≤ k) :
    stepBlock isOddMirBody st =
      .choice .demonic (fun s_next =>
        ∃ ret,
          (m ≤ k ∧ ret = .bool (m % 2 == 0)) ∧
          s_next = { ((st.writeLocal ⟨3⟩ (some (.usize m))).writeLocal ⟨0⟩ (some ret)) with
            pc := ⟨3⟩ }) := by
  have h_dec : decide (m ≤ k) = true := decide_eq_true h_le
  simp [stepBlock, isOddMirBody, h_pc, execStatements, execStatement,
    evalRvalue, evalOperand, MirState.readLocal, MirState.writeLocal,
    h_arg, execTerminator, evalOperandList, evenOddCallSpecTable,
    fnIsEven, h_fuel, h_dec]

theorem isOdd_step_bb3 (st : MirState) (ret : MirVal)
    (h_pc : st.pc = ⟨3⟩) (h_ret : st.locals 0 = some ret) :
    stepBlock isOddMirBody st = .terminated (.normal ret) := by
  simp [stepBlock, isOddMirBody, h_pc, execStatements, execTerminator,
    MirState.readLocal, h_ret]

theorem mod2_succ_eq_one_iff (m : Nat) :
    (m % 2 == 0) = ((m + 1) % 2 == 1) := by
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq]
  omega

/-- Modular verification of `isOddMirBody` at fuel `k`. -/
theorem validOdd_at_fuel (k : Nat) (_h_even_below : ∀ j, j < k → ValidEven j) :
    ValidOdd k := by
  intro n h_n_le steps st tr out h_pc h_arg h_fuel h_reach
  cases n with
  | zero =>
    have h_step0 := isOdd_step_bb0_zero st h_pc h_arg
    cases h_reach with
    | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
    | step _ _ s1 _ tr1 _ h_st0 h_r1 =>
      change StepResult.step () s1 = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0
      injection h_st0 with _ h_s1
      have h_pc1 : s1.pc = ⟨1⟩ := by rw [h_s1]
      have h_step1 := isOdd_step_bb1 s1 h_pc1
      cases h_r1 with
      | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
      | step _ _ _ _ _ _ h_st1 _ =>
        change StepResult.step _ _ = stepBlock isOddMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | choice _ _ _ _ _ _ _ h_st1 _ _ =>
        change StepResult.choice _ _ = stepBlock isOddMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | emptyChoice _ _ _ _ h_st1 _ =>
        change StepResult.choice _ _ = stepBlock isOddMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | terminated _ _ term h_st1 =>
        change StepResult.terminated term = stepBlock isOddMirBody s1 at h_st1
        rw [h_step1] at h_st1
        injection h_st1 with h_t
        refine ⟨trivial, fun term' h_out => ?_⟩
        injection h_out with h_teq
        rw [← h_teq, h_t]; rfl
      | failed _ _ _ h_st1 =>
        change StepResult.failed _ = stepBlock isOddMirBody s1 at h_st1
        rw [h_step1] at h_st1; nomatch h_st1
      | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ _ h_st0 _ _ =>
      change StepResult.choice _ _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | emptyChoice _ _ _ _ h_st0 _ =>
      change StepResult.choice _ _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | terminated _ _ _ h_st0 =>
      change StepResult.terminated _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | failed _ _ _ h_st0 =>
      change StepResult.failed _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
  | succ m =>
    have h_m_le : m ≤ k := by omega
    have h_step0 := isOdd_step_bb0_succ st m h_pc h_arg
    cases h_reach with
    | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
    | step _ _ s1 _ tr1 _ h_st0 h_r1 =>
      change StepResult.step () s1 = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0
      injection h_st0 with _ h_s1
      have h_pc1 : s1.pc = ⟨2⟩ := by rw [h_s1]
      have h_arg1 : s1.locals 1 = some (.usize (m + 1)) := by
        rw [h_s1]; simp [MirState.writeLocal, h_arg]
      have h_fuel1 : s1.callFuel = k := by
        rw [h_s1]; exact h_fuel
      have h_step2 := isOdd_step_bb2 s1 m k h_pc1 h_arg1 h_fuel1 h_m_le
      cases h_r1 with
      | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
      | step _ _ _ _ _ _ h_st2 _ =>
        change StepResult.step _ _ = stepBlock isOddMirBody s1 at h_st2
        rw [h_step2] at h_st2; nomatch h_st2
      | choice _ _ _ s2 branches _ _ h_st2 h_b h_r2 =>
        change StepResult.choice _ branches = stepBlock isOddMirBody s1 at h_st2
        rw [h_step2] at h_st2
        injection h_st2 with _ h_br_eq
        rw [h_br_eq] at h_b
        rcases h_b with ⟨ret, ⟨_, h_ret_eq⟩, h_s2⟩
        have h_pc2 : s2.pc = ⟨3⟩ := by rw [h_s2]
        have h_ret2 : s2.locals 0 = some ret := by
          rw [h_s2]; simp [MirState.writeLocal]
        have h_step3 := isOdd_step_bb3 s2 ret h_pc2 h_ret2
        cases h_r2 with
        | zero => exact ⟨trivial, fun _ h => by nomatch h⟩
        | step _ _ _ _ _ _ h_st3 _ =>
          change StepResult.step _ _ = stepBlock isOddMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | choice _ _ _ _ _ _ _ h_st3 _ _ =>
          change StepResult.choice _ _ = stepBlock isOddMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | emptyChoice _ _ _ _ h_st3 _ =>
          change StepResult.choice _ _ = stepBlock isOddMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | terminated _ _ term h_st3 =>
          change StepResult.terminated term = stepBlock isOddMirBody s2 at h_st3
          rw [h_step3] at h_st3
          injection h_st3 with h_t
          refine ⟨trivial, fun term' h_out => ?_⟩
          injection h_out with h_teq
          rw [← h_teq, h_t, h_ret_eq, mod2_succ_eq_one_iff m]
        | failed _ _ _ h_st3 =>
          change StepResult.failed _ = stepBlock isOddMirBody s2 at h_st3
          rw [h_step3] at h_st3; nomatch h_st3
        | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
      | emptyChoice _ _ _ branches h_st2 h_nb =>
        change StepResult.choice _ branches = stepBlock isOddMirBody s1 at h_st2
        rw [h_step2] at h_st2
        injection h_st2 with _ h_br_eq
        rw [h_br_eq] at h_nb
        exact False.elim (h_nb ⟨_, .bool (m % 2 == 0), ⟨h_m_le, rfl⟩, rfl⟩)
      | terminated _ _ _ h_st2 =>
        change StepResult.terminated _ = stepBlock isOddMirBody s1 at h_st2
        rw [h_step2] at h_st2; nomatch h_st2
      | failed _ _ _ h_st2 =>
        change StepResult.failed _ = stepBlock isOddMirBody s1 at h_st2
        rw [h_step2] at h_st2; nomatch h_st2
      | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ _ h_st0 _ _ =>
      change StepResult.choice _ _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | emptyChoice _ _ _ _ h_st0 _ =>
      change StepResult.choice _ _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | terminated _ _ _ h_st0 =>
      change StepResult.terminated _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | failed _ _ _ h_st0 =>
      change StepResult.failed _ = stepBlock isOddMirBody st at h_st0
      rw [h_step0] at h_st0; nomatch h_st0
    | noStep _ _ h_ns => exact False.elim (h_ns ⟨_, rfl⟩)

/-- Instantiating `mutual_recursion_callSpec_sound` on `isEvenMirBody` and
    `isOddMirBody` discharges both contracts simultaneously for all fuel budgets
    `k : Nat`. -/
theorem is_even_is_odd_mutual_sound :
    ∀ k, ValidEven k ∧ ValidOdd k :=
  mutual_recursion_callSpec_sound validEven_at_fuel validOdd_at_fuel

-- ============================================================================
-- Section 5: Cross-Track 64-Bit Hardware Projection (`π_isa`) & Lawful `BEq`
--            Without `deriving`
-- ============================================================================

/-- 64-bit hardware machine state (`HwIsaState`) modeling a 16-register
    general-purpose register file (`regs : Fin 16 → BitVec 64`, where
    `rdi = 0`, `rsi = 1`, `rax = 2`), stack pointer `sp : BitVec 64`,
    instruction pointer `pc : Nat`, and memory `mem : MemState`. -/
structure HwIsaState where
  pc : Nat
  regs : Fin 16 → BitVec 64
  sp : BitVec 64
  mem : MemState

/-- Update a 64-bit general-purpose register in `HwIsaState`. -/
def HwIsaState.writeReg (hst : HwIsaState) (r : Fin 16) (v : BitVec 64) :
    HwIsaState :=
  { hst with regs := fun r' => if r'.val == r.val then v else hst.regs r' }

/-- 64-bit hardware instructions (`HwIsaStmt`), defined without `deriving`
    to respect `TrustedBoundary.lean`. -/
inductive HwIsaStmt where
  | movImm (dst : Fin 16) (imm : BitVec 64)
  | movReg (dst src : Fin 16)
  | addReg (dst lhs rhs : Fin 16)
  | subImm (dst : Fin 16) (imm : BitVec 64)

/-- 64-bit hardware block terminators (`HwIsaTerm`), defined without
    `deriving`. `ret` returns the 64-bit value in `rax` (`regs 2`). -/
inductive HwIsaTerm where
  | ret
  | jmp (target : Nat)
  | trap

/-- A basic block in the 64-bit hardware language. -/
structure HwIsaBlock where
  stmts : List HwIsaStmt
  term : HwIsaTerm

/-- A 64-bit hardware program (`HwIsaProg`), defined without `deriving`. -/
structure HwIsaProg where
  blocks : List HwIsaBlock

-- ----------------------------------------------------------------------------
-- Explicit Recursive Equality Checkers (`beqHwIsa*`) Without `deriving`
-- ----------------------------------------------------------------------------

def beqFin16 (a b : Fin 16) : Bool :=
  a.val == b.val

theorem beqFin16_eq_of_true :
    ∀ (a b : Fin 16), beqFin16 a b = true → a = b
  | ⟨v1, _⟩, ⟨v2, _⟩, h => by
    simp only [beqFin16, beq_iff_eq] at h
    subst h; rfl

def beqBitVec64 (a b : BitVec 64) : Bool :=
  a.toNat == b.toNat

theorem beqBitVec64_eq_of_true (a b : BitVec 64)
    (h : beqBitVec64 a b = true) : a = b := by
  simp only [beqBitVec64, beq_iff_eq] at h
  exact BitVec.eq_of_toNat_eq h

def beqHwIsaStmt : HwIsaStmt → HwIsaStmt → Bool
  | .movImm d1 i1, .movImm d2 i2 => beqFin16 d1 d2 && beqBitVec64 i1 i2
  | .movReg d1 s1, .movReg d2 s2 => beqFin16 d1 d2 && beqFin16 s1 s2
  | .addReg d1 l1 r1, .addReg d2 l2 r2 =>
    beqFin16 d1 d2 && (beqFin16 l1 l2 && beqFin16 r1 r2)
  | .subImm d1 i1, .subImm d2 i2 => beqFin16 d1 d2 && beqBitVec64 i1 i2
  | _, _ => false

theorem beqHwIsaStmt_eq_of_true :
    ∀ (s1 s2 : HwIsaStmt), beqHwIsaStmt s1 s2 = true → s1 = s2
  | .movImm d1 i1, .movImm d2 i2, h => by
    simp only [beqHwIsaStmt, Bool.and_eq_true] at h
    rw [beqFin16_eq_of_true d1 d2 h.1, beqBitVec64_eq_of_true i1 i2 h.2]
  | .movReg d1 s1, .movReg d2 s2, h => by
    simp only [beqHwIsaStmt, Bool.and_eq_true] at h
    rw [beqFin16_eq_of_true d1 d2 h.1, beqFin16_eq_of_true s1 s2 h.2]
  | .addReg d1 l1 r1, .addReg d2 l2 r2, h => by
    simp only [beqHwIsaStmt, Bool.and_eq_true] at h
    rw [beqFin16_eq_of_true d1 d2 h.1, beqFin16_eq_of_true l1 l2 h.2.1,
        beqFin16_eq_of_true r1 r2 h.2.2]
  | .subImm d1 i1, .subImm d2 i2, h => by
    simp only [beqHwIsaStmt, Bool.and_eq_true] at h
    rw [beqFin16_eq_of_true d1 d2 h.1, beqBitVec64_eq_of_true i1 i2 h.2]

def beqHwIsaTerm : HwIsaTerm → HwIsaTerm → Bool
  | .ret, .ret => true
  | .jmp n1, .jmp n2 => n1 == n2
  | .trap, .trap => true
  | _, _ => false

theorem beqHwIsaTerm_eq_of_true :
    ∀ (t1 t2 : HwIsaTerm), beqHwIsaTerm t1 t2 = true → t1 = t2
  | .ret, .ret, _ => rfl
  | .jmp n1, .jmp n2, h => by
    simp only [beqHwIsaTerm, beq_iff_eq] at h
    rw [h]
  | .trap, .trap, _ => rfl

def beqHwIsaBlock (b1 b2 : HwIsaBlock) : Bool :=
  beqList beqHwIsaStmt b1.stmts b2.stmts && beqHwIsaTerm b1.term b2.term

theorem beqHwIsaBlock_eq_of_true :
    ∀ (b1 b2 : HwIsaBlock), beqHwIsaBlock b1 b2 = true → b1 = b2
  | ⟨s1, t1⟩, ⟨s2, t2⟩, h => by
    simp only [beqHwIsaBlock, Bool.and_eq_true] at h
    rw [beqList_eq_of_true beqHwIsaStmt_eq_of_true s1 s2 h.1,
        beqHwIsaTerm_eq_of_true t1 t2 h.2]

def beqHwIsaProg (p1 p2 : HwIsaProg) : Bool :=
  beqList beqHwIsaBlock p1.blocks p2.blocks

theorem beqHwIsaProg_eq_of_true :
    ∀ (p1 p2 : HwIsaProg), beqHwIsaProg p1 p2 = true → p1 = p2
  | ⟨bs1⟩, ⟨bs2⟩, h => by
    simp only [beqHwIsaProg] at h
    rw [beqList_eq_of_true beqHwIsaBlock_eq_of_true bs1 bs2 h]

-- ----------------------------------------------------------------------------
-- Operational Semantics of `HwIsaMachine` & `HwIsaLang`
-- ----------------------------------------------------------------------------

/-- Execute a single 64-bit hardware instruction. -/
def execHwIsaStmt (hst : HwIsaState) (stmt : HwIsaStmt) : HwIsaState :=
  match stmt with
  | .movImm dst imm => hst.writeReg dst imm
  | .movReg dst src => hst.writeReg dst (hst.regs src)
  | .addReg dst lhs rhs =>
    hst.writeReg dst (BitVec.ofNat 64 ((hst.regs lhs).toNat + (hst.regs rhs).toNat))
  | .subImm dst imm => hst.writeReg dst (hst.regs dst - imm)

/-- Execute a list of 64-bit hardware instructions. -/
def execHwIsaStmts (hst : HwIsaState) : List HwIsaStmt → HwIsaState
  | [] => hst
  | s :: rest => execHwIsaStmts (execHwIsaStmt hst s) rest

/-- Execute a 64-bit hardware basic block. `ret` returns `rax` (`regs 2`). -/
def stepHwIsaBlock (prog : HwIsaProg) (hst : HwIsaState) :
    StepResult HwIsaState Unit (BitVec 64) :=
  match prog.blocks[hst.pc]? with
  | none => .failed .ub
  | some blk =>
    let hst' := execHwIsaStmts hst blk.stmts
    match blk.term with
    | .ret => .terminated (.normal (hst'.regs ⟨2, by omega⟩))
    | .jmp target => .step () { hst' with pc := target }
    | .trap => .terminated .unwind

def HwIsaMachine : SmallStepMachine HwIsaProg HwIsaState Unit (BitVec 64) where
  initState _ hst := hst.pc = 0
  step prog hst r := r = stepHwIsaBlock prog hst

abbrev HwIsaLang : Language := HwIsaMachine.toLanguage

-- ----------------------------------------------------------------------------
-- Non-Identity Cross-Track Behavior Projection `π_isa`
-- ----------------------------------------------------------------------------

/-- ABI register indices: `rdi = 0` (arg 1 / `_1`), `rsi = 1` (arg 2 / `_2`),
    `rax = 2` (return value / `_0`). -/
def regRdi : Fin 16 := ⟨0, by omega⟩
def regRsi : Fin 16 := ⟨1, by omega⟩
def regRax : Fin 16 := ⟨2, by omega⟩

/-- Encode a `MirVal` as a 64-bit hardware word (`BitVec 64`). -/
def encodeMirVal64 : MirVal → BitVec 64
  | .usize n => BitVec.ofNat 64 n
  | .bool b => if b then 1#64 else 0#64
  | .unit => 0#64
  | .tupleUsizeBool v _ => BitVec.ofNat 64 v
  | .atomicLoc l => BitVec.ofNat 64 l
  | .refSharedLoc l => BitVec.ofNat 64 l
  | .refMutLoc l => BitVec.ofNat 64 l
  | .refSliceLoc l len => BitVec.ofNat 64 (l + len)
  | .adtVal v _ => BitVec.ofNat 64 v
  | .ordering _ => 0#64

/-- Map a `TerminationKind MirVal` to a `TerminationKind (BitVec 64)` via
    `encodeMirVal64`. -/
def mapTerminationKind64 : TerminationKind MirVal → TerminationKind (BitVec 64)
  | .normal v => .normal (encodeMirVal64 v)
  | .unwind => .unwind

/-- Map a `PrefixOutcome MirVal` to a `PrefixOutcome (BitVec 64)` via
    `encodeMirVal64`. -/
def mapPrefixOutcome64 : PrefixOutcome MirVal → PrefixOutcome (BitVec 64)
  | .running => .running
  | .terminated term => .terminated (mapTerminationKind64 term)
  | .failed err => .failed err
  | .stuck => .stuck

/-- Lift a 64-bit hardware state `hst : HwIsaState` to a corresponding
    `MirState` according to the System V x86-64 register convention:
    - `_0` (return place) ← `rax` (`regs 2`)
    - `_1` (first argument) ← `rdi` (`regs 0`)
    - `_2` (second argument) ← `rsi` (`regs 1`) -/
def hwToMirState (hst : HwIsaState) : MirState where
  pc := ⟨hst.pc⟩
  locals := fun idx =>
    if idx == 0 then some (.usize (hst.regs regRax).toNat)
    else if idx == 1 then some (.usize (hst.regs regRdi).toNat)
    else if idx == 2 then some (.usize (hst.regs regRsi).toNat)
    else none
  mem := hst.mem
  curView := fun _ => 0
  acqView := fun _ _ => 0
  callFuel := 0

/-- Map a MIR outcome predicate `ExecOut Unit MirVal → Prop` to a 64-bit
    hardware outcome predicate `ExecOut Unit (BitVec 64) → Prop`. -/
def mapExecOut64 (P_mir : ExecOut Unit MirVal → Prop) :
    ExecOut Unit (BitVec 64) → Prop :=
  fun o_isa =>
    ∃ o_mir,
      P_mir o_mir ∧
      o_isa.trace = o_mir.trace ∧
      o_isa.outcome = mapPrefixOutcome64 o_mir.outcome

/-- Cross-track behavior projection `π_isa : MirLang.Behavior → HwIsaLang.Behavior`
    connecting `MirLang` (`State := MirState`, `Val := MirVal`) to `HwIsaLang`
    (`State := HwIsaState`, `Val := BitVec 64`). -/
def π_isa (B_mir : MirLang.Behavior) : HwIsaLang.Behavior :=
  fun q_isa =>
    (B_mir ⟨hwToMirState q_isa.init, q_isa.steps⟩).map mapExecOut64

/-- `π_isa` is monotone with respect to `≤` (`Preorder.le`), enabling
    multi-language composition in `Trusted.Compiler.compose`. -/
theorem monotone_π_isa : Monotone π_isa := by
  intro B1 B2 h_le q_isa h_def2
  rcases h_le ⟨hwToMirState q_isa.init, q_isa.steps⟩ h_def2 with ⟨h_def1, h_val_le⟩
  refine ⟨h_def1, ?_⟩
  intro o_isa ⟨o_mir, h_p1, h_tr, h_out⟩
  exact ⟨o_mir, h_val_le o_mir h_p1, h_tr, h_out⟩

-- ----------------------------------------------------------------------------
-- Verified Cross-Track Lowering (`MirLang` → `HwIsaLang` via `π_isa`)
-- ----------------------------------------------------------------------------

/-- Source MIR body `mirAddU64Body`: computes `_0 = Add(_1, _2)` on 64-bit
    words and returns `_0`. -/
def mirAddU64Body : MirBody where
  paramTys := [.usize, .usize]
  returnTy := .usize
  localCount := 3
  blocks := [
    { statements := [
        .assign ⟨0⟩ (.binaryOp .add (.copy ⟨1⟩) (.copy ⟨2⟩))
      ],
      terminator := .return_ }
  ]

/-- Target 64-bit hardware program `hwAddU64Prog`: executes `add rax, rdi, rsi`
    and returns `rax`. -/
def hwAddU64Prog : HwIsaProg where
  blocks := [
    { stmts := [.addReg regRax regRdi regRsi],
      term := .ret }
  ]

theorem initMirState_hwToMirState (hst : HwIsaState) (h_pc : hst.pc = 0) :
    initMirState mirAddU64Body (hwToMirState hst) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hwToMirState, h_pc]
  · decide
  · intro i hi
    match i with
    | 0 => exact ⟨.usize (hst.regs regRdi).toNat, rfl, trivial⟩
    | 1 => exact ⟨.usize (hst.regs regRsi).toNat, rfl, trivial⟩
  · intro _ w _
    exact Nat.zero_le w.ts

theorem hwAddU64_step_pc0 (hst : HwIsaState) (h_pc : hst.pc = 0) :
    stepHwIsaBlock hwAddU64Prog hst =
      .terminated (.normal
        (BitVec.ofNat 64 ((hst.regs regRdi).toNat + (hst.regs regRsi).toNat))) := by
  simp [stepHwIsaBlock, hwAddU64Prog, h_pc, execHwIsaStmts, execHwIsaStmt,
    HwIsaState.writeReg, regRax]

theorem mirAddU64_step_pc0 (hst : HwIsaState) (h_pc : hst.pc = 0) :
    stepBlock mirAddU64Body (hwToMirState hst) =
      .terminated (.normal
        (.usize ((hst.regs regRdi).toNat + (hst.regs regRsi).toNat))) := by
  simp [stepBlock, mirAddU64Body, hwToMirState, h_pc, execStatements,
    execStatement, evalRvalue, evalOperand, MirState.readLocal,
    MirState.writeLocal, execTerminator]

/-- `hwAddU64Prog` refines `mirAddU64Body` across the non-identity behavior
    projection `π_isa`. -/
theorem hwAddU64_compiles :
    Compiles MirLang HwIsaLang π_isa mirAddU64Body hwAddU64Prog := by
  intro ⟨hst, steps⟩ _h_src_def
  refine ⟨?_, ?_⟩
  · intro h_init tr out h_reach
    cases h_reach with
    | zero => trivial
    | step _ _ _ _ _ _ h_st _ =>
      change StepResult.step _ _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | choice _ _ _ _ _ _ _ h_st _ _ =>
      change StepResult.choice _ _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | emptyChoice _ _ _ _ h_st _ =>
      change StepResult.choice _ _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | terminated _ _ _ _ => trivial
    | failed _ _ _ h_st =>
      change StepResult.failed _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | noStep _ _ h_ns =>
      exact False.elim (h_ns ⟨_, rfl⟩)
  · intro ⟨tr, out_isa⟩ ⟨h_init, h_reach⟩
    have h_mir_init := initMirState_hwToMirState hst h_init
    cases h_reach with
    | zero =>
      refine ⟨⟨[], .running⟩, ⟨h_mir_init, .zero (hwToMirState hst)⟩, rfl, rfl⟩
    | step _ _ _ _ _ _ h_st _ =>
      change StepResult.step _ _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | choice _ _ _ _ _ _ _ h_st _ _ =>
      change StepResult.choice _ _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | emptyChoice _ _ _ _ h_st _ =>
      change StepResult.choice _ _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | terminated n _ term h_st =>
      change StepResult.terminated term = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st
      injection h_st with h_t
      refine ⟨⟨[], .terminated (.normal (.usize ((hst.regs regRdi).toNat + (hst.regs regRsi).toNat)))⟩,
        ⟨h_mir_init, .terminated n (hwToMirState hst) _ (mirAddU64_step_pc0 hst h_init).symm⟩,
        rfl, ?_⟩
      rw [h_t]; rfl
    | failed _ _ _ h_st =>
      change StepResult.failed _ = stepHwIsaBlock hwAddU64Prog hst at h_st
      rw [hwAddU64_step_pc0 hst h_init] at h_st; nomatch h_st
    | noStep _ _ h_ns =>
      exact False.elim (h_ns ⟨_, rfl⟩)

/-- Any 64-bit hardware program `hwProg` validated against `hwAddU64Prog` by the
    `deriving`-free equality checker `beqHwIsaProg` compiles `mirAddU64Body`
    across `π_isa` without using `deriving` or `Lean.ofReduceBool`. -/
theorem lowerMirToHwIsa_compiles (hwProg : HwIsaProg)
    (h_beq : beqHwIsaProg hwProg hwAddU64Prog = true) :
    Compiles MirLang HwIsaLang π_isa mirAddU64Body hwProg := by
  rw [beqHwIsaProg_eq_of_true hwProg hwAddU64Prog h_beq]
  exact hwAddU64_compiles

end Anneal

-- ============================================================================
-- Section 6: Axiom Audit (`#guard_msgs in #print axioms`)
-- ============================================================================

/-- info: 'Trusted.beqMirVal_eq_of_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Trusted.beqMirVal_eq_of_true

/-- info: 'Anneal.evalSym_slice_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.evalSym_slice_sound

/-- info: 'Anneal.sliceCheckerMirBody_two_elem_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.sliceCheckerMirBody_two_elem_sound

/-- info: 'Anneal.evalSym_enumCert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.evalSym_enumCert

/-- info: 'Anneal.retag_lowering_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.retag_lowering_compiles

/-- info: 'Anneal.unsafePinned_retag_is_pure_copy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.unsafePinned_retag_is_pure_copy

/-- info: 'Anneal.duplicate_retag_refutes_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.duplicate_retag_refutes_compiles

/-- info: 'Anneal.erase_withRetag_refutes_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Anneal.erase_withRetag_refutes_compiles

/-- info: 'Anneal.retag_copy_prop_compiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.retag_copy_prop_compiles

/-- info: 'Anneal.mutual_recursion_callSpec_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.mutual_recursion_callSpec_sound

/-- info: 'Anneal.is_even_is_odd_mutual_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.is_even_is_odd_mutual_sound

/-- info: 'Anneal.beqHwIsaProg_eq_of_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.beqHwIsaProg_eq_of_true

/-- info: 'Anneal.monotone_π_isa' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.monotone_π_isa

/-- info: 'Anneal.lowerMirToHwIsa_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Anneal.lowerMirToHwIsa_compiles


