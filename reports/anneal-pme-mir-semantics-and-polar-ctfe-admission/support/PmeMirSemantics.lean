-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Post-Monomorphization Errors (PMEs), Partial Compilation, and the `zerocopy` Bridge

This standalone Lean 4.34.1 mechanization investigates how Anneal's MIR AST
(`Trusted/MirAst.lean`), small-step operational semantics
(`Trusted/MirSemantics.lean`), and compiler lowering contract
(`TCBItem.rustcLowering` in `Trusted/Refinement.lean` and
`Trusted/MirSemantics.lean`) should model Rust Post-Monomorphization Errors
(PMEs).

Every declaration that models a `rustc` MIR construct or Rust execution/CTFE
rule cites its normative source at the repository's pinned revisions
(`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

## Core Findings Mechanized in This File

1. **Galois Connection Between Program-Side and Spec-Side Compile-Time Gates
   (`Section 1`):**
   In the refinement lattice `Behavior Query Out := Query → Partial (Out → Prop)`,
   a specification precondition (`L.SpecOn pre post`) maps excluded queries to
   the top element `Partial.ub` (`defined := False`), whereas a compile-time
   admissibility filter (`Behavior.when P b`) maps rejected instantiations
   (`¬ P`) to the bottom element `Partial.bot` (`defined := True`,
   `val := fun _ _ => False`, representing zero runtime executions). We prove
   the constructive Galois connection (`behavior_when_given_adjunction`):
   `Behavior.when P b ≤ spec ↔ (P → b ≤ spec) ↔ b ≤ Behavior.given P spec`.
2. **Equivalence and Tradeoffs of Approach 1 vs. Approach 2 (`Sections 2 & 4`):**
   - **Approach 1 (`PartialCompiler` + `TCBItem.rustcLowering`):** Keeps
     `MirSem body` as the unguarded runtime semantics of `body`'s basic blocks,
     makes `compile : MirBody → Partial TargetArtifact` partial, and records in
     `RustcPartialCompiler.SoundOn body` that `(compile body).defined` implies
     both `body.CompileAdmitted` and target refinement `Compiles`.
   - **Approach 2 (`MirMachine.withAdmitted MirBody.CompileAdmitted`):** Gates
     `MirMachine.initState` by `body.CompileAdmitted`. Because `TotalStep` and
     `InhabitedDemonic` depend only on `M.step` (not `M.initState`), structural
     non-vacuity (`non_vacuity_at_every_depth`) is preserved unchanged, and
     `MirSemAdmitted body ≤ spec` is provably equivalent (`↔`) to
     `body.CompileAdmitted → MirSem body ≤ spec` (`mirSemAdmitted_le_iff`).
3. **End-to-End Verification of `const_bounded_add<N>` and `zerocopy`-style
   `transmute_ref<Src, Dst>` (`Section 5`):**
   - Models `Body::required_consts` (`requiredConsts : List ConstMirBody`)
     evaluated in CTFE mode by the same small-step MIR machine (`evalMirStep`),
     plus monomorphized layout checks (`requiredLayouts : List TyLayout`).
   - Verifies `const_bounded_add<N>` for all `N : Nat` with `pre := True`, and
     proves `(constBoundedAddBody N).CompileAdmitted ↔ N ≤ 1000`.
   - Verifies a safe `transmute_ref<Src, Dst>(src: &Src) -> &Dst` (`pre := True`)
     whose runtime reference reborrow `&*(src as *const Src as *const Dst)` is
     only UB-free because its `requiredConsts` assert equal size and compatible
     alignment in CTFE.
   - Proves negative controls rejecting `transmute_ref` when the PME is omitted
     or placed in an unreached runtime dead branch, and flagging
     `const { assert!(false) }` and `const { loop {} }` as failing
     `CompileAdmitted`.
-/

namespace PmeResearch

/-!
## 1. Refinement Preorder, `Partial`, and the `Behavior.when ⊣ Behavior.given` Adjunction
-/

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces with a
    refinement preorder. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructively lifted partial domain $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- Top element ($\mathsf{UB}$, `defined := False`) of `Partial B`. -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Bottom element ($\bot$, `defined := True`, empty outcome predicate) of
    `Partial (Out → Prop)`, representing a compile-time-rejected program with
    zero runtime executions. -/
def Partial.bot {Out : Type u} : Partial (Out → Prop) where
  defined := True
  val _ _ := False

/-- Refinement preorder on `Partial B`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- `Partial.bot` is the bottom element of `Partial (Out → Prop)`: it refines
    every partial outcome predicate `p` (whether defined or undefined). -/
theorem bot_le {Out : Type u} (p : Partial (Out → Prop)) :
    (@Partial.bot Out) ≤ p :=
  fun _ => ⟨True.intro, fun _ hfalse => False.elim hfalse⟩

/-- `Partial.ub` is the top element of `Partial B`. -/
theorem le_ub {B : Type u} [Preorder B] (p : Partial B) :
    p ≤ (@Partial.ub B) :=
  fun hfalse => False.elim hfalse

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Query-indexed partial behaviors over `Query` and `Out`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Left compile-time gate on a program behavior `b`: when `P` holds, behaves as
    `b`; when `¬ P` holds (e.g., compilation rejects the program due to a PME),
    collapses to `Partial.bot` (`defined := True`, empty outcome set). -/
def Behavior.when {Query Out : Type} (P : Prop)
    (b : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P → (b q).defined
    val := fun hdef out => ∃ hP : P, (b q).val (hdef hP) out
  }

/-- Right compile-time guard on a specification `spec`: requires `spec` only
    when `P` holds, collapsing to `Partial.ub` (`defined := False`) when
    `¬ P`. -/
def Behavior.given {Query Out : Type} (P : Prop)
    (spec : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P ∧ (spec q).defined
    val := fun hdef out => (spec q).val hdef.2 out
  }

/-- Program-side compile-time gating (`Behavior.when P b ≤ spec`) is
    constructively equivalent to conditional refinement (`P → b ≤ spec`). -/
theorem behavior_when_le_iff {Query Out : Type} (P : Prop)
    (b spec : Behavior Query Out) :
    Behavior.when P b ≤ spec ↔ (P → b ≤ spec) := by
  constructor
  · intro h hP q hs
    cases h q hs with
    | intro hdef hval =>
      exact ⟨hdef hP, fun out hb => hval out ⟨hP, hb⟩⟩
  · intro h q hs
    refine ⟨fun hP => (h hP q hs).1, ?_⟩
    intro out ⟨hP, hb⟩
    exact (h hP q hs).2 out hb

/-- Conditional refinement (`P → b ≤ spec`) is constructively equivalent to
    refining the guarded specification `Behavior.given P spec`. -/
theorem behavior_le_given_iff {Query Out : Type} (P : Prop)
    (b spec : Behavior Query Out) :
    (P → b ≤ spec) ↔ b ≤ Behavior.given P spec := by
  constructor
  · intro h q ⟨hP, hs⟩
    exact h hP q hs
  · intro h hP q hs
    exact h q ⟨hP, hs⟩

/-- Galois connection (`Behavior.when P ⊣ Behavior.given P`): gating the program
    behavior on the left by `P` (collapsing to `Partial.bot` when `¬ P`) is
    adjoint to guarding the specification on the right by `P` (collapsing to
    `Partial.ub` when `¬ P`). -/
theorem behavior_when_given_adjunction {Query Out : Type} (P : Prop)
    (b spec : Behavior Query Out) :
    Behavior.when P b ≤ spec ↔ b ≤ Behavior.given P spec :=
  Iff.trans (behavior_when_le_iff P b spec) (behavior_le_given_iff P b spec)

/-- Language carrier bundling programs, queries, outcomes, and semantics. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  PmeResearch.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

class TrustedAssumption (A : Type) where
  meaning : A → Prop

structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

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

abbrev VerificationResult
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (specs : List L_src.Behavior := []) : Prop :=
  VerificationResultOn C policy assumptions prog (fun _ => True) specs

/-!
## 2. Small-Step Prefix Semantics and Compile-Time `initState` Gating
-/

inductive ChoiceKind where
  | demonic
  | angelic

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive FailureKind where
  | ub
  | contractViolation

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

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

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

theorem exists_reaches_prefix
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (init : State) (n : Nat) :
    ∀ (s : State),
      ∃ tr out, ReachesPrefix M p init n s tr out ∧ out ≠ .stuck := by
  induction n with
  | zero =>
    intro s
    exact ⟨[], .running, ReachesPrefix.zero s, by intro h; cases h⟩
  | succ k ih =>
    intro s
    cases h_tot p s with
    | intro r hstep =>
      cases r with
      | step obs s' =>
        cases ih s' with
        | intro tr hrest =>
          cases hrest with
          | intro out hpair =>
            exact ⟨obs :: tr, out,
              ReachesPrefix.step k s s' obs tr out hstep hpair.1,
              hpair.2⟩
      | choice kind branches =>
        cases h_dem p s kind branches hstep with
        | intro s' hbranch =>
          cases ih s' with
          | intro tr hrest =>
            cases hrest with
            | intro out hpair =>
              exact ⟨tr, out,
                ReachesPrefix.choice k kind s s' branches tr out hstep hbranch hpair.1,
                hpair.2⟩
      | terminated term =>
        exact ⟨[], .terminated term,
          ReachesPrefix.terminated k s term hstep,
          by intro h; cases h⟩
      | failed err =>
        exact ⟨[], .failed err,
          ReachesPrefix.failed k s err hstep,
          by intro h; cases h⟩

theorem non_vacuity_at_every_depth
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (init : State)
    (h_init : M.initState p init)
    (n : Nat) :
    ∃ out : ExecOut Obs Val,
      M.initState p init ∧
      ReachesPrefix M p init n init out.trace out.outcome ∧
      out.outcome ≠ .stuck := by
  cases exists_reaches_prefix h_tot h_dem p init n init with
  | intro tr hrest =>
    cases hrest with
    | intro oc hpair =>
      exact ⟨{ trace := tr, outcome := oc }, h_init, hpair.1, hpair.2⟩

/-- Gate a `SmallStepMachine`'s initial-state predicate by a compile-time
    admissibility predicate `Admitted : Prog → Prop` (Approach 2). -/
def SmallStepMachine.withAdmitted
    (M : SmallStepMachine Prog State Obs Val)
    (Admitted : Prog → Prop) : SmallStepMachine Prog State Obs Val where
  initState p s := Admitted p ∧ M.initState p s
  step := M.step

/-- Because `TotalStep` depends only on `M.step` (not `M.initState`), gating
    `initState` by `Admitted` preserves `TotalStep` identically. -/
theorem totalStep_withAdmitted
    {M : SmallStepMachine Prog State Obs Val}
    (Admitted : Prog → Prop)
    (h_tot : TotalStep M) :
    TotalStep (M.withAdmitted Admitted) :=
  h_tot

/-- Because `InhabitedDemonic` depends only on `M.step` (not `M.initState`),
    gating `initState` by `Admitted` preserves `InhabitedDemonic`
    identically. -/
theorem inhabitedDemonic_withAdmitted
    {M : SmallStepMachine Prog State Obs Val}
    (Admitted : Prog → Prop)
    (h_dem : InhabitedDemonic M) :
    InhabitedDemonic (M.withAdmitted Admitted) :=
  h_dem

/-- `ReachesPrefix` on `M.withAdmitted Admitted` is identical to `ReachesPrefix`
    on `M` because `ReachesPrefix` only references `M.step`. -/
theorem reachesPrefix_withAdmitted_iff
    {M : SmallStepMachine Prog State Obs Val}
    {Admitted : Prog → Prop}
    {p : Prog} {init : State} {n : Nat} {s : State}
    {tr : List Obs} {out : PrefixOutcome Val} :
    ReachesPrefix (M.withAdmitted Admitted) p init n s tr out ↔
      ReachesPrefix M p init n s tr out := by
  constructor
  · intro h
    induction h with
    | zero s => exact ReachesPrefix.zero s
    | step n s s' obs tr out hstep _ ih =>
      exact ReachesPrefix.step n s s' obs tr out hstep ih
    | choice n kind s s' branches tr out hstep hbr _ ih =>
      exact ReachesPrefix.choice n kind s s' branches tr out hstep hbr ih
    | emptyChoice n kind s branches hstep hemp =>
      exact ReachesPrefix.emptyChoice n kind s branches hstep hemp
    | terminated n s term hstep =>
      exact ReachesPrefix.terminated n s term hstep
    | failed n s err hstep =>
      exact ReachesPrefix.failed n s err hstep
    | noStep n s hno =>
      exact ReachesPrefix.noStep n s hno
  · intro h
    induction h with
    | zero s => exact ReachesPrefix.zero s
    | step n s s' obs tr out hstep _ ih =>
      exact ReachesPrefix.step n s s' obs tr out hstep ih
    | choice n kind s s' branches tr out hstep hbr _ ih =>
      exact ReachesPrefix.choice n kind s s' branches tr out hstep hbr ih
    | emptyChoice n kind s branches hstep hemp =>
      exact ReachesPrefix.emptyChoice n kind s branches hstep hemp
    | terminated n s term hstep =>
      exact ReachesPrefix.terminated n s term hstep
    | failed n s err hstep =>
      exact ReachesPrefix.failed n s err hstep
    | noStep n s hno =>
      exact ReachesPrefix.noStep n s hno

/-- Order-isomorphism (part 1): `BehaviorOf (M.withAdmitted Admitted) p`
    refines `Behavior.when (Admitted p) (BehaviorOf M p)`. -/
theorem behaviorOf_withAdmitted_le_when
    (M : SmallStepMachine Prog State Obs Val)
    (Admitted : Prog → Prop) (p : Prog) :
    BehaviorOf (M.withAdmitted Admitted) p ≤
      Behavior.when (Admitted p) (BehaviorOf M p) := by
  intro q hdef
  refine ⟨?_, ?_⟩
  · intro hinit tr out hreach
    exact hdef hinit.1 hinit.2 tr out (reachesPrefix_withAdmitted_iff.mp hreach)
  · intro out hval
    exact ⟨hval.1.1, hval.1.2, reachesPrefix_withAdmitted_iff.mp hval.2⟩

/-- Order-isomorphism (part 2): `Behavior.when (Admitted p) (BehaviorOf M p)`
    refines `BehaviorOf (M.withAdmitted Admitted) p`. -/
theorem behavior_when_le_behaviorOf_withAdmitted
    (M : SmallStepMachine Prog State Obs Val)
    (Admitted : Prog → Prop) (p : Prog) :
    Behavior.when (Admitted p) (BehaviorOf M p) ≤
      BehaviorOf (M.withAdmitted Admitted) p := by
  intro q hdef
  refine ⟨?_, ?_⟩
  · intro hadm hinit tr out hreach
    exact hdef ⟨hadm, hinit⟩ tr out (reachesPrefix_withAdmitted_iff.mpr hreach)
  · intro out ⟨hadm, hinit, hreach⟩
    exact ⟨⟨hadm, hinit⟩, reachesPrefix_withAdmitted_iff.mpr hreach⟩

/-- Universal equivalence between Approach 2 (`BehaviorOf (M.withAdmitted
    Admitted) p ≤ spec`) and Approach 1 (`Admitted p → BehaviorOf M p ≤ spec`)
    for ANY behavior or specification `spec`. -/
theorem behaviorOf_withAdmitted_le_iff
    (M : SmallStepMachine Prog State Obs Val)
    (Admitted : Prog → Prop) (p : Prog)
    (spec : Behavior (ExecQuery State) (ExecOut Obs Val)) :
    BehaviorOf (M.withAdmitted Admitted) p ≤ spec ↔
      (Admitted p → BehaviorOf M p ≤ spec) := by
  constructor
  · intro h
    exact (behavior_when_le_iff (Admitted p) (BehaviorOf M p) spec).mp
      (Preorder.le_trans (behavior_when_le_behaviorOf_withAdmitted M Admitted p) h)
  · intro h
    exact Preorder.le_trans
      (behaviorOf_withAdmitted_le_when M Admitted p)
      ((behavior_when_le_iff (Admitted p) (BehaviorOf M p) spec).mpr h)

theorem behaviorOf_le_pure
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (fun q => Partial.pure (Post q)) := by
  intro q _
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hval).2

/-!
## 3. Extended MIR AST with `requiredConsts`, `TyLayout`, and Reference Reborrows
-/

/-- Maximum representable 64-bit `isize::MAX` (`2^63 - 1`), bounding valid Rust
    type sizes (`rustc_abi::LayoutError::SizeOverflow`).

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/type-layout.md#L18-L25 -/
def isizeMax : Nat := 9223372036854775807

/-- Maximum representable 64-bit `usize::MAX` (`2^64 - 1`).

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38 -/
def usizeMax : Nat := 18446744073709551615

/-- Concrete size and alignment of a sized Rust type (`rustc_abi::LayoutData`).

    In Rust (`r[layout.properties]`), every sized type has a size in bytes and a
    positive alignment (a power of two dividing `size`, with `size ≤ isize::MAX`):

    > "Alignment is measured in bytes, and must be at least 1, and always a
    > power of 2. The size of a value is always a multiple of its alignment."

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/type-layout.md#L18-L25 -/
structure TyLayout where
  size : Nat
  align : Nat
  deriving DecidableEq

/-- Compile-time layout validity predicate (`rustc_middle::ty::layout::LayoutError`
    freedom): positive alignment, size bounded by `isize::MAX`, and size a
    multiple of alignment. -/
def TyLayout.WellFormed (ly : TyLayout) : Prop :=
  0 < ly.align ∧ ly.size ≤ isizeMax ∧ ly.align ∣ ly.size

/-- Standard concrete layouts for `u8` (`size = 1, align = 1`) and `u64`
    (`size = 8, align = 8`). -/
def u8Layout : TyLayout := { size := 1, align := 1 }
def u64Layout : TyLayout := { size := 8, align := 8 }

structure LocalId where
  index : Nat

structure BlockId where
  index : Nat

/-- Minimal MIR type grammar extended with layout-parameterized shared
    references (`&T` of layout `ly`) and raw pointers (`*const T` of layout
    `ly`) for modeling `zerocopy`'s `transmute_ref<Src, Dst>`. -/
inductive MirTy where
  | usize
  | bool
  | unit
  | tupleUsizeBool
  | refShared (layout : TyLayout)
  | rawPtr (layout : TyLayout)

/-- Runtime scalar, reference, or raw-pointer value.

    - `refLoc loc addr layout` represents a shared reference `&T` pointing to
      allocation `loc` at non-zero byte address `addr` with static pointee
      layout `layout`.
    - `ptrLoc loc addr layout` represents a raw pointer `*const T` pointing to
      allocation `loc` at byte address `addr` with target layout `layout`. -/
inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  | refLoc (loc : Nat) (addr : Nat) (layout : TyLayout)
  | ptrLoc (loc : Nat) (addr : Nat) (layout : TyLayout)

inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

inductive BinOp where
  | lt
  | le
  | eq
  | ne
  | gt
  | ge
  | rem

inductive CheckedBinOp where
  | add
  | sub
  | mul

/-- Right-hand side value computation of a MIR assignment statement, including
    raw-pointer address-of (`&raw const (*src)`), pointer-to-pointer cast
    (`src as *const Dst`), and shared reference reborrow (`&(*src)`).

    Corresponds to `rustc_middle::mir::Rvalue` (`Use`, `RawPtr`, `Cast(PtrToPtr)`,
    `Ref`, `BinaryOp`, and checked arithmetic):

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L975-L1060 -/
inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | checkedBinaryOp (op : CheckedBinOp) (lhs : Operand) (rhs : Operand)
  | proj0 (src : LocalId)
  | proj1 (src : LocalId)
  | addrOfDeref (src : LocalId)
  | castPtrToPtr (src : LocalId) (dstLayout : TyLayout)
  | reborrowShared (src : LocalId) (dstLayout : TyLayout)

inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop

/-- Control-flow transfer at the end of a MIR basic block.

    - `panic` models `core::panicking::panic(...)` in CTFE or runtime `assert!`
      failure blocks, transitioning to `.failed .contractViolation`.
    - `assertNotOverflow` models MIR `TerminatorKind::Assert` on checked
      arithmetic overflow tuples.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L683-L808 -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | panic
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | assertNotOverflow (tupleLocal : LocalId) (target : BlockId)

structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

/-- A constant-evaluation MIR body (`fn_name::{constant#k}: () = { ... }`)
    referenced by `MirBody.requiredConsts`.

    Corresponds to an anonymous constant body referenced by a `ConstOperand` in
    `rustc_middle::mir::Body::required_consts`:

    > "Constants that are required to evaluate successfully for this `Body` to
    > be well-formed. Wait until monomorphization to evaluate them."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L278-L285 -/
structure ConstMirBody where
  localCount : Nat
  blocks : List BasicBlock

/-- Lowered `Runtime(PostCleanup)` MIR body of a single function, extended with
    `requiredConsts` (`Body::required_consts`) and `requiredLayouts` (concrete
    type layouts queried during monomorphization and codegen).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L204-L285 -/
structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock
  requiredConsts : List ConstMirBody := []
  requiredLayouts : List TyLayout := []

/-!
## 4. Operational Semantics, `CompileAdmitted`, and Approaches 1 & 2
-/

/-- Memory state recording the live initialized byte size `allocSize loc` of
    each allocation `loc`. -/
structure MemState where
  allocSize : Nat → Nat

def MemState.empty : MemState where
  allocSize := fun _ => 0

structure MirState where
  locals : Nat → Option MirVal
  mem : MemState
  block : Nat
  stmtIdx : Nat

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Dynamic value validity matching a produced `MirVal` against its static
    `MirTy` in memory state `m` (`r[undefined.invalid]`,
    `r[undefined.validity.reference-box]`):
    - A shared reference `.refLoc loc addr ly` of type `.refShared ly` must be
      non-null (`addr ≠ 0`), properly aligned (`0 < ly.align ∧ ly.align ∣ addr`),
      and in-bounds of its live allocation (`ly.size ≤ m.allocSize loc`).
    - A raw pointer `.ptrLoc loc addr ly` of type `.rawPtr ly` has no alignment
      or dereferenceable-size requirement until dereferenced or reborrowed as a
      reference.

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L114-L147 -/
def refValidIn (m : MemState) (loc addr : Nat) (ly : TyLayout) : Prop :=
  addr ≠ 0 ∧ 0 < ly.align ∧ ly.align ∣ addr ∧ ly.size ≤ m.allocSize loc

def MirVal.hasTy (m : MemState) (v : MirVal) (ty : MirTy) : Prop :=
  match v, ty with
  | .usize _, .usize => True
  | .bool _, .bool => True
  | .unit, .unit => True
  | .tupleUsizeBool _ _, .tupleUsizeBool => True
  | .refLoc loc addr ly, .refShared expectedLy =>
    ly = expectedLy ∧ refValidIn m loc addr ly
  | .ptrLoc _ _ ly, .rawPtr expectedLy =>
    ly = expectedLy
  | _, _ => False

def argsMatchLocals (m : MemState) (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k => (∃ v, locals k = some v ∧ v.hasTy m ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  argsMatchLocals s.mem body.argTys s.locals

def evalOperand (locals : Nat → Option MirVal) (op : Operand) :
    Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    match locals src.index with
    | some v => some (v, locals)
    | none => none
  | .move src =>
    match locals src.index with
    | some v => some (v, updateLocal locals src.index none)
    | none => none
  | .constVal v =>
    some (v, locals)

def evalBinOp (op : BinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .lt => some (.bool (decide (n1 < n2)))
    | .le => some (.bool (decide (n1 ≤ n2)))
    | .eq => some (.bool (decide (n1 = n2)))
    | .ne => some (.bool (decide (n1 ≠ n2)))
    | .gt => some (.bool (decide (n2 < n1)))
    | .ge => some (.bool (decide (n2 ≤ n1)))
    | .rem => some (.usize (n1 % n2))
  | _, _ => none

def evalCheckedBinOp (op : CheckedBinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.tupleUsizeBool (n1 + n2) (decide (usizeMax < n1 + n2)))
    | .sub => some (.tupleUsizeBool (n1 - n2) (decide (n1 < n2)))
    | .mul => some (.tupleUsizeBool (n1 * n2) (decide (usizeMax < n1 * n2)))
  | _, _ => none

/-- Single-step statement evaluation.

    In particular, `.reborrowShared src dstLayout` (`_0 = &(*_2)`) checks that
    the raw pointer in `src` is non-null, aligned to `dstLayout.align`
    (`addr % dstLayout.align = 0`), and points to an allocation of size at least
    `dstLayout.size` (`dstLayout.size ≤ s.mem.allocSize loc`). Producing a
    misaligned or out-of-bounds reference triggers immediate `.failed .ub`
    (`r[undefined.validity.reference-box]`).

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/behavior-considered-undefined.md#L130-L147 -/
def evalMirStmt (s : MirState) (stmt : Stmt) : StepResult MirState Unit MirVal :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      .step () { s with
        locals := updateLocal locals' dst.index (some v)
        stmtIdx := s.stmtIdx + 1
      }
    | none => .failed .ub
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some res =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
  | .assign dst (.checkedBinaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalCheckedBinOp op v1 v2 with
        | some res =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
  | .assign dst (.proj0 src) =>
    match s.locals src.index with
    | some (.tupleUsizeBool val _) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.usize val))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed .ub
  | .assign dst (.proj1 src) =>
    match s.locals src.index with
    | some (.tupleUsizeBool _ ov) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.bool ov))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed .ub
  | .assign dst (.addrOfDeref src) =>
    match s.locals src.index with
    | some (.refLoc loc addr ly) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.ptrLoc loc addr ly))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed .ub
  | .assign dst (.castPtrToPtr src dstLayout) =>
    match s.locals src.index with
    | some (.ptrLoc loc addr _) =>
      .step () { s with
        locals := updateLocal s.locals dst.index (some (.ptrLoc loc addr dstLayout))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => .failed .ub
  | .assign dst (.reborrowShared src dstLayout) =>
    match s.locals src.index with
    | some (.ptrLoc loc addr ptrLy) =>
      if decide (ptrLy = dstLayout) &&
         decide (addr ≠ 0) &&
         decide (0 < dstLayout.align) &&
         decide (dstLayout.align ∣ addr) &&
         decide (dstLayout.size ≤ s.mem.allocSize loc) then
        .step () { s with
          locals := updateLocal s.locals dst.index (some (.refLoc loc addr dstLayout))
          stmtIdx := s.stmtIdx + 1
        }
      else
        .failed .ub
    | _ => .failed .ub
  | .storageLive loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .storageDead loc =>
    .step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

def evalMirTerminator (s : MirState) (term : Terminator) :
    StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | some retVal => .terminated (.normal retVal)
    | none => .failed .ub
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed .ub
  | .panic =>
    .failed .contractViolation
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand s.locals discr with
    | some (.bool false, locals') =>
      .step () { s with
        locals := locals'
        block := falseTarget.index
        stmtIdx := 0
      }
    | some (.bool true, locals') =>
      .step () { s with
        locals := locals'
        block := trueTarget.index
        stmtIdx := 0
      }
    | _ => .failed .ub
  | .assertNotOverflow tupleLocal target =>
    match s.locals tupleLocal.index with
    | some (.tupleUsizeBool _ false) =>
      .step () { s with
        block := target.index
        stmtIdx := 0
      }
    | some (.tupleUsizeBool _ true) =>
      .failed .contractViolation
    | _ => .failed .ub

def evalBlocksStep (blocks : List BasicBlock) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator s bb.terminator

def evalMirStep (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  evalBlocksStep body.blocks s

/-- Unguarded runtime small-step machine for `MirBody` (Approach 1 base
    machine). -/
def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = evalMirStep body s

def MirLang : Language :=
  MirMachine.toLanguage

abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

/-- Initial empty state for evaluating a `ConstMirBody` in CTFE mode. -/
def initCtfeState : MirState where
  locals := fun _ => none
  mem := MemState.empty
  block := 0
  stmtIdx := 0

/-- Small-step machine evaluating a `ConstMirBody` in CTFE mode using the exact
    same `evalBlocksStep` transition semantics as runtime MIR. -/
def ConstMirMachine : SmallStepMachine ConstMirBody MirState Unit MirVal where
  initState _ s := s = initCtfeState
  step c s r := r = evalBlocksStep c.blocks s

/-- Deterministic multi-step fuel evaluator for `ConstMirBody` in CTFE mode,
    mirroring `ReachesPrefix ConstMirMachine`. -/
def evalCtfeFuel (c : ConstMirBody) : Nat → MirState → PrefixOutcome MirVal
  | 0, _ => .running
  | n + 1, s =>
    match evalBlocksStep c.blocks s with
    | .step _ s' => evalCtfeFuel c n s'
    | .choice _ _ => .stuck
    | .terminated term => .terminated term
    | .failed err => .failed err

theorem evalMirStmt_not_choice (s : MirState) (stmt : Stmt)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirStmt s stmt := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals op <;> intro h <;> cases h
    | binaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals lhs with
      | none => intro h; cases h
      | some p1 =>
        dsimp
        cases evalOperand p1.2 rhs with
        | none => intro h; cases h
        | some p2 =>
          dsimp
          cases evalBinOp op p1.1 p2.1 <;> intro h <;> cases h
    | checkedBinaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      cases evalOperand s.locals lhs with
      | none => intro h; cases h
      | some p1 =>
        dsimp
        cases evalOperand p1.2 rhs with
        | none => intro h; cases h
        | some p2 =>
          dsimp
          cases evalCheckedBinOp op p1.1 p2.1 <;> intro h <;> cases h
    | proj0 src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v => cases v <;> intro h <;> cases h
    | proj1 src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v => cases v <;> intro h <;> cases h
    | addrOfDeref src =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v => cases v <;> intro h <;> cases h
    | castPtrToPtr src dstLy =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v => cases v <;> intro h <;> cases h
    | reborrowShared src dstLy =>
      dsimp [evalMirStmt]
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v with
        | ptrLoc loc addr ptrLy =>
          dsimp
          split <;> intro h <;> cases h
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | refLoc _ _ _ =>
          intro h; cases h
  | storageLive _ => intro h; cases h
  | storageDead _ => intro h; cases h
  | nop => intro h; cases h

theorem evalMirTerminator_not_choice (s : MirState) (term : Terminator)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirTerminator s term := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    cases s.locals 0 <;> intro h <;> cases h
  | goto _ => intro h; cases h
  | unreachable => intro h; cases h
  | panic => intro h; cases h
  | switchInt discr _ _ =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk val _ =>
        cases val with
        | bool b => cases b <;> intro h <;> cases h
        | usize _ | unit | tupleUsizeBool _ _ | refLoc _ _ _ | ptrLoc _ _ _ =>
          intro h; cases h
  | assertNotOverflow tl _ =>
    dsimp [evalMirTerminator]
    cases s.locals tl.index with
    | none => intro h; cases h
    | some v =>
      cases v with
      | tupleUsizeBool _ ov => cases ov <;> intro h <;> cases h
      | usize _ | bool _ | unit | refLoc _ _ _ | ptrLoc _ _ _ =>
        intro h; cases h

theorem evalBlocksStep_not_choice (blocks : List BasicBlock) (s : MirState)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalBlocksStep blocks s := by
  unfold evalBlocksStep
  cases blocks[s.block]? with
  | none => intro h; cases h
  | some bb =>
    dsimp
    cases bb.stmts[s.stmtIdx]? with
    | none => exact evalMirTerminator_not_choice s bb.terminator kind branches
    | some stmt => exact evalMirStmt_not_choice s stmt kind branches

/-- Bridge lemma: `ReachesPrefix ConstMirMachine` is completely determined by
    `evalCtfeFuel`. -/
theorem reachesPrefix_constMirMachine_eq_evalCtfeFuel
    (c : ConstMirBody) (init : MirState) (n : Nat) :
    ∀ (s : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      ReachesPrefix ConstMirMachine c init n s tr out →
      out = evalCtfeFuel c n s := by
  induction n with
  | zero =>
    intro s tr out hreach
    cases hreach with
    | zero => rfl
  | succ k ih =>
    intro s tr out hreach
    unfold evalCtfeFuel
    cases hreach with
    | step _ _ s' obs tr' _ hstep hrest =>
      have hstep' : StepResult.step obs s' = evalBlocksStep c.blocks s := hstep
      rw [← hstep']
      exact ih s' tr' out hrest
    | choice _ kind _ _ branches _ _ hstep _ _ =>
      exact False.elim (evalBlocksStep_not_choice c.blocks s kind branches hstep)
    | emptyChoice _ kind _ branches hstep _ =>
      exact False.elim (evalBlocksStep_not_choice c.blocks s kind branches hstep)
    | terminated _ _ term hstep =>
      have hstep' : StepResult.terminated term = evalBlocksStep c.blocks s := hstep
      rw [← hstep']
    | failed _ _ err hstep =>
      have hstep' : StepResult.failed err = evalBlocksStep c.blocks s := hstep
      rw [← hstep']
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, rfl⟩)

/-- A `ConstMirBody` succeeds in CTFE (`CtfeAdmitted c`) when:
    1. Every finite execution prefix from `initCtfeState` is safe (`out.isSafe`,
       ruling out CTFE panic `.failed .contractViolation` and CTFE UB
       `.failed .ub`), and
    2. There exists a finite step budget `steps` reaching
       `.terminated (.normal .unit)` (ruling out CTFE infinite loops such as
       `const { loop {} }`).

    Corresponds to `tcx.eval_mir_constant` succeeding during
    `rustc_monomorphize::collector::collect_items_rec`:

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1090-L1110 -/
def CtfeAdmitted (c : ConstMirBody) : Prop :=
  (∀ steps tr out,
    ReachesPrefix ConstMirMachine c initCtfeState steps initCtfeState tr out →
    out.isSafe) ∧
  (∃ steps tr,
    ReachesPrefix ConstMirMachine c initCtfeState steps initCtfeState tr
      (.terminated (.normal .unit)))

/-- Compile-time admissibility (`CompileAdmitted`) of a monomorphized `MirBody`:
    every required constant in `body.requiredConsts` succeeds in CTFE, and every
    queried layout in `body.requiredLayouts` is well-formed. -/
def MirBody.CompileAdmitted (body : MirBody) : Prop :=
  AllHold (body.requiredConsts.map CtfeAdmitted) ∧
  AllHold (body.requiredLayouts.map TyLayout.WellFormed)

/-!
### 4.1 Approach 1: Partial `compile` in `RustcPartialCompiler` and `TCBItem.rustcLowering`
-/

/-- A compiler whose `compile` phase is partial (`L_src.Prog → Partial L_tgt.Prog`),
    rejecting source programs that fail post-monomorphization checks. -/
structure PartialCompiler (L_src L_tgt : Language) where
  compile : L_src.Prog → Partial L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of a `PartialCompiler` on `body : MirBody`
    (`TCBItem.rustcLowering`'s meaning under Approach 1):
    1. `C.π` is monotone,
    2. **Compile-time PME gate soundness:** if `C.compile body` is defined
       (`rustc` succeeds in compiling `body`), then `body.CompileAdmitted` holds
       (because `rustc` evaluates `body.requiredConsts` and `body.requiredLayouts`
       before emitting target code), and
    3. **Target lowering soundness:** whenever `h : (C.compile body).defined`
       holds, the emitted artifact `(C.compile body).val h` refines
       `C.π (MirSem body)`. -/
def PartialCompiler.SoundOn {L_tgt : Language}
    (C : PartialCompiler MirLang L_tgt) (body : MirBody) : Prop :=
  Monotone C.π ∧
  ((C.compile body).defined → body.CompileAdmitted) ∧
  (∀ h : (C.compile body).defined,
    Compiles MirLang L_tgt C.π body ((C.compile body).val h))

/-- Verification obligation under `PartialCompiler`: for every successful
    compilation `h : (C.compile s).defined`, both the source `s` and the
    compiled target `(C.compile s).val h` satisfy `spec`. -/
def PartialCompiler.Verified {L_src L_tgt : Language}
    (C : PartialCompiler L_src L_tgt) (s : L_src.Prog)
    (spec : L_src.Behavior) : Prop :=
  ∀ h : (C.compile s).defined,
    L_src.sem s ≤ spec ∧
    Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
    L_tgt.sem ((C.compile s).val h) ≤ C.π spec

/-- Bridge lemma for Approach 1: given `C.SoundOn body` and a proof that
    `body.CompileAdmitted → MirSem body ≤ spec`, discharges
    `C.Verified body spec`. -/
theorem PartialCompiler.SoundOn.verify {L_tgt : Language}
    {C : PartialCompiler MirLang L_tgt}
    {body : MirBody} {spec : MirLang.Behavior}
    (h_sound : C.SoundOn body)
    (h_src : body.CompileAdmitted → MirSem body ≤ spec) :
    C.Verified body spec := by
  intro hcomp
  have hadm : body.CompileAdmitted := h_sound.2.1 hcomp
  have hle : MirSem body ≤ spec := h_src hadm
  have hcompiles := h_sound.2.2 hcomp
  exact ⟨hle, hcompiles, Preorder.le_trans hcompiles (h_sound.1 hle)⟩

structure TargetArtifact where
  private mk ::
  unit : Unit

opaque rustcPartial : MirBody → Partial TargetArtifact :=
  fun body => {
    defined := body.CompileAdmitted
    val := fun _ => { unit := () }
  }

opaque TargetSem :
    TargetArtifact → ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop) :=
  fun _ _ => Partial.ub

def TargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery MirState
  Out := ExecOut Unit MirVal
  sem := TargetSem

opaque π_c : MirLang.Behavior → TargetLang.Behavior :=
  fun b => b

def RustcPartialCompiler : PartialCompiler MirLang TargetLang where
  compile := rustcPartial
  π := π_c

/-!
### 4.2 Approach 2: Gating `MirMachine.initState` by `MirBody.CompileAdmitted`
-/

/-- `MirMachine` gated at `initState` by `MirBody.CompileAdmitted`
    (Approach 2). -/
def MirMachineAdmitted : SmallStepMachine MirBody MirState Unit MirVal :=
  MirMachine.withAdmitted MirBody.CompileAdmitted

def MirLangAdmitted : Language :=
  MirMachineAdmitted.toLanguage

abbrev MirSemAdmitted (body : MirBody) : MirLangAdmitted.Behavior :=
  MirLangAdmitted.sem body

/-- `MirMachine` is total. -/
theorem mirMachine_total : TotalStep MirMachine :=
  fun body s => ⟨evalMirStep body s, rfl⟩

/-- `MirMachine` has no empty choice nodes. -/
theorem mirMachine_inhabited : InhabitedDemonic MirMachine := by
  intro body s kind branches hstep
  exact False.elim (evalBlocksStep_not_choice body.blocks s kind branches hstep)

/-- Approach 2 preserves `TotalStep` unchanged. -/
theorem mirMachineAdmitted_total : TotalStep MirMachineAdmitted :=
  totalStep_withAdmitted MirBody.CompileAdmitted mirMachine_total

/-- Approach 2 preserves `InhabitedDemonic` unchanged. -/
theorem mirMachineAdmitted_inhabited : InhabitedDemonic MirMachineAdmitted :=
  inhabitedDemonic_withAdmitted MirBody.CompileAdmitted mirMachine_inhabited

/-- Fundamental Equivalence Theorem between Approach 2 and Approach 1:
    `MirSemAdmitted body ≤ spec` holds if and only if
    `body.CompileAdmitted → MirSem body ≤ spec`. -/
theorem mirSemAdmitted_le_iff (body : MirBody) (spec : MirLang.Behavior) :
    MirSemAdmitted body ≤ spec ↔ (body.CompileAdmitted → MirSem body ≤ spec) :=
  behaviorOf_withAdmitted_le_iff MirMachine MirBody.CompileAdmitted body spec

/-- Any Approach 2 proof (`MirSemAdmitted body ≤ spec`) directly discharges
    Approach 1 (`RustcPartialCompiler.Verified body spec`) given
    `RustcPartialCompiler.SoundOn body`. -/
theorem approach1_verified_of_approach2
    {body : MirBody} {spec : MirLang.Behavior}
    (h_sound : RustcPartialCompiler.SoundOn body)
    (h_app2 : MirSemAdmitted body ≤ spec) :
    RustcPartialCompiler.Verified body spec :=
  PartialCompiler.SoundOn.verify h_sound ((mirSemAdmitted_le_iff body spec).mp h_app2)

/-!
### 4.3 Distinguishing Conditional Soundness from Compile-Time Admissibility
-/

/-- Concrete-function / monomorphic admissibility obligation: pairs conditional
    verification (`RustcPartialCompiler.Verified body spec`) with a proof that
    `body` is itself compile-time admissible (`body.CompileAdmitted`), catching
    dead concrete functions like `pub fn broken() { const { assert!(false) }; }`. -/
def ConcreteVerifiedAndAdmitted (body : MirBody) (spec : MirLang.Behavior) : Prop :=
  body.CompileAdmitted ∧ MirSemAdmitted body ≤ spec

/-- Parametric / generic function admissibility obligation: proves that every
    monomorphization `body a` is safe and satisfies `spec a` when compiled
    (`∀ a, MirSemAdmitted (body a) ≤ spec a`), that `CompileAdmitted` is
    characterized by `Domain a` (`∀ a, (body a).CompileAdmitted ↔ Domain a`),
    and that `Domain` is inhabited (`∃ a, Domain a`). -/
def GenericVerifiedWithDomain {α : Type}
    (body : α → MirBody) (Domain : α → Prop)
    (spec : α → MirLang.Behavior) : Prop :=
  (∀ a, MirSemAdmitted (body a) ≤ spec a) ∧
  (∀ a, (body a).CompileAdmitted ↔ Domain a) ∧
  (∃ a, Domain a)

/-!
## 5. End-to-End Case Studies and Negative Controls
-/

/-!
### 5.1 Case Study 1: `const_bounded_add<const N: usize>(x: usize) -> usize`

```rust
pub fn const_bounded_add<const N: usize>(x: usize) -> usize {
    const { assert!(N <= 1000) };
    if x <= 1000 { x + N } else { 0 }
}
```
-/

/-- Anonymous constant MIR body `const_bounded_add::{constant#0}` emitted by
    `rustc --emit=mir` for `const { assert!(N <= 1000) }`:
    ```text
    bb0: {
        _1 = Le(const N, const 1000_usize);
        switchInt(move _1) -> [0: bb1, otherwise: bb2];
    }
    bb1: {
        panic;
    }
    bb2: {
        _0 = const ();
        return;
    }
    ``` -/
def constBoundedAddConst0 (N : Nat) : ConstMirBody where
  localCount := 2
  blocks := [
    { stmts := [
        .assign ⟨1⟩ (.binaryOp .le (.constVal (.usize N)) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨1⟩) ⟨1⟩ ⟨2⟩ },
    { stmts := []
      terminator := .panic },
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal .unit))
      ]
      terminator := .return_ }
  ]

/-- Lowered `Runtime(PostCleanup)` MIR body for `const_bounded_add<N>`:
    ```text
    bb0: {
        _2 = Le(copy _1, const 1000_usize);
        switchInt(move _2) -> [0: bb3, otherwise: bb1];
    }
    bb1: {
        _3 = AddWithOverflow(copy _1, const N);
        assert(!move (_3.1: bool)) -> [success: bb2];
    }
    bb2: {
        _0 = move (_3.0: usize);
        goto -> bb4;
    }
    bb3: {
        _0 = const 0_usize;
        goto -> bb4;
    }
    bb4: {
        return;
    }
    ``` -/
def constBoundedAddBody (N : Nat) : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.binaryOp .le (.copy ⟨1⟩) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨3⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨3⟩ (.checkedBinaryOp .add (.copy ⟨1⟩) (.constVal (.usize N)))
      ]
      terminator := .assertNotOverflow ⟨3⟩ ⟨2⟩ },
    { stmts := [
        .assign ⟨0⟩ (.proj0 ⟨3⟩)
      ]
      terminator := .goto ⟨4⟩ },
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0)))
      ]
      terminator := .goto ⟨4⟩ },
    { stmts := []
      terminator := .return_ }
  ]
  requiredConsts := [constBoundedAddConst0 N]
  requiredLayouts := []

/-- Specification for `const_bounded_add<N>`:
    - `defined := True` (unconditional safety for a safe `pub fn`, `pre := True`)
    - `val`: returns `x + N` when `x ≤ 1000`, and `0` otherwise. -/
def EnsuresConstBoundedAdd (N : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret x0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      ret = .usize (if decide (x0 ≤ 1000) then x0 + N else 0))

theorem evalCtfeFuel_step {c : ConstMirBody} {n : Nat} {s s' : MirState}
    (h : evalBlocksStep c.blocks s = .step () s') :
    evalCtfeFuel c (n + 1) s = evalCtfeFuel c n s' := by
  cases n <;> (unfold evalCtfeFuel; rw [h]; rfl)

theorem evalCtfeFuel_terminated {c : ConstMirBody} {n : Nat} {s : MirState}
    {term : TerminationKind MirVal}
    (h : evalBlocksStep c.blocks s = .terminated term) :
    evalCtfeFuel c (n + 1) s = .terminated term := by
  unfold evalCtfeFuel
  rw [h]

/-- Exact step-by-step CTFE evaluation of `constBoundedAddConst0 N`:
    - When `N ≤ 1000`, `evalCtfeFuel` reaches `.terminated (.normal .unit)` at
      step `4` and is safe at every step budget `n`.
    - When `¬ (N ≤ 1000)`, `evalCtfeFuel` reaches `.failed .contractViolation`
      at step `3`. -/
theorem constBoundedAddConst0_ctfe_iff (N : Nat) :
    CtfeAdmitted (constBoundedAddConst0 N) ↔ N ≤ 1000 := by
  constructor
  · intro ⟨hSafe, _⟩
    cases hdec : decide (N ≤ 1000) with
    | true => exact of_decide_eq_true hdec
    | false =>
      let s1 : MirState := {
        locals := updateLocal initCtfeState.locals 1 (some (.bool false))
        mem := MemState.empty
        block := 0
        stmtIdx := 1
      }
      let s2 : MirState := {
        locals := updateLocal s1.locals 1 none
        mem := MemState.empty
        block := 1
        stmtIdx := 0
      }
      have hstep0 : evalBlocksStep (constBoundedAddConst0 N).blocks initCtfeState = .step () s1 := by
        change StepResult.step () {
          locals := updateLocal initCtfeState.locals 1 (some (.bool (decide (N ≤ 1000))))
          mem := MemState.empty
          block := 0
          stmtIdx := 1
        } = .step () s1
        rw [hdec]
      have hstep1 : evalBlocksStep (constBoundedAddConst0 N).blocks s1 = .step () s2 := rfl
      have hstep2 : evalBlocksStep (constBoundedAddConst0 N).blocks s2 = .failed .contractViolation := rfl
      have hr3 : ReachesPrefix ConstMirMachine (constBoundedAddConst0 N) initCtfeState 3 initCtfeState [(), ()] (.failed .contractViolation) :=
        ReachesPrefix.step 2 initCtfeState s1 () [()] (.failed .contractViolation) hstep0.symm
          (ReachesPrefix.step 1 s1 s2 () [] (.failed .contractViolation) hstep1.symm
            (ReachesPrefix.failed 0 s2 .contractViolation hstep2.symm))
      exact False.elim (hSafe 3 [(), ()] (.failed .contractViolation) hr3)
  · intro hLe
    have hdec : decide (N ≤ 1000) = true := decide_eq_true hLe
    let s1 : MirState := {
      locals := updateLocal initCtfeState.locals 1 (some (.bool true))
      mem := MemState.empty
      block := 0
      stmtIdx := 1
    }
    let s2 : MirState := {
      locals := updateLocal s1.locals 1 none
      mem := MemState.empty
      block := 2
      stmtIdx := 0
    }
    let s3 : MirState := {
      locals := updateLocal s2.locals 0 (some .unit)
      mem := MemState.empty
      block := 2
      stmtIdx := 1
    }
    have hstep0 : evalBlocksStep (constBoundedAddConst0 N).blocks initCtfeState = .step () s1 := by
      change StepResult.step () {
        locals := updateLocal initCtfeState.locals 1 (some (.bool (decide (N ≤ 1000))))
        mem := MemState.empty
        block := 0
        stmtIdx := 1
      } = .step () s1
      rw [hdec]
    have hstep1 : evalBlocksStep (constBoundedAddConst0 N).blocks s1 = .step () s2 := rfl
    have hstep2 : evalBlocksStep (constBoundedAddConst0 N).blocks s2 = .step () s3 := rfl
    have hstep3 : evalBlocksStep (constBoundedAddConst0 N).blocks s3 = .terminated (.normal .unit) := rfl
    refine ⟨?_, ?_⟩
    · intro steps tr out hreach
      have hout := reachesPrefix_constMirMachine_eq_evalCtfeFuel
        (constBoundedAddConst0 N) initCtfeState steps initCtfeState tr out hreach
      subst hout
      cases steps with
      | zero => exact True.intro
      | succ n1 =>
        rw [evalCtfeFuel_step hstep0]
        cases n1 with
        | zero => exact True.intro
        | succ n2 =>
          rw [evalCtfeFuel_step hstep1]
          cases n2 with
          | zero => exact True.intro
          | succ n3 =>
            rw [evalCtfeFuel_step hstep2]
            cases n3 with
            | zero => exact True.intro
            | succ n4 =>
              rw [evalCtfeFuel_terminated hstep3]
              exact True.intro
    · refine ⟨4, [(), (), ()], ?_⟩
      exact ReachesPrefix.step 3 initCtfeState s1 () [(), ()] (.terminated (.normal MirVal.unit)) hstep0.symm
        (ReachesPrefix.step 2 s1 s2 () [()] (.terminated (.normal MirVal.unit)) hstep1.symm
          (ReachesPrefix.step 1 s2 s3 () [] (.terminated (.normal MirVal.unit)) hstep2.symm
            (ReachesPrefix.terminated 0 s3 (.normal MirVal.unit) hstep3.symm)))

/-- Theorem 1a: `constBoundedAddBody N` is compile-time admissible if and only
    if `N ≤ 1000`. -/
theorem constBoundedAdd_compileAdmitted_iff (N : Nat) :
    (constBoundedAddBody N).CompileAdmitted ↔ N ≤ 1000 := by
  unfold MirBody.CompileAdmitted constBoundedAddBody AllHold
  dsimp [List.map, List.foldr]
  constructor
  · intro h
    exact (constBoundedAddConst0_ctfe_iff N).mp h.1.1
  · intro hLe
    exact ⟨⟨(constBoundedAddConst0_ctfe_iff N).mpr hLe, True.intro⟩, True.intro⟩

/-- Deterministic fuel evaluator for runtime `MirBody`, used to simplify
    small-step prefix case analysis. -/
def evalMirFuel (body : MirBody) : Nat → MirState → PrefixOutcome MirVal
  | 0, _ => .running
  | n + 1, s =>
    match evalMirStep body s with
    | .step _ s' => evalMirFuel body n s'
    | .choice _ _ => .stuck
    | .terminated term => .terminated term
    | .failed err => .failed err

theorem evalMirFuel_step {body : MirBody} {n : Nat} {s s' : MirState}
    (h : evalMirStep body s = .step () s') :
    evalMirFuel body (n + 1) s = evalMirFuel body n s' := by
  cases n <;> (unfold evalMirFuel; rw [h]; rfl)

theorem evalMirFuel_terminated {body : MirBody} {n : Nat} {s : MirState}
    {term : TerminationKind MirVal}
    (h : evalMirStep body s = .terminated term) :
    evalMirFuel body (n + 1) s = .terminated term := by
  unfold evalMirFuel
  rw [h]

theorem reachesPrefix_mirMachine_eq_evalMirFuel
    (body : MirBody) (init : MirState) (n : Nat) :
    ∀ (s : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      ReachesPrefix MirMachine body init n s tr out →
      out = evalMirFuel body n s := by
  induction n with
  | zero =>
    intro s tr out hreach
    cases hreach with
    | zero => rfl
  | succ k ih =>
    intro s tr out hreach
    unfold evalMirFuel
    cases hreach with
    | step _ _ s' obs tr' _ hstep hrest =>
      have hstep' : StepResult.step obs s' = evalMirStep body s := hstep
      rw [← hstep']
      exact ih s' tr' out hrest
    | choice _ kind _ _ branches _ _ hstep _ _ =>
      exact False.elim (evalBlocksStep_not_choice body.blocks s kind branches hstep)
    | emptyChoice _ kind _ branches hstep _ =>
      exact False.elim (evalBlocksStep_not_choice body.blocks s kind branches hstep)
    | terminated _ _ term hstep =>
      have hstep' : StepResult.terminated term = evalMirStep body s := hstep
      rw [← hstep']
    | failed _ _ err hstep =>
      have hstep' : StepResult.failed err = evalMirStep body s := hstep
      rw [← hstep']
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, rfl⟩)

/-- Source conditional correctness of `constBoundedAddBody N`: assuming
    `(constBoundedAddBody N).CompileAdmitted`, every runtime prefix is safe
    (no overflow failure can occur because `x0 ≤ 1000` and `N ≤ 1000` imply
    `x0 + N ≤ 2000 ≤ usizeMax`) and satisfies `EnsuresConstBoundedAdd N`. -/
theorem constBoundedAdd_source_verified (N : Nat) :
    (constBoundedAddBody N).CompileAdmitted →
      MirSem (constBoundedAddBody N) ≤ EnsuresConstBoundedAdd N := by
  intro hAdm
  have hN : N ≤ 1000 := (constBoundedAdd_compileAdmitted_iff N).mp hAdm
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out ⟨hinit, hreach⟩
  cases q with
  | mk init steps =>
    cases init with
    | mk locals mem block stmtIdx =>
      have hb : block = 0 := hinit.1
      have hs : stmtIdx = 0 := hinit.2.1
      subst hb hs
      have harg : ∃ v, locals 1 = some v ∧ v.hasTy mem .usize :=
        hinit.2.2.2.1
      cases harg with
      | intro v hv =>
        cases v with
        | bool _ | unit | tupleUsizeBool _ _ | refLoc _ _ _ | ptrLoc _ _ _ =>
          cases hv.2
        | usize x0 =>
          have hx0 : locals 1 = some (.usize x0) := hv.1
          let s0 : MirState := { locals := locals, mem := mem, block := 0, stmtIdx := 0 }
          have hout := reachesPrefix_mirMachine_eq_evalMirFuel
            (constBoundedAddBody N) s0 steps s0 out.trace out.outcome hreach
          cases hbranch : decide (x0 ≤ 1000) with
          | false =>
            -- Branch `x0 > 1000`: jumps to `bb3`, sets `_0 = 0`, jumps to `bb4`, returns `0`.
            let s1 : MirState := {
              locals := updateLocal locals 2 (some (.bool false))
              mem := mem
              block := 0
              stmtIdx := 1
            }
            let s2 : MirState := {
              locals := updateLocal s1.locals 2 none
              mem := mem
              block := 3
              stmtIdx := 0
            }
            let s3 : MirState := {
              locals := updateLocal s2.locals 0 (some (.usize 0))
              mem := mem
              block := 3
              stmtIdx := 1
            }
            let s4 : MirState := {
              locals := s3.locals
              mem := mem
              block := 4
              stmtIdx := 0
            }
            have hstep0 : evalMirStep (constBoundedAddBody N) s0 = .step () s1 := by
              change (match evalOperand locals (.copy ⟨1⟩) with
                | none => StepResult.failed .ub
                | some (v1, locals1) =>
                  match evalOperand locals1 (.constVal (.usize 1000)) with
                  | none => StepResult.failed .ub
                  | some (v2, locals2) =>
                    match evalBinOp .le v1 v2 with
                    | some res => StepResult.step () ({ locals := updateLocal locals2 2 (some res), mem := mem, block := 0, stmtIdx := 1 } : MirState)
                    | none => StepResult.failed .ub) = .step () s1
              dsimp [evalOperand]
              rw [hx0]
              dsimp [evalBinOp]
              rw [hbranch]
            have hstep1 : evalMirStep (constBoundedAddBody N) s1 = .step () s2 := rfl
            have hstep2 : evalMirStep (constBoundedAddBody N) s2 = .step () s3 := rfl
            have hstep3 : evalMirStep (constBoundedAddBody N) s3 = .step () s4 := rfl
            have hstep4 : evalMirStep (constBoundedAddBody N) s4 = .terminated (.normal (.usize 0)) := rfl
            rw [hout]
            cases steps with
            | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
            | succ n1 =>
              rw [evalMirFuel_step hstep0]
              cases n1 with
              | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
              | succ n2 =>
                rw [evalMirFuel_step hstep1]
                cases n2 with
                | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                | succ n3 =>
                  rw [evalMirFuel_step hstep2]
                  cases n3 with
                  | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                  | succ n4 =>
                    rw [evalMirFuel_step hstep3]
                    cases n4 with
                    | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                    | succ n5 =>
                      rw [evalMirFuel_terminated hstep4]
                      refine ⟨True.intro, ?_⟩
                      intro ret x0' hterm hx0'
                      injection hterm with hnorm
                      injection hnorm with hret
                      dsimp at hx0'
                      rw [hx0] at hx0'
                      injection hx0' with hval
                      injection hval with hx_eq
                      subst hx_eq
                      rw [hbranch]
                      exact hret.symm
          | true =>
            -- Branch `x0 ≤ 1000`: since `N ≤ 1000` (from PME!), `x0 + N ≤ 2000 ≤ usizeMax`.
            have hx0_le : x0 ≤ 1000 := of_decide_eq_true hbranch
            have hsum_le : x0 + N ≤ 2000 := Nat.add_le_add hx0_le hN
            have h2000_le : 2000 ≤ usizeMax := by decide
            have h_no_ov : ¬ (usizeMax < x0 + N) :=
              Nat.not_lt_of_ge (Nat.le_trans hsum_le h2000_le)
            have hov_false : decide (usizeMax < x0 + N) = false :=
              decide_eq_false h_no_ov
            let s1 : MirState := {
              locals := updateLocal locals 2 (some (.bool true))
              mem := mem
              block := 0
              stmtIdx := 1
            }
            let s2 : MirState := {
              locals := updateLocal s1.locals 2 none
              mem := mem
              block := 1
              stmtIdx := 0
            }
            let s3 : MirState := {
              locals := updateLocal s2.locals 3 (some (.tupleUsizeBool (x0 + N) false))
              mem := mem
              block := 1
              stmtIdx := 1
            }
            let s4 : MirState := {
              locals := s3.locals
              mem := mem
              block := 2
              stmtIdx := 0
            }
            let s5 : MirState := {
              locals := updateLocal s4.locals 0 (some (.usize (x0 + N)))
              mem := mem
              block := 2
              stmtIdx := 1
            }
            let s6 : MirState := {
              locals := s5.locals
              mem := mem
              block := 4
              stmtIdx := 0
            }
            have hstep0 : evalMirStep (constBoundedAddBody N) s0 = .step () s1 := by
              change (match evalOperand locals (.copy ⟨1⟩) with
                | none => StepResult.failed .ub
                | some (v1, locals1) =>
                  match evalOperand locals1 (.constVal (.usize 1000)) with
                  | none => StepResult.failed .ub
                  | some (v2, locals2) =>
                    match evalBinOp .le v1 v2 with
                    | some res => StepResult.step () ({ locals := updateLocal locals2 2 (some res), mem := mem, block := 0, stmtIdx := 1 } : MirState)
                    | none => StepResult.failed .ub) = .step () s1
              dsimp [evalOperand]
              rw [hx0]
              dsimp [evalBinOp]
              rw [hbranch]
            have hstep1 : evalMirStep (constBoundedAddBody N) s1 = .step () s2 := rfl
            have hstep2 : evalMirStep (constBoundedAddBody N) s2 = .step () s3 := by
              change (match evalOperand s2.locals (.copy ⟨1⟩) with
                | none => StepResult.failed .ub
                | some (v1, locals1) =>
                  match evalOperand locals1 (.constVal (.usize N)) with
                  | none => StepResult.failed .ub
                  | some (v2, locals2) =>
                    match evalCheckedBinOp .add v1 v2 with
                    | some res => StepResult.step () ({ locals := updateLocal locals2 3 (some res), mem := mem, block := 1, stmtIdx := 1 } : MirState)
                    | none => StepResult.failed .ub) = .step () s3
              dsimp [evalOperand, s2, s1, updateLocal]
              rw [hx0]
              dsimp [evalCheckedBinOp]
              rw [hov_false]
            have hstep3 : evalMirStep (constBoundedAddBody N) s3 = .step () s4 := rfl
            have hstep4 : evalMirStep (constBoundedAddBody N) s4 = .step () s5 := rfl
            have hstep5 : evalMirStep (constBoundedAddBody N) s5 = .step () s6 := rfl
            have hstep6 : evalMirStep (constBoundedAddBody N) s6 = .terminated (.normal (.usize (x0 + N))) := rfl
            rw [hout]
            cases steps with
            | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
            | succ n1 =>
              rw [evalMirFuel_step hstep0]
              cases n1 with
              | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
              | succ n2 =>
                rw [evalMirFuel_step hstep1]
                cases n2 with
                | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                | succ n3 =>
                  rw [evalMirFuel_step hstep2]
                  cases n3 with
                  | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                  | succ n4 =>
                    rw [evalMirFuel_step hstep3]
                    cases n4 with
                    | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                    | succ n5 =>
                      rw [evalMirFuel_step hstep4]
                      cases n5 with
                      | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                      | succ n6 =>
                        rw [evalMirFuel_step hstep5]
                        cases n6 with
                        | zero => exact ⟨True.intro, fun _ _ h => by cases h⟩
                        | succ n7 =>
                          rw [evalMirFuel_terminated hstep6]
                          refine ⟨True.intro, ?_⟩
                          intro ret x0' hterm hx0'
                          injection hterm with hnorm
                          injection hnorm with hret
                          dsimp at hx0'
                          rw [hx0] at hx0'
                          injection hx0' with hval
                          injection hval with hx_eq
                          subst hx_eq
                          rw [hbranch]
                          exact hret.symm

/-- Theorem 1b (Approach 2): For ALL `N : Nat`, `constBoundedAddBody N` refines
    `EnsuresConstBoundedAdd N` in `MirSemAdmitted`. -/
theorem constBoundedAdd_verified_approach2 (N : Nat) :
    MirSemAdmitted (constBoundedAddBody N) ≤ EnsuresConstBoundedAdd N :=
  (mirSemAdmitted_le_iff (constBoundedAddBody N) (EnsuresConstBoundedAdd N)).mpr
    (constBoundedAdd_source_verified N)

/-- Theorem 1b (Approach 1): For ALL `N : Nat`, `constBoundedAddBody N`
    satisfies `RustcPartialCompiler.Verified` given `TCBItem.rustcLowering`. -/
theorem constBoundedAdd_verified_approach1 (N : Nat)
    (h_sound : RustcPartialCompiler.SoundOn (constBoundedAddBody N)) :
    RustcPartialCompiler.Verified (constBoundedAddBody N) (EnsuresConstBoundedAdd N) :=
  approach1_verified_of_approach2 h_sound (constBoundedAdd_verified_approach2 N)

/-- Theorem 1b (Full Parametric Domain Characterization): `const_bounded_add`
    satisfies `GenericVerifiedWithDomain` with compile-time domain `N ≤ 1000`
    witnessed at `N = 500`. -/
theorem constBoundedAdd_generic_verified_with_domain :
    GenericVerifiedWithDomain constBoundedAddBody (fun N => N ≤ 1000) EnsuresConstBoundedAdd :=
  ⟨constBoundedAdd_verified_approach2,
   constBoundedAdd_compileAdmitted_iff,
   ⟨500, by decide⟩⟩

/-- Theorem 1c (Negative Control — Invalid Concrete Instantiation `N = 2000`):
    `constBoundedAddBody 2000` is rejected by `CompileAdmitted` and
    `ConcreteVerifiedAndAdmitted`. -/
theorem constBoundedAdd_2000_not_compileAdmitted :
    ¬ (constBoundedAddBody 2000).CompileAdmitted := by
  intro hAdm
  have hLe : 2000 ≤ 1000 := (constBoundedAdd_compileAdmitted_iff 2000).mp hAdm
  exact (by decide : ¬ (2000 ≤ 1000)) hLe

/-- Theorem 1c (Negative Control — Unguarded Runtime Overflow at `N = usizeMax`):
    Without the PME compile-time gate, executing `constBoundedAddBody usizeMax`
    at `x = 1` triggers an arithmetic overflow failure at runtime, refuting
    unguarded `MirSem (constBoundedAddBody usizeMax) ≤ MirLang.WellFormed`. -/
theorem constBoundedAdd_usizeMax_unguarded_runtime_fails :
    ¬ (MirSem (constBoundedAddBody usizeMax) ≤ MirLang.WellFormed) := by
  intro hWF
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 1))
  let s0 : MirState := {
    locals := locals0
    mem := MemState.empty
    block := 0
    stmtIdx := 0
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step h => cases h
      | succ m => rfl
  have hinit : initMirState (constBoundedAddBody usizeMax) s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨.usize 1, rfl, True.intro⟩, hrest⟩⟩
  let s1 : MirState := { s0 with
    locals := updateLocal locals0 2 (some (.bool true))
    stmtIdx := 1
  }
  let s2 : MirState := { s1 with
    locals := updateLocal s1.locals 2 none
    block := 1
    stmtIdx := 0
  }
  let s3 : MirState := { s2 with
    locals := updateLocal s2.locals 3 (some (.tupleUsizeBool (1 + usizeMax) true))
    stmtIdx := 1
  }
  have hr4 : ReachesPrefix MirMachine (constBoundedAddBody usizeMax) s0 4 s0 [(), (), ()] (.failed .contractViolation) :=
    ReachesPrefix.step 3 s0 s1 () [(), ()] (.failed .contractViolation) rfl
      (ReachesPrefix.step 2 s1 s2 () [()] (.failed .contractViolation) rfl
        (ReachesPrefix.step 1 s2 s3 () [] (.failed .contractViolation) rfl
          (ReachesPrefix.failed 0 s3 .contractViolation rfl)))
  have hdef := (hWF { init := s0, steps := 4 } True.intro).1
  exact hdef hinit [(), (), ()] (.failed .contractViolation) hr4

/-!
### 5.2 Case Study 2: `zerocopy`-style `transmute_ref<Src, Dst>(src: &Src) -> &Dst`

```rust
pub fn transmute_ref<Src, Dst>(src: &Src) -> &Dst {
    const { assert!(size_of::<Src>() == size_of::<Dst>()) };
    const { assert!(align_of::<Src>() % align_of::<Dst>() == 0) };
    unsafe { &*(src as *const Src as *const Dst) }
}
```
-/

/-- `transmute_ref::{constant#0}`: `const { assert!(size_of::<Src>() == size_of::<Dst>()) }`. -/
def transmuteRefConstSize (src dst : TyLayout) : ConstMirBody where
  localCount := 2
  blocks := [
    { stmts := [
        .assign ⟨1⟩ (.binaryOp .eq (.constVal (.usize src.size)) (.constVal (.usize dst.size)))
      ]
      terminator := .switchInt (.move ⟨1⟩) ⟨1⟩ ⟨2⟩ },
    { stmts := []
      terminator := .panic },
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal .unit))
      ]
      terminator := .return_ }
  ]

/-- `transmute_ref::{constant#1}`: `const { assert!(align_of::<Src>() % align_of::<Dst>() == 0) }`
    (for power-of-two alignments, equivalent to `align_of::<Dst>() <= align_of::<Src>()`,
    Directly expressing `dst.align ∣ src.align`). -/
def transmuteRefConstAlign (src dst : TyLayout) : ConstMirBody where
  localCount := 3
  blocks := [
    { stmts := [
        .assign ⟨1⟩ (.binaryOp .rem (.constVal (.usize src.align)) (.constVal (.usize dst.align))),
        .assign ⟨2⟩ (.binaryOp .eq (.move ⟨1⟩) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨1⟩ ⟨2⟩ },
    { stmts := []
      terminator := .panic },
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal .unit))
      ]
      terminator := .return_ }
  ]

/-- Lowered `Runtime(PostCleanup)` MIR body for `transmute_ref<Src, Dst>`:
    ```text
    bb0: {
        _3 = &raw const (*_1);
        _2 = copy _3 as *const Dst (PtrToPtr);
        _0 = &(*_2);
        return;
    }
    ```
    with `requiredConsts := [transmuteRefConstSize src dst, transmuteRefConstAlign src dst]`
    and `requiredLayouts := [src, dst]`. -/
def transmuteRefBody (src dst : TyLayout) : MirBody where
  argTys := [.refShared src]
  retTy := .refShared dst
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.addrOfDeref ⟨1⟩),
        .assign ⟨2⟩ (.castPtrToPtr ⟨3⟩ dst),
        .assign ⟨0⟩ (.reborrowShared ⟨2⟩ dst)
      ]
      terminator := .return_ }
  ]
  requiredConsts := [transmuteRefConstSize src dst, transmuteRefConstAlign src dst]
  requiredLayouts := [src, dst]

/-- Specification for `transmute_ref<Src, Dst>`:
    - `defined := True`: safe function (`pre := fun _ => True`)—every finite
      prefix is free of UB!
    - `val`: for any valid input reference `_1 = .refLoc loc addr src`, returns
      a valid `&Dst` reference `.refLoc loc addr dst` to the same allocation and
      address (`refValidIn q.init.mem loc addr dst`). -/
def EnsuresTransmuteRef (src dst : TyLayout) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret loc addr,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.refLoc loc addr src) →
      ret = .refLoc loc addr dst ∧ refValidIn q.init.mem loc addr dst)

theorem transmuteRefConstSize_ctfe_iff (src dst : TyLayout) :
    CtfeAdmitted (transmuteRefConstSize src dst) ↔ src.size = dst.size := by
  constructor
  · intro ⟨hSafe, _⟩
    cases hdec : decide (src.size = dst.size) with
    | true => exact of_decide_eq_true hdec
    | false =>
      let s1 : MirState := {
        locals := updateLocal initCtfeState.locals 1 (some (.bool false))
        mem := MemState.empty
        block := 0
        stmtIdx := 1
      }
      let s2 : MirState := {
        locals := updateLocal s1.locals 1 none
        mem := MemState.empty
        block := 1
        stmtIdx := 0
      }
      have hstep0 : evalBlocksStep (transmuteRefConstSize src dst).blocks initCtfeState = .step () s1 := by
        change StepResult.step () {
          locals := updateLocal initCtfeState.locals 1 (some (.bool (decide (src.size = dst.size))))
          mem := MemState.empty
          block := 0
          stmtIdx := 1
        } = .step () s1
        rw [hdec]
      have hstep1 : evalBlocksStep (transmuteRefConstSize src dst).blocks s1 = .step () s2 := rfl
      have hstep2 : evalBlocksStep (transmuteRefConstSize src dst).blocks s2 = .failed .contractViolation := rfl
      have hr3 : ReachesPrefix ConstMirMachine (transmuteRefConstSize src dst) initCtfeState 3 initCtfeState [(), ()] (.failed .contractViolation) :=
        ReachesPrefix.step 2 initCtfeState s1 () [()] (.failed .contractViolation) hstep0.symm
          (ReachesPrefix.step 1 s1 s2 () [] (.failed .contractViolation) hstep1.symm
            (ReachesPrefix.failed 0 s2 .contractViolation hstep2.symm))
      exact False.elim (hSafe 3 [(), ()] (.failed .contractViolation) hr3)
  · intro hEq
    have hdec : decide (src.size = dst.size) = true := decide_eq_true hEq
    let s1 : MirState := {
      locals := updateLocal initCtfeState.locals 1 (some (.bool true))
      mem := MemState.empty
      block := 0
      stmtIdx := 1
    }
    let s2 : MirState := {
      locals := updateLocal s1.locals 1 none
      mem := MemState.empty
      block := 2
      stmtIdx := 0
    }
    let s3 : MirState := {
      locals := updateLocal s2.locals 0 (some .unit)
      mem := MemState.empty
      block := 2
      stmtIdx := 1
    }
    have hstep0 : evalBlocksStep (transmuteRefConstSize src dst).blocks initCtfeState = .step () s1 := by
      change StepResult.step () {
        locals := updateLocal initCtfeState.locals 1 (some (.bool (decide (src.size = dst.size))))
        mem := MemState.empty
        block := 0
        stmtIdx := 1
      } = .step () s1
      rw [hdec]
    have hstep1 : evalBlocksStep (transmuteRefConstSize src dst).blocks s1 = .step () s2 := rfl
    have hstep2 : evalBlocksStep (transmuteRefConstSize src dst).blocks s2 = .step () s3 := rfl
    have hstep3 : evalBlocksStep (transmuteRefConstSize src dst).blocks s3 = .terminated (.normal .unit) := rfl
    refine ⟨?_, ?_⟩
    · intro steps tr out hreach
      have hout := reachesPrefix_constMirMachine_eq_evalCtfeFuel
        (transmuteRefConstSize src dst) initCtfeState steps initCtfeState tr out hreach
      subst hout
      cases steps with
      | zero => exact True.intro
      | succ n1 =>
        rw [evalCtfeFuel_step hstep0]
        cases n1 with
        | zero => exact True.intro
        | succ n2 =>
          rw [evalCtfeFuel_step hstep1]
          cases n2 with
          | zero => exact True.intro
          | succ n3 =>
            rw [evalCtfeFuel_step hstep2]
            cases n3 with
            | zero => exact True.intro
            | succ n4 =>
              rw [evalCtfeFuel_terminated hstep3]
              exact True.intro
    · refine ⟨4, [(), (), ()], ?_⟩
      exact ReachesPrefix.step 3 initCtfeState s1 () [(), ()] (.terminated (.normal MirVal.unit)) hstep0.symm
        (ReachesPrefix.step 2 s1 s2 () [()] (.terminated (.normal MirVal.unit)) hstep1.symm
          (ReachesPrefix.step 1 s2 s3 () [] (.terminated (.normal MirVal.unit)) hstep2.symm
            (ReachesPrefix.terminated 0 s3 (.normal MirVal.unit) hstep3.symm)))

theorem transmuteRefConstAlign_ctfe_iff (src dst : TyLayout) :
    CtfeAdmitted (transmuteRefConstAlign src dst) ↔ dst.align ∣ src.align := by
  rw [Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro ⟨hSafe, _⟩
    cases hdec : decide (src.align % dst.align = 0) with
    | true => exact of_decide_eq_true hdec
    | false =>
      let s1 : MirState := {
        locals := updateLocal initCtfeState.locals 1 (some (.usize (src.align % dst.align)))
        mem := MemState.empty
        block := 0
        stmtIdx := 1
      }
      let s2 : MirState := {
        locals := updateLocal (updateLocal s1.locals 1 none) 2 (some (.bool false))
        mem := MemState.empty
        block := 0
        stmtIdx := 2
      }
      let s3 : MirState := {
        locals := updateLocal s2.locals 2 none
        mem := MemState.empty
        block := 1
        stmtIdx := 0
      }
      have hstep0 : evalBlocksStep (transmuteRefConstAlign src dst).blocks initCtfeState = .step () s1 := rfl
      have hstep1 : evalBlocksStep (transmuteRefConstAlign src dst).blocks s1 = .step () s2 := by
        change StepResult.step () {
          locals := updateLocal (updateLocal s1.locals 1 none) 2 (some (.bool (decide (src.align % dst.align = 0))))
          mem := MemState.empty
          block := 0
          stmtIdx := 2
        } = .step () s2
        rw [hdec]
      have hstep2 : evalBlocksStep (transmuteRefConstAlign src dst).blocks s2 = .step () s3 := rfl
      have hstep3 : evalBlocksStep (transmuteRefConstAlign src dst).blocks s3 = .failed .contractViolation := rfl
      have hr4 : ReachesPrefix ConstMirMachine (transmuteRefConstAlign src dst) initCtfeState 4 initCtfeState [(), (), ()] (.failed .contractViolation) :=
        ReachesPrefix.step 3 initCtfeState s1 () [(), ()] (.failed .contractViolation) hstep0.symm
          (ReachesPrefix.step 2 s1 s2 () [()] (.failed .contractViolation) hstep1.symm
            (ReachesPrefix.step 1 s2 s3 () [] (.failed .contractViolation) hstep2.symm
              (ReachesPrefix.failed 0 s3 .contractViolation hstep3.symm)))
      exact False.elim (hSafe 4 [(), (), ()] (.failed .contractViolation) hr4)
  · intro hMod
    have hdec : decide (src.align % dst.align = 0) = true := decide_eq_true hMod
    let s1 : MirState := {
      locals := updateLocal initCtfeState.locals 1 (some (.usize (src.align % dst.align)))
      mem := MemState.empty
      block := 0
      stmtIdx := 1
    }
    let s2 : MirState := {
      locals := updateLocal (updateLocal s1.locals 1 none) 2 (some (.bool true))
      mem := MemState.empty
      block := 0
      stmtIdx := 2
    }
    let s3 : MirState := {
      locals := updateLocal s2.locals 2 none
      mem := MemState.empty
      block := 2
      stmtIdx := 0
    }
    let s4 : MirState := {
      locals := updateLocal s3.locals 0 (some .unit)
      mem := MemState.empty
      block := 2
      stmtIdx := 1
    }
    have hstep0 : evalBlocksStep (transmuteRefConstAlign src dst).blocks initCtfeState = .step () s1 := rfl
    have hstep1 : evalBlocksStep (transmuteRefConstAlign src dst).blocks s1 = .step () s2 := by
      change StepResult.step () {
        locals := updateLocal (updateLocal s1.locals 1 none) 2 (some (.bool (decide (src.align % dst.align = 0))))
        mem := MemState.empty
        block := 0
        stmtIdx := 2
      } = .step () s2
      rw [hdec]
    have hstep2 : evalBlocksStep (transmuteRefConstAlign src dst).blocks s2 = .step () s3 := rfl
    have hstep3 : evalBlocksStep (transmuteRefConstAlign src dst).blocks s3 = .step () s4 := rfl
    have hstep4 : evalBlocksStep (transmuteRefConstAlign src dst).blocks s4 = .terminated (.normal .unit) := rfl
    refine ⟨?_, ?_⟩
    · intro steps tr out hreach
      have hout := reachesPrefix_constMirMachine_eq_evalCtfeFuel
        (transmuteRefConstAlign src dst) initCtfeState steps initCtfeState tr out hreach
      subst hout
      cases steps with
      | zero => exact True.intro
      | succ n1 =>
        rw [evalCtfeFuel_step hstep0]
        cases n1 with
        | zero => exact True.intro
        | succ n2 =>
          rw [evalCtfeFuel_step hstep1]
          cases n2 with
          | zero => exact True.intro
          | succ n3 =>
            rw [evalCtfeFuel_step hstep2]
            cases n3 with
            | zero => exact True.intro
            | succ n4 =>
              rw [evalCtfeFuel_step hstep3]
              cases n4 with
              | zero => exact True.intro
              | succ n5 =>
                rw [evalCtfeFuel_terminated hstep4]
                exact True.intro
    · refine ⟨5, [(), (), (), ()], ?_⟩
      exact ReachesPrefix.step 4 initCtfeState s1 () [(), (), ()] (.terminated (.normal MirVal.unit)) hstep0.symm
        (ReachesPrefix.step 3 s1 s2 () [(), ()] (.terminated (.normal MirVal.unit)) hstep1.symm
          (ReachesPrefix.step 2 s2 s3 () [()] (.terminated (.normal MirVal.unit)) hstep2.symm
            (ReachesPrefix.step 1 s3 s4 () [] (.terminated (.normal MirVal.unit)) hstep3.symm
              (ReachesPrefix.terminated 0 s4 (.normal MirVal.unit) hstep4.symm))))

/-- Theorem 2a: `transmuteRefBody src dst` is compile-time admissible if and
    only if `src.size = dst.size`, `dst.align ∣ src.align`, and both layouts are
    well-formed. -/
theorem transmuteRef_compileAdmitted_iff (src dst : TyLayout) :
    (transmuteRefBody src dst).CompileAdmitted ↔
      (src.size = dst.size ∧ dst.align ∣ src.align ∧ src.WellFormed ∧ dst.WellFormed) := by
  unfold MirBody.CompileAdmitted transmuteRefBody AllHold
  dsimp [List.map, List.foldr]
  rw [transmuteRefConstSize_ctfe_iff, transmuteRefConstAlign_ctfe_iff]
  constructor
  · intro ⟨⟨hSz, hAl, _⟩, hSrcWf, hDstWf, _⟩
    exact ⟨hSz, hAl, hSrcWf, hDstWf⟩
  · intro ⟨hSz, hAl, hSrcWf, hDstWf⟩
    exact ⟨⟨hSz, hAl, True.intro⟩, hSrcWf, hDstWf, True.intro⟩

/-- Source conditional correctness of `transmuteRefBody src dst`: when
    `CompileAdmitted` holds, the PME guarantees `src.size = dst.size`,
    `dst.align ∣ src.align`, and `0 < dst.align`, so every valid input `&Src`
    reference is also aligned and in-bounds for `&Dst`, ensuring the unsafe
    reborrow `&*(_2 as *const Dst)` never triggers UB! -/
theorem transmuteRef_source_verified (src dst : TyLayout) :
    (transmuteRefBody src dst).CompileAdmitted →
      MirSem (transmuteRefBody src dst) ≤ EnsuresTransmuteRef src dst := by
  intro hAdm
  have ⟨hSizeEq, hAlignDvd, _, hDstWf⟩ :=
    (transmuteRef_compileAdmitted_iff src dst).mp hAdm
  refine behaviorOf_le_pure (M := MirMachine) ?_
  intro q out ⟨hinit, hreach⟩
  cases q with
  | mk init steps =>
    cases init with
    | mk locals mem block stmtIdx =>
      have hb : block = 0 := hinit.1
      have hs : stmtIdx = 0 := hinit.2.1
      subst hb hs
      have harg : ∃ v, locals 1 = some v ∧ v.hasTy mem (.refShared src) :=
        hinit.2.2.2.1
      cases harg with
      | intro v hv =>
        cases v with
        | usize _ | bool _ | unit | tupleUsizeBool _ _ | ptrLoc _ _ _ =>
          cases hv.2
        | refLoc loc addr ly =>
          have hly : ly = src := hv.2.1
          subst ly
          have hSrcValid : refValidIn mem loc addr src := hv.2.2
          have hNonNull : addr ≠ 0 := hSrcValid.1
          have hSrcAlignDvd : src.align ∣ addr := hSrcValid.2.2.1
          have hSrcSizeBound : src.size ≤ mem.allocSize loc := hSrcValid.2.2.2
          -- Key PME bridge: transfer alignment and size validity from `src` to `dst`!
          have hDstAlignPos : 0 < dst.align := hDstWf.1
          have hDstAlignDvd : dst.align ∣ addr := Nat.dvd_trans hAlignDvd hSrcAlignDvd
          have hDstSizeBound : dst.size ≤ mem.allocSize loc := by
            rw [← hSizeEq]
            exact hSrcSizeBound
          have hDstValid : refValidIn mem loc addr dst :=
            ⟨hNonNull, hDstAlignPos, hDstAlignDvd, hDstSizeBound⟩
          have href1 : locals 1 = some (.refLoc loc addr src) := hv.1
          let s0 : MirState := { locals := locals, mem := mem, block := 0, stmtIdx := 0 }
          let s1 : MirState := {
            locals := updateLocal locals 3 (some (.ptrLoc loc addr src))
            mem := mem
            block := 0
            stmtIdx := 1
          }
          let s2 : MirState := {
            locals := updateLocal s1.locals 2 (some (.ptrLoc loc addr dst))
            mem := mem
            block := 0
            stmtIdx := 2
          }
          let s3 : MirState := {
            locals := updateLocal s2.locals 0 (some (.refLoc loc addr dst))
            mem := mem
            block := 0
            stmtIdx := 3
          }
          have hstep0 : evalMirStep (transmuteRefBody src dst) s0 = .step () s1 := by
            change (match locals 1 with
              | some (.refLoc loc addr ly) =>
                StepResult.step () ({ locals := updateLocal locals 3 (some (.ptrLoc loc addr ly)), mem := mem, block := 0, stmtIdx := 1 } : MirState)
              | _ => StepResult.failed .ub) = .step () s1
            rw [href1]
          have hstep1 : evalMirStep (transmuteRefBody src dst) s1 = .step () s2 := rfl
          have hstep2 : evalMirStep (transmuteRefBody src dst) s2 = .step () s3 := by
            change (if (decide (dst = dst) && decide (addr ≠ 0) && decide (0 < dst.align) &&
                  decide (dst.align ∣ addr) && decide (dst.size ≤ mem.allocSize loc)) = true then
                StepResult.step () s3
              else StepResult.failed .ub) = .step () s3
            have hd1 : decide (dst = dst) = true := decide_eq_true rfl
            have hd2 : decide (addr ≠ 0) = true := decide_eq_true hNonNull
            have hd3 : decide (0 < dst.align) = true := decide_eq_true hDstAlignPos
            have hd4 : decide (dst.align ∣ addr) = true := decide_eq_true hDstAlignDvd
            have hd5 : decide (dst.size ≤ mem.allocSize loc) = true :=
              decide_eq_true hDstSizeBound
            rw [hd1, hd2, hd3, hd4, hd5]
            rfl
          have hstep3 : evalMirStep (transmuteRefBody src dst) s3 =
              .terminated (.normal (.refLoc loc addr dst)) := rfl
          have hout := reachesPrefix_mirMachine_eq_evalMirFuel
            (transmuteRefBody src dst) s0 steps s0 out.trace out.outcome hreach
          rw [hout]
          cases steps with
          | zero => exact ⟨True.intro, fun _ _ _ h => by cases h⟩
          | succ n1 =>
            rw [evalMirFuel_step hstep0]
            cases n1 with
            | zero => exact ⟨True.intro, fun _ _ _ h => by cases h⟩
            | succ n2 =>
              rw [evalMirFuel_step hstep1]
              cases n2 with
              | zero => exact ⟨True.intro, fun _ _ _ h => by cases h⟩
              | succ n3 =>
                rw [evalMirFuel_step hstep2]
                cases n3 with
                | zero => exact ⟨True.intro, fun _ _ _ h => by cases h⟩
                | succ n4 =>
                  rw [evalMirFuel_terminated hstep3]
                  refine ⟨True.intro, ?_⟩
                  intro ret loc' addr' hterm href1'
                  injection hterm with hnorm
                  injection hnorm with hret
                  dsimp at href1'
                  rw [href1] at href1'
                  injection href1' with hval
                  injection hval with hloc haddr _
                  subst hloc haddr
                  exact ⟨hret.symm, hDstValid⟩

/-- Theorem 2b (Approach 2): For ALL `src dst : TyLayout` with safe caller
    precondition `pre := True`, `transmuteRefBody src dst` refines
    `EnsuresTransmuteRef src dst` in `MirSemAdmitted`. -/
theorem transmuteRef_verified_approach2 (src dst : TyLayout) :
    MirSemAdmitted (transmuteRefBody src dst) ≤ EnsuresTransmuteRef src dst :=
  (mirSemAdmitted_le_iff (transmuteRefBody src dst) (EnsuresTransmuteRef src dst)).mpr
    (transmuteRef_source_verified src dst)

/-- Theorem 2b (Approach 1): For ALL `src dst : TyLayout` with safe caller
    precondition `pre := True`, `transmuteRefBody src dst` satisfies
    `RustcPartialCompiler.Verified` given `TCBItem.rustcLowering`. -/
theorem transmuteRef_verified_approach1 (src dst : TyLayout)
    (h_sound : RustcPartialCompiler.SoundOn (transmuteRefBody src dst)) :
    RustcPartialCompiler.Verified (transmuteRefBody src dst) (EnsuresTransmuteRef src dst) :=
  approach1_verified_of_approach2 h_sound (transmuteRef_verified_approach2 src dst)

/-!
### 5.3 Negative Controls (`transmute_ref` Without PME, Dead-Branch PME, and Always-Failing `const`)
-/

/-- Negative Control 1 (`transmuteRefNoPmeBody`): `transmute_ref` with the PME
    omitted (`requiredConsts := []`). -/
def transmuteRefNoPmeBody (src dst : TyLayout) : MirBody :=
  { transmuteRefBody src dst with requiredConsts := [] }

/-- Theorem 2c: When the PME is omitted (`requiredConsts := []`),
    `transmuteRefNoPmeBody u8Layout u64Layout` is compile-time admissible, yet
    triggers immediate Undefined Behavior at runtime when called on a 1-byte
    aligned `&u8`, refuting `MirSemAdmitted ... ≤ MirLang.WellFormed`! -/
theorem negative_control_omitted_pme_rejected :
    (transmuteRefNoPmeBody u8Layout u64Layout).CompileAdmitted ∧
    ¬ (MirSemAdmitted (transmuteRefNoPmeBody u8Layout u64Layout) ≤ MirLang.WellFormed) := by
  have hU8Wf : u8Layout.WellFormed := ⟨by decide, by decide, Nat.dvd_refl 1⟩
  have hU64Wf : u64Layout.WellFormed := ⟨by decide, by decide, Nat.dvd_refl 8⟩
  have hAdm : (transmuteRefNoPmeBody u8Layout u64Layout).CompileAdmitted :=
    ⟨True.intro, hU8Wf, hU64Wf, True.intro⟩
  refine ⟨hAdm, ?_⟩
  intro hWF
  have hSrcWF := (mirSemAdmitted_le_iff
    (transmuteRefNoPmeBody u8Layout u64Layout) MirLang.WellFormed).mp hWF hAdm
  let mem0 : MemState := { allocSize := fun _ => 1 }
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.refLoc 0 1 u8Layout))
  let s0 : MirState := {
    locals := locals0
    mem := mem0
    block := 0
    stmtIdx := 0
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step h => cases h
      | succ m => rfl
  have hRefValid : refValidIn mem0 0 1 u8Layout :=
    ⟨by decide, by decide, Nat.dvd_refl 1, by decide⟩
  have hinit : initMirState (transmuteRefNoPmeBody u8Layout u64Layout) s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨.refLoc 0 1 u8Layout, rfl, rfl, hRefValid⟩, hrest⟩⟩
  let s1 : MirState := { s0 with
    locals := updateLocal locals0 3 (some (.ptrLoc 0 1 u8Layout))
    stmtIdx := 1
  }
  let s2 : MirState := { s1 with
    locals := updateLocal s1.locals 2 (some (.ptrLoc 0 1 u64Layout))
    stmtIdx := 2
  }
  have hr3 : ReachesPrefix MirMachine (transmuteRefNoPmeBody u8Layout u64Layout) s0 3 s0 [(), ()] (.failed .ub) :=
    ReachesPrefix.step 2 s0 s1 () [()] (.failed .ub) rfl
      (ReachesPrefix.step 1 s1 s2 () [] (.failed .ub) rfl
        (ReachesPrefix.failed 0 s2 .ub rfl))
  have hdef := (hSrcWF { init := s0, steps := 3 } True.intro).1
  exact hdef hinit [(), ()] (.failed .ub) hr3

/-- Negative Control 2 (`transmuteRefDeadBranchBody`): an attempt to guard
    `transmute_ref` with a runtime assertion inside a dead branch (`if false`)
    instead of a compile-time `requiredConsts` PME. -/
def transmuteRefDeadBranchBody (src dst : TyLayout) : MirBody where
  argTys := [.refShared src]
  retTy := .refShared dst
  localCount := 4
  blocks := [
    -- bb0: `if false` jumps to `bb1` (live unsafe reborrow), skipping `bb2` (dead check)
    { stmts := []
      terminator := .switchInt (.constVal (.bool false)) ⟨1⟩ ⟨2⟩ },
    -- bb1: unsafe reborrow `&*(_2 as *const Dst)`
    { stmts := [
        .assign ⟨3⟩ (.addrOfDeref ⟨1⟩),
        .assign ⟨2⟩ (.castPtrToPtr ⟨3⟩ dst),
        .assign ⟨0⟩ (.reborrowShared ⟨2⟩ dst)
      ]
      terminator := .return_ },
    -- bb2: unreached dead assertion block
    { stmts := []
      terminator := .panic }
  ]
  requiredConsts := []
  requiredLayouts := [src, dst]

/-- Theorem 2d: Placing an assertion in an unreached runtime dead branch instead
    of `requiredConsts` fails verification (`¬ (MirSemAdmitted ... ≤
    MirLang.WellFormed)`). -/
theorem negative_control_dead_branch_assertion_rejected :
    ¬ (MirSemAdmitted (transmuteRefDeadBranchBody u8Layout u64Layout) ≤ MirLang.WellFormed) := by
  intro hWF
  have hU8Wf : u8Layout.WellFormed := ⟨by decide, by decide, Nat.dvd_refl 1⟩
  have hU64Wf : u64Layout.WellFormed := ⟨by decide, by decide, Nat.dvd_refl 8⟩
  have hAdm : (transmuteRefDeadBranchBody u8Layout u64Layout).CompileAdmitted :=
    ⟨True.intro, hU8Wf, hU64Wf, True.intro⟩
  have hSrcWF := (mirSemAdmitted_le_iff
    (transmuteRefDeadBranchBody u8Layout u64Layout) MirLang.WellFormed).mp hWF hAdm
  let mem0 : MemState := { allocSize := fun _ => 1 }
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.refLoc 0 1 u8Layout))
  let s0 : MirState := {
    locals := locals0
    mem := mem0
    block := 0
    stmtIdx := 0
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step h => cases h
      | succ m => rfl
  have hRefValid : refValidIn mem0 0 1 u8Layout :=
    ⟨by decide, by decide, Nat.dvd_refl 1, by decide⟩
  have hinit : initMirState (transmuteRefDeadBranchBody u8Layout u64Layout) s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨.refLoc 0 1 u8Layout, rfl, rfl, hRefValid⟩, hrest⟩⟩
  let s1 : MirState := { s0 with block := 1, stmtIdx := 0 }
  let s2 : MirState := { s1 with
    locals := updateLocal locals0 3 (some (.ptrLoc 0 1 u8Layout))
    stmtIdx := 1
  }
  let s3 : MirState := { s2 with
    locals := updateLocal s2.locals 2 (some (.ptrLoc 0 1 u64Layout))
    stmtIdx := 2
  }
  have hr4 : ReachesPrefix MirMachine (transmuteRefDeadBranchBody u8Layout u64Layout) s0 4 s0 [(), (), ()] (.failed .ub) :=
    ReachesPrefix.step 3 s0 s1 () [(), ()] (.failed .ub) rfl
      (ReachesPrefix.step 2 s1 s2 () [()] (.failed .ub) rfl
        (ReachesPrefix.step 1 s2 s3 () [] (.failed .ub) rfl
          (ReachesPrefix.failed 0 s3 .ub rfl)))
  have hdef := (hSrcWF { init := s0, steps := 4 } True.intro).1
  exact hdef hinit [(), (), ()] (.failed .ub) hr4

/-- Negative Control 3a (`brokenConstFalseBody`): `pub fn broken() { const { assert!(false) }; }`. -/
def brokenConstFalseBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ }
  ]
  requiredConsts := [
    { localCount := 1
      blocks := [{ stmts := [], terminator := .panic }] }
  ]

/-- Theorem 2e (Part 1): `pub fn broken() { const { assert!(false) }; }` fails
    `CompileAdmitted` and is rejected by `ConcreteVerifiedAndAdmitted`. -/
theorem negative_control_const_assert_false_not_admitted :
    ¬ brokenConstFalseBody.CompileAdmitted ∧
    ¬ ConcreteVerifiedAndAdmitted brokenConstFalseBody MirLang.WellFormed := by
  have hNotAdm : ¬ brokenConstFalseBody.CompileAdmitted := by
    intro hAdm
    have hSafe := hAdm.1.1.1
    have hr1 : ReachesPrefix ConstMirMachine
        { localCount := 1, blocks := [{ stmts := [], terminator := .panic }] }
        initCtfeState 1 initCtfeState [] (.failed .contractViolation) :=
      ReachesPrefix.failed 0 initCtfeState .contractViolation rfl
    exact hSafe 1 [] (.failed .contractViolation) hr1
  exact ⟨hNotAdm, fun h => hNotAdm h.1⟩

/-- Negative Control 3b (`brokenConstLoopBody`): `pub fn broken_loop() { const { loop {} }; }`. -/
def brokenConstLoopBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ }
  ]
  requiredConsts := [
    { localCount := 1
      blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }] }
  ]

theorem constLoop_evalCtfeFuel_running (n : Nat) :
    evalCtfeFuel { localCount := 1, blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }] }
      n initCtfeState = .running := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold evalCtfeFuel
    exact ih

/-- Theorem 2e (Part 2): `pub fn broken_loop() { const { loop {} }; }` fails
    `CompileAdmitted` because its CTFE constant never terminates. -/
theorem negative_control_const_loop_not_admitted :
    ¬ brokenConstLoopBody.CompileAdmitted := by
  intro hAdm
  cases hAdm.1.1.2 with
  | intro steps hrest =>
    cases hrest with
    | intro tr hreach =>
      have hout := reachesPrefix_constMirMachine_eq_evalCtfeFuel
        { localCount := 1, blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }] }
        initCtfeState steps initCtfeState tr (.terminated (.normal .unit)) hreach
      rw [constLoop_evalCtfeFuel_running steps] at hout
      cases hout

end PmeResearch
