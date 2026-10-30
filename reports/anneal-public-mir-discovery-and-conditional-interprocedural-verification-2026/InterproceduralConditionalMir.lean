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
# Call-Stack MIR, Transitive `CompileAdmitted`, and Dual-Mode Summaries

This standalone Lean 4.34.1 mechanization unifies three Round 1 findings into a
single interprocedural verification architecture for Anneal:

1. **Call-Stack Operational Semantics for `Terminator.call`
   (`Sections 3 & 4`):**
   Replaces the hardcoded `PureCallee2` enum in `Trusted/MirSemantics.lean` with
   a general `Terminator.call dst callee args target` resolved against a
   crate-level function table (`CrateEnv := List FnEntry`). `MirMachine`
   executes `Terminator.call` by pushing a caller continuation frame
   `CallFrame` (`callerBody`, `dst`, `returnTarget`, `callerLocals`) onto a call
   stack `frames : List CallFrame` in `MirState` and popping the top frame on
   `Terminator.return_`. We prove that this call-stack `MirMachine` preserves
   `TotalStep`, `InhabitedDemonic`, and `non_vacuity_at_every_depth`.
2. **Transitive `CompileAdmitted` Across `requiredConsts` and `mentionedItems`
   (`Section 5`):**
   Extends `MirBody` with `requiredConsts : List ConstMirBody` and
   `mentionedItems : List String`, and defines fuel-bounded transitive
   `CompileAdmitted` (along with an executable boolean checker
   `checkCompileAdmitted`) that verifies both `body.requiredConsts` via CTFE and
   every `callee ∈ body.mentionedItems`.
3. **Dual-Mode Interprocedural Symbolic Evaluation (`Sections 6 & 7`):**
   - **Mode A (Zero-Annotation Symbolic Call Inlining):** When `TransPlan` uses
     `.callInline calleePlan afterCall`, `evalSymState` looks up `callee` in
     `CrateEnv` and symbolically executes `callee` inline, returning a
     spine-preserving `Option (Bool × SymVal)` pair so caller and callee reduce
     together by kernel `rfl`. Private helpers (`isPublic := false`) require
     zero user-written specifications, preconditions, or summaries.
   - **Mode B (Modular Verified Callee Summaries):** When `TransPlan` uses
     `.callSummary afterCall`, `evalSymState` discharges the call in one step
     using a verified spine-preserving summary in `SummaryEnv`. Because
     `MirMachine` executes the actual callee body on the call stack, modular
     summaries live entirely outside the TCB in `theory/`.

Every declaration that models a `rustc` MIR construct or Rust execution rule
cites its normative source at the repository's pinned revisions
(`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).
-/

namespace AnnealR2WS2

/-!
## 1. Layer 1A: Refinement Preorder, `Partial`, `SpecOn`, and `when ⊣ given`
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

/-- Functorial map over the defined payload of `Partial`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- `Partial.bot` refines every partial outcome predicate `p`. -/
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

theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v}
    [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp hdef₂
  cases hp hdef₂ with
  | intro hdef₁ hle =>
    exact ⟨hdef₁, hf hle⟩

/-- Query-indexed partial behaviors over `Query` and `Out`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Left compile-time gate on a program behavior `b`: when `P` holds, behaves as
    `b`; when `¬ P` holds, collapses to `Partial.bot`. -/
def Behavior.when {Query Out : Type} (P : Prop)
    (b : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P → (b q).defined
    val := fun hdef out => ∃ hP : P, (b q).val (hdef hP) out
  }

/-- Right compile-time guard on a specification `spec`: requires `spec` only
    when `P` holds, collapsing to `Partial.ub` when `¬ P`. -/
def Behavior.given {Query Out : Type} (P : Prop)
    (spec : Behavior Query Out) : Behavior Query Out :=
  fun q => {
    defined := P ∧ (spec q).defined
    val := fun hdef out => (spec q).val hdef.2 out
  }

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

theorem behavior_le_given_iff {Query Out : Type} (P : Prop)
    (b spec : Behavior Query Out) :
    (P → b ≤ spec) ↔ b ≤ Behavior.given P spec := by
  constructor
  · intro h q ⟨hP, hs⟩
    exact h hP q hs
  · intro h hP q hs
    exact h q ⟨hP, hs⟩

/-- Galois connection (`Behavior.when P ⊣ Behavior.given P`), proved with zero
    axioms. -/
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
  AnnealR2WS2.Behavior L.Query L.Out

/-- Query-indexed specification with domain precondition `pre` and outcome
    postcondition `post`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification (`L.SpecOn (fun _ => True) post`). -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness (`L.SpecOn pre (fun _ _ => True)`). -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness (`L.WellFormedOn (fun _ => True)`). -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

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

theorem le_wellFormedOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) :
    b ≤ L.WellFormedOn pre ↔ ∀ q, pre q → (b q).defined := by
  constructor
  · intro h q hpre
    exact (h q hpre).1
  · intro h q hpre
    exact ⟨h q hpre, fun _ _ => True.intro⟩

theorem le_wellFormed_iff {L : Language} (b : L.Behavior) :
    b ≤ L.WellFormed ↔ ∀ q, (b q).defined := by
  constructor
  · intro h q
    exact (le_wellFormedOn_iff b (fun _ => True)).mp h q True.intro
  · intro h
    exact (le_wellFormedOn_iff b (fun _ => True)).mpr (fun q _ => h q)

theorem specOn_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

theorem spec_le_wellFormed {L : Language} (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ L.WellFormed :=
  specOn_le_wellFormedOn (fun _ => True) post

theorem not_le_spec_of_not_defined {L : Language} {b : L.Behavior}
    {q : L.Query} (hundef : ¬ (b q).defined)
    (post : L.Query → L.Out → Prop) :
    ¬ (b ≤ L.Spec post) :=
  fun hle => hundef (hle q True.intro).1

theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

theorem Compiler.Verified.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.Verified s spec₁)
    (h_le : spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.Verified s spec₂ :=
  ⟨Preorder.le_trans h_ver.1 h_le,
   h_ver.2.1,
   Preorder.le_trans h_ver.2.2 (h_mono h_le)⟩

theorem Compiler.Verified.with_wellFormedOn
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {pre : L_src.Query → Prop} {spec : L_src.Behavior}
    (h_ver : C.Verified s spec)
    (h_wf : spec ≤ L_src.WellFormedOn pre)
    (h_mono : Monotone C.π) :
    AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s)) :=
  ⟨Compiler.Verified.mono h_ver h_wf h_mono, h_ver, True.intro⟩

/-!
## 2. Layer 1B: Small-Step Transition Outcomes and Structural Non-Vacuity
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

theorem behaviorOf_le_wellFormedOn_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop} :
    BehaviorOf M p ≤ (M.toLanguage).WellFormedOn pre ↔
      ∀ init steps tr out,
        pre { init := init, steps := steps } →
        M.initState p init →
        ReachesPrefix M p init steps init tr out →
        out.isSafe := by
  constructor
  · intro h init steps tr out hpre hinit hreach
    have hdef := (le_wellFormedOn_iff (L := M.toLanguage) (BehaviorOf M p) pre).mp h
      { init := init, steps := steps } hpre
    exact hdef hinit tr out hreach
  · intro h
    refine (le_wellFormedOn_iff (L := M.toLanguage) (BehaviorOf M p) pre).mpr ?_
    intro q hpre hinit tr out hreach
    exact h q.init q.steps tr out hpre hinit hreach

theorem behaviorOf_le_wellFormed_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} :
    BehaviorOf M p ≤ (M.toLanguage).WellFormed ↔
      ∀ init steps tr out,
        M.initState p init →
        ReachesPrefix M p init steps init tr out →
        out.isSafe := by
  constructor
  · intro h init steps tr out hinit hreach
    exact (behaviorOf_le_wellFormedOn_iff (M := M)).mp h init steps tr out True.intro hinit hreach
  · intro h
    exact (behaviorOf_le_wellFormedOn_iff (M := M)).mpr
      (fun init steps tr out _ hinit hreach => h init steps tr out hinit hreach)

/-!
## 3. Unified MIR AST: `Terminator.call`, `requiredConsts`, & `mentionedItems`
-/

/-- Maximum representable 64-bit `usize::MAX` (`2^64 - 1`).

    Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38 -/
def usizeMax : Nat := 18446744073709551615

/-- MIR local slot index (`_0` is the return place, `_1 ..= arg_count` are
    function parameters, and remaining slots are temporaries).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L245-L249 -/
structure LocalIdx where
  index : Nat
  deriving DecidableEq, Repr

/-- MIR basic block index (`bb0` is `START_BLOCK`).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L194-L202 -/
structure BasicBlockIdx where
  index : Nat
  deriving DecidableEq, Repr

/-- MIR type grammar for scalar values and checked-arithmetic overflow
    tuples. -/
inductive MirTy where
  | usize
  | bool
  | unit
  | tupleUsizeBool
  deriving DecidableEq, Repr

/-- Runtime MIR scalar or tuple value. -/
inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  deriving DecidableEq, Repr

/-- MIR operand (`copy _local`, `move _local`, or `const val`).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L842-L873 -/
inductive Operand where
  | copy (src : LocalIdx)
  | move (src : LocalIdx)
  | constVal (val : MirVal)
  deriving DecidableEq, Repr

/-- Binary comparison and bitwise operators on `usize`. -/
inductive BinOp where
  | lt
  | le
  | eq
  | ne
  | gt
  | ge
  | bitAnd
  | bitOr
  | bitXor
  deriving DecidableEq, Repr

/-- Checked arithmetic operators (`AddWithOverflow`, `SubWithOverflow`,
    `MulWithOverflow`) producing `(usize, bool)`. -/
inductive CheckedBinOp where
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- Right-hand side computation of a MIR assignment statement.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L975-L1060 -/
inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | checkedBinaryOp (op : CheckedBinOp) (lhs : Operand) (rhs : Operand)
  | proj0 (src : LocalIdx)
  | proj1 (src : LocalIdx)
  deriving DecidableEq, Repr

/-- MIR statement within a basic block.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L305-L385 -/
inductive Stmt where
  | assign (dst : LocalIdx) (rv : Rvalue)
  | storageLive (loc : LocalIdx)
  | storageDead (loc : LocalIdx)
  | nop
  deriving DecidableEq, Repr

/-- MIR basic-block terminator with a general crate-resolved `Terminator.call`
    replacing the hardcoded `PureCallee2` enum.

    - `call dst callee args target` models `TerminatorKind::Call`, evaluating
      `args` left-to-right, resolving `callee` in the crate's function table,
      pushing a continuation frame `(callerBody, dst, target, callerLocals)`
      onto `MirState.frames`, and transferring control to `callee`'s entry
      block `bb0`.
    - `return_` models `TerminatorKind::Return`, popping the top continuation
      frame from `MirState.frames` (if non-empty) and writing `_0` into the
      caller's `dst` local at `returnTarget`, or terminating top-level
      execution when `MirState.frames` is empty.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L683-L808 -/
inductive Terminator where
  | return_
  | goto (target : BasicBlockIdx)
  | unreachable
  | panic
  | call (dst : LocalIdx) (callee : String) (args : List Operand) (target : BasicBlockIdx)
  | switchInt (discr : Operand) (falseTarget : BasicBlockIdx) (trueTarget : BasicBlockIdx)
  | assertNotOverflow (tupleLocal : LocalIdx) (target : BasicBlockIdx)
  deriving DecidableEq, Repr

/-- Basic block comprising a sequence of statements and a terminator. -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator
  deriving DecidableEq, Repr

/-- A compile-time constant-evaluation MIR body (`fn_name::{constant#k}: ()`)
    extracted from `Body::required_consts`.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L278-L285 -/
structure ConstMirBody where
  localCount : Nat
  blocks : List BasicBlock
  deriving DecidableEq, Repr

/-- Lowered `Runtime(PostCleanup)` MIR body of a function, carrying its
    compile-time `requiredConsts` (`Body::required_consts`) and
    `mentionedItems` (`Body::mentioned_items`) for transitive PME checking.

    Sources:
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L278-L295
    - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1364-L1389 -/
structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock
  requiredConsts : List ConstMirBody := []
  mentionedItems : List String := []
  deriving DecidableEq, Repr

/-- Entry in a crate's function lookup environment pairing a function's
    canonical identifier with its `MirBody`. -/
structure FnEntry where
  name : String
  body : MirBody
  deriving DecidableEq, Repr

/-- Crate-level function environment mapping function identifiers to their
    lowered `MirBody` definitions. -/
abbrev CrateEnv := List FnEntry

/-- Look up a function's `MirBody` by name in `env`. -/
def lookupFn (env : CrateEnv) (name : String) : Option MirBody :=
  match env with
  | [] => none
  | e :: rest => if e.name == name then some e.body else lookupFn rest name

/-- A crate-scoped MIR program pairing an entry `MirBody` with the surrounding
    `CrateEnv` used to resolve interprocedural calls and `mentionedItems`. -/
structure MirProg where
  env : CrateEnv
  body : MirBody
  deriving DecidableEq, Repr

/-!
## 4. Call-Stack Operational Semantics (`MirMachine`) and Non-Vacuity
-/

/-- Operational memory state. -/
structure MemState where
  unit : Unit := ()

def MemState.empty : MemState := { unit := () }

/-- Saved caller continuation frame pushed onto `MirState.frames` when
    executing `Terminator.call` and popped when the callee executes
    `Terminator.return_`:
    - `callerBody`: the `MirBody` of the calling function,
    - `dst`: the local slot in `callerLocals` that receives the callee's return
      value `_0`,
    - `returnTarget`: the basic block in `callerBody` to jump to after the
      call returns,
    - `callerLocals`: the caller's local store after evaluating all call
      operand arguments left-to-right.

    Corresponds to the return-place assignment and successor jump of
    `TerminatorKind::Return` and `TerminatorKind::Call`:

    > "Returning very likely at least assigns the value currently in the return
    > place (`_0`) to the place specified in the associated `Call` terminator
    > in the calling function, as if assigned via `dest = move _0`."

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L696-L700 -/
structure CallFrame where
  callerBody : MirBody
  dst : LocalIdx
  returnTarget : BasicBlockIdx
  callerLocals : Nat → Option MirVal

/-- Instantaneous state of the call-stack MIR machine:
    - `curBody`: the `MirBody` of the currently executing function frame,
    - `locals`: local store of the current frame,
    - `mem`: memory state,
    - `block`: basic block index within `curBody`,
    - `stmtIdx`: statement index within `curBody.blocks[block]`,
    - `frames`: stack of suspended caller continuation frames (`[]` at the root
      entry frame). -/
structure MirState where
  curBody : MirBody
  locals : Nat → Option MirVal
  mem : MemState
  block : Nat
  stmtIdx : Nat
  frames : List CallFrame := []

/-- Update local slot `target` in a local store `locals`. -/
def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Executable dynamic type check matching a `MirVal` against a `MirTy`. -/
def valHasTyBool (v : MirVal) (ty : MirTy) : Bool :=
  match v, ty with
  | .usize _, .usize => true
  | .bool _, .bool => true
  | .unit, .unit => true
  | .tupleUsizeBool _ _, .tupleUsizeBool => true
  | _, _ => false

/-- Propositional type validity of a `MirVal` against a `MirTy`. -/
def MirVal.hasTy (v : MirVal) (ty : MirTy) : Prop :=
  valHasTyBool v ty = true

/-- Check that a list of evaluated argument values matches a callee's expected
    parameter types `argTys` in arity and element types. -/
def argsHaveTysBool : List MirVal → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => valHasTyBool v ty && argsHaveTysBool vs tys
  | _, _ => false

/-- Construct a callee's initial local store from evaluated argument values
    `args`, binding parameters `1 ..= args.length` and leaving `_0` and all
    temporaries `> args.length` uninitialized (`none`). -/
def buildCalleeLocalsAux (idx : Nat) : List MirVal → (Nat → Option MirVal)
  | [] => fun _ => none
  | v :: rest => updateLocal (buildCalleeLocalsAux (idx + 1) rest) idx (some v)

def buildCalleeLocals (args : List MirVal) : Nat → Option MirVal :=
  buildCalleeLocalsAux 1 args

/-- Entry parameter initialization predicate for `initMirState`. -/
def argsMatchLocals (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k => (∃ v, locals k = some v ∧ v.hasTy ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

/-- Entry state predicate for a root `MirBody`: execution starts in `body` with
    an empty caller stack `frames = []`, at basic block `0`, statement `0`,
    return place `_0` uninitialized, and parameters `1 ..= argTys.length`
    holding type-valid values. -/
def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.curBody = body ∧
  s.frames = [] ∧
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  argsMatchLocals body.argTys s.locals

/-- Evaluate a single MIR `Operand` against `locals`. -/
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

/-- Evaluate a list of call argument operands left-to-right, threading the
    updated local store across `Operand.move` deinitializations.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L783-L784 -/
def evalOperandList (locals : Nat → Option MirVal) :
    List Operand → Option (List MirVal × (Nat → Option MirVal))
  | [] => some ([], locals)
  | op :: rest =>
    match evalOperand locals op with
    | none => none
    | some (v, locals1) =>
      match evalOperandList locals1 rest with
      | none => none
      | some (vs, locals2) => some (v :: vs, locals2)

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
    | .bitAnd => some (.usize (Nat.land n1 n2))
    | .bitOr => some (.usize (Nat.lor n1 n2))
    | .bitXor => some (.usize (Nat.xor n1 n2))
  | _, _ => none

def evalCheckedBinOp (op : CheckedBinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.tupleUsizeBool (n1 + n2) (decide (usizeMax < n1 + n2)))
    | .sub => some (.tupleUsizeBool (n1 - n2) (decide (n1 < n2)))
    | .mul => some (.tupleUsizeBool (n1 * n2) (decide (usizeMax < n1 * n2)))
  | _, _ => none

/-- Single-step statement evaluation within the active call frame. -/
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

/-- Single-step terminator evaluation with call-stack push on `Terminator.call`
    and caller-frame restoration on `Terminator.return_`. -/
def evalMirTerminator (env : CrateEnv) (s : MirState) (term : Terminator) :
    StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | none => .failed .ub
    | some retVal =>
      match s.frames with
      | [] => .terminated (.normal retVal)
      | frame :: restFrames =>
        .step () {
          curBody := frame.callerBody
          locals := updateLocal frame.callerLocals frame.dst.index (some retVal)
          mem := s.mem
          block := frame.returnTarget.index
          stmtIdx := 0
          frames := restFrames
        }
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed .ub
  | .panic =>
    .failed .contractViolation
  | .call dst callee args target =>
    match evalOperandList s.locals args with
    | none => .failed .ub
    | some (argVals, localsAfterArgs) =>
      match lookupFn env callee with
      | none => .failed .ub
      | some calleeBody =>
        if argsHaveTysBool argVals calleeBody.argTys then
          let frame : CallFrame := {
            callerBody := s.curBody
            dst := dst
            returnTarget := target
            callerLocals := localsAfterArgs
          }
          .step () {
            curBody := calleeBody
            locals := buildCalleeLocals argVals
            mem := s.mem
            block := 0
            stmtIdx := 0
            frames := frame :: s.frames
          }
        else
          .failed .ub
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

/-- Single-step operational evaluation of a `MirState` in crate environment
    `env`. -/
def evalMirStep (env : CrateEnv) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match s.curBody.blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator env s bb.terminator

/-- Call-stack small-step operational machine for `MirProg`. -/
def MirMachine : SmallStepMachine MirProg MirState Unit MirVal where
  initState p s := initMirState p.body s
  step p s r := r = evalMirStep p.env s

/-- Operational language of crate-resolved Rust MIR
    (`MirMachine.toLanguage`). -/
def MirLang : Language :=
  MirMachine.toLanguage

/-- Operational behavior of a `MirBody` inside crate environment `env`. -/
abbrev MirSem (env : CrateEnv) (body : MirBody) : MirLang.Behavior :=
  MirLang.sem { env := env, body := body }

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
  | storageLive _ => intro h; cases h
  | storageDead _ => intro h; cases h
  | nop => intro h; cases h

theorem evalMirTerminator_not_choice (env : CrateEnv) (s : MirState)
    (term : Terminator) (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirTerminator env s term := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    cases s.locals 0 with
    | none => intro h; cases h
    | some _ => cases s.frames <;> intro h <;> cases h
  | goto _ => intro h; cases h
  | unreachable => intro h; cases h
  | panic => intro h; cases h
  | call dst callee args target =>
    dsimp [evalMirTerminator]
    cases evalOperandList s.locals args with
    | none => intro h; cases h
    | some pArgs =>
      dsimp
      cases lookupFn env callee with
      | none => intro h; cases h
      | some calleeBody =>
        dsimp
        cases argsHaveTysBool pArgs.1 calleeBody.argTys <;> intro h <;> cases h
  | switchInt discr _ _ =>
    dsimp [evalMirTerminator]
    cases evalOperand s.locals discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk val _ =>
        cases val with
        | bool b => cases b <;> intro h <;> cases h
        | usize _ | unit | tupleUsizeBool _ _ => intro h; cases h
  | assertNotOverflow tl _ =>
    dsimp [evalMirTerminator]
    cases s.locals tl.index with
    | none => intro h; cases h
    | some v =>
      cases v with
      | tupleUsizeBool _ ov => cases ov <;> intro h <;> cases h
      | usize _ | bool _ | unit => intro h; cases h

theorem evalMirStep_not_choice (env : CrateEnv) (s : MirState)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    StepResult.choice kind branches ≠ evalMirStep env s := by
  unfold evalMirStep
  cases s.curBody.blocks[s.block]? with
  | none => intro h; cases h
  | some bb =>
    dsimp
    cases bb.stmts[s.stmtIdx]? with
    | none => exact evalMirTerminator_not_choice env s bb.terminator kind branches
    | some stmt => exact evalMirStmt_not_choice s stmt kind branches

/-- **Deliverable 1a (`mirMachine_totalStep`)**:
    The call-stack `MirMachine` is total at every state `s` and program `p`. -/
theorem mirMachine_totalStep : TotalStep MirMachine :=
  fun p s => ⟨evalMirStep p.env s, rfl⟩

/-- **Deliverable 1b (`mirMachine_inhabitedDemonic`)**:
    The call-stack `MirMachine` has no empty choice transitions. -/
theorem mirMachine_inhabitedDemonic : InhabitedDemonic MirMachine := by
  intro p s kind branches hstep
  exact False.elim (evalMirStep_not_choice p.env s kind branches hstep)

/-- **Deliverable 1c (`mirMachine_non_vacuity_at_every_depth`)**:
    From any valid initial state of any `MirProg`, the call-stack `MirMachine`
    produces at least one non-stuck execution prefix at every step budget
    `n`. -/
theorem mirMachine_non_vacuity_at_every_depth
    (p : MirProg) (init : MirState)
    (h_init : MirMachine.initState p init)
    (n : Nat) :
    ∃ out : ExecOut Unit MirVal,
      MirMachine.initState p init ∧
      ReachesPrefix MirMachine p init n init out.trace out.outcome ∧
      out.outcome ≠ .stuck :=
  non_vacuity_at_every_depth mirMachine_totalStep mirMachine_inhabitedDemonic p init h_init n

/-!
## 5. Transitive `CompileAdmitted` Across `requiredConsts` and `mentionedItems`
-/

/-- Empty `MirBody` placeholder used as `curBody` when evaluating a standalone
    `ConstMirBody` in CTFE mode. -/
def emptyMirBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 0
  blocks := []

/-- Initial state for evaluating a `ConstMirBody` in CTFE mode. -/
def initCtfeState (c : ConstMirBody) : MirState where
  curBody := { emptyMirBody with localCount := c.localCount, blocks := c.blocks }
  locals := fun _ => none
  mem := MemState.empty
  block := 0
  stmtIdx := 0
  frames := []

/-- Small-step CTFE machine for `ConstMirBody`, reusing the exact same
    `evalMirStep` transition function as runtime MIR. -/
def ConstMirMachine : SmallStepMachine ConstMirBody MirState Unit MirVal where
  initState c s := s = initCtfeState c
  step _ s r := r = evalMirStep [] s

/-- Deterministic fuel-bounded CTFE evaluator mirroring `ConstMirMachine`. -/
def evalCtfeFuel : Nat → MirState → PrefixOutcome MirVal
  | 0, _ => .running
  | n + 1, s =>
    match evalMirStep [] s with
    | .step _ s' => evalCtfeFuel n s'
    | .choice _ _ => .stuck
    | .terminated term => .terminated term
    | .failed err => .failed err

/-- Executable boolean CTFE check: returns `true` when `c` terminates normally
    with `.unit` within `ctfeFuel` steps. -/
def evalCtfeBool (ctfeFuel : Nat) (c : ConstMirBody) : Bool :=
  match evalCtfeFuel ctfeFuel (initCtfeState c) with
  | .terminated (.normal .unit) => true
  | _ => false

theorem reachesPrefix_constMirMachine_eq_evalCtfeFuel
    (c : ConstMirBody) (init : MirState) (n : Nat) :
    ∀ (s : MirState) (tr : List Unit) (out : PrefixOutcome MirVal),
      ReachesPrefix ConstMirMachine c init n s tr out →
      out = evalCtfeFuel n s := by
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
      have hstep' : StepResult.step obs s' = evalMirStep [] s := hstep
      rw [← hstep']
      exact ih s' tr' out hrest
    | choice _ kind _ _ branches _ _ hstep _ _ =>
      exact False.elim (evalMirStep_not_choice [] s kind branches hstep)
    | emptyChoice _ kind _ branches hstep _ =>
      exact False.elim (evalMirStep_not_choice [] s kind branches hstep)
    | terminated _ _ term hstep =>
      have hstep' : StepResult.terminated term = evalMirStep [] s := hstep
      rw [← hstep']
    | failed _ _ err hstep =>
      have hstep' : StepResult.failed err = evalMirStep [] s := hstep
      rw [← hstep']
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, rfl⟩)

/-- Deterministic safety persistence: if `evalCtfeFuel fuel s` reaches a
    `.terminated` outcome, then `evalCtfeFuel steps s` is safe (`isSafe`) at
    **every** step budget `steps : Nat` (either `.running` before termination
    or `.terminated` at and after termination). -/
theorem evalCtfeFuel_safe_of_terminated :
    ∀ (fuel : Nat) (s : MirState) (term : TerminationKind MirVal),
      evalCtfeFuel fuel s = .terminated term →
      ∀ (steps : Nat), (evalCtfeFuel steps s).isSafe
  | 0, _, _, hTerm, _ => by cases hTerm
  | f + 1, s, term, hTerm, steps => by
    unfold evalCtfeFuel at hTerm
    cases hStep : evalMirStep [] s with
    | choice _ _ => rw [hStep] at hTerm; cases hTerm
    | failed _ => rw [hStep] at hTerm; cases hTerm
    | terminated term' =>
      cases steps with
      | zero => exact True.intro
      | succ st =>
        unfold evalCtfeFuel
        rw [hStep]
        exact True.intro
    | step _ s' =>
      rw [hStep] at hTerm
      cases steps with
      | zero => exact True.intro
      | succ st =>
        unfold evalCtfeFuel
        rw [hStep]
        exact evalCtfeFuel_safe_of_terminated f s' term hTerm st

/-- Construct a `ReachesPrefix` witness from
    `evalCtfeFuel fuel s = .terminated term`. -/
theorem reachesPrefix_of_evalCtfeFuel_terminated
    (c : ConstMirBody) (init : MirState) :
    ∀ (fuel : Nat) (s : MirState) (term : TerminationKind MirVal),
      evalCtfeFuel fuel s = .terminated term →
      ∃ tr, ReachesPrefix ConstMirMachine c init fuel s tr (.terminated term)
  | 0, _, _, hTerm => by cases hTerm
  | f + 1, s, term, hTerm => by
    unfold evalCtfeFuel at hTerm
    cases hStep : evalMirStep [] s with
    | choice _ _ => rw [hStep] at hTerm; cases hTerm
    | failed _ => rw [hStep] at hTerm; cases hTerm
    | terminated term' =>
      rw [hStep] at hTerm
      injection hTerm with hEq
      subst hEq
      exact ⟨[], ReachesPrefix.terminated f s term' hStep.symm⟩
    | step obs s' =>
      rw [hStep] at hTerm
      have ⟨tr', hReach'⟩ :=
        reachesPrefix_of_evalCtfeFuel_terminated c init f s' term hTerm
      exact ⟨obs :: tr', ReachesPrefix.step f s s' obs tr' (.terminated term) hStep.symm hReach'⟩

/-- A `ConstMirBody` succeeds in CTFE (`CtfeAdmitted c`) when every finite
    execution prefix from `initCtfeState c` is safe and some finite step budget
    reaches `.terminated (.normal .unit)`.

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1364-L1375 -/
def CtfeAdmitted (c : ConstMirBody) : Prop :=
  (∀ steps tr out,
    ReachesPrefix ConstMirMachine c (initCtfeState c) steps (initCtfeState c) tr out →
    out.isSafe) ∧
  (∃ steps tr,
    ReachesPrefix ConstMirMachine c (initCtfeState c) steps (initCtfeState c) tr
      (.terminated (.normal .unit)))

/-- Soundness of the executable CTFE boolean checker: if
    `evalCtfeBool ctfeFuel c = true`, then `CtfeAdmitted c` holds. -/
theorem ctfeAdmitted_of_evalCtfeBool {ctfeFuel : Nat} {c : ConstMirBody}
    (hBool : evalCtfeBool ctfeFuel c = true) :
    CtfeAdmitted c := by
  unfold evalCtfeBool at hBool
  cases hFuel : evalCtfeFuel ctfeFuel (initCtfeState c) with
  | running | failed _ | stuck => rw [hFuel] at hBool; cases hBool
  | terminated term =>
    rw [hFuel] at hBool
    cases term with
    | unwind => cases hBool
    | normal v =>
      cases v with
      | usize _ | bool _ | tupleUsizeBool _ _ => cases hBool
      | unit =>
        refine ⟨?_, ?_⟩
        · intro steps tr out hReach
          have hEq := reachesPrefix_constMirMachine_eq_evalCtfeFuel
            c (initCtfeState c) steps (initCtfeState c) tr out hReach
          rw [hEq]
          exact evalCtfeFuel_safe_of_terminated ctfeFuel (initCtfeState c) (.normal .unit) hFuel steps
        · have ⟨tr, hReach⟩ := reachesPrefix_of_evalCtfeFuel_terminated
            c (initCtfeState c) ctfeFuel (initCtfeState c) (.normal .unit) hFuel
          exact ⟨ctfeFuel, tr, hReach⟩

/-- If `evalCtfeFuel ctfeFuel (initCtfeState c)` reaches `.failed err`, then
    `¬ CtfeAdmitted c`. -/
theorem not_ctfeAdmitted_of_evalCtfeFuel_failed {ctfeFuel : Nat} {c : ConstMirBody}
    {err : FailureKind}
    (hFail : evalCtfeFuel ctfeFuel (initCtfeState c) = .failed err) :
    ¬ CtfeAdmitted c := by
  intro ⟨hSafe, _⟩
  have ⟨tr, out, hReach, _⟩ :=
    exists_reaches_prefix (M := ConstMirMachine)
      (fun _ s => ⟨evalMirStep [] s, rfl⟩)
      (fun _ s kind branches hstep => False.elim (evalMirStep_not_choice [] s kind branches hstep))
      c (initCtfeState c) ctfeFuel (initCtfeState c)
  have hOutEq := reachesPrefix_constMirMachine_eq_evalCtfeFuel
    c (initCtfeState c) ctfeFuel (initCtfeState c) tr out hReach
  rw [hFail] at hOutEq
  subst hOutEq
  exact hSafe ctfeFuel tr (.failed err) hReach

/-- Transitive compile-time admissibility (`CompileAdmitted env fuel body`):
    models `rustc_monomorphize::collector::collect_items_of_instance`, which
    evaluates every constant in `body.required_consts()` and recursively visits
    every item in `body.mentioned_items()` in `CollectionMode::MentionedItems`
    to evaluate its `required_consts()` (even when the item is only referenced
    inside a dead branch `if false { callee(); }`).

    Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1364-L1389 -/
def CompileAdmitted (env : CrateEnv) : Nat → MirBody → Prop
  | 0, _ => False
  | fuel + 1, body =>
    AllHold (body.requiredConsts.map CtfeAdmitted) ∧
    AllHold (body.mentionedItems.map (fun calleeName =>
      match lookupFn env calleeName with
      | some calleeBody => CompileAdmitted env fuel calleeBody
      | none => False))

/-- Executable boolean checker for transitive `CompileAdmitted`. -/
def checkCompileAdmitted (env : CrateEnv) (ctfeFuel : Nat) : Nat → MirBody → Bool
  | 0, _ => false
  | fuel + 1, body =>
    body.requiredConsts.all (evalCtfeBool ctfeFuel) &&
    body.mentionedItems.all (fun calleeName =>
      match lookupFn env calleeName with
      | some calleeBody => checkCompileAdmitted env ctfeFuel fuel calleeBody
      | none => false)

theorem allHold_of_list_all {α : Type} {f : α → Bool} {P : α → Prop}
    (hImp : ∀ x, f x = true → P x) :
    ∀ (xs : List α), xs.all f = true → AllHold (xs.map P)
  | [], _ => True.intro
  | x :: rest, hAll => by
    dsimp [List.all] at hAll
    have hAnd := Eq.mp (Bool.and_eq_true _ _) hAll
    exact ⟨hImp x hAnd.1, allHold_of_list_all hImp rest hAnd.2⟩

/-- Soundness of `checkCompileAdmitted`: if `checkCompileAdmitted env ctfeFuel
    fuel body = true`, then `CompileAdmitted env fuel body` holds. -/
theorem compileAdmitted_of_checkCompileAdmitted
    (env : CrateEnv) (ctfeFuel : Nat) :
    ∀ (fuel : Nat) (body : MirBody),
      checkCompileAdmitted env ctfeFuel fuel body = true →
      CompileAdmitted env fuel body
  | 0, _, h => by cases h
  | fuel + 1, body, h => by
    dsimp [checkCompileAdmitted] at h
    have hAnd := Eq.mp (Bool.and_eq_true _ _) h
    refine ⟨?_, ?_⟩
    · exact allHold_of_list_all (fun _ hc => ctfeAdmitted_of_evalCtfeBool hc)
        body.requiredConsts hAnd.1
    · refine allHold_of_list_all ?_ body.mentionedItems hAnd.2
      intro calleeName hCallee
      cases hLook : lookupFn env calleeName with
      | none => rw [hLook] at hCallee; cases hCallee
      | some calleeBody =>
        rw [hLook] at hCallee
        exact compileAdmitted_of_checkCompileAdmitted env ctfeFuel fuel calleeBody hCallee


/-!
## 6. Unified `FunctionalTranslation`: Inlining (Mode A) & Summaries (Mode B)
-/

/-- Symbolic values tracked by `FunctionalTranslation`. -/
inductive SymVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  deriving DecidableEq, Repr

/-- Convert a `MirVal` constant into a `SymVal`. -/
def SymVal.ofMirVal : MirVal → SymVal
  | .usize n => .usize n
  | .bool b => .bool b
  | .unit => .unit
  | .tupleUsizeBool val ov => .tupleUsizeBool val ov

/-- Convert a `SymVal` into its corresponding concrete `MirVal`. -/
def SymVal.toMirVal : SymVal → MirVal
  | .usize n => .usize n
  | .bool b => .bool b
  | .unit => .unit
  | .tupleUsizeBool val ov => .tupleUsizeBool val ov

/-- Refinement relation between symbolic values and concrete `MirVal`s. -/
def SymValRefines (sv : SymVal) (mv : MirVal) : Prop :=
  mv = sv.toMirVal

@[simp]
theorem symValRefines_toMirVal (sv : SymVal) :
    SymValRefines sv sv.toMirVal := rfl

@[simp]
theorem symValRefines_ofMirVal (mv : MirVal) :
    SymValRefines (SymVal.ofMirVal mv) mv := by
  cases mv <;> rfl

/-- Executable type check for `SymVal`. -/
def symValHasTyBool (sv : SymVal) (ty : MirTy) : Bool :=
  match sv, ty with
  | .usize _, .usize => true
  | .bool _, .bool => true
  | .unit, .unit => true
  | .tupleUsizeBool _ _, .tupleUsizeBool => true
  | _, _ => false

/-- Executable arity and type check for a list of symbolic call arguments. -/
def symArgsHaveTysBool : List SymVal → List MirTy → Bool
  | [], [] => true
  | sv :: svs, ty :: tys => symValHasTyBool sv ty && symArgsHaveTysBool svs tys
  | _, _ => false

/-- Pairwise relation lifting over two lists of equal length. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

theorem valHasTyBool_of_symValRefines {sv : SymVal} {mv : MirVal} {ty : MirTy}
    (hRef : SymValRefines sv mv) :
    valHasTyBool mv ty = symValHasTyBool sv ty := by
  subst hRef
  cases sv <;> cases ty <;> rfl

theorem argsHaveTysBool_of_forall2 {argSvs : List SymVal} {argMvs : List MirVal}
    (hArgs : Forall2 SymValRefines argSvs argMvs) :
    ∀ (tys : List MirTy),
      argsHaveTysBool argMvs tys = symArgsHaveTysBool argSvs tys := by
  induction hArgs with
  | nil =>
    intro tys
    cases tys <;> rfl
  | cons hHead _ ih =>
    intro tys
    cases tys with
    | nil => rfl
    | cons ty restTys =>
      dsimp [argsHaveTysBool, symArgsHaveTysBool]
      rw [valHasTyBool_of_symValRefines hHead, ih restTys]

/-- Symbolic machine state within a single frame. -/
structure SymState where
  locals : List (Option SymVal)
  block : Nat
  stmtIdx : Nat
  deriving DecidableEq, Repr

/-- Update index `idx` in a symbolic local list `locals`. -/
def setSymLocal : List (Option SymVal) → Nat → Option SymVal → List (Option SymVal)
  | [], _, _ => []
  | _ :: rest, 0, val => val :: rest
  | head :: rest, n + 1, val => head :: setSymLocal rest n val

/-- Initialize symbolic parameter locals `1 ..= args.length` inside a local
    list. -/
def setSymArgsAux (idx : Nat) :
    List SymVal → List (Option SymVal) → List (Option SymVal)
  | [], locals => locals
  | sv :: rest, locals =>
    setSymLocal (setSymArgsAux (idx + 1) rest locals) idx (some sv)

/-- Build the initial symbolic local store for a function with `localCount`
    slots and symbolic argument values `args`. -/
def buildSymCalleeLocals (localCount : Nat) (args : List SymVal) :
    List (Option SymVal) :=
  setSymArgsAux 1 args (List.replicate localCount none)

/-- Build the initial `SymState` for a `MirBody` applied to `args`. -/
def initSymState (body : MirBody) (args : List SymVal) : SymState where
  locals := buildSymCalleeLocals body.localCount args
  block := 0
  stmtIdx := 0

/-- Evaluate an `Operand` symbolically. -/
def evalSymOperand (locals : List (Option SymVal)) (op : Operand) :
    Option (SymVal × List (Option SymVal)) :=
  match op with
  | .copy src =>
    match locals[src.index]? with
    | some (some sv) => some (sv, locals)
    | _ => none
  | .move src =>
    match locals[src.index]? with
    | some (some sv) => some (sv, setSymLocal locals src.index none)
    | _ => none
  | .constVal v =>
    some (SymVal.ofMirVal v, locals)

/-- Evaluate a list of call argument operands left-to-right symbolically. -/
def evalSymOperandList (locals : List (Option SymVal)) :
    List Operand → Option (List SymVal × List (Option SymVal))
  | [] => some ([], locals)
  | op :: rest =>
    match evalSymOperand locals op with
    | none => none
    | some (sv, locals1) =>
      match evalSymOperandList locals1 rest with
      | none => none
      | some (svs, locals2) => some (sv :: svs, locals2)

def evalSymBinOp (op : BinOp) (v1 v2 : SymVal) : Option SymVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .lt => some (.bool (decide (n1 < n2)))
    | .le => some (.bool (decide (n1 ≤ n2)))
    | .eq => some (.bool (decide (n1 = n2)))
    | .ne => some (.bool (decide (n1 ≠ n2)))
    | .gt => some (.bool (decide (n2 < n1)))
    | .ge => some (.bool (decide (n2 ≤ n1)))
    | .bitAnd => some (.usize (Nat.land n1 n2))
    | .bitOr => some (.usize (Nat.lor n1 n2))
    | .bitXor => some (.usize (Nat.xor n1 n2))
  | _, _ => none

def evalSymCheckedBinOp (op : CheckedBinOp) (v1 v2 : SymVal) : Option SymVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.tupleUsizeBool (n1 + n2) (decide (usizeMax < n1 + n2)))
    | .sub => some (.tupleUsizeBool (n1 - n2) (decide (n1 < n2)))
    | .mul => some (.tupleUsizeBool (n1 * n2) (decide (usizeMax < n1 * n2)))
  | _, _ => none

/-- Evaluate a single non-terminator statement symbolically. -/
def evalSymStmt (s : SymState) (stmt : Stmt) : Option SymState :=
  match stmt with
  | .assign dst (.use op) =>
    match evalSymOperand s.locals op with
    | some (sv, locals1) =>
      some { s with
        locals := setSymLocal locals1 dst.index (some sv)
        stmtIdx := s.stmtIdx + 1
      }
    | none => none
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalSymOperand s.locals lhs with
    | none => none
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | none => none
      | some (v2, locals2) =>
        match evalSymBinOp op v1 v2 with
        | some res =>
          some { s with
            locals := setSymLocal locals2 dst.index (some res)
            stmtIdx := s.stmtIdx + 1
          }
        | none => none
  | .assign dst (.checkedBinaryOp op lhs rhs) =>
    match evalSymOperand s.locals lhs with
    | none => none
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | none => none
      | some (v2, locals2) =>
        match evalSymCheckedBinOp op v1 v2 with
        | some res =>
          some { s with
            locals := setSymLocal locals2 dst.index (some res)
            stmtIdx := s.stmtIdx + 1
          }
        | none => none
  | .assign dst (.proj0 src) =>
    match s.locals[src.index]? with
    | some (some (.tupleUsizeBool val _)) =>
      some { s with
        locals := setSymLocal s.locals dst.index (some (.usize val))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => none
  | .assign dst (.proj1 src) =>
    match s.locals[src.index]? with
    | some (some (.tupleUsizeBool _ ov)) =>
      some { s with
        locals := setSymLocal s.locals dst.index (some (.bool ov))
        stmtIdx := s.stmtIdx + 1
      }
    | _ => none
  | .storageLive loc =>
    some { s with
      locals := setSymLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .storageDead loc =>
    some { s with
      locals := setSymLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    }
  | .nop =>
    some { s with stmtIdx := s.stmtIdx + 1 }

/-- Spine-preserving boolean disjunction that matches on its second argument so
    `orBool ov false` reduces definitionally to `ov` by kernel `rfl` even when
    `ov` is a symbolic `decide (...)` term. -/
def orBool (ov1 ov2 : Bool) : Bool :=
  match ov2 with
  | false => ov1
  | true => true

theorem orBool_eq_or (ov1 ov2 : Bool) :
    orBool ov1 ov2 = (ov1 || ov2) := by
  cases ov1 <;> cases ov2 <;> rfl

theorem orBool_eq_false_iff (ov1 ov2 : Bool) :
    orBool ov1 ov2 = false ↔ ov1 = false ∧ ov2 = false := by
  cases ov1 <;> cases ov2 <;> decide

/-- Spine-preserving branch merge for `SymVal`: lifts the outer `SymVal`
    constructor above a boolean branch condition `cond` so that `evalSymState`
    keeps both `some` and the `SymVal` tag exposed at the spine even across
    `switchInt` branches. -/
def mergeBranchSymVal (cond : Bool) (vFalse vTrue : SymVal) : Option SymVal :=
  match vFalse, vTrue with
  | .usize nF, .usize nT =>
    some (.usize (match cond with | false => nF | true => nT))
  | .bool bF, .bool bT =>
    some (.bool (match cond with | false => bF | true => bT))
  | .unit, .unit =>
    some .unit
  | .tupleUsizeBool nF ovF, .tupleUsizeBool nT ovT =>
    some (.tupleUsizeBool
      (match cond with | false => nF | true => nT)
      (match cond with | false => ovF | true => ovT))
  | _, _ => none

theorem mergeBranchSymVal_false {vFalse vTrue merged : SymVal}
    (h : mergeBranchSymVal false vFalse vTrue = some merged) :
    merged = vFalse := by
  cases vFalse <;> cases vTrue <;> cases h <;> rfl

theorem mergeBranchSymVal_true {vFalse vTrue merged : SymVal}
    (h : mergeBranchSymVal true vFalse vTrue = some merged) :
    merged = vTrue := by
  cases vFalse <;> cases vTrue <;> cases h <;> rfl

/-- Modular callee summary entry used by Mode B (`.callSummary`).
    `eval` maps symbolic arguments `List SymVal` to `Option (Bool × SymVal)`
    (`some (failed, retSv)`), keeping the outer `some` and return constructor
    exposed at the spine. -/
structure CalleeSummary where
  name : String
  argTys : List MirTy
  retTy : MirTy
  eval : List SymVal → Option (Bool × SymVal)

/-- Environment of modular callee summaries available to `evalSymState`. -/
abbrev SummaryEnv := List CalleeSummary

/-- Look up a modular callee summary by function name. -/
def lookupSummary (summaries : SummaryEnv) (name : String) :
    Option CalleeSummary :=
  match summaries with
  | [] => none
  | s :: rest => if s.name == name then some s else lookupSummary rest name

/-- Execution plan guiding symbolic evaluation (`evalSymState`).
    Supports both interprocedural verification modes:
    - `callInline calleePlan afterCall` (Mode A): symbolically executes the
      callee's `MirBody` inline using `calleePlan`, then continues in the caller
      with `afterCall`.
    - `callSummary afterCall` (Mode B): discharges the call using a verified
      `CalleeSummary` from `SummaryEnv`, then continues in the caller with
      `afterCall`. -/
inductive TransPlan where
  | return_
  | step (next : TransPlan)
  | goto (next : TransPlan)
  | assertNotOverflow (next : TransPlan)
  | branch (falseBranch : TransPlan) (trueBranch : TransPlan)
  | callInline (calleePlan : TransPlan) (afterCall : TransPlan)
  | callSummary (afterCall : TransPlan)
  deriving DecidableEq, Repr

/-- Spine-preserving symbolic evaluator over `TransPlan`.
    Returns `some (failed, retSv)` where `failed : Bool` accumulates whether any
    checked arithmetic assertion or callee precondition failed along the
    executed path, and `retSv : SymVal` is the symbolic return value. -/
def evalSymState (env : CrateEnv) (summaries : SummaryEnv) :
    TransPlan → MirBody → SymState → Option (Bool × SymVal)
  | .return_, body, s =>
    match body.blocks[s.block]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some _ => none
      | none =>
        match bb.terminator with
        | .return_ =>
          match s.locals[0]? with
          | some (some retSv) => some (false, retSv)
          | _ => none
        | _ => none
  | .step nextPlan, body, s =>
    match body.blocks[s.block]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | none => none
      | some stmt =>
        match evalSymStmt s stmt with
        | some s' => evalSymState env summaries nextPlan body s'
        | none => none
  | .goto nextPlan, body, s =>
    match body.blocks[s.block]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some _ => none
      | none =>
        match bb.terminator with
        | .goto target =>
          evalSymState env summaries nextPlan body
            { s with block := target.index, stmtIdx := 0 }
        | _ => none
  | .assertNotOverflow nextPlan, body, s =>
    match body.blocks[s.block]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some _ => none
      | none =>
        match bb.terminator with
        | .assertNotOverflow tupleLocal target =>
          match s.locals[tupleLocal.index]? with
          | some (some (.tupleUsizeBool _ ov)) =>
            match evalSymState env summaries nextPlan body
                { s with block := target.index, stmtIdx := 0 } with
            | some (restFailed, retSv) => some (orBool ov restFailed, retSv)
            | none => none
          | _ => none
        | _ => none
  | .branch falsePlan truePlan, body, s =>
    match body.blocks[s.block]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some _ => none
      | none =>
        match bb.terminator with
        | .switchInt discr falseTarget trueTarget =>
          match evalSymOperand s.locals discr with
          | some (.bool cond, locals') =>
            match evalSymState env summaries falsePlan body
                { s with locals := locals', block := falseTarget.index, stmtIdx := 0 },
              evalSymState env summaries truePlan body
                { s with locals := locals', block := trueTarget.index, stmtIdx := 0 } with
            | some (fFail, fVal), some (tFail, tVal) =>
              match mergeBranchSymVal cond fVal tVal with
              | some mergedVal =>
                some ((match cond with | false => fFail | true => tFail), mergedVal)
              | none => none
            | _, _ => none
          | _ => none
        | _ => none
  | .callInline calleePlan afterCall, body, s =>
    match body.blocks[s.block]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some _ => none
      | none =>
        match bb.terminator with
        | .call dst callee args target =>
          match evalSymOperandList s.locals args with
          | none => none
          | some (argSvs, localsAfterArgs) =>
            match lookupFn env callee with
            | none => none
            | some calleeBody =>
              if symArgsHaveTysBool argSvs calleeBody.argTys then
                match evalSymState env summaries calleePlan calleeBody
                    (initSymState calleeBody argSvs) with
                | some (callFailed, callRetSv) =>
                  let callerAfter : SymState := {
                    locals := setSymLocal localsAfterArgs dst.index (some callRetSv)
                    block := target.index
                    stmtIdx := 0
                  }
                  match evalSymState env summaries afterCall body callerAfter with
                  | some (afterFailed, finalRetSv) =>
                    some (orBool callFailed afterFailed, finalRetSv)
                  | none => none
                | none => none
              else
                none
        | _ => none
  | .callSummary afterCall, body, s =>
    match body.blocks[s.block]? with
    | none => none
    | some bb =>
      match bb.stmts[s.stmtIdx]? with
      | some _ => none
      | none =>
        match bb.terminator with
        | .call dst callee args target =>
          match evalSymOperandList s.locals args with
          | none => none
          | some (argSvs, localsAfterArgs) =>
            match lookupSummary summaries callee with
            | none => none
            | some summary =>
              if symArgsHaveTysBool argSvs summary.argTys then
                match summary.eval argSvs with
                | some (callFailed, callRetSv) =>
                  let callerAfter : SymState := {
                    locals := setSymLocal localsAfterArgs dst.index (some callRetSv)
                    block := target.index
                    stmtIdx := 0
                  }
                  match evalSymState env summaries afterCall body callerAfter with
                  | some (afterFailed, finalRetSv) =>
                    some (orBool callFailed afterFailed, finalRetSv)
                  | none => none
                | none => none
              else
                none
        | _ => none

/-- Compute a `TransPlan` automatically from fuel.
    When `inlinedCallees` contains `callee` (or `lookupSummary summaries callee`
    is `none`) and `callFuel > 0`, `computePlan` emits `.callInline`; otherwise,
    if a summary is registered in `summaries`, it emits `.callSummary`. -/
def computePlan (env : CrateEnv) (summaries : SummaryEnv) :
    Nat → Nat → MirBody → Nat → Nat → Option TransPlan
  | 0, _, _, _, _ => none
  | stepFuel + 1, callFuel, body, block, stmtIdx =>
    match body.blocks[block]? with
    | none => none
    | some bb =>
      match bb.stmts[stmtIdx]? with
      | some _ =>
        match computePlan env summaries stepFuel callFuel body block (stmtIdx + 1) with
        | some nextPlan => some (.step nextPlan)
        | none => none
      | none =>
        match bb.terminator with
        | .return_ => some .return_
        | .goto target =>
          match computePlan env summaries stepFuel callFuel body target.index 0 with
          | some nextPlan => some (.goto nextPlan)
          | none => none
        | .assertNotOverflow _ target =>
          match computePlan env summaries stepFuel callFuel body target.index 0 with
          | some nextPlan => some (.assertNotOverflow nextPlan)
          | none => none
        | .switchInt _ falseTarget trueTarget =>
          match computePlan env summaries stepFuel callFuel body falseTarget.index 0,
                computePlan env summaries stepFuel callFuel body trueTarget.index 0 with
          | some fp, some tp => some (.branch fp tp)
          | _, _ => none
        | .call _ callee _ target =>
          match computePlan env summaries stepFuel callFuel body target.index 0 with
          | none => none
          | some afterPlan =>
            match lookupSummary summaries callee with
            | some _ => some (.callSummary afterPlan)
            | none =>
              match callFuel, lookupFn env callee with
              | cFuel + 1, some calleeBody =>
                match computePlan env summaries stepFuel cFuel calleeBody 0 0 with
                | some calleePlan => some (.callInline calleePlan afterPlan)
                | none => none
              | _, _ => none
        | .unreachable | .panic => none

/-- Top-level symbolic evaluator returning `Option SymVal` (`some retSv` iff
    symbolic execution succeeds with `failed = false`). -/
def evalSym (env : CrateEnv) (summaries : SummaryEnv) (plan : TransPlan)
    (body : MirBody) (args : List SymVal) : Option SymVal :=
  match evalSymState env summaries plan body (initSymState body args) with
  | some (false, retSv) => some retSv
  | _ => none

/-- Pure functional translation of a `MirBody` using `computePlan`.
    When `summaries = []` and `callFuel > 0` (Mode A), private helper calls are
    inlined automatically; when a helper has an entry in `summaries` (Mode B),
    its modular summary is used instead. -/
def translatePure (env : CrateEnv) (summaries : SummaryEnv)
    (stepFuel callFuel : Nat) (body : MirBody) (args : List SymVal) :
    Option SymVal :=
  match computePlan env summaries stepFuel callFuel body 0 0 with
  | some plan => evalSym env summaries plan body args
  | none => none

/-- Prefix safety from an arbitrary concrete `MirState`: at every step budget,
    every execution prefix of `MirMachine` starting at `s` is either still
    `.running` or `.terminated (.normal v)`. -/
def SafeFrom (env : CrateEnv) (s : MirState) (v : MirVal) : Prop :=
  ∀ (rootBody : MirBody) (init : MirState) (steps : Nat) (tr : List Unit)
    (out : PrefixOutcome MirVal),
    ReachesPrefix MirMachine { env := env, body := rootBody } init steps s tr out →
    out = .running ∨ out = .terminated (.normal v)

theorem safeFrom_terminated {env : CrateEnv} {s : MirState} {v : MirVal}
    (hterm : evalMirStep env s = .terminated (.normal v)) :
    SafeFrom env s v := by
  intro rootBody init steps tr out hreach
  cases steps with
  | zero =>
    cases hreach with
    | zero => exact Or.inl rfl
  | succ k =>
    cases hreach with
    | step _ _ _ _ _ _ hs _ =>
      exact False.elim (by cases hs.trans hterm)
    | choice _ _ _ _ _ _ _ hs _ _ =>
      exact False.elim (by cases hs.trans hterm)
    | emptyChoice _ _ _ _ hs _ =>
      exact False.elim (by cases hs.trans hterm)
    | terminated _ _ term hs =>
      have hs' : StepResult.terminated term = StepResult.terminated (.normal v) :=
        hs.trans hterm
      injection hs' with hEq
      subst hEq
      exact Or.inr rfl
    | failed _ _ _ hs =>
      exact False.elim (by cases hs.trans hterm)
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.terminated (.normal v), hterm.symm⟩)

theorem safeFrom_step {env : CrateEnv} {s s' : MirState} {v : MirVal}
    (hstep : evalMirStep env s = .step () s')
    (hnext : SafeFrom env s' v) :
    SafeFrom env s v := by
  intro rootBody init steps tr out hreach
  cases steps with
  | zero =>
    cases hreach with
    | zero => exact Or.inl rfl
  | succ k =>
    cases hreach with
    | step _ _ s2 obs tr' _ hs hrest =>
      have hs' : StepResult.step obs s2 = StepResult.step () s' := hs.trans hstep
      injection hs' with _ hs2
      subst hs2
      exact hnext rootBody init k tr' out hrest
    | choice _ _ _ _ _ _ _ hs _ _ =>
      exact False.elim (by cases hs.trans hstep)
    | emptyChoice _ _ _ _ hs _ =>
      exact False.elim (by cases hs.trans hstep)
    | terminated _ _ _ hs =>
      exact False.elim (by cases hs.trans hstep)
    | failed _ _ _ hs =>
      exact False.elim (by cases hs.trans hstep)
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.step () s', hstep.symm⟩)

/-- Continuation predicate over a stack of suspended `CallFrame`s:
    - when `frames = []`, the current frame is the root entry frame and its
      return value `retVal` must equal `finalVal`;
    - when `frames = frame :: restFrames`, restoring `frame` with `retVal`
      stored at `frame.dst` must be `SafeFrom` with respect to `finalVal`. -/
def ReturnCont (env : CrateEnv) (frames : List CallFrame) (retVal : MirVal)
    (finalVal : MirVal) : Prop :=
  match frames with
  | [] => retVal = finalVal
  | frame :: restFrames =>
    ∀ (mem : MemState),
      SafeFrom env
        { curBody := frame.callerBody
          locals := updateLocal frame.callerLocals frame.dst.index (some retVal)
          mem := mem
          block := frame.returnTarget.index
          stmtIdx := 0
          frames := restFrames }
        finalVal

theorem safeFrom_of_returnCont {env : CrateEnv} {conc : MirState}
    {retMv finalVal : MirVal}
    (hStep : evalMirStep env conc = evalMirTerminator env conc .return_)
    (hLoc0 : conc.locals 0 = some retMv)
    (hCont : ReturnCont env conc.frames retMv finalVal) :
    SafeFrom env conc finalVal := by
  cases hFrames : conc.frames with
  | nil =>
    rw [hFrames] at hCont
    dsimp [ReturnCont] at hCont
    subst hCont
    apply safeFrom_terminated
    rw [hStep]
    dsimp [evalMirTerminator]
    rw [hLoc0, hFrames]
  | cons frame restFrames =>
    rw [hFrames] at hCont
    dsimp [ReturnCont] at hCont
    apply safeFrom_step (s' := {
      curBody := frame.callerBody
      locals := updateLocal frame.callerLocals frame.dst.index (some retMv)
      mem := conc.mem
      block := frame.returnTarget.index
      stmtIdx := 0
      frames := restFrames
    })
    · rw [hStep]
      dsimp [evalMirTerminator]
      rw [hLoc0, hFrames]
    · exact hCont conc.mem

/-- Local-store refinement between a symbolic local list and a concrete local
    store. -/
def LocalsRefines (symLocals : List (Option SymVal))
    (concLocals : Nat → Option MirVal) : Prop :=
  ∀ (idx : Nat) (sv : SymVal),
    symLocals[idx]? = some (some sv) →
    ∃ mv, concLocals idx = some mv ∧ SymValRefines sv mv

/-- Full frame-state refinement between a symbolic `SymState` and a concrete
    `MirState` executing `body`. -/
def SymStateRefines (body : MirBody) (sym : SymState) (conc : MirState) : Prop :=
  conc.curBody = body ∧
  sym.block = conc.block ∧
  sym.stmtIdx = conc.stmtIdx ∧
  LocalsRefines sym.locals conc.locals

theorem getElem?_setSymLocal_same :
    ∀ (locals : List (Option SymVal)) (target : Nat) (val : Option SymVal),
      (setSymLocal locals target val)[target]? =
        match locals[target]? with
        | some _ => some val
        | none => none
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: rest, n + 1, val => getElem?_setSymLocal_same rest n val

theorem getElem?_setSymLocal_diff :
    ∀ (locals : List (Option SymVal)) (target idx : Nat) (val : Option SymVal),
      idx ≠ target →
      (setSymLocal locals target val)[idx]? = locals[idx]?
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hne => False.elim (hne rfl)
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: rest, t + 1, i + 1, val, hne =>
    getElem?_setSymLocal_diff rest t i val (fun h => hne (congrArg Nat.succ h))

theorem nat_beq_self (n : Nat) : (n == n) = true :=
  beq_self_eq_true n

theorem localsRefines_setSymLocal_some {symLocals : List (Option SymVal)}
    {concLocals : Nat → Option MirVal} (hRef : LocalsRefines symLocals concLocals)
    (target : Nat) {sv : SymVal} {mv : MirVal} (hVal : SymValRefines sv mv) :
    LocalsRefines (setSymLocal symLocals target (some sv))
      (updateLocal concLocals target (some mv)) := by
  intro idx sv' hGet
  cases hBeq : (idx == target) with
  | true =>
    have hEq : idx = target := eq_of_beq hBeq
    subst hEq
    rw [getElem?_setSymLocal_same] at hGet
    cases hSlot : symLocals[idx]? with
    | none => rw [hSlot] at hGet; cases hGet
    | some _ =>
      rw [hSlot] at hGet
      injection hGet with hOpt
      injection hOpt with hSv
      subst hSv
      refine ⟨mv, ?_, hVal⟩
      unfold updateLocal
      rw [hBeq]
      rfl
  | false =>
    have hNe : idx ≠ target := fun h => by
      subst h
      rw [nat_beq_self] at hBeq
      cases hBeq
    rw [getElem?_setSymLocal_diff symLocals target idx (some sv) hNe] at hGet
    have ⟨mv', hConc, hRef'⟩ := hRef idx sv' hGet
    refine ⟨mv', ?_, hRef'⟩
    unfold updateLocal
    rw [hBeq]
    exact hConc

theorem localsRefines_setSymLocal_none {symLocals : List (Option SymVal)}
    {concLocals : Nat → Option MirVal} (hRef : LocalsRefines symLocals concLocals)
    (target : Nat) :
    LocalsRefines (setSymLocal symLocals target none)
      (updateLocal concLocals target none) := by
  intro idx sv' hGet
  cases hBeq : (idx == target) with
  | true =>
    have hEq : idx = target := eq_of_beq hBeq
    subst hEq
    rw [getElem?_setSymLocal_same] at hGet
    cases hSlot : symLocals[idx]? with
    | none => rw [hSlot] at hGet; cases hGet
    | some _ => rw [hSlot] at hGet; cases hGet
  | false =>
    have hNe : idx ≠ target := fun h => by
      subst h
      rw [nat_beq_self] at hBeq
      cases hBeq
    rw [getElem?_setSymLocal_diff symLocals target idx none hNe] at hGet
    have ⟨mv', hConc, hRef'⟩ := hRef idx sv' hGet
    refine ⟨mv', ?_, hRef'⟩
    unfold updateLocal
    rw [hBeq]
    exact hConc

theorem getElem?_replicate_none :
    ∀ (n idx : Nat) (sv : SymVal),
      (List.replicate n (none : Option SymVal))[idx]? ≠ some (some sv)
  | 0, _, _, h => by cases h
  | _ + 1, 0, _, h => by cases h
  | n + 1, i + 1, sv, h => getElem?_replicate_none n i sv h

theorem localsRefines_replicate_none (localCount : Nat)
    (concLocals : Nat → Option MirVal) :
    LocalsRefines (List.replicate localCount none) concLocals := by
  intro idx sv hGet
  exact False.elim (getElem?_replicate_none localCount idx sv hGet)

theorem localsRefines_setSymArgsAux :
    ∀ {argSvs : List SymVal} {argMvs : List MirVal},
      Forall2 SymValRefines argSvs argMvs →
      ∀ (idx : Nat) (baseSym : List (Option SymVal)),
        (∀ (i : Nat) (sv : SymVal), baseSym[i]? ≠ some (some sv)) →
        LocalsRefines (setSymArgsAux idx argSvs baseSym)
          (buildCalleeLocalsAux idx argMvs)
  | [], [], .nil, _, baseSym, hBase => by
    intro i sv hGet
    exact False.elim (hBase i sv hGet)
  | _ :: _, _ :: _, .cons hHead hTail, idx, baseSym, hBase => by
    dsimp [setSymArgsAux, buildCalleeLocalsAux]
    exact localsRefines_setSymLocal_some
      (localsRefines_setSymArgsAux hTail (idx + 1) baseSym hBase)
      idx hHead

theorem localsRefines_buildSymCalleeLocals (localCount : Nat)
    {argSvs : List SymVal} {argMvs : List MirVal}
    (hArgs : Forall2 SymValRefines argSvs argMvs) :
    LocalsRefines (buildSymCalleeLocals localCount argSvs)
      (buildCalleeLocals argMvs) :=
  localsRefines_setSymArgsAux hArgs 1 (List.replicate localCount none)
    (getElem?_replicate_none localCount)

theorem evalSymOperand_refines {symLocals : List (Option SymVal)}
    {concLocals : Nat → Option MirVal} (hRef : LocalsRefines symLocals concLocals)
    (op : Operand) {sv : SymVal} {symLocals' : List (Option SymVal)}
    (hSym : evalSymOperand symLocals op = some (sv, symLocals')) :
    ∃ mv concLocals',
      evalOperand concLocals op = some (mv, concLocals') ∧
      SymValRefines sv mv ∧
      LocalsRefines symLocals' concLocals' := by
  cases op with
  | copy src =>
    dsimp [evalSymOperand] at hSym
    cases hGet : symLocals[src.index]? with
    | none => rw [hGet] at hSym; cases hSym
    | some opt =>
      rw [hGet] at hSym
      cases opt with
      | none => cases hSym
      | some sv0 =>
        injection hSym with hPair
        injection hPair with hSv hLoc
        subst hSv; subst hLoc
        have ⟨mv, hConc, hVal⟩ := hRef src.index sv0 hGet
        refine ⟨mv, concLocals, ?_, hVal, hRef⟩
        dsimp [evalOperand]
        rw [hConc]
  | move src =>
    dsimp [evalSymOperand] at hSym
    cases hGet : symLocals[src.index]? with
    | none => rw [hGet] at hSym; cases hSym
    | some opt =>
      rw [hGet] at hSym
      cases opt with
      | none => cases hSym
      | some sv0 =>
        injection hSym with hPair
        injection hPair with hSv hLoc
        subst hSv; subst hLoc
        have ⟨mv, hConc, hVal⟩ := hRef src.index sv0 hGet
        refine ⟨mv, updateLocal concLocals src.index none, ?_, hVal,
          localsRefines_setSymLocal_none hRef src.index⟩
        dsimp [evalOperand]
        rw [hConc]
  | constVal v =>
    dsimp [evalSymOperand] at hSym
    injection hSym with hPair
    injection hPair with hSv hLoc
    subst hSv; subst hLoc
    exact ⟨v, concLocals, rfl, symValRefines_ofMirVal v, hRef⟩

theorem evalSymOperandList_refines :
    ∀ (args : List Operand) {symLocals : List (Option SymVal)}
      {concLocals : Nat → Option MirVal},
      LocalsRefines symLocals concLocals →
      ∀ {argSvs : List SymVal} {symLocals' : List (Option SymVal)},
        evalSymOperandList symLocals args = some (argSvs, symLocals') →
        ∃ argMvs concLocals',
          evalOperandList concLocals args = some (argMvs, concLocals') ∧
          Forall2 SymValRefines argSvs argMvs ∧
          LocalsRefines symLocals' concLocals'
  | [], _, concLocals, hRef, _, _, hSym => by
    dsimp [evalSymOperandList] at hSym
    injection hSym with hPair
    injection hPair with hSvs hLoc
    subst hSvs; subst hLoc
    exact ⟨[], concLocals, rfl, .nil, hRef⟩
  | op :: rest, symLocals, _, hRef, _, _, hSym => by
    dsimp [evalSymOperandList] at hSym
    cases hOp : evalSymOperand symLocals op with
    | none => rw [hOp] at hSym; cases hSym
    | some p1 =>
      rw [hOp] at hSym
      dsimp at hSym
      cases hRest : evalSymOperandList p1.2 rest with
      | none => rw [hRest] at hSym; cases hSym
      | some p2 =>
        rw [hRest] at hSym
        injection hSym with hPair
        injection hPair with hSvs hLoc
        subst hSvs; subst hLoc
        have ⟨mv, concLocals1, hConcOp, hVal, hRef1⟩ :=
          evalSymOperand_refines hRef op hOp
        have ⟨mvs, concLocals2, hConcRest, hVals, hRef2⟩ :=
          evalSymOperandList_refines rest hRef1 hRest
        refine ⟨mv :: mvs, concLocals2, ?_, .cons hVal hVals, hRef2⟩
        dsimp [evalOperandList]
        rw [hConcOp]
        dsimp
        rw [hConcRest]

theorem evalSymBinOp_refines (op : BinOp) {sv1 sv2 res : SymVal} {mv1 mv2 : MirVal}
    (h1 : SymValRefines sv1 mv1) (h2 : SymValRefines sv2 mv2)
    (hSym : evalSymBinOp op sv1 sv2 = some res) :
    ∃ mres, evalBinOp op mv1 mv2 = some mres ∧ SymValRefines res mres := by
  subst h1; subst h2
  cases sv1 with
  | bool _ | unit | tupleUsizeBool _ _ => cases hSym
  | usize n1 =>
    cases sv2 with
    | bool _ | unit | tupleUsizeBool _ _ => cases hSym
    | usize n2 =>
      cases op <;> (
        dsimp [evalSymBinOp] at hSym
        injection hSym with hRes
        subst hRes
        exact ⟨_, rfl, rfl⟩
      )

theorem evalSymCheckedBinOp_refines (op : CheckedBinOp) {sv1 sv2 res : SymVal}
    {mv1 mv2 : MirVal} (h1 : SymValRefines sv1 mv1) (h2 : SymValRefines sv2 mv2)
    (hSym : evalSymCheckedBinOp op sv1 sv2 = some res) :
    ∃ mres, evalCheckedBinOp op mv1 mv2 = some mres ∧ SymValRefines res mres := by
  subst h1; subst h2
  cases sv1 with
  | bool _ | unit | tupleUsizeBool _ _ => cases hSym
  | usize n1 =>
    cases sv2 with
    | bool _ | unit | tupleUsizeBool _ _ => cases hSym
    | usize n2 =>
      cases op <;> (
        dsimp [evalSymCheckedBinOp] at hSym
        injection hSym with hRes
        subst hRes
        exact ⟨_, rfl, rfl⟩
      )

theorem evalSymStmt_refines {body : MirBody} {sym sym' : SymState} {conc : MirState}
    (hState : SymStateRefines body sym conc) (stmt : Stmt)
    (hSym : evalSymStmt sym stmt = some sym') :
    ∃ conc',
      evalMirStmt conc stmt = .step () conc' ∧
      SymStateRefines body sym' conc' ∧
      conc'.frames = conc.frames := by
  have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalSymStmt] at hSym
      cases hOp : evalSymOperand sym.locals op with
      | none => rw [hOp] at hSym; cases hSym
      | some p =>
        rw [hOp] at hSym
        injection hSym with hSym'
        subst hSym'
        have ⟨mv, concLocals1, hConcOp, hVal, hRef1⟩ :=
          evalSymOperand_refines hLoc op hOp
        refine ⟨{ conc with
          locals := updateLocal concLocals1 dst.index (some mv)
          stmtIdx := conc.stmtIdx + 1
        }, ?_, ⟨hBody, hBlk, congrArg (· + 1) hIdx,
          localsRefines_setSymLocal_some hRef1 dst.index hVal⟩, rfl⟩
        dsimp [evalMirStmt]
        rw [hConcOp]
    | binaryOp op lhs rhs =>
      dsimp [evalSymStmt] at hSym
      cases hOp1 : evalSymOperand sym.locals lhs with
      | none => rw [hOp1] at hSym; cases hSym
      | some p1 =>
        rw [hOp1] at hSym
        dsimp at hSym
        cases hOp2 : evalSymOperand p1.2 rhs with
        | none => rw [hOp2] at hSym; cases hSym
        | some p2 =>
          rw [hOp2] at hSym
          dsimp at hSym
          cases hBin : evalSymBinOp op p1.1 p2.1 with
          | none => rw [hBin] at hSym; cases hSym
          | some res =>
            rw [hBin] at hSym
            injection hSym with hSym'
            subst hSym'
            have ⟨mv1, concLocals1, hConc1, hVal1, hRef1⟩ :=
              evalSymOperand_refines hLoc lhs hOp1
            have ⟨mv2, concLocals2, hConc2, hVal2, hRef2⟩ :=
              evalSymOperand_refines hRef1 rhs hOp2
            have ⟨mres, hConcBin, hValRes⟩ :=
              evalSymBinOp_refines op hVal1 hVal2 hBin
            refine ⟨{ conc with
              locals := updateLocal concLocals2 dst.index (some mres)
              stmtIdx := conc.stmtIdx + 1
            }, ?_, ⟨hBody, hBlk, congrArg (· + 1) hIdx,
              localsRefines_setSymLocal_some hRef2 dst.index hValRes⟩, rfl⟩
            dsimp [evalMirStmt]
            rw [hConc1]; dsimp; rw [hConc2]; dsimp; rw [hConcBin]
    | checkedBinaryOp op lhs rhs =>
      dsimp [evalSymStmt] at hSym
      cases hOp1 : evalSymOperand sym.locals lhs with
      | none => rw [hOp1] at hSym; cases hSym
      | some p1 =>
        rw [hOp1] at hSym
        dsimp at hSym
        cases hOp2 : evalSymOperand p1.2 rhs with
        | none => rw [hOp2] at hSym; cases hSym
        | some p2 =>
          rw [hOp2] at hSym
          dsimp at hSym
          cases hBin : evalSymCheckedBinOp op p1.1 p2.1 with
          | none => rw [hBin] at hSym; cases hSym
          | some res =>
            rw [hBin] at hSym
            injection hSym with hSym'
            subst hSym'
            have ⟨mv1, concLocals1, hConc1, hVal1, hRef1⟩ :=
              evalSymOperand_refines hLoc lhs hOp1
            have ⟨mv2, concLocals2, hConc2, hVal2, hRef2⟩ :=
              evalSymOperand_refines hRef1 rhs hOp2
            have ⟨mres, hConcBin, hValRes⟩ :=
              evalSymCheckedBinOp_refines op hVal1 hVal2 hBin
            refine ⟨{ conc with
              locals := updateLocal concLocals2 dst.index (some mres)
              stmtIdx := conc.stmtIdx + 1
            }, ?_, ⟨hBody, hBlk, congrArg (· + 1) hIdx,
              localsRefines_setSymLocal_some hRef2 dst.index hValRes⟩, rfl⟩
            dsimp [evalMirStmt]
            rw [hConc1]; dsimp; rw [hConc2]; dsimp; rw [hConcBin]
    | proj0 src =>
      dsimp [evalSymStmt] at hSym
      cases hGet : sym.locals[src.index]? with
      | none => rw [hGet] at hSym; cases hSym
      | some opt =>
        rw [hGet] at hSym
        cases opt with
        | none => cases hSym
        | some sv =>
          cases sv with
          | usize _ | bool _ | unit => cases hSym
          | tupleUsizeBool val ov =>
            injection hSym with hSym'
            subst hSym'
            have ⟨mv, hConc, hVal⟩ := hLoc src.index (.tupleUsizeBool val ov) hGet
            subst hVal
            dsimp [SymVal.toMirVal] at hConc
            refine ⟨{ conc with
              locals := updateLocal conc.locals dst.index (some (.usize val))
              stmtIdx := conc.stmtIdx + 1
            }, ?_, ⟨hBody, hBlk, congrArg (· + 1) hIdx,
              localsRefines_setSymLocal_some hLoc dst.index rfl⟩, rfl⟩
            dsimp [evalMirStmt]
            rw [hConc]
    | proj1 src =>
      dsimp [evalSymStmt] at hSym
      cases hGet : sym.locals[src.index]? with
      | none => rw [hGet] at hSym; cases hSym
      | some opt =>
        rw [hGet] at hSym
        cases opt with
        | none => cases hSym
        | some sv =>
          cases sv with
          | usize _ | bool _ | unit => cases hSym
          | tupleUsizeBool val ov =>
            injection hSym with hSym'
            subst hSym'
            have ⟨mv, hConc, hVal⟩ := hLoc src.index (.tupleUsizeBool val ov) hGet
            subst hVal
            dsimp [SymVal.toMirVal] at hConc
            refine ⟨{ conc with
              locals := updateLocal conc.locals dst.index (some (.bool ov))
              stmtIdx := conc.stmtIdx + 1
            }, ?_, ⟨hBody, hBlk, congrArg (· + 1) hIdx,
              localsRefines_setSymLocal_some hLoc dst.index rfl⟩, rfl⟩
            dsimp [evalMirStmt]
            rw [hConc]
  | storageLive loc =>
    dsimp [evalSymStmt] at hSym
    injection hSym with hSym'
    subst hSym'
    exact ⟨{ conc with
      locals := updateLocal conc.locals loc.index none
      stmtIdx := conc.stmtIdx + 1
    }, rfl, ⟨hBody, hBlk, congrArg (· + 1) hIdx,
      localsRefines_setSymLocal_none hLoc loc.index⟩, rfl⟩
  | storageDead loc =>
    dsimp [evalSymStmt] at hSym
    injection hSym with hSym'
    subst hSym'
    exact ⟨{ conc with
      locals := updateLocal conc.locals loc.index none
      stmtIdx := conc.stmtIdx + 1
    }, rfl, ⟨hBody, hBlk, congrArg (· + 1) hIdx,
      localsRefines_setSymLocal_none hLoc loc.index⟩, rfl⟩
  | nop =>
    dsimp [evalSymStmt] at hSym
    injection hSym with hSym'
    subst hSym'
    exact ⟨{ conc with stmtIdx := conc.stmtIdx + 1 }, rfl,
      ⟨hBody, hBlk, congrArg (· + 1) hIdx, hLoc⟩, rfl⟩

/-- Semantic soundness contract of a modular `CalleeSummary` with respect to
    `env : CrateEnv`:
    1. `lookupFn env summary.name` resolves to a `calleeBody` whose `argTys`
       and `retTy` match `summary`.
    2. Whenever `summary.eval argSvs = some (false, callRetSv)` for type-valid
       symbolic arguments `argSvs` refined by `argMvs`, executing `calleeBody`
       from block `0`, statement `0` above any caller frame stack `frames` is
       `SafeFrom` for any `finalVal` satisfied by `ReturnCont env frames`. -/
def SummaryEntrySound (env : CrateEnv) (summary : CalleeSummary) : Prop :=
  ∃ calleeBody : MirBody,
    lookupFn env summary.name = some calleeBody ∧
    calleeBody.argTys = summary.argTys ∧
    calleeBody.retTy = summary.retTy ∧
    ∀ (argSvs : List SymVal) (argMvs : List MirVal) (callRetSv : SymVal)
      (mem : MemState) (frames : List CallFrame) (finalVal : MirVal),
      symArgsHaveTysBool argSvs summary.argTys = true →
      Forall2 SymValRefines argSvs argMvs →
      summary.eval argSvs = some (false, callRetSv) →
      (∀ callRetMv, SymValRefines callRetSv callRetMv →
        ReturnCont env frames callRetMv finalVal) →
      SafeFrom env
        { curBody := calleeBody
          locals := buildCalleeLocals argMvs
          mem := mem
          block := 0
          stmtIdx := 0
          frames := frames }
        finalVal

/-- Soundness of a `SummaryEnv` with respect to `env : CrateEnv`. -/
def SummarySoundForEnv (env : CrateEnv) (summaries : SummaryEnv) : Prop :=
  ∀ (name : String) (summary : CalleeSummary),
    lookupSummary summaries name = some summary →
    summary.name = name ∧ SummaryEntrySound env summary

/-- **Master Frame-Stack Soundness Theorem (`evalSymState_sound`)**:
    If `evalSymState env summaries plan body sym = some (false, retSv)`, then
    every concrete `MirState` `conc` refining `sym` in `body` whose caller stack
    `conc.frames` satisfies `ReturnCont` for `retSv` is `SafeFrom` in
    `MirMachine`.

    Handles both Mode A (`.callInline calleePlan afterCall`) and Mode B
    (`.callSummary afterCall`) in a single structural induction on `plan`. -/
theorem evalSymState_sound (env : CrateEnv) (summaries : SummaryEnv)
    (hSum : SummarySoundForEnv env summaries) :
    ∀ (plan : TransPlan) (body : MirBody) (sym : SymState) (conc : MirState)
      (failed : Bool) (retSv : SymVal) (finalVal : MirVal),
      evalSymState env summaries plan body sym = some (failed, retSv) →
      failed = false →
      SymStateRefines body sym conc →
      (∀ retMv, SymValRefines retSv retMv →
        ReturnCont env conc.frames retMv finalVal) →
      SafeFrom env conc finalVal
  | .return_, body, sym, conc, failed, retSv, finalVal, hEval, _, hState, hCont => by
    have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
    dsimp [evalSymState] at hEval
    cases hBb : body.blocks[sym.block]? with
    | none => rw [hBb] at hEval; cases hEval
    | some bb =>
      rw [hBb] at hEval
      dsimp at hEval
      cases hStmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hStmt] at hEval; cases hEval
      | none =>
        rw [hStmt] at hEval
        dsimp at hEval
        cases hTerm : bb.terminator with
        | goto _ | unreachable | panic | call _ _ _ _ | switchInt _ _ _
        | assertNotOverflow _ _ =>
          rw [hTerm] at hEval; cases hEval
        | return_ =>
          rw [hTerm] at hEval
          dsimp at hEval
          cases hRet0 : sym.locals[0]? with
          | none => rw [hRet0] at hEval; cases hEval
          | some opt0 =>
            rw [hRet0] at hEval
            cases opt0 with
            | none => cases hEval
            | some sv0 =>
              injection hEval with hPair
              injection hPair with _ hSv
              subst hSv
              have ⟨retMv, hConc0, hVal0⟩ := hLoc 0 sv0 hRet0
              apply safeFrom_of_returnCont _ hConc0 (hCont retMv hVal0)
              unfold evalMirStep
              rw [hBody, ← hBlk, hBb]
              dsimp
              rw [← hIdx, hStmt, hTerm]
  | .step nextPlan, body, sym, conc, failed, retSv, finalVal, hEval, hNoFail, hState, hCont => by
    have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
    dsimp [evalSymState] at hEval
    cases hBb : body.blocks[sym.block]? with
    | none => rw [hBb] at hEval; cases hEval
    | some bb =>
      rw [hBb] at hEval
      dsimp at hEval
      cases hStmt : bb.stmts[sym.stmtIdx]? with
      | none => rw [hStmt] at hEval; cases hEval
      | some stmt =>
        rw [hStmt] at hEval
        dsimp at hEval
        cases hSymStmt : evalSymStmt sym stmt with
        | none => rw [hSymStmt] at hEval; cases hEval
        | some sym' =>
          rw [hSymStmt] at hEval
          have ⟨conc', hConcStmt, hState', hFrames'⟩ :=
            evalSymStmt_refines ⟨hBody, hBlk, hIdx, hLoc⟩ stmt hSymStmt
          apply safeFrom_step (s' := conc')
          · unfold evalMirStep
            rw [hBody, ← hBlk, hBb]
            dsimp
            rw [← hIdx, hStmt]
            exact hConcStmt
          · exact evalSymState_sound env summaries hSum nextPlan body sym' conc'
              failed retSv finalVal hEval hNoFail hState'
              (fun retMv hVal => by rw [hFrames']; exact hCont retMv hVal)
  | .goto nextPlan, body, sym, conc, failed, retSv, finalVal, hEval, hNoFail, hState, hCont => by
    have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
    dsimp [evalSymState] at hEval
    cases hBb : body.blocks[sym.block]? with
    | none => rw [hBb] at hEval; cases hEval
    | some bb =>
      rw [hBb] at hEval
      dsimp at hEval
      cases hStmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hStmt] at hEval; cases hEval
      | none =>
        rw [hStmt] at hEval
        dsimp at hEval
        cases hTerm : bb.terminator with
        | return_ | unreachable | panic | call _ _ _ _ | switchInt _ _ _
        | assertNotOverflow _ _ =>
          rw [hTerm] at hEval; cases hEval
        | goto target =>
          rw [hTerm] at hEval
          have hBb' : conc.curBody.blocks[conc.block]? = some bb := by
            rw [hBody, ← hBlk, hBb]
          have hStmt' : bb.stmts[conc.stmtIdx]? = none := by
            rw [← hIdx, hStmt]
          apply safeFrom_step (s' := { conc with block := target.index, stmtIdx := 0 })
          · unfold evalMirStep
            rw [hBb']
            dsimp
            rw [hStmt', hTerm]
            rfl
          · exact evalSymState_sound env summaries hSum nextPlan body
              { sym with block := target.index, stmtIdx := 0 }
              { conc with block := target.index, stmtIdx := 0 }
              failed retSv finalVal hEval hNoFail ⟨hBody, rfl, rfl, hLoc⟩ hCont
  | .assertNotOverflow nextPlan, body, sym, conc, failed, retSv, finalVal, hEval, hNoFail, hState, hCont => by
    have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
    dsimp [evalSymState] at hEval
    cases hBb : body.blocks[sym.block]? with
    | none => rw [hBb] at hEval; cases hEval
    | some bb =>
      rw [hBb] at hEval
      dsimp at hEval
      cases hStmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hStmt] at hEval; cases hEval
      | none =>
        rw [hStmt] at hEval
        dsimp at hEval
        cases hTerm : bb.terminator with
        | return_ | goto _ | unreachable | panic | call _ _ _ _ | switchInt _ _ _ =>
          rw [hTerm] at hEval; cases hEval
        | assertNotOverflow tupleLocal target =>
          rw [hTerm] at hEval
          dsimp at hEval
          cases hGet : sym.locals[tupleLocal.index]? with
          | none => rw [hGet] at hEval; cases hEval
          | some opt =>
            rw [hGet] at hEval
            cases opt with
            | none => cases hEval
            | some sv =>
              cases sv with
              | usize _ | bool _ | unit => cases hEval
              | tupleUsizeBool val ov =>
                dsimp at hEval
                cases hNext : evalSymState env summaries nextPlan body
                    { sym with block := target.index, stmtIdx := 0 } with
                | none => rw [hNext] at hEval; cases hEval
                | some resPair =>
                  rw [hNext] at hEval
                  injection hEval with hPair
                  injection hPair with hFailEq hRetEq
                  rw [hNoFail] at hFailEq
                  have ⟨hOvFalse, hRestFalse⟩ :=
                    (orBool_eq_false_iff ov resPair.1).mp hFailEq
                  subst hOvFalse
                  have ⟨mv, hConc, hVal⟩ :=
                    hLoc tupleLocal.index (.tupleUsizeBool val false) hGet
                  subst hVal
                  dsimp [SymVal.toMirVal] at hConc
                  have hBb' : conc.curBody.blocks[conc.block]? = some bb := by
                    rw [hBody, ← hBlk, hBb]
                  have hStmt' : bb.stmts[conc.stmtIdx]? = none := by
                    rw [← hIdx, hStmt]
                  apply safeFrom_step (s' := { conc with block := target.index, stmtIdx := 0 })
                  · unfold evalMirStep
                    rw [hBb']
                    dsimp
                    rw [hStmt', hTerm]
                    dsimp [evalMirTerminator]
                    rw [hConc]
                  · exact evalSymState_sound env summaries hSum nextPlan body
                      { sym with block := target.index, stmtIdx := 0 }
                      { conc with block := target.index, stmtIdx := 0 }
                      resPair.1 resPair.2 finalVal hNext hRestFalse ⟨hBody, rfl, rfl, hLoc⟩
                      (fun retMv hVal => by rw [← hRetEq] at hCont; exact hCont retMv hVal)
  | .branch falsePlan truePlan, body, sym, conc, failed, retSv, finalVal, hEval, hNoFail, hState, hCont => by
    have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
    dsimp [evalSymState] at hEval
    cases hBb : body.blocks[sym.block]? with
    | none => rw [hBb] at hEval; cases hEval
    | some bb =>
      rw [hBb] at hEval
      dsimp at hEval
      cases hStmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hStmt] at hEval; cases hEval
      | none =>
        rw [hStmt] at hEval
        dsimp at hEval
        cases hTerm : bb.terminator with
        | return_ | goto _ | unreachable | panic | call _ _ _ _
        | assertNotOverflow _ _ =>
          rw [hTerm] at hEval; cases hEval
        | switchInt discr falseTarget trueTarget =>
          rw [hTerm] at hEval
          dsimp at hEval
          cases hOp : evalSymOperand sym.locals discr with
          | none => rw [hOp] at hEval; cases hEval
          | some p =>
            rw [hOp] at hEval
            cases p with
            | mk pv locals' =>
              cases pv with
              | usize _ | unit | tupleUsizeBool _ _ => cases hEval
              | bool cond =>
                dsimp at hEval
                cases hF : evalSymState env summaries falsePlan body
                    { sym with locals := locals', block := falseTarget.index, stmtIdx := 0 } with
                | none => rw [hF] at hEval; cases hEval
                | some fRes =>
                  rw [hF] at hEval
                  cases hT : evalSymState env summaries truePlan body
                      { sym with locals := locals', block := trueTarget.index, stmtIdx := 0 } with
                  | none => rw [hT] at hEval; cases hEval
                  | some tRes =>
                    rw [hT] at hEval
                    dsimp at hEval
                    cases hMerge : mergeBranchSymVal cond fRes.2 tRes.2 with
                    | none => rw [hMerge] at hEval; cases hEval
                    | some mergedVal =>
                      rw [hMerge] at hEval
                      injection hEval with hPair
                      injection hPair with hFailEq hRetEq
                      subst hRetEq
                      have ⟨mv, concLocals', hConcOp, hVal, hRef'⟩ :=
                        evalSymOperand_refines hLoc discr hOp
                      subst hVal
                      dsimp [SymVal.toMirVal] at hConcOp
                      have hBb' : conc.curBody.blocks[conc.block]? = some bb := by
                        rw [hBody, ← hBlk, hBb]
                      have hStmt' : bb.stmts[conc.stmtIdx]? = none := by
                        rw [← hIdx, hStmt]
                      cases cond with
                      | false =>
                        have hMergedEq : mergedVal = fRes.2 :=
                          mergeBranchSymVal_false hMerge
                        subst hMergedEq
                        have hFFail : fRes.1 = false := by
                          dsimp at hFailEq
                          exact hFailEq.trans hNoFail
                        apply safeFrom_step (s' := { conc with
                          locals := concLocals'
                          block := falseTarget.index
                          stmtIdx := 0
                        })
                        · unfold evalMirStep
                          rw [hBb']
                          dsimp
                          rw [hStmt', hTerm]
                          dsimp [evalMirTerminator]
                          rw [hConcOp]
                        · exact evalSymState_sound env summaries hSum falsePlan body
                            { sym with locals := locals', block := falseTarget.index, stmtIdx := 0 }
                            { conc with locals := concLocals', block := falseTarget.index, stmtIdx := 0 }
                            fRes.1 fRes.2 finalVal hF hFFail ⟨hBody, rfl, rfl, hRef'⟩ hCont
                      | true =>
                        have hMergedEq : mergedVal = tRes.2 :=
                          mergeBranchSymVal_true hMerge
                        subst hMergedEq
                        have hTFail : tRes.1 = false := by
                          dsimp at hFailEq
                          exact hFailEq.trans hNoFail
                        apply safeFrom_step (s' := { conc with
                          locals := concLocals'
                          block := trueTarget.index
                          stmtIdx := 0
                        })
                        · unfold evalMirStep
                          rw [hBb']
                          dsimp
                          rw [hStmt', hTerm]
                          dsimp [evalMirTerminator]
                          rw [hConcOp]
                        · exact evalSymState_sound env summaries hSum truePlan body
                            { sym with locals := locals', block := trueTarget.index, stmtIdx := 0 }
                            { conc with locals := concLocals', block := trueTarget.index, stmtIdx := 0 }
                            tRes.1 tRes.2 finalVal hT hTFail ⟨hBody, rfl, rfl, hRef'⟩ hCont
  | .callInline calleePlan afterCall, body, sym, conc, failed, retSv, finalVal, hEval, hNoFail, hState, hCont => by
    have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
    dsimp [evalSymState] at hEval
    cases hBb : body.blocks[sym.block]? with
    | none => rw [hBb] at hEval; cases hEval
    | some bb =>
      rw [hBb] at hEval
      dsimp at hEval
      cases hStmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hStmt] at hEval; cases hEval
      | none =>
        rw [hStmt] at hEval
        dsimp at hEval
        cases hTerm : bb.terminator with
        | return_ | goto _ | unreachable | panic | switchInt _ _ _
        | assertNotOverflow _ _ =>
          rw [hTerm] at hEval; cases hEval
        | call dst callee args target =>
          rw [hTerm] at hEval
          dsimp at hEval
          cases hArgs : evalSymOperandList sym.locals args with
          | none => rw [hArgs] at hEval; cases hEval
          | some pArgs =>
            rw [hArgs] at hEval
            dsimp at hEval
            cases hLook : lookupFn env callee with
            | none => rw [hLook] at hEval; cases hEval
            | some calleeBody =>
              rw [hLook] at hEval
              dsimp at hEval
              cases hTys : symArgsHaveTysBool pArgs.1 calleeBody.argTys with
              | false => rw [hTys] at hEval; cases hEval
              | true =>
                rw [hTys] at hEval
                dsimp at hEval
                cases hCalleeEval : evalSymState env summaries calleePlan calleeBody
                    (initSymState calleeBody pArgs.1) with
                | none => rw [hCalleeEval] at hEval; cases hEval
                | some calleeRes =>
                  rw [hCalleeEval] at hEval
                  dsimp at hEval
                  cases hAfterEval : evalSymState env summaries afterCall body
                      { locals := setSymLocal pArgs.2 dst.index (some calleeRes.2)
                        block := target.index
                        stmtIdx := 0 } with
                  | none => rw [hAfterEval] at hEval; cases hEval
                  | some afterRes =>
                    rw [hAfterEval] at hEval
                    injection hEval with hPair
                    injection hPair with hFailEq hRetEq
                    rw [hNoFail] at hFailEq
                    have ⟨hCalleeNoFail, hAfterNoFail⟩ :=
                      (orBool_eq_false_iff calleeRes.1 afterRes.1).mp hFailEq
                    have ⟨argMvs, concLocalsAfterArgs, hConcArgs, hArgRefs, hLocAfter⟩ :=
                      evalSymOperandList_refines args hLoc hArgs
                    have hConcTys : argsHaveTysBool argMvs calleeBody.argTys = true := by
                      rw [argsHaveTysBool_of_forall2 hArgRefs calleeBody.argTys]
                      exact hTys
                    have hBb' : conc.curBody.blocks[conc.block]? = some bb := by
                      rw [hBody, ← hBlk, hBb]
                    have hStmt' : bb.stmts[conc.stmtIdx]? = none := by
                      rw [← hIdx, hStmt]
                    let frame : CallFrame := {
                      callerBody := conc.curBody
                      dst := dst
                      returnTarget := target
                      callerLocals := concLocalsAfterArgs
                    }
                    let calleeConc : MirState := {
                      curBody := calleeBody
                      locals := buildCalleeLocals argMvs
                      mem := conc.mem
                      block := 0
                      stmtIdx := 0
                      frames := frame :: conc.frames
                    }
                    apply safeFrom_step (s' := calleeConc)
                    · unfold evalMirStep
                      rw [hBb']
                      dsimp
                      rw [hStmt', hTerm]
                      dsimp [evalMirTerminator]
                      rw [hConcArgs]
                      dsimp
                      rw [hLook]
                      dsimp
                      rw [hConcTys]
                      rfl
                    · apply evalSymState_sound env summaries hSum calleePlan calleeBody
                        (initSymState calleeBody pArgs.1) calleeConc
                        calleeRes.1 calleeRes.2 finalVal hCalleeEval hCalleeNoFail
                      · exact ⟨rfl, rfl, rfl,
                          localsRefines_buildSymCalleeLocals calleeBody.localCount hArgRefs⟩
                      · intro callRetMv hCallRetRef mem'
                        exact evalSymState_sound env summaries hSum afterCall body
                          { locals := setSymLocal pArgs.2 dst.index (some calleeRes.2)
                            block := target.index
                            stmtIdx := 0 }
                          { curBody := conc.curBody
                            locals := updateLocal concLocalsAfterArgs dst.index (some callRetMv)
                            mem := mem'
                            block := target.index
                            stmtIdx := 0
                            frames := conc.frames }
                          afterRes.1 afterRes.2 finalVal hAfterEval hAfterNoFail
                          ⟨hBody, rfl, rfl,
                            localsRefines_setSymLocal_some hLocAfter dst.index hCallRetRef⟩
                          (fun retMv hVal => by rw [← hRetEq] at hCont; exact hCont retMv hVal)
  | .callSummary afterCall, body, sym, conc, failed, retSv, finalVal, hEval, hNoFail, hState, hCont => by
    have ⟨hBody, hBlk, hIdx, hLoc⟩ := hState
    dsimp [evalSymState] at hEval
    cases hBb : body.blocks[sym.block]? with
    | none => rw [hBb] at hEval; cases hEval
    | some bb =>
      rw [hBb] at hEval
      dsimp at hEval
      cases hStmt : bb.stmts[sym.stmtIdx]? with
      | some _ => rw [hStmt] at hEval; cases hEval
      | none =>
        rw [hStmt] at hEval
        dsimp at hEval
        cases hTerm : bb.terminator with
        | return_ | goto _ | unreachable | panic | switchInt _ _ _
        | assertNotOverflow _ _ =>
          rw [hTerm] at hEval; cases hEval
        | call dst callee args target =>
          rw [hTerm] at hEval
          dsimp at hEval
          cases hArgs : evalSymOperandList sym.locals args with
          | none => rw [hArgs] at hEval; cases hEval
          | some pArgs =>
            rw [hArgs] at hEval
            dsimp at hEval
            cases hLookSum : lookupSummary summaries callee with
            | none => rw [hLookSum] at hEval; cases hEval
            | some summary =>
              rw [hLookSum] at hEval
              dsimp at hEval
              cases hTys : symArgsHaveTysBool pArgs.1 summary.argTys with
              | false => rw [hTys] at hEval; cases hEval
              | true =>
                rw [hTys] at hEval
                dsimp at hEval
                cases hSumEval : summary.eval pArgs.1 with
                | none => rw [hSumEval] at hEval; cases hEval
                | some calleeRes =>
                  rw [hSumEval] at hEval
                  dsimp at hEval
                  cases hAfterEval : evalSymState env summaries afterCall body
                      { locals := setSymLocal pArgs.2 dst.index (some calleeRes.2)
                        block := target.index
                        stmtIdx := 0 } with
                  | none => rw [hAfterEval] at hEval; cases hEval
                  | some afterRes =>
                    rw [hAfterEval] at hEval
                    injection hEval with hPair
                    injection hPair with hFailEq hRetEq
                    rw [hNoFail] at hFailEq
                    have ⟨hCalleeNoFail, hAfterNoFail⟩ :=
                      (orBool_eq_false_iff calleeRes.1 afterRes.1).mp hFailEq
                    have ⟨hNameEq, calleeBody, hLookFn, hArgTysEq, _, hSumRun⟩ :=
                      hSum callee summary hLookSum
                    rw [hNameEq] at hLookFn
                    have ⟨argMvs, concLocalsAfterArgs, hConcArgs, hArgRefs, hLocAfter⟩ :=
                      evalSymOperandList_refines args hLoc hArgs
                    have hConcTys : argsHaveTysBool argMvs calleeBody.argTys = true := by
                      rw [hArgTysEq, argsHaveTysBool_of_forall2 hArgRefs summary.argTys]
                      exact hTys
                    have hBb' : conc.curBody.blocks[conc.block]? = some bb := by
                      rw [hBody, ← hBlk, hBb]
                    have hStmt' : bb.stmts[conc.stmtIdx]? = none := by
                      rw [← hIdx, hStmt]
                    let frame : CallFrame := {
                      callerBody := conc.curBody
                      dst := dst
                      returnTarget := target
                      callerLocals := concLocalsAfterArgs
                    }
                    let calleeConc : MirState := {
                      curBody := calleeBody
                      locals := buildCalleeLocals argMvs
                      mem := conc.mem
                      block := 0
                      stmtIdx := 0
                      frames := frame :: conc.frames
                    }
                    apply safeFrom_step (s' := calleeConc)
                    · unfold evalMirStep
                      rw [hBb']
                      dsimp
                      rw [hStmt', hTerm]
                      dsimp [evalMirTerminator]
                      rw [hConcArgs]
                      dsimp
                      rw [hLookFn]
                      dsimp
                      rw [hConcTys]
                      rfl
                    · cases calleeRes with
                      | mk cFail cRetSv =>
                        dsimp at hCalleeNoFail
                        subst hCalleeNoFail
                        apply hSumRun pArgs.1 argMvs cRetSv conc.mem (frame :: conc.frames)
                          finalVal hTys hArgRefs hSumEval
                        intro callRetMv hCallRetRef mem'
                        exact evalSymState_sound env summaries hSum afterCall body
                          { locals := setSymLocal pArgs.2 dst.index (some cRetSv)
                            block := target.index
                            stmtIdx := 0 }
                          { curBody := conc.curBody
                            locals := updateLocal concLocalsAfterArgs dst.index (some callRetMv)
                            mem := mem'
                            block := target.index
                            stmtIdx := 0
                            frames := conc.frames }
                          afterRes.1 afterRes.2 finalVal hAfterEval hAfterNoFail
                          ⟨hBody, rfl, rfl,
                            localsRefines_setSymLocal_some hLocAfter dst.index hCallRetRef⟩
                          (fun retMv hVal => by rw [← hRetEq] at hCont; exact hCont retMv hVal)

/-- **Top-Level `evalSym_sound` Bridge**:
    If `evalSym env summaries plan body args = some retSv`, then for any root
    concrete initial state `conc` of `body` refining `initSymState body args`,
    every finite execution prefix of `MirMachine` is safe and terminates only
    with `.normal retSv.toMirVal`. -/
theorem evalSym_sound (env : CrateEnv) (summaries : SummaryEnv)
    (hSum : SummarySoundForEnv env summaries)
    {plan : TransPlan} {body : MirBody} {args : List SymVal} {retSv : SymVal}
    {conc : MirState}
    (hEval : evalSym env summaries plan body args = some retSv)
    (hFrames : conc.frames = [])
    (hState : SymStateRefines body (initSymState body args) conc) :
    SafeFrom env conc retSv.toMirVal := by
  unfold evalSym at hEval
  cases hSt : evalSymState env summaries plan body (initSymState body args) with
  | none => rw [hSt] at hEval; cases hEval
  | some p =>
    rw [hSt] at hEval
    cases p with
    | mk failed val =>
      cases failed with
      | true => cases hEval
      | false =>
        injection hEval with hRet
        subst hRet
        exact evalSymState_sound env summaries hSum plan body
          (initSymState body args) conc false val val.toMirVal hSt rfl hState
          (fun retMv hVal => by
            rw [hFrames]
            exact hVal)

/-- **Deliverable 2b Bridge (`summaryEntrySound_of_evalSymState`)**:
    Any `CalleeSummary` whose `.eval` function agrees with `evalSymState` on
    `calleeBody` is automatically sound (`SummaryEntrySound env summary`). -/
theorem summaryEntrySound_of_evalSymState (env : CrateEnv)
    (summaries : SummaryEnv) (hSum : SummarySoundForEnv env summaries)
    (summary : CalleeSummary) (calleeBody : MirBody) (calleePlan : TransPlan)
    (hLook : lookupFn env summary.name = some calleeBody)
    (hArgTys : calleeBody.argTys = summary.argTys)
    (hRetTy : calleeBody.retTy = summary.retTy)
    (hEvalEq : ∀ argSvs,
      symArgsHaveTysBool argSvs summary.argTys = true →
      summary.eval argSvs =
        evalSymState env summaries calleePlan calleeBody
          (initSymState calleeBody argSvs)) :
    SummaryEntrySound env summary := by
  refine ⟨calleeBody, hLook, hArgTys, hRetTy, ?_⟩
  intro argSvs argMvs callRetSv mem frames finalVal hTys hArgRefs hSumEval hCont
  rw [hEvalEq argSvs hTys] at hSumEval
  exact evalSymState_sound env summaries hSum calleePlan calleeBody
    (initSymState calleeBody argSvs)
    { curBody := calleeBody
      locals := buildCalleeLocals argMvs
      mem := mem
      block := 0
      stmtIdx := 0
      frames := frames }
    false callRetSv finalVal hSumEval rfl
    ⟨rfl, rfl, rfl, localsRefines_buildSymCalleeLocals calleeBody.localCount hArgRefs⟩
    hCont


/-!
## 7. End-to-End Verification Case Studies (Mode A, Mode B, and Transitive PME)
-/

/-- Pointwise local refinement helper for concrete initial states
    (`initMirState`), where `concLocals target = some mv` is already satisfied
    without modifying `concLocals`. -/
theorem localsRefines_setSymLocal_point {symLocals : List (Option SymVal)}
    {concLocals : Nat → Option MirVal} (hRef : LocalsRefines symLocals concLocals)
    (target : Nat) {sv : SymVal} {mv : MirVal}
    (hConc : concLocals target = some mv) (hVal : SymValRefines sv mv) :
    LocalsRefines (setSymLocal symLocals target (some sv)) concLocals := by
  intro idx sv' hGet
  cases hBeq : (idx == target) with
  | true =>
    have hEq : idx = target := eq_of_beq hBeq
    subst hEq
    rw [getElem?_setSymLocal_same] at hGet
    cases hSlot : symLocals[idx]? with
    | none => rw [hSlot] at hGet; cases hGet
    | some _ =>
      rw [hSlot] at hGet
      injection hGet with hOpt
      injection hOpt with hSv
      subst hSv
      exact ⟨mv, hConc, hVal⟩
  | false =>
    have hNe : idx ≠ target := fun h => by
      subst h
      rw [nat_beq_self] at hBeq
      cases hBeq
    rw [getElem?_setSymLocal_diff symLocals target idx (some sv) hNe] at hGet
    exact hRef idx sv' hGet

/-- Initial state refinement for any 1-parameter `usize` function. -/
theorem symStateRefines_init_1 {body : MirBody} {s : MirState}
    (hArgTys : body.argTys = [.usize])
    (hInit : initMirState body s) :
    ∃ x : Nat,
      s.locals 1 = some (.usize x) ∧
      s.frames = [] ∧
      SymStateRefines body (initSymState body [.usize x]) s := by
  have ⟨hBody, hFrames, hBlk, hIdx, _, hArgs⟩ := hInit
  rw [hArgTys] at hArgs
  have ⟨⟨v1, hLoc1, hTy1⟩, _⟩ := hArgs
  cases v1 with
  | bool _ | unit | tupleUsizeBool _ _ => cases hTy1
  | usize x =>
    refine ⟨x, hLoc1, hFrames, hBody, hBlk.symm, hIdx.symm, ?_⟩
    unfold initSymState buildSymCalleeLocals setSymArgsAux
    exact localsRefines_setSymLocal_point
      (localsRefines_replicate_none body.localCount s.locals) 1 hLoc1 rfl

/-- Initial state refinement for any 2-parameter `(usize, usize)` function. -/
theorem symStateRefines_init_2 {body : MirBody} {s : MirState}
    (hArgTys : body.argTys = [.usize, .usize])
    (hInit : initMirState body s) :
    ∃ x y : Nat,
      s.locals 1 = some (.usize x) ∧
      s.locals 2 = some (.usize y) ∧
      s.frames = [] ∧
      SymStateRefines body (initSymState body [.usize x, .usize y]) s := by
  have ⟨hBody, hFrames, hBlk, hIdx, _, hArgs⟩ := hInit
  rw [hArgTys] at hArgs
  have ⟨⟨v1, hLoc1, hTy1⟩, ⟨v2, hLoc2, hTy2⟩, _⟩ := hArgs
  cases v1 with
  | bool _ | unit | tupleUsizeBool _ _ => cases hTy1
  | usize x =>
    cases v2 with
    | bool _ | unit | tupleUsizeBool _ _ => cases hTy2
    | usize y =>
      refine ⟨x, y, hLoc1, hLoc2, hFrames, hBody, hBlk.symm, hIdx.symm, ?_⟩
      unfold initSymState buildSymCalleeLocals setSymArgsAux
      exact localsRefines_setSymLocal_point (sv := .usize x)
        (localsRefines_setSymLocal_point (sv := .usize y)
          (localsRefines_replicate_none body.localCount s.locals) 2 hLoc2 rfl)
        1 hLoc1 rfl

/-- Empty summary environment soundness (`SummarySoundForEnv env []`). -/
theorem summarySoundForEnv_nil (env : CrateEnv) :
    SummarySoundForEnv env [] := by
  intro _ _ hLook
  cases hLook

/-- TCB assumption carrier for crate-level verification. -/
inductive TCBItem where
  | rustcRipening
  deriving DecidableEq, Repr

instance : TrustedAssumption TCBItem where
  meaning _ := True

def DefaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed _ := True

/-- Identity compiler on `MirLang`. -/
def IdentityMirCompiler : Compiler MirLang MirLang where
  compile p := p
  π b := b

theorem identityMirCompiler_monotone : Monotone IdentityMirCompiler.π :=
  fun _ _ h => h

theorem identityMirCompiler_soundOn (p : MirProg) :
    IdentityMirCompiler.SoundOn p :=
  ⟨identityMirCompiler_monotone, Preorder.le_refl (MirLang.sem p)⟩

/-- Captured function descriptor in a crate, combining WS3 (`requiredConsts`
    and `mentionedItems` on `body`), WS4 (`isPublic` visibility flag), and WS5
    (`pre` domain precondition and `specs` behavioral contracts). -/
structure CapturedFn where
  name : String
  body : MirBody
  isPublic : Bool := true
  pre : MirLang.Query → Prop := fun _ => True
  specs : List MirLang.Behavior := []
  assumptions : List TCBItem := []

/-- Captured crate comprising all lowered functions (both public entrypoints and
    private helpers). -/
structure Crate where
  fns : List CapturedFn

/-- Build the crate's `CrateEnv` lookup table from all captured functions
    (including private helpers so interprocedural calls resolve). -/
def Crate.toEnv (c : Crate) : CrateEnv :=
  c.fns.map (fun f => { name := f.name, body := f.body })

/-- Filter to the crate's public entrypoints (`isPublic = true`) for Mode A
    crate-level verification, where unannotated private helpers are verified as
    part of their public callers via symbolic inlining. -/
def Crate.publicFns (c : Crate) : List CapturedFn :=
  c.fns.filter (fun f => f.isPublic)

/-- Crate-level theorem over a list of target `CapturedFn`s, requiring both
    transitive `CompileAdmitted` (WS3) and conditional `VerificationResultOn`
    (WS5) for each target function. -/
def AdmittedFnsTheorem
    (C : Compiler MirLang MirLang)
    (policy : TrustPolicy TCBItem)
    (env : CrateEnv)
    (compileFuel : Nat)
    (targets : List CapturedFn) : Prop :=
  AllHold (targets.map (fun f =>
    CompileAdmitted env compileFuel f.body ∧
    VerificationResultOn C policy f.assumptions
      { env := env, body := f.body } f.pre f.specs))

/-- **Mode A Crate Theorem (`PublicAdmittedCrateTheorem`)**:
    Every public function in `c.publicFns` is transitively `CompileAdmitted`
    (which checks `requiredConsts` and `mentionedItems` across all reachable
    private helpers) and satisfies `VerificationResultOn` (discharging private
    helper calls via zero-annotation symbolic inlining). -/
def PublicAdmittedCrateTheorem
    (C : Compiler MirLang MirLang)
    (policy : TrustPolicy TCBItem)
    (compileFuel : Nat)
    (c : Crate) : Prop :=
  AdmittedFnsTheorem C policy c.toEnv compileFuel c.publicFns

/-- **Mode B Crate Theorem (`ModularAdmittedCrateTheorem`)**:
    Every function in `c.fns` (both helpers with conditional contracts and
    callers) is transitively `CompileAdmitted` and satisfies its own
    `VerificationResultOn` obligation. -/
def ModularAdmittedCrateTheorem
    (C : Compiler MirLang MirLang)
    (policy : TrustPolicy TCBItem)
    (compileFuel : Nat)
    (c : Crate) : Prop :=
  AdmittedFnsTheorem C policy c.toEnv compileFuel c.fns

/-!
### 7.1 Concrete MIR Bodies: `add`, `double_guarded`, and `double_conditional`
-/

/-- Lowered `Runtime(PostCleanup)` MIR body for:
    ```rust
    fn add(x: usize, y: usize) -> usize { x + y }
    ```
    Locals: `_0: usize`, `_1: usize (x)`, `_2: usize (y)`,
    `_3: (usize, bool)`, `_4: usize`. -/
def addBody : MirBody where
  argTys := [.usize, .usize]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.checkedBinaryOp .add (.copy ⟨1⟩) (.copy ⟨2⟩)),
        .assign ⟨4⟩ (.proj0 ⟨3⟩)
      ]
      terminator := .assertNotOverflow ⟨3⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨0⟩ (.use (.move ⟨4⟩))
      ]
      terminator := .return_ }
  ]
  requiredConsts := []
  mentionedItems := []

/-- Lowered `Runtime(PostCleanup)` MIR body for:
    ```rust
    pub fn double_guarded(x: usize) -> usize {
        if x <= 1000 { add(x, x) } else { 0 }
    }
    ```
    Locals: `_0: usize`, `_1: usize (x)`, `_2: bool`, `_3: usize`. -/
def doubleGuardedBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 4
  blocks := [
    -- bb0: _2 = Le(copy _1, const 1000usize);
    --      switchInt(move _2) -> [false: bb1, true: bb2]
    { stmts := [
        .assign ⟨2⟩ (.binaryOp .le (.copy ⟨1⟩) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨1⟩ ⟨2⟩ },
    -- bb1 (false: x > 1000): _0 = const 0usize; goto -> bb3
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0)))
      ]
      terminator := .goto ⟨3⟩ },
    -- bb2 (true: x <= 1000): _3 = call "add"(copy _1, copy _1) -> bb4
    { stmts := []
      terminator := .call ⟨3⟩ "add" [.copy ⟨1⟩, .copy ⟨1⟩] ⟨4⟩ },
    -- bb3 (return join): return
    { stmts := []
      terminator := .return_ },
    -- bb4 (after call): _0 = move _3; goto -> bb3
    { stmts := [
        .assign ⟨0⟩ (.use (.move ⟨3⟩))
      ]
      terminator := .goto ⟨3⟩ }
  ]
  requiredConsts := []
  mentionedItems := ["add"]

/-- Lowered `Runtime(PostCleanup)` MIR body for:
    ```rust
    pub fn double_conditional(x: usize) -> usize { add(x, x) }
    ```
    Locals: `_0: usize`, `_1: usize (x)`, `_2: usize`. -/
def doubleConditionalBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 3
  blocks := [
    -- bb0: _2 = call "add"(copy _1, copy _1) -> bb1
    { stmts := []
      terminator := .call ⟨2⟩ "add" [.copy ⟨1⟩, .copy ⟨1⟩] ⟨1⟩ },
    -- bb1: _0 = move _2; return
    { stmts := [
        .assign ⟨0⟩ (.use (.move ⟨2⟩))
      ]
      terminator := .return_ }
  ]
  requiredConsts := []
  mentionedItems := ["add"]

/-- Crate environment containing `add`, `double_guarded`, and
    `double_conditional`. -/
def interprocEnv : CrateEnv := [
  { name := "add", body := addBody },
  { name := "double_guarded", body := doubleGuardedBody },
  { name := "double_conditional", body := doubleConditionalBody }
]

/-- Return-value postcondition for `double_guarded`:
    every terminating prefix returns `if x <= 1000 then x + x else 0`. -/
def PostDoubleGuarded (q : MirLang.Query) (out : MirLang.Out) : Prop :=
  initMirState doubleGuardedBody q.init →
    ∀ x : Nat,
      q.init.locals 1 = some (.usize x) →
      out.outcome = .running ∨
      out.outcome = .terminated (.normal (.usize
        (match decide (x ≤ 1000) with | false => 0 | true => x + x)))

def EnsuresDoubleGuarded : MirLang.Behavior :=
  MirLang.Spec PostDoubleGuarded

/-!
### 7.2 Mode A: Zero-Annotation Symbolic Call Inlining
-/

/-- Computed Mode A execution plan for `doubleGuardedBody` with `summaries = []`
    and `callFuel = 1`: automatically emits `.callInline` for the private
    helper `"add"`. -/
def doubleGuardedPlanModeA : TransPlan :=
  .step (.branch
    (.step (.goto .return_))
    (.callInline
      (.step (.step (.assertNotOverflow (.step .return_))))
      (.step (.goto .return_))))

theorem computePlan_doubleGuarded_modeA :
    computePlan interprocEnv [] 12 1 doubleGuardedBody 0 0 =
      some doubleGuardedPlanModeA := rfl

/-- **Deliverable 2a (`evalSymState_doubleGuarded_modeA_rfl`)**:
    In Mode A (zero-annotation symbolic call inlining with `summaries = []`),
    `evalSymState` on `doubleGuardedBody` reduces by **kernel `rfl`** for
    universally quantified `x : Nat`! -/
theorem evalSymState_doubleGuarded_modeA_rfl (x : Nat) :
    evalSymState interprocEnv [] doubleGuardedPlanModeA doubleGuardedBody
        (initSymState doubleGuardedBody [.usize x]) =
      some (
        (match decide (x ≤ 1000) with
         | false => false
         | true => decide (usizeMax < x + x)),
        .usize (match decide (x ≤ 1000) with
                | false => 0
                | true => x + x)
      ) := rfl

theorem guard_1000_no_overflow {x : Nat}
    (hLe : decide (x ≤ 1000) = true) :
    decide (usizeMax < x + x) = false := by
  have hx : x ≤ 1000 := of_decide_eq_true hLe
  have hSum : x + x ≤ 2000 := Nat.add_le_add hx hx
  have hMax : 2000 ≤ usizeMax := by decide
  exact decide_eq_false (Nat.not_lt_of_ge (Nat.le_trans hSum hMax))

/-- **Deliverable 2a (`translatePure_doubleGuarded_modeA_eq`)**:
    `translatePure` in Mode A (`summaries = []`, `callFuel = 1`) evaluates
    `doubleGuardedBody` on any symbolic `x : Nat` to `some (.usize ...)`
    matching `if x <= 1000 then x + x else 0`. -/
theorem translatePure_doubleGuarded_modeA_eq (x : Nat) :
    translatePure interprocEnv [] 12 1 doubleGuardedBody [.usize x] =
      some (.usize (match decide (x ≤ 1000) with | false => 0 | true => x + x)) := by
  unfold translatePure
  rw [computePlan_doubleGuarded_modeA]
  dsimp [evalSym]
  rw [evalSymState_doubleGuarded_modeA_rfl x]
  cases hCond : decide (x ≤ 1000) with
  | false => rfl
  | true =>
    dsimp
    rw [guard_1000_no_overflow hCond]

/-- **Deliverable 2a (`doubleGuardedBody_verified_modeA`)**:
    `doubleGuardedBody` refines `EnsuresDoubleGuarded` in the call-stack
    `MirMachine` using Mode A (zero-annotation symbolic inlining of `add`). -/
theorem doubleGuardedBody_verified_modeA :
    MirSem interprocEnv doubleGuardedBody ≤ EnsuresDoubleGuarded := by
  intro q _
  have hSafe :
      ∀ (hInit : initMirState doubleGuardedBody q.init),
        ∃ x : Nat,
          q.init.locals 1 = some (.usize x) ∧
          SafeFrom interprocEnv q.init
            (.usize (match decide (x ≤ 1000) with | false => 0 | true => x + x)) := by
    intro hInit
    have ⟨x, hLoc1, hFrames, hRef⟩ :=
      symStateRefines_init_1 (body := doubleGuardedBody) rfl hInit
    have hEval :
        evalSym interprocEnv [] doubleGuardedPlanModeA doubleGuardedBody [.usize x] =
          some (.usize (match decide (x ≤ 1000) with | false => 0 | true => x + x)) :=
      translatePure_doubleGuarded_modeA_eq x
    exact ⟨x, hLoc1,
      evalSym_sound interprocEnv [] (summarySoundForEnv_nil interprocEnv)
        hEval hFrames hRef⟩
  refine ⟨?_, ?_⟩
  · intro hInit tr out hReach
    have ⟨x, _, hSafeX⟩ := hSafe hInit
    cases hSafeX doubleGuardedBody q.init q.steps tr out hReach with
    | inl hRun => rw [hRun]; exact True.intro
    | inr hTerm => rw [hTerm]; exact True.intro
  · intro out ⟨hInit, hReach⟩ _ x hLoc1
    have ⟨x0, hLoc1_0, hSafeX0⟩ := hSafe hInit
    rw [hLoc1] at hLoc1_0
    injection hLoc1_0 with hValEq
    injection hValEq with hXEq
    subst hXEq
    exact hSafeX0 doubleGuardedBody q.init q.steps out.trace out.outcome hReach

/-- Mode A crate containing private helper `add` (`isPublic := false`, with NO
    user-written specification or precondition) and public caller
    `double_guarded` (`isPublic := true`). -/
def guardedCrateModeA : Crate where
  fns := [
    { name := "add"
      body := addBody
      isPublic := false },
    { name := "double_guarded"
      body := doubleGuardedBody
      isPublic := true
      pre := fun _ => True
      specs := [EnsuresDoubleGuarded] },
    { name := "double_conditional"
      body := doubleConditionalBody
      isPublic := false }
  ]

/-- **Deliverable 2a (`prove_guarded_crate_modeA`)**:
    End-to-end verification of `guardedCrateModeA` in Mode A with zero
    annotations on the private helper `add`. -/
theorem prove_guarded_crate_modeA :
    PublicAdmittedCrateTheorem IdentityMirCompiler DefaultTrustPolicy 2
      guardedCrateModeA := by
  dsimp [PublicAdmittedCrateTheorem, Crate.publicFns, Crate.toEnv,
    guardedCrateModeA, AdmittedFnsTheorem, AllHold]
  refine ⟨⟨?_, ?_⟩, True.intro⟩
  · exact compileAdmitted_of_checkCompileAdmitted interprocEnv 10 2
      doubleGuardedBody rfl
  · refine ⟨True.intro, fun _ => ?_⟩
    have hVer :
        IdentityMirCompiler.Verified
          { env := interprocEnv, body := doubleGuardedBody }
          EnsuresDoubleGuarded :=
      (identityMirCompiler_soundOn _).verify doubleGuardedBody_verified_modeA
    exact hVer.with_wellFormedOn (spec_le_wellFormed PostDoubleGuarded)
      identityMirCompiler_monotone

/-!
### 7.3 Mode B: Modular Verified Callee Summaries
-/

/-- Domain precondition `PreAdd` for `add(x, y)`: `x + y <= usize::MAX`. -/
def PreAdd (q : MirLang.Query) : Prop :=
  initMirState addBody q.init →
    ∃ x y : Nat,
      q.init.locals 1 = some (.usize x) ∧
      q.init.locals 2 = some (.usize y) ∧
      decide (usizeMax < x + y) = false

/-- Postcondition `PostAdd` for `add(x, y)`. -/
def PostAdd (q : MirLang.Query) (out : MirLang.Out) : Prop :=
  initMirState addBody q.init →
    ∀ x y : Nat,
      q.init.locals 1 = some (.usize x) →
      q.init.locals 2 = some (.usize y) →
      out.outcome = .running ∨
      out.outcome = .terminated (.normal (.usize (x + y)))

/-- Conditional behavioral contract for `add`:
    `MirLang.SpecOn PreAdd PostAdd`. -/
def EnsuresAddOn : MirLang.Behavior :=
  MirLang.SpecOn PreAdd PostAdd

def addPlan : TransPlan :=
  .step (.step (.assertNotOverflow (.step .return_)))

theorem evalSymState_add_rfl (x y : Nat) :
    evalSymState interprocEnv [] addPlan addBody
        (initSymState addBody [.usize x, .usize y]) =
      some (decide (usizeMax < x + y), .usize (x + y)) := rfl

/-- **Deliverable 2b (`addBody_verified_specOn`)**:
    `addBody` satisfies its conditional specification `EnsuresAddOn`
    (`MirLang.SpecOn PreAdd PostAdd`). -/
theorem addBody_verified_specOn :
    MirSem interprocEnv addBody ≤ EnsuresAddOn := by
  intro q hPre
  have hSafe :
      ∀ (hInit : initMirState addBody q.init),
        ∃ x y : Nat,
          q.init.locals 1 = some (.usize x) ∧
          q.init.locals 2 = some (.usize y) ∧
          SafeFrom interprocEnv q.init (.usize (x + y)) := by
    intro hInit
    have ⟨x, y, hLoc1, hLoc2, hNoOv⟩ := hPre hInit
    have ⟨x', y', hLoc1', hLoc2', hFrames, hRef⟩ :=
      symStateRefines_init_2 (body := addBody) rfl hInit
    rw [hLoc1] at hLoc1'; injection hLoc1' with h1; injection h1 with hx; subst hx
    rw [hLoc2] at hLoc2'; injection hLoc2' with h2; injection h2 with hy; subst hy
    have hEval :
        evalSym interprocEnv [] addPlan addBody [.usize x, .usize y] =
          some (.usize (x + y)) := by
      unfold evalSym
      rw [evalSymState_add_rfl x y, hNoOv]
    exact ⟨x, y, hLoc1, hLoc2,
      evalSym_sound interprocEnv [] (summarySoundForEnv_nil interprocEnv)
        hEval hFrames hRef⟩
  refine ⟨?_, ?_⟩
  · intro hInit tr out hReach
    have ⟨x, y, _, _, hSafeXY⟩ := hSafe hInit
    cases hSafeXY addBody q.init q.steps tr out hReach with
    | inl hRun => rw [hRun]; exact True.intro
    | inr hTerm => rw [hTerm]; exact True.intro
  · intro out ⟨hInit, hReach⟩ _ x y hLoc1 hLoc2
    have ⟨x0, y0, hLoc1_0, hLoc2_0, hSafeXY0⟩ := hSafe hInit
    rw [hLoc1] at hLoc1_0; injection hLoc1_0 with h1; injection h1 with hx; subst hx
    rw [hLoc2] at hLoc2_0; injection hLoc2_0 with h2; injection h2 with hy; subst hy
    exact hSafeXY0 addBody q.init q.steps out.trace out.outcome hReach

/-- Spine-preserving modular summary for `add(x, y)`. -/
def addSummary : CalleeSummary where
  name := "add"
  argTys := [.usize, .usize]
  retTy := .usize
  eval args :=
    match args with
    | [.usize x, .usize y] =>
      some (decide (usizeMax < x + y), .usize (x + y))
    | _ => none

/-- **Deliverable 2b (`addSummary_sound`)**:
    `addSummary` is sound with respect to `interprocEnv`, proved directly from
    `summaryEntrySound_of_evalSymState` without re-Unfolding `MirMachine`! -/
theorem addSummary_sound :
    SummaryEntrySound interprocEnv addSummary := by
  refine summaryEntrySound_of_evalSymState interprocEnv []
    (summarySoundForEnv_nil interprocEnv) addSummary addBody addPlan
    rfl rfl rfl ?_
  intro argSvs hTys
  cases argSvs with
  | nil => cases hTys
  | cons a1 rest1 =>
    cases a1 with
    | bool _ | unit | tupleUsizeBool _ _ => cases hTys
    | usize x =>
      cases rest1 with
      | nil => cases hTys
      | cons a2 rest2 =>
        cases a2 with
        | bool _ | unit | tupleUsizeBool _ _ => cases hTys
        | usize y =>
          cases rest2 with
          | nil => rfl
          | cons _ _ => cases hTys

theorem summarySoundForEnv_add :
    SummarySoundForEnv interprocEnv [addSummary] := by
  intro name summary hLook
  dsimp [lookupSummary, addSummary] at hLook
  cases hEq : ("add" == name) with
  | false => rw [hEq] at hLook; cases hLook
  | true =>
    rw [hEq] at hLook
    injection hLook with hSumEq
    subst hSumEq
    exact ⟨eq_of_beq hEq, addSummary_sound⟩

/-- Computed Mode B execution plan for `doubleGuardedBody` with
    `summaries = [addSummary]` and `callFuel = 0`: emits `.callSummary` for
    `"add"`. -/
def doubleGuardedPlanModeB : TransPlan :=
  .step (.branch
    (.step (.goto .return_))
    (.callSummary (.step (.goto .return_))))

theorem computePlan_doubleGuarded_modeB :
    computePlan interprocEnv [addSummary] 12 0 doubleGuardedBody 0 0 =
      some doubleGuardedPlanModeB := rfl

/-- **Deliverable 2b (`evalSymState_doubleGuarded_modeB_rfl`)**:
    In Mode B (modular callee summary `[addSummary]`, `callFuel = 0`),
    `evalSymState` on `doubleGuardedBody` reduces by **kernel `rfl`** to the
    exact same symbolic expression as Mode A! -/
theorem evalSymState_doubleGuarded_modeB_rfl (x : Nat) :
    evalSymState interprocEnv [addSummary] doubleGuardedPlanModeB doubleGuardedBody
        (initSymState doubleGuardedBody [.usize x]) =
      some (
        (match decide (x ≤ 1000) with
         | false => false
         | true => decide (usizeMax < x + x)),
        .usize (match decide (x ≤ 1000) with
                | false => 0
                | true => x + x)
      ) := rfl

/-- **Deliverable 2b (`evalSymState_doubleGuarded_modeA_eq_modeB`)**:
    Mode A (symbolic inlining) and Mode B (modular summary) produce
    definitionally identical symbolic evaluation results on `doubleGuardedBody`
    by **kernel `rfl`**! -/
theorem evalSymState_doubleGuarded_modeA_eq_modeB (x : Nat) :
    evalSymState interprocEnv [] doubleGuardedPlanModeA doubleGuardedBody
        (initSymState doubleGuardedBody [.usize x]) =
      evalSymState interprocEnv [addSummary] doubleGuardedPlanModeB doubleGuardedBody
        (initSymState doubleGuardedBody [.usize x]) := rfl

theorem translatePure_doubleGuarded_modeB_eq (x : Nat) :
    translatePure interprocEnv [addSummary] 12 0 doubleGuardedBody [.usize x] =
      some (.usize (match decide (x ≤ 1000) with | false => 0 | true => x + x)) := by
  unfold translatePure
  rw [computePlan_doubleGuarded_modeB]
  dsimp [evalSym]
  rw [evalSymState_doubleGuarded_modeB_rfl x]
  cases hCond : decide (x ≤ 1000) with
  | false => rfl
  | true =>
    dsimp
    rw [guard_1000_no_overflow hCond]

theorem translatePure_doubleGuarded_modeA_eq_modeB (x : Nat) :
    translatePure interprocEnv [] 12 1 doubleGuardedBody [.usize x] =
      translatePure interprocEnv [addSummary] 12 0 doubleGuardedBody [.usize x] := by
  rw [translatePure_doubleGuarded_modeA_eq, translatePure_doubleGuarded_modeB_eq]

/-- **Deliverable 2b (`doubleGuardedBody_verified_modeB`)**:
    `doubleGuardedBody` refines `EnsuresDoubleGuarded` in Mode B using
    `addSummary_sound`. -/
theorem doubleGuardedBody_verified_modeB :
    MirSem interprocEnv doubleGuardedBody ≤ EnsuresDoubleGuarded := by
  intro q _
  have hSafe :
      ∀ (hInit : initMirState doubleGuardedBody q.init),
        ∃ x : Nat,
          q.init.locals 1 = some (.usize x) ∧
          SafeFrom interprocEnv q.init
            (.usize (match decide (x ≤ 1000) with | false => 0 | true => x + x)) := by
    intro hInit
    have ⟨x, hLoc1, hFrames, hRef⟩ :=
      symStateRefines_init_1 (body := doubleGuardedBody) rfl hInit
    have hEval :
        evalSym interprocEnv [addSummary] doubleGuardedPlanModeB
            doubleGuardedBody [.usize x] =
          some (.usize (match decide (x ≤ 1000) with | false => 0 | true => x + x)) :=
      translatePure_doubleGuarded_modeB_eq x
    exact ⟨x, hLoc1,
      evalSym_sound interprocEnv [addSummary] summarySoundForEnv_add
        hEval hFrames hRef⟩
  refine ⟨?_, ?_⟩
  · intro hInit tr out hReach
    have ⟨x, _, hSafeX⟩ := hSafe hInit
    cases hSafeX doubleGuardedBody q.init q.steps tr out hReach with
    | inl hRun => rw [hRun]; exact True.intro
    | inr hTerm => rw [hTerm]; exact True.intro
  · intro out ⟨hInit, hReach⟩ _ x hLoc1
    have ⟨x0, hLoc1_0, hSafeX0⟩ := hSafe hInit
    rw [hLoc1] at hLoc1_0
    injection hLoc1_0 with hValEq
    injection hValEq with hXEq
    subst hXEq
    exact hSafeX0 doubleGuardedBody q.init q.steps out.trace out.outcome hReach

/-- Conditional contract for `double_conditional(x)`: requires
    `x + x <= usizeMax` and ensures return value `x + x`. -/
def PreDouble (q : MirLang.Query) : Prop :=
  initMirState doubleConditionalBody q.init →
    ∃ x : Nat,
      q.init.locals 1 = some (.usize x) ∧
      decide (usizeMax < x + x) = false

def PostDouble (q : MirLang.Query) (out : MirLang.Out) : Prop :=
  initMirState doubleConditionalBody q.init →
    ∀ x : Nat,
      q.init.locals 1 = some (.usize x) →
      out.outcome = .running ∨
      out.outcome = .terminated (.normal (.usize (x + x)))

def EnsuresDoubleOn : MirLang.Behavior :=
  MirLang.SpecOn PreDouble PostDouble

def doubleConditionalPlanModeB : TransPlan :=
  .callSummary (.step .return_)

theorem evalSymState_doubleConditional_modeB_rfl (x : Nat) :
    evalSymState interprocEnv [addSummary] doubleConditionalPlanModeB
        doubleConditionalBody (initSymState doubleConditionalBody [.usize x]) =
      some (decide (usizeMax < x + x), .usize (x + x)) := rfl

/-- **Deliverable 2b (`doubleConditionalBody_verified_modeB`)**:
    `doubleConditionalBody` refines `EnsuresDoubleOn` in Mode B using
    `addSummary_sound`. -/
theorem doubleConditionalBody_verified_modeB :
    MirSem interprocEnv doubleConditionalBody ≤ EnsuresDoubleOn := by
  intro q hPre
  have hSafe :
      ∀ (hInit : initMirState doubleConditionalBody q.init),
        ∃ x : Nat,
          q.init.locals 1 = some (.usize x) ∧
          SafeFrom interprocEnv q.init (.usize (x + x)) := by
    intro hInit
    have ⟨x, hLoc1, hNoOv⟩ := hPre hInit
    have ⟨x', hLoc1', hFrames, hRef⟩ :=
      symStateRefines_init_1 (body := doubleConditionalBody) rfl hInit
    rw [hLoc1] at hLoc1'; injection hLoc1' with h1; injection h1 with hx; subst hx
    have hEval :
        evalSym interprocEnv [addSummary] doubleConditionalPlanModeB
            doubleConditionalBody [.usize x] =
          some (.usize (x + x)) := by
      unfold evalSym
      rw [evalSymState_doubleConditional_modeB_rfl x, hNoOv]
    exact ⟨x, hLoc1,
      evalSym_sound interprocEnv [addSummary] summarySoundForEnv_add
        hEval hFrames hRef⟩
  refine ⟨?_, ?_⟩
  · intro hInit tr out hReach
    have ⟨x, _, hSafeX⟩ := hSafe hInit
    cases hSafeX doubleConditionalBody q.init q.steps tr out hReach with
    | inl hRun => rw [hRun]; exact True.intro
    | inr hTerm => rw [hTerm]; exact True.intro
  · intro out ⟨hInit, hReach⟩ _ x hLoc1
    have ⟨x0, hLoc1_0, hSafeX0⟩ := hSafe hInit
    rw [hLoc1] at hLoc1_0
    injection hLoc1_0 with hValEq
    injection hValEq with hXEq
    subst hXEq
    exact hSafeX0 doubleConditionalBody q.init q.steps out.trace out.outcome hReach

/-- Mode B crate where all three functions (`add`, `double_guarded`, and
    `double_conditional`) carry modular specifications. -/
def modularCrateModeB : Crate where
  fns := [
    { name := "add"
      body := addBody
      isPublic := false
      pre := PreAdd
      specs := [EnsuresAddOn] },
    { name := "double_guarded"
      body := doubleGuardedBody
      isPublic := true
      pre := fun _ => True
      specs := [EnsuresDoubleGuarded] },
    { name := "double_conditional"
      body := doubleConditionalBody
      isPublic := true
      pre := PreDouble
      specs := [EnsuresDoubleOn] }
  ]

/-- **Deliverable 2b (`prove_modular_crate_modeB`)**:
    End-to-end verification of `modularCrateModeB` in Mode B. -/
theorem prove_modular_crate_modeB :
    ModularAdmittedCrateTheorem IdentityMirCompiler DefaultTrustPolicy 2
      modularCrateModeB := by
  dsimp [ModularAdmittedCrateTheorem, Crate.toEnv, modularCrateModeB,
    AdmittedFnsTheorem, AllHold]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, True.intro⟩
  · exact compileAdmitted_of_checkCompileAdmitted interprocEnv 10 2
      addBody rfl
  · refine ⟨True.intro, fun _ => ?_⟩
    have hVer :
        IdentityMirCompiler.Verified
          { env := interprocEnv, body := addBody } EnsuresAddOn :=
      (identityMirCompiler_soundOn _).verify addBody_verified_specOn
    exact hVer.with_wellFormedOn (specOn_le_wellFormedOn PreAdd PostAdd)
      identityMirCompiler_monotone
  · exact compileAdmitted_of_checkCompileAdmitted interprocEnv 10 2
      doubleGuardedBody rfl
  · refine ⟨True.intro, fun _ => ?_⟩
    have hVer :
        IdentityMirCompiler.Verified
          { env := interprocEnv, body := doubleGuardedBody }
          EnsuresDoubleGuarded :=
      (identityMirCompiler_soundOn _).verify doubleGuardedBody_verified_modeB
    exact hVer.with_wellFormedOn (spec_le_wellFormed PostDoubleGuarded)
      identityMirCompiler_monotone
  · exact compileAdmitted_of_checkCompileAdmitted interprocEnv 10 2
      doubleConditionalBody rfl
  · refine ⟨True.intro, fun _ => ?_⟩
    have hVer :
        IdentityMirCompiler.Verified
          { env := interprocEnv, body := doubleConditionalBody }
          EnsuresDoubleOn :=
      (identityMirCompiler_soundOn _).verify doubleConditionalBody_verified_modeB
    exact hVer.with_wellFormedOn (specOn_le_wellFormedOn PreDouble PostDouble)
      identityMirCompiler_monotone

/-- Negative Control for Mode B: an unsound summary for `add` that omits the
    overflow guard (`failed = false` unconditionally) is rejected by
    `SummaryEntrySound`. -/
def bogusUnconditionalAddSummary : CalleeSummary where
  name := "add"
  argTys := [.usize, .usize]
  retTy := .usize
  eval args :=
    match args with
    | [.usize x, .usize y] => some (false, .usize (x + y))
    | _ => none

theorem bogusUnconditionalAddSummary_not_sound :
    ¬ SummaryEntrySound interprocEnv bogusUnconditionalAddSummary := by
  intro ⟨calleeBody, hLook, _, _, hRun⟩
  dsimp [lookupFn, interprocEnv, bogusUnconditionalAddSummary] at hLook
  injection hLook with hBodyEq
  subst hBodyEq
  have hArgs :
      Forall2 SymValRefines [.usize usizeMax, .usize 1]
        [.usize usizeMax, .usize 1] :=
    .cons rfl (.cons rfl .nil)
  have hSafe := hRun
    [.usize usizeMax, .usize 1]
    [.usize usizeMax, .usize 1]
    (.usize (usizeMax + 1))
    MemState.empty [] (.usize (usizeMax + 1))
    rfl hArgs rfl (fun _ hVal => hVal)
  let s0 : MirState := {
    curBody := addBody
    locals := buildCalleeLocals [.usize usizeMax, .usize 1]
    mem := MemState.empty
    block := 0
    stmtIdx := 0
    frames := []
  }
  let s1 : MirState := { s0 with
    locals := updateLocal s0.locals 3
      (some (.tupleUsizeBool (usizeMax + 1) true))
    stmtIdx := 1
  }
  let s2 : MirState := { s1 with
    locals := updateLocal s1.locals 4 (some (.usize (usizeMax + 1)))
    stmtIdx := 2
  }
  have hReach2 :
      ReachesPrefix MirMachine { env := interprocEnv, body := addBody } s0 1 s2
        [] (.failed .contractViolation) :=
    ReachesPrefix.failed 0 s2 .contractViolation rfl
  have hReach1 :
      ReachesPrefix MirMachine { env := interprocEnv, body := addBody } s0 2 s1
        [()] (.failed .contractViolation) :=
    ReachesPrefix.step 1 s1 s2 () [] (.failed .contractViolation) rfl hReach2
  have hReach0 :
      ReachesPrefix MirMachine { env := interprocEnv, body := addBody } s0 3 s0
        [(), ()] (.failed .contractViolation) :=
    ReachesPrefix.step 2 s0 s1 () [()] (.failed .contractViolation) rfl hReach1
  cases hSafe addBody s0 3 [(), ()] (.failed .contractViolation) hReach0 with
  | inl h => cases h
  | inr h => cases h

/-!
### 7.4 Transitive `CompileAdmitted` Positive & Dead-Branch Negative Controls
-/

/-- Compile-time constant body `const { assert!(N <= 1000) }` extracted into
    `requiredConsts` of `const_bounded_add<N>`. -/
def constBoundedAddConst (N : Nat) : ConstMirBody where
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

/-- Lowered `MirBody` for:
    ```rust
    fn const_bounded_add<const N: usize>(x: usize) -> usize {
        const { assert!(N <= 1000) };
        x
    }
    ```
    At runtime (after const promotion), the body simply returns `x`, while
    `requiredConsts` holds `[constBoundedAddConst N]`. -/
def constBoundedAddBody (N : Nat) : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [
        .assign ⟨0⟩ (.use (.copy ⟨1⟩))
      ]
      terminator := .return_ }
  ]
  requiredConsts := [constBoundedAddConst N]
  mentionedItems := []

/-- Positive Control Caller:
    ```rust
    pub fn caller_good_500(x: usize) -> usize {
        const_bounded_add::<500>(x)
    }
    ``` -/
def callerGood500Body : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := []
      terminator := .call ⟨2⟩ "const_bounded_add_500" [.copy ⟨1⟩] ⟨1⟩ },
    { stmts := [
        .assign ⟨0⟩ (.use (.move ⟨2⟩))
      ]
      terminator := .return_ }
  ]
  requiredConsts := []
  mentionedItems := ["const_bounded_add_500"]

/-- Negative Control Caller with Dead Runtime Branch:
    ```rust
    pub fn dead_branch_bad_caller(x: usize) -> usize {
        if false {
            const_bounded_add::<2000>(x)
        } else {
            x
        }
    }
    ```
    Even though the `true` branch is dead at runtime (`switchInt (const false)`
    always jumps to `bb1`), `"const_bounded_add_2000"` is recorded in
    `mentionedItems`, matching `rustc_monomorphize::collector`. -/
def deadBranchBadCallerBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 3
  blocks := [
    -- bb0: switchInt(const false) -> [false: bb1, true: bb2]
    { stmts := []
      terminator := .switchInt (.constVal (.bool false)) ⟨1⟩ ⟨2⟩ },
    -- bb1 (live false branch): _0 = copy _1; return
    { stmts := [
        .assign ⟨0⟩ (.use (.copy ⟨1⟩))
      ]
      terminator := .return_ },
    -- bb2 (dead true branch):
    -- _2 = call "const_bounded_add_2000"(copy _1) -> bb3
    { stmts := []
      terminator := .call ⟨2⟩ "const_bounded_add_2000" [.copy ⟨1⟩] ⟨3⟩ },
    -- bb3: _0 = move _2; return
    { stmts := [
        .assign ⟨0⟩ (.use (.move ⟨2⟩))
      ]
      terminator := .return_ }
  ]
  requiredConsts := []
  mentionedItems := ["const_bounded_add_2000"]

/-- Crate environment for the PME positive and negative controls. -/
def pmeEnv : CrateEnv := [
  { name := "const_bounded_add_500", body := constBoundedAddBody 500 },
  { name := "const_bounded_add_2000", body := constBoundedAddBody 2000 },
  { name := "caller_good_500", body := callerGood500Body },
  { name := "dead_branch_bad_caller", body := deadBranchBadCallerBody }
]

/-- **Deliverable 3a (`callerGood500_compileAdmitted`)**:
    `callerGood500Body` is transitively `CompileAdmitted` because its
    `mentionedItems` target `"const_bounded_add_500"` whose `requiredConsts`
    succeeds in CTFE (`500 <= 1000`). -/
theorem callerGood500_compileAdmitted :
    CompileAdmitted pmeEnv 2 callerGood500Body :=
  compileAdmitted_of_checkCompileAdmitted pmeEnv 10 2 callerGood500Body rfl

/-- `const_bounded_add<2000>` fails CTFE in 3 steps (`2000 <= 1000` is `false`,
    jumping to `.panic`). -/
theorem constBoundedAdd2000_not_ctfeAdmitted :
    ¬ CtfeAdmitted (constBoundedAddConst 2000) :=
  not_ctfeAdmitted_of_evalCtfeFuel_failed (ctfeFuel := 3) (err := .contractViolation) rfl

/-- `constBoundedAddBody 2000` is not `CompileAdmitted` at any fuel depth. -/
theorem constBoundedAdd2000_not_compileAdmitted :
    ∀ (fuel : Nat), ¬ CompileAdmitted pmeEnv fuel (constBoundedAddBody 2000)
  | 0, h => h
  | _ + 1, ⟨⟨hCtfe, _⟩, _⟩ => constBoundedAdd2000_not_ctfeAdmitted hCtfe

/-- **Deliverable 3b (`deadBranchBadCaller_not_compileAdmitted`)**:
    Even though `deadBranchBadCallerBody` only references
    `const_bounded_add::<2000>` inside a dead `if false` branch, it is rejected
    at **every** fuel depth by transitive `CompileAdmitted` via
    `mentionedItems`! -/
theorem deadBranchBadCaller_not_compileAdmitted :
    ∀ (fuel : Nat), ¬ CompileAdmitted pmeEnv fuel deadBranchBadCallerBody
  | 0, h => h
  | fuel + 1, ⟨_, hMentioned, _⟩ =>
    constBoundedAdd2000_not_compileAdmitted fuel hMentioned

/-- Identity return postcondition (`_0 == x`) shared by `callerGood500Body` and
    `deadBranchBadCallerBody` at runtime. -/
def PostIdentityCaller (body : MirBody) (q : MirLang.Query)
    (out : MirLang.Out) : Prop :=
  initMirState body q.init →
    ∀ x : Nat,
      q.init.locals 1 = some (.usize x) →
      out.outcome = .running ∨
      out.outcome = .terminated (.normal (.usize x))

def EnsuresCallerGood500 : MirLang.Behavior :=
  MirLang.Spec (PostIdentityCaller callerGood500Body)

def EnsuresDeadBranchBadCaller : MirLang.Behavior :=
  MirLang.Spec (PostIdentityCaller deadBranchBadCallerBody)

/-- **Deliverable 3c (`callerGood500_runtime_verified`)**:
    `callerGood500Body` is verified at runtime via Mode A symbolic call
    inlining of `const_bounded_add_500`. -/
theorem callerGood500_runtime_verified :
    MirSem pmeEnv callerGood500Body ≤ EnsuresCallerGood500 := by
  intro q _
  let plan : TransPlan :=
    .callInline (.step .return_) (.step .return_)
  have hSafe :
      ∀ (hInit : initMirState callerGood500Body q.init),
        ∃ x : Nat,
          q.init.locals 1 = some (.usize x) ∧
          SafeFrom pmeEnv q.init (.usize x) := by
    intro hInit
    have ⟨x, hLoc1, hFrames, hRef⟩ :=
      symStateRefines_init_1 (body := callerGood500Body) rfl hInit
    exact ⟨x, hLoc1,
      evalSym_sound pmeEnv [] (summarySoundForEnv_nil pmeEnv)
        (plan := plan) (args := [.usize x]) (retSv := .usize x)
        rfl hFrames hRef⟩
  refine ⟨?_, ?_⟩
  · intro hInit tr out hReach
    have ⟨x, _, hSafeX⟩ := hSafe hInit
    cases hSafeX callerGood500Body q.init q.steps tr out hReach with
    | inl hRun => rw [hRun]; exact True.intro
    | inr hTerm => rw [hTerm]; exact True.intro
  · intro out ⟨hInit, hReach⟩ _ x hLoc1
    have ⟨x0, hLoc1_0, hSafeX0⟩ := hSafe hInit
    rw [hLoc1] at hLoc1_0
    injection hLoc1_0 with hValEq
    injection hValEq with hXEq
    subst hXEq
    exact hSafeX0 callerGood500Body q.init q.steps out.trace out.outcome hReach

/-- **Deliverable 3d (`deadBranchBadCaller_runtime_verified`)**:
    At runtime, `deadBranchBadCallerBody` is completely safe and refines
    `EnsuresDeadBranchBadCaller` because `switchInt (const false)` always takes
    the live `false` branch `bb1`, never entering `const_bounded_add_2000`.
    Combining `deadBranchBadCaller_runtime_verified` with
    `deadBranchBadCaller_not_compileAdmitted` proves that runtime MIR semantics
    alone cannot detect PMEs in dead branches without transitive
    `CompileAdmitted` over `mentionedItems`! -/
theorem deadBranchBadCaller_runtime_verified :
    MirSem pmeEnv deadBranchBadCallerBody ≤ EnsuresDeadBranchBadCaller := by
  intro q _
  let plan : TransPlan :=
    .branch (.step .return_) (.callInline (.step .return_) (.step .return_))
  have hSafe :
      ∀ (hInit : initMirState deadBranchBadCallerBody q.init),
        ∃ x : Nat,
          q.init.locals 1 = some (.usize x) ∧
          SafeFrom pmeEnv q.init (.usize x) := by
    intro hInit
    have ⟨x, hLoc1, hFrames, hRef⟩ :=
      symStateRefines_init_1 (body := deadBranchBadCallerBody) rfl hInit
    exact ⟨x, hLoc1,
      evalSym_sound pmeEnv [] (summarySoundForEnv_nil pmeEnv)
        (plan := plan) (args := [.usize x]) (retSv := .usize x)
        rfl hFrames hRef⟩
  refine ⟨?_, ?_⟩
  · intro hInit tr out hReach
    have ⟨x, _, hSafeX⟩ := hSafe hInit
    cases hSafeX deadBranchBadCallerBody q.init q.steps tr out hReach with
    | inl hRun => rw [hRun]; exact True.intro
    | inr hTerm => rw [hTerm]; exact True.intro
  · intro out ⟨hInit, hReach⟩ _ x hLoc1
    have ⟨x0, hLoc1_0, hSafeX0⟩ := hSafe hInit
    rw [hLoc1] at hLoc1_0
    injection hLoc1_0 with hValEq
    injection hValEq with hXEq
    subst hXEq
    exact hSafeX0 deadBranchBadCallerBody q.init q.steps out.trace out.outcome hReach

/-- Furthermore, under the compile-time gate `Behavior.when`, any function that
    fails `CompileAdmitted` (such as `deadBranchBadCallerBody`) has its gated
    behavior collapse to `Partial.bot`, refining every specification vacuously
    while `AdmittedFnsTheorem` explicitly rejects the crate. -/
theorem deadBranchBadCaller_when_compileAdmitted_refines_any
    (fuel : Nat) (spec : MirLang.Behavior) :
    Behavior.when (CompileAdmitted pmeEnv fuel deadBranchBadCallerBody)
      (MirSem pmeEnv deadBranchBadCallerBody) ≤ spec :=
  (behavior_when_le_iff _ _ _).mpr (fun hAdm =>
    False.elim (deadBranchBadCaller_not_compileAdmitted fuel hAdm))

/-!
## 8. Axiom Audit (`#print axioms`)
-/

#print axioms behavior_when_given_adjunction
#print axioms mirMachine_totalStep
#print axioms mirMachine_inhabitedDemonic
#print axioms mirMachine_non_vacuity_at_every_depth
#print axioms compileAdmitted_of_checkCompileAdmitted
#print axioms evalSymState_sound
#print axioms evalSym_sound
#print axioms summaryEntrySound_of_evalSymState
#print axioms evalSymState_doubleGuarded_modeA_rfl
#print axioms translatePure_doubleGuarded_modeA_eq
#print axioms doubleGuardedBody_verified_modeA
#print axioms prove_guarded_crate_modeA
#print axioms addBody_verified_specOn
#print axioms addSummary_sound
#print axioms evalSymState_doubleGuarded_modeB_rfl
#print axioms translatePure_doubleGuarded_modeA_eq_modeB
#print axioms doubleGuardedBody_verified_modeB
#print axioms doubleConditionalBody_verified_modeB
#print axioms prove_modular_crate_modeB
#print axioms bogusUnconditionalAddSummary_not_sound
#print axioms callerGood500_compileAdmitted
#print axioms callerGood500_runtime_verified
#print axioms deadBranchBadCaller_not_compileAdmitted
#print axioms deadBranchBadCaller_runtime_verified
#print axioms deadBranchBadCaller_when_compileAdmitted_refines_any

end AnnealR2WS2
