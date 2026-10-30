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
# Conditional Verification Results and Interprocedural Call Discharge (WS5)

This standalone Lean 4.34.1 module mechanizes the semantic foundations and
symbolic evaluation machinery for conditional verification results in Anneal:

1. **Taxonomy of Calling Conditions and Unified `Language.SpecOn`:**
   - **Type, memory, and aliasing validity (`initMirState`):** Scoped by the
     operational machine's initial-state predicate `M.initState`. Outside
     `initMirState`, `BehaviorOf M p` is vacuously defined with an empty outcome
     set (`AeneasRes.inapplicable`).
   - **Safety and no-overflow preconditions (`pre` in `WellFormedOn` and
     `SpecOn`):** When a function may fail (with `.failed .ub` or
     `.failed .contractViolation`) outside a calling condition `pre`, it cannot
     refine `L.Spec post` (`defined := True`) for *any* `post`
     (`not_le_spec_of_not_defined`). Instead, both baseline safety
     (`L.WellFormedOn pre`) and functional specifications (`L.SpecOn pre post`)
     must be conditioned on `pre` via `Language.SpecOn`.
   - **Functional preconditions (`req`) on unconditionally safe functions:**
     Captured by `L.SpecOn pre (fun q out => req q → post q out)`, which
     preserves `spec ≤ L.WellFormedOn pre` (`specOn_le_wellFormedOn`) even when
     `req` is stronger than `pre`.
2. **Public vs. Private Functions and Conditional Interprocedural Calls:**
   - Distinguishes public crate entry points (`Visibility.pub`) from private
     crate-internal helpers (`Visibility.priv`) in `CapturedFn` and `Crate`.
   - Models conditional 2-argument callees (`PureCallee2.add`) returning
     `Option (Bool × MirVal)` (`some (violated, retVal)`), where `violated`
     records whether the callee's precondition fails at the call site.
   - Preserves outer constructor spines in `evalSymStep` (`some (violated,
     sym')`) so `translatePure` reduces interprocedural calls by kernel `rfl`
     (First Futamura Projection), discharging the callee's precondition either
     from a caller branch guard (`double_guarded`) or from the caller's own
     precondition (`double_conditional`).
   - Enforces callee contract adequacy (`CalleeSpec2`) in `CrateTheorem` so a
     callee summary cannot silently weaken the callee body's precondition.
3. **Unwinding Overflow Semantics Comparison (`MirLangUnwind`):**
   - Contrasts contract-violation overflow semantics (`.failed
     .contractViolation`, requiring conditional `WellFormedOn PreAdd`) with
     Rust's unwinding panic semantics (`.terminated .unwind`, where `addBody` is
     unconditionally `WellFormed` and has a conditional normal-return /
     no-unwind guarantee inside `MirLangUnwind.Spec`).
-/

namespace AnnealWS5

/-!
## 1. Layer 1A: Refinement Preorder, `Partial`, and `Language.SpecOn`
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

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever `B` is a `Preorder`. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructively lifted partial domain $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- Top element ($\mathsf{UB}$) of `Partial B` (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

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

/-- Query-indexed partial behavior domain. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling programs, queries, outcomes, and semantics. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  AnnealWS5.Behavior L.Query L.Out

/-- Unified query-indexed specification with domain precondition `pre` and
    outcome postcondition `post`. -/
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

/-- Compilation pass (`L_tgt.sem t ≤ π_c (L_src.sem s)`). -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Verification abstraction pass (`L_src.sem s ≤ π_v (L_v.sem v)`). -/
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- Compiler lowering programs from `L_src` to `L_tgt`. -/
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

/-- Conditional verification envelope requiring `C.Verified prog` on
    `L_src.WellFormedOn pre :: specs`. -/
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

/-- Unconditional verification envelope (`pre := fun _ => True`). -/
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
### 1.1 Algebraic Characterizations of `SpecOn`, `Spec`, and `WellFormedOn`
-/

theorem le_specOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    b ≤ L.SpecOn pre post ↔
      ∀ q, pre q → ∃ h : (b q).defined, ∀ out, (b q).val h out → post q out :=
  ⟨fun h => h, fun h => h⟩

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

/-- **Critical Discovery Verification (`not_le_spec_of_not_defined`)**:
    If a behavior `b` is undefined (`¬ (b q).defined`) at even one query `q`,
    then `b ≤ L.Spec post` is false for *every* postcondition `post` (even when
    `post` is guarded by an implication `pre q → ...`).

    Consequently, if a function `fn` is only well-formed on a non-trivial
    precondition `pre` (so `¬ (L.sem fn.prog q).defined` for some `q` with
    `¬ pre q`), any specification in `fn.specs` must be built with
    `L.SpecOn pre post` (`defined := pre q`) rather than `L.Spec post`
    (`defined := True`). -/
theorem not_le_spec_of_not_defined {L : Language} {b : L.Behavior}
    {q : L.Query} (hundef : ¬ (b q).defined)
    (post : L.Query → L.Out → Prop) :
    ¬ (b ≤ L.Spec post) :=
  fun hle => hundef (hle q True.intro).1

/-- Separation of safety precondition `pre` (in `.defined`) from functional
    precondition `req` (in `.val`): `L.SpecOn pre (fun q out => req q → post q
    out)` always refines `L.WellFormedOn pre`, even when `req` is stronger than
    `pre` (e.g., `binary_search` where `pre = fun _ => True` and `req =
    sorted`). -/
theorem specOn_functional_req_le_wellFormedOn {L : Language}
    (pre req : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre (fun q out => req q → post q out) ≤ L.WellFormedOn pre :=
  specOn_le_wellFormedOn pre _

theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

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
## 2. Layer 1B: Small-Step Transition Outcomes and Prefix Behaviors
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
    exact (behaviorOf_le_wellFormedOn_iff (M := M)).mpr (fun init steps tr out _ => h init steps tr out)

theorem behaviorOf_le_specOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

theorem behaviorOf_le_spec
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).Spec Post :=
  behaviorOf_le_specOn (fun q out _ hpfx => h q out hpfx)

/-!
## 3. Minimal MIR AST, Conditional Callee Semantics, and Public/Private Crates
-/

structure LocalId where
  index : Nat

structure BlockId where
  index : Nat

inductive AtomicOrdering where
  | relaxed
  | acquire

inductive MirTy where
  | usize
  | bool
  | unit
  | tupleUsizeBool
  | refAtomicUsize
  | refSharedUsize
  | refMutUsize
  | atomicOrdering

inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  | atomicLoc (loc : Nat)
  | refSharedLoc (loc : Nat)
  | refMutLoc (loc : Nat)
  | ordering (ord : AtomicOrdering)

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
  | bitAnd
  | bitOr
  | bitXor

inductive CheckedBinOp where
  | add
  | sub
  | mul

inductive Rvalue where
  | use (op : Operand)
  | deref (src : LocalId)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | checkedBinaryOp (op : CheckedBinOp) (lhs : Operand) (rhs : Operand)
  | proj0 (src : LocalId)
  | proj1 (src : LocalId)

inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | assignDeref (dst : LocalId) (op : Operand)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop

/-- 2-argument `usize` callees, extended with conditional `PureCallee2.add`
    (`fn add(x: usize, y: usize) -> usize { x + y }`). -/
inductive PureCallee2 where
  | addBounded
  | absDiff
  | add

inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | callPure2 (dst : LocalId) (callee : PureCallee2) (arg1 : Operand) (arg2 : Operand) (target : BlockId)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | assertNotOverflow (tupleLocal : LocalId) (target : BlockId)

structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock

abbrev Timestamp := Nat
abbrev View := Nat → Timestamp

def View.bot : View := fun _ => 0

def View.bump (v : View) (loc : Nat) (ts : Timestamp) : View :=
  fun l => if l == loc then max (v l) ts else v l

structure AtomicMsg where
  loc : Nat
  ts : Timestamp
  bits : Nat
  relView : View

structure MemState where
  curView : View
  atomicMsgs : List AtomicMsg
  naVal : Nat → Option MirVal
  naWriteTs : Nat → Timestamp
  naReadTs : Nat → Timestamp

def MemState.empty : MemState where
  curView := View.bot
  atomicMsgs := []
  naVal := fun _ => none
  naWriteTs := fun _ => 0
  naReadTs := fun _ => 0

def MemState.visibleAtomicMsgs (m : MemState) (loc : Nat) : List AtomicMsg :=
  m.atomicMsgs.filter fun msg =>
    msg.loc == loc && decide (m.curView loc ≤ msg.ts)

def MemState.readNA (m : MemState) (loc : Nat) : Option (MirVal × MemState) :=
  if decide (m.naWriteTs loc ≤ m.curView loc) then
    match m.naVal loc with
    | some v =>
      some (v, { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) })
    | none => none
  else
    none

def MemState.writeNA (m : MemState) (loc : Nat) (v : MirVal) : Option MemState :=
  if decide (m.naWriteTs loc ≤ m.curView loc) && decide (m.naReadTs loc ≤ m.curView loc) then
    let nextTs := m.curView loc + 1
    some { m with
      curView := View.bump m.curView loc nextTs
      naVal := fun l => if l == loc then some v else m.naVal l
      naWriteTs := View.bump m.naWriteTs loc nextTs
      naReadTs := View.bump m.naReadTs loc nextTs }
  else
    none

structure MirState where
  locals : Nat → Option MirVal
  mem : MemState
  block : Nat
  stmtIdx : Nat

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

def MirVal.hasTy (m : MemState) (v : MirVal) (ty : MirTy) : Prop :=
  match v, ty with
  | .usize _, .usize => True
  | .bool _, .bool => True
  | .unit, .unit => True
  | .tupleUsizeBool _ _, .tupleUsizeBool => True
  | .atomicLoc loc, .refAtomicUsize => m.visibleAtomicMsgs loc ≠ []
  | .refSharedLoc loc, .refSharedUsize =>
    ∃ n, m.naVal loc = some (.usize n) ∧
      m.naWriteTs loc ≤ m.curView loc
  | .refMutLoc loc, .refMutUsize =>
    ∃ n, m.naVal loc = some (.usize n) ∧
      m.naWriteTs loc ≤ m.curView loc ∧
      m.naReadTs loc ≤ m.curView loc
  | .ordering _, .atomicOrdering => True
  | _, _ => False

def argValidAt (m : MemState) (locals : Nat → Option MirVal) (k : Nat)
    (v : MirVal) (ty : MirTy) : Prop :=
  match ty with
  | .refMutUsize =>
    v.hasTy m .refMutUsize ∧
      ∀ loc i, v = .refMutLoc loc → 1 ≤ i → i < k →
        locals i ≠ some (.refMutLoc loc) ∧ locals i ≠ some (.refSharedLoc loc)
  | .refSharedUsize =>
    v.hasTy m .refSharedUsize ∧
      ∀ loc i, v = .refSharedLoc loc → 1 ≤ i → i < k →
        locals i ≠ some (.refMutLoc loc)
  | _ => v.hasTy m ty

def argsMatchLocals (m : MemState) (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k => (∃ v, locals k = some v ∧ argValidAt m locals k v ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  argsMatchLocals s.mem body.argTys s.locals

/-- Non-initialized entry states are vacuously defined (`defined = True`) with
    an empty outcome set (`val = False`) in `BehaviorOf`. -/
theorem behaviorOf_outside_initState_vacuous
    {M : SmallStepMachine Prog State Obs Val} (p : Prog) (q : ExecQuery State)
    (hnot : ¬ M.initState p q.init) :
    (BehaviorOf M p q).defined ∧ ∀ h out, ¬ (BehaviorOf M p q).val h out :=
  ⟨fun hinit => False.elim (hnot hinit), fun _ _ hval => hnot hval.1⟩

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
    | .bitAnd => some (.usize (Nat.land n1 n2))
    | .bitOr => some (.usize (Nat.lor n1 n2))
    | .bitXor => some (.usize (Nat.xor n1 n2))
  | _, _ => none

def usizeMax : Nat := 18446744073709551615

def evalCheckedBinOp (op : CheckedBinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.tupleUsizeBool (n1 + n2) (decide (usizeMax < n1 + n2)))
    | .sub => some (.tupleUsizeBool (n1 - n2) (decide (n1 < n2)))
    | .mul => some (.tupleUsizeBool (n1 * n2) (decide (usizeMax < n1 * n2)))
  | _, _ => none

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
  | .assign dst (.deref src) =>
    match s.locals src.index with
    | some (.refMutLoc loc) | some (.refSharedLoc loc) =>
      match s.mem.readNA loc with
      | some (v, mem') =>
        .step () { s with
          locals := updateLocal s.locals dst.index (some v)
          mem := mem'
          stmtIdx := s.stmtIdx + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
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
  | .assignDeref dst op =>
    match evalOperand s.locals op with
    | none => .failed .ub
    | some (v, locals1) =>
      match locals1 dst.index with
      | some (.refMutLoc loc) =>
        match s.mem.writeNA loc v with
        | some mem' =>
          .step () { s with
            locals := locals1
            mem := mem'
            stmtIdx := s.stmtIdx + 1
          }
        | none => .failed .ub
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

/-- Evaluate a 2-argument `usize` callee (`PureCallee2`), returning
    `some (violated, retVal)`:
    - `violated = false`: the callee's precondition holds and the call returns
      `retVal`.
    - `violated = true`: the callee's precondition or overflow check is
      violated (e.g., `usizeMax < x0 + y0` in `PureCallee2.add`), triggering
      `.failed .contractViolation` in Mode 1 or `.terminated .unwind` in Mode 2.
    - `none`: dynamic operand type mismatch, triggering `.failed .ub`. -/
def evalPureCallee2 (callee : PureCallee2) (v1 v2 : MirVal) :
    Option (Bool × MirVal) :=
  match v1, v2 with
  | .usize x0, .usize y0 =>
    match callee with
    | .addBounded =>
      some (false, .usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0))
    | .absDiff =>
      some (false, .usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0))
    | .add =>
      some (decide (usizeMax < x0 + y0), .usize (x0 + y0))
  | _, _ => none

/-- Mode 1 terminator evaluation: overflow assertions (`assertNotOverflow`) and
    violated callee preconditions (`evalPureCallee2 = some (true, _)`)
    transition to `.failed .contractViolation`. -/
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
  | .callPure2 dst callee arg1 arg2 target =>
    match evalOperand s.locals arg1 with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 arg2 with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalPureCallee2 callee v1 v2 with
        | some (false, res) =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            block := target.index
            stmtIdx := 0
          }
        | some (true, _) => .failed .contractViolation
        | none => .failed .ub
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

def evalMirStep (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminator s bb.terminator

def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = evalMirStep body s

def MirLang : Language :=
  MirMachine.toLanguage

abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

/-!
### 3.1 Callee Contract Obligations and Public/Private Crates
-/

/-- Calling precondition induced by `evalPureCallee2 callee`: holds at query `q`
    whenever `.usize` arguments in `_1` and `_2` satisfy the callee's
    non-failure condition (`evalPureCallee2 callee (.usize x0) (.usize y0) =
    some (false, retVal)`). -/
def CalleePre2 (callee : PureCallee2) (q : ExecQuery MirState) : Prop :=
  ∀ x0 y0,
    q.init.locals 1 = some (.usize x0) →
    q.init.locals 2 = some (.usize y0) →
    ∃ retVal, evalPureCallee2 callee (.usize x0) (.usize y0) = some (false, retVal)

/-- Behavioral specification induced by `evalPureCallee2 callee` via
    `MirLang.SpecOn`: on all queries satisfying `CalleePre2 callee`, execution
    is defined (safe at every step budget) and any normal return value matches
    the `retVal` produced by `evalPureCallee2 callee`. -/
def CalleeSpec2 (callee : PureCallee2) : MirLang.Behavior :=
  MirLang.SpecOn (CalleePre2 callee) (fun q out =>
    ∀ ret x0 y0 retVal,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      q.init.locals 2 = some (.usize y0) →
      evalPureCallee2 callee (.usize x0) (.usize y0) = some (false, retVal) →
      ret = retVal)

theorem calleeSpec2_le_wellFormedOn (callee : PureCallee2) :
    CalleeSpec2 callee ≤ MirLang.WellFormedOn (CalleePre2 callee) :=
  specOn_le_wellFormedOn (L := MirLang) (CalleePre2 callee) _

structure TargetArtifact where
  private mk ::
  unit : Unit

opaque rustc : MirBody → TargetArtifact := fun _ => { unit := () }

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

def RustcCompiler : Compiler MirLang TargetLang where
  compile := rustc
  π := π_c

inductive TCBItem where
  | rustcLowering (fnName : String) (body : MirBody)
  | userAxiom (name : String) (prop : Prop)

instance instTrustedAssumptionTCBItem : TrustedAssumption TCBItem where
  meaning
    | .rustcLowering _ body => RustcCompiler.SoundOn body
    | .userAxiom _ prop => prop

def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ _ => True
    | .userAxiom _ _ => False

/-- Visibility of a captured function within its crate:
    - `pub`: exported as part of the crate's public interface; its `pre` is an
      external calling condition required of callers of the crate.
    - `priv`: internal helper function not callable outside the crate; its `pre`
      is an internal precondition discharged at internal call sites. -/
inductive Visibility where
  | pub
  | priv

/-- Captured MIR function pairing its identifier, visibility (`.pub` or
    `.priv`), optional interprocedural callee summary link (`callee : Option
    PureCallee2`), lowered `MirBody`, caller precondition `pre`, and additional
    specifications `specs`. -/
structure CapturedFn where
  name : String
  visibility : Visibility := .pub
  callee : Option PureCallee2 := none
  prog : MirBody
  pre : ExecQuery MirState → Prop := fun _ => True
  specs : List MirLang.Behavior := []

/-- Callee summary adequacy obligation for a captured function: if `fn` is
    registered as the implementation of `some cal`, `fn.prog` must satisfy
    `VerificationResultOn` for `(CalleePre2 cal, [CalleeSpec2 cal])`, ensuring
    that `evalPureCallee2 cal` cannot assume a weaker precondition or return a
    different value than `fn.prog` actually implements. -/
def CalleeSummaryVerified (tcb : List TCBItem) (fn : CapturedFn) : Prop :=
  match fn.callee with
  | none => True
  | some cal =>
    VerificationResultOn RustcCompiler defaultTrustPolicy tcb
      fn.prog (CalleePre2 cal) [CalleeSpec2 cal]

structure Crate where
  functions : List CapturedFn
  tcb : List TCBItem

/-- Top-level crate theorem:
    1. The crate contains at least one captured function (`c.functions ≠ []`).
    2. Every function `fn ∈ c.functions` (both `.pub` and `.priv`) satisfies
       `VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog
       fn.pre fn.specs`.
    3. Every function `fn ∈ c.functions` registered as an interprocedural callee
       (`fn.callee = some cal`) satisfies `CalleeSummaryVerified c.tcb fn`. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  AllHold (c.functions.map (fun fn =>
    VerificationResultOn RustcCompiler defaultTrustPolicy c.tcb fn.prog fn.pre fn.specs ∧
    CalleeSummaryVerified c.tcb fn))

/-- Predicate asserting that every public function (`fn.visibility = .pub`) in
    crate `c` has an unconditional entry contract (`∀ q, fn.pre q`), even if
    private helper functions (`fn.visibility = .priv`) have conditional
    contracts. -/
def PublicApiUnconditional (c : Crate) : Prop :=
  AllHold (c.functions.map (fun fn =>
    fn.visibility = .pub → ∀ q, fn.pre q))

/-!
## 4. Plan-Guided Shallow Functional Translation with Conditional `SpecOn`
-/

inductive AeneasRes (Val : Type) where
  | ok (v : Val)
  | inapplicable
  | fail

def FuncLang : Language where
  Prog := MirState → AeneasRes MirVal
  Query := MirState
  Out := MirVal
  sem p init := {
    defined := p init ≠ .fail
    val := fun _ v => p init = .ok v
  }

def π_func (b : FuncLang.Behavior) : MirLang.Behavior :=
  fun q =>
    Partial.map
      (fun (post : MirVal → Prop) (out : ExecOut Unit MirVal) =>
        out.outcome.isSafe ∧
        ∀ ret, out.outcome = .terminated (.normal ret) → post ret)
      (b q.init)

theorem monotone_π_func : Monotone π_func :=
  fun _ _ hb q =>
    Partial.monotone_map
      (by intro _ _ hle out ⟨hsafe, hret⟩; exact ⟨hsafe, fun r hr => hle r (hret r hr)⟩)
      (hb q.init)

/-- Pointwise elimination of `FuncLang.sem p ≤ FuncLang.SpecOn Pre Post`:
    requires `p init ≠ .fail` and `Post init ret` only at states `init`
    satisfying `Pre init`. -/
theorem funcSem_le_specOn {p : MirState → AeneasRes MirVal}
    {Pre : MirState → Prop}
    {Post : MirState → MirVal → Prop}
    (hEval : ∀ init, Pre init → p init ≠ .fail ∧ (∀ ret, p init = .ok ret → Post init ret)) :
    FuncLang.sem p ≤ FuncLang.SpecOn Pre Post :=
  fun init hPre => ⟨(hEval init hPre).1, (hEval init hPre).2⟩

/-- Pointwise elimination of `FuncLang.sem p ≤ FuncLang.Spec Post`
    (specialization of `funcSem_le_specOn` to `Pre := fun _ => True`). -/
theorem funcSem_le_spec {p : MirState → AeneasRes MirVal}
    {Post : MirState → MirVal → Prop}
    (hEval : ∀ init, p init ≠ .fail ∧ (∀ ret, p init = .ok ret → Post init ret)) :
    FuncLang.sem p ≤ FuncLang.Spec Post :=
  funcSem_le_specOn (fun init _ => hEval init)

/-- Conditional specification bridge across `π_func`: any conditional functional
    specification `FuncLang.SpecOn Pre Post` maps under `π_func` to a behavior
    that refines `MirLang.SpecOn (fun q => Pre q.init) ...`. -/
theorem π_func_specOn_le (Pre : MirState → Prop) (Post : MirState → MirVal → Prop) :
    π_func (FuncLang.SpecOn Pre Post) ≤
      MirLang.SpecOn (fun q => Pre q.init) (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → Post q.init ret) :=
  fun _ hPre => ⟨hPre, fun _ hout => hout.2⟩

/-- Unconditional specification bridge across `π_func` (specialization of
    `π_func_specOn_le` to `Pre := fun _ => True`). -/
theorem π_func_spec_le (Post : MirState → MirVal → Prop) :
    π_func (FuncLang.Spec Post) ≤
      MirLang.Spec (fun q out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → Post q.init ret) :=
  π_func_specOn_le (fun _ => True) Post

/-!
### 4.1 Small-Step Prefix Simulation Helpers (`SafeAndReturns`)
-/

def SafeAndReturns (body : MirBody) (s : MirState) (v : MirVal) : Prop :=
  ∀ (init : MirState) (steps : Nat) (tr : List Unit) (out : PrefixOutcome MirVal),
    ReachesPrefix MirMachine body init steps s tr out →
    out.isSafe ∧ (∀ ret, out = .terminated (.normal ret) → ret = v)

theorem SafeAndReturns.of_step {body : MirBody} {s s' : MirState} {v : MirVal}
    (hstep : evalMirStep body s = .step () s')
    (hnext : SafeAndReturns body s' v) :
    SafeAndReturns body s v := by
  intro init steps tr out hreach
  cases hreach with
  | zero =>
    exact ⟨True.intro, fun _ h => by cases h⟩
  | step n _ s'' obs tr' out h1 h2 =>
    have h1' : StepResult.step obs s'' = evalMirStep body s := h1
    rw [hstep] at h1'
    injection h1' with _ hs''
    subst hs''
    exact hnext init n tr' out h2
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hstep.symm⟩)

theorem SafeAndReturns.of_terminated {body : MirBody} {s : MirState} {v : MirVal}
    (hterm : evalMirStep body s = .terminated (.normal v)) :
    SafeAndReturns body s v := by
  intro init steps tr out hreach
  cases hreach with
  | zero =>
    exact ⟨True.intro, fun _ h => by cases h⟩
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | terminated _ _ term h1 =>
    have h1' : StepResult.terminated term = evalMirStep body s := h1
    rw [hterm] at h1'
    injection h1' with hterm_eq
    subst hterm_eq
    refine ⟨True.intro, ?_⟩
    intro ret hret
    injection hret with hterm_ret
    injection hterm_ret with hret_eq
    exact hret_eq.symm
  | failed _ _ _ h1 =>
    have h1' : _ = evalMirStep body s := h1
    rw [hterm] at h1'; cases h1'
  | noStep _ _ hnostep =>
    exact False.elim (hnostep ⟨_, hterm.symm⟩)

/-!
### 4.2 Symbolic Values (`SymVal`), Plans (`TransPlan`), and Symbolic Evaluator
-/

inductive SymVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)

def SymVal.toScalarMirVal : SymVal → Option MirVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | .tupleUsizeBool val ov => some (.tupleUsizeBool val ov)

def zipAeneasRes (b : Bool) (tRes fRes : AeneasRes MirVal) : AeneasRes MirVal :=
  match tRes, fRes with
  | .ok (.usize nt), .ok (.usize nf) => .ok (.usize (if b then nt else nf))
  | .ok (.bool bt), .ok (.bool bf) => .ok (.bool (if b then bt else bf))
  | .ok .unit, .ok .unit => .ok .unit
  | _, _ => if b then tRes else fRes

theorem zipAeneasRes_eq_ite (b : Bool) (tRes fRes : AeneasRes MirVal) :
    zipAeneasRes b tRes fRes = (if b then tRes else fRes) := by
  cases b <;> cases tRes with
  | inapplicable => rfl
  | fail => rfl
  | ok vt =>
    cases vt <;> cases fRes with
    | inapplicable => rfl
    | fail => rfl
    | ok vf => cases vf <;> rfl

structure SymState where
  locals : Nat → Option SymVal
  block : Nat
  stmtIdx : Nat

def updateSymLocal (locals : Nat → Option SymVal) (target : Nat)
    (val : Option SymVal) : Nat → Option SymVal :=
  fun i => if i == target then val else locals i

inductive TransPlan where
  | ret
  | step (next : TransPlan)
  | branch (falsePlan : TransPlan) (truePlan : TransPlan)
  | fail

def evalSymConst : MirVal → Option SymVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | _ => none

def evalSymOperand (locals : Nat → Option SymVal) (op : Operand) :
    Option (SymVal × (Nat → Option SymVal)) :=
  match op with
  | .copy src =>
    match locals src.index with
    | some sv => some (sv, locals)
    | none => none
  | .move src =>
    match locals src.index with
    | some sv => some (sv, updateSymLocal locals src.index none)
    | none => none
  | .constVal mv =>
    match evalSymConst mv with
    | some sv => some (sv, locals)
    | none => none

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

/-- Spine-preserving symbolic evaluation of `PureCallee2`:
    returns `some (violated, res)` with the outer `some` and `.usize`
    constructors exposed so `evalSymStep` and `evalSymState` reduce across
    interprocedural calls on symbolic `x0, y0 : Nat` via kernel `rfl`, emitting
    `if violated then .fail else ...` for the caller to discharge. -/
def evalSymPureCallee2 (callee : PureCallee2) (v1 v2 : SymVal) :
    Option (Bool × SymVal) :=
  match v1, v2 with
  | .usize x0, .usize y0 =>
    match callee with
    | .addBounded =>
      some (false, .usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0))
    | .absDiff =>
      some (false, .usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0))
    | .add =>
      some (decide (usizeMax < x0 + y0), .usize (x0 + y0))
  | _, _ => none

def evalSymStmt (sym : SymState) (stmt : Stmt) : Option SymState :=
  match stmt with
  | .assign dst (.use op) =>
    match evalSymOperand sym.locals op with
    | some (sv, locals') =>
      some { sym with
        locals := updateSymLocal locals' dst.index (some sv)
        stmtIdx := sym.stmtIdx + 1
      }
    | none => none
  | .assign dst (.proj0 src) =>
    match sym.locals src.index with
    | some (.tupleUsizeBool val _) =>
      some { sym with
        locals := updateSymLocal sym.locals dst.index (some (.usize val))
        stmtIdx := sym.stmtIdx + 1
      }
    | _ => none
  | .assign dst (.proj1 src) =>
    match sym.locals src.index with
    | some (.tupleUsizeBool _ ov) =>
      some { sym with
        locals := updateSymLocal sym.locals dst.index (some (.bool ov))
        stmtIdx := sym.stmtIdx + 1
      }
    | _ => none
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalSymOperand sym.locals lhs with
    | none => none
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | none => none
      | some (v2, locals2) =>
        match evalSymBinOp op v1 v2 with
        | some res =>
          some { sym with
            locals := updateSymLocal locals2 dst.index (some res)
            stmtIdx := sym.stmtIdx + 1
          }
        | none => none
  | .assign dst (.checkedBinaryOp op lhs rhs) =>
    match evalSymOperand sym.locals lhs with
    | none => none
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | none => none
      | some (v2, locals2) =>
        match evalSymCheckedBinOp op v1 v2 with
        | some res =>
          some { sym with
            locals := updateSymLocal locals2 dst.index (some res)
            stmtIdx := sym.stmtIdx + 1
          }
        | none => none
  | .storageLive loc =>
    some { sym with
      locals := updateSymLocal sym.locals loc.index none
      stmtIdx := sym.stmtIdx + 1
    }
  | .storageDead loc =>
    some { sym with
      locals := updateSymLocal sym.locals loc.index none
      stmtIdx := sym.stmtIdx + 1
    }
  | .nop =>
    some { sym with stmtIdx := sym.stmtIdx + 1 }
  | .assign _ (.deref _) | .assignDeref _ _ =>
    none

/-- Execute one statement, `goto`, `assertNotOverflow`, or `callPure2` step in
    `sym`, returning `some (violated, sym')` where `violated` is the overflow or
    callee precondition violation flag. -/
def evalSymStep (body : MirBody) (sym : SymState) : Option (Bool × SymState) :=
  match body.blocks[sym.block]? with
  | none => none
  | some bb =>
    match bb.stmts[sym.stmtIdx]? with
    | some stmt =>
      match evalSymStmt sym stmt with
      | some sym' => some (false, sym')
      | none => none
    | none =>
      match bb.terminator with
      | .goto target =>
        some (false, { sym with block := target.index, stmtIdx := 0 })
      | .assertNotOverflow tupleLocal target =>
        match sym.locals tupleLocal.index with
        | some (.tupleUsizeBool _ ov) =>
          some (ov, { sym with block := target.index, stmtIdx := 0 })
        | _ => none
      | .callPure2 dst callee arg1 arg2 target =>
        match evalSymOperand sym.locals arg1 with
        | none => none
        | some (v1, locals1) =>
          match evalSymOperand locals1 arg2 with
          | none => none
          | some (v2, locals2) =>
            match evalSymPureCallee2 callee v1 v2 with
            | some (ov, res) =>
              some (ov, {
                sym with
                locals := updateSymLocal locals2 dst.index (some res)
                block := target.index
                stmtIdx := 0
              })
            | none => none
      | _ => none

def evalReturn (body : MirBody) (sym : SymState) : Option MirVal :=
  match body.blocks[sym.block]? with
  | none => none
  | some bb =>
    match bb.stmts[sym.stmtIdx]?, bb.terminator with
    | none, .return_ =>
      match sym.locals 0 with
      | some sv => sv.toScalarMirVal
      | none => none
    | _, _ => none

def evalBranchStep (body : MirBody) (sym : SymState) :
    Option (Bool × SymState × SymState) :=
  match body.blocks[sym.block]? with
  | none => none
  | some bb =>
    match bb.stmts[sym.stmtIdx]?, bb.terminator with
    | none, .switchInt discr falseTarget trueTarget =>
      match evalSymOperand sym.locals discr with
      | some (.bool cond, locals') =>
        let symFalse := { sym with locals := locals', block := falseTarget.index, stmtIdx := 0 }
        let symTrue := { sym with locals := locals', block := trueTarget.index, stmtIdx := 0 }
        some (cond, symFalse, symTrue)
      | _ => none
    | _, _ => none

noncomputable def evalSymState (plan : TransPlan) (body : MirBody) (sym : SymState) :
    AeneasRes MirVal :=
  match plan with
  | .ret =>
    match evalReturn body sym with
    | some mv => .ok mv
    | none => .fail
  | .step next =>
    match evalSymStep body sym with
    | some (ov, sym') =>
      if ov then .fail else evalSymState next body sym'
    | none => .fail
  | .branch falsePlan truePlan =>
    match evalBranchStep body sym with
    | some (cond, symFalse, symTrue) =>
      zipAeneasRes cond
        (evalSymState truePlan body symTrue)
        (evalSymState falsePlan body symFalse)
    | none => .fail
  | .fail => .fail

inductive SymArg where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit

def emptySymLocals : Nat → Option SymVal := fun _ => none

noncomputable def buildPureSymStateAux (idx : Nat) : List SymArg → (Nat → Option SymVal)
  | [] => emptySymLocals
  | arg :: rest =>
    let locals := buildPureSymStateAux (idx + 1) rest
    match arg with
    | .usize n => updateSymLocal locals idx (some (.usize n))
    | .bool b => updateSymLocal locals idx (some (.bool b))
    | .unit => updateSymLocal locals idx (some .unit)

noncomputable def buildPureSymState (args : List SymArg) : SymState :=
  { locals := buildPureSymStateAux 1 args
    block := 0
    stmtIdx := 0 }

noncomputable def translatePure (plan : TransPlan) (body : MirBody) (args : List SymArg) :
    AeneasRes MirVal :=
  evalSymState plan body (buildPureSymState args)

noncomputable def extractSymArgsAux (idx : Nat) : List MirTy → MirState → Option (List SymArg)
  | [], _ => some []
  | ty :: restTys, init =>
    match ty, init.locals idx with
    | .usize, some (.usize n) =>
      match extractSymArgsAux (idx + 1) restTys init with
      | some restArgs => some (.usize n :: restArgs)
      | none => none
    | .bool, some (.bool b) =>
      match extractSymArgsAux (idx + 1) restTys init with
      | some restArgs => some (.bool b :: restArgs)
      | none => none
    | .unit, some .unit =>
      match extractSymArgsAux (idx + 1) restTys init with
      | some restArgs => some (.unit :: restArgs)
      | none => none
    | _, _ => none

def isSupportedArgTy : MirTy → Bool
  | .usize => true
  | .bool => true
  | .unit => true
  | _ => false

noncomputable def allSupportedArgTys (tys : List MirTy) : Bool :=
  tys.all isSupportedArgTy

noncomputable def extractSymArgs (argTys : List MirTy) (init : MirState) : Option (List SymArg) :=
  if init.block == 0 && init.stmtIdx == 0 then
    extractSymArgsAux 1 argTys init
  else
    none

noncomputable def evalSym (plan : TransPlan) (body : MirBody) (init : MirState) :
    AeneasRes MirVal :=
  if allSupportedArgTys body.argTys then
    match extractSymArgs body.argTys init with
    | some args => translatePure plan body args
    | none => .inapplicable
  else
    .fail

/-!
### 4.3 Universal Soundness of `evalSym` with Conditional Callees
-/

def ValRel (sv : SymVal) (mv : MirVal) : Prop :=
  match sv with
  | .usize n => mv = .usize n
  | .bool b => mv = .bool b
  | .unit => mv = .unit
  | .tupleUsizeBool val ov => mv = .tupleUsizeBool val ov

theorem ValRel.toScalarMirVal_eq {sv : SymVal} {mv mv' : MirVal}
    (hRel : ValRel sv mv)
    (hScalar : sv.toScalarMirVal = some mv') :
    mv = mv' := by
  cases sv with
  | usize n => injection hScalar with h1; exact Eq.trans hRel h1
  | bool b => injection hScalar with h1; exact Eq.trans hRel h1
  | unit => injection hScalar with h1; exact Eq.trans hRel h1
  | tupleUsizeBool val ov => injection hScalar with h1; exact Eq.trans hRel h1

def LocalRel (symLocals : Nat → Option SymVal) (concLocals : Nat → Option MirVal) : Prop :=
  ∀ i sv, symLocals i = some sv → ∃ mv, concLocals i = some mv ∧ ValRel sv mv

theorem LocalRel.update_some {symLocals : Nat → Option SymVal} {concLocals : Nat → Option MirVal}
    (hRel : LocalRel symLocals concLocals)
    (dst : Nat) {sv : SymVal} {mv : MirVal} (hVal : ValRel sv mv) :
    LocalRel (updateSymLocal symLocals dst (some sv))
      (updateLocal concLocals dst (some mv)) := by
  intro i sv' hlookup
  unfold updateSymLocal at hlookup
  unfold updateLocal
  cases h : (i == dst) with
  | false =>
    rw [h] at hlookup
    exact hRel i sv' hlookup
  | true =>
    rw [h] at hlookup
    injection hlookup with heq
    subst heq
    exact ⟨mv, rfl, hVal⟩

theorem LocalRel.update_none {symLocals : Nat → Option SymVal} {concLocals : Nat → Option MirVal}
    (hRel : LocalRel symLocals concLocals) (dst : Nat) :
    LocalRel (updateSymLocal symLocals dst none)
      (updateLocal concLocals dst none) := by
  intro i sv' hlookup
  unfold updateSymLocal at hlookup
  unfold updateLocal
  cases h : (i == dst) with
  | false =>
    rw [h] at hlookup
    exact hRel i sv' hlookup
  | true =>
    rw [h] at hlookup
    cases hlookup

structure StateRel (sym : SymState) (conc : MirState) : Prop where
  block_eq : conc.block = sym.block
  stmtIdx_eq : conc.stmtIdx = sym.stmtIdx
  localRel : LocalRel sym.locals conc.locals

theorem evalSymOperand_sound
    {symLocals symLocals' : Nat → Option SymVal}
    {concLocals : Nat → Option MirVal}
    {op : Operand} {sv : SymVal}
    (hRel : LocalRel symLocals concLocals)
    (hEval : evalSymOperand symLocals op = some (sv, symLocals')) :
    ∃ mv concLocals',
      evalOperand concLocals op = some (mv, concLocals') ∧
      ValRel sv mv ∧
      LocalRel symLocals' concLocals' := by
  cases op with
  | copy src =>
    dsimp [evalSymOperand] at hEval
    cases hsrc : symLocals src.index with
    | none => rw [hsrc] at hEval; cases hEval
    | some sv0 =>
      rw [hsrc] at hEval
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      cases hRel src.index sv0 hsrc with
      | intro mv hmv =>
        refine ⟨mv, concLocals, ?_, hmv.2, hRel⟩
        dsimp [evalOperand]
        rw [hmv.1]
  | move src =>
    dsimp [evalSymOperand] at hEval
    cases hsrc : symLocals src.index with
    | none => rw [hsrc] at hEval; cases hEval
    | some sv0 =>
      rw [hsrc] at hEval
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      cases hRel src.index sv0 hsrc with
      | intro mv hmv =>
        refine ⟨mv, updateLocal concLocals src.index none, ?_, hmv.2,
          LocalRel.update_none hRel src.index⟩
        dsimp [evalOperand]
        rw [hmv.1]
  | constVal mv0 =>
    dsimp [evalSymOperand] at hEval
    cases mv0 with
    | usize n =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨.usize n, concLocals, rfl, rfl, hRel⟩
    | bool b =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨.bool b, concLocals, rfl, rfl, hRel⟩
    | unit =>
      injection hEval with hpair
      injection hpair with hsv hloc
      subst hsv hloc
      exact ⟨.unit, concLocals, rfl, rfl, hRel⟩
    | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
      cases hEval

theorem evalSymBinOp_sound
    {op : BinOp} {sv1 sv2 res : SymVal} {mv1 mv2 : MirVal}
    (hVal1 : ValRel sv1 mv1)
    (hVal2 : ValRel sv2 mv2)
    (hBin : evalSymBinOp op sv1 sv2 = some res) :
    ∃ mres, evalBinOp op mv1 mv2 = some mres ∧ ValRel res mres := by
  cases sv1 with
  | bool _ | unit | tupleUsizeBool _ _ => cases hBin
  | usize n1 =>
    cases sv2 with
    | bool _ | unit | tupleUsizeBool _ _ => cases hBin
    | usize n2 =>
      subst hVal1 hVal2
      cases op <;> (injection hBin with hres; subst hres; exact ⟨_, rfl, rfl⟩)

theorem evalSymCheckedBinOp_sound
    {op : CheckedBinOp} {sv1 sv2 res : SymVal} {mv1 mv2 : MirVal}
    (hVal1 : ValRel sv1 mv1)
    (hVal2 : ValRel sv2 mv2)
    (hBin : evalSymCheckedBinOp op sv1 sv2 = some res) :
    ∃ mres, evalCheckedBinOp op mv1 mv2 = some mres ∧ ValRel res mres := by
  cases sv1 with
  | bool _ | unit | tupleUsizeBool _ _ => cases hBin
  | usize n1 =>
    cases sv2 with
    | bool _ | unit | tupleUsizeBool _ _ => cases hBin
    | usize n2 =>
      subst hVal1 hVal2
      cases op <;> (injection hBin with hres; subst hres; exact ⟨_, rfl, rfl⟩)

/-- Soundness of `evalSymPureCallee2`: whenever symbolic evaluation of `callee`
    succeeds with `ov = false` (`some (false, res)`), concrete `evalPureCallee2`
    also produces `some (false, mres)` with `ValRel res mres`. -/
theorem evalSymPureCallee2_sound
    {callee : PureCallee2} {v1 v2 res : SymVal} {mv1 mv2 : MirVal} {ov : Bool}
    (hVal1 : ValRel v1 mv1)
    (hVal2 : ValRel v2 mv2)
    (hCall : evalSymPureCallee2 callee v1 v2 = some (ov, res)) :
    ∃ mres,
      evalPureCallee2 callee mv1 mv2 = some (ov, mres) ∧
      ValRel res mres := by
  cases v1 with
  | bool _ | unit | tupleUsizeBool _ _ => cases hCall
  | usize x0 =>
    cases v2 with
    | bool _ | unit | tupleUsizeBool _ _ => cases hCall
    | usize y0 =>
      subst hVal1 hVal2
      cases callee with
      | addBounded =>
        injection hCall with hpair
        injection hpair with hov hres
        subst hov hres
        exact ⟨.usize (if decide (x0 ≤ 1000) && decide (y0 ≤ 1000) then x0 + y0 else 0), rfl, rfl⟩
      | absDiff =>
        injection hCall with hpair
        injection hpair with hov hres
        subst hov hres
        exact ⟨.usize (if decide (y0 ≤ x0) then x0 - y0 else y0 - x0), rfl, rfl⟩
      | add =>
        injection hCall with hpair
        injection hpair with hov hres
        subst hov hres
        exact ⟨.usize (x0 + y0), rfl, rfl⟩

theorem evalReturn_sound
    {body : MirBody} {sym : SymState} {conc : MirState} {mv : MirVal}
    (hState : StateRel sym conc)
    (hRet : evalReturn body sym = some mv) :
    SafeAndReturns body conc mv := by
  unfold evalReturn at hRet
  cases hbb : body.blocks[sym.block]? with
  | none => rw [hbb] at hRet; cases hRet
  | some bb =>
    rw [hbb] at hRet
    dsimp at hRet
    cases hstmt : bb.stmts[sym.stmtIdx]? with
    | some _ => rw [hstmt] at hRet; cases hRet
    | none =>
      rw [hstmt] at hRet
      cases hterm : bb.terminator with
      | goto _ | unreachable | switchInt _ _ _ | assertNotOverflow _ _ | callPure2 _ _ _ _ _ =>
        rw [hterm] at hRet; cases hRet
      | return_ =>
        rw [hterm] at hRet
        dsimp at hRet
        cases hloc0 : sym.locals 0 with
        | none => rw [hloc0] at hRet; cases hRet
        | some sv0 =>
          rw [hloc0] at hRet
          have ⟨mv0, hconc0, hval0⟩ := hState.localRel 0 sv0 hloc0
          have hmv_eq : mv0 = mv := ValRel.toScalarMirVal_eq hval0 hRet
          subst hmv_eq
          refine SafeAndReturns.of_terminated ?_
          unfold evalMirStep
          rw [hState.block_eq, hbb]
          dsimp
          rw [hState.stmtIdx_eq, hstmt]
          dsimp
          rw [hterm]
          dsimp [evalMirTerminator]
          rw [hconc0]

theorem evalSymStmt_sound
    {sym sym' : SymState} {conc : MirState} {stmt : Stmt}
    (hState : StateRel sym conc)
    (hStmt : evalSymStmt sym stmt = some sym') :
    ∃ conc',
      evalMirStmt conc stmt = .step () conc' ∧
      StateRel sym' conc' := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalSymStmt] at hStmt
      cases hOp : evalSymOperand sym.locals op with
      | none => rw [hOp] at hStmt; cases hStmt
      | some p =>
        cases p with
        | mk sv locals' =>
          rw [hOp] at hStmt
          injection hStmt with hsym'
          subst hsym'
          have ⟨mv, concLocals', hConcOp, hVal, hLocRel'⟩ :=
            evalSymOperand_sound hState.localRel hOp
          refine ⟨{ conc with
            locals := updateLocal concLocals' dst.index (some mv)
            stmtIdx := conc.stmtIdx + 1
          }, ?_, ?_⟩
          · dsimp [evalMirStmt]; rw [hConcOp]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localRel := LocalRel.update_some hLocRel' dst.index hVal
            }
    | deref _ => cases hStmt
    | proj0 src =>
      dsimp [evalSymStmt] at hStmt
      cases hsrc : sym.locals src.index with
      | none => rw [hsrc] at hStmt; cases hStmt
      | some svSrc =>
        rw [hsrc] at hStmt
        cases svSrc with
        | usize _ | bool _ | unit => cases hStmt
        | tupleUsizeBool val ov =>
          dsimp at hStmt
          injection hStmt with hsym'
          subst hsym'
          have ⟨mvSrc, hconcSrc, hvalSrc⟩ :=
            hState.localRel src.index (.tupleUsizeBool val ov) hsrc
          subst hvalSrc
          refine ⟨{ conc with
            locals := updateLocal conc.locals dst.index (some (.usize val))
            stmtIdx := conc.stmtIdx + 1
          }, ?_, ?_⟩
          · dsimp [evalMirStmt]; rw [hconcSrc]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localRel := LocalRel.update_some hState.localRel dst.index rfl
            }
    | proj1 src =>
      dsimp [evalSymStmt] at hStmt
      cases hsrc : sym.locals src.index with
      | none => rw [hsrc] at hStmt; cases hStmt
      | some svSrc =>
        rw [hsrc] at hStmt
        cases svSrc with
        | usize _ | bool _ | unit => cases hStmt
        | tupleUsizeBool val ov =>
          dsimp at hStmt
          injection hStmt with hsym'
          subst hsym'
          have ⟨mvSrc, hconcSrc, hvalSrc⟩ :=
            hState.localRel src.index (.tupleUsizeBool val ov) hsrc
          subst hvalSrc
          refine ⟨{ conc with
            locals := updateLocal conc.locals dst.index (some (.bool ov))
            stmtIdx := conc.stmtIdx + 1
          }, ?_, ?_⟩
          · dsimp [evalMirStmt]; rw [hconcSrc]
          · exact {
              block_eq := hState.block_eq
              stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
              localRel := LocalRel.update_some hState.localRel dst.index rfl
            }
    | binaryOp op lhs rhs =>
      dsimp [evalSymStmt] at hStmt
      cases hOp1 : evalSymOperand sym.locals lhs with
      | none => rw [hOp1] at hStmt; cases hStmt
      | some p1 =>
        cases p1 with
        | mk v1 locals1 =>
          rw [hOp1] at hStmt
          dsimp at hStmt
          cases hOp2 : evalSymOperand locals1 rhs with
          | none => rw [hOp2] at hStmt; cases hStmt
          | some p2 =>
            cases p2 with
            | mk v2 locals2 =>
              rw [hOp2] at hStmt
              dsimp at hStmt
              cases hBin : evalSymBinOp op v1 v2 with
              | none => rw [hBin] at hStmt; cases hStmt
              | some res =>
                rw [hBin] at hStmt
                injection hStmt with hsym'
                subst hsym'
                have ⟨mv1, concLocals1, hConcOp1, hVal1, hLocRel1⟩ :=
                  evalSymOperand_sound hState.localRel hOp1
                have ⟨mv2, concLocals2, hConcOp2, hVal2, hLocRel2⟩ :=
                  evalSymOperand_sound hLocRel1 hOp2
                have ⟨mres, hConcBin, hValRes⟩ :=
                  evalSymBinOp_sound hVal1 hVal2 hBin
                refine ⟨{ conc with
                  locals := updateLocal concLocals2 dst.index (some mres)
                  stmtIdx := conc.stmtIdx + 1
                }, ?_, ?_⟩
                · dsimp [evalMirStmt]; rw [hConcOp1]; dsimp; rw [hConcOp2]; dsimp; rw [hConcBin]
                · exact {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localRel := LocalRel.update_some hLocRel2 dst.index hValRes
                  }
    | checkedBinaryOp op lhs rhs =>
      dsimp [evalSymStmt] at hStmt
      cases hOp1 : evalSymOperand sym.locals lhs with
      | none => rw [hOp1] at hStmt; cases hStmt
      | some p1 =>
        cases p1 with
        | mk v1 locals1 =>
          rw [hOp1] at hStmt
          dsimp at hStmt
          cases hOp2 : evalSymOperand locals1 rhs with
          | none => rw [hOp2] at hStmt; cases hStmt
          | some p2 =>
            cases p2 with
            | mk v2 locals2 =>
              rw [hOp2] at hStmt
              dsimp at hStmt
              cases hBin : evalSymCheckedBinOp op v1 v2 with
              | none => rw [hBin] at hStmt; cases hStmt
              | some res =>
                rw [hBin] at hStmt
                injection hStmt with hsym'
                subst hsym'
                have ⟨mv1, concLocals1, hConcOp1, hVal1, hLocRel1⟩ :=
                  evalSymOperand_sound hState.localRel hOp1
                have ⟨mv2, concLocals2, hConcOp2, hVal2, hLocRel2⟩ :=
                  evalSymOperand_sound hLocRel1 hOp2
                have ⟨mres, hConcBin, hValRes⟩ :=
                  evalSymCheckedBinOp_sound hVal1 hVal2 hBin
                refine ⟨{ conc with
                  locals := updateLocal concLocals2 dst.index (some mres)
                  stmtIdx := conc.stmtIdx + 1
                }, ?_, ?_⟩
                · dsimp [evalMirStmt]; rw [hConcOp1]; dsimp; rw [hConcOp2]; dsimp; rw [hConcBin]
                · exact {
                    block_eq := hState.block_eq
                    stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
                    localRel := LocalRel.update_some hLocRel2 dst.index hValRes
                  }
  | assignDeref _ _ => cases hStmt
  | storageLive loc =>
    dsimp [evalSymStmt] at hStmt
    injection hStmt with hsym'
    subst hsym'
    refine ⟨{ conc with
      locals := updateLocal conc.locals loc.index none
      stmtIdx := conc.stmtIdx + 1
    }, rfl, ?_⟩
    exact {
      block_eq := hState.block_eq
      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
      localRel := LocalRel.update_none hState.localRel loc.index
    }
  | storageDead loc =>
    dsimp [evalSymStmt] at hStmt
    injection hStmt with hsym'
    subst hsym'
    refine ⟨{ conc with
      locals := updateLocal conc.locals loc.index none
      stmtIdx := conc.stmtIdx + 1
    }, rfl, ?_⟩
    exact {
      block_eq := hState.block_eq
      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
      localRel := LocalRel.update_none hState.localRel loc.index
    }
  | nop =>
    dsimp [evalSymStmt] at hStmt
    injection hStmt with hsym'
    subst hsym'
    refine ⟨{ conc with stmtIdx := conc.stmtIdx + 1 }, rfl, ?_⟩
    exact {
      block_eq := hState.block_eq
      stmtIdx_eq := by dsimp; rw [hState.stmtIdx_eq]
      localRel := hState.localRel
    }

theorem evalSymStep_sound
    {body : MirBody} {sym sym' : SymState} {conc : MirState}
    (hState : StateRel sym conc)
    (hStep : evalSymStep body sym = some (false, sym')) :
    ∃ conc',
      evalMirStep body conc = .step () conc' ∧
      StateRel sym' conc' := by
  unfold evalSymStep at hStep
  cases hbb : body.blocks[sym.block]? with
  | none => rw [hbb] at hStep; cases hStep
  | some bb =>
    rw [hbb] at hStep
    dsimp at hStep
    cases hstmt : bb.stmts[sym.stmtIdx]? with
    | some stmt =>
      rw [hstmt] at hStep
      dsimp at hStep
      cases hSymStmt : evalSymStmt sym stmt with
      | none => rw [hSymStmt] at hStep; cases hStep
      | some sym1 =>
        rw [hSymStmt] at hStep
        injection hStep with hpair
        injection hpair with _ hsym'
        subst hsym'
        have ⟨conc', hConcStmt, hState'⟩ := evalSymStmt_sound hState hSymStmt
        refine ⟨conc', ?_, hState'⟩
        unfold evalMirStep
        rw [hState.block_eq, hbb]
        dsimp
        rw [hState.stmtIdx_eq, hstmt]
        exact hConcStmt
    | none =>
      rw [hstmt] at hStep
      dsimp at hStep
      cases hterm : bb.terminator with
      | return_ | unreachable | switchInt _ _ _ =>
        rw [hterm] at hStep; cases hStep
      | goto target =>
        rw [hterm] at hStep
        injection hStep with hpair
        injection hpair with _ hsym'
        subst hsym'
        refine ⟨{ conc with block := target.index, stmtIdx := 0 }, ?_, ?_⟩
        · unfold evalMirStep
          rw [hState.block_eq, hbb]; dsimp
          rw [hState.stmtIdx_eq, hstmt]; dsimp
          rw [hterm]; rfl
        · exact {
            block_eq := rfl
            stmtIdx_eq := rfl
            localRel := hState.localRel
          }
      | assertNotOverflow tupleLocal target =>
        rw [hterm] at hStep
        dsimp at hStep
        cases hloc : sym.locals tupleLocal.index with
        | none => rw [hloc] at hStep; cases hStep
        | some sv =>
          rw [hloc] at hStep
          cases sv with
          | usize _ | bool _ | unit => cases hStep
          | tupleUsizeBool val ov =>
            dsimp at hStep
            injection hStep with hpair
            injection hpair with hov hsym'
            subst hov hsym'
            have ⟨mv, hconcLoc, hVal⟩ :=
              hState.localRel tupleLocal.index (.tupleUsizeBool val false) hloc
            subst hVal
            refine ⟨{ conc with block := target.index, stmtIdx := 0 }, ?_, ?_⟩
            · unfold evalMirStep
              rw [hState.block_eq, hbb]; dsimp
              rw [hState.stmtIdx_eq, hstmt]; dsimp
              rw [hterm]; dsimp [evalMirTerminator]
              rw [hconcLoc]
            · exact {
                block_eq := rfl
                stmtIdx_eq := rfl
                localRel := hState.localRel
              }
      | callPure2 dst callee arg1 arg2 target =>
        rw [hterm] at hStep
        dsimp at hStep
        cases hOp1 : evalSymOperand sym.locals arg1 with
        | none => rw [hOp1] at hStep; cases hStep
        | some p1 =>
          cases p1 with
          | mk v1 locals1 =>
            rw [hOp1] at hStep
            dsimp at hStep
            cases hOp2 : evalSymOperand locals1 arg2 with
            | none => rw [hOp2] at hStep; cases hStep
            | some p2 =>
              cases p2 with
              | mk v2 locals2 =>
                rw [hOp2] at hStep
                dsimp at hStep
                cases hCall : evalSymPureCallee2 callee v1 v2 with
                | none => rw [hCall] at hStep; cases hStep
                | some pCall =>
                  cases pCall with
                  | mk ov res =>
                    rw [hCall] at hStep
                    injection hStep with hpair
                    injection hpair with hov hsym'
                    subst hov hsym'
                    have ⟨mv1, concLocals1, hConcOp1, hVal1, hLocRel1⟩ :=
                      evalSymOperand_sound hState.localRel hOp1
                    have ⟨mv2, concLocals2, hConcOp2, hVal2, hLocRel2⟩ :=
                      evalSymOperand_sound hLocRel1 hOp2
                    have ⟨mres, hConcCall, hValRes⟩ :=
                      evalSymPureCallee2_sound hVal1 hVal2 hCall
                    refine ⟨{ conc with
                      locals := updateLocal concLocals2 dst.index (some mres)
                      block := target.index
                      stmtIdx := 0
                    }, ?_, ?_⟩
                    · unfold evalMirStep
                      rw [hState.block_eq, hbb]; dsimp
                      rw [hState.stmtIdx_eq, hstmt]; dsimp
                      rw [hterm]; dsimp [evalMirTerminator]
                      rw [hConcOp1]; dsimp
                      rw [hConcOp2]; dsimp
                      rw [hConcCall]
                    · exact {
                        block_eq := rfl
                        stmtIdx_eq := rfl
                        localRel := LocalRel.update_some hLocRel2 dst.index hValRes
                      }

theorem evalBranchStep_sound
    {body : MirBody} {sym symFalse symTrue : SymState}
    {conc : MirState} {cond : Bool}
    (hState : StateRel sym conc)
    (hBranch : evalBranchStep body sym = some (cond, symFalse, symTrue)) :
    ∃ concNext,
      evalMirStep body conc = .step () concNext ∧
      StateRel (if cond then symTrue else symFalse) concNext := by
  unfold evalBranchStep at hBranch
  cases hbb : body.blocks[sym.block]? with
  | none => rw [hbb] at hBranch; cases hBranch
  | some bb =>
    rw [hbb] at hBranch
    dsimp at hBranch
    cases hstmt : bb.stmts[sym.stmtIdx]? with
    | some _ => rw [hstmt] at hBranch; cases hBranch
    | none =>
      rw [hstmt] at hBranch
      cases hterm : bb.terminator with
      | return_ | goto _ | unreachable | assertNotOverflow _ _ | callPure2 _ _ _ _ _ =>
        rw [hterm] at hBranch; cases hBranch
      | switchInt discr falseTarget trueTarget =>
        rw [hterm] at hBranch
        dsimp at hBranch
        cases hOp : evalSymOperand sym.locals discr with
        | none => rw [hOp] at hBranch; cases hBranch
        | some p =>
          cases p with
          | mk sv locals' =>
            rw [hOp] at hBranch
            cases sv with
            | usize _ | unit | tupleUsizeBool _ _ => cases hBranch
            | bool b =>
              dsimp at hBranch
              injection hBranch with htuple
              injection htuple with hb hpair
              injection hpair with hF hT
              subst hb hF hT
              have ⟨mv, concLocals', hConcOp, hVal, hLocRel'⟩ :=
                evalSymOperand_sound hState.localRel hOp
              subst hVal
              cases b with
              | false =>
                refine ⟨{ conc with
                  locals := concLocals'
                  block := falseTarget.index
                  stmtIdx := 0
                }, ?_, ?_⟩
                · unfold evalMirStep
                  rw [hState.block_eq, hbb]; dsimp
                  rw [hState.stmtIdx_eq, hstmt]; dsimp
                  rw [hterm]; dsimp [evalMirTerminator]
                  rw [hConcOp]
                · exact { block_eq := rfl, stmtIdx_eq := rfl, localRel := hLocRel' }
              | true =>
                refine ⟨{ conc with
                  locals := concLocals'
                  block := trueTarget.index
                  stmtIdx := 0
                }, ?_, ?_⟩
                · unfold evalMirStep
                  rw [hState.block_eq, hbb]; dsimp
                  rw [hState.stmtIdx_eq, hstmt]; dsimp
                  rw [hterm]; dsimp [evalMirTerminator]
                  rw [hConcOp]
                · exact { block_eq := rfl, stmtIdx_eq := rfl, localRel := hLocRel' }

theorem evalSymState_sound (plan : TransPlan) (body : MirBody) :
    ∀ {sym : SymState} {conc : MirState} {ret : MirVal},
      StateRel sym conc →
      evalSymState plan body sym = .ok ret →
      SafeAndReturns body conc ret := by
  induction plan with
  | fail =>
    intro _ _ _ _ hEval
    cases hEval
  | ret =>
    intro sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hRet : evalReturn body sym with
    | none => rw [hRet] at hEval; cases hEval
    | some mv =>
      rw [hRet] at hEval
      injection hEval with hmv
      subst hmv
      exact evalReturn_sound hState hRet
  | step next ih =>
    intro sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hStep : evalSymStep body sym with
    | none => rw [hStep] at hEval; cases hEval
    | some p =>
      cases p with
      | mk ov sym' =>
        rw [hStep] at hEval
        dsimp at hEval
        cases ov with
        | true => cases hEval
        | false =>
          dsimp at hEval
          have ⟨conc', hConcStep, hState'⟩ := evalSymStep_sound hState hStep
          exact SafeAndReturns.of_step hConcStep (ih hState' hEval)
  | branch falsePlan truePlan ihFalse ihTrue =>
    intro sym conc ret hState hEval
    unfold evalSymState at hEval
    cases hBr : evalBranchStep body sym with
    | none => rw [hBr] at hEval; cases hEval
    | some brTuple =>
      have ⟨cond, symFalse, symTrue⟩ := brTuple
      rw [hBr] at hEval
      dsimp at hEval
      rw [zipAeneasRes_eq_ite] at hEval
      have ⟨concNext, hConcStep, hStateNext⟩ := evalBranchStep_sound hState hBr
      cases cond with
      | false =>
        exact SafeAndReturns.of_step hConcStep (ihFalse hStateNext hEval)
      | true =>
        exact SafeAndReturns.of_step hConcStep (ihTrue hStateNext hEval)

theorem evalSymState_ne_inapplicable (plan : TransPlan) (body : MirBody) :
    ∀ (sym : SymState), evalSymState plan body sym ≠ .inapplicable := by
  induction plan with
  | fail => intro _ h; cases h
  | ret =>
    intro sym
    unfold evalSymState
    cases evalReturn body sym <;> intro h <;> cases h
  | step next ih =>
    intro sym
    unfold evalSymState
    cases evalSymStep body sym with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk ov sym' =>
        dsimp
        cases ov with
        | true => intro h; cases h
        | false => exact ih sym'
  | branch falsePlan truePlan ihFalse ihTrue =>
    intro sym
    unfold evalSymState
    cases evalBranchStep body sym with
    | none => intro h; cases h
    | some brTuple =>
      have ⟨cond, symFalse, symTrue⟩ := brTuple
      dsimp
      rw [zipAeneasRes_eq_ite]
      cases cond with
      | false => exact ihFalse symFalse
      | true => exact ihTrue symTrue

theorem extractSymArgsAux_spec :
    ∀ (tys : List MirTy) (idx : Nat) (init : MirState) (args : List SymArg),
      extractSymArgsAux idx tys init = some args →
      LocalRel (buildPureSymStateAux idx args) init.locals
  | [], _, _, args, hExt => by
    injection hExt with hargs
    subst hargs
    intro _ _ h
    cases h
  | ty :: restTys, idx, init, args, hExt => by
    dsimp [extractSymArgsAux] at hExt
    cases ty with
    | tupleUsizeBool | refAtomicUsize | refSharedUsize | refMutUsize | atomicOrdering =>
      cases hExt
    | usize =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
          cases hExt
        | usize n =>
          dsimp at hExt
          cases hRest : extractSymArgsAux (idx + 1) restTys init with
          | none => rw [hRest] at hExt; cases hExt
          | some restArgs =>
            rw [hRest] at hExt
            injection hExt with hargs
            subst hargs
            have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hRest
            intro i sv hlookup
            dsimp [buildPureSymStateAux] at hlookup
            unfold updateSymLocal at hlookup
            cases hb : (i == idx) with
            | true =>
              rw [hb] at hlookup
              injection hlookup with hsv
              have hi_eq : i = idx := of_decide_eq_true hb
              subst hi_eq hsv
              exact ⟨.usize n, hloc, rfl⟩
            | false =>
              rw [hb] at hlookup
              exact ih i sv hlookup
    | bool =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | usize _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
          cases hExt
        | bool b =>
          dsimp at hExt
          cases hRest : extractSymArgsAux (idx + 1) restTys init with
          | none => rw [hRest] at hExt; cases hExt
          | some restArgs =>
            rw [hRest] at hExt
            injection hExt with hargs
            subst hargs
            have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hRest
            intro i sv hlookup
            dsimp [buildPureSymStateAux] at hlookup
            unfold updateSymLocal at hlookup
            cases hb : (i == idx) with
            | true =>
              rw [hb] at hlookup
              injection hlookup with hsv
              have hi_eq : i = idx := of_decide_eq_true hb
              subst hi_eq hsv
              exact ⟨.bool b, hloc, rfl⟩
            | false =>
              rw [hb] at hlookup
              exact ih i sv hlookup
    | unit =>
      cases hloc : init.locals idx with
      | none => rw [hloc] at hExt; cases hExt
      | some mv =>
        rw [hloc] at hExt
        cases mv with
        | usize _ | bool _ | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
          cases hExt
        | unit =>
          dsimp at hExt
          cases hRest : extractSymArgsAux (idx + 1) restTys init with
          | none => rw [hRest] at hExt; cases hExt
          | some restArgs =>
            rw [hRest] at hExt
            injection hExt with hargs
            subst hargs
            have ih := extractSymArgsAux_spec restTys (idx + 1) init restArgs hRest
            intro i sv hlookup
            dsimp [buildPureSymStateAux] at hlookup
            unfold updateSymLocal at hlookup
            cases hb : (i == idx) with
            | true =>
              rw [hb] at hlookup
              injection hlookup with hsv
              have hi_eq : i = idx := of_decide_eq_true hb
              subst hi_eq hsv
              exact ⟨.unit, hloc, rfl⟩
            | false =>
              rw [hb] at hlookup
              exact ih i sv hlookup

theorem extractSymArgs_sound (argTys : List MirTy) (init : MirState) (args : List SymArg)
    (hExt : extractSymArgs argTys init = some args) :
    StateRel (buildPureSymState args) init := by
  unfold extractSymArgs at hExt
  cases hblk : (init.block == 0 && init.stmtIdx == 0) with
  | false => rw [hblk] at hExt; cases hExt
  | true =>
    rw [hblk] at hExt
    have hba := Eq.mp (Bool.and_eq_true _ _) hblk
    exact {
      block_eq := of_decide_eq_true hba.1
      stmtIdx_eq := of_decide_eq_true hba.2
      localRel := extractSymArgsAux_spec argTys 1 init args hExt
    }

theorem extractSymArgsAux_of_argsMatchLocals :
    ∀ (tys : List MirTy) (idx : Nat) (init : MirState),
      allSupportedArgTys tys = true →
      List.foldr
        (fun ty rest k => (∃ v, init.locals k = some v ∧ argValidAt init.mem init.locals k v ty) ∧ rest (k + 1))
        (fun k => ∀ j, k ≤ j → init.locals j = none)
        tys idx →
      ∃ args, extractSymArgsAux idx tys init = some args
  | [], _, _, _, _ => ⟨[], rfl⟩
  | ty :: restTys, idx, init, hSupp, hFold => by
    dsimp [allSupportedArgTys, List.all, List.foldr] at hSupp
    have hsa := Eq.mp (Bool.and_eq_true _ _) hSupp
    have ⟨⟨v, hvLoc, hvValid⟩, hRestFold⟩ := hFold
    have ⟨restArgs, hRestExt⟩ :=
      extractSymArgsAux_of_argsMatchLocals restTys (idx + 1) init hsa.2 hRestFold
    cases ty with
    | tupleUsizeBool | refAtomicUsize | refSharedUsize | refMutUsize | atomicOrdering =>
      cases hsa.1
    | usize =>
      cases v with
      | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
        cases hvValid
      | usize n =>
        refine ⟨.usize n :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]; rw [hvLoc]; dsimp; rw [hRestExt]
    | bool =>
      cases v with
      | usize _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
        cases hvValid
      | bool b =>
        refine ⟨.bool b :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]; rw [hvLoc]; dsimp; rw [hRestExt]
    | unit =>
      cases v with
      | usize _ | bool _ | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
        cases hvValid
      | unit =>
        refine ⟨.unit :: restArgs, ?_⟩
        dsimp [extractSymArgsAux]; rw [hvLoc]; dsimp; rw [hRestExt]

theorem extractSymArgs_of_initMirState {body : MirBody} {init : MirState}
    (hSupp : allSupportedArgTys body.argTys = true)
    (hInit : initMirState body init) :
    ∃ args, extractSymArgs body.argTys init = some args := by
  have hb : (init.block == 0) = true := decide_eq_true hInit.1
  have hs : (init.stmtIdx == 0) = true := decide_eq_true hInit.2.1
  unfold extractSymArgs
  rw [hb, hs]
  dsimp
  exact extractSymArgsAux_of_argsMatchLocals body.argTys 1 init hSupp hInit.2.2.2

/-- Universal soundness of `evalSym` (`Abstracts FuncLang MirLang π_func`). -/
theorem evalSym_sound (plan : TransPlan) (body : MirBody) :
    Abstracts FuncLang MirLang π_func (evalSym plan body) body := by
  intro q hdef
  have hne : evalSym plan body q.init ≠ .fail := hdef
  unfold evalSym at hne
  cases hSupp : allSupportedArgTys body.argTys with
  | false =>
    rw [hSupp] at hne
    exact False.elim (hne rfl)
  | true =>
    rw [hSupp] at hne
    dsimp at hne
    cases hExt : extractSymArgs body.argTys q.init with
    | none =>
      have hNotInit : ¬ initMirState body q.init := by
        intro hInit
        have ⟨args, hSome⟩ := extractSymArgs_of_initMirState hSupp hInit
        rw [hExt] at hSome
        cases hSome
      refine ⟨fun hInit => False.elim (hNotInit hInit), ?_⟩
      intro out hexec
      exact False.elim (hNotInit hexec.1)
    | some args =>
      rw [hExt] at hne
      dsimp at hne
      cases hRes : translatePure plan body args with
      | fail =>
        rw [hRes] at hne
        exact False.elim (hne rfl)
      | inapplicable =>
        exact False.elim (evalSymState_ne_inapplicable plan body (buildPureSymState args) hRes)
      | ok ret =>
        have hState := extractSymArgs_sound body.argTys q.init args hExt
        have hSafe : SafeAndReturns body q.init ret :=
          evalSymState_sound plan body hState hRes
        have hMirDef : (MirLang.sem body q).defined :=
          fun _ tr out hreach => (hSafe q.init q.steps tr out hreach).1
        refine ⟨hMirDef, ?_⟩
        intro out hexec
        have h := hSafe q.init q.steps out.trace out.outcome hexec.2
        refine ⟨h.1, ?_⟩
        intro r hr
        have hr_eq : r = ret := h.2 r hr
        subst hr_eq
        change evalSym plan body q.init = .ok r
        unfold evalSym
        rw [hSupp]; dsimp; rw [hExt]
        exact hRes

noncomputable def computePlanAux : Nat → MirBody → Nat → Nat → TransPlan
  | 0, _, _, _ => .fail
  | fuel + 1, body, blk, stmtIdx =>
    match body.blocks[blk]? with
    | none => .fail
    | some bb =>
      match bb.stmts[stmtIdx]? with
      | some _ => .step (computePlanAux fuel body blk (stmtIdx + 1))
      | none =>
        match bb.terminator with
        | .return_ => .ret
        | .goto target | .assertNotOverflow _ target | .callPure2 _ _ _ _ target =>
          .step (computePlanAux fuel body target.index 0)
        | .switchInt _ falseTarget trueTarget =>
          .branch
            (computePlanAux fuel body falseTarget.index 0)
            (computePlanAux fuel body trueTarget.index 0)
        | .unreachable => .fail

noncomputable def computePlan (body : MirBody) : TransPlan :=
  computePlanAux 64 body 0 0

noncomputable def translate (body : MirBody) : FuncLang.Prog :=
  evalSym (computePlan body) body

theorem translate_sound (body : MirBody) :
    Abstracts FuncLang MirLang π_func (translate body) body :=
  evalSym_sound (computePlan body) body

/-!
## 5. End-to-End Verification: `add`, `double_guarded`, and `double_conditional`
-/

/-!
### 5.1 Private Conditional Helper `fn add(x: usize, y: usize) -> usize`
-/

/-- `Runtime(PostCleanup)` MIR body for
    `fn add(x: usize, y: usize) -> usize { x + y }`:
    ```text
    bb0: {
        _3 = AddWithOverflow(copy _1, copy _2);
        assert(!move (_3.1: bool), ...) -> [success: bb1, unwind continue];
    }
    bb1: {
        _0 = move (_3.0: usize);
        return;
    }
    ``` -/
def addBody : MirBody where
  argTys := [.usize, .usize]
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.checkedBinaryOp .add (.copy ⟨1⟩) (.copy ⟨2⟩))
      ]
      terminator := .assertNotOverflow ⟨3⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨0⟩ (.proj0 ⟨3⟩)
      ]
      terminator := .return_ }
  ]

/-- State-level precondition for `add`: any `.usize` arguments in `_1` and `_2`
    do not overflow `usizeMax`. -/
def FuncPreAdd (init : MirState) : Prop :=
  ∀ x0 y0,
    init.locals 1 = some (.usize x0) →
    init.locals 2 = some (.usize y0) →
    x0 + y0 ≤ usizeMax

/-- Query-indexed precondition for `add`. -/
def PreAdd (q : ExecQuery MirState) : Prop :=
  FuncPreAdd q.init

/-- Existential phrasing of `add`'s precondition
    (`∃ x0 y0, ... ∧ x0 + y0 ≤ usizeMax`). -/
def PreAddExists (q : ExecQuery MirState) : Prop :=
  ∃ x0 y0,
    q.init.locals 1 = some (.usize x0) ∧
    q.init.locals 2 = some (.usize y0) ∧
    x0 + y0 ≤ usizeMax

/-- On any valid entry state `initMirState addBody q.init`, the implicational
    precondition `PreAdd q` and the existential precondition `PreAddExists q`
    are equivalent. -/
theorem preAdd_iff_exists_on_init {q : ExecQuery MirState}
    (hInit : initMirState addBody q.init) :
    PreAdd q ↔ PreAddExists q := by
  constructor
  · intro hPre
    have ⟨⟨v1, hv1, hty1⟩, ⟨v2, hv2, hty2⟩, _⟩ := hInit.2.2.2
    cases v1 with
    | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
      cases hty1
    | usize x0 =>
      cases v2 with
      | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
        cases hty2
      | usize y0 =>
        exact ⟨x0, y0, hv1, hv2, hPre x0 y0 hv1 hv2⟩
  · intro ⟨x0, y0, hv1, hv2, hle⟩ x0' y0' hv1' hv2'
    rw [hv1] at hv1'; injection hv1' with h1; injection h1 with hx
    rw [hv2] at hv2'; injection hv2' with h2; injection h2 with hy
    subst hx hy
    exact hle

/-- Functional postcondition for `add` in `FuncLang`. -/
def FuncPostAdd (init : MirState) (ret : MirVal) : Prop :=
  ∀ x0 y0,
    init.locals 1 = some (.usize x0) →
    init.locals 2 = some (.usize y0) →
    ret = .usize (x0 + y0)

/-- Conditional `MirLang.SpecOn` specification for `add`:
    - `defined := PreAdd q` (`x0 + y0 ≤ usizeMax`), and
    - `val`: any normal return value equals `.usize (x0 + y0)`. -/
def EnsuresAddOn : MirLang.Behavior :=
  MirLang.SpecOn PreAdd (fun q out =>
    ∀ ret x0 y0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      q.init.locals 2 = some (.usize y0) →
      ret = .usize (x0 + y0))

theorem ensuresAddOn_le_wellFormedOn :
    EnsuresAddOn ≤ MirLang.WellFormedOn PreAdd :=
  specOn_le_wellFormedOn (L := MirLang) PreAdd _

/-- **First Futamura Projection for `addBody`**:
    `translatePure (computePlan addBody) addBody` reduces by kernel `rfl` on
    symbolic `x0, y0 : Nat` to `if decide (usizeMax < x0 + y0) then .fail else
    .ok (.usize (x0 + y0))`. -/
theorem translatePure_add_rfl (x0 y0 : Nat) :
    translatePure (computePlan addBody) addBody [.usize x0, .usize y0] =
      (if decide (usizeMax < x0 + y0) then .fail else .ok (.usize (x0 + y0))) :=
  rfl

/-- Under `x0 + y0 ≤ usizeMax`, `translatePure` on `addBody` evaluates to
    `.ok (.usize (x0 + y0))`. -/
theorem translatePure_add_eq_of_le {x0 y0 : Nat} (hle : x0 + y0 ≤ usizeMax) :
    translatePure (computePlan addBody) addBody [.usize x0, .usize y0] =
      .ok (.usize (x0 + y0)) := by
  rw [translatePure_add_rfl]
  have hov : decide (usizeMax < x0 + y0) = false :=
    decide_eq_false (Nat.not_lt_of_ge hle)
  rw [hov]
  rfl

/-- **Callee Contract Adequacy (`rfl`)**:
    `evalPureCallee2 .add` agrees definitionally with `translatePure` of
    `addBody` for all `x0, y0 : Nat`. -/
theorem evalPureCallee2_add_eq_translatePure (x0 y0 : Nat) :
    (evalPureCallee2 .add (.usize x0) (.usize y0)).map
      (fun p => if p.1 then AeneasRes.fail else AeneasRes.ok p.2) =
      some (translatePure (computePlan addBody) addBody [.usize x0, .usize y0]) :=
  rfl

/-- `translate addBody` satisfies `FuncLang.SpecOn FuncPreAdd FuncPostAdd`. -/
theorem translate_addBody_specOn :
    FuncLang.sem (translate addBody) ≤ FuncLang.SpecOn FuncPreAdd FuncPostAdd := by
  refine funcSem_le_specOn (fun init hPre => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys addBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs addBody.argTys init with
  | none =>
    exact ⟨(by intro h; cases h), fun _ hok => by cases hok⟩
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [addBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ =>
          cases hExt
        | usize x0' =>
          dsimp at hExt
          cases hloc2 : init.locals 2 with
          | none => rw [hloc2] at hExt; cases hExt
          | some mv2 =>
            rw [hloc2] at hExt
            cases mv2 with
            | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ =>
              cases hExt
            | usize y0' =>
              dsimp at hExt
              injection hExt with hargs
              subst hargs
              dsimp
              have hle : x0' + y0' ≤ usizeMax := hPre x0' y0' hloc1 hloc2
              rw [translatePure_add_eq_of_le hle]
              refine ⟨(by intro h; cases h), ?_⟩
              intro ret hok x0 y0 hl1 hl2
              injection hok with hret
              rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
              rw [hloc2] at hl2; injection hl2 with h2_mv; injection h2_mv with h2; subst h2
              exact hret.symm

theorem π_func_add_le_ensuresOn :
    π_func (FuncLang.SpecOn FuncPreAdd FuncPostAdd) ≤ EnsuresAddOn := by
  refine Preorder.le_trans (π_func_specOn_le FuncPreAdd FuncPostAdd) ?_
  intro q hPre
  refine ⟨hPre, ?_⟩
  intro out hpost ret x0 y0 hterm hl1 hl2
  exact hpost ret hterm x0 y0 hl1 hl2

/-- **Source MIR Conditional Correctness of `addBody`**:
    `MirSem addBody ≤ EnsuresAddOn`, proved via `translate_sound` and
    `translate_addBody_specOn`. -/
theorem addBody_satisfies_ensuresOn :
    MirSem addBody ≤ EnsuresAddOn :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound addBody)
      (monotone_π_func translate_addBody_specOn))
    π_func_add_le_ensuresOn

theorem addBody_satisfies_wellFormedOn :
    MirSem addBody ≤ MirLang.WellFormedOn PreAdd :=
  Preorder.le_trans addBody_satisfies_ensuresOn ensuresAddOn_le_wellFormedOn

/-- `EnsuresAddOn` refines `CalleeSpec2 .add`: proving `EnsuresAddOn`
    immediately discharges the callee contract adequacy obligation for
    `PureCallee2.add`. -/
theorem ensuresAddOn_le_calleeSpec2 :
    EnsuresAddOn ≤ CalleeSpec2 .add := by
  intro q hCalleePre
  have hPre : PreAdd q := by
    intro x0 y0 hl1 hl2
    have ⟨retVal, hEval⟩ := hCalleePre x0 y0 hl1 hl2
    dsimp [evalPureCallee2] at hEval
    injection hEval with hpair
    injection hpair with hov _
    exact Nat.not_lt.mp (of_decide_eq_false hov)
  refine ⟨hPre, ?_⟩
  intro out hpost ret x0 y0 retVal hterm hl1 hl2 hEval
  have hret := hpost ret x0 y0 hterm hl1 hl2
  dsimp [evalPureCallee2] at hEval
  injection hEval with hpair
  injection hpair with _ hretVal
  exact Eq.trans hret hretVal

theorem addBody_satisfies_calleeSpec2 :
    MirSem addBody ≤ CalleeSpec2 .add :=
  Preorder.le_trans addBody_satisfies_ensuresOn ensuresAddOn_le_calleeSpec2

/-!
### 5.2 Public Unconditional Caller `pub fn double_guarded(x: usize) -> usize`
-/

/-- `Runtime(PostCleanup)` MIR body for:
    ```rust
    pub fn double_guarded(x: usize) -> usize {
        if x <= 1000 {
            add(x, x)
        } else {
            0
        }
    }
    ```
    Calls the conditional private helper `PureCallee2.add` on `bb1` (the `x <=
    1000` branch). -/
def doubleGuardedBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [
        .assign ⟨2⟩ (.binaryOp .le (.copy ⟨1⟩) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := []
      terminator := .callPure2 ⟨0⟩ .add (.copy ⟨1⟩) (.copy ⟨1⟩) ⟨3⟩ },
    { stmts := [
        .assign ⟨0⟩ (.use (.constVal (.usize 0)))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- Unconditional specification for `double_guarded` (`MirLang.Spec`, with
    `defined := True` for all `q`):
    - `defined := True`: never triggers UB or overflow assertion failure on
      *any* input `x0 : Nat`, and
    - `val`: returns `.usize (if decide (x0 ≤ 1000) then x0 + x0 else 0)`. -/
def EnsuresDoubleGuarded : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret x0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      ret = .usize (if decide (x0 ≤ 1000) then x0 + x0 else 0))

theorem ensuresDoubleGuarded_le_wellFormed :
    EnsuresDoubleGuarded ≤ MirLang.WellFormed :=
  spec_le_wellFormed _

/-- **First Futamura Projection for `doubleGuardedBody` (`rfl`)**:
    Evaluating `translatePure (computePlan doubleGuardedBody) doubleGuardedBody`
    on symbolic `x0 : Nat` reduces by kernel `rfl` across the conditional call
    `PureCallee2.add` to `zipAeneasRes` with the callee's precondition check
    `decide (usizeMax < x0 + x0)` isolated on the `x0 ≤ 1000` branch. -/
theorem translatePure_doubleGuarded_rfl (x0 : Nat) :
    translatePure (computePlan doubleGuardedBody) doubleGuardedBody [.usize x0] =
      zipAeneasRes (decide (x0 ≤ 1000))
        (if decide (usizeMax < x0 + x0) then .fail else .ok (.usize (x0 + x0)))
        (.ok (.usize 0)) :=
  rfl

/-- **Path-Sensitive Call-Site Precondition Discharge (`double_guarded`)**:
    On the `decide (x0 ≤ 1000) = true` branch, `x0 + x0 ≤ 2000 ≤ usizeMax`,
    discharging `add`'s precondition (`decide (usizeMax < x0 + x0) = false`) so
    `translatePure` succeeds for *all* `x0 : Nat`. -/
theorem translatePure_doubleGuarded_eq (x0 : Nat) :
    translatePure (computePlan doubleGuardedBody) doubleGuardedBody [.usize x0] =
      .ok (.usize (if decide (x0 ≤ 1000) then x0 + x0 else 0)) := by
  rw [translatePure_doubleGuarded_rfl, zipAeneasRes_eq_ite]
  cases hx : decide (x0 ≤ 1000) with
  | false => rfl
  | true =>
    have hxle : x0 ≤ 1000 := of_decide_eq_true hx
    have hsum : x0 + x0 ≤ 2000 := Nat.add_le_add hxle hxle
    have h2000 : (2000 : Nat) ≤ usizeMax := of_decide_eq_true rfl
    have hle : x0 + x0 ≤ usizeMax := Nat.le_trans hsum h2000
    have hov : decide (usizeMax < x0 + x0) = false :=
      decide_eq_false (Nat.not_lt_of_ge hle)
    rw [hov]
    rfl

def FuncPostDoubleGuarded (init : MirState) (ret : MirVal) : Prop :=
  ∀ x0,
    init.locals 1 = some (.usize x0) →
    ret = .usize (if decide (x0 ≤ 1000) then x0 + x0 else 0)

theorem translate_doubleGuardedBody_spec :
    FuncLang.sem (translate doubleGuardedBody) ≤ FuncLang.Spec FuncPostDoubleGuarded := by
  refine funcSem_le_spec (fun init => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys doubleGuardedBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs doubleGuardedBody.argTys init with
  | none =>
    exact ⟨(by intro h; cases h), fun _ hok => by cases hok⟩
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [doubleGuardedBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ =>
          cases hExt
        | usize x0' =>
          dsimp at hExt
          injection hExt with hargs
          subst hargs
          dsimp
          rw [translatePure_doubleGuarded_eq x0']
          refine ⟨(by intro h; cases h), ?_⟩
          intro ret hok x0 hl1
          injection hok with hret
          rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
          exact hret.symm

theorem π_func_doubleGuarded_le_ensures :
    π_func (FuncLang.Spec FuncPostDoubleGuarded) ≤ EnsuresDoubleGuarded := by
  refine Preorder.le_trans (π_func_spec_le FuncPostDoubleGuarded) ?_
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out hpost ret x0 hterm hl1
  exact hpost ret hterm x0 hl1

theorem doubleGuardedBody_satisfies_ensures :
    MirSem doubleGuardedBody ≤ EnsuresDoubleGuarded :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound doubleGuardedBody)
      (monotone_π_func translate_doubleGuardedBody_spec))
    π_func_doubleGuarded_le_ensures

theorem doubleGuardedBody_satisfies_wellFormed :
    MirSem doubleGuardedBody ≤ MirLang.WellFormed :=
  Preorder.le_trans doubleGuardedBody_satisfies_ensures ensuresDoubleGuarded_le_wellFormed

/-!
### 5.3 Public Conditional Caller `pub fn double_conditional(x: usize) -> usize`
-/

/-- `Runtime(PostCleanup)` MIR body for:
    ```rust
    pub fn double_conditional(x: usize) -> usize {
        add(x, x)
    }
    ```
    Calls the conditional private helper `PureCallee2.add` directly without a
    branch guard. -/
def doubleConditionalBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := []
      terminator := .callPure2 ⟨0⟩ .add (.copy ⟨1⟩) (.copy ⟨1⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- State-level calling precondition for `double_conditional`: `x0 + x0 ≤
    usizeMax`. -/
def FuncPreDoubleConditional (init : MirState) : Prop :=
  ∀ x0, init.locals 1 = some (.usize x0) → x0 + x0 ≤ usizeMax

/-- Query-indexed calling precondition for `double_conditional`. -/
def PreDoubleConditional (q : ExecQuery MirState) : Prop :=
  FuncPreDoubleConditional q.init

/-- Conditional specification for `double_conditional` via `MirLang.SpecOn`:
    - `defined := PreDoubleConditional q` (`x0 + x0 ≤ usizeMax`), and
    - `val`: any normal return value equals `.usize (x0 + x0)`. -/
def EnsuresDoubleConditionalOn : MirLang.Behavior :=
  MirLang.SpecOn PreDoubleConditional (fun q out =>
    ∀ ret x0,
      out.outcome = .terminated (.normal ret) →
      q.init.locals 1 = some (.usize x0) →
      ret = .usize (x0 + x0))

theorem ensuresDoubleConditionalOn_le_wellFormedOn :
    EnsuresDoubleConditionalOn ≤ MirLang.WellFormedOn PreDoubleConditional :=
  specOn_le_wellFormedOn (L := MirLang) PreDoubleConditional _

/-- **First Futamura Projection for `doubleConditionalBody` (`rfl`)**:
    Evaluating `translatePure` on symbolic `x0 : Nat` reduces by kernel `rfl`
    to `if decide (usizeMax < x0 + x0) then .fail else .ok (.usize (x0 + x0))`.
-/
theorem translatePure_doubleConditional_rfl (x0 : Nat) :
    translatePure (computePlan doubleConditionalBody) doubleConditionalBody [.usize x0] =
      (if decide (usizeMax < x0 + x0) then .fail else .ok (.usize (x0 + x0))) :=
  rfl

/-- **Caller-Precondition Call-Site Discharge (`double_conditional`)**:
    Under the caller's precondition `x0 + x0 ≤ usizeMax`, `add`'s precondition
    at the call site `add(x, x)` is discharged (`decide (usizeMax < x0 + x0) =
    false`) and `translatePure` evaluates to `.ok (.usize (x0 + x0))`. -/
theorem translatePure_doubleConditional_eq_of_le {x0 : Nat} (hle : x0 + x0 ≤ usizeMax) :
    translatePure (computePlan doubleConditionalBody) doubleConditionalBody [.usize x0] =
      .ok (.usize (x0 + x0)) := by
  rw [translatePure_doubleConditional_rfl]
  have hov : decide (usizeMax < x0 + x0) = false :=
    decide_eq_false (Nat.not_lt_of_ge hle)
  rw [hov]
  rfl

def FuncPostDoubleConditional (init : MirState) (ret : MirVal) : Prop :=
  ∀ x0, init.locals 1 = some (.usize x0) → ret = .usize (x0 + x0)

theorem translate_doubleConditionalBody_specOn :
    FuncLang.sem (translate doubleConditionalBody) ≤
      FuncLang.SpecOn FuncPreDoubleConditional FuncPostDoubleConditional := by
  refine funcSem_le_specOn (fun init hPre => ?_)
  unfold translate evalSym
  have hSupp : allSupportedArgTys doubleConditionalBody.argTys = true := rfl
  rw [hSupp]
  dsimp
  cases hExt : extractSymArgs doubleConditionalBody.argTys init with
  | none =>
    exact ⟨(by intro h; cases h), fun _ hok => by cases hok⟩
  | some args =>
    unfold extractSymArgs at hExt
    cases hblk : (init.block == 0 && init.stmtIdx == 0) with
    | false => rw [hblk] at hExt; cases hExt
    | true =>
      rw [hblk] at hExt
      dsimp [doubleConditionalBody, extractSymArgsAux] at hExt
      cases hloc1 : init.locals 1 with
      | none => rw [hloc1] at hExt; cases hExt
      | some mv1 =>
        rw [hloc1] at hExt
        cases mv1 with
        | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refMutLoc _ | refSharedLoc _ | ordering _ =>
          cases hExt
        | usize x0' =>
          dsimp at hExt
          injection hExt with hargs
          subst hargs
          dsimp
          have hle : x0' + x0' ≤ usizeMax := hPre x0' hloc1
          rw [translatePure_doubleConditional_eq_of_le hle]
          refine ⟨(by intro h; cases h), ?_⟩
          intro ret hok x0 hl1
          injection hok with hret
          rw [hloc1] at hl1; injection hl1 with h1_mv; injection h1_mv with h1; subst h1
          exact hret.symm

theorem π_func_doubleConditional_le_ensuresOn :
    π_func (FuncLang.SpecOn FuncPreDoubleConditional FuncPostDoubleConditional) ≤
      EnsuresDoubleConditionalOn := by
  refine Preorder.le_trans (π_func_specOn_le FuncPreDoubleConditional FuncPostDoubleConditional) ?_
  intro q hPre
  refine ⟨hPre, ?_⟩
  intro out hpost ret x0 hterm hl1
  exact hpost ret hterm x0 hl1

theorem doubleConditionalBody_satisfies_ensuresOn :
    MirSem doubleConditionalBody ≤ EnsuresDoubleConditionalOn :=
  Preorder.le_trans
    (Preorder.le_trans
      (translate_sound doubleConditionalBody)
      (monotone_π_func translate_doubleConditionalBody_specOn))
    π_func_doubleConditional_le_ensuresOn

theorem doubleConditionalBody_satisfies_wellFormedOn :
    MirSem doubleConditionalBody ≤ MirLang.WellFormedOn PreDoubleConditional :=
  Preorder.le_trans doubleConditionalBody_satisfies_ensuresOn ensuresDoubleConditionalOn_le_wellFormedOn

/-!
### 5.4 Multi-Function Public/Private `CrateTheorem` Proofs
-/

/-- Crate 1 (`guardedCrate`): contains private conditional helper `add`
    (`visibility := .priv`, `callee := some .add`, `pre := PreAdd`) and public
    unconditional entry point `double_guarded` (`visibility := .pub`, `pre :=
    fun _ => True`). -/
def guardedCrate (fnAdd fnDoubleGuarded : String) : Crate where
  functions := [
    { name := fnAdd
      visibility := .priv
      callee := some .add
      prog := addBody
      pre := PreAdd
      specs := [EnsuresAddOn] },
    { name := fnDoubleGuarded
      visibility := .pub
      callee := none
      prog := doubleGuardedBody
      pre := fun _ => True
      specs := [EnsuresDoubleGuarded] }
  ]
  tcb := [
    .rustcLowering fnAdd addBody,
    .rustcLowering fnDoubleGuarded doubleGuardedBody
  ]

/-- End-to-end proof that `guardedCrate` satisfies both `CrateTheorem`
    (including `CalleeSummaryVerified` for private `add`) and
    `PublicApiUnconditional` (every `.pub` function has an unconditional entry
    contract). -/
theorem prove_guarded_crate (fnAdd fnDoubleGuarded : String) :
    CrateTheorem (guardedCrate fnAdd fnDoubleGuarded) ∧
    PublicApiUnconditional (guardedCrate fnAdd fnDoubleGuarded) := by
  refine ⟨⟨(by intro h; cases h), ?_⟩, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, True.intro⟩, True.intro⟩
    · refine ⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩
      intro hAssumptions
      exact Compiler.Verified.with_wellFormedOn
        (Compiler.SoundOn.verify hAssumptions.1 addBody_satisfies_ensuresOn)
        ensuresAddOn_le_wellFormedOn
        hAssumptions.1.1
    · refine ⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩
      intro hAssumptions
      exact Compiler.Verified.with_wellFormedOn
        (Compiler.SoundOn.verify hAssumptions.1 addBody_satisfies_calleeSpec2)
        (calleeSpec2_le_wellFormedOn .add)
        hAssumptions.1.1
    · refine ⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩
      intro hAssumptions
      exact Compiler.Verified.with_wellFormedOn
        (Compiler.SoundOn.verify hAssumptions.2.1 doubleGuardedBody_satisfies_ensures)
        ensuresDoubleGuarded_le_wellFormed
        hAssumptions.2.1.1
  · exact ⟨(fun h => by cases h), (fun _ _ => True.intro), True.intro⟩

/-- Crate 2 (`mixedCrate`): contains private conditional helper `add`, public
    unconditional `double_guarded`, and public conditional
    `double_conditional`. -/
def mixedCrate (fnAdd fnDoubleGuarded fnDoubleConditional : String) : Crate where
  functions := [
    { name := fnAdd
      visibility := .priv
      callee := some .add
      prog := addBody
      pre := PreAdd
      specs := [EnsuresAddOn] },
    { name := fnDoubleGuarded
      visibility := .pub
      callee := none
      prog := doubleGuardedBody
      pre := fun _ => True
      specs := [EnsuresDoubleGuarded] },
    { name := fnDoubleConditional
      visibility := .pub
      callee := none
      prog := doubleConditionalBody
      pre := PreDoubleConditional
      specs := [EnsuresDoubleConditionalOn] }
  ]
  tcb := [
    .rustcLowering fnAdd addBody,
    .rustcLowering fnDoubleGuarded doubleGuardedBody,
    .rustcLowering fnDoubleConditional doubleConditionalBody
  ]

/-- End-to-end proof of `CrateTheorem` for the 3-function `mixedCrate`. -/
theorem prove_mixed_crate (fnAdd fnDoubleGuarded fnDoubleConditional : String) :
    CrateTheorem (mixedCrate fnAdd fnDoubleGuarded fnDoubleConditional) := by
  refine ⟨(by intro h; cases h), ?_⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, True.intro⟩, ⟨?_, True.intro⟩, True.intro⟩
  · refine ⟨⟨True.intro, True.intro, True.intro, True.intro⟩, ?_⟩
    intro hAssumptions
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hAssumptions.1 addBody_satisfies_ensuresOn)
      ensuresAddOn_le_wellFormedOn
      hAssumptions.1.1
  · refine ⟨⟨True.intro, True.intro, True.intro, True.intro⟩, ?_⟩
    intro hAssumptions
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hAssumptions.1 addBody_satisfies_calleeSpec2)
      (calleeSpec2_le_wellFormedOn .add)
      hAssumptions.1.1
  · refine ⟨⟨True.intro, True.intro, True.intro, True.intro⟩, ?_⟩
    intro hAssumptions
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hAssumptions.2.1 doubleGuardedBody_satisfies_ensures)
      ensuresDoubleGuarded_le_wellFormed
      hAssumptions.2.1.1
  · refine ⟨⟨True.intro, True.intro, True.intro, True.intro⟩, ?_⟩
    intro hAssumptions
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hAssumptions.2.2.1 doubleConditionalBody_satisfies_ensuresOn)
      ensuresDoubleConditionalOn_le_wellFormedOn
      hAssumptions.2.2.1.1

/-!
## 6. Negative Controls
-/

/-- Initial state for `addBody` with `_1 = usizeMax` and `_2 = 1`
    (`usizeMax + 1 > usizeMax`). -/
def addOverflowInit : MirState where
  locals := updateLocal (updateLocal (fun _ => none) 1 (some (.usize usizeMax))) 2 (some (.usize 1))
  mem := MemState.empty
  block := 0
  stmtIdx := 0

theorem addOverflowInit_is_init : initMirState addBody addOverflowInit := by
  refine ⟨rfl, rfl, rfl, ⟨⟨.usize usizeMax, rfl, True.intro⟩, ⟨.usize 1, rfl, True.intro⟩, ?_⟩⟩
  intro j hj
  cases j with
  | zero => cases hj
  | succ k1 =>
    cases k1 with
    | zero => cases hj with | step h => cases h
    | succ k2 =>
      cases k2 with
      | zero => cases hj with | step h => cases h with | step h2 => cases h2
      | succ _ => rfl

/-- **Negative Control 1a (`addBody_not_wellFormed`)**:
    `addBody` does *not* satisfy unconditional `MirLang.WellFormed` because at
    `(_1 = usizeMax, _2 = 1)`, step 1 computes `(usizeMax + 1, true)` and step 2
    triggers `assertNotOverflow` -> `.failed .contractViolation`. -/
theorem addBody_not_wellFormed :
    ¬ (MirSem addBody ≤ MirLang.WellFormed) := by
  intro hWF
  let s1 : MirState := {
    addOverflowInit with
    locals := updateLocal addOverflowInit.locals 3 (some (.tupleUsizeBool (usizeMax + 1) true))
    stmtIdx := 1
  }
  have hreach1 : ReachesPrefix MirMachine addBody addOverflowInit 1 s1 []
      (.failed .contractViolation) :=
    ReachesPrefix.failed 0 s1 .contractViolation rfl
  have hreach2 : ReachesPrefix MirMachine addBody addOverflowInit 2 addOverflowInit [()]
      (.failed .contractViolation) :=
    ReachesPrefix.step 1 addOverflowInit s1 () [] (.failed .contractViolation) rfl hreach1
  exact (behaviorOf_le_wellFormed_iff (M := MirMachine)).mp hWF
    addOverflowInit 2 [()] (.failed .contractViolation) addOverflowInit_is_init hreach2

/-- **Negative Control 1b (`addBody_not_le_spec`)**:
    `addBody` cannot refine `MirLang.Spec post` for *any* postcondition `post`
    (even `fun q out => PreAdd q → ...`), because `MirLang.Spec` sets
    `defined := True` at every query `q`, whereas
    `(MirSem addBody ⟨addOverflowInit, 2⟩).defined` is `False`. -/
theorem addBody_not_le_spec (post : ExecQuery MirState → ExecOut Unit MirVal → Prop) :
    ¬ (MirSem addBody ≤ MirLang.Spec post) := by
  refine not_le_spec_of_not_defined (L := MirLang) (b := MirSem addBody)
    (q := ⟨addOverflowInit, 2⟩) ?_ post
  intro hdef
  let s1 : MirState := {
    addOverflowInit with
    locals := updateLocal addOverflowInit.locals 3 (some (.tupleUsizeBool (usizeMax + 1) true))
    stmtIdx := 1
  }
  have hreach1 : ReachesPrefix MirMachine addBody addOverflowInit 1 s1 []
      (.failed .contractViolation) :=
    ReachesPrefix.failed 0 s1 .contractViolation rfl
  have hreach2 : ReachesPrefix MirMachine addBody addOverflowInit 2 addOverflowInit [()]
      (.failed .contractViolation) :=
    ReachesPrefix.step 1 addOverflowInit s1 () [] (.failed .contractViolation) rfl hreach1
  exact hdef addOverflowInit_is_init [()] (.failed .contractViolation) hreach2

/-- **Negative Control 2 (`doubleConditionalBody_not_wellFormed`)**:
    Calling `add(x, x)` without a guard or caller precondition
    (`doubleConditionalBody`) violates unconditional `MirLang.WellFormed` at
    `_1 = usizeMax`. -/
theorem doubleConditionalBody_not_wellFormed :
    ¬ (MirSem doubleConditionalBody ≤ MirLang.WellFormed) := by
  intro hWF
  let s0 : MirState := {
    locals := updateLocal (fun _ => none) 1 (some (.usize usizeMax))
    mem := MemState.empty
    block := 0
    stmtIdx := 0
  }
  have hrest : ∀ j, 2 ≤ j → s0.locals j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k1 =>
      cases k1 with
      | zero => cases hj with | step h => cases h
      | succ _ => rfl
  have hinit : initMirState doubleConditionalBody s0 :=
    ⟨rfl, rfl, rfl, ⟨⟨.usize usizeMax, rfl, True.intro⟩, hrest⟩⟩
  have hreach1 : ReachesPrefix MirMachine doubleConditionalBody s0 1 s0 []
      (.failed .contractViolation) :=
    ReachesPrefix.failed 0 s0 .contractViolation rfl
  exact (behaviorOf_le_wellFormed_iff (M := MirMachine)).mp hWF
    s0 1 [] (.failed .contractViolation) hinit hreach1

/-- **Negative Control 3 (`bogus_unconditional_add_callee_rejected`)**:
    Suppose a bogus callee summary claimed that `addBody` has an unconditional
    callee precondition (`BogusCalleePre := fun _ => True`). Then `addBody`
    provably refutes `MirLang.SpecOn BogusCalleePre post`, so
    `CalleeSummaryVerified` in `CrateTheorem` rejects any attempt to summarize a
    conditional helper as unconditional. -/
theorem bogus_unconditional_add_callee_rejected
    (post : ExecQuery MirState → ExecOut Unit MirVal → Prop) :
    ¬ (MirSem addBody ≤ MirLang.SpecOn (fun _ => True) post) :=
  addBody_not_le_spec post

/-!
## 7. Mode 2 Comparison: Unwinding Overflow Semantics (`MirLangUnwind`)

In standard safe Rust (`rust-lang/reference`), an arithmetic overflow check or
`assert!` failure unwinds the stack (`.terminated .unwind`), which is
well-defined behavior (not UB). Because `(PrefixOutcome.terminated
.unwind).isSafe = True`, modeling `assertNotOverflow` as `.terminated .unwind`
makes `addBody` **unconditionally** `WellFormed` (`pre = fun _ => True`), while
its normal-return and no-unwind guarantee under `x0 + y0 ≤ usizeMax` is stated
inside an unconditional `MirLangUnwind.Spec`.
-/

/-- Mode 2 terminator evaluation: overflow in `assertNotOverflow` or a callee
    call transitions to `.terminated .unwind` (stack unwinding) rather than
    `.failed .contractViolation`. -/
def evalMirTerminatorUnwind (s : MirState) (term : Terminator) :
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
  | .callPure2 dst callee arg1 arg2 target =>
    match evalOperand s.locals arg1 with
    | none => .failed .ub
    | some (v1, locals1) =>
      match evalOperand locals1 arg2 with
      | none => .failed .ub
      | some (v2, locals2) =>
        match evalPureCallee2 callee v1 v2 with
        | some (false, res) =>
          .step () { s with
            locals := updateLocal locals2 dst.index (some res)
            block := target.index
            stmtIdx := 0
          }
        | some (true, _) => .terminated .unwind
        | none => .failed .ub
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
      .terminated .unwind
    | _ => .failed .ub

def evalMirStepUnwind (body : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  match body.blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmt s stmt
    | none => evalMirTerminatorUnwind s bb.terminator

def MirMachineUnwind : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = evalMirStepUnwind body s

def MirLangUnwind : Language :=
  MirMachineUnwind.toLanguage

abbrev MirSemUnwind (body : MirBody) : MirLangUnwind.Behavior :=
  MirLangUnwind.sem body

/-- Unconditional Mode 2 specification for `addBody`:
    - `defined := True`: `addBody` never triggers UB at *any* query `q` (even
      when `x0 + y0 > usizeMax`),
    - `val`: for any initial state with `_1 = some (.usize x0)` and `_2 = some
      (.usize y0)`:
      1. Any normal return value `ret` equals `.usize (x0 + y0)` and implies
         `x0 + y0 ≤ usizeMax`.
      2. Conditional panic-freedom: if `x0 + y0 ≤ usizeMax`, execution never
         unwinds (`out.outcome ≠ .terminated .unwind`). -/
def EnsuresAddUnwind : MirLangUnwind.Behavior :=
  MirLangUnwind.Spec (fun q out =>
    ∀ x0 y0,
      q.init.locals 1 = some (.usize x0) →
      q.init.locals 2 = some (.usize y0) →
      (∀ ret, out.outcome = .terminated (.normal ret) →
        ret = .usize (x0 + y0) ∧ x0 + y0 ≤ usizeMax) ∧
      (x0 + y0 ≤ usizeMax → out.outcome ≠ .terminated .unwind))

theorem ensuresAddUnwind_le_wellFormed :
    EnsuresAddUnwind ≤ MirLangUnwind.WellFormed :=
  spec_le_wellFormed _

/-- Under Mode 2 (`.terminated .unwind`), `addBody` satisfies the unconditional
    specification `EnsuresAddUnwind` (and hence unconditional
    `MirLangUnwind.WellFormed`). -/
theorem addBody_satisfies_ensuresUnwind :
    MirSemUnwind addBody ≤ EnsuresAddUnwind := by
  refine behaviorOf_le_spec (M := MirMachineUnwind) ?_
  intro ⟨init, steps⟩ ⟨trace, outcome⟩ ⟨hinit, hreach⟩
  have hb : init.block = 0 := hinit.1
  have hs : init.stmtIdx = 0 := hinit.2.1
  have ⟨⟨v1, hv1, hty1⟩, ⟨v2, hv2, hty2⟩, _⟩ := hinit.2.2.2
  cases v1 with
  | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
    cases hty1
  | usize x0 =>
    cases v2 with
    | bool _ | unit | tupleUsizeBool _ _ | atomicLoc _ | refSharedLoc _ | refMutLoc _ | ordering _ =>
      cases hty2
    | usize y0 =>
      let ov := decide (usizeMax < x0 + y0)
      let s1 : MirState := {
        init with
        locals := updateLocal init.locals 3 (some (.tupleUsizeBool (x0 + y0) ov))
        block := 0
        stmtIdx := 1
      }
      have hstep0 : evalMirStepUnwind addBody init = .step () s1 := by
        unfold evalMirStepUnwind addBody
        rw [hb, hs]
        change (match evalOperand init.locals (.copy ⟨1⟩) with
          | none => StepResult.failed .ub
          | some (v1, locals1) =>
            match evalOperand locals1 (.copy ⟨2⟩) with
            | none => StepResult.failed .ub
            | some (v2, locals2) =>
              match evalCheckedBinOp .add v1 v2 with
              | some res =>
                StepResult.step (State := MirState) (Obs := Unit) (Val := MirVal) () {
                  init with
                  locals := updateLocal locals2 3 (some res)
                  stmtIdx := init.stmtIdx + 1
                }
              | none => StepResult.failed .ub) = _
        dsimp [evalOperand]
        rw [hv1]
        dsimp
        rw [hv2]
        dsimp [evalCheckedBinOp]
        rw [hb, hs]
      cases hreach with
      | zero =>
        refine ⟨True.intro, ?_⟩
        intro x0' y0' _ _
        exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
      | step n _ s1' _ tr1 _ h1 h2 =>
        have h1' : _ = evalMirStepUnwind addBody init := h1
        rw [hstep0] at h1'
        injection h1' with _ hs1'
        subst hs1'
        cases hov : decide (usizeMax < x0 + y0) with
        | true =>
          have hstep1 : evalMirStepUnwind addBody s1 = .terminated .unwind := by
            change evalMirTerminatorUnwind s1 (.assertNotOverflow ⟨3⟩ ⟨1⟩) = _
            dsimp [evalMirTerminatorUnwind, s1, updateLocal, ov]
            rw [hov]
          cases h2 with
          | zero =>
            refine ⟨True.intro, ?_⟩
            intro _ _ _ _
            exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
          | step _ _ _ _ _ _ hbad _ =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | choice _ _ _ _ _ _ _ hbad _ _ =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | emptyChoice _ _ _ _ hbad _ =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | terminated _ _ term hterm =>
            have hterm' : StepResult.terminated term = evalMirStepUnwind addBody s1 := hterm
            rw [hstep1] at hterm'
            injection hterm' with hterm_eq
            subst hterm_eq
            refine ⟨True.intro, ?_⟩
            intro x0' y0' hl1 hl2
            rw [hv1] at hl1; injection hl1 with h1_mv; injection h1_mv with hx; subst hx
            rw [hv2] at hl2; injection hl2 with h2_mv; injection h2_mv with hy; subst hy
            refine ⟨(fun _ h => by cases h), ?_⟩
            intro hle
            exact False.elim (Nat.not_lt_of_ge hle (of_decide_eq_true hov))
          | failed _ _ _ hbad =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | noStep _ _ hnostep =>
            exact False.elim (hnostep ⟨_, hstep1.symm⟩)
        | false =>
          let s2 : MirState := { s1 with block := 1, stmtIdx := 0 }
          have hstep1 : evalMirStepUnwind addBody s1 = .step () s2 := by
            change evalMirTerminatorUnwind s1 (.assertNotOverflow ⟨3⟩ ⟨1⟩) = _
            dsimp [evalMirTerminatorUnwind, s1, s2, updateLocal, ov]
            rw [hov]
          cases h2 with
          | zero =>
            refine ⟨True.intro, ?_⟩
            intro _ _ _ _
            exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
          | step m _ s2' _ tr2 _ h2_step h3 =>
            have h2' : _ = evalMirStepUnwind addBody s1 := h2_step
            rw [hstep1] at h2'
            injection h2' with _ hs2'
            subst hs2'
            let s3 : MirState := {
              s2 with
              locals := updateLocal s2.locals 0 (some (.usize (x0 + y0)))
              stmtIdx := 1
            }
            have hstep2 : evalMirStepUnwind addBody s2 = .step () s3 := rfl
            cases h3 with
            | zero =>
              refine ⟨True.intro, ?_⟩
              intro _ _ _ _
              exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
            | step k _ s3' _ tr3 _ h3_step h4 =>
              have h3' : _ = evalMirStepUnwind addBody s2 := h3_step
              rw [hstep2] at h3'
              injection h3' with _ hs3'
              subst hs3'
              have hstep3 : evalMirStepUnwind addBody s3 =
                  .terminated (.normal (.usize (x0 + y0))) := rfl
              cases h4 with
              | zero =>
                refine ⟨True.intro, ?_⟩
                intro _ _ _ _
                exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
              | step _ _ _ _ _ _ hbad _ =>
                have hbad' : _ = evalMirStepUnwind addBody s3 := hbad
                rw [hstep3] at hbad'; cases hbad'
              | choice _ _ _ _ _ _ _ hbad _ _ =>
                have hbad' : _ = evalMirStepUnwind addBody s3 := hbad
                rw [hstep3] at hbad'; cases hbad'
              | emptyChoice _ _ _ _ hbad _ =>
                have hbad' : _ = evalMirStepUnwind addBody s3 := hbad
                rw [hstep3] at hbad'; cases hbad'
              | terminated _ _ term hterm =>
                have hterm' : StepResult.terminated term = evalMirStepUnwind addBody s3 := hterm
                rw [hstep3] at hterm'
                injection hterm' with hterm_eq
                subst hterm_eq
                refine ⟨True.intro, ?_⟩
                intro x0' y0' hl1 hl2
                rw [hv1] at hl1; injection hl1 with h1_mv; injection h1_mv with hx; subst hx
                rw [hv2] at hl2; injection hl2 with h2_mv; injection h2_mv with hy; subst hy
                have hle : x0 + y0 ≤ usizeMax := Nat.not_lt.mp (of_decide_eq_false hov)
                refine ⟨?_, fun _ hbad => by cases hbad⟩
                intro ret hret
                injection hret with hterm_ret
                injection hterm_ret with hret_eq
                exact ⟨hret_eq.symm, hle⟩
              | failed _ _ _ hbad =>
                have hbad' : _ = evalMirStepUnwind addBody s3 := hbad
                rw [hstep3] at hbad'; cases hbad'
              | noStep _ _ hnostep =>
                exact False.elim (hnostep ⟨_, hstep3.symm⟩)
            | choice _ _ _ _ _ _ _ hbad _ _ =>
              have hbad' : _ = evalMirStepUnwind addBody s2 := hbad
              rw [hstep2] at hbad'; cases hbad'
            | emptyChoice _ _ _ _ hbad _ =>
              have hbad' : _ = evalMirStepUnwind addBody s2 := hbad
              rw [hstep2] at hbad'; cases hbad'
            | terminated _ _ _ hbad =>
              have hbad' : _ = evalMirStepUnwind addBody s2 := hbad
              rw [hstep2] at hbad'; cases hbad'
            | failed _ _ _ hbad =>
              have hbad' : _ = evalMirStepUnwind addBody s2 := hbad
              rw [hstep2] at hbad'; cases hbad'
            | noStep _ _ hnostep =>
              exact False.elim (hnostep ⟨_, hstep2.symm⟩)
          | choice _ _ _ _ _ _ _ hbad _ _ =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | emptyChoice _ _ _ _ hbad _ =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | terminated _ _ _ hbad =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | failed _ _ _ hbad =>
            have hbad' : _ = evalMirStepUnwind addBody s1 := hbad
            rw [hstep1] at hbad'; cases hbad'
          | noStep _ _ hnostep =>
            exact False.elim (hnostep ⟨_, hstep1.symm⟩)
      | choice _ _ _ _ _ _ _ h1 _ _ =>
        have h1' : _ = evalMirStepUnwind addBody init := h1
        rw [hstep0] at h1'; cases h1'
      | emptyChoice _ _ _ _ h1 _ =>
        have h1' : _ = evalMirStepUnwind addBody init := h1
        rw [hstep0] at h1'; cases h1'
      | terminated _ _ _ h1 =>
        have h1' : _ = evalMirStepUnwind addBody init := h1
        rw [hstep0] at h1'; cases h1'
      | failed _ _ _ h1 =>
        have h1' : _ = evalMirStepUnwind addBody init := h1
        rw [hstep0] at h1'; cases h1'
      | noStep _ _ hnostep =>
        exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- Under Mode 2 (`.terminated .unwind`), `addBody` is unconditionally
    `WellFormed` (`pre = fun _ => True`). -/
theorem addBody_satisfies_wellFormedUnwind :
    MirSemUnwind addBody ≤ MirLangUnwind.WellFormed :=
  Preorder.le_trans addBody_satisfies_ensuresUnwind ensuresAddUnwind_le_wellFormed

end AnnealWS5
