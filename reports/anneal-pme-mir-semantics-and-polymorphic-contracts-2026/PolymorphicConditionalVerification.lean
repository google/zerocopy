-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Polymorphic and Cross-Crate Conditional Verification with Partial `compile`

This module mechanizes conditional verification results for polymorphic public
MIR functions (`pub fn checked<T: Bound, const N: usize>(x: usize) -> usize`)
and cross-crate client instantiations in the presence of Post-Monomorphization
Errors (PMEs), caller-supplied trait implementation obligations (`LIB-07`), and
call-site runtime argument preconditions (`pre : ExecQuery MirState → Prop`).

## Summary of Results

1. **Dual Lifting of Partial Compilation (`semIfCompiled` vs. `semTotalCompiled`):**
   When `compile` returns `Partial TargetArtifact` (because `rustc`
   monomorphization may fail with a PME when evaluating `Body::required_consts`
   or computing post-monomorphization layouts), lifting `ConcreteTargetLang.sem`
   across `h_def : (compile s).defined` yields two dual behavior interpretations:
   - `semIfCompiled` (universal over `h_def`) maps a PME to the bottom behavior
     ($\bot$, empty execution set), capturing *Unconditional Safety If Compiled*.
   - `semTotalCompiled` (existential over `h_def`) maps a PME to the top
     behavior `Partial.ub` ($\top$), capturing *Total Compilation (`NoPME`) +
     Target Safety*.
   - Theorem `verifiedTotal_iff_noPme_and_verifiedIfCompiled` proves that total
     verification is equivalent to `NoPME` paired with `VerifiedIfCompiled`.

2. **Comparing Representation R1 (Instantiation-Indexed `CapturedFn` Family) and
   Representation R2 (Query-Enriched `PolyMirLang`):**
   - **R1 (`PolyCapturedFnR1`):** Parameterizes `CapturedFn` by `inst : InstCtx`
     and states polymorphic verification by quantifying over `inst : InstCtx` at
     the crate-theorem level.
   - **R2 (`PolyMirLang` / `PolyTargetLang`):** Enriches `Language.Query` to
     `PolyQuery InstCtx := InstCtx × ExecQuery MirState` so that instantiation
     conditions (`instPre`, `noPmePre`) and runtime argument conditions
     (`argPre`) are both predicates `PolyQuery InstCtx → Prop` inside the
     existing `Trusted.VerificationResultOn` envelope.
   - **Boundary Discovery (`model-refinement`):** A naive conjunction
     `fun ⟨inst, q⟩ => instPre inst ∧ noPmePre inst ∧ argPre inst q` in R2
     loses compile-time `NoPME` whenever `argPre inst` is uninhabited
     (`naive_r2_vacuous_argPre_counterexample`), whereas `rustc` evaluates
     `Body::required_consts` during monomorphization regardless of runtime
     arguments. Observing that `q.steps = 0` in `Trusted.StepResult` represents
     0 runtime steps (compile time, where `ReachesPrefix.zero` is always
     `.running`), the refined R2 precondition
     `unifiedTotalPre := fun ⟨inst, q⟩ => instPre inst ∧ noPmePre inst ∧ (q.steps = 0 ∨ argPre inst q)`
     restores an exact equivalence with R1 (`r1_iff_r2_source_wellFormed`),
     even when `argPre inst` is `fun _ => False`
     (`refined_r2_rejects_pme_even_when_argPre_empty`).

3. **Three-Way Distinction for `checked<T: Bound, const N: usize>(x: usize)` and
   Cross-Crate Composition:**
   - **Guarantee 1 (`checked_polymorphic_safety_if_compiled_r1` / `_r2`):**
     For every `inst` where `checked<inst>` compiles without a PME and `<T as
     Bound>` satisfies `boundTraitContract` (`LIB-07`), calling `checked<inst>`
     under `x ≤ 1000` is free of UB and satisfies its postcondition.
   - **Guarantee 2 (`checked_no_pme_r1` / `_r2`):**
     For every `inst` satisfying `boundTraitContract inst` and the explicit
     bound `N ≤ T::LIMIT`, `checked<inst>` is guaranteed to compile without a
     PME (`(MonoRustcCompiler.compile (checkedUnit inst)).defined`).
   - **Guarantee 3 (`client_good_entry_verified_modularly` and Negative
     Controls 1–4):**
     Downstream crate `client_good` instantiates `checked::<TypeA, 1>(50)`
     (`TypeA::LIMIT = 10`, `TypeA::delta() = 3`), discharges `LIB-07`, proves
     `1 ≤ 10` (`NoPME`), and proves `50 ≤ 1000`, obtaining a modular
     `VerificationResultOn` for `client_good::entry`. Conversely, violating the
     PME bound (`TypeB::LIMIT = 0`, `1 ≤ 0`), the `LIB-07` trait contract
     (`RogueType::delta() = usizeMax`), or the runtime argument precondition
     (`x = usizeMax`) each refutes the corresponding verification obligation.
-/

namespace PolymorphicVerification

/-!
## 1. Core Layer 1A and Layer 1B Definitions (`Trusted.Refinement`, `Trusted.StepResult`)
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

/-- A partially defined value of type `B`, constructively representing
    $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element ($\mathsf{UB}$) of `Partial B` (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

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

/-- Query-indexed partial behaviors (`Query → Partial (Out → Prop)`). -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling `Prog`, `Query`, `Out`, and `sem`. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- Behavior domain of a `Language`. -/
abbrev Language.Behavior (L : Language) : Type :=
  PolymorphicVerification.Behavior L.Query L.Out

/-- Query-indexed specification with domain precondition `pre` and outcome
    postcondition `post`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification (`pre := fun _ => True`). -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `pre`. -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`. -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Compiler lowering programs from `L_src` to `L_tgt`. -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`. -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification obligation for `s` and `spec` under compiler `C`. -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- Audited assumption in a verification unit's Trusted Computing Base. -/
class TrustedAssumption (A : Type) where
  meaning : A → Prop

/-- Policy governing which trusted assumptions are permitted. -/
structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

/-- Conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Top-level conditional verification envelope (`Trusted.VerificationResultOn`). -/
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

/-- Contravariance of `Language.SpecOn` in its domain precondition `pre`:
    strengthening the precondition (`∀ q, pre₂ q → pre₁ q`) weakens the
    specification (`L.SpecOn pre₁ post ≤ L.SpecOn pre₂ post`). -/
theorem specOn_antitone_pre {L : Language}
    {pre₁ pre₂ : L.Query → Prop} {post : L.Query → L.Out → Prop}
    (h_imp : ∀ q, pre₂ q → pre₁ q) :
    L.SpecOn pre₁ post ≤ L.SpecOn pre₂ post :=
  fun q h₂ => ⟨h_imp q h₂, fun _ hpost => hpost⟩

/-- Contravariance of `Language.WellFormedOn` in its domain precondition `pre`. -/
theorem wellFormedOn_antitone_pre {L : Language}
    {pre₁ pre₂ : L.Query → Prop}
    (h_imp : ∀ q, pre₂ q → pre₁ q) :
    L.WellFormedOn pre₁ ≤ L.WellFormedOn pre₂ :=
  specOn_antitone_pre h_imp

/-- Every `L.SpecOn pre post` refines `L.WellFormedOn pre`. -/
theorem specOn_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Monotonicity of `Compiler.Verified` in the specification argument. -/
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

/-- Discharge `C.Verified s spec` from `C.SoundOn s` and `L_src.sem s ≤ spec`. -/
theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

/-- Combine `C.Verified s spec` with `spec ≤ L_src.WellFormedOn pre`. -/
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
## 2. Layer 1B Small-Step Semantics and Minimal MIR Fragment
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

/-- At step budget `0`, `BehaviorOf M p` is unconditionally defined for every
    program `p` and initial state `init`, because `ReachesPrefix.zero` is the
    only 0-step prefix and its outcome `.running` is always safe. -/
theorem behaviorOf_defined_at_zero
    {M : SmallStepMachine Prog State Obs Val} (p : Prog) (init : State) :
    (BehaviorOf M p { init := init, steps := 0 }).defined := by
  intro _ tr out hreach
  cases hreach with
  | zero => exact True.intro

/-- Bridge lemma for establishing `BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post`. -/
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

structure LocalId where
  index : Nat

structure BlockId where
  index : Nat

inductive MirTy where
  | usize
  | bool
  | unit
  | tupleUsizeBool

inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)

inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

inductive CheckedBinOp where
  | add
  | sub
  | mul

inductive Rvalue where
  | use (op : Operand)
  | checkedBinaryOp (op : CheckedBinOp) (lhs : Operand) (rhs : Operand)
  | proj0 (src : LocalId)
  | proj1 (src : LocalId)

inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | nop

/-- Monomorphization context (`Instance<'tcx>`) for
    `checked<T: Bound, const N: usize>(x: usize) -> usize`. -/
structure CheckedInstCtx where
  tySize : Nat
  tyAlign : Nat
  constN : Nat
  traitLimit : Nat
  traitDelta : Nat

inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | assertNotOverflow (tupleLocal : LocalId) (target : BlockId)
  | callChecked (dst : LocalId) (inst : CheckedInstCtx) (arg : Operand) (target : BlockId)

structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock

structure MirState where
  locals : Nat → Option MirVal
  block : Nat
  stmtIdx : Nat

def dummyMirState : MirState where
  locals := fun _ => none
  block := 0
  stmtIdx := 0

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

def MirVal.hasTy (v : MirVal) (ty : MirTy) : Prop :=
  match v, ty with
  | .usize _, .usize => True
  | .bool _, .bool => True
  | .unit, .unit => True
  | .tupleUsizeBool _ _, .tupleUsizeBool => True
  | _, _ => False

def argsMatchLocals (argTys : List MirTy) (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k => (∃ v, locals k = some v ∧ v.hasTy ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.locals 0 = none ∧
  argsMatchLocals body.argTys s.locals

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

def usizeMax : Nat := 18446744073709551615
def isizeMax : Nat := 9223372036854775807

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
  | .nop =>
    .step () { s with stmtIdx := s.stmtIdx + 1 }

def evalCheckedCallee (inst : CheckedInstCtx) (v : MirVal) : Option MirVal :=
  match v with
  | .usize x0 =>
    if decide (usizeMax < x0 + inst.constN) ||
       decide (usizeMax < x0 + inst.constN + inst.traitDelta) then
      none
    else
      some (.usize (x0 + inst.constN + inst.traitDelta))
  | _ => none

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
  | .assertNotOverflow tupleLocal target =>
    match s.locals tupleLocal.index with
    | some (.tupleUsizeBool _ false) =>
      .step () { s with block := target.index, stmtIdx := 0 }
    | some (.tupleUsizeBool _ true) =>
      .failed .contractViolation
    | _ => .failed .ub
  | .callChecked dst inst argOp target =>
    match evalOperand s.locals argOp with
    | some (v, locals1) =>
      match evalCheckedCallee inst v with
      | some retVal =>
        .step () { s with
          locals := updateLocal locals1 dst.index (some retVal)
          block := target.index
          stmtIdx := 0
        }
      | none => .failed .contractViolation
    | none => .failed .ub

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

/-!
## 3. Partial Compilation, PMEs, and Dual Target Liftings (`semIfCompiled` vs. `semTotalCompiled`)

In `rustc`, monomorphization and codegen happen per `Instance<'tcx>`
(`rustc_monomorphize::collector`, `rustc_codegen_ssa::mir`). During
monomorphization of an instance, `rustc` evaluates every constant in
`Body::required_consts` (`rustc_middle/src/mir/mod.rs`) and computes concrete
type layouts (`tcx.layout_of`). If any required constant panics or any layout
overflows `isize::MAX`, `rustc` aborts compilation with a Post-Monomorphization
Error (PME) and emits no target artifact for that instance.

We model a monomorphized MIR compilation unit by `MonoMirUnit`, pairing the
substituted `MirBody` with its compile-time PME predicate `pmeOk : Prop`
(evaluating `Body::required_consts` and layout validity). Lowering a
`MonoMirUnit` produces a `Partial TargetArtifact` whose `.defined` proposition is
`u.pmeOk`.
-/

/-- A monomorphized MIR compilation unit pairing a concrete `MirBody` with the
    compile-time PME predicate `pmeOk` (`Body::required_consts` and layout
    validity) evaluated during monomorphization. -/
structure MonoMirUnit where
  body : MirBody
  pmeOk : Prop

/-- Source behavior of a `MonoMirUnit`: defined at query `q` if and only if
    compile-time monomorphization checks (`u.pmeOk`) succeed and the runtime
    `MirBody` is defined at `q`. -/
def MonoMirSem (u : MonoMirUnit) : MirLang.Behavior :=
  fun q => {
    defined := u.pmeOk ∧ (MirLang.sem u.body q).defined
    val := fun h out => (MirLang.sem u.body q).val h.2 out
  }

/-- Language of monomorphized MIR units (`MonoMirUnit`). -/
def MonoMirLang : Language where
  Prog := MonoMirUnit
  Query := ExecQuery MirState
  Out := ExecOut Unit MirVal
  sem := MonoMirSem

/-- Bridge lemma for establishing `MonoMirLang.sem u ≤ MonoMirLang.SpecOn pre Post`
    from `u.pmeOk` and a runtime small-step invariant on `u.body`. -/
theorem monoMirSem_le_specOn
    {u : MonoMirUnit}
    {pre : ExecQuery MirState → Prop}
    {Post : ExecQuery MirState → ExecOut Unit MirVal → Prop}
    (h_pme : u.pmeOk)
    (h_mir : MirLang.sem u.body ≤ MirLang.SpecOn pre Post) :
    MonoMirLang.sem u ≤ MonoMirLang.SpecOn pre Post := by
  intro q hpre
  cases h_mir q hpre with
  | intro h_def h_val =>
    exact ⟨⟨h_pme, h_def⟩, h_val⟩

/-- Abstract compiled target artifact produced by `rustc` when monomorphization
    and codegen succeed without a PME. -/
structure TargetArtifact where
  private mk ::
  unit : Unit

/-- Abstract `rustc` codegen for a PME-free `MirBody`. -/
opaque rustcCodegen : MirBody → TargetArtifact := fun _ => { unit := () }

/-- Partial `rustc` compilation of a `MonoMirUnit`: defined if and only if
    compile-time monomorphization checks (`u.pmeOk`) succeed. -/
def rustcCompileMono (u : MonoMirUnit) : Partial TargetArtifact where
  defined := u.pmeOk
  val _ := rustcCodegen u.body

/-- Abstract operational behavior of a compiled `TargetArtifact`. -/
opaque TargetSem :
    TargetArtifact → ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop) :=
  fun _ _ => Partial.ub

/-- Concrete target language for a single compiled `TargetArtifact`. -/
def ConcreteTargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery MirState
  Out := ExecOut Unit MirVal
  sem := TargetSem

/-- Abstract behavior mapping from MIR behaviors to target behaviors. -/
opaque π_c : MirLang.Behavior → ConcreteTargetLang.Behavior := fun b => b

/-- Universal ("If Compiled") lifting of `ConcreteTargetLang.sem` to
    `Partial TargetArtifact`.

    When `p.defined` is `False` (compilation aborted with a PME),
    `semIfCompiled p` has `defined := True` and `val := False` (the bottom
    behavior $\bot$ with zero runtime executions). Consequently,
    `semIfCompiled p ≤ b` is equivalent to
    `∀ h : p.defined, ConcreteTargetLang.sem (p.val h) ≤ b`. -/
def semIfCompiled (p : Partial TargetArtifact) : ConcreteTargetLang.Behavior :=
  fun q => {
    defined := ∀ h_def : p.defined, (ConcreteTargetLang.sem (p.val h_def) q).defined
    val := fun h_all out =>
      ∃ h_def : p.defined, (ConcreteTargetLang.sem (p.val h_def) q).val (h_all h_def) out
  }

/-- Existential ("Total Compilation + Target Safety") lifting of
    `ConcreteTargetLang.sem` to `Partial TargetArtifact`.

    When `p.defined` is `False` (compilation aborted with a PME),
    `semTotalCompiled p` has `defined := False` (`Partial.ub`, the top behavior
    $\top$). Consequently, refining any specification `b` that is defined at `q`
    forces `p.defined` (`NoPME`) to hold in addition to target refinement. -/
def semTotalCompiled (p : Partial TargetArtifact) : ConcreteTargetLang.Behavior :=
  fun q => {
    defined := ∃ h_def : p.defined, (ConcreteTargetLang.sem (p.val h_def) q).defined
    val := fun _ out =>
      ∀ h_def : p.defined, ∀ h_t : (ConcreteTargetLang.sem (p.val h_def) q).defined,
        (ConcreteTargetLang.sem (p.val h_def) q).val h_t out
  }

/-- `semIfCompiled p ≤ b` is equivalent to conditional target refinement
    `∀ h_def : p.defined, ConcreteTargetLang.sem (p.val h_def) ≤ b`. -/
theorem semIfCompiled_le_iff
    (p : Partial TargetArtifact) (b : ConcreteTargetLang.Behavior) :
    semIfCompiled p ≤ b ↔
      ∀ h_def : p.defined, ConcreteTargetLang.sem (p.val h_def) ≤ b := by
  constructor
  · intro h h_def q h_b
    cases h q h_b with
    | intro h_all h_val =>
      exact ⟨h_all h_def, fun out h_out => h_val out ⟨h_def, h_out⟩⟩
  · intro h q h_b
    refine ⟨fun h_def => (h h_def q h_b).1, ?_⟩
    intro out ⟨h_def, h_out⟩
    exact (h h_def q h_b).2 out h_out

/-- Whenever `p.defined` (`NoPME`) holds, `semTotalCompiled p` and
    `ConcreteTargetLang.sem (p.val h_def)` refine the exact same specifications. -/
theorem semTotalCompiled_le_iff_of_defined
    {p : Partial TargetArtifact} (h_def : p.defined)
    (b : ConcreteTargetLang.Behavior) :
    semTotalCompiled p ≤ b ↔ ConcreteTargetLang.sem (p.val h_def) ≤ b := by
  constructor
  · intro h q h_b
    cases h q h_b with
    | intro h_ex h_val =>
      cases h_ex with
      | intro h_def' h_t =>
        exact ⟨h_t, fun out h_out => h_val out (fun _ _ => h_out)⟩
  · intro h q h_b
    cases h q h_b with
    | intro h_t h_val =>
      refine ⟨⟨h_def, h_t⟩, ?_⟩
      intro out h_sem_out
      exact h_val out (h_sem_out h_def h_t)

/-- Conversely, if `semTotalCompiled p ≤ b` holds and `b` is defined at some
    query `q₀`, then compilation of `p` must succeed (`p.defined`). -/
theorem defined_of_semTotalCompiled_le
    {p : Partial TargetArtifact} {b : ConcreteTargetLang.Behavior}
    (h_le : semTotalCompiled p ≤ b)
    {q₀ : ExecQuery MirState} (h_b₀ : (b q₀).defined) :
    p.defined := by
  cases h_le q₀ h_b₀ with
  | intro h_ex _ => exact h_ex.1

/-- Partial target language `PartialTargetLang` whose programs are
    `Partial TargetArtifact` and whose semantics is `semTotalCompiled`. -/
def PartialTargetLang : Language where
  Prog := Partial TargetArtifact
  Query := ExecQuery MirState
  Out := ExecOut Unit MirVal
  sem := semTotalCompiled

/-- Standard `Trusted.Compiler` instance lowering `MonoMirUnit` to
    `Partial TargetArtifact`. -/
def MonoRustcCompiler : Compiler MonoMirLang PartialTargetLang where
  compile := rustcCompileMono
  π := π_c

/-- Conditional ("If Compiled") verification for a `MonoMirUnit`:
    Assuming `u` compiles without a PME (`(MonoRustcCompiler.compile u).defined`),
    `MonoRustcCompiler.Verified u spec` holds. -/
def VerifiedIfCompiled (u : MonoMirUnit) (spec : MonoMirLang.Behavior) : Prop :=
  (MonoRustcCompiler.compile u).defined → MonoRustcCompiler.Verified u spec

/-- Total verification (`MonoRustcCompiler.Verified u spec`) is equivalent to
    `NoPME` (`(MonoRustcCompiler.compile u).defined`) paired with
    `VerifiedIfCompiled u spec` whenever `spec` is defined at some query `q₀`. -/
theorem verifiedTotal_iff_noPme_and_verifiedIfCompiled
    (u : MonoMirUnit) (spec : MonoMirLang.Behavior)
    {q₀ : ExecQuery MirState} (h_spec₀ : (spec q₀).defined) :
    ((MonoRustcCompiler.compile u).defined ∧ VerifiedIfCompiled u spec) ↔
      MonoRustcCompiler.Verified u spec := by
  constructor
  · intro ⟨h_def, h_if⟩
    exact h_if h_def
  · intro h_ver
    have h_def : (MonoRustcCompiler.compile u).defined :=
      ((h_ver.1 q₀ h_spec₀).1).1
    exact ⟨h_def, fun _ => h_ver⟩

/-!
## 4. Comparing Representation R1 and Representation R2 (`model-refinement`)

### Representation R1: Instantiation-Indexed `MonoMirUnit` Family
-/

inductive TCBItem where
  | rustcLoweringMono (fnName : String) (u : MonoMirUnit)
  | userAxiom (name : String) (prop : Prop)

instance instTrustedAssumptionTCBItem : TrustedAssumption TCBItem where
  meaning
    | .rustcLoweringMono _ u => MonoRustcCompiler.SoundOn u
    | .userAxiom _ prop => prop

def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLoweringMono _ _ => True
    | .userAxiom _ _ => False

/-- Representation R1 of a polymorphic captured MIR function: an
    `InstCtx`-indexed family of `MonoMirUnit`s with instantiation precondition
    `instPre` (`LIB-07` semantic trait obligations and layout validity),
    explicit PME-freedom bound `noPmePre`, runtime argument precondition
    `argPre`, and specifications `specs`. -/
structure PolyCapturedFnR1 (InstCtx : Type) where
  name : String
  unit : InstCtx → MonoMirUnit
  tcb : InstCtx → List TCBItem
  instPre : InstCtx → Prop := fun _ => True
  noPmePre : InstCtx → Prop := fun _ => True
  argPre : InstCtx → ExecQuery MirState → Prop := fun _ _ => True
  specs : InstCtx → List MonoMirLang.Behavior := fun _ => []

/-- R1 Theorem Shape 1 (Unconditional Polymorphic Safety If Compiled):
    For every `inst : InstCtx` satisfying `fn.instPre inst` where `rustc`
    compiles `fn.unit inst` (`(MonoRustcCompiler.compile (fn.unit inst)).defined`),
    the monomorphized unit satisfies `VerificationResultOn`. -/
def PolySafetyIfCompiledR1 {InstCtx : Type} (fn : PolyCapturedFnR1 InstCtx) : Prop :=
  ∀ inst : InstCtx,
    fn.instPre inst →
    (MonoRustcCompiler.compile (fn.unit inst)).defined →
    VerificationResultOn MonoRustcCompiler defaultTrustPolicy (fn.tcb inst)
      (fn.unit inst) (fn.argPre inst) (fn.specs inst)

/-- R1 Theorem Shape 2 (Sufficient Compile-Time Totality Condition `NoPME`):
    For every `inst : InstCtx` satisfying `fn.instPre inst` and `fn.noPmePre inst`,
    `rustc` compilation of `fn.unit inst` is guaranteed to succeed without a PME. -/
def PolyNoPmeR1 {InstCtx : Type} (fn : PolyCapturedFnR1 InstCtx) : Prop :=
  ∀ inst : InstCtx,
    fn.instPre inst →
    fn.noPmePre inst →
    (MonoRustcCompiler.compile (fn.unit inst)).defined

/-- R1 Theorem Shape 3 (Total Polymorphic Verification on `instPre ∧ noPmePre`):
    For every `inst : InstCtx` satisfying `fn.instPre inst` and `fn.noPmePre inst`,
    `fn.unit inst` compiles without a PME and satisfies `VerificationResultOn`. -/
def PolyTotalVerifiedR1 {InstCtx : Type} (fn : PolyCapturedFnR1 InstCtx) : Prop :=
  ∀ inst : InstCtx,
    fn.instPre inst →
    fn.noPmePre inst →
    (MonoRustcCompiler.compile (fn.unit inst)).defined ∧
    VerificationResultOn MonoRustcCompiler defaultTrustPolicy (fn.tcb inst)
      (fn.unit inst) (fn.argPre inst) (fn.specs inst)

/-- Combining `PolySafetyIfCompiledR1` (Guarantee 1) and `PolyNoPmeR1`
    (Guarantee 2) immediately yields `PolyTotalVerifiedR1` (Guarantee 3). -/
theorem polyTotalVerifiedR1_of_ifCompiled_and_noPme
    {InstCtx : Type} {fn : PolyCapturedFnR1 InstCtx}
    (h_if : PolySafetyIfCompiledR1 fn)
    (h_nopme : PolyNoPmeR1 fn) :
    PolyTotalVerifiedR1 fn := by
  intro inst h_inst h_bound
  have h_def := h_nopme inst h_inst h_bound
  exact ⟨h_def, h_if inst h_inst h_def⟩

/-!
### Representation R2: Query-Enriched Language (`PolyMirLang InstCtx`)

In R2, we enrich the language query type itself to
`PolyQuery InstCtx := InstCtx × ExecQuery MirState`:
- `PolyMirLang.sem prog ⟨inst, q⟩` is definitionally `MonoMirLang.sem (prog inst) q`.
- `PolyTargetLang.sem t ⟨inst, q⟩` is definitionally `PartialTargetLang.sem (t inst) q`.
- Both instantiation preconditions (`instPre`, `noPmePre`) and runtime argument
  preconditions (`argPre`) are predicates on `PolyQuery InstCtx`!
-/

/-- Enriched query pairing a monomorphization context `inst : InstCtx` with a
    runtime execution query `q : ExecQuery MirState`. -/
abbrev PolyQuery (InstCtx : Type) : Type :=
  InstCtx × ExecQuery MirState

/-- Polymorphic MIR program in R2 (`InstCtx → MonoMirUnit`). -/
abbrev PolyProg (InstCtx : Type) : Type :=
  InstCtx → MonoMirUnit

/-- Polymorphic target program in R2 (`InstCtx → Partial TargetArtifact`). -/
abbrev PolyTargetProg (InstCtx : Type) : Type :=
  InstCtx → Partial TargetArtifact

/-- Query-enriched source language `PolyMirLang InstCtx`. -/
def PolyMirLang (InstCtx : Type) : Language where
  Prog := PolyProg InstCtx
  Query := PolyQuery InstCtx
  Out := ExecOut Unit MirVal
  sem prog pq := MonoMirLang.sem (prog pq.1) pq.2

/-- Query-enriched target language `PolyTargetLang InstCtx`. -/
def PolyTargetLang (InstCtx : Type) : Language where
  Prog := PolyTargetProg InstCtx
  Query := PolyQuery InstCtx
  Out := ExecOut Unit MirVal
  sem t pq := PartialTargetLang.sem (t pq.1) pq.2

/-- Pointwise lifting of `π_c` to `PolyMirLang` / `PolyTargetLang` behaviors. -/
def π_poly (InstCtx : Type)
    (b : (PolyMirLang InstCtx).Behavior) : (PolyTargetLang InstCtx).Behavior :=
  fun ⟨inst, q⟩ => π_c (fun q' => b ⟨inst, q'⟩) q

/-- Standard `Trusted.Compiler` instance from `PolyMirLang InstCtx` to
    `PolyTargetLang InstCtx`. -/
def PolyRustcCompiler (InstCtx : Type) :
    Compiler (PolyMirLang InstCtx) (PolyTargetLang InstCtx) where
  compile prog inst := MonoRustcCompiler.compile (prog inst)
  π := π_poly InstCtx

/-- If `π_c` is monotone, then `π_poly InstCtx` is monotone. -/
theorem monotone_π_poly (InstCtx : Type) (h_mono : Monotone π_c) :
    Monotone (π_poly InstCtx) := by
  intro b₁ b₂ hle ⟨inst, q⟩
  exact h_mono (fun q' => hle ⟨inst, q'⟩) q

/-- Pointwise `MonoRustcCompiler.SoundOn (prog inst)` across all `inst : InstCtx`
    implies `(PolyRustcCompiler InstCtx).SoundOn prog` with zero extra axioms! -/
theorem polyRustcCompiler_soundOn_of_pointwise
    {InstCtx : Type} (prog : PolyProg InstCtx)
    (h_mono : Monotone π_c)
    (h_sound : ∀ inst : InstCtx, MonoRustcCompiler.SoundOn (prog inst)) :
    (PolyRustcCompiler InstCtx).SoundOn prog := by
  refine ⟨monotone_π_poly InstCtx h_mono, ?_⟩
  intro ⟨inst, q⟩
  exact (h_sound inst).2 q

/-- In R2, the "If Compiled" precondition on `PolyQuery InstCtx` conjoins
    compile-time PME success `(prog inst).pmeOk`, the instantiation precondition
    `instPre inst`, and the runtime argument precondition `argPre inst q`. -/
def polyIfCompiledPre {InstCtx : Type}
    (prog : PolyProg InstCtx)
    (instPre : InstCtx → Prop)
    (argPre : InstCtx → ExecQuery MirState → Prop) : PolyQuery InstCtx → Prop :=
  fun ⟨inst, q⟩ => (prog inst).pmeOk ∧ instPre inst ∧ argPre inst q

/-- Naive R2 total precondition: conjoins `instPre inst`, `noPmePre inst`, and
    `argPre inst q`. (As shown in `naive_r2_vacuous_argPre_counterexample` below,
    this naive conjunction loses `NoPME` whenever `argPre inst` is uninhabited.) -/
def naiveTotalPre {InstCtx : Type}
    (instPre noPmePre : InstCtx → Prop)
    (argPre : InstCtx → ExecQuery MirState → Prop) : PolyQuery InstCtx → Prop :=
  fun ⟨inst, q⟩ => instPre inst ∧ noPmePre inst ∧ argPre inst q

/-- Refined R2 total precondition (`model-refinement` Pass 2):
    Because `q.steps = 0` represents 0 runtime steps (compile-time
    monomorphization before any runtime step executes, where `MirLang.sem` is
    always `.running`), requiring definedness on `q.steps = 0 ∨ argPre inst q`
    enforces compile-time `NoPME` at `q.steps = 0` independently of whether
    `argPre inst` is inhabited, while enforcing runtime UB-freedom across all
    `q` satisfying `argPre inst q`. -/
def unifiedTotalPre {InstCtx : Type}
    (instPre noPmePre : InstCtx → Prop)
    (argPre : InstCtx → ExecQuery MirState → Prop) : PolyQuery InstCtx → Prop :=
  fun ⟨inst, q⟩ => instPre inst ∧ noPmePre inst ∧ (q.steps = 0 ∨ argPre inst q)

/-- Exact Equivalence Theorem between R1 and R2 at the Source Semantic Level:
    Refining `(PolyMirLang InstCtx).WellFormedOn (unifiedTotalPre instPre noPmePre argPre)`
    in R2 is constructively equivalent (`↔`) to R1's conjunction of:
    1. `PolyNoPmeR1`: `∀ inst, instPre inst → noPmePre inst → (prog inst).pmeOk`, and
    2. Pointwise conditional well-formedness:
       `∀ inst, instPre inst → noPmePre inst → MonoMirLang.sem (prog inst) ≤ MonoMirLang.WellFormedOn (argPre inst)`. -/
theorem r1_iff_r2_source_wellFormed
    {InstCtx : Type} (prog : PolyProg InstCtx)
    (instPre noPmePre : InstCtx → Prop)
    (argPre : InstCtx → ExecQuery MirState → Prop) :
    ((PolyMirLang InstCtx).sem prog ≤
      (PolyMirLang InstCtx).WellFormedOn (unifiedTotalPre instPre noPmePre argPre)) ↔
    ((∀ inst, instPre inst → noPmePre inst → (prog inst).pmeOk) ∧
     (∀ inst, instPre inst → noPmePre inst →
       MonoMirLang.sem (prog inst) ≤ MonoMirLang.WellFormedOn (argPre inst))) := by
  constructor
  · intro h_r2
    refine ⟨?_, ?_⟩
    · intro inst h_inst h_nopme
      have h_at_zero := h_r2 ⟨inst, { init := dummyMirState, steps := 0 }⟩
        ⟨h_inst, h_nopme, Or.inl rfl⟩
      exact h_at_zero.1.1
    · intro inst h_inst h_nopme q h_arg
      have h_at_q := h_r2 ⟨inst, q⟩ ⟨h_inst, h_nopme, Or.inr h_arg⟩
      exact ⟨h_at_q.1, fun _ _ => True.intro⟩
  · intro ⟨h_nopme, h_wf⟩ ⟨inst, q⟩ ⟨h_inst, h_bound, h_zero_or_arg⟩
    cases h_zero_or_arg with
    | inl h_zero =>
      have hpme := h_nopme inst h_inst h_bound
      have h_mir0 : (MirLang.sem (prog inst).body q).defined := by
        cases q with
        | mk init steps =>
          cases h_zero
          exact behaviorOf_defined_at_zero (prog inst).body init
      exact ⟨⟨hpme, h_mir0⟩, fun _ _ => True.intro⟩
    | inr h_arg =>
      exact h_wf inst h_inst h_bound q h_arg

/-- Retained Domain Preservation (`model-refinement` Check):
    A monomorphic compilation unit `u : MonoMirUnit` embeds into R2 at
    `InstCtx = Unit` (`fun _ : Unit => u`), and R2 well-formedness on
    `unifiedTotalPre (fun _ => True) (fun _ => True) (fun _ => argPre)` is
    constructively equivalent (`↔`) to `u.pmeOk ∧ MonoMirLang.sem u ≤ MonoMirLang.WellFormedOn argPre`. -/
theorem mono_embeds_into_r2_iff
    (u : MonoMirUnit) (argPre : ExecQuery MirState → Prop) :
    ((PolyMirLang Unit).sem (fun _ => u) ≤
      (PolyMirLang Unit).WellFormedOn
        (unifiedTotalPre (fun _ => True) (fun _ => True) (fun _ => argPre))) ↔
    (u.pmeOk ∧ MonoMirLang.sem u ≤ MonoMirLang.WellFormedOn argPre) := by
  constructor
  · intro h_r2
    have h_iff := (r1_iff_r2_source_wellFormed (fun _ : Unit => u)
      (fun _ => True) (fun _ => True) (fun _ => argPre)).mp h_r2
    exact ⟨h_iff.1 () True.intro True.intro, h_iff.2 () True.intro True.intro⟩
  · intro ⟨h_pme, h_wf⟩
    exact (r1_iff_r2_source_wellFormed (fun _ : Unit => u)
      (fun _ => True) (fun _ => True) (fun _ => argPre)).mpr
      ⟨fun _ _ _ => h_pme, fun _ _ _ => h_wf⟩

/-- Projecting a Concrete Instance from R2 to R1:
    Given an R2 `(PolyRustcCompiler InstCtx).Verified` proof on `unifiedTotalPre`,
    any downstream caller supplying a concrete `inst : InstCtx` that satisfies
    `instPre inst` and `noPmePre inst` immediately extracts:
    1. `(MonoRustcCompiler.compile (prog inst)).defined` (`NoPME` at `inst`), and
    2. `MonoRustcCompiler.Verified (prog inst) (MonoMirLang.WellFormedOn (argPre inst))`! -/
theorem r2_projects_to_r1_instance
    {InstCtx : Type} (prog : PolyProg InstCtx)
    (instPre noPmePre : InstCtx → Prop)
    (argPre : InstCtx → ExecQuery MirState → Prop)
    (h_mono : Monotone π_c)
    (h_r2 : (PolyRustcCompiler InstCtx).Verified prog
      ((PolyMirLang InstCtx).WellFormedOn (unifiedTotalPre instPre noPmePre argPre)))
    (inst : InstCtx) (h_inst : instPre inst) (h_bound : noPmePre inst) :
    (MonoRustcCompiler.compile (prog inst)).defined ∧
    MonoRustcCompiler.Verified (prog inst) (MonoMirLang.WellFormedOn (argPre inst)) := by
  have h_src_iff := (r1_iff_r2_source_wellFormed prog instPre noPmePre argPre).mp h_r2.1
  have h_pme : (MonoRustcCompiler.compile (prog inst)).defined :=
    h_src_iff.1 inst h_inst h_bound
  have h_src_inst : MonoMirLang.sem (prog inst) ≤ MonoMirLang.WellFormedOn (argPre inst) :=
    h_src_iff.2 inst h_inst h_bound
  have h_comp_inst : Compiles MonoMirLang PartialTargetLang π_c
      (prog inst) (MonoRustcCompiler.compile (prog inst)) :=
    fun q => h_r2.2.1 ⟨inst, q⟩
  have h_sound_inst : MonoRustcCompiler.SoundOn (prog inst) :=
    ⟨h_mono, h_comp_inst⟩
  exact ⟨h_pme, Compiler.SoundOn.verify h_sound_inst h_src_inst⟩

/-- In R2, proving `PolyNoPmeR1` (`∀ inst, instPre inst → noPmePre inst → (prog inst).pmeOk`)
    and `IfCompiled` verification on `polyIfCompiledPre` for `(q.steps = 0 ∨ argPre inst q)`
    immediately yields total verification on `unifiedTotalPre` via `specOn_antitone_pre`
    and `Compiler.Verified.mono`! -/
theorem r2_total_verified_of_ifCompiled_and_noPme
    {InstCtx : Type} (prog : PolyProg InstCtx)
    (instPre noPmePre : InstCtx → Prop)
    (argPre : InstCtx → ExecQuery MirState → Prop)
    (post : PolyQuery InstCtx → ExecOut Unit MirVal → Prop)
    (h_mono : Monotone π_c)
    (h_if_compiled :
      (PolyRustcCompiler InstCtx).Verified prog
        ((PolyMirLang InstCtx).SpecOn
          (polyIfCompiledPre prog instPre (fun inst q => q.steps = 0 ∨ argPre inst q))
          post))
    (h_nopme : ∀ inst, instPre inst → noPmePre inst → (prog inst).pmeOk) :
    (PolyRustcCompiler InstCtx).Verified prog
      ((PolyMirLang InstCtx).SpecOn
        (unifiedTotalPre instPre noPmePre argPre)
        post) := by
  refine Compiler.Verified.mono h_if_compiled ?_ (monotone_π_poly InstCtx h_mono)
  refine specOn_antitone_pre ?_
  intro ⟨inst, q⟩ ⟨h_inst, h_bound, h_q⟩
  exact ⟨h_nopme inst h_inst h_bound, h_inst, h_q⟩

/-!
## 5. Boundary Counterexample (`naiveTotalPre` vs. `unifiedTotalPre` under `model-refinement`)

Suppose a polymorphic function has an uninhabited runtime argument precondition
`argPre inst := fun _ => False` (or is referenced inside a cold branch that is
never dynamically entered), and fails compilation with a PME (`pmeOk = False`).
In `rustc`, `Body::required_consts` is evaluated during monomorphization
collection regardless of runtime arguments, so compilation aborts.

We prove that:
1. `naiveTotalPre` (`instPre inst ∧ noPmePre inst ∧ argPre inst q`) vacuously
   accepts `brokenPmeProg` (`naive_r2_vacuous_argPre_counterexample`), failing
   to detect the PME.
2. `unifiedTotalPre` (`instPre inst ∧ noPmePre inst ∧ (q.steps = 0 ∨ argPre inst q)`)
   rejects `brokenPmeProg` (`refined_r2_rejects_pme_even_when_argPre_empty`),
   because `q.steps = 0` checks compile-time monomorphization independently of
   `argPre`.
-/

def trivialRetBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ }
  ]

def brokenPmeProg : PolyProg Unit :=
  fun _ => { body := trivialRetBody, pmeOk := False }

/-- Negative Control 4a: `brokenPmeProg` fails compilation with a PME at `()`. -/
theorem brokenPmeProg_not_compiled :
    ¬ (MonoRustcCompiler.compile (brokenPmeProg ())).defined :=
  fun h => h

/-- Negative Control 4b: Despite failing compilation with a PME, `brokenPmeProg`
    vacuously satisfies `WellFormedOn (naiveTotalPre ...)` when `argPre` is
    uninhabited (`fun _ _ => False`). -/
theorem naive_r2_vacuous_argPre_counterexample :
    (PolyMirLang Unit).sem brokenPmeProg ≤
      (PolyMirLang Unit).WellFormedOn
        (naiveTotalPre (fun _ => True) (fun _ => True) (fun _ _ => False)) := by
  intro ⟨_, _⟩ ⟨_, _, h_false⟩
  exact False.elim h_false

/-- Negative Control 4c: Our refined R2 precondition `unifiedTotalPre` rejects
    `brokenPmeProg` even when `argPre` is `fun _ _ => False`, because the
    0-step query `q.steps = 0` tests compile-time PME-freedom directly. -/
theorem refined_r2_rejects_pme_even_when_argPre_empty :
    ¬ ((PolyMirLang Unit).sem brokenPmeProg ≤
        (PolyMirLang Unit).WellFormedOn
          (unifiedTotalPre (fun _ => True) (fun _ => True) (fun _ _ => False))) := by
  intro h_le
  have h_zero := h_le ⟨(), { init := dummyMirState, steps := 0 }⟩
    ⟨True.intro, True.intro, Or.inl rfl⟩
  exact h_zero.1.1

/-!
## 6. Mechanization of `pub fn checked<T: Bound, const N: usize>(x: usize) -> usize`

Consider the generic Rust library function:
```rust
pub trait Bound {
    const LIMIT: usize;
    fn delta() -> usize;
    // Semantic trait contract (`LIB-07`):
    // `delta() <= LIMIT` and `LIMIT <= 1000`
}

pub fn checked<T: Bound, const N: usize>(x: usize) -> usize {
    const { assert!(N <= T::LIMIT); }
    x + N + T::delta()
}
```
-/

/-- Post-monomorphization layout validity (`tcx.layout_of(T)`). -/
def layoutValid (inst : CheckedInstCtx) : Prop :=
  0 < inst.tyAlign ∧ inst.tySize ≤ isizeMax

/-- Compile-time PME predicate (`Body::required_consts` `const { assert!(N <= T::LIMIT); }`
    and post-monomorphization layout check). -/
def checkedPmeOk (inst : CheckedInstCtx) : Prop :=
  layoutValid inst ∧ inst.constN ≤ inst.traitLimit

/-- Caller-supplied semantic trait implementation contract (`LIB-07`) for `T: Bound`. -/
def boundTraitContract (inst : CheckedInstCtx) : Prop :=
  layoutValid inst ∧ inst.traitDelta ≤ inst.traitLimit ∧ inst.traitLimit ≤ 1000

/-- Explicit caller-visible const generic bound sufficient to prevent a PME. -/
def checkedNoPmePre (inst : CheckedInstCtx) : Prop :=
  inst.constN ≤ inst.traitLimit

/-- Runtime call-site argument precondition (`x <= 1000`). -/
def checkedArgPre (_inst : CheckedInstCtx) (q : ExecQuery MirState) : Prop :=
  ∀ x0, q.init.locals 1 = some (.usize x0) → x0 ≤ 1000

/-- Functional postcondition for `checked<T, N>(x)`:
    any normal return value equals `x0 + N + T::delta()` and is bounded by
    `x0 + 2 * T::LIMIT`. -/
def checkedPost (inst : CheckedInstCtx) (q : ExecQuery MirState)
    (out : ExecOut Unit MirVal) : Prop :=
  ∀ ret x0,
    out.outcome = .terminated (.normal ret) →
    q.init.locals 1 = some (.usize x0) →
    ret = .usize (x0 + inst.constN + inst.traitDelta) ∧
      x0 + inst.constN + inst.traitDelta ≤ x0 + 2 * inst.traitLimit

/-- Monomorphized `Runtime(PostCleanup)` `MirBody` of
    `pub fn checked<T: Bound, const N: usize>(x: usize) -> usize`:
    - `bb0`: `_2 = CheckedAdd(copy _1, const N)`; `assert(!move (_2.1)) -> bb1`
    - `bb1`: `_3 = _2.0`; `_4 = CheckedAdd(copy _3, const T::delta())`;
      `assert(!move (_4.1)) -> bb2`
    - `bb2`: `_0 = _4.0`; `return` -/
def checkedMonoBody (inst : CheckedInstCtx) : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 5
  blocks := [
    -- bb0
    { stmts := [
        .assign ⟨2⟩ (.checkedBinaryOp .add (.copy ⟨1⟩) (.constVal (.usize inst.constN)))
      ]
      terminator := .assertNotOverflow ⟨2⟩ ⟨1⟩ },
    -- bb1
    { stmts := [
        .assign ⟨3⟩ (.proj0 ⟨2⟩),
        .assign ⟨4⟩ (.checkedBinaryOp .add (.copy ⟨3⟩) (.constVal (.usize inst.traitDelta)))
      ]
      terminator := .assertNotOverflow ⟨4⟩ ⟨2⟩ },
    -- bb2
    { stmts := [
        .assign ⟨0⟩ (.proj0 ⟨4⟩)
      ]
      terminator := .return_ }
  ]

/-- Monomorphized compilation unit for `checked<T, N>`. -/
def checkedUnit (inst : CheckedInstCtx) : MonoMirUnit where
  body := checkedMonoBody inst
  pmeOk := checkedPmeOk inst

/-- Specification of `checked<inst>` in `MonoMirLang`. -/
def EnsuresChecked (inst : CheckedInstCtx) : MonoMirLang.Behavior :=
  MonoMirLang.SpecOn (checkedArgPre inst) (checkedPost inst)

/-- Arithmetic helper: if `x0 ≤ 1000`, `N ≤ limit`, and `limit ≤ 1000`, then
    `decide (usizeMax < x0 + N) = false`. -/
theorem checked_add1_no_overflow
    {x0 constN limit : Nat}
    (hx : x0 ≤ 1000) (hN : constN ≤ limit) (hlim : limit ≤ 1000) :
    decide (usizeMax < x0 + constN) = false :=
  decide_eq_false (by unfold usizeMax; omega)

/-- Arithmetic helper: if `x0 ≤ 1000`, `N ≤ limit`, `delta ≤ limit`, and
    `limit ≤ 1000`, then `decide (usizeMax < x0 + N + delta) = false`. -/
theorem checked_add2_no_overflow
    {x0 constN delta limit : Nat}
    (hx : x0 ≤ 1000) (hN : constN ≤ limit) (hD : delta ≤ limit) (hlim : limit ≤ 1000) :
    decide (usizeMax < x0 + constN + delta) = false :=
  decide_eq_false (by unfold usizeMax; omega)

/-- Operational verification of `checkedMonoBody inst`:
    Under `boundTraitContract inst` (`LIB-07`), `inst.constN ≤ inst.traitLimit`
    (from PME `required_consts`), and `checkedArgPre inst q` (`x0 ≤ 1000`),
    every finite execution prefix of `checkedMonoBody inst` is safe and
    satisfies `checkedPost inst`. -/
theorem checkedMonoBody_le_specOn
    (inst : CheckedInstCtx)
    (h_trait : boundTraitContract inst)
    (h_bound : inst.constN ≤ inst.traitLimit) :
    MirLang.sem (checkedMonoBody inst) ≤
      MirLang.SpecOn (checkedArgPre inst) (checkedPost inst) := by
  refine behaviorOf_le_specOn ?_
  rintro ⟨init, steps⟩ ⟨tr, oc⟩ h_pre ⟨h_init, h_reach⟩
  dsimp at h_pre h_init h_reach
  rcases h_init with ⟨hb0, hs0, hloc0, ⟨v1, hloc1, hty1⟩, _⟩
  cases v1 with
  | bool _ => cases hty1
  | unit => cases hty1
  | tupleUsizeBool _ _ => cases hty1
  | usize x0 =>
    have hx0 : x0 ≤ 1000 := h_pre x0 hloc1
    have hD : inst.traitDelta ≤ inst.traitLimit := h_trait.2.1
    have hlim : inst.traitLimit ≤ 1000 := h_trait.2.2
    have hov1 : decide (usizeMax < x0 + inst.constN) = false :=
      checked_add1_no_overflow hx0 h_bound hlim
    have hov2 : decide (usizeMax < x0 + inst.constN + inst.traitDelta) = false :=
      checked_add2_no_overflow hx0 h_bound hD hlim
    -- Step-by-step symbolic execution of `checkedMonoBody inst` across all `steps`:
    have h_step0 : evalMirStep (checkedMonoBody inst) init =
        .step () { init with
          locals := updateLocal init.locals 2
            (some (.tupleUsizeBool (x0 + inst.constN) false))
          stmtIdx := 1 } := by
      simp [evalMirStep, checkedMonoBody, hb0, hs0, evalMirStmt, evalOperand,
        hloc1, evalCheckedBinOp, hov1]
    generalize hs1_def :
      ({ init with
        locals := updateLocal init.locals 2
          (some (.tupleUsizeBool (x0 + inst.constN) false))
        stmtIdx := 1 } : MirState) = s1 at h_step0
    have h_step1 : evalMirStep (checkedMonoBody inst) s1 =
        .step () { s1 with block := 1, stmtIdx := 0 } := by
      rw [← hs1_def]
      simp [evalMirStep, checkedMonoBody, hb0, evalMirTerminator, updateLocal]
    generalize hs2_def : ({ s1 with block := 1, stmtIdx := 0 } : MirState) = s2 at h_step1
    have h_step2 : evalMirStep (checkedMonoBody inst) s2 =
        .step () { s2 with
          locals := updateLocal s2.locals 3 (some (.usize (x0 + inst.constN)))
          stmtIdx := 1 } := by
      rw [← hs2_def, ← hs1_def]
      simp [evalMirStep, checkedMonoBody, evalMirStmt, updateLocal]
    generalize hs3_def :
      ({ s2 with
        locals := updateLocal s2.locals 3 (some (.usize (x0 + inst.constN)))
        stmtIdx := 1 } : MirState) = s3 at h_step2
    have h_step3 : evalMirStep (checkedMonoBody inst) s3 =
        .step () { s3 with
          locals := updateLocal s3.locals 4
            (some (.tupleUsizeBool (x0 + inst.constN + inst.traitDelta) false))
          stmtIdx := 2 } := by
      rw [← hs3_def, ← hs2_def, ← hs1_def]
      simp [evalMirStep, checkedMonoBody, evalMirStmt, evalOperand, updateLocal,
        evalCheckedBinOp, hov2]
    generalize hs4_def :
      ({ s3 with
        locals := updateLocal s3.locals 4
          (some (.tupleUsizeBool (x0 + inst.constN + inst.traitDelta) false))
        stmtIdx := 2 } : MirState) = s4 at h_step3
    have h_step4 : evalMirStep (checkedMonoBody inst) s4 =
        .step () { s4 with block := 2, stmtIdx := 0 } := by
      rw [← hs4_def, ← hs3_def, ← hs2_def, ← hs1_def]
      simp [evalMirStep, checkedMonoBody, evalMirTerminator, updateLocal]
    generalize hs5_def : ({ s4 with block := 2, stmtIdx := 0 } : MirState) = s5 at h_step4
    have h_step5 : evalMirStep (checkedMonoBody inst) s5 =
        .step () { s5 with
          locals := updateLocal s5.locals 0
            (some (.usize (x0 + inst.constN + inst.traitDelta)))
          stmtIdx := 1 } := by
      rw [← hs5_def, ← hs4_def, ← hs3_def, ← hs2_def, ← hs1_def]
      simp [evalMirStep, checkedMonoBody, evalMirStmt, updateLocal]
    generalize hs6_def :
      ({ s5 with
        locals := updateLocal s5.locals 0
          (some (.usize (x0 + inst.constN + inst.traitDelta)))
        stmtIdx := 1 } : MirState) = s6 at h_step5
    have h_step6 : evalMirStep (checkedMonoBody inst) s6 =
        .terminated (.normal (.usize (x0 + inst.constN + inst.traitDelta))) := by
      rw [← hs6_def, ← hs5_def, ← hs4_def, ← hs3_def, ← hs2_def, ← hs1_def]
      simp [evalMirStep, checkedMonoBody, evalMirTerminator, updateLocal]
    -- Invert up to 7 steps of `ReachesPrefix`:
    cases h_reach with
    | zero =>
      exact ⟨True.intro, fun _ _ hterm _ => by cases hterm⟩
    | choice _ _ _ _ _ _ _ hst =>
      change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
    | emptyChoice _ _ _ _ hst =>
      change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
    | terminated _ _ _ hst =>
      change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
    | failed _ _ _ hst =>
      change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, h_step0.symm⟩)
    | step _ _ _ _ _ _ hst0 hr1 =>
      change _ = evalMirStep _ _ at hst0; rw [h_step0] at hst0; cases hst0
      cases hr1 with
      | zero =>
        exact ⟨True.intro, fun _ _ hterm _ => by cases hterm⟩
      | choice _ _ _ _ _ _ _ hst =>
        change _ = evalMirStep _ _ at hst; rw [h_step1] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        change _ = evalMirStep _ _ at hst; rw [h_step1] at hst; cases hst
      | terminated _ _ _ hst =>
        change _ = evalMirStep _ _ at hst; rw [h_step1] at hst; cases hst
      | failed _ _ _ hst =>
        change _ = evalMirStep _ _ at hst; rw [h_step1] at hst; cases hst
      | noStep _ _ hno =>
        exact False.elim (hno ⟨_, h_step1.symm⟩)
      | step _ _ _ _ _ _ hst1 hr2 =>
        change _ = evalMirStep _ _ at hst1; rw [h_step1] at hst1; cases hst1
        cases hr2 with
        | zero =>
          exact ⟨True.intro, fun _ _ hterm _ => by cases hterm⟩
        | choice _ _ _ _ _ _ _ hst =>
          change _ = evalMirStep _ _ at hst; rw [h_step2] at hst; cases hst
        | emptyChoice _ _ _ _ hst =>
          change _ = evalMirStep _ _ at hst; rw [h_step2] at hst; cases hst
        | terminated _ _ _ hst =>
          change _ = evalMirStep _ _ at hst; rw [h_step2] at hst; cases hst
        | failed _ _ _ hst =>
          change _ = evalMirStep _ _ at hst; rw [h_step2] at hst; cases hst
        | noStep _ _ hno =>
          exact False.elim (hno ⟨_, h_step2.symm⟩)
        | step _ _ _ _ _ _ hst2 hr3 =>
          change _ = evalMirStep _ _ at hst2; rw [h_step2] at hst2; cases hst2
          cases hr3 with
          | zero =>
            exact ⟨True.intro, fun _ _ hterm _ => by cases hterm⟩
          | choice _ _ _ _ _ _ _ hst =>
            change _ = evalMirStep _ _ at hst; rw [h_step3] at hst; cases hst
          | emptyChoice _ _ _ _ hst =>
            change _ = evalMirStep _ _ at hst; rw [h_step3] at hst; cases hst
          | terminated _ _ _ hst =>
            change _ = evalMirStep _ _ at hst; rw [h_step3] at hst; cases hst
          | failed _ _ _ hst =>
            change _ = evalMirStep _ _ at hst; rw [h_step3] at hst; cases hst
          | noStep _ _ hno =>
            exact False.elim (hno ⟨_, h_step3.symm⟩)
          | step _ _ _ _ _ _ hst3 hr4 =>
            change _ = evalMirStep _ _ at hst3; rw [h_step3] at hst3; cases hst3
            cases hr4 with
            | zero =>
              exact ⟨True.intro, fun _ _ hterm _ => by cases hterm⟩
            | choice _ _ _ _ _ _ _ hst =>
              change _ = evalMirStep _ _ at hst; rw [h_step4] at hst; cases hst
            | emptyChoice _ _ _ _ hst =>
              change _ = evalMirStep _ _ at hst; rw [h_step4] at hst; cases hst
            | terminated _ _ _ hst =>
              change _ = evalMirStep _ _ at hst; rw [h_step4] at hst; cases hst
            | failed _ _ _ hst =>
              change _ = evalMirStep _ _ at hst; rw [h_step4] at hst; cases hst
            | noStep _ _ hno =>
              exact False.elim (hno ⟨_, h_step4.symm⟩)
            | step _ _ _ _ _ _ hst4 hr5 =>
              change _ = evalMirStep _ _ at hst4; rw [h_step4] at hst4; cases hst4
              cases hr5 with
              | zero =>
                exact ⟨True.intro, fun _ _ hterm _ => by cases hterm⟩
              | choice _ _ _ _ _ _ _ hst =>
                change _ = evalMirStep _ _ at hst; rw [h_step5] at hst; cases hst
              | emptyChoice _ _ _ _ hst =>
                change _ = evalMirStep _ _ at hst; rw [h_step5] at hst; cases hst
              | terminated _ _ _ hst =>
                change _ = evalMirStep _ _ at hst; rw [h_step5] at hst; cases hst
              | failed _ _ _ hst =>
                change _ = evalMirStep _ _ at hst; rw [h_step5] at hst; cases hst
              | noStep _ _ hno =>
                exact False.elim (hno ⟨_, h_step5.symm⟩)
              | step _ _ _ _ _ _ hst5 hr6 =>
                change _ = evalMirStep _ _ at hst5; rw [h_step5] at hst5; cases hst5
                cases hr6 with
                | zero =>
                  exact ⟨True.intro, fun _ _ hterm _ => by cases hterm⟩
                | step _ _ _ _ _ _ hst6 =>
                  change _ = evalMirStep _ _ at hst6; rw [h_step6] at hst6; cases hst6
                | choice _ _ _ _ _ _ _ hst6 =>
                  change _ = evalMirStep _ _ at hst6; rw [h_step6] at hst6; cases hst6
                | emptyChoice _ _ _ _ hst6 =>
                  change _ = evalMirStep _ _ at hst6; rw [h_step6] at hst6; cases hst6
                | failed _ _ _ hst6 =>
                  change _ = evalMirStep _ _ at hst6; rw [h_step6] at hst6; cases hst6
                | noStep _ _ hno =>
                  exact False.elim (hno ⟨_, h_step6.symm⟩)
                | terminated _ _ _ hst6 =>
                  change _ = evalMirStep _ _ at hst6; rw [h_step6] at hst6; cases hst6
                  refine ⟨True.intro, ?_⟩
                  intro ret x0' hterm hx0'
                  cases hterm
                  rw [hloc1] at hx0'
                  cases hx0'
                  exact ⟨rfl, by omega⟩

/-- R1 Representation of `checked<T: Bound, const N: usize>(x: usize) -> usize`. -/
def checkedPolyFnR1 : PolyCapturedFnR1 CheckedInstCtx where
  name := "checked_lib::checked"
  unit := checkedUnit
  tcb inst := [.rustcLoweringMono "checked_lib::checked" (checkedUnit inst)]
  instPre := boundTraitContract
  noPmePre := checkedNoPmePre
  argPre := checkedArgPre
  specs inst := [EnsuresChecked inst]

/-- Guarantee 1 in R1 (Unconditional Polymorphic Safety If Compiled):
    For every `inst : CheckedInstCtx` satisfying `boundTraitContract inst`
    (`LIB-07`) where `rustc` compiles `checkedUnit inst` without a PME,
    `checkedUnit inst` satisfies `VerificationResultOn` for `checkedArgPre inst`
    and `[EnsuresChecked inst]`. -/
theorem checked_polymorphic_safety_if_compiled_r1 :
    PolySafetyIfCompiledR1 checkedPolyFnR1 := by
  intro inst h_trait h_compiled
  refine ⟨⟨True.intro, True.intro⟩, ?_⟩
  intro ⟨h_sound, _⟩
  have h_mir : MirLang.sem (checkedMonoBody inst) ≤
      MirLang.SpecOn (checkedArgPre inst) (checkedPost inst) :=
    checkedMonoBody_le_specOn inst h_trait h_compiled.2
  have h_mono_src : MonoMirLang.sem (checkedUnit inst) ≤ EnsuresChecked inst :=
    monoMirSem_le_specOn h_compiled h_mir
  have h_ver : MonoRustcCompiler.Verified (checkedUnit inst) (EnsuresChecked inst) :=
    Compiler.SoundOn.verify h_sound h_mono_src
  exact Compiler.Verified.with_wellFormedOn h_ver
    (specOn_le_wellFormedOn (L := MonoMirLang) (checkedArgPre inst) (checkedPost inst))
    h_sound.1

/-- Guarantee 2 in R1 (Sufficient Compile-Time Totality Condition `NoPME`):
    For every `inst : CheckedInstCtx` satisfying `boundTraitContract inst`
    (`LIB-07`) and the explicit bound `checkedNoPmePre inst` (`N ≤ T::LIMIT`),
    `checkedUnit inst` is guaranteed to compile without a PME. -/
theorem checked_no_pme_r1 :
    PolyNoPmeR1 checkedPolyFnR1 := by
  intro inst h_trait h_bound
  exact ⟨h_trait.1, h_bound⟩

/-- Combined Total Polymorphic Verification in R1:
    Follows immediately from Guarantees 1 and 2 via
    `polyTotalVerifiedR1_of_ifCompiled_and_noPme`. -/
theorem checked_total_verified_r1 :
    PolyTotalVerifiedR1 checkedPolyFnR1 :=
  polyTotalVerifiedR1_of_ifCompiled_and_noPme
    checked_polymorphic_safety_if_compiled_r1
    checked_no_pme_r1

/-- R2 Representation of `checked<T: Bound, const N: usize>` in `PolyMirLang`. -/
def checkedPolyProgR2 : PolyProg CheckedInstCtx :=
  checkedUnit

def checkedPolyPostR2 : PolyQuery CheckedInstCtx → ExecOut Unit MirVal → Prop :=
  fun ⟨inst, q⟩ out => q.steps = 0 ∨ checkedPost inst q out

/-- Guarantee 1 in R2 (Unconditional Polymorphic Safety If Compiled):
    Verified directly in `PolyMirLang CheckedInstCtx` on `polyIfCompiledPre`. -/
theorem checked_polymorphic_safety_if_compiled_r2
    (h_mono : Monotone π_c)
    (h_sound : ∀ inst, MonoRustcCompiler.SoundOn (checkedUnit inst)) :
    (PolyRustcCompiler CheckedInstCtx).Verified checkedPolyProgR2
      ((PolyMirLang CheckedInstCtx).SpecOn
        (polyIfCompiledPre checkedPolyProgR2 boundTraitContract
          (fun inst q => q.steps = 0 ∨ checkedArgPre inst q))
        checkedPolyPostR2) := by
  refine Compiler.SoundOn.verify
    (polyRustcCompiler_soundOn_of_pointwise checkedPolyProgR2 h_mono h_sound) ?_
  intro ⟨inst, q⟩ ⟨h_pme, h_trait, h_zero_or_arg⟩
  cases h_zero_or_arg with
  | inl h_zero =>
    have h_mir0 : (MirLang.sem (checkedMonoBody inst) q).defined := by
      cases q with
      | mk init steps =>
        cases h_zero
        exact behaviorOf_defined_at_zero (checkedMonoBody inst) init
    exact ⟨⟨h_pme, h_mir0⟩, fun _ _ => Or.inl h_zero⟩
  | inr h_arg =>
    have h_mir := checkedMonoBody_le_specOn inst h_trait h_pme.2 q h_arg
    exact ⟨⟨h_pme, h_mir.1⟩, fun out hout => Or.inr (h_mir.2 out hout)⟩

/-- Guarantee 2 in R2 (Sufficient Compile-Time Totality Condition `NoPME`):
    Expressed as a pure `PolyMirLang` specification at `q.steps = 0`! -/
theorem checked_no_pme_r2 :
    (PolyMirLang CheckedInstCtx).sem checkedPolyProgR2 ≤
      (PolyMirLang CheckedInstCtx).WellFormedOn
        (fun ⟨inst, q⟩ => boundTraitContract inst ∧ checkedNoPmePre inst ∧ q.steps = 0) := by
  intro ⟨inst, q⟩ ⟨h_trait, h_bound, h_zero⟩
  have h_mir0 : (MirLang.sem (checkedMonoBody inst) q).defined := by
    cases q with
    | mk init steps =>
      cases h_zero
      exact behaviorOf_defined_at_zero (checkedMonoBody inst) init
  exact ⟨⟨⟨h_trait.1, h_bound⟩, h_mir0⟩, fun _ _ => True.intro⟩

/-- Combined Total Polymorphic Verification in R2 on `unifiedTotalPre`:
    Derived from `checked_polymorphic_safety_if_compiled_r2` and
    `checked_no_pme_r1` by `r2_total_verified_of_ifCompiled_and_noPme`! -/
theorem checked_total_verified_r2
    (h_mono : Monotone π_c)
    (h_sound : ∀ inst, MonoRustcCompiler.SoundOn (checkedUnit inst)) :
    (PolyRustcCompiler CheckedInstCtx).Verified checkedPolyProgR2
      ((PolyMirLang CheckedInstCtx).SpecOn
        (unifiedTotalPre boundTraitContract checkedNoPmePre checkedArgPre)
        checkedPolyPostR2) :=
  r2_total_verified_of_ifCompiled_and_noPme
    checkedPolyProgR2 boundTraitContract checkedNoPmePre checkedArgPre checkedPolyPostR2
    h_mono
    (checked_polymorphic_safety_if_compiled_r2 h_mono h_sound)
    checked_no_pme_r1

/-!
## 7. Cross-Crate Client Instantiation and Negative Controls 1–3

### 7.1 Positive Cross-Crate Client (`client_good`): `checked::<TypeA, 1>(50)`
In crate `client_good`, `TypeA` implements `Bound` with `LIMIT = 10` and
`delta() = 3`, and `client_good` instantiates `checked::<TypeA, 1>(50)`.
-/

/-- Concrete instantiation `checked::<TypeA, 1>` (`TypeA::LIMIT = 10`,
    `TypeA::delta() = 3`, `N = 1`, `size = 8`, `align = 8`). -/
def instA1 : CheckedInstCtx where
  tySize := 8
  tyAlign := 8
  constN := 1
  traitLimit := 10
  traitDelta := 3

/-- `client_good` discharges the `LIB-07` semantic trait obligation for `TypeA`. -/
theorem instA1_satisfies_boundTraitContract : boundTraitContract instA1 := by
  dsimp [boundTraitContract, layoutValid, instA1, isizeMax]
  omega

/-- `client_good` discharges the explicit PME-freedom bound `1 ≤ 10`. -/
theorem instA1_satisfies_noPmePre : checkedNoPmePre instA1 := by
  dsimp [checkedNoPmePre, instA1]
  omega

/-- Modular Cross-Crate Instantiation Theorem for `client_good`:
    Using **only** the library theorem `checked_total_verified_r1` (without
    re-proving `checkedMonoBody`), `client_good` obtains both compile-time
    PME-freedom (`(MonoRustcCompiler.compile (checkedUnit instA1)).defined`) and
    `VerificationResultOn` for `checked::<TypeA, 1>`. -/
theorem client_good_instantiation_verified_modularly :
    (MonoRustcCompiler.compile (checkedUnit instA1)).defined ∧
    VerificationResultOn MonoRustcCompiler defaultTrustPolicy
      (checkedPolyFnR1.tcb instA1)
      (checkedUnit instA1)
      (checkedArgPre instA1)
      [EnsuresChecked instA1] :=
  checked_total_verified_r1 instA1
    instA1_satisfies_boundTraitContract
    instA1_satisfies_noPmePre

/-- Canonical initial `MirState` calling a 1-argument `usize` function with
    argument `x0`. -/
def initStateWithArg1 (x0 : Nat) : MirState where
  locals := fun i => if i == 1 then some (.usize x0) else none
  block := 0
  stmtIdx := 0

theorem initMirState_checked_arg1 (inst : CheckedInstCtx) (x0 : Nat) :
    initMirState (checkedMonoBody inst) (initStateWithArg1 x0) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  refine ⟨⟨.usize x0, rfl, True.intro⟩, ?_⟩
  intro j hj
  simp [initStateWithArg1]
  omega

/-- At the call site `checked::<TypeA, 1>(50)`, `client_good` discharges the
    runtime argument precondition `checkedArgPre instA1` (`50 ≤ 1000`). -/
theorem client_good_arg50_satisfies_pre (steps : Nat) :
    checkedArgPre instA1 { init := initStateWithArg1 50, steps := steps } := by
  intro x0 hloc1
  simp [initStateWithArg1] at hloc1
  cases hloc1
  omega

/-- Concrete end-to-end call-site guarantee for `checked::<TypeA, 1>(50)` in
    `client_good`:
    1. Compilation of `checked::<TypeA, 1>` succeeds without a PME,
    2. Every finite execution prefix starting from `x = 50` is free of UB, and
    3. Any normal return value equals `.usize 54` and satisfies `54 ≤ 50 + 2 * 10`. -/
theorem client_good_call_50_safe_and_exact (steps : Nat) :
    (MonoRustcCompiler.compile (checkedUnit instA1)).defined ∧
    (MonoMirLang.sem (checkedUnit instA1)
      { init := initStateWithArg1 50, steps := steps }).defined ∧
    (∀ out hdef ret,
      (MonoMirLang.sem (checkedUnit instA1)
        { init := initStateWithArg1 50, steps := steps }).val hdef out →
      out.outcome = .terminated (.normal ret) →
      ret = .usize 54 ∧ 54 ≤ 50 + 2 * 10) := by
  have h_mod := client_good_instantiation_verified_modularly
  have h_pme : (MonoRustcCompiler.compile (checkedUnit instA1)).defined := h_mod.1
  have h_mir := checkedMonoBody_le_specOn instA1
    instA1_satisfies_boundTraitContract
    instA1_satisfies_noPmePre
    { init := initStateWithArg1 50, steps := steps }
    (client_good_arg50_satisfies_pre steps)
  refine ⟨h_pme, ⟨h_pme, h_mir.1⟩, ?_⟩
  intro out hdef ret hval hterm
  have hpost := h_mir.2 out hval ret 50 hterm rfl
  exact hpost

/-- Downstream caller MIR body `pub fn entry() -> usize { checked::<T, N>(50) }`:
    - `bb0`: `_0 = call checked::<T, N>(const 50_usize) -> bb1`
    - `bb1`: `return` -/
def clientEntryBody (inst : CheckedInstCtx) : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [
    { stmts := []
      terminator := .callChecked ⟨0⟩ inst (.constVal (.usize 50)) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- Monomorphized compilation unit for `client::entry` calling `checked::<T, N>(50)`.
    In `rustc_monomorphize::collector`, collecting `client::entry` transitively
    monomorphizes its callee `checked::<T, N>`, so `clientEntryUnit inst` is
    PME-free if and only if `(MonoRustcCompiler.compile (checkedUnit inst)).defined`
    holds. -/
def clientEntryUnit (inst : CheckedInstCtx) : MonoMirUnit where
  body := clientEntryBody inst
  pmeOk := (MonoRustcCompiler.compile (checkedUnit inst)).defined

/-- Postcondition specification for `client_good::entry`:
    unconditional UB-freedom (`MonoMirLang.Spec`) and normal return `.usize 54`. -/
def EnsuresClientGoodEntry : MonoMirLang.Behavior :=
  MonoMirLang.Spec (fun _ out =>
    ∀ ret, out.outcome = .terminated (.normal ret) → ret = .usize 54)

def clientGoodTcb : List TCBItem :=
  [.rustcLoweringMono "checked_lib::checked" (checkedUnit instA1),
   .rustcLoweringMono "client_good::entry" (clientEntryUnit instA1)]

/-- Modular Call-Site Bridge Lemma:
    From `MonoMirLang.sem (checkedUnit inst) ≤ EnsuresChecked inst` and the
    call-site argument precondition `∀ steps, checkedArgPre inst { init := initStateWithArg1 x0, steps := steps }`
    alone (without inspecting `boundTraitContract` or `checkedNoPmePre`),
    we derive:
    1. `(MonoRustcCompiler.compile (checkedUnit inst)).defined` (`NoPME`),
    2. `evalCheckedCallee inst (.usize x0) = some (.usize (x0 + inst.constN + inst.traitDelta))`, and
    3. `x0 + inst.constN + inst.traitDelta ≤ x0 + 2 * inst.traitLimit`. -/
theorem evalCheckedCallee_of_ensuresChecked
    {inst : CheckedInstCtx} {x0 : Nat}
    (h_ens : MonoMirLang.sem (checkedUnit inst) ≤ EnsuresChecked inst)
    (h_arg : ∀ steps, checkedArgPre inst { init := initStateWithArg1 x0, steps := steps }) :
    (MonoRustcCompiler.compile (checkedUnit inst)).defined ∧
    evalCheckedCallee inst (.usize x0) =
      some (.usize (x0 + inst.constN + inst.traitDelta)) ∧
    x0 + inst.constN + inst.traitDelta ≤ x0 + 2 * inst.traitLimit := by
  let s0 := initStateWithArg1 x0
  have h_init : initMirState (checkedMonoBody inst) s0 :=
    initMirState_checked_arg1 inst x0
  have h_pme : (MonoRustcCompiler.compile (checkedUnit inst)).defined :=
    (h_ens { init := s0, steps := 0 } (h_arg 0)).1.1
  -- Step 1: Prove `decide (usizeMax < x0 + inst.constN) = false` by 2-step safety:
  have hov1 : decide (usizeMax < x0 + inst.constN) = false := by
    cases h_b1 : decide (usizeMax < x0 + inst.constN) with
    | false => rfl
    | true =>
      have h_safe2 := (h_ens { init := s0, steps := 2 } (h_arg 2)).1.2
      let s1 : MirState := { s0 with
        locals := updateLocal s0.locals 2 (some (.tupleUsizeBool (x0 + inst.constN) true))
        stmtIdx := 1 }
      have hs0 : MirMachine.step (checkedMonoBody inst) s0 (.step () s1) := by
        change (.step () s1) = evalMirStep (checkedMonoBody inst) s0
        simp [evalMirStep, checkedMonoBody, s0, initStateWithArg1, evalMirStmt,
          evalOperand, evalCheckedBinOp, h_b1, s1]
      have hs1 : MirMachine.step (checkedMonoBody inst) s1 (.failed .contractViolation) := by
        change (.failed .contractViolation) = evalMirStep (checkedMonoBody inst) s1
        simp [evalMirStep, checkedMonoBody, s1, s0, initStateWithArg1,
          evalMirTerminator, updateLocal]
      have h_reach2 : ReachesPrefix MirMachine (checkedMonoBody inst) s0 2 s0
          [()] (.failed .contractViolation) :=
        .step 1 s0 s1 () [] (.failed .contractViolation) hs0
          (.failed 0 s1 .contractViolation hs1)
      exact False.elim (h_safe2 h_init [()] (.failed .contractViolation) h_reach2)
  -- Step 2: Prove `decide (usizeMax < x0 + inst.constN + inst.traitDelta) = false` by 5-step safety:
  have hov2 : decide (usizeMax < x0 + inst.constN + inst.traitDelta) = false := by
    cases h_b2 : decide (usizeMax < x0 + inst.constN + inst.traitDelta) with
    | false => rfl
    | true =>
      have h_safe5 := (h_ens { init := s0, steps := 5 } (h_arg 5)).1.2
      let s1 : MirState := { s0 with
        locals := updateLocal s0.locals 2 (some (.tupleUsizeBool (x0 + inst.constN) false))
        stmtIdx := 1 }
      let s2 : MirState := { s1 with block := 1, stmtIdx := 0 }
      let s3 : MirState := { s2 with
        locals := updateLocal s2.locals 3 (some (.usize (x0 + inst.constN)))
        stmtIdx := 1 }
      let s4 : MirState := { s3 with
        locals := updateLocal s3.locals 4
          (some (.tupleUsizeBool (x0 + inst.constN + inst.traitDelta) true))
        stmtIdx := 2 }
      have hs0 : MirMachine.step (checkedMonoBody inst) s0 (.step () s1) := by
        change (.step () s1) = evalMirStep (checkedMonoBody inst) s0
        simp [evalMirStep, checkedMonoBody, s0, initStateWithArg1, evalMirStmt,
          evalOperand, evalCheckedBinOp, hov1, s1]
      have hs1 : MirMachine.step (checkedMonoBody inst) s1 (.step () s2) := by
        change (.step () s2) = evalMirStep (checkedMonoBody inst) s1
        simp [evalMirStep, checkedMonoBody, s1, s2, s0, initStateWithArg1,
          evalMirTerminator, updateLocal]
      have hs2 : MirMachine.step (checkedMonoBody inst) s2 (.step () s3) := by
        change (.step () s3) = evalMirStep (checkedMonoBody inst) s2
        simp [evalMirStep, checkedMonoBody, s2, s3, s1, s0, initStateWithArg1,
          evalMirStmt, updateLocal]
      have hs3 : MirMachine.step (checkedMonoBody inst) s3 (.step () s4) := by
        change (.step () s4) = evalMirStep (checkedMonoBody inst) s3
        simp [evalMirStep, checkedMonoBody, s3, s4, s2, s1, s0, initStateWithArg1,
          evalMirStmt, evalOperand, updateLocal, evalCheckedBinOp, h_b2]
      have hs4 : MirMachine.step (checkedMonoBody inst) s4 (.failed .contractViolation) := by
        change (.failed .contractViolation) = evalMirStep (checkedMonoBody inst) s4
        simp [evalMirStep, checkedMonoBody, s4, s3, s2,
          evalMirTerminator, updateLocal]
      have h_reach5 : ReachesPrefix MirMachine (checkedMonoBody inst) s0 5 s0
          [(), (), (), ()] (.failed .contractViolation) :=
        .step 4 s0 s1 () [(), (), ()] (.failed .contractViolation) hs0
          (.step 3 s1 s2 () [(), ()] (.failed .contractViolation) hs1
            (.step 2 s2 s3 () [()] (.failed .contractViolation) hs2
              (.step 1 s3 s4 () [] (.failed .contractViolation) hs3
                (.failed 0 s4 .contractViolation hs4))))
      exact False.elim (h_safe5 h_init [(), (), (), ()] (.failed .contractViolation) h_reach5)
  -- Step 3: Construct the 7-step normal termination prefix and extract `checkedPost`:
  let s1 : MirState := { s0 with
    locals := updateLocal s0.locals 2 (some (.tupleUsizeBool (x0 + inst.constN) false))
    stmtIdx := 1 }
  let s2 : MirState := { s1 with block := 1, stmtIdx := 0 }
  let s3 : MirState := { s2 with
    locals := updateLocal s2.locals 3 (some (.usize (x0 + inst.constN)))
    stmtIdx := 1 }
  let s4 : MirState := { s3 with
    locals := updateLocal s3.locals 4
      (some (.tupleUsizeBool (x0 + inst.constN + inst.traitDelta) false))
    stmtIdx := 2 }
  let s5 : MirState := { s4 with block := 2, stmtIdx := 0 }
  let s6 : MirState := { s5 with
    locals := updateLocal s5.locals 0
      (some (.usize (x0 + inst.constN + inst.traitDelta)))
    stmtIdx := 1 }
  have hs0 : MirMachine.step (checkedMonoBody inst) s0 (.step () s1) := by
    change (.step () s1) = evalMirStep (checkedMonoBody inst) s0
    simp [evalMirStep, checkedMonoBody, s0, initStateWithArg1, evalMirStmt,
      evalOperand, evalCheckedBinOp, hov1, s1]
  have hs1 : MirMachine.step (checkedMonoBody inst) s1 (.step () s2) := by
    change (.step () s2) = evalMirStep (checkedMonoBody inst) s1
    simp [evalMirStep, checkedMonoBody, s1, s2, s0, initStateWithArg1,
      evalMirTerminator, updateLocal]
  have hs2 : MirMachine.step (checkedMonoBody inst) s2 (.step () s3) := by
    change (.step () s3) = evalMirStep (checkedMonoBody inst) s2
    simp [evalMirStep, checkedMonoBody, s2, s3, s1, s0, initStateWithArg1,
      evalMirStmt, updateLocal]
  have hs3 : MirMachine.step (checkedMonoBody inst) s3 (.step () s4) := by
    change (.step () s4) = evalMirStep (checkedMonoBody inst) s3
    simp [evalMirStep, checkedMonoBody, s3, s4, s2, s1, s0, initStateWithArg1,
      evalMirStmt, evalOperand, updateLocal, evalCheckedBinOp, hov2]
  have hs4 : MirMachine.step (checkedMonoBody inst) s4 (.step () s5) := by
    change (.step () s5) = evalMirStep (checkedMonoBody inst) s4
    simp [evalMirStep, checkedMonoBody, s4, s5, s3, s2, s1, s0, initStateWithArg1,
      evalMirTerminator, updateLocal]
  have hs5 : MirMachine.step (checkedMonoBody inst) s5 (.step () s6) := by
    change (.step () s6) = evalMirStep (checkedMonoBody inst) s5
    simp [evalMirStep, checkedMonoBody, s5, s6, s4, s3, s2, s1, s0, initStateWithArg1,
      evalMirStmt, updateLocal]
  have hs6 : MirMachine.step (checkedMonoBody inst) s6
      (.terminated (.normal (.usize (x0 + inst.constN + inst.traitDelta)))) := by
    change (.terminated (.normal (.usize (x0 + inst.constN + inst.traitDelta)))) =
      evalMirStep (checkedMonoBody inst) s6
    simp [evalMirStep, checkedMonoBody, s6, s5,
      evalMirTerminator, updateLocal]
  have h_reach7 : ReachesPrefix MirMachine (checkedMonoBody inst) s0 7 s0
      [(), (), (), (), (), ()]
      (.terminated (.normal (.usize (x0 + inst.constN + inst.traitDelta)))) :=
    .step 6 s0 s1 () [(), (), (), (), ()] _ hs0
      (.step 5 s1 s2 () [(), (), (), ()] _ hs1
        (.step 4 s2 s3 () [(), (), ()] _ hs2
          (.step 3 s3 s4 () [(), ()] _ hs3
            (.step 2 s4 s5 () [()] _ hs4
              (.step 1 s5 s6 () [] _ hs5
                (.terminated 0 s6 _ hs6))))))
  have h_post7 := (h_ens { init := s0, steps := 7 } (h_arg 7)).2
    { trace := [(), (), (), (), (), ()]
      outcome := .terminated (.normal (.usize (x0 + inst.constN + inst.traitDelta))) }
    ⟨h_init, h_reach7⟩
    (.usize (x0 + inst.constN + inst.traitDelta))
    x0
    rfl
    rfl
  have h_callee_eq :
      evalCheckedCallee inst (.usize x0) =
        some (.usize (x0 + inst.constN + inst.traitDelta)) := by
    simp [evalCheckedCallee, hov1, hov2]
  exact ⟨h_pme, h_callee_eq, h_post7.2⟩

/-- Operational verification of `clientEntryBody instA1`: proved modularly via
    `evalCheckedCallee_of_ensuresChecked` from `EnsuresChecked instA1`! -/
theorem clientGoodEntryBody_le_spec
    (h_callee_ens : MonoMirLang.sem (checkedUnit instA1) ≤ EnsuresChecked instA1) :
    MirLang.sem (clientEntryBody instA1) ≤
      MirLang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .usize 54) := by
  have h_bridge := evalCheckedCallee_of_ensuresChecked h_callee_ens client_good_arg50_satisfies_pre
  have h_callee50 : evalCheckedCallee instA1 (.usize 50) = some (.usize 54) := h_bridge.2.1
  refine behaviorOf_le_specOn ?_
  rintro ⟨init, steps⟩ ⟨tr, oc⟩ _ ⟨h_init, h_reach⟩
  dsimp at h_init h_reach
  rcases h_init with ⟨hb0, hs0, hloc0, _⟩
  have h_step0 : evalMirStep (clientEntryBody instA1) init =
      .step () { init with
        locals := updateLocal init.locals 0 (some (.usize 54))
        block := 1
        stmtIdx := 0 } := by
    simp [evalMirStep, clientEntryBody, hb0, hs0, evalMirTerminator, evalOperand,
      h_callee50]
  generalize hs1_def :
    ({ init with
      locals := updateLocal init.locals 0 (some (.usize 54))
      block := 1
      stmtIdx := 0 } : MirState) = s1 at h_step0
  have h_step1 : evalMirStep (clientEntryBody instA1) s1 =
      .terminated (.normal (.usize 54)) := by
    rw [← hs1_def]
    simp [evalMirStep, clientEntryBody, evalMirTerminator, updateLocal]
  cases h_reach with
  | zero =>
    exact ⟨True.intro, fun _ hterm => by cases hterm⟩
  | choice _ _ _ _ _ _ _ hst =>
    change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
  | emptyChoice _ _ _ _ hst =>
    change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
  | terminated _ _ _ hst =>
    change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
  | failed _ _ _ hst =>
    change _ = evalMirStep _ _ at hst; rw [h_step0] at hst; cases hst
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, h_step0.symm⟩)
  | step _ _ _ _ _ _ hst0 hr1 =>
    change _ = evalMirStep _ _ at hst0; rw [h_step0] at hst0; cases hst0
    cases hr1 with
    | zero =>
      exact ⟨True.intro, fun _ hterm => by cases hterm⟩
    | step _ _ _ _ _ _ hst1 =>
      change _ = evalMirStep _ _ at hst1; rw [h_step1] at hst1; cases hst1
    | choice _ _ _ _ _ _ _ hst1 =>
      change _ = evalMirStep _ _ at hst1; rw [h_step1] at hst1; cases hst1
    | emptyChoice _ _ _ _ hst1 =>
      change _ = evalMirStep _ _ at hst1; rw [h_step1] at hst1; cases hst1
    | failed _ _ _ hst1 =>
      change _ = evalMirStep _ _ at hst1; rw [h_step1] at hst1; cases hst1
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, h_step1.symm⟩)
    | terminated _ _ _ hst1 =>
      change _ = evalMirStep _ _ at hst1; rw [h_step1] at hst1; cases hst1
      refine ⟨True.intro, ?_⟩
      intro ret hterm
      cases hterm
      rfl

/-- Concrete `VerificationResultOn` for `client_good::entry` calling
    `checked::<TypeA, 1>(50)`:
    `client_good` discharges the callee's PME and `EnsuresChecked instA1`
    obligations modularly via `client_good_instantiation_verified_modularly`
    (without re-proving `checkedMonoBody`), and obtains a complete
    `VerificationResultOn` for `clientEntryUnit instA1`! -/
theorem client_good_entry_verified :
    (MonoRustcCompiler.compile (clientEntryUnit instA1)).defined ∧
    VerificationResultOn MonoRustcCompiler defaultTrustPolicy
      clientGoodTcb
      (clientEntryUnit instA1)
      (fun _ => True)
      [EnsuresClientGoodEntry] := by
  have h_callee := client_good_instantiation_verified_modularly
  have h_callee_pme : (MonoRustcCompiler.compile (checkedUnit instA1)).defined :=
    h_callee.1
  refine ⟨h_callee_pme, ⟨True.intro, True.intro, True.intro⟩, ?_⟩
  intro ⟨h_sound_callee, h_sound_entry, _⟩
  have h_callee_ver :
      MonoRustcCompiler.Verified (checkedUnit instA1) (EnsuresChecked instA1) :=
    (h_callee.2.2 ⟨h_sound_callee, True.intro⟩).2.1
  have h_mono_src : MonoMirLang.sem (clientEntryUnit instA1) ≤ EnsuresClientGoodEntry :=
    monoMirSem_le_specOn h_callee_pme (clientGoodEntryBody_le_spec h_callee_ver.1)
  have h_ver : MonoRustcCompiler.Verified (clientEntryUnit instA1) EnsuresClientGoodEntry :=
    Compiler.SoundOn.verify h_sound_entry h_mono_src
  exact Compiler.Verified.with_wellFormedOn h_ver
    (specOn_le_wellFormedOn (L := MonoMirLang) (fun _ => True) _)
    h_sound_entry.1

/-!
### 7.2 Negative Control 1 (`client_bad_pme`): PME Violation (`N > T::LIMIT`)
In crate `client_bad_pme`, `TypeB` implements `Bound` with `LIMIT = 0` and
`delta() = 0` (`boundTraitContract` holds!), and calls `checked::<TypeB, 1>(50)`.
Because `1 ≤ 0` is false, `rustc` aborts compilation with a PME.
-/

def instB1 : CheckedInstCtx where
  tySize := 8
  tyAlign := 8
  constN := 1
  traitLimit := 0
  traitDelta := 0

/-- `TypeB` is a completely valid implementation of `Bound` (`LIB-07` holds). -/
theorem instB1_satisfies_boundTraitContract : boundTraitContract instB1 := by
  dsimp [boundTraitContract, layoutValid, instB1, isizeMax]
  omega

/-- However, `instB1` violates the explicit PME bound `N ≤ T::LIMIT` (`1 ≤ 0`). -/
theorem instB1_violates_noPmePre : ¬ checkedNoPmePre instB1 := by
  dsimp [checkedNoPmePre, instB1]
  omega

/-- Negative Control 1a: `rustc` compilation of `checked::<TypeB, 1>` fails with
    a Post-Monomorphization Error (`¬ defined`). -/
theorem client_bad_pme_fails_to_compile :
    ¬ (MonoRustcCompiler.compile (checkedUnit instB1)).defined := by
  intro ⟨_, h_le⟩
  exact instB1_violates_noPmePre h_le

/-- Negative Control 1b: Even at valid runtime argument `x = 50`,
    `checked::<TypeB, 1>` cannot satisfy `MonoRustcCompiler.Verified` on
    `checkedArgPre instB1`. -/
theorem client_bad_pme_cannot_be_verified :
    ¬ MonoRustcCompiler.Verified (checkedUnit instB1)
        (MonoMirLang.WellFormedOn (checkedArgPre instB1)) := by
  intro h_ver
  have h_pre50 : checkedArgPre instB1 { init := initStateWithArg1 50, steps := 0 } := by
    intro x0 hloc1
    simp [initStateWithArg1] at hloc1
    cases hloc1
    omega
  have h_def := (h_ver.1 { init := initStateWithArg1 50, steps := 0 } h_pre50).1.1
  exact client_bad_pme_fails_to_compile h_def

/-- Negative Control 1c: Downstream caller `client_bad::entry`
    (`clientEntryUnit instB1`, which calls `checked::<TypeB, 1>(50)`) fails
    transitive monomorphization with a PME and cannot satisfy
    `MonoRustcCompiler.Verified`! -/
theorem client_bad_entry_fails_to_compile_and_verify :
    ¬ (MonoRustcCompiler.compile (clientEntryUnit instB1)).defined ∧
    ¬ MonoRustcCompiler.Verified (clientEntryUnit instB1)
        MonoMirLang.WellFormed := by
  refine ⟨client_bad_pme_fails_to_compile, ?_⟩
  intro h_ver
  have h_def := (h_ver.1 { init := dummyMirState, steps := 0 } True.intro).1.1
  exact client_bad_pme_fails_to_compile h_def

/-!
### 7.3 Negative Control 2 (`client_bad_trait`): `LIB-07` Trait Obligation Violation
In crate `client_bad_trait`, `RogueType` implements `Bound` with `LIMIT = 10`
(so `N = 1 ≤ 10` **passes** the compile-time PME check!) but defines
`delta() = usizeMax` (violating `LIB-07` `delta() ≤ LIMIT`).
At runtime, calling `checked::<RogueType, 1>(50)` overflows in `bb1` and fails
with `.contractViolation` at step 5!
-/

def instRogue : CheckedInstCtx where
  tySize := 8
  tyAlign := 8
  constN := 1
  traitLimit := 10
  traitDelta := usizeMax

/-- `checked::<RogueType, 1>` passes the compile-time PME check (`1 ≤ 10`)! -/
theorem instRogue_compiles_without_pme :
    (MonoRustcCompiler.compile (checkedUnit instRogue)).defined := by
  dsimp [MonoRustcCompiler, rustcCompileMono, checkedUnit, checkedPmeOk,
    layoutValid, instRogue, isizeMax]
  omega

/-- However, `RogueType` violates the `LIB-07` semantic trait obligation
    `boundTraitContract`. -/
theorem instRogue_violates_boundTraitContract : ¬ boundTraitContract instRogue := by
  dsimp [boundTraitContract, layoutValid, instRogue, usizeMax, isizeMax]
  omega

/-- Negative Control 2: Despite compiling without a PME and being called with a
    valid runtime argument `x = 50` (`50 ≤ 1000`), `checked::<RogueType, 1>(50)`
    triggers an arithmetic overflow failure at step 5, refuting
    `MonoMirLang.WellFormedOn (checkedArgPre instRogue)`. -/
theorem client_bad_trait_fails_at_runtime :
    ¬ (MonoMirLang.sem (checkedUnit instRogue) ≤
        MonoMirLang.WellFormedOn (checkedArgPre instRogue)) := by
  intro h_wf
  let s0 := initStateWithArg1 50
  have h_pre50 : checkedArgPre instRogue { init := s0, steps := 5 } := by
    intro x0 hloc1
    simp [s0, initStateWithArg1] at hloc1
    cases hloc1
    omega
  have h_def := (h_wf { init := s0, steps := 5 } h_pre50).1.2
  have h_init : initMirState (checkedMonoBody instRogue) s0 :=
    initMirState_checked_arg1 instRogue 50
  -- Construct the 5-step execution prefix from `s0` that fails with `.contractViolation`:
  let s1 : MirState := { s0 with
    locals := updateLocal s0.locals 2 (some (.tupleUsizeBool 51 false))
    stmtIdx := 1 }
  let s2 : MirState := { s1 with block := 1, stmtIdx := 0 }
  let s3 : MirState := { s2 with
    locals := updateLocal s2.locals 3 (some (.usize 51))
    stmtIdx := 1 }
  let s4 : MirState := { s3 with
    locals := updateLocal s3.locals 4 (some (.tupleUsizeBool (51 + usizeMax) true))
    stmtIdx := 2 }
  have h0 : MirMachine.step (checkedMonoBody instRogue) s0 (.step () s1) := by rfl
  have h1 : MirMachine.step (checkedMonoBody instRogue) s1 (.step () s2) := by rfl
  have h2 : MirMachine.step (checkedMonoBody instRogue) s2 (.step () s3) := by rfl
  have h3 : MirMachine.step (checkedMonoBody instRogue) s3 (.step () s4) := by rfl
  have h4 : MirMachine.step (checkedMonoBody instRogue) s4 (.failed .contractViolation) := by rfl
  have h_reach : ReachesPrefix MirMachine (checkedMonoBody instRogue) s0 5 s0
      [(), (), (), ()] (.failed .contractViolation) :=
    .step 4 s0 s1 () [(), (), ()] (.failed .contractViolation) h0
      (.step 3 s1 s2 () [(), ()] (.failed .contractViolation) h1
        (.step 2 s2 s3 () [()] (.failed .contractViolation) h2
          (.step 1 s3 s4 () [] (.failed .contractViolation) h3
            (.failed 0 s4 .contractViolation h4))))
  exact h_def h_init [(), (), (), ()] (.failed .contractViolation) h_reach

/-!
### 7.4 Negative Control 3 (`client_bad_arg`): Runtime Argument Precondition Violation
Even for `instA1` (`checked::<TypeA, 1>`, where both `boundTraitContract` and
`checkedNoPmePre` hold), calling `checked::<TypeA, 1>(usizeMax)` (violating
`checkedArgPre` `x ≤ 1000`) overflows in `bb0` at step 2 and refutes
unconditional `MonoMirLang.WellFormed`.
-/

theorem client_bad_arg_refutes_unconditional_wellFormed :
    ¬ (MonoMirLang.sem (checkedUnit instA1) ≤ MonoMirLang.WellFormed) := by
  intro h_wf
  let s0 := initStateWithArg1 usizeMax
  have h_def := (h_wf { init := s0, steps := 2 } True.intro).1.2
  have h_init : initMirState (checkedMonoBody instA1) s0 :=
    initMirState_checked_arg1 instA1 usizeMax
  let s1 : MirState := { s0 with
    locals := updateLocal s0.locals 2 (some (.tupleUsizeBool (usizeMax + 1) true))
    stmtIdx := 1 }
  have h0 : MirMachine.step (checkedMonoBody instA1) s0 (.step () s1) := by rfl
  have h1 : MirMachine.step (checkedMonoBody instA1) s1 (.failed .contractViolation) := by rfl
  have h_reach : ReachesPrefix MirMachine (checkedMonoBody instA1) s0 2 s0
      [()] (.failed .contractViolation) :=
    .step 1 s0 s1 () [] (.failed .contractViolation) h0
      (.failed 0 s1 .contractViolation h1)
  exact h_def h_init [()] (.failed .contractViolation) h_reach

end PolymorphicVerification
