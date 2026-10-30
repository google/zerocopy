-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Probe 2: Execution Cost, Stack Depth, Constant-Time 2-Safety, and Crypto Lift

This standalone Lean `v4.34.1` probe embeds Anneal's small-step prefix behavior
framework (`Trusted.Refinement`, `Trusted.StepResult`, `Anneal.Refinement`,
`Anneal.StepResult`, and `Anneal.FunctionalTranslation` core) and demonstrates
how it supports:

1. **Structured Step Observations (`StepObs`)**: Instantiating the `Obs`
   parameter of `SmallStepMachine Prog State Obs Val` with per-step instruction
   cost (`cost : Nat`), stack-frame delta (`stackDelta : Int`), and side-channel
   leakage observations (`leak : LeakEvent`, matching `VCV-io`'s
   `ObservationOracle.lean` / `Leakage.lean`).
2. **Unary Worst-Case Execution Cost and Peak Stack Depth (`A-BEH-04`,
   `A-BEH-05`, `A-BEH-06`)**: Proving concrete upper bounds on `totalCost` and
   `peakStackDepth` together with functional correctness in a single
   `Language.SpecOn` refinement judgment, plus a cost-scaling refinement bridge
   for compiler passes with per-step expansion factor `≤ k`.
3. **Relational 2-Safety Constant-Time Noninterference (`A-BEH-12`)**: Defining
   `ConstantTime2Safety` over `BehaviorOf M p` (requiring equal `leakageTrace`
   and `totalCost` across any two public-equivalent initial states) and proving
   both a positive theorem for a branchless constant-time select program
   (`ctSelectProg` / `ctSelectXorBody`) and a negative canary theorem
   (`E-EVAL-02`) rejecting an isochronous secret-branching select program
   (`branchSelectProg` / `secretBranchBody`).
4. **Lifting Verified `FuncLang` Programs into `VCV-io` / `SampCert`
   (`A-BEH-14`, `A-BEH-18`)**: Proving that Anneal's `AeneasRes` (`.ok`,
   `.fail`, `.inapplicable`) lifts directly into `VCV-io`'s `RustOracleComp`
   stack (`ExceptT Error (OptionT M)`) and collapses to a total monadic lift
   whenever Anneal's `SafeAndReturns` theorem holds
   (`liftAeneasToOracle_sound` / `liftAeneasRes_eq_ok_of_safeAndReturns`).
-/

namespace Trusted

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partiality / undefined-behavior container (`B ∪ {UB}`). -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v} [Preorder B₁]
    [Preorder B₂] {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp h₂
  rcases hp h₂ with ⟨h₁, hle⟩
  exact ⟨h₁, hf hle⟩

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

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
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State)
      (branches : State → Prop) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State)
      (branches : State → Prop) :
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

end Trusted

namespace Anneal

open Trusted

def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

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

theorem behaviorOf_le_wellFormed_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} :
    BehaviorOf M p ≤ (M.toLanguage).WellFormed ↔
      ∀ init steps tr out,
        M.initState p init →
        ReachesPrefix M p init steps init tr out →
        out.isSafe := by
  constructor
  · intro h init steps tr out hinit hreach
    have hdef := (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mp h
      { init := init, steps := steps }
    exact hdef hinit tr out hreach
  · intro h
    refine (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mpr ?_
    intro q hinit tr out hreach
    exact h q.init q.steps tr out hinit hreach

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

end Anneal

namespace Anneal.CostCtProbe

open Trusted
open Anneal

/-!
## 1. Observation Algebra: Cost, Stack Depth, and Side-Channel Leakage
-/

/-- Side-channel leakage observation emitted by a single transition step,
capturing the standard constant-time leakage model (control-flow branch
conditions, secret-dependent memory addresses, and variable-time hardware
instructions such as division). -/
inductive LeakEvent where
  | none
  | branch (cond : Bool)
  | memAccess (addr : Nat)
  | varTimeDiv (divisor : Nat)
  deriving DecidableEq, Repr

/-- Structured step observation instantiating `Obs` in `SmallStepMachine`. -/
structure StepObs where
  cost       : Nat
  stackDelta : Int
  leak       : LeakEvent
  deriving DecidableEq, Repr

/-- Total execution cost accumulated along a finite observation trace. -/
def totalCost : List StepObs → Nat
  | [] => 0
  | e :: es => e.cost + totalCost es

/-- Current stack depth after executing a trace from initial depth `cur`. -/
def curStackDepth (cur : Int) : List StepObs → Int
  | [] => cur
  | e :: es => curStackDepth (cur + e.stackDelta) es

/-- High-water-mark (peak) stack depth reached along a finite trace. -/
def peakStackDepthAux (cur peak : Int) : List StepObs → Int
  | [] => peak
  | e :: es =>
      let next := cur + e.stackDelta
      let nextPeak := if peak < next then next else peak
      peakStackDepthAux next nextPeak es

def peakStackDepth (init : Int) (tr : List StepObs) : Int :=
  peakStackDepthAux init init tr

/-- Extracted sequence of side-channel leakage events along a trace. -/
def leakageTrace : List StepObs → List LeakEvent
  | [] => []
  | e :: es => e.leak :: leakageTrace es

/-!
## 2. Small-Step Machine with Stack Frames and Constant-Time vs. Leaky Select
-/

inductive CostCtInstr where
  | pushFrame (bytes : Nat)
  | popFrame (bytes : Nat)
  | ctSelect
  | branchSelect
  | secretMemLoad
  deriving DecidableEq, Repr

abbrev CostCtProg := List CostCtInstr

structure CostCtState where
  pc         : Nat
  pubInput   : Nat
  secretCond : Bool
  secretA    : Nat
  secretB    : Nat
  acc        : Nat
  deriving DecidableEq, Repr

def costCtStepFn (p : CostCtProg) (st : CostCtState) :
    StepResult CostCtState StepObs Nat :=
  match p[st.pc]? with
  | none => .terminated (.normal st.acc)
  | some (.pushFrame bytes) =>
      .step
        { cost := 1, stackDelta := Int.ofNat bytes, leak := .none }
        { st with pc := st.pc + 1 }
  | some (.popFrame bytes) =>
      .step
        { cost := 1, stackDelta := -Int.ofNat bytes, leak := .none }
        { st with pc := st.pc + 1 }
  | some .ctSelect =>
      .step
        { cost := 1, stackDelta := 0, leak := .none }
        { st with
          pc  := st.pc + 1
          acc := if st.secretCond then st.secretA else st.secretB }
  | some .branchSelect =>
      .step
        { cost := 1, stackDelta := 0, leak := .branch st.secretCond }
        { st with
          pc  := st.pc + 1
          acc := if st.secretCond then st.secretA else st.secretB }
  | some .secretMemLoad =>
      .step
        { cost := 1, stackDelta := 0, leak := .memAccess st.secretA }
        { st with pc := st.pc + 1, acc := st.secretA }

def costCtMachine : SmallStepMachine CostCtProg CostCtState StepObs Nat where
  initState := fun _ st => st.pc = 0
  step := fun p st r => r = costCtStepFn p st

abbrev CostCtLang : Language := costCtMachine.toLanguage

/-!
## 3. Totality, Non-Vacuity, and Universal Well-Formedness
-/

theorem costCtMachine_total : TotalStep costCtMachine := by
  intro p s
  exact ⟨costCtStepFn p s, rfl⟩

theorem costCtMachine_inhabitedDemonic : InhabitedDemonic costCtMachine := by
  intro p st kind branches hStep
  simp only [costCtMachine, costCtStepFn] at hStep
  cases hInstr : p[st.pc]? with
  | none => rw [hInstr] at hStep; exact nomatch hStep
  | some instr =>
    rw [hInstr] at hStep
    cases instr <;> exact nomatch hStep

theorem costCtMachine_reaches_safe
    (p : CostCtProg) (init : CostCtState) (steps : Nat)
    (st : CostCtState) (tr : List StepObs) (out : PrefixOutcome Nat)
    (hReach : ReachesPrefix costCtMachine p init steps st tr out) :
    out.isSafe := by
  induction hReach with
  | zero => exact trivial
  | step _ _ _ _ _ _ _ _ ih => exact ih
  | choice _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | emptyChoice _ kind s branches hStep hEmpty =>
    exfalso
    exact hEmpty (costCtMachine_inhabitedDemonic p s kind branches hStep)
  | terminated => exact trivial
  | failed _ s err hStep =>
    simp only [costCtMachine, costCtStepFn] at hStep
    cases hInstr : p[s.pc]? with
    | none => rw [hInstr] at hStep; exact nomatch hStep
    | some instr =>
      rw [hInstr] at hStep
      cases instr <;> exact nomatch hStep
  | noStep _ s hNo =>
    exfalso
    exact hNo (costCtMachine_total p s)

theorem costCtMachine_wellFormed (p : CostCtProg) :
    BehaviorOf costCtMachine p ≤ CostCtLang.WellFormed := by
  rw [behaviorOf_le_wellFormed_iff]
  intro init steps tr out _ hReach
  exact costCtMachine_reaches_safe p init steps init tr out hReach

/-- Deterministic characterization of `ReachesPrefix` for `costCtMachine` when
instructions execute via `.step` or `.terminated`. -/
def execSteps (p : CostCtProg) : Nat → CostCtState → List StepObs × PrefixOutcome Nat
  | 0, _ => ([], .running)
  | n + 1, st =>
      match costCtStepFn p st with
      | .step obs st' =>
          let (tr, oc) := execSteps p n st'
          (obs :: tr, oc)
      | .terminated term => ([], .terminated term)
      | .choice _ _ => ([], .stuck)
      | .failed err => ([], .failed err)

theorem reachesPrefix_eq_execSteps
    (p : CostCtProg) (init : CostCtState) (steps : Nat) :
    ∀ (st : CostCtState) (tr : List StepObs) (oc : PrefixOutcome Nat),
      ReachesPrefix costCtMachine p init steps st tr oc →
      (tr, oc) = execSteps p steps st := by
  induction steps with
  | zero =>
    intro st tr oc hReach
    cases hReach with
    | zero => rfl
  | succ n ih =>
    intro st tr oc hReach
    have hSafe : oc.isSafe := costCtMachine_reaches_safe p init (n + 1) st tr oc hReach
    cases hReach with
    | emptyChoice => exact False.elim hSafe
    | failed => exact False.elim hSafe
    | noStep => exact False.elim hSafe
    | choice =>
      rename_i kind s' branches _ hStep _
      exfalso
      cases (costCtMachine_inhabitedDemonic p st kind branches hStep) with
      | intro _ _ =>
        simp only [costCtMachine, costCtStepFn] at hStep
        cases hInstr : p[st.pc]? with
        | none => rw [hInstr] at hStep; exact nomatch hStep
        | some instr => rw [hInstr] at hStep; cases instr <;> exact nomatch hStep
    | terminated =>
      rename_i term hStep
      simp only [costCtMachine] at hStep
      unfold execSteps
      rw [← hStep]
    | step =>
      rename_i st' obs tr' hStep hRest
      simp only [costCtMachine] at hStep
      unfold execSteps
      rw [← hStep]
      dsimp only
      have ihEq := ih st' tr' oc hRest
      rw [← ihEq]

/-!
## 4. Positive Theorem 1: Worst-Case Cost & Stack Depth Bound (`A-BEH-04`–`06`)

We verify a 3-instruction subroutine (`boundedStackSelectProg`) that:
1. Allocates a 16-byte stack frame (`pushFrame 16`),
2. Computes a branchless select (`ctSelect`),
3. Deallocates the 16-byte stack frame (`popFrame 16`), and
4. Returns (`terminated (.normal ...)`).

We prove via `Language.SpecOn` that at step budget `4`, every execution:
- Incurs `totalCost out.trace ≤ 3`,
- Maintains `peakStackDepth 0 out.trace ≤ 16` and returns to
  `curStackDepth 0 = 0`,
- Emits an all-`.none` leakage trace, and
- Terminates normally with
  `if init.secretCond then init.secretA else init.secretB`.
-/

def boundedStackSelectProg : CostCtProg :=
  [.pushFrame 16, .ctSelect, .popFrame 16]

theorem execSteps_boundedStackSelectProg (pub sA sB acc : Nat) (sCond : Bool) :
    execSteps boundedStackSelectProg 4
      { pc := 0, pubInput := pub, secretCond := sCond,
        secretA := sA, secretB := sB, acc := acc } =
    ([ { cost := 1, stackDelta := 16, leak := .none },
       { cost := 1, stackDelta := 0, leak := .none },
       { cost := 1, stackDelta := -16, leak := .none } ],
     .terminated (.normal (if sCond then sA else sB))) := rfl

theorem boundedStackSelectProg_cost_and_stack_bound :
    BehaviorOf costCtMachine boundedStackSelectProg ≤
      CostCtLang.SpecOn
        (fun q => q.init.pc = 0 ∧ q.steps = 4)
        (fun q out =>
          totalCost out.trace ≤ 3 ∧
          peakStackDepth 0 out.trace ≤ 16 ∧
          curStackDepth 0 out.trace = 0 ∧
          out.outcome = .terminated (.normal
            (if q.init.secretCond then q.init.secretA else q.init.secretB))) := by
  apply behaviorOf_le_specOn
  rintro ⟨⟨pc, pub, sCond, sA, sB, acc⟩, steps⟩ ⟨tr, oc⟩ ⟨hPc, hSteps⟩ ⟨hInit, hReach⟩
  dsimp at hPc hSteps hInit hReach ⊢
  subst hPc hSteps
  have hSafe : oc.isSafe :=
    costCtMachine_reaches_safe boundedStackSelectProg _ 4 _ tr oc hReach
  refine ⟨hSafe, ?_⟩
  have hExec := reachesPrefix_eq_execSteps boundedStackSelectProg _ 4 _ tr oc hReach
  rw [execSteps_boundedStackSelectProg] at hExec
  injection hExec with hTr hOc
  subst hTr hOc
  refine ⟨by decide, by decide, rfl, rfl⟩

/-!
## 5. Positive Theorem 2: Compiler Cost-Scaling Bridge (`A-BEH-06`)

When a compiler pass translates a source program with cost bound `B` into a
target trace where each source step expands to at most `k` target cost units,
any target trace `tr_tgt` linked to a source trace `tr_src` by
`totalCost tr_tgt ≤ k * totalCost tr_src` satisfies `totalCost tr_tgt ≤ k * B`.
-/

theorem compiler_cost_scaling_bound
    (k B : Nat) (tr_src tr_tgt : List StepObs)
    (hScale : totalCost tr_tgt ≤ k * totalCost tr_src)
    (hSrcBound : totalCost tr_src ≤ B) :
    totalCost tr_tgt ≤ k * B :=
  Nat.le_trans hScale (Nat.mul_le_mul_left k hSrcBound)

/-!
## 6. Relational 2-Safety Constant-Time Noninterference (`A-BEH-12`)

Constant-time security is a **2-safety hyperproperty**: for any two initial
states `s₁` and `s₂` that agree on public inputs (`PubEquiv s₁ s₂`) and any step
budget `steps`, both executions are safe and every pair of reachable prefix
outputs `out₁` and `out₂` produces identical side-channel leakage traces
(`leakageTrace out₁.trace = leakageTrace out₂.trace`) and identical instruction
costs (`totalCost out₁.trace = totalCost out₂.trace`).

This matches `VCV-io`'s `TraceNoninterference`
(`ProgramLogic/Relational/Leakage.lean:56-60`) specialized to Anneal's
small-step `BehaviorOf M p`.
-/

def PubEquiv (s₁ s₂ : CostCtState) : Prop :=
  s₁.pc = s₂.pc ∧ s₁.pubInput = s₂.pubInput

def ConstantTime2Safety
    (M : SmallStepMachine CostCtProg CostCtState StepObs Nat)
    (p : CostCtProg) : Prop :=
  ∀ (s₁ s₂ : CostCtState) (steps : Nat),
    M.initState p s₁ →
    M.initState p s₂ →
    PubEquiv s₁ s₂ →
    ∃ (hDef₁ : (BehaviorOf M p ⟨s₁, steps⟩).defined)
      (hDef₂ : (BehaviorOf M p ⟨s₂, steps⟩).defined),
      ∀ (out₁ out₂ : ExecOut StepObs Nat),
        (BehaviorOf M p ⟨s₁, steps⟩).val hDef₁ out₁ →
        (BehaviorOf M p ⟨s₂, steps⟩).val hDef₂ out₂ →
        leakageTrace out₁.trace = leakageTrace out₂.trace ∧
        totalCost out₁.trace = totalCost out₂.trace

/-- Branchless constant-time select program (`[.ctSelect]`). -/
def ctSelectProg : CostCtProg := [.ctSelect]

/-- Alias for `ctSelectProg` representing a branchless bitwise select body. -/
abbrev ctSelectXorBody : CostCtProg := ctSelectProg

/-- **Positive Theorem 3 (`A-BEH-12`):** `ctSelectProg` is constant-time
(`ConstantTime2Safety costCtMachine ctSelectProg`) across all step budgets
`steps : Nat` and all secret inputs `(secretCond, secretA, secretB)`. -/
theorem ctSelectProg_is_constant_time :
    ConstantTime2Safety costCtMachine ctSelectProg := by
  intro s₁ s₂ steps hInit₁ hInit₂ _
  have hDef₁ : (BehaviorOf costCtMachine ctSelectProg ⟨s₁, steps⟩).defined := by
    intro _ tr out hReach
    exact costCtMachine_reaches_safe ctSelectProg s₁ steps s₁ tr out hReach
  have hDef₂ : (BehaviorOf costCtMachine ctSelectProg ⟨s₂, steps⟩).defined := by
    intro _ tr out hReach
    exact costCtMachine_reaches_safe ctSelectProg s₂ steps s₂ tr out hReach
  refine ⟨hDef₁, hDef₂, ?_⟩
  rintro ⟨tr₁, oc₁⟩ ⟨tr₂, oc₂⟩ ⟨_, hReach₁⟩ ⟨_, hReach₂⟩
  have hPc₁ : s₁.pc = 0 := hInit₁
  have hPc₂ : s₂.pc = 0 := hInit₂
  have hExec₁ := reachesPrefix_eq_execSteps ctSelectProg s₁ steps s₁ tr₁ oc₁ hReach₁
  have hExec₂ := reachesPrefix_eq_execSteps ctSelectProg s₂ steps s₂ tr₂ oc₂ hReach₂
  cases steps with
  | zero =>
    unfold execSteps at hExec₁ hExec₂
    injection hExec₁ with hTr₁ _
    injection hExec₂ with hTr₂ _
    subst hTr₁ hTr₂
    exact ⟨rfl, rfl⟩
  | succ n =>
    cases n with
    | zero =>
      unfold execSteps costCtStepFn ctSelectProg at hExec₁ hExec₂
      simp only [hPc₁, hPc₂] at hExec₁ hExec₂
      dsimp at hExec₁ hExec₂
      injection hExec₁ with hTr₁ _
      injection hExec₂ with hTr₂ _
      subst hTr₁ hTr₂
      exact ⟨rfl, rfl⟩
    | succ m =>
      unfold execSteps costCtStepFn ctSelectProg at hExec₁ hExec₂
      simp only [hPc₁, hPc₂] at hExec₁ hExec₂
      dsimp at hExec₁ hExec₂
      injection hExec₁ with hTr₁ _
      injection hExec₂ with hTr₂ _
      subst hTr₁ hTr₂
      exact ⟨rfl, rfl⟩

/-- Alias theorem for `ctSelectProg_is_constant_time` under the
`ctSelectXorBody` name. -/
theorem ctSelectXorBody_is_constant_time :
    ConstantTime2Safety costCtMachine ctSelectXorBody :=
  ctSelectProg_is_constant_time

/-!
## 7. Negative Canary Theorem (`E-EVAL-02`): Secret Branch Rejected

We now show that `branchSelectProg := [.branchSelect]`—even though it executes
in the exact same number of steps (`1`), incurs the exact same instruction cost
(`totalCost = 1`), uses the exact same stack depth (`0`), and returns the exact
same functional result as `ctSelectProg`—is **rejected** by
`ConstantTime2Safety` because its observation trace leaks `.branch secretCond`.
-/

def branchSelectProg : CostCtProg := [.branchSelect]

/-- Alias for `branchSelectProg` representing an isochronous secret-branching
body. -/
abbrev secretBranchBody : CostCtProg := branchSelectProg

theorem branchSelectProg_not_constant_time :
    ¬ ConstantTime2Safety costCtMachine branchSelectProg := by
  intro hCT
  let sTrue : CostCtState :=
    { pc := 0, pubInput := 0, secretCond := true, secretA := 10, secretB := 20, acc := 0 }
  let sFalse : CostCtState :=
    { pc := 0, pubInput := 0, secretCond := false, secretA := 10, secretB := 20, acc := 0 }
  have hInitTrue : costCtMachine.initState branchSelectProg sTrue := rfl
  have hInitFalse : costCtMachine.initState branchSelectProg sFalse := rfl
  have hPub : PubEquiv sTrue sFalse := ⟨rfl, rfl⟩
  rcases hCT sTrue sFalse 1 hInitTrue hInitFalse hPub with ⟨hDef₁, hDef₂, hRel⟩
  let obsTrue : StepObs := { cost := 1, stackDelta := 0, leak := .branch true }
  let obsFalse : StepObs := { cost := 1, stackDelta := 0, leak := .branch false }
  let outTrue : ExecOut StepObs Nat := { trace := [obsTrue], outcome := .running }
  let outFalse : ExecOut StepObs Nat := { trace := [obsFalse], outcome := .running }
  have hStepTrue : costCtMachine.step branchSelectProg sTrue
      (.step obsTrue { sTrue with pc := 1, acc := 10 }) := rfl
  have hStepFalse : costCtMachine.step branchSelectProg sFalse
      (.step obsFalse { sFalse with pc := 1, acc := 20 }) := rfl
  have hReachTrue : ReachesPrefix costCtMachine branchSelectProg sTrue 1 sTrue
      outTrue.trace outTrue.outcome :=
    ReachesPrefix.step 0 sTrue { sTrue with pc := 1, acc := 10 } obsTrue [] .running
      hStepTrue (ReachesPrefix.zero _)
  have hReachFalse : ReachesPrefix costCtMachine branchSelectProg sFalse 1 sFalse
      outFalse.trace outFalse.outcome :=
    ReachesPrefix.step 0 sFalse { sFalse with pc := 1, acc := 20 } obsFalse [] .running
      hStepFalse (ReachesPrefix.zero _)
  have hLeakEq := (hRel outTrue outFalse ⟨hInitTrue, hReachTrue⟩ ⟨hInitFalse, hReachFalse⟩).1
  change [LeakEvent.branch true] = [LeakEvent.branch false] at hLeakEq
  injection hLeakEq with hHead
  injection hHead with hBool
  exact nomatch hBool

/-- Alias theorem for `branchSelectProg_not_constant_time` under the
`secretBranchBody` name. -/
theorem secretBranchBody_not_constant_time :
    ¬ ConstantTime2Safety costCtMachine secretBranchBody :=
  branchSelectProg_not_constant_time

/-!
## 8. Lifting `FuncLang` Programs into `VCV-io`/`SampCert` (`A-BEH-14`, `18`)

In `VCV-io/Interop/Rust/Common.lean:75-76`, the monadic target for verified Rust
code is:
```lean
abbrev RustOracleComp (spec : OracleSpec ι) (α : Type) : Type :=
  ExceptT Error (OptionT (OracleComp spec)) α
```
where `ExceptT Error (OptionT M) α` is isomorphic to
`M (Option (Except Error α))`:
- `.ok v` lifts to `pure (some (.ok v))`,
- `.fail` lifts to `pure (some (.error err))`, and
- `.inapplicable` (or divergence `.div` in Aeneas) lifts to `pure none`.

We embed Anneal's `AeneasRes Val` and `FuncLang` / `π_func` from
`theory/Anneal/FunctionalTranslation.lean:73-120` and prove that `AeneasRes Val`
embeds directly into `Option (Except Unit Val)` (the carrier of
`RustOracleComp`), and that whenever Anneal's `SafeAndReturns` holds
(`f s = .ok (g s)`), the lift reduces definitionally to the total pure embedding
`some (.ok (g s))`!
-/

/-- Result of plan-guided symbolic evaluation
(`Anneal.FunctionalTranslation`). -/
inductive AeneasRes (Val : Type) where
  | ok (v : Val)
  | inapplicable
  | fail
  deriving DecidableEq, Repr

/-- Runtime scalar or reference value in `MirLang` (`Trusted.MirVal`). -/
inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (val : Nat) (overflow : Bool)
  deriving DecidableEq, Repr

/-- Minimal instantaneous execution state of a `MirBody`
(`Trusted.MirState`). -/
structure MirState where
  locals : Nat → Option MirVal
  block : Nat
  stmtIdx : Nat

/-- Pure functional target language for the Aeneas-inspired translation
(`Anneal.FunctionalTranslation.FuncLang`). -/
def FuncLang : Language where
  Prog := MirState → AeneasRes MirVal
  Query := MirState
  Out := MirVal
  sem p init := {
    defined := p init ≠ .fail
    val := fun _ v => p init = .ok v
  }

/-- Small-step MIR language behavior carrier over `ExecQuery MirState` and
`ExecOut Unit MirVal`. -/
abbrev MirBehavior : Type :=
  ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop)

/-- Behavior mapping `π_func : FuncLang.Behavior → MirBehavior` lifting a
big-step functional behavior to small-step prefix behaviors via
`Partial.map`. -/
def π_func (b : FuncLang.Behavior) : MirBehavior :=
  fun q =>
    Partial.map
      (fun (post : MirVal → Prop) (out : ExecOut Unit MirVal) =>
        out.outcome.isSafe ∧
        ∀ ret, out.outcome = .terminated (.normal ret) → post ret)
      (b q.init)

/-- `π_func` is monotone with respect to `Trusted.Preorder` (`≤`). -/
theorem monotone_π_func : Monotone π_func :=
  fun _ _ hb q =>
    Partial.monotone_map
      (by intro _ _ hle out ⟨hsafe, hret⟩; exact ⟨hsafe, fun r hr => hle r (hret r hr)⟩)
      (hb q.init)

/-- Lift Anneal's `AeneasRes α` into the `ExceptT Unit (OptionT M) α` result
carrier `Option (Except Unit α)` used by `VCV-io`'s `RustOracleComp`. -/
def liftAeneasResToRustOracle {α : Type} : AeneasRes α → Option (Except Unit α)
  | .ok v         => some (.ok v)
  | .fail         => some (.error ())
  | .inapplicable => none

/-- When a pure functional model `f : MirState → AeneasRes MirVal` satisfies
Anneal's `SafeAndReturns` on a state `s` (`f s = .ok (g s)`), its
`RustOracleComp` lift is guaranteed never to fail or become inapplicable,
reducing to `some (.ok (g s))`. -/
theorem liftAeneasRes_eq_ok_of_safeAndReturns
    (f : MirState → AeneasRes MirVal)
    (g : MirState → MirVal)
    (s : MirState)
    (hSafe : f s = .ok (g s)) :
    liftAeneasResToRustOracle (f s) = some (.ok (g s)) := by
  rw [hSafe]
  rfl

/-- Alias theorem for `liftAeneasRes_eq_ok_of_safeAndReturns` under the
`liftAeneasToOracle_sound` name. -/
theorem liftAeneasToOracle_sound
    (f : MirState → AeneasRes MirVal)
    (g : MirState → MirVal)
    (s : MirState)
    (hSafe : f s = .ok (g s)) :
    liftAeneasResToRustOracle (f s) = some (.ok (g s)) :=
  liftAeneasRes_eq_ok_of_safeAndReturns f g s hSafe

end Anneal.CostCtProbe

#print axioms Anneal.CostCtProbe.boundedStackSelectProg_cost_and_stack_bound
#print axioms Anneal.CostCtProbe.compiler_cost_scaling_bound
#print axioms Anneal.CostCtProbe.ctSelectProg_is_constant_time
#print axioms Anneal.CostCtProbe.ctSelectXorBody_is_constant_time
#print axioms Anneal.CostCtProbe.branchSelectProg_not_constant_time
#print axioms Anneal.CostCtProbe.secretBranchBody_not_constant_time
#print axioms Anneal.CostCtProbe.liftAeneasRes_eq_ok_of_safeAndReturns
#print axioms Anneal.CostCtProbe.liftAeneasToOracle_sound
