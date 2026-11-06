-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Round 2 Empirical Probe (`R2-04`)

This standalone, zero-`sorry` Lean 4 (`v4.34.1`) module mechanizes and proves
all four Round 2 follow-up investigations identified in `R1-06` and `R1-07`:

1. **`TrackedFuncLang` and Trace-Preserving Adequacy to `MirLang.SpecOn`:**
   Extends `FuncLang` (`MirState → AeneasRes MirVal`) to `TrackedFuncLang`
   (`MirState → AeneasRes (List StepObs × MirVal)`), where `MirMachine` and
   `evalSymWithTracked` emit `[StepObs.step]` per basic-block transition. Proves
   monotone abstraction `Abstracts TrackedFuncLang MirLang π_tracked` and the
   adequacy bridge theorems (`trackedFuncLang_adequacy_specOn` and
   `trackedFuncLang_exact_trace_length_at_steps`) showing that a
   `TrackedFuncLang` proof discharges `MirLang.SpecOn` with the exact
   observation trace `t` (`t.length = steps` at the transition count and
   `.terminated (.normal v)` with trace `t` once `steps > t.length`).

2. **Compositional Loop Invariant + Ranking Measure (`loop_spec_decr_nat`) for
   `MirMachine`:**
   Formalizes a general loop-header invariant and ranking-measure theorem for
   `MirMachine` CFGs (`loop_spec_decr_nat`) by well-founded induction on
   `rank : MirState → Nat`. Proves that if each loop iteration from `bb_head`
   when `guard s = true` takes at most `k` basic-block transitions back to
   `bb_head` while preserving `Inv` and strictly decreasing `rank`, and the exit
   branch when `guard s = false` takes at most `k_exit` transitions to
   `.return v` with `Post v`, then for any `fuel ≥ k * rank s + k_exit`,
   `MirMachine` reaches `.return v` with `Post v` and observation trace length
   `≤ k * rank s + k_exit`, while satisfying fuel-free safety and partial
   correctness across all step budgets. Demonstrates this theorem on a concrete
   `sum_to_n` loop CFG (`k = 3`, `k_exit = 2`, entry = `1`, yielding the exact
   `3 * n + 3` fuel bound and a fuel-free `MirLang.SpecOn` theorem).

3. **Diamond CFG Join-Point Cutpoints & `JCACHED` Side-Condition Subsumption:**
   Formalizes both join-block cutpoint summarization (`diamond_join_cutpoint`,
   collapsing $2^k$ diamond paths into $2k$ linear verification conditions) and
   RefinedRust-style `JCached` side-condition caching
   (`jcache_subsumes_shelvedVC` and `diamond_shelvedVC_cached_once`),
   demonstrating both on a multi-diamond MIR CFG (`twoDiamondBody`).

4. **Relational 2-Safety Constant-Time Bridge (`ConstantTime2Safety`):**
   Proves `evalSymTracked_trace_eq_of_branchAligned` and
   `trackedFuncLang_implies_constantTime2Safety`, showing that if two executions
   of `evalSymWithTracked` from public-equivalent initial states (`PubEquiv`)
   take identical branch decisions at every `switchInt`, their `TrackedFuncLang`
   observation traces and step counts are equal, which lifts via
   `evalSymWithTracked_sound` to `ConstantTime2Safety` on `MirMachine`.
-/

namespace Anneal.R2Probe

/-!
## Section 1: Layer 1A / Layer 1B Foundation and Basic-Block `MirMachine`
-/

namespace Trusted

/-- Reflexive and transitive refinement preorder (`b₁ ≤ b₂`). -/
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

/-- Partially defined behavior carrier representing $B \cup \{\mathsf{UB}\}$. -/
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

abbrev Language.Spec (L : Language) (post : L.Query → L.Out → Prop) :
    L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- Step observation emitted per basic-block jump in `MirMachine`. -/
inductive StepObs where
  | step
  deriving DecidableEq, Repr

inductive ChoiceKind where
  | demonic
  | angelic

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind
  deriving DecidableEq, Repr

inductive FailureKind where
  | ub
  | contractViolation
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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

/-- Runtime MIR scalar value. -/
inductive MirVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  deriving DecidableEq, Repr

/-- MIR operand. -/
inductive Operand where
  | copy (idx : Nat)
  | constVal (v : MirVal)
  deriving DecidableEq, Repr

/-- Binary arithmetic, comparison, and bitwise operators. -/
inductive BinOp where
  | add
  | sub
  | lt
  | le
  | eq
  | bitXor
  deriving DecidableEq, Repr

/-- Sequential statement inside a MIR basic block. -/
inductive Stmt where
  | assignUse (dst : Nat) (op : Operand)
  | assignBinOp (dst : Nat) (op : BinOp) (lhs rhs : Operand)
  | assertLe (lhs rhs : Operand)
  deriving DecidableEq, Repr

/-- Basic-block control-flow terminator. -/
inductive Terminator where
  | return_ (op : Operand)
  | goto (target : Nat)
  | switchInt (discr : Operand) (falseTarget trueTarget : Nat)
  deriving DecidableEq, Repr

/-- Basic block consisting of sequential statements and a terminator. -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator
  deriving DecidableEq, Repr

/-- MIR control-flow graph body. -/
structure MirBody where
  argCount : Nat
  blocks : List BasicBlock
  deriving DecidableEq, Repr

/-- Instantaneous MIR state at basic-block entry `block`. -/
structure MirState where
  locals : Nat → Option MirVal
  block : Nat

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

def evalOperand (locals : Nat → Option MirVal) : Operand → Option MirVal
  | .copy idx => locals idx
  | .constVal v => some v

def evalBinOp (op : BinOp) (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | .usize n1, .usize n2 =>
    match op with
    | .add => some (.usize (n1 + n2))
    | .sub => if n2 ≤ n1 then some (.usize (n1 - n2)) else none
    | .lt => some (.bool (decide (n1 < n2)))
    | .le => some (.bool (decide (n1 ≤ n2)))
    | .eq => some (.bool (decide (n1 = n2)))
    | .bitXor => some (.usize (Nat.xor n1 n2))
  | _, _ => none

def evalStmt (locals : Nat → Option MirVal) (stmt : Stmt) :
    Except FailureKind (Nat → Option MirVal) :=
  match stmt with
  | .assignUse dst op =>
    match evalOperand locals op with
    | some v => .ok (updateLocal locals dst (some v))
    | none => .error .ub
  | .assignBinOp dst op lhs rhs =>
    match evalOperand locals lhs, evalOperand locals rhs with
    | some v1, some v2 =>
      match evalBinOp op v1 v2 with
      | some res => .ok (updateLocal locals dst (some res))
      | none => .error .contractViolation
    | _, _ => .error .ub
  | .assertLe lhs rhs =>
    match evalOperand locals lhs, evalOperand locals rhs with
    | some (.usize n1), some (.usize n2) =>
      if n1 ≤ n2 then .ok locals else .error .contractViolation
    | _, _ => .error .ub

def evalStmts (locals : Nat → Option MirVal) :
    List Stmt → Except FailureKind (Nat → Option MirVal)
  | [] => .ok locals
  | stmt :: rest =>
    match evalStmt locals stmt with
    | .ok locals' => evalStmts locals' rest
    | .error err => .error err

/-- Single basic-block transition step of `MirMachine`.
Every `.goto` and `.switchInt` jump emits `StepObs.step`. -/
def evalMirBlockStep (body : MirBody) (s : MirState) :
    StepResult MirState StepObs MirVal :=
  match body.blocks[s.block]? with
  | none => .failed .ub
  | some bb =>
    match evalStmts s.locals bb.stmts with
    | .error err => .failed err
    | .ok locals' =>
      match bb.terminator with
      | .goto target =>
        .step StepObs.step { locals := locals', block := target }
      | .switchInt discr falseTarget trueTarget =>
        match evalOperand locals' discr with
        | some (.bool false) =>
          .step StepObs.step { locals := locals', block := falseTarget }
        | some (.bool true) =>
          .step StepObs.step { locals := locals', block := trueTarget }
        | _ => .failed .ub
      | .return_ op =>
        match evalOperand locals' op with
        | some v => .terminated (.normal v)
        | none => .failed .ub

def initMirState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧ ∀ i, 1 ≤ i → i ≤ body.argCount → (s.locals i).isSome

def MirMachine : SmallStepMachine MirBody MirState StepObs MirVal where
  initState := initMirState
  step body s r := r = evalMirBlockStep body s

def MirLang : Language := MirMachine.toLanguage

end Trusted

/-!
## Section 2: Task 1 — `TrackedFuncLang` and Adequacy to `MirLang.SpecOn`
-/

namespace Theory

open Trusted

theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v}
    [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp hdef₂
  rcases hp hdef₂ with ⟨hdef₁, hle⟩
  exact ⟨hdef₁, hf hle⟩

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

/-- Executable `steps`-bounded runner for `MirMachine`. -/
def runMir (steps : Nat) (body : MirBody) (s : MirState) :
    List StepObs × PrefixOutcome MirVal :=
  match steps with
  | 0 => ([], .running)
  | n + 1 =>
    match evalMirBlockStep body s with
    | .step obs s' =>
      let (tr, out) := runMir n body s'
      (obs :: tr, out)
    | .terminated term => ([], .terminated term)
    | .failed err => ([], .failed err)
    | .choice _ _ => ([], .stuck)

theorem evalMirBlockStep_ne_choice (body : MirBody) (s : MirState)
    (kind : ChoiceKind) (branches : MirState → Prop) :
    evalMirBlockStep body s ≠ .choice kind branches := by
  intro h
  unfold evalMirBlockStep at h
  repeat (split at h <;> try contradiction)

/-- Exact equivalence between relational `ReachesPrefix` on `MirMachine` and
executable `runMir`. -/
theorem reachesPrefix_iff_runMir (body : MirBody) (init : MirState) :
    ∀ (steps : Nat) (s : MirState) (tr : List StepObs)
      (out : PrefixOutcome MirVal),
      ReachesPrefix MirMachine body init steps s tr out ↔
        runMir steps body s = (tr, out) := by
  intro steps
  induction steps with
  | zero =>
    intro s tr out
    constructor
    · intro h
      cases h
      rfl
    · intro h
      simp only [runMir, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ReachesPrefix.zero s
  | succ n ih =>
    intro s tr out
    constructor
    · intro h
      cases h with
      | step _ _ s' obs tr' _ hstep hrest =>
        have hstep' : StepResult.step obs s' = evalMirBlockStep body s := hstep
        simp only [runMir, ← hstep']
        rw [(ih s' tr' out).mp hrest]
      | choice _ kind _ _ branches _ _ hstep _ _ =>
        have hstep' : StepResult.choice kind branches = evalMirBlockStep body s := hstep
        exact False.elim (evalMirBlockStep_ne_choice body s kind branches hstep'.symm)
      | emptyChoice _ kind _ branches hstep _ =>
        have hstep' : StepResult.choice kind branches = evalMirBlockStep body s := hstep
        exact False.elim (evalMirBlockStep_ne_choice body s kind branches hstep'.symm)
      | terminated _ _ term hstep =>
        have hstep' : StepResult.terminated term = evalMirBlockStep body s := hstep
        simp only [runMir, ← hstep']
      | failed _ _ err hstep =>
        have hstep' : StepResult.failed err = evalMirBlockStep body s := hstep
        simp only [runMir, ← hstep']
      | noStep _ _ hno =>
        exfalso
        exact hno ⟨evalMirBlockStep body s, rfl⟩
    · intro h
      simp only [runMir] at h
      cases hstep : evalMirBlockStep body s with
      | step obs s' =>
        rw [hstep] at h
        dsimp only at h
        cases hrun : runMir n body s' with
        | mk tr' out' =>
          rw [hrun] at h
          injection h with htr hout
          subst htr hout
          exact ReachesPrefix.step n s s' obs tr' out' hstep.symm
            ((ih s' tr' out').mpr hrun)
      | terminated term =>
        rw [hstep] at h
        injection h with htr hout
        subst htr hout
        exact ReachesPrefix.terminated n s term hstep.symm
      | failed err =>
        rw [hstep] at h
        injection h with htr hout
        subst htr hout
        exact ReachesPrefix.failed n s err hstep.symm
      | choice kind branches =>
        exact False.elim (evalMirBlockStep_ne_choice body s kind branches hstep)

/-- Result carrier of functional translation. -/
inductive AeneasRes (α : Type) where
  | ok (v : α)
  | inapplicable
  | fail
  deriving DecidableEq, Repr

/-- **Tracked Functional Target Language (`TrackedFuncLang`):**
Unlike `FuncLang` (which erases the observation trace `[]`), `TrackedFuncLang`
produces `List StepObs × MirVal`: the exact sequence of basic-block step
observations alongside the returned value. -/
def TrackedFuncLang : Language where
  Prog := MirState → AeneasRes (List StepObs × MirVal)
  Query := MirState
  Out := List StepObs × MirVal
  sem p init := {
    defined := p init ≠ .fail
    val := fun _ tv => p init = .ok tv
  }

/-- Behavior mapping `π_tracked : TrackedFuncLang.Behavior → MirLang.Behavior`.
Lifts a big-step tracked postcondition `post : List StepObs × MirVal → Prop`
to small-step prefix queries `q : ExecQuery MirState`:
- Every finite prefix is safe (`out.outcome.isSafe`).
- Any normal termination `out.outcome = .terminated (.normal ret)` satisfies
  `post (out.trace, ret)`.
- Whenever `q.init` is a valid initial state, there exists a complete trace `t`
  and return value `v` satisfying `post (t, v)` such that:
  - For `q.steps ≤ t.length`, `out.outcome = .running`,
    `out.trace = t.take q.steps`, and `out.trace.length = q.steps` (in
    particular, at `q.steps = t.length`, `out.trace = t` with
    `t.length = q.steps`).
  - For `t.length < q.steps`, `out.outcome = .terminated (.normal v)` and
    `out.trace = t`. -/
def π_tracked (b : TrackedFuncLang.Behavior) : MirLang.Behavior :=
  fun q =>
    Partial.map
      (fun (post : List StepObs × MirVal → Prop)
          (out : ExecOut StepObs MirVal) =>
        out.outcome.isSafe ∧
        (∀ ret, out.outcome = .terminated (.normal ret) →
          post (out.trace, ret)) ∧
        ∃ t v,
          post (t, v) ∧
          (q.steps ≤ t.length →
            out.outcome = .running ∧
            out.trace = t.take q.steps ∧
            out.trace.length = q.steps) ∧
          (t.length < q.steps →
            out.outcome = .terminated (.normal v) ∧
            out.trace = t))
      (b q.init)

/-- `π_tracked` is monotone with respect to `Preorder` (`≤`). -/
theorem monotone_π_tracked : Monotone π_tracked := by
  intro b₁ b₂ hb q
  apply Partial.monotone_map _ (hb q.init)
  intro post₁ post₂ hle out ⟨hsafe, hterm, ⟨t, v, hpost₁, hle_s, hgt_s⟩⟩
  refine ⟨hsafe, ?_, ⟨t, v, hle (t, v) hpost₁, hle_s, hgt_s⟩⟩
  intro ret hret
  exact hle (out.trace, ret) (hterm ret hret)

/-- Positional translation plan over basic blocks. -/
inductive TransPlan where
  | ret
  | step (next : TransPlan)
  | branch (falsePlan : TransPlan) (truePlan : TransPlan)
  | fail
  deriving DecidableEq, Repr

/-- Evaluate a single basic block for a `.branch` plan step, returning the
evaluated boolean branch condition `cond` and the successor `MirState`. -/
def evalBranchBlock (body : MirBody) (s : MirState) :
    Option (Bool × MirState) :=
  match body.blocks[s.block]? with
  | none => none
  | some bb =>
    match evalStmts s.locals bb.stmts with
    | .error _ => none
    | .ok locals' =>
      match bb.terminator with
      | .switchInt discr falseTarget trueTarget =>
        match evalOperand locals' discr with
        | some (.bool false) =>
          some (false, { locals := locals', block := falseTarget })
        | some (.bool true) =>
          some (true, { locals := locals', block := trueTarget })
        | _ => none
      | _ => none

theorem evalMirBlockStep_of_evalBranchBlock {body : MirBody} {s s' : MirState}
    {cond : Bool} (h : evalBranchBlock body s = some (cond, s')) :
    evalMirBlockStep body s = .step StepObs.step s' := by
  unfold evalBranchBlock at h
  unfold evalMirBlockStep
  repeat (split at h <;> try contradiction)
  all_goals simp_all

/-- Plan-guided tracked symbolic evaluator emitting `StepObs.step` on every
basic-block transition. -/
def evalSymTracked (plan : TransPlan) (body : MirBody) (s : MirState) :
    AeneasRes (List StepObs × MirVal) :=
  match plan with
  | .ret =>
    match evalMirBlockStep body s with
    | .terminated (.normal v) => .ok ([], v)
    | _ => .fail
  | .step next =>
    match evalMirBlockStep body s with
    | .step obs s' =>
      match evalSymTracked next body s' with
      | .ok (t, v) => .ok (obs :: t, v)
      | _ => .fail
    | _ => .fail
  | .branch falsePlan truePlan =>
    match evalBranchBlock body s with
    | some (false, sFalse) =>
      match evalSymTracked falsePlan body sFalse with
      | .ok (t, v) => .ok (StepObs.step :: t, v)
      | _ => .fail
    | some (true, sTrue) =>
      match evalSymTracked truePlan body sTrue with
      | .ok (t, v) => .ok (StepObs.step :: t, v)
      | _ => .fail
    | none => .fail
  | .fail => .fail

/-- Input-indexed translation plan (`SymPlan`). -/
abbrev SymPlan := MirState → TransPlan

/-- Tracked input-indexed evaluator (`evalSymWithTracked`). -/
def evalSymWithTracked (symPlan : SymPlan) (body : MirBody) (init : MirState) :
    AeneasRes (List StepObs × MirVal) :=
  evalSymTracked (symPlan init) body init

theorem evalSymTracked_ne_inapplicable (plan : TransPlan) (body : MirBody)
    (s : MirState) :
    evalSymTracked plan body s ≠ .inapplicable := by
  intro h
  cases plan with
  | ret =>
    unfold evalSymTracked at h
    repeat (split at h <;> try contradiction)
  | step _ =>
    unfold evalSymTracked at h
    repeat (split at h <;> try contradiction)
  | branch _ _ =>
    unfold evalSymTracked at h
    repeat (split at h <;> try contradiction)
  | fail =>
    cases h

/-- Core simulation theorem for `evalSymTracked`:
When `evalSymTracked plan body s = .ok (t, v)`, `runMir steps body s` is safe
at every step budget `steps`, produces `(t.take steps, .running)` with trace
length `steps` when `steps ≤ t.length`, and produces
`(t, .terminated (.normal v))` when `t.length < steps`. -/
theorem evalSymTracked_runMir (plan : TransPlan) (body : MirBody) :
    ∀ (s : MirState) (t : List StepObs) (v : MirVal),
      evalSymTracked plan body s = .ok (t, v) →
      ∀ (steps : Nat),
        (steps ≤ t.length →
          runMir steps body s = (t.take steps, .running) ∧
          (runMir steps body s).1.length = steps) ∧
        (t.length < steps →
          runMir steps body s = (t, .terminated (.normal v))) := by
  induction plan with
  | ret =>
    intro s t v heval steps
    unfold evalSymTracked at heval
    cases hstep : evalMirBlockStep body s with
    | step _ _ => rw [hstep] at heval; cases heval
    | choice _ _ => rw [hstep] at heval; cases heval
    | failed _ => rw [hstep] at heval; cases heval
    | terminated term =>
      rw [hstep] at heval
      cases term with
      | unwind => cases heval
      | normal retVal =>
        injection heval with hpair
        injection hpair with ht hv
        subst ht hv
        cases steps with
        | zero =>
          refine ⟨fun _ => ⟨rfl, rfl⟩, fun hlt => by omega⟩
        | succ n =>
          refine ⟨fun hle => by simp at hle, fun _ => ?_⟩
          simp [runMir, hstep]
  | step next ih =>
    intro s t v heval steps
    unfold evalSymTracked at heval
    cases hstep : evalMirBlockStep body s with
    | terminated _ => rw [hstep] at heval; cases heval
    | choice _ _ => rw [hstep] at heval; cases heval
    | failed _ => rw [hstep] at heval; cases heval
    | step obs s' =>
      rw [hstep] at heval
      dsimp only at heval
      cases hnext : evalSymTracked next body s' with
      | fail => rw [hnext] at heval; cases heval
      | inapplicable => rw [hnext] at heval; cases heval
      | ok tv' =>
        rcases tv' with ⟨t', v'⟩
        rw [hnext] at heval
        injection heval with hpair
        injection hpair with ht hv
        subst ht hv
        cases steps with
        | zero =>
          refine ⟨fun _ => ⟨rfl, rfl⟩, fun hlt => by omega⟩
        | succ n =>
          have ih_n := ih s' t' v' hnext n
          refine ⟨?_, ?_⟩
          · intro hle
            simp only [List.length_cons, Nat.add_le_add_iff_right] at hle
            rcases (ih_n.1 hle) with ⟨hrun', _⟩
            simp only [runMir, hstep, hrun', List.take_succ_cons,
              true_and, List.length_cons, List.length_take]
            omega
          · intro hlt
            simp only [List.length_cons, Nat.add_lt_add_iff_right] at hlt
            have hrun' := ih_n.2 hlt
            simp only [runMir, hstep, hrun']
  | branch falsePlan truePlan ihFalse ihTrue =>
    intro s t v heval steps
    unfold evalSymTracked at heval
    cases hbr : evalBranchBlock body s with
    | none => rw [hbr] at heval; cases heval
    | some pair =>
      rcases pair with ⟨cond, s'⟩
      have hstep := evalMirBlockStep_of_evalBranchBlock hbr
      cases cond with
      | false =>
        rw [hbr] at heval
        dsimp only at heval
        cases hnext : evalSymTracked falsePlan body s' with
        | fail => rw [hnext] at heval; cases heval
        | inapplicable => rw [hnext] at heval; cases heval
        | ok tv' =>
          rcases tv' with ⟨t', v'⟩
          rw [hnext] at heval
          injection heval with hpair
          injection hpair with ht hv
          subst ht hv
          cases steps with
          | zero =>
            refine ⟨fun _ => ⟨rfl, rfl⟩, fun hlt => by omega⟩
          | succ n =>
            have ih_n := ihFalse s' t' v' hnext n
            refine ⟨?_, ?_⟩
            · intro hle
              simp only [List.length_cons, Nat.add_le_add_iff_right] at hle
              rcases (ih_n.1 hle) with ⟨hrun', _⟩
              simp only [runMir, hstep, hrun', List.take_succ_cons,
                true_and, List.length_cons, List.length_take]
              omega
            · intro hlt
              simp only [List.length_cons, Nat.add_lt_add_iff_right] at hlt
              have hrun' := ih_n.2 hlt
              simp only [runMir, hstep, hrun']
      | true =>
        rw [hbr] at heval
        dsimp only at heval
        cases hnext : evalSymTracked truePlan body s' with
        | fail => rw [hnext] at heval; cases heval
        | inapplicable => rw [hnext] at heval; cases heval
        | ok tv' =>
          rcases tv' with ⟨t', v'⟩
          rw [hnext] at heval
          injection heval with hpair
          injection hpair with ht hv
          subst ht hv
          cases steps with
          | zero =>
            refine ⟨fun _ => ⟨rfl, rfl⟩, fun hlt => by omega⟩
          | succ n =>
            have ih_n := ihTrue s' t' v' hnext n
            refine ⟨?_, ?_⟩
            · intro hle
              simp only [List.length_cons, Nat.add_le_add_iff_right] at hle
              rcases (ih_n.1 hle) with ⟨hrun', _⟩
              simp only [runMir, hstep, hrun', List.take_succ_cons,
                true_and, List.length_cons, List.length_take]
              omega
            · intro hlt
              simp only [List.length_cons, Nat.add_lt_add_iff_right] at hlt
              have hrun' := ih_n.2 hlt
              simp only [runMir, hstep, hrun']
  | fail =>
    intro _ _ _ heval
    cases heval

/-- **Universal Tracked Abstraction Theorem (`evalSymWithTracked_sound`):**
For every `symPlan : SymPlan` and `body : MirBody`,
`evalSymWithTracked symPlan body` is a sound tracked functional abstraction of
`body` under `π_tracked` (`Abstracts TrackedFuncLang MirLang π_tracked`). -/
theorem evalSymWithTracked_sound (symPlan : SymPlan) (body : MirBody) :
    Abstracts TrackedFuncLang MirLang π_tracked
      (evalSymWithTracked symPlan body) body := by
  intro q hdef
  have hne : evalSymWithTracked symPlan body q.init ≠ .fail := hdef
  unfold evalSymWithTracked at hne
  cases hres : evalSymTracked (symPlan q.init) body q.init with
  | fail => exact False.elim (hne hres)
  | inapplicable =>
    exact False.elim
      (evalSymTracked_ne_inapplicable (symPlan q.init) body q.init hres)
  | ok tv =>
    rcases tv with ⟨t, v⟩
    have hsim := evalSymTracked_runMir (symPlan q.init) body q.init t v hres q.steps
    have hMirDef : (MirLang.sem body q).defined := by
      intro _ tr out hreach
      have hrun := (reachesPrefix_iff_runMir body q.init q.steps q.init tr out).mp hreach
      by_cases hle : q.steps ≤ t.length
      · have h1 := (hsim.1 hle).1
        rw [hrun] at h1
        injection h1 with _ hout
        subst hout
        exact True.intro
      · have hlt : t.length < q.steps := by omega
        have h2 := hsim.2 hlt
        rw [hrun] at h2
        injection h2 with _ hout
        subst hout
        exact True.intro
    refine ⟨hMirDef, ?_⟩
    intro out ⟨_, hreach⟩
    have hrun :=
      (reachesPrefix_iff_runMir body q.init q.steps q.init out.trace out.outcome).mp hreach
    have hpost_ok : evalSymWithTracked symPlan body q.init = .ok (t, v) := hres
    by_cases hle : q.steps ≤ t.length
    · rcases (hsim.1 hle) with ⟨h1, hlen⟩
      rw [hrun] at h1 hlen
      injection h1 with htr hout
      refine ⟨by rw [hout]; exact True.intro, ?_, ⟨t, v, hpost_ok, ?_, ?_⟩⟩
      · intro ret hterm
        rw [hout] at hterm
        cases hterm
      · intro _
        exact ⟨hout, htr, hlen⟩
      · intro hlt
        omega
    · have hlt : t.length < q.steps := by omega
      have h2 := hsim.2 hlt
      rw [hrun] at h2
      injection h2 with htr hout
      refine ⟨by rw [hout]; exact True.intro, ?_, ⟨t, v, hpost_ok, ?_, ?_⟩⟩
      · intro ret hterm
        rw [hout] at hterm
        injection hterm with hnorm
        injection hnorm with hret
        subst hret htr
        exact hpost_ok
      · intro hle'
        omega
      · intro _
        exact ⟨hout, htr⟩

/-- **Adequacy Bridge Theorem 1
(`trackedFuncLang_exact_trace_length_at_steps`):**
When `evalSymWithTracked symPlan body init = .ok (t, v)` on `pre init`,
`MirLang.sem body` refines `MirLang.SpecOn` at `q.steps = t.length` with exact
observation trace `out.trace = t` and `out.trace.length = q.steps`
(`t.length = steps`). -/
theorem trackedFuncLang_exact_trace_length_at_steps
    (symPlan : SymPlan) (body : MirBody)
    (pre : MirState → Prop)
    (tOf : MirState → List StepObs)
    (vOf : MirState → MirVal)
    (heval : ∀ init, pre init →
      evalSymWithTracked symPlan body init = .ok (tOf init, vOf init)) :
    MirLang.sem body ≤
      MirLang.SpecOn
        (fun q => pre q.init ∧ q.steps = (tOf q.init).length)
        (fun q out =>
          out.trace = tOf q.init ∧
          out.trace.length = q.steps ∧
          (tOf q.init).length = q.steps) := by
  apply behaviorOf_le_specOn
  intro q out ⟨hpre, hsteps⟩ hexec
  have habs := evalSymWithTracked_sound symPlan body q
  have hok := heval q.init hpre
  have hdef : (π_tracked (TrackedFuncLang.sem (evalSymWithTracked symPlan body)) q).defined := by
    intro hfail
    rw [hok] at hfail
    cases hfail
  rcases habs hdef with ⟨_, hval⟩
  rcases hval out hexec with ⟨hsafe, _, ⟨t, v, htv, hle, _⟩⟩
  change evalSymWithTracked symPlan body q.init = .ok (t, v) at htv
  rw [hok] at htv
  injection htv with hpair
  injection hpair with ht hv
  subst ht hv
  have hle_steps : q.steps ≤ (tOf q.init).length := by omega
  rcases hle hle_steps with ⟨_, htr, hlen⟩
  rw [hsteps, List.take_length] at htr
  exact ⟨hsafe, htr, hlen, hsteps.symm⟩

/-- **Adequacy Bridge Theorem 2 (`trackedFuncLang_adequacy_specOn`):**
When `evalSymWithTracked symPlan body init = .ok (tOf init, vOf init)` with
`Post init (tOf init) (vOf init)`, `MirLang.sem body` refines `MirLang.SpecOn`
for all `q.steps > (tOf q.init).length`, guaranteeing normal termination
`out.outcome = .terminated (.normal (vOf q.init))`, exact observation trace
`out.trace = tOf q.init`, and `Post q.init out.trace (vOf q.init)`. -/
theorem trackedFuncLang_adequacy_specOn
    (symPlan : SymPlan) (body : MirBody)
    (pre : MirState → Prop)
    (Post : MirState → List StepObs → MirVal → Prop)
    (tOf : MirState → List StepObs)
    (vOf : MirState → MirVal)
    (heval : ∀ init, pre init →
      evalSymWithTracked symPlan body init = .ok (tOf init, vOf init) ∧
      Post init (tOf init) (vOf init)) :
    MirLang.sem body ≤
      MirLang.SpecOn
        (fun q => pre q.init ∧ (tOf q.init).length < q.steps)
        (fun q out =>
          out.outcome = .terminated (.normal (vOf q.init)) ∧
          out.trace = tOf q.init ∧
          Post q.init out.trace (vOf q.init)) := by
  apply behaviorOf_le_specOn
  intro q out ⟨hpre, hlt⟩ hexec
  have habs := evalSymWithTracked_sound symPlan body q
  rcases heval q.init hpre with ⟨hok, hpost⟩
  have hdef : (π_tracked (TrackedFuncLang.sem (evalSymWithTracked symPlan body)) q).defined := by
    intro hfail
    rw [hok] at hfail
    cases hfail
  rcases habs hdef with ⟨_, hval⟩
  rcases hval out hexec with ⟨hsafe, _, ⟨t, v, htv, _, hgt⟩⟩
  change evalSymWithTracked symPlan body q.init = .ok (t, v) at htv
  rw [hok] at htv
  injection htv with hpair
  injection hpair with ht hv
  subst ht hv
  rcases hgt hlt with ⟨hout, htr⟩
  refine ⟨hsafe, hout, htr, ?_⟩
  rw [htr]
  exact hpost

/-!
## Section 3: Task 2 — Loop Invariant + Ranking Measure (`loop_spec_decr_nat`)
-/

/-- Multi-step basic-block transition relation (`ReachInSteps body m s₁ tr s₂`):
starting from `s₁`, `MirMachine` executes `m` basic-block transitions to `s₂`,
emitting trace `tr` (with `tr.length = m`). -/
inductive ReachInSteps (body : MirBody) :
    Nat → MirState → List StepObs → MirState → Prop where
  | zero (s : MirState) :
      ReachInSteps body 0 s [] s
  | step {n : Nat} {s s' s'' : MirState} {obs : StepObs} {tr : List StepObs} :
      evalMirBlockStep body s = .step obs s' →
      ReachInSteps body n s' tr s'' →
      ReachInSteps body (n + 1) s (obs :: tr) s''

/-- Multi-step terminal reachability (`ReachReturnInSteps body n s tr v`):
starting from `s`, `MirMachine` reaches `.terminated (.normal v)` in `n` step
evaluations, emitting trace `tr` (with `n = tr.length + 1`). -/
inductive ReachReturnInSteps (body : MirBody) :
    Nat → MirState → List StepObs → MirVal → Prop where
  | ret {s : MirState} {v : MirVal} :
      evalMirBlockStep body s = .terminated (.normal v) →
      ReachReturnInSteps body 1 s [] v
  | step {n : Nat} {s s' : MirState} {obs : StepObs} {tr : List StepObs}
      {v : MirVal} :
      evalMirBlockStep body s = .step obs s' →
      ReachReturnInSteps body n s' tr v →
      ReachReturnInSteps body (n + 1) s (obs :: tr) v

theorem ReachInSteps.trace_length {body : MirBody} {m : Nat}
    {s₁ s₂ : MirState} {tr : List StepObs}
    (h : ReachInSteps body m s₁ tr s₂) :
    tr.length = m := by
  induction h with
  | zero => rfl
  | step _ _ ih => simp [ih]

theorem ReachReturnInSteps.trace_length {body : MirBody} {n : Nat}
    {s : MirState} {tr : List StepObs} {v : MirVal}
    (h : ReachReturnInSteps body n s tr v) :
    tr.length + 1 = n := by
  induction h with
  | ret => rfl
  | step _ _ ih => simp [ih]

/-- Composing a `ReachInSteps` prefix with a `ReachReturnInSteps`
continuation. -/
theorem ReachInSteps.trans_return {body : MirBody} {m n : Nat}
    {s₁ s₂ : MirState} {tr₁ tr₂ : List StepObs} {v : MirVal}
    (h₁ : ReachInSteps body m s₁ tr₁ s₂)
    (h₂ : ReachReturnInSteps body n s₂ tr₂ v) :
    ReachReturnInSteps body (m + n) s₁ (tr₁ ++ tr₂) v := by
  induction h₁ with
  | zero =>
    simp only [Nat.zero_add, List.nil_append]
    exact h₂
  | step hstep _ ih =>
    rw [Nat.succ_add, List.cons_append]
    exact ReachReturnInSteps.step hstep (ih h₂)

/-- Fuel-monotonicity and prefix-safety of `ReachReturnInSteps`:
If `ReachReturnInSteps body n s tr v`, then:
1. For any `fuel ≥ n`, `runMir fuel body s = (tr, .terminated (.normal v))`.
2. For any `fuel : Nat` (including `fuel < n`), `(runMir fuel body s).2.isSafe`
   holds and any `.terminated (.normal ret)` outcome has `ret = v` and
   `trace = tr`. -/
theorem ReachReturnInSteps.to_runMir {body : MirBody} {n : Nat}
    {s : MirState} {tr : List StepObs} {v : MirVal}
    (h : ReachReturnInSteps body n s tr v) :
    (∀ fuel, n ≤ fuel → runMir fuel body s = (tr, .terminated (.normal v))) ∧
    (∀ fuel, (runMir fuel body s).2.isSafe ∧
      ∀ ret, (runMir fuel body s).2 = .terminated (.normal ret) →
        ret = v ∧ (runMir fuel body s).1 = tr) := by
  induction h with
  | ret hterm =>
    constructor
    · intro fuel hle
      cases fuel with
      | zero => omega
      | succ f => simp [runMir, hterm]
    · intro fuel
      cases fuel with
      | zero =>
        refine ⟨True.intro, fun _ h => by cases h⟩
      | succ f =>
        refine ⟨by simp [runMir, hterm, PrefixOutcome.isSafe], ?_⟩
        intro ret h
        simp only [runMir, hterm] at h ⊢
        injection h with hnorm
        injection hnorm with hret
        exact ⟨hret.symm, trivial⟩
  | step hstep _ ih =>
    rcases ih with ⟨ih_ge, ih_all⟩
    constructor
    · intro fuel hle
      cases fuel with
      | zero => omega
      | succ f =>
        have hle' : _ ≤ f := Nat.le_of_succ_le_succ hle
        simp [runMir, hstep, ih_ge f hle']
    · intro fuel
      cases fuel with
      | zero =>
        refine ⟨True.intro, fun _ h => by cases h⟩
      | succ f =>
        rcases ih_all f with ⟨hsafe, hret⟩
        simp only [runMir, hstep]
        refine ⟨hsafe, ?_⟩
        intro ret hout
        rcases hret ret hout with ⟨heq_v, heq_tr⟩
        exact ⟨heq_v, congrArg (_ :: ·) heq_tr⟩

/-- **Compositional Loop-Header Invariant and Ranking-Measure Theorem
(`loop_spec_decr_nat`):**
Given a loop header block `bb_head`, state invariant `Inv : MirState → Prop`,
loop guard `guard : MirState → Bool`, ranking measure `rank : MirState → Nat`,
and per-iteration step bound `k > 0` and exit step bound `k_exit > 0`:
1. (**Body step**): When `guard s = true`, executing the loop body from
   `bb_head` takes `m ≤ k` basic-block transitions back to `bb_head`,
   preserving `Inv s'` and strictly decreasing the ranking measure
   (`rank s' < rank s`).
2. (**Exit step**): When `guard s = false`, executing the exit branch from
   `bb_head` takes `m_exit ≤ k_exit` transitions to `.return v` with `Post v`.

Then by well-founded induction on `rank s`, from any state `s` at `bb_head`
satisfying `Inv s`, there exist `m ≤ k * rank s + k_exit`, `tr : List StepObs`
with `tr.length ≤ k * rank s + k_exit`, and `v : MirVal` with `Post v` such that
`ReachReturnInSteps body m s tr v` holds—and therefore for **every**
`fuel ≥ k * rank s + k_exit`, `MirMachine` reaches `.terminated (.normal v)`
with trace `tr`! -/
theorem loop_spec_decr_nat
    (body : MirBody)
    (bb_head : Nat)
    (Inv : MirState → Prop)
    (guard : MirState → Bool)
    (rank : MirState → Nat)
    (Post : MirVal → Prop)
    (k k_exit : Nat)
    (h_body : ∀ s, s.block = bb_head → Inv s → guard s = true →
      ∃ m tr_body s',
        m ≤ k ∧
        ReachInSteps body m s tr_body s' ∧
        s'.block = bb_head ∧
        Inv s' ∧
        rank s' < rank s)
    (h_exit : ∀ s, s.block = bb_head → Inv s → guard s = false →
      ∃ m_exit tr_exit v,
        m_exit ≤ k_exit ∧
        ReachReturnInSteps body m_exit s tr_exit v ∧
        Post v) :
    ∀ (s : MirState),
      s.block = bb_head →
      Inv s →
      ∃ m tr v,
        m ≤ k * rank s + k_exit ∧
        tr.length ≤ k * rank s + k_exit ∧
        ReachReturnInSteps body m s tr v ∧
        Post v ∧
        (∀ fuel, k * rank s + k_exit ≤ fuel →
          runMir fuel body s = (tr, .terminated (.normal v))) := by
  suffices h_ind : ∀ (bound : Nat) (s : MirState),
      rank s ≤ bound →
      s.block = bb_head →
      Inv s →
      ∃ m tr v,
        m ≤ k * rank s + k_exit ∧
        tr.length ≤ k * rank s + k_exit ∧
        ReachReturnInSteps body m s tr v ∧
        Post v ∧
        (∀ fuel, k * rank s + k_exit ≤ fuel →
          runMir fuel body s = (tr, .terminated (.normal v))) by
    intro s hblk hinv
    exact h_ind (rank s) s (Nat.le_refl _) hblk hinv
  intro bound
  induction bound with
  | zero =>
    intro s hrank0 hblk hinv
    cases hguard : guard s with
    | false =>
      rcases h_exit s hblk hinv hguard with ⟨m_exit, tr_exit, v, hm_le, hret, hpost⟩
      have hlen_eq := hret.trace_length
      have hm_bound : m_exit ≤ k * rank s + k_exit := by omega
      have hlen_bound : tr_exit.length ≤ k * rank s + k_exit := by omega
      refine ⟨m_exit, tr_exit, v, hm_bound, hlen_bound, hret, hpost, ?_⟩
      intro fuel hfuel
      exact hret.to_runMir.1 fuel (by omega)
    | true =>
      rcases h_body s hblk hinv hguard with ⟨_, _, s', _, _, _, _, hlt⟩
      omega
  | succ b ih =>
    intro s hrank hblk hinv
    cases hguard : guard s with
    | false =>
      rcases h_exit s hblk hinv hguard with ⟨m_exit, tr_exit, v, hm_le, hret, hpost⟩
      have hlen_eq := hret.trace_length
      have hm_bound : m_exit ≤ k * rank s + k_exit := by omega
      have hlen_bound : tr_exit.length ≤ k * rank s + k_exit := by omega
      refine ⟨m_exit, tr_exit, v, hm_bound, hlen_bound, hret, hpost, ?_⟩
      intro fuel hfuel
      exact hret.to_runMir.1 fuel (by omega)
    | true =>
      rcases h_body s hblk hinv hguard with
        ⟨m₁, tr₁, s', hm₁_le, hstep₁, hblk', hinv', hlt⟩
      have hrank' : rank s' ≤ b := by omega
      rcases ih s' hrank' hblk' hinv' with
        ⟨m₂, tr₂, v, hm₂_le, _, hret₂, hpost, _⟩
      have hcomp := hstep₁.trans_return hret₂
      have hlen_comp := hcomp.trace_length
      have hmul : k * rank s' + k ≤ k * rank s := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left k hlt
      have hm_total : m₁ + m₂ ≤ k * rank s + k_exit := by omega
      have hlen_total : (tr₁ ++ tr₂).length ≤ k * rank s + k_exit := by omega
      refine ⟨m₁ + m₂, tr₁ ++ tr₂, v, hm_total, hlen_total, hcomp, hpost, ?_⟩
      intro fuel hfuel
      exact hcomp.to_runMir.1 fuel (by omega)

/-- Ranking-measure-indexed `TransPlan` generator for loops:
unrolls `planIter` `r = rank s` times before terminating with `planExit`. -/
def loopPlanByRank (planExit : TransPlan) (planIter : TransPlan → TransPlan) :
    Nat → TransPlan
  | 0 => planExit
  | r + 1 => planIter (loopPlanByRank planExit planIter r)

/-- **`TrackedFuncLang` Loop Invariant & Ranking-Measure Theorem
(`tracked_loop_spec_decr_nat`):**
If `rank s = 0` executes `planExit` in `≤ k_exit` observations to `v` with
`Post v`, and `rank s = r + 1` steps one loop iteration via `planIter` in `≤ k`
observations to `s'` with `Inv s'` and `rank s' = r`, then `evalSymTracked` on
`loopPlanByRank planExit planIter (rank s)` succeeds with `.ok (t, v)` where
`t.length ≤ k * rank s + k_exit` and `Post v`. -/
theorem tracked_loop_spec_decr_nat
    (body : MirBody)
    (Inv : MirState → Prop)
    (rank : MirState → Nat)
    (Post : MirVal → Prop)
    (planExit : TransPlan)
    (planIter : TransPlan → TransPlan)
    (k k_exit : Nat)
    (h_exit : ∀ s, Inv s → rank s = 0 →
      ∃ t_exit v,
        t_exit.length ≤ k_exit ∧
        evalSymTracked planExit body s = .ok (t_exit, v) ∧
        Post v)
    (h_iter : ∀ r s, Inv s → rank s = r + 1 →
      ∃ t_iter s',
        t_iter.length ≤ k ∧
        Inv s' ∧
        rank s' = r ∧
        ∀ (rest : TransPlan) (t_rest : List StepObs) (v : MirVal),
          evalSymTracked rest body s' = .ok (t_rest, v) →
          evalSymTracked (planIter rest) body s = .ok (t_iter ++ t_rest, v)) :
    ∀ (s : MirState),
      Inv s →
      ∃ t v,
        t.length ≤ k * rank s + k_exit ∧
        evalSymTracked (loopPlanByRank planExit planIter (rank s)) body s = .ok (t, v) ∧
        Post v := by
  suffices h_ind : ∀ (r : Nat) (s : MirState),
      Inv s → rank s = r →
      ∃ t v,
        t.length ≤ k * r + k_exit ∧
        evalSymTracked (loopPlanByRank planExit planIter r) body s = .ok (t, v) ∧
        Post v by
    intro s hinv
    exact h_ind (rank s) s hinv rfl
  intro r
  induction r with
  | zero =>
    intro s hinv hr0
    rcases h_exit s hinv hr0 with ⟨t_exit, v, hlen, hev, hpost⟩
    refine ⟨t_exit, v, by omega, hev, hpost⟩
  | succ r' ih =>
    intro s hinv hr
    rcases h_iter r' s hinv hr with ⟨t_iter, s', hlen_iter, hinv', hr', hstep_iter⟩
    rcases ih s' hinv' hr' with ⟨t_rest, v, hlen_rest, hev_rest, hpost⟩
    have hev_full := hstep_iter (loopPlanByRank planExit planIter r') t_rest v hev_rest
    have hlen_full : (t_iter ++ t_rest).length ≤ k * (r' + 1) + k_exit := by
      rw [List.length_append, Nat.mul_succ]
      omega
    exact ⟨t_iter ++ t_rest, v, hlen_full, hev_full, hpost⟩

/-!
### Concrete Demonstration of `loop_spec_decr_nat` on `sum_to_n`

Consider the Rust loop:
```rust
pub fn sum_to_n(n: usize) -> usize {
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        i += 1;
        acc += i;
    }
    acc
}
```
Its lowered basic-block CFG (`sumToNBody`) has 5 basic blocks:
- `bb0` (entry): `_2 = 0; _3 = 0; goto bb1` (`1` transition to reach `bb1`).
- `bb1` (loop header `bb_head = 1`): `_4 = (_2 < _1); switchInt _4 -> [false: bb4, true: bb2]`.
- `bb2` (loop body part 1): `_2 = _2 + 1; goto bb3`.
- `bb3` (loop body part 2): `_3 = _3 + _2; goto bb1`.
- `bb4` (exit): `_0 = _3; return _0`.

Notice that:
- Each loop iteration (`bb1 -> bb2 -> bb3 -> bb1`) takes `k = 3` transitions.
- The loop exit (`bb1 -> bb4 -> return`) takes `k_exit = 2` step evaluations.
- Together with `bb0 -> bb1` (`1` step), the total step budget from `bb0` is
  `1 + (3 * n + 2) = 3 * n + 3`!
-/

/-- Mathematical sum $\sum_{j=1}^i j$. -/
def sumTo : Nat → Nat
  | 0 => 0
  | i + 1 => sumTo i + (i + 1)

/-- Concrete MIR body for `sum_to_n`. -/
def sumToNBody : MirBody where
  argCount := 1
  blocks := [
    -- bb0: _2 = 0; _3 = 0; goto bb1
    { stmts := [
        .assignUse 2 (.constVal (.usize 0)),
        .assignUse 3 (.constVal (.usize 0))
      ]
      terminator := .goto 1 },
    -- bb1 (header): _4 = (_2 < _1); switchInt _4 -> [false: bb4, true: bb2]
    { stmts := [
        .assignBinOp 4 .lt (.copy 2) (.copy 1)
      ]
      terminator := .switchInt (.copy 4) 4 2 },
    -- bb2: _2 = _2 + 1; goto bb3
    { stmts := [
        .assignBinOp 2 .add (.copy 2) (.constVal (.usize 1))
      ]
      terminator := .goto 3 },
    -- bb3: _3 = _3 + _2; goto bb1
    { stmts := [
        .assignBinOp 3 .add (.copy 3) (.copy 2)
      ]
      terminator := .goto 1 },
    -- bb4 (exit): _0 = _3; return _0
    { stmts := [
        .assignUse 0 (.copy 3)
      ]
      terminator := .return_ (.copy 0) }
  ]

/-- Extract the loop counter `i` from local `_2`. -/
def sumToNCounter (s : MirState) : Nat :=
  match s.locals 2 with
  | some (.usize i) => i
  | _ => 0

/-- Loop invariant at `bb1` for input `n`:
`_1 = n`, `_2 = i` with `i ≤ n`, and `_3 = sumTo i`. -/
structure SumToNInv (n : Nat) (s : MirState) : Prop where
  block_eq : s.block = 1
  local1 : s.locals 1 = some (.usize n)
  counter_le : sumToNCounter s ≤ n
  local2 : s.locals 2 = some (.usize (sumToNCounter s))
  local3 : s.locals 3 = some (.usize (sumTo (sumToNCounter s)))

/-- Ranking measure `rank s := n - i` at loop header `bb1`. -/
def sumToNRank (n : Nat) (s : MirState) : Nat :=
  n - sumToNCounter s

/-- Loop guard `i < n` at loop header `bb1`. -/
def sumToNGuard (n : Nat) (s : MirState) : Bool :=
  decide (sumToNCounter s < n)

/-- Single-iteration body lemma for `sum_to_n` (`k = 3` transitions:
`bb1 -> bb2 -> bb3 -> bb1`), proved by symbolic stepping without unfolding the
loop. -/
theorem sumToN_loop_body_step (n : Nat) (s : MirState)
    (hblk : s.block = 1)
    (hinv : SumToNInv n s)
    (hguard : sumToNGuard n s = true) :
    ∃ m tr_body s',
      m ≤ 3 ∧
      ReachInSteps sumToNBody m s tr_body s' ∧
      s'.block = 1 ∧
      SumToNInv n s' ∧
      sumToNRank n s' < sumToNRank n s := by
  have hilt : sumToNCounter s < n := of_decide_eq_true hguard
  let i := sumToNCounter s
  have h1 := hinv.local1
  have h2 : s.locals 2 = some (.usize i) := hinv.local2
  have h3 : s.locals 3 = some (.usize (sumTo i)) := hinv.local3
  let locals1 := updateLocal s.locals 4 (some (.bool true))
  let s_bb2 : MirState := { locals := locals1, block := 2 }
  let locals2 := updateLocal locals1 2 (some (.usize (i + 1)))
  let s_bb3 : MirState := { locals := locals2, block := 3 }
  let locals3 := updateLocal locals2 3 (some (.usize (sumTo i + (i + 1))))
  let s_bb1' : MirState := { locals := locals3, block := 1 }
  have hstep1 : evalMirBlockStep sumToNBody s = .step StepObs.step s_bb2 := by
    cases s with
    | mk locals block =>
      dsimp at hblk h1 h2 h3
      subst hblk
      have hdec : decide (i < n) = true := decide_eq_true hilt
      simp [evalMirBlockStep, sumToNBody, evalStmts, evalStmt, evalOperand,
        evalBinOp, h1, h2, hdec, s_bb2, locals1, updateLocal]
  have hstep2 : evalMirBlockStep sumToNBody s_bb2 = .step StepObs.step s_bb3 := by
    have h2' : locals1 2 = some (.usize i) := h2
    simp [evalMirBlockStep, sumToNBody, evalStmts, evalStmt, evalOperand,
      evalBinOp, h2', s_bb2, s_bb3, locals2]
  have hstep3 : evalMirBlockStep sumToNBody s_bb3 = .step StepObs.step s_bb1' := by
    have h3' : locals2 3 = some (.usize (sumTo i)) := h3
    have h2'' : locals2 2 = some (.usize (i + 1)) := rfl
    simp [evalMirBlockStep, sumToNBody, evalStmts, evalStmt, evalOperand,
      evalBinOp, h3', h2'', s_bb3, s_bb1', locals3]
  have hcnt' : sumToNCounter s_bb1' = i + 1 := rfl
  refine ⟨3, [StepObs.step, StepObs.step, StepObs.step], s_bb1', Nat.le_refl 3,
    ReachInSteps.step hstep1 (ReachInSteps.step hstep2 (ReachInSteps.step hstep3 (ReachInSteps.zero _))),
    rfl, ?_, ?_⟩
  · refine ⟨rfl, h1, ?_, ?_, ?_⟩
    · rw [hcnt']; omega
    · rw [hcnt']; rfl
    · rw [hcnt']; rfl
  · unfold sumToNRank
    rw [hcnt']
    omega

/-- Exit branch lemma for `sum_to_n` (`k_exit = 2` steps: `bb1 -> bb4 -> return`). -/
theorem sumToN_loop_exit_step (n : Nat) (s : MirState)
    (hblk : s.block = 1)
    (hinv : SumToNInv n s)
    (hguard : sumToNGuard n s = false) :
    ∃ m_exit tr_exit v,
      m_exit ≤ 2 ∧
      ReachReturnInSteps sumToNBody m_exit s tr_exit v ∧
      v = .usize (sumTo n) := by
  have hge : n ≤ sumToNCounter s := Nat.not_lt.mp (of_decide_eq_false hguard)
  have hi_eq : sumToNCounter s = n := Nat.le_antisymm hinv.counter_le hge
  have h1 := hinv.local1
  have h2 : s.locals 2 = some (.usize n) := by rw [← hi_eq]; exact hinv.local2
  have h3 : s.locals 3 = some (.usize (sumTo n)) := by rw [← hi_eq]; exact hinv.local3
  let locals1 := updateLocal s.locals 4 (some (.bool false))
  let s_bb4 : MirState := { locals := locals1, block := 4 }
  have hstep1 : evalMirBlockStep sumToNBody s = .step StepObs.step s_bb4 := by
    cases s with
    | mk locals block =>
      dsimp at hblk h1 h2 h3
      subst hblk
      simp [evalMirBlockStep, sumToNBody, evalStmts, evalStmt, evalOperand,
        evalBinOp, h1, h2, s_bb4, locals1, updateLocal]
  have hstep2 : evalMirBlockStep sumToNBody s_bb4 = .terminated (.normal (.usize (sumTo n))) := by
    have h3' : locals1 3 = some (.usize (sumTo n)) := h3
    simp [evalMirBlockStep, sumToNBody, evalStmts, evalStmt, evalOperand,
      h3', s_bb4, updateLocal]
  exact ⟨2, [StepObs.step], .usize (sumTo n), Nat.le_refl 2,
    ReachReturnInSteps.step hstep1 (ReachReturnInSteps.ret hstep2), rfl⟩

/-- **Instantiating `loop_spec_decr_nat` on `sumToNBody`:**
Proves in one shot that from any initial state `init` with `init.block = 0` and
`init.locals 1 = some (.usize n)`, there exists a trace `tr` with
`tr.length ≤ 3 * n + 3` such that for **all** `fuel ≥ 3 * n + 3`, `MirMachine`
reaches `.terminated (.normal (.usize (sumTo n)))` with trace `tr`—without
unfolding the loop $3n + 3$ steps manually! -/
theorem sumToN_verified_via_ranking_measure (n : Nat) (init : MirState)
    (hblk0 : init.block = 0)
    (harg1 : init.locals 1 = some (.usize n)) :
    ∃ m tr,
      m ≤ 3 * n + 3 ∧
      tr.length ≤ 3 * n + 3 ∧
      ReachReturnInSteps sumToNBody m init tr (.usize (sumTo n)) ∧
      (∀ fuel, 3 * n + 3 ≤ fuel →
        runMir fuel sumToNBody init = (tr, .terminated (.normal (.usize (sumTo n))))) := by
  let locals_bb1 := updateLocal (updateLocal init.locals 2 (some (.usize 0))) 3 (some (.usize 0))
  let s_bb1 : MirState := { locals := locals_bb1, block := 1 }
  have hstep_entry : evalMirBlockStep sumToNBody init = .step StepObs.step s_bb1 := by
    cases init with
    | mk locals block =>
      dsimp at hblk0
      subst hblk0
      rfl
  have hinv_bb1 : SumToNInv n s_bb1 :=
    ⟨rfl, harg1, Nat.zero_le n, rfl, rfl⟩
  have hrank_bb1 : sumToNRank n s_bb1 = n := Nat.sub_zero n
  rcases loop_spec_decr_nat
      sumToNBody 1 (SumToNInv n) (sumToNGuard n) (sumToNRank n)
      (fun v => v = .usize (sumTo n)) 3 2
      (sumToN_loop_body_step n)
      (sumToN_loop_exit_step n)
      s_bb1 rfl hinv_bb1 with
    ⟨m_loop, tr_loop, v, hm_le, _, hret_loop, hv_eq, _⟩
  subst hv_eq
  rw [hrank_bb1] at hm_le
  have hret_full :
      ReachReturnInSteps sumToNBody (1 + m_loop) init (StepObs.step :: tr_loop)
        (.usize (sumTo n)) := by
    rw [Nat.add_comm 1 m_loop]
    exact ReachReturnInSteps.step hstep_entry hret_loop
  have hlen_full := hret_full.trace_length
  have hm_bound : 1 + m_loop ≤ 3 * n + 3 := by omega
  have hlen_bound : (StepObs.step :: tr_loop).length ≤ 3 * n + 3 := by omega
  refine ⟨1 + m_loop, StepObs.step :: tr_loop, hm_bound, hlen_bound, hret_full, ?_⟩
  intro fuel hfuel
  exact hret_full.to_runMir.1 fuel (by omega)

/-- **Fuel-Free Specification Corollary (`sumToN_satisfies_fuelFree_specOn`):**
Because `sumToN_verified_via_ranking_measure` establishes `ReachReturnInSteps`
with a ranking-derived bound, the user-facing `MirLang.SpecOn` specification can
be stated **completely without `fuel` in the precondition** (`q.steps` is
unconstrained!):
- Every finite prefix at any `q.steps : Nat` is safe (`out.outcome.isSafe`),
- Any normal return at any `q.steps : Nat` equals `.usize (sumTo n)` with trace
  length `≤ 3 * n + 3`, AND
- Whenever `q.steps ≥ 3 * n + 3`, termination with `.usize (sumTo n)` is
  guaranteed! -/
theorem sumToN_satisfies_fuelFree_specOn (n : Nat) :
    MirLang.sem sumToNBody ≤
      MirLang.SpecOn
        (fun q => q.init.block = 0 ∧ q.init.locals 1 = some (.usize n))
        (fun q out =>
          (∀ ret, out.outcome = .terminated (.normal ret) →
            ret = .usize (sumTo n) ∧ out.trace.length ≤ 3 * n + 3) ∧
          (3 * n + 3 ≤ q.steps →
            out.outcome = .terminated (.normal (.usize (sumTo n))) ∧
            out.trace.length ≤ 3 * n + 3)) := by
  apply behaviorOf_le_specOn
  intro q out ⟨hblk0, harg1⟩ ⟨_, hreach⟩
  have hrun :=
    (reachesPrefix_iff_runMir sumToNBody q.init q.steps q.init out.trace out.outcome).mp hreach
  rcases sumToN_verified_via_ranking_measure n q.init hblk0 harg1 with
    ⟨m, tr, hm_le, htr_le, hret, hterm_ge⟩
  rcases hret.to_runMir.2 q.steps with ⟨hsafe, hpartial⟩
  rw [hrun] at hsafe hpartial
  refine ⟨hsafe, ?_, ?_⟩
  · intro ret hout
    rcases hpartial ret hout with ⟨heq_v, heq_tr⟩
    dsimp at heq_tr
    rw [heq_tr]
    exact ⟨heq_v, htr_le⟩
  · intro hsteps
    have hfull := hterm_ge q.steps hsteps
    rw [hrun] at hfull
    injection hfull with htr_eq hout_eq
    rw [htr_eq]
    exact ⟨hout_eq, htr_le⟩

/-!
## Section 4: Task 3 — Diamond Join Cutpoints & `JCACHED` Subsumption

On a CFG containing a chain of $k$ sequential `switchInt` diamonds:
`bb_split_1 -> [bb_T_1, bb_F_1] -> bb_join_1 -> ... -> bb_join_k`:
- Naively unfolding the continuation at each `switchInt` duplicates the suffix
  CFG across both branches, generating $\sum_{i=1}^k 2^i = 2^{k+1} - 2$ branch
  verification conditions.
- Below we mechanize two complementary techniques that eliminate this $2^k$
  blowup in Lean `v4.34.1`:
  1. **Join-Block Cutpoint Summarization (`diamond_join_cutpoint`):**
     By cutting at `bb_join` with a join predicate `JoinInv : MirState → Prop`
     (mirroring RefinedRust's `type_goto_precond` at `program_rules.v:5074` and
     Aeneas's monadic `spec_bind'`), each diamond generates only **2** branch
     VCs to `bb_join` and verifies the continuation from `bb_join` **once**,
     collapsing $2^{k+1} - 2$ VCs to $2k$ linear VCs.
  2. **`JCached` Side-Condition Caching (`jcache_subsumes_shelvedVC`):**
     Mirroring RefinedRust's `JCACHED` (`proof_state.v:121–136`) and
     `cache_sidecond` (`automation.v:2114–2122`), once a pure obligation `P` is
     proved and entered into `JCached`, any duplicate
     `ShelvedVC span kind trace P` on subsequent diamond branches is discharged
     in $O(1)$ regardless of its branch trace `trace`.
-/

/-- Number of branch VCs generated by naive path-tree symbolic execution on a
chain of `k` sequential diamonds (`2^(k+1) - 2`). -/
def vcCountNaive : Nat → Nat
  | 0 => 0
  | k + 1 => 2 + 2 * vcCountNaive k

/-- Number of branch VCs generated with join-block cutpoints on a chain of `k`
sequential diamonds (`2 * k`). -/
def vcCountJoinCutpoint (k : Nat) : Nat :=
  2 * k

/-- Exact closed-form proof that `vcCountNaive k + 2 = 2 ^ (k + 1)`, confirming
exponential $\Theta(2^k)$ blowup without join cutpoints vs. linear $2k$ with
join cutpoints. -/
theorem vcCountNaive_closed_form (k : Nat) :
    vcCountNaive k + 2 = 2 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold vcCountNaive
    rw [Nat.pow_succ (2 : Nat) (n + 1)]
    omega

/-- For $k = 10$ sequential diamonds, join cutpoints reduce branch VCs from
$2046$ to $20$ (over $100\times$ reduction). -/
theorem vcCount_comparison_k10 :
    vcCountJoinCutpoint 10 = 20 ∧ vcCountNaive 10 = 2046 := by
  decide

/-- **Compositional Join-Block Cutpoint Theorem (`diamond_join_cutpoint`):**
Suppose a basic block `bb_split` branches via `guard : MirState → Bool`:
- When `guard s = true`, `MirMachine` reaches `bb_join` in `m₁ ≤ k_br` steps
  at a state `s'` satisfying `JoinInv s'` (Branch VC 1).
- When `guard s = false`, `MirMachine` reaches `bb_join` in `m₂ ≤ k_br` steps
  at a state `s'` satisfying `JoinInv s'` (Branch VC 2).
- From **any single** state `s'` at `bb_join` satisfying `JoinInv s'`,
  `MirMachine` reaches `.return v` with `Post v` in `m_rest ≤ k_rest` steps
  (Continuation VC proved **once**).

Then from `s` at `bb_split`, `MirMachine` reaches `.return v` with `Post v` in
at most `k_br + k_rest` steps! -/
theorem diamond_join_cutpoint
    (body : MirBody)
    (bb_split bb_join : Nat)
    (Pre JoinInv : MirState → Prop)
    (guard : MirState → Bool)
    (Post : MirVal → Prop)
    (k_br k_rest : Nat)
    (h_then : ∀ s, s.block = bb_split → Pre s → guard s = true →
      ∃ m₁ tr₁ s',
        m₁ ≤ k_br ∧
        ReachInSteps body m₁ s tr₁ s' ∧
        s'.block = bb_join ∧
        JoinInv s')
    (h_else : ∀ s, s.block = bb_split → Pre s → guard s = false →
      ∃ m₂ tr₂ s',
        m₂ ≤ k_br ∧
        ReachInSteps body m₂ s tr₂ s' ∧
        s'.block = bb_join ∧
        JoinInv s')
    (h_join_cont : ∀ s', s'.block = bb_join → JoinInv s' →
      ∃ m_rest tr_rest v,
        m_rest ≤ k_rest ∧
        ReachReturnInSteps body m_rest s' tr_rest v ∧
        Post v) :
    ∀ s, s.block = bb_split → Pre s →
      ∃ m tr v,
        m ≤ k_br + k_rest ∧
        ReachReturnInSteps body m s tr v ∧
        Post v := by
  intro s hblk hpre
  cases hguard : guard s with
  | true =>
    rcases h_then s hblk hpre hguard with ⟨m₁, tr₁, s', hm₁, hreach₁, hblk', hjoin⟩
    rcases h_join_cont s' hblk' hjoin with ⟨m_rest, tr_rest, v, hm_rest, hret, hpost⟩
    exact ⟨m₁ + m_rest, tr₁ ++ tr_rest, v, Nat.add_le_add hm₁ hm_rest,
      hreach₁.trans_return hret, hpost⟩
  | false =>
    rcases h_else s hblk hpre hguard with ⟨m₂, tr₂, s', hm₂, hreach₂, hblk', hjoin⟩
    rcases h_join_cont s' hblk' hjoin with ⟨m_rest, tr_rest, v, hm_rest, hret, hpost⟩
    exact ⟨m₂ + m_rest, tr₂ ++ tr_rest, v, Nat.add_le_add hm₂ hm_rest,
      hreach₂.trans_return hret, hpost⟩

/-- Source span metadata for `ShelvedVC`. -/
structure SourceSpan where
  file : String
  line : Nat
  col : Nat
  deriving DecidableEq, Repr

inductive ObligationKind where
  | arithmeticOverflow
  | postconditionViolation
  deriving DecidableEq, Repr

structure BranchTrace where
  span : SourceSpan
  condition : String
  taken : Bool
  deriving DecidableEq, Repr

/-- Shelved verification condition (`ShelvedVC`), mirroring RefinedRust's
`SHELVED_SIDECOND` tagged with `LAST_RUST_PROGRAM_POINT` and
`CASE_DISTINCTION_INFO`. -/
structure ShelvedVC (span : SourceSpan) (kind : ObligationKind)
    (trace : List BranchTrace) (goal : Prop) : Prop where
  intro ::
  proof : goal

/-- Joint side-condition cache (`JCached`), mirroring RefinedRust's
`Definition JCACHED {A : Type} (a : A) := a` in
`theories/refinedrust/rust_typing/automation/proof_state.v` (lines 121–136). -/
structure JCached (Cache : Prop) : Prop where
  intro ::
  proof : Cache

theorem init_jcache : JCached True := ⟨True.intro⟩

theorem enter_jcache {A B : Prop} (hb : B) (hcache : JCached A) :
    JCached (B ∧ A) :=
  ⟨⟨hb, hcache.proof⟩⟩

/-- **`JCACHED` Side-Condition Subsumption (`jcache_subsumes_shelvedVC`):**
Once a pure obligation `P` is entailed by the joint cache `JCached Cache`
(`Cache → P`), any `ShelvedVC span kind trace P`—under **any** branch trace
`trace : List BranchTrace`—is discharged immediately without re-running the
arithmetic solver! -/
theorem jcache_subsumes_shelvedVC
    {Cache P : Prop} (span : SourceSpan) (kind : ObligationKind)
    (trace : List BranchTrace)
    (hcache : JCached Cache)
    (hlookup : Cache → P) :
    ShelvedVC span kind trace P :=
  ⟨hlookup hcache.proof⟩

/-- **RefinedRust `cache_sidecond` Combinator in Lean 4
(`diamond_shelvedVC_cached_once`):**
When two diamond branches (`traceTrue` and `traceFalse`) both require the same
pure side condition `P` at `span` in their shared continuation, proving `P`
**once** and entering it into `JCached` simultaneously discharges both
`ShelvedVC span kind traceTrue P` and `ShelvedVC span kind traceFalse P`! -/
theorem diamond_shelvedVC_cached_once
    {Cache P : Prop} (span : SourceSpan) (kind : ObligationKind)
    (traceTrue traceFalse : List BranchTrace)
    (hcache : JCached Cache)
    (hp : P) :
    let hcache' := enter_jcache hp hcache
    have _ := hcache'
    ShelvedVC span kind traceTrue P ∧
    ShelvedVC span kind traceFalse P := by
  intro hcache'
  exact ⟨jcache_subsumes_shelvedVC span kind traceTrue hcache' And.left,
         jcache_subsumes_shelvedVC span kind traceFalse hcache' And.left⟩

/-- Concrete 2-diamond MIR CFG (`twoDiamondBody`):
```rust
pub fn two_diamond_clamp_and_add(x: usize, a: usize, b: usize) -> usize {
    // Diamond 1 (bb0 -> [bb1, bb2] -> bb3):
    let y = if x < 10 { x } else { 10 };
    // Diamond 2 (bb3 -> [bb4, bb5] -> bb6):
    let z = if y < 5 { y + 1 } else { y };
    // Continuation at bb6: checked bound a + b <= 1000, return z + a + b
    assert!(a <= 1000);
    z + a
}
```
-/
def twoDiamondBody : MirBody where
  argCount := 2
  blocks := [
    -- bb0 (split 1): _3 = (_1 < 10); switchInt _3 -> [false: bb2, true: bb1]
    { stmts := [.assignBinOp 3 .lt (.copy 1) (.constVal (.usize 10))]
      terminator := .switchInt (.copy 3) 2 1 },
    -- bb1 (then 1): _4 = _1; goto bb3
    { stmts := [.assignUse 4 (.copy 1)]
      terminator := .goto 3 },
    -- bb2 (else 1): _4 = 10; goto bb3
    { stmts := [.assignUse 4 (.constVal (.usize 10))]
      terminator := .goto 3 },
    -- bb3 (join 1 / split 2): _5 = (_4 < 5); switchInt _5 -> [false: bb5, true: bb4]
    { stmts := [.assignBinOp 5 .lt (.copy 4) (.constVal (.usize 5))]
      terminator := .switchInt (.copy 5) 5 4 },
    -- bb4 (then 2): _6 = _4 + 1; goto bb6
    { stmts := [.assignBinOp 6 .add (.copy 4) (.constVal (.usize 1))]
      terminator := .goto 6 },
    -- bb5 (else 2): _6 = _4; goto bb6
    { stmts := [.assignUse 6 (.copy 4)]
      terminator := .goto 6 },
    -- bb6 (join 2 / exit): assert(_2 <= 1000); _0 = _6 + _2; return _0
    { stmts := [
        .assertLe (.copy 2) (.constVal (.usize 1000)),
        .assignBinOp 0 .add (.copy 6) (.copy 2)
      ]
      terminator := .return_ (.copy 0) }
  ]

/-- Join invariant at `bb3` (after Diamond 1): `_4` holds `min x 10 ≤ 10`, and
`_2` still holds `a ≤ 1000`. -/
structure Join1Inv (a : Nat) (s : MirState) : Prop where
  local2 : s.locals 2 = some (.usize a)
  local4 : ∃ y, y ≤ 10 ∧ s.locals 4 = some (.usize y)

/-- Join invariant at `bb6` (after Diamond 2): `_6` holds `z ≤ 10`, and `_2`
still holds `a ≤ 1000`. -/
structure Join2Inv (a : Nat) (s : MirState) : Prop where
  local2 : s.locals 2 = some (.usize a)
  local6 : ∃ z, z ≤ 10 ∧ s.locals 6 = some (.usize z)

/-- Verification of `twoDiamondBody` via linear composition of two
`diamond_join_cutpoint` lemmas (2 VCs for Diamond 1 + 2 VCs for Diamond 2 + 1
continuation VC at `bb6`, never duplicating `bb3..bb6` across Diamond 1!). -/
theorem twoDiamondBody_verified_linear (x a : Nat) (ha : a ≤ 1000)
    (init : MirState) (hblk0 : init.block = 0)
    (hx : init.locals 1 = some (.usize x))
    (ha_loc : init.locals 2 = some (.usize a)) :
    ∃ m tr v,
      m ≤ 5 ∧
      ReachReturnInSteps twoDiamondBody m init tr v ∧
      ∃ z, z ≤ 10 ∧ v = .usize (z + a) := by
  -- Step 1: Prove the continuation at `bb6` ONCE under `Join2Inv a`.
  have h_bb6 : ∀ s6, s6.block = 6 → Join2Inv a s6 →
      ∃ m_rest tr_rest v,
        m_rest ≤ 1 ∧
        ReachReturnInSteps twoDiamondBody m_rest s6 tr_rest v ∧
        ∃ z, z ≤ 10 ∧ v = .usize (z + a) := by
    intro s6 hblk6 ⟨h2, z, hz_le, h6⟩
    have hstep6 : evalMirBlockStep twoDiamondBody s6 =
        .terminated (.normal (.usize (z + a))) := by
      cases s6 with
      | mk locals block =>
        dsimp at hblk6 h2 h6
        subst hblk6
        simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
          evalOperand, evalBinOp, h2, h6, ha, updateLocal]
    exact ⟨1, [], .usize (z + a), Nat.le_refl 1,
      ReachReturnInSteps.ret hstep6, ⟨z, hz_le, rfl⟩⟩
  -- Step 2: Prove Diamond 2 (`bb3 -> [bb4, bb5] -> bb6`) ONCE using `diamond_join_cutpoint`.
  have h_bb3 : ∀ s3, s3.block = 3 → Join1Inv a s3 →
      ∃ m₂ tr₂ v,
        m₂ ≤ 2 + 1 ∧
        ReachReturnInSteps twoDiamondBody m₂ s3 tr₂ v ∧
        ∃ z, z ≤ 10 ∧ v = .usize (z + a) := by
    apply diamond_join_cutpoint twoDiamondBody 3 6
      (Join1Inv a) (Join2Inv a)
      (fun s => match s.locals 4 with | some (.usize y) => decide (y < 5) | _ => false)
      (fun v => ∃ z, z ≤ 10 ∧ v = .usize (z + a))
      2 1
    · -- Diamond 2 `then` branch (`bb3 -> bb4 -> bb6`)
      intro s3 hblk3 ⟨h2, y, hy_le, h4⟩ hguard
      simp only [h4] at hguard
      have hlt5 : y < 5 := of_decide_eq_true hguard
      let loc_bb4 := updateLocal s3.locals 5 (some (.bool true))
      let s_bb4 : MirState := { locals := loc_bb4, block := 4 }
      let loc_bb6 := updateLocal loc_bb4 6 (some (.usize (y + 1)))
      let s_bb6 : MirState := { locals := loc_bb6, block := 6 }
      have hs1 : evalMirBlockStep twoDiamondBody s3 = .step StepObs.step s_bb4 := by
        cases s3 with
        | mk locals block =>
          dsimp at hblk3 h4
          subst hblk3
          simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
            evalOperand, evalBinOp, h4, hguard, s_bb4, loc_bb4, updateLocal]
      have hs2 : evalMirBlockStep twoDiamondBody s_bb4 = .step StepObs.step s_bb6 := by
        have h4' : loc_bb4 4 = some (.usize y) := h4
        simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
          evalOperand, evalBinOp, h4', s_bb4, s_bb6, loc_bb6]
      exact ⟨2, [StepObs.step, StepObs.step], s_bb6, Nat.le_refl 2,
        ReachInSteps.step hs1 (ReachInSteps.step hs2 (ReachInSteps.zero _)),
        rfl, ⟨h2, y + 1, by omega, rfl⟩⟩
    · -- Diamond 2 `else` branch (`bb3 -> bb5 -> bb6`)
      intro s3 hblk3 ⟨h2, y, hy_le, h4⟩ hguard
      simp only [h4] at hguard
      let loc_bb5 := updateLocal s3.locals 5 (some (.bool false))
      let s_bb5 : MirState := { locals := loc_bb5, block := 5 }
      let loc_bb6 := updateLocal loc_bb5 6 (some (.usize y))
      let s_bb6 : MirState := { locals := loc_bb6, block := 6 }
      have hs1 : evalMirBlockStep twoDiamondBody s3 = .step StepObs.step s_bb5 := by
        cases s3 with
        | mk locals block =>
          dsimp at hblk3 h4
          subst hblk3
          simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
            evalOperand, evalBinOp, h4, hguard, s_bb5, loc_bb5, updateLocal]
      have hs2 : evalMirBlockStep twoDiamondBody s_bb5 = .step StepObs.step s_bb6 := by
        have h4' : loc_bb5 4 = some (.usize y) := h4
        simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
          evalOperand, h4', s_bb5, s_bb6, loc_bb6]
      exact ⟨2, [StepObs.step, StepObs.step], s_bb6, Nat.le_refl 2,
        ReachInSteps.step hs1 (ReachInSteps.step hs2 (ReachInSteps.zero _)),
        rfl, ⟨h2, y, hy_le, rfl⟩⟩
    · exact h_bb6
  -- Step 3: Prove Diamond 1 (`bb0 -> [bb1, bb2] -> bb3`) using `diamond_join_cutpoint`
  -- chained into `h_bb3`.
  exact diamond_join_cutpoint twoDiamondBody 0 3
    (fun s => s.locals 1 = some (.usize x) ∧ s.locals 2 = some (.usize a))
    (Join1Inv a)
    (fun _ => decide (x < 10))
    (fun v => ∃ z, z ≤ 10 ∧ v = .usize (z + a))
    2 3
    (by
      intro s0 hblk ⟨h1, h2⟩ hguard
      have hlt10 : x < 10 := of_decide_eq_true hguard
      let loc_bb1 := updateLocal s0.locals 3 (some (.bool true))
      let s_bb1 : MirState := { locals := loc_bb1, block := 1 }
      let loc_bb3 := updateLocal loc_bb1 4 (some (.usize x))
      let s_bb3 : MirState := { locals := loc_bb3, block := 3 }
      have hs1 : evalMirBlockStep twoDiamondBody s0 = .step StepObs.step s_bb1 := by
        cases s0 with
        | mk locals block =>
          dsimp at hblk h1
          subst hblk
          simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
            evalOperand, evalBinOp, h1, hguard, s_bb1, loc_bb1, updateLocal]
      have hs2 : evalMirBlockStep twoDiamondBody s_bb1 = .step StepObs.step s_bb3 := by
        have h1' : loc_bb1 1 = some (.usize x) := h1
        simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
          evalOperand, h1', s_bb1, s_bb3, loc_bb3]
      exact ⟨2, [StepObs.step, StepObs.step], s_bb3, Nat.le_refl 2,
        ReachInSteps.step hs1 (ReachInSteps.step hs2 (ReachInSteps.zero _)),
        rfl, ⟨h2, x, by omega, rfl⟩⟩)
    (by
      intro s0 hblk ⟨h1, h2⟩ hguard
      let loc_bb2 := updateLocal s0.locals 3 (some (.bool false))
      let s_bb2 : MirState := { locals := loc_bb2, block := 2 }
      let loc_bb3 := updateLocal loc_bb2 4 (some (.usize 10))
      let s_bb3 : MirState := { locals := loc_bb3, block := 3 }
      have hs1 : evalMirBlockStep twoDiamondBody s0 = .step StepObs.step s_bb2 := by
        cases s0 with
        | mk locals block =>
          dsimp at hblk h1
          subst hblk
          simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
            evalOperand, evalBinOp, h1, hguard, s_bb2, loc_bb2, updateLocal]
      have hs2 : evalMirBlockStep twoDiamondBody s_bb2 = .step StepObs.step s_bb3 := by
        simp [evalMirBlockStep, twoDiamondBody, evalStmts, evalStmt,
          evalOperand, s_bb2, s_bb3, loc_bb3]
      exact ⟨2, [StepObs.step, StepObs.step], s_bb3, Nat.le_refl 2,
        ReachInSteps.step hs1 (ReachInSteps.step hs2 (ReachInSteps.zero _)),
        rfl, ⟨h2, 10, Nat.le_refl 10, rfl⟩⟩)
    h_bb3
    init hblk0 ⟨hx, ha_loc⟩

/-!
## Section 5: Task 4 — `TrackedFuncLang` to 2-Safety Constant-Time
-/

/-- Relational 2-safety constant-time property (`ConstantTime2Safety`) over
`MirMachine`: for any two initial states `s₁` and `s₂` that are
public-equivalent (`PubEquiv s₁ s₂`) and any step budget `steps : Nat`, both
executions are safe and emit identical observation traces
(`out₁.trace = out₂.trace`) and identical step counts
(`out₁.trace.length = out₂.trace.length`). -/
def ConstantTime2Safety (PubEquiv : MirState → MirState → Prop)
    (body : MirBody) : Prop :=
  ∀ (s₁ s₂ : MirState) (steps : Nat),
    MirMachine.initState body s₁ →
    MirMachine.initState body s₂ →
    PubEquiv s₁ s₂ →
    ∃ (hDef₁ : (BehaviorOf MirMachine body ⟨s₁, steps⟩).defined)
      (hDef₂ : (BehaviorOf MirMachine body ⟨s₂, steps⟩).defined),
      ∀ (out₁ out₂ : ExecOut StepObs MirVal),
        (BehaviorOf MirMachine body ⟨s₁, steps⟩).val hDef₁ out₁ →
        (BehaviorOf MirMachine body ⟨s₂, steps⟩).val hDef₂ out₂ →
        out₁.trace = out₂.trace ∧
        out₁.trace.length = out₂.trace.length

/-- Relational predicate `BranchAligned plan body s₁ s₂` stating that two
executions of `evalSymTracked plan body` from `s₁` and `s₂` take identical
branch decisions (`cond₁ = cond₂`) at every `switchInt` along `plan`. -/
def BranchAligned : TransPlan → MirBody → MirState → MirState → Prop
  | .ret, _, _, _ => True
  | .step next, body, s₁, s₂ =>
    match evalMirBlockStep body s₁, evalMirBlockStep body s₂ with
    | .step _ s₁', .step _ s₂' => BranchAligned next body s₁' s₂'
    | _, _ => False
  | .branch falsePlan truePlan, body, s₁, s₂ =>
    match evalBranchBlock body s₁, evalBranchBlock body s₂ with
    | some (cond₁, s₁'), some (cond₂, s₂') =>
      cond₁ = cond₂ ∧
      if cond₁ then
        BranchAligned truePlan body s₁' s₂'
      else
        BranchAligned falsePlan body s₁' s₂'
    | _, _ => False
  | .fail, _, _, _ => False

/-- **Relational Trace-Equality Theorem for `TrackedFuncLang`
(`evalSymTracked_trace_eq_of_branchAligned`):**
If two executions of `evalSymTracked plan body` from `s₁` and `s₂` both succeed
with `.ok (t₁, v₁)` and `.ok (t₂, v₂)` and take identical branch decisions at
every `switchInt` (`BranchAligned plan body s₁ s₂`), then their
`TrackedFuncLang` observation traces and step counts are equal
(`t₁ = t₂ ∧ t₁.length = t₂.length`)! -/
theorem evalSymTracked_trace_eq_of_branchAligned (plan : TransPlan)
    (body : MirBody) :
    ∀ (s₁ s₂ : MirState) (t₁ t₂ : List StepObs) (v₁ v₂ : MirVal),
      evalSymTracked plan body s₁ = .ok (t₁, v₁) →
      evalSymTracked plan body s₂ = .ok (t₂, v₂) →
      BranchAligned plan body s₁ s₂ →
      t₁ = t₂ ∧ t₁.length = t₂.length := by
  induction plan with
  | ret =>
    intro s₁ s₂ t₁ t₂ v₁ v₂ hev₁ hev₂ _
    unfold evalSymTracked at hev₁ hev₂
    repeat (split at hev₁ <;> try contradiction)
    repeat (split at hev₂ <;> try contradiction)
    injection hev₁ with hp₁
    injection hp₁ with ht₁ _
    injection hev₂ with hp₂
    injection hp₂ with ht₂ _
    subst ht₁ ht₂
    exact ⟨rfl, rfl⟩
  | step next ih =>
    intro s₁ s₂ t₁ t₂ v₁ v₂ hev₁ hev₂ halign
    unfold evalSymTracked at hev₁ hev₂
    unfold BranchAligned at halign
    cases hs₁ : evalMirBlockStep body s₁ with
    | terminated _ => rw [hs₁] at hev₁; cases hev₁
    | choice _ _ => rw [hs₁] at hev₁; cases hev₁
    | failed _ => rw [hs₁] at hev₁; cases hev₁
    | step obs₁ s₁' =>
      cases hs₂ : evalMirBlockStep body s₂ with
      | terminated _ => rw [hs₂] at hev₂; cases hev₂
      | choice _ _ => rw [hs₂] at hev₂; cases hev₂
      | failed _ => rw [hs₂] at hev₂; cases hev₂
      | step obs₂ s₂' =>
        rw [hs₁, hs₂] at halign
        rw [hs₁] at hev₁
        rw [hs₂] at hev₂
        dsimp only at hev₁ hev₂
        cases hn₁ : evalSymTracked next body s₁' with
        | fail => rw [hn₁] at hev₁; cases hev₁
        | inapplicable => rw [hn₁] at hev₁; cases hev₁
        | ok tv₁' =>
          rcases tv₁' with ⟨t₁', v₁'⟩
          rw [hn₁] at hev₁
          injection hev₁ with hp₁
          injection hp₁ with ht₁ _
          cases hn₂ : evalSymTracked next body s₂' with
          | fail => rw [hn₂] at hev₂; cases hev₂
          | inapplicable => rw [hn₂] at hev₂; cases hev₂
          | ok tv₂' =>
            rcases tv₂' with ⟨t₂', v₂'⟩
            rw [hn₂] at hev₂
            injection hev₂ with hp₂
            injection hp₂ with ht₂ _
            rcases ih s₁' s₂' t₁' t₂' v₁' v₂' hn₁ hn₂ halign with ⟨heq_t, _⟩
            cases obs₁
            cases obs₂
            subst ht₁ ht₂ heq_t
            exact ⟨rfl, rfl⟩
  | branch falsePlan truePlan ihFalse ihTrue =>
    intro s₁ s₂ t₁ t₂ v₁ v₂ hev₁ hev₂ halign
    unfold evalSymTracked at hev₁ hev₂
    unfold BranchAligned at halign
    cases hb₁ : evalBranchBlock body s₁ with
    | none => rw [hb₁] at hev₁; cases hev₁
    | some p₁ =>
      rcases p₁ with ⟨cond₁, s₁'⟩
      cases hb₂ : evalBranchBlock body s₂ with
      | none => rw [hb₂] at hev₂; cases hev₂
      | some p₂ =>
        rcases p₂ with ⟨cond₂, s₂'⟩
        rw [hb₁, hb₂] at halign
        rcases halign with ⟨hcond_eq, halign_br⟩
        subst hcond_eq
        rw [hb₁] at hev₁
        rw [hb₂] at hev₂
        cases cond₁ with
        | false =>
          dsimp only at hev₁ hev₂ halign_br
          cases hn₁ : evalSymTracked falsePlan body s₁' with
          | fail => rw [hn₁] at hev₁; cases hev₁
          | inapplicable => rw [hn₁] at hev₁; cases hev₁
          | ok tv₁' =>
            rcases tv₁' with ⟨t₁', v₁'⟩
            rw [hn₁] at hev₁
            injection hev₁ with hp₁
            injection hp₁ with ht₁ _
            cases hn₂ : evalSymTracked falsePlan body s₂' with
            | fail => rw [hn₂] at hev₂; cases hev₂
            | inapplicable => rw [hn₂] at hev₂; cases hev₂
            | ok tv₂' =>
              rcases tv₂' with ⟨t₂', v₂'⟩
              rw [hn₂] at hev₂
              injection hev₂ with hp₂
              injection hp₂ with ht₂ _
              rcases ihFalse s₁' s₂' t₁' t₂' v₁' v₂' hn₁ hn₂ halign_br with ⟨heq_t, _⟩
              subst ht₁ ht₂ heq_t
              exact ⟨rfl, rfl⟩
        | true =>
          dsimp only at hev₁ hev₂ halign_br
          cases hn₁ : evalSymTracked truePlan body s₁' with
          | fail => rw [hn₁] at hev₁; cases hev₁
          | inapplicable => rw [hn₁] at hev₁; cases hev₁
          | ok tv₁' =>
            rcases tv₁' with ⟨t₁', v₁'⟩
            rw [hn₁] at hev₁
            injection hev₁ with hp₁
            injection hp₁ with ht₁ _
            cases hn₂ : evalSymTracked truePlan body s₂' with
            | fail => rw [hn₂] at hev₂; cases hev₂
            | inapplicable => rw [hn₂] at hev₂; cases hev₂
            | ok tv₂' =>
              rcases tv₂' with ⟨t₂', v₂'⟩
              rw [hn₂] at hev₂
              injection hev₂ with hp₂
              injection hp₂ with ht₂ _
              rcases ihTrue s₁' s₂' t₁' t₂' v₁' v₂' hn₁ hn₂ halign_br with ⟨heq_t, _⟩
              subst ht₁ ht₂ heq_t
              exact ⟨rfl, rfl⟩
  | fail =>
    intro _ _ _ _ _ _ hev₁
    cases hev₁

/-- **Bridge Theorem from `TrackedFuncLang` to `ConstantTime2Safety`
(`trackedFuncLang_implies_constantTime2Safety`):**
If for any two initial states `s₁, s₂` with `PubEquiv s₁ s₂`:
1. `symPlan s₁ = symPlan s₂` (the translation plan depends only on public
   inputs),
2. `evalSymWithTracked symPlan body s₁` and `evalSymWithTracked symPlan body s₂`
   both succeed (`.ok`), and
3. `BranchAligned (symPlan s₁) body s₁ s₂` holds (both runs take identical
   branch decisions at every `switchInt`),

then `body` satisfies `ConstantTime2Safety PubEquiv body` on `MirMachine`
across **all** step budgets `steps : Nat`! -/
theorem trackedFuncLang_implies_constantTime2Safety
    (PubEquiv : MirState → MirState → Prop)
    (symPlan : SymPlan) (body : MirBody)
    (h_plan_pub : ∀ s₁ s₂,
      MirMachine.initState body s₁ →
      MirMachine.initState body s₂ →
      PubEquiv s₁ s₂ →
      symPlan s₁ = symPlan s₂)
    (h_aligned : ∀ s₁ s₂,
      MirMachine.initState body s₁ →
      MirMachine.initState body s₂ →
      PubEquiv s₁ s₂ →
      (∃ t₁ v₁, evalSymWithTracked symPlan body s₁ = .ok (t₁, v₁)) ∧
      (∃ t₂ v₂, evalSymWithTracked symPlan body s₂ = .ok (t₂, v₂)) ∧
      BranchAligned (symPlan s₁) body s₁ s₂) :
    ConstantTime2Safety PubEquiv body := by
  intro s₁ s₂ steps hinit₁ hinit₂ hpub
  have hplan_eq := h_plan_pub s₁ s₂ hinit₁ hinit₂ hpub
  rcases h_aligned s₁ s₂ hinit₁ hinit₂ hpub with
    ⟨⟨t₁, v₁, hev₁⟩, ⟨t₂, v₂, hev₂⟩, hbr⟩
  unfold evalSymWithTracked at hev₁ hev₂
  rw [← hplan_eq] at hev₂
  rcases evalSymTracked_trace_eq_of_branchAligned (symPlan s₁) body s₁ s₂ t₁ t₂ v₁ v₂
      hev₁ hev₂ hbr with ⟨ht_eq, _⟩
  subst ht_eq
  have habs₁ := evalSymWithTracked_sound symPlan body ⟨s₁, steps⟩
  have habs₂ := evalSymWithTracked_sound symPlan body ⟨s₂, steps⟩
  have hdef_f₁ : (π_tracked (TrackedFuncLang.sem (evalSymWithTracked symPlan body)) ⟨s₁, steps⟩).defined := by
    intro hfail
    change evalSymTracked (symPlan s₁) body s₁ = .fail at hfail
    rw [hev₁] at hfail
    cases hfail
  have hdef_f₂ : (π_tracked (TrackedFuncLang.sem (evalSymWithTracked symPlan body)) ⟨s₂, steps⟩).defined := by
    intro hfail
    change evalSymTracked (symPlan s₂) body s₂ = .fail at hfail
    rw [← hplan_eq, hev₂] at hfail
    cases hfail
  rcases habs₁ hdef_f₁ with ⟨hDef₁, hVal₁⟩
  rcases habs₂ hdef_f₂ with ⟨hDef₂, hVal₂⟩
  refine ⟨hDef₁, hDef₂, ?_⟩
  intro out₁ out₂ hout₁ hout₂
  rcases hVal₁ out₁ hout₁ with ⟨_, _, ⟨t₁', v₁', htv₁, hle₁, hgt₁⟩⟩
  rcases hVal₂ out₂ hout₂ with ⟨_, _, ⟨t₂', v₂', htv₂, hle₂, hgt₂⟩⟩
  change evalSymTracked (symPlan s₁) body s₁ = .ok (t₁', v₁') at htv₁
  change evalSymTracked (symPlan s₂) body s₂ = .ok (t₂', v₂') at htv₂
  rw [← hplan_eq] at htv₂
  rw [hev₁] at htv₁
  rw [hev₂] at htv₂
  injection htv₁ with hp₁; injection hp₁ with ht₁' _
  injection htv₂ with hp₂; injection hp₂ with ht₂' _
  subst ht₁' ht₂'
  by_cases hle : steps ≤ t₁.length
  · rcases hle₁ hle with ⟨_, htr₁, _⟩
    rcases hle₂ hle with ⟨_, htr₂, _⟩
    rw [htr₁, htr₂]
    exact ⟨rfl, rfl⟩
  · have hgt : t₁.length < steps := by omega
    rcases hgt₁ hgt with ⟨_, htr₁⟩
    rcases hgt₂ hgt with ⟨_, htr₂⟩
    rw [htr₁, htr₂]
    exact ⟨rfl, rfl⟩

/-- Concrete demonstration of `trackedFuncLang_implies_constantTime2Safety`:
A cryptographic masking subroutine (`ctPublicModeXorBody`) with public mode
parameter `_1 : bool` (`pub_mode`) and secret key/message parameters
`_2, _3 : usize` (`secret_x`, `secret_mask`):
```rust
pub fn ct_public_mode_xor(pub_mode: bool, secret_x: usize, secret_mask: usize) -> usize {
    if pub_mode {
        secret_x ^ secret_mask
    } else {
        secret_x ^ 0xff
    }
}
```
Even though `ct_public_mode_xor` contains a `switchInt` branch and computes on
secret locals `_2` and `_3`, its branch condition depends solely on the public
input `_1`, so `BranchAligned` holds for any two states agreeing on `_1`! -/
def ctPublicModeXorBody : MirBody where
  argCount := 3
  blocks := [
    -- bb0: switchInt _1 -> [false: bb2, true: bb1]
    { stmts := []
      terminator := .switchInt (.copy 1) 2 1 },
    -- bb1: _0 = _2 ^ _3; return _0
    { stmts := [.assignBinOp 0 .bitXor (.copy 2) (.copy 3)]
      terminator := .return_ (.copy 0) },
    -- bb2: _0 = _2 ^ 255; return _0
    { stmts := [.assignBinOp 0 .bitXor (.copy 2) (.constVal (.usize 255))]
      terminator := .return_ (.copy 0) }
  ]

def ctPublicModePlan : SymPlan :=
  fun _ => .branch .ret .ret

/-- Public equivalence for `ctPublicModeXorBody`: two states agree on the public
mode boolean in local `_1`, while secret locals `_2` and `_3` may hold arbitrary
distinct `.usize` values. -/
def PubEquivMode (s₁ s₂ : MirState) : Prop :=
  (∃ mode : Bool, s₁.locals 1 = some (.bool mode) ∧ s₂.locals 1 = some (.bool mode)) ∧
  (∃ x₁ m₁ : Nat, s₁.locals 2 = some (.usize x₁) ∧ s₁.locals 3 = some (.usize m₁)) ∧
  (∃ x₂ m₂ : Nat, s₂.locals 2 = some (.usize x₂) ∧ s₂.locals 3 = some (.usize m₂))

/-- End-to-end proof that `ctPublicModeXorBody` satisfies `ConstantTime2Safety`
via `trackedFuncLang_implies_constantTime2Safety`. -/
theorem ctPublicModeXor_is_constant_time :
    ConstantTime2Safety PubEquivMode ctPublicModeXorBody := by
  apply trackedFuncLang_implies_constantTime2Safety PubEquivMode ctPublicModePlan
  · intros
    rfl
  · intro s₁ s₂ ⟨hblk₁, _⟩ ⟨hblk₂, _⟩ ⟨⟨mode, hm₁, hm₂⟩, ⟨x₁, k₁, hx₁, hk₁⟩, ⟨x₂, k₂, hx₂, hk₂⟩⟩
    cases s₁ with
    | mk loc₁ blk₁ =>
      cases s₂ with
      | mk loc₂ blk₂ =>
        dsimp at hblk₁ hblk₂ hm₁ hm₂ hx₁ hk₁ hx₂ hk₂
        subst hblk₁ hblk₂
        cases mode with
        | false =>
          refine ⟨⟨[StepObs.step], .usize (Nat.xor x₁ 255), ?_⟩,
                  ⟨[StepObs.step], .usize (Nat.xor x₂ 255), ?_⟩, ?_⟩
          · simp [evalSymWithTracked, ctPublicModePlan, evalSymTracked,
              evalBranchBlock, ctPublicModeXorBody, evalMirBlockStep,
              evalStmts, evalStmt, evalOperand, evalBinOp, updateLocal,
              hm₁, hx₁]
          · simp [evalSymWithTracked, ctPublicModePlan, evalSymTracked,
              evalBranchBlock, ctPublicModeXorBody, evalMirBlockStep,
              evalStmts, evalStmt, evalOperand, evalBinOp, updateLocal,
              hm₂, hx₂]
          · simp [ctPublicModePlan, BranchAligned, evalBranchBlock,
              ctPublicModeXorBody, evalStmts, evalOperand, hm₁, hm₂]
        | true =>
          refine ⟨⟨[StepObs.step], .usize (Nat.xor x₁ k₁), ?_⟩,
                  ⟨[StepObs.step], .usize (Nat.xor x₂ k₂), ?_⟩, ?_⟩
          · simp [evalSymWithTracked, ctPublicModePlan, evalSymTracked,
              evalBranchBlock, ctPublicModeXorBody, evalMirBlockStep,
              evalStmts, evalStmt, evalOperand, evalBinOp, updateLocal,
              hm₁, hx₁, hk₁]
          · simp [evalSymWithTracked, ctPublicModePlan, evalSymTracked,
              evalBranchBlock, ctPublicModeXorBody, evalMirBlockStep,
              evalStmts, evalStmt, evalOperand, evalBinOp, updateLocal,
              hm₂, hx₂, hk₂]
          · simp [ctPublicModePlan, BranchAligned, evalBranchBlock,
              ctPublicModeXorBody, evalStmts, evalOperand, hm₁, hm₂]

end Theory
end Anneal.R2Probe

#print axioms Anneal.R2Probe.Theory.evalSymWithTracked_sound
#print axioms Anneal.R2Probe.Theory.trackedFuncLang_exact_trace_length_at_steps
#print axioms Anneal.R2Probe.Theory.trackedFuncLang_adequacy_specOn
#print axioms Anneal.R2Probe.Theory.loop_spec_decr_nat
#print axioms Anneal.R2Probe.Theory.tracked_loop_spec_decr_nat
#print axioms Anneal.R2Probe.Theory.sumToN_verified_via_ranking_measure
#print axioms Anneal.R2Probe.Theory.sumToN_satisfies_fuelFree_specOn
#print axioms Anneal.R2Probe.Theory.diamond_join_cutpoint
#print axioms Anneal.R2Probe.Theory.twoDiamondBody_verified_linear
#print axioms Anneal.R2Probe.Theory.evalSymTracked_trace_eq_of_branchAligned
#print axioms Anneal.R2Probe.Theory.trackedFuncLang_implies_constantTime2Safety
#print axioms Anneal.R2Probe.Theory.ctPublicModeXor_is_constant_time
