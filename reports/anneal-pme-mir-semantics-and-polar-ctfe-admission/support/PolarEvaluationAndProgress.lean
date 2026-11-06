-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Polar CTFE Evaluation and Step-Dilated Progress Preservation in Anneal

This standalone Lean 4 (`v4.34.1`) mechanization investigates and resolves two
foundational soundness questions in Anneal's small-step operational semantics
and refinement framework (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`,
`Trusted/MirSemantics.lean` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`, and
`Trusted/X86Semantics.lean`, `theory/Anneal/Compiler/NaiveCodegen.lean` at
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`):

1. **Negative-Polarity `.stuck` Fail-Open Inversion in CTFE Admission:**
   In `Trusted/StepResult.lean`, `ReachesPrefix` records `.stuck` (with
   `PrefixOutcome.isSafe .stuck = False`) whenever a state has no outgoing step
   or an empty nondeterministic choice set. In positive positions (evaluating
   the runtime body on the left-hand side of `≤`), `.stuck` is fail-closed.
   However, `Trusted/MirSemantics.lean` reuses `ReachesPrefix` inside
   `ConstSucceeds` and places `MonoAdmitted` in the negative (premise) position
   of `initMirState`. When a `requiredConsts` entry reaches `.stuck` (modeling
   an unsupported CTFE feature), `ConstSucceeds` becomes `False`, `MonoAdmitted`
   becomes `False`, `initMirState` becomes `False`, and `MirSem` collapses to
   `Partial.bot`—vacuously certifying an unconditionally UB-exhibiting runtime
   function as `MirLang.WellFormed` and `MirLang.Spec (fun _ _ => False)`.
   Moreover, `non_vacuity_at_every_depth` (`TotalStep` + `InhabitedDemonic`)
   does not detect this collapse because it assumes `M.initState p init` as a
   hypothesis rather than requiring `∃ init, M.initState p init`.

2. **Infinite-Loop and Unwind Progress Collapse in `Compiles` and
   Functional Specifications:**
   Because `PrefixOutcome.isSafe .running = True` and
   `PrefixOutcome.isSafe (.terminated .unwind) = True`, and because
   `EnsuresRetLibInv`, `EnsuresEqArg`, and `EnsuresConst` guard their
   postconditions behind `out.outcome = .terminated (.normal ret) → ...`, a
   degenerate compiler pass `loopCodegen` (emitting `bb0: jmp bb0`) or
   `unwindCodegen` (emitting `bb0: call abort`) produces an `X86Body` that
   satisfies `X86Lang.WellFormed`, `EnsuresRetLibInv`, `EnsuresEqArg`, and
   `EnsuresConst` for every input `MirBody`. We design and prove a 100%
   constructive (zero `Classical.choice`, zero coinduction) **step-dilated
   prefix simulation** (`π_dilated k`) and **bounded total specification**
   (`SpecTotalOn m₀`) that leverage the fuel-absorption property of
   `ReachesPrefix.terminated` to reject `loopCodegen` and `unwindCodegen` on
   all terminating programs while admitting $1 \to [1..k]$ variable instruction
   expansion and legitimate source infinite loops and unwinds.
-/

namespace PolarEvaluationAndProgress

/-!
## 1. Baseline Trusted Core Definitions (`Trusted/Refinement.lean` & `Trusted/StepResult.lean`)
-/

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

/-- Partially defined behavior carrier $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- The bottom element ($\bot$) of `Partial (Out → Prop)`: unconditionally
    defined (`defined := True`) with an empty outcome set (`fun _ _ => False`). -/
def Partial.bot {Out : Type u} : Partial (Out → Prop) where
  defined := True
  val _ _ := False

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
  PolarEvaluationAndProgress.Behavior L.Query L.Out

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

structure TrustPolicy (A : Type) where
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

/-- Distinguishes normal return from panic/unwind completion. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Single-step transition outcome (`Trusted/StepResult.lean`). -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Finite-prefix execution outcome (`Trusted/StepResult.lean`). -/
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

/-- Alias matching the `.incomplete` terminology for an unexhausted prefix. -/
abbrev PrefixOutcome.incomplete {Val : Type} : PrefixOutcome Val :=
  .running

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed => False
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

/-- Inductive prefix reachability (`Trusted/StepResult.lean`). -/
inductive ReachesPrefix
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      step p s (.choice branches) →
      branches s' →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix step p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      step p s (.terminated term) →
      ReachesPrefix step p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      step p s .failed →
      ReachesPrefix step p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, step p s r) →
      ReachesPrefix step p (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M.step p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M.step p q.steps q.init out.trace out.outcome
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
  ∀ (p : Prog) (s : State) (branches : State → Prop),
    M.step p s (.choice branches) → ∃ s', branches s'

theorem exists_reaches_prefix
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (n : Nat) :
    ∀ (s : State),
      ∃ tr out, ReachesPrefix M.step p n s tr out ∧ out ≠ .stuck := by
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
      | choice branches =>
        cases h_dem p s branches hstep with
        | intro s' hbranch =>
          cases ih s' with
          | intro tr hrest =>
            cases hrest with
            | intro out hpair =>
              exact ⟨tr, out,
                ReachesPrefix.choice k s s' branches tr out hstep hbranch hpair.1,
                hpair.2⟩
      | terminated term =>
        exact ⟨[], .terminated term,
          ReachesPrefix.terminated k s term hstep,
          by intro h; cases h⟩
      | failed =>
        exact ⟨[], .failed,
          ReachesPrefix.failed k s hstep,
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
      ReachesPrefix M.step p n init out.trace out.outcome ∧
      out.outcome ≠ .stuck := by
  cases exists_reaches_prefix h_tot h_dem p n init with
  | intro tr hrest =>
    cases hrest with
    | intro oc hpair =>
      exact ⟨{ trace := tr, outcome := oc }, h_init, hpair.1, hpair.2⟩

/-!
## 2. Baseline MIR AST and Operational Semantics (`Trusted/MirAst.lean` & `Trusted/MirSemantics.lean`)
-/

structure LocalId where
  index : Nat

structure BlockId where
  index : Nat

inductive MirTy where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | ref (inner : MirTy)

inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | bytes (sz : Nat) (bits : Nat)
  | ref (loc : LocalId)

inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

inductive BinOp where
  | eq

inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | aggregate (adtId : Nat) (op : Operand)
  | field0 (src : LocalId)
  | ref (src : LocalId)
  | reborrow (src : LocalId)

inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop
  /-- Represents an unmodeled MIR/CTFE construct that has no transition in the
      partial small-step semantics, stepping to `PrefixOutcome.stuck` via
      `ReachesPrefix.noStep`. -/
  | unmodeled

mutual
  inductive Terminator where
    | return_
    | goto (target : BlockId)
    | unreachable
    | panic
    | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
    | callSizeOf (dst : LocalId) (ty : MirTy) (target : BlockId)
    | callTransmuteCopy (dst : LocalId) (srcTy dstTy : MirTy) (op : Operand)
        (target : BlockId)
    | call1 (dst : LocalId) (callee : MirBody) (arg : Operand) (target : BlockId)
        (typeArgs : List MirTy := [])

  structure BasicBlock where
    stmts : List Stmt
    terminator : Terminator

  structure MirBody where
    argTys : List MirTy
    retTy : MirTy
    localCount : Nat
    blocks : List BasicBlock
    requiredConsts : List MirBody := []
end

structure StackFrame where
  callerBody : MirBody
  callerLocals : Nat → Option MirVal
  callerTySizes : Nat → Nat := fun _ => 0
  retDst : LocalId
  retBlock : Nat

structure MirState where
  locals : Nat → Option MirVal
  block : Nat
  stmtIdx : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option MirBody := none
  stack : List StackFrame := []

def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

def evalTyByteSize (tySizes : Nat → Nat) (ty : MirTy) : Nat :=
  match ty with
  | .usize => 8
  | .bool => 1
  | .unit => 0
  | .adt _ => 8
  | .param idx => tySizes idx
  | .ref _ => 8

def substTySizes (tySizes : Nat → Nat) (typeArgs : List MirTy)
    (idx : Nat) : Nat :=
  match typeArgs[idx]? with
  | some ty => evalTyByteSize tySizes ty
  | none => tySizes idx

abbrev AdtInv := Nat → MirVal → Prop

def defaultAdtInv : AdtInv :=
  fun _ _ => True

def MirVal.satisfiesInv (adtInv : AdtInv) (tySizes : Nat → Nat)
    (v : MirVal) (ty : MirTy) : Prop :=
  match ty, v with
  | .usize, .usize _ => True
  | .bool, .bool _ => True
  | .unit, .unit => True
  | .adt tyId, .adt vId (.usize n) => vId = tyId ∧ adtInv tyId (.usize n)
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .ref _, .ref _ => True
  | _, _ => False

abbrev MirVal.hasTy (tySizes : Nat → Nat) (v : MirVal) (ty : MirTy) : Prop :=
  v.satisfiesInv defaultAdtInv tySizes ty

def argsMatchInv (adtInv : AdtInv) (tySizes : Nat → Nat)
    (argTys : List MirTy) (locals : Nat → Option MirVal) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, locals k = some v ∧ v.satisfiesInv adtInv tySizes ty) ∧
      rest (k + 1))
    (fun k => ∀ j, k ≤ j → locals j = none)
    1

abbrev argsMatchLocals (tySizes : Nat → Nat) (argTys : List MirTy)
    (locals : Nat → Option MirVal) : Prop :=
  argsMatchInv defaultAdtInv tySizes argTys locals

def initEntryState (body : MirBody) (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.locals 0 = none ∧
  argsMatchLocals s.tySizes body.argTys s.locals

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
  | .constVal v => some (v, locals)

def evalBinOp (op : BinOp) (lhs rhs : MirVal) : Option MirVal :=
  match op, lhs, rhs with
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | _, _, _ => none

/-- Partial statement evaluation returning `none` on `Stmt.unmodeled` (so
    `ReachesPrefix.noStep` transitions to `.stuck`) and `some r` on all modeled
    statements. -/
def evalMirStmtOpt (s : MirState) (stmt : Stmt) :
    Option (StepResult MirState Unit MirVal) :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      some (.step () { s with
        locals := updateLocal locals' dst.index (some v)
        stmtIdx := s.stmtIdx + 1
      })
    | none => some .failed
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand s.locals lhs with
    | some (v1, locals1) =>
      match evalOperand locals1 rhs with
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some outVal =>
          some (.step () { s with
            locals := updateLocal locals2 dst.index (some outVal)
            stmtIdx := s.stmtIdx + 1
          })
        | none => some .failed
      | none => some .failed
    | none => some .failed
  | .assign dst (.aggregate adtId op) =>
    match evalOperand s.locals op with
    | some (v, locals') =>
      some (.step () { s with
        locals := updateLocal locals' dst.index (some (.adt adtId v))
        stmtIdx := s.stmtIdx + 1
      })
    | none => some .failed
  | .assign dst (.field0 src) =>
    match s.locals src.index with
    | some (.adt _ inner) =>
      some (.step () { s with
        locals := updateLocal s.locals dst.index (some inner)
        stmtIdx := s.stmtIdx + 1
      })
    | _ => some .failed
  | .assign dst (.ref src) =>
    match s.locals src.index with
    | some _ =>
      some (.step () { s with
        locals := updateLocal s.locals dst.index (some (.ref src))
        stmtIdx := s.stmtIdx + 1
      })
    | none => some .failed
  | .assign dst (.reborrow src) =>
    match s.locals src.index with
    | some (.ref target) =>
      match s.locals target.index with
      | some _ =>
        some (.step () { s with
          locals := updateLocal s.locals dst.index (some (.ref target))
          stmtIdx := s.stmtIdx + 1
        })
      | none => some .failed
    | _ => some .failed
  | .storageLive loc =>
    some (.step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    })
  | .storageDead loc =>
    some (.step () { s with
      locals := updateLocal s.locals loc.index none
      stmtIdx := s.stmtIdx + 1
    })
  | .nop =>
    some (.step () { s with stmtIdx := s.stmtIdx + 1 })
  | .unmodeled =>
    none

def evalTransmuteCopy (tySizes : Nat → Nat) (locals : Nat → Option MirVal)
    (srcTy dstTy : MirTy) (argVal : MirVal) : Option MirVal :=
  let srcSz := evalTyByteSize tySizes srcTy
  let dstSz := evalTyByteSize tySizes dstTy
  if decide (srcSz = dstSz) then
    match argVal with
    | .ref target =>
      match locals target.index with
      | some (.bytes vSz bits) =>
        if decide (vSz = srcSz) then
          some (.bytes dstSz bits)
        else
          none
      | _ => none
    | _ => none
  else
    none

def evalMirTerminator (activeBody : MirBody) (s : MirState)
    (term : Terminator) : StepResult MirState Unit MirVal :=
  match term with
  | .return_ =>
    match s.locals 0 with
    | none => .failed
    | some retVal =>
      match s.stack with
      | [] => .terminated (.normal retVal)
      | frame :: restStack =>
        .step () {
          locals := updateLocal frame.callerLocals frame.retDst.index (some retVal)
          block := frame.retBlock
          stmtIdx := 0
          tySizes := frame.callerTySizes
          curBody := if restStack.isEmpty then none else some frame.callerBody
          stack := restStack
        }
  | .goto target =>
    .step () { s with block := target.index, stmtIdx := 0 }
  | .unreachable =>
    .failed
  | .panic =>
    .terminated .unwind
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand s.locals discr with
    | some (.bool false, locals') =>
      .step () { s with locals := locals', block := falseTarget.index, stmtIdx := 0 }
    | some (.bool true, locals') =>
      .step () { s with locals := locals', block := trueTarget.index, stmtIdx := 0 }
    | _ => .failed
  | .callSizeOf dst ty target =>
    let sz := evalTyByteSize s.tySizes ty
    .step () { s with
      locals := updateLocal s.locals dst.index (some (.usize sz))
      block := target.index
      stmtIdx := 0
    }
  | .callTransmuteCopy dst srcTy dstTy op target =>
    match evalOperand s.locals op with
    | some (argVal, locals') =>
      match evalTransmuteCopy s.tySizes locals' srcTy dstTy argVal with
      | some outVal =>
        .step () { s with
          locals := updateLocal locals' dst.index (some outVal)
          block := target.index
          stmtIdx := 0
        }
      | none => .failed
    | none => .failed
  | .call1 dst callee arg target typeArgs =>
    match evalOperand s.locals arg with
    | some (argVal, callerLocals') =>
      let calleeLocals : Nat → Option MirVal :=
        updateLocal (fun _ => none) 1 (some argVal)
      let frame : StackFrame := {
        callerBody := activeBody
        callerLocals := callerLocals'
        callerTySizes := s.tySizes
        retDst := dst
        retBlock := target.index
      }
      .step () {
        locals := calleeLocals
        block := 0
        stmtIdx := 0
        tySizes := substTySizes s.tySizes typeArgs
        curBody := some callee
        stack := frame :: s.stack
      }
    | none => .failed

/-- Partial step evaluation (`none` on `Stmt.unmodeled`, `some r` otherwise). -/
def evalMirStepOpt (rootBody : MirBody) (s : MirState) :
    Option (StepResult MirState Unit MirVal) :=
  let active := s.curBody.getD rootBody
  match active.blocks[s.block]? with
  | none => some .failed
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some stmt => evalMirStmtOpt s stmt
    | none => some (evalMirTerminator active s bb.terminator)

/-- Relational step transition (`some r = evalMirStepOpt body s`). When
    `evalMirStepOpt body s = none` (at `Stmt.unmodeled`), `¬ ∃ r, MirStep body
    s r` holds and `ReachesPrefix.noStep` transitions to `PrefixOutcome.stuck`. -/
abbrev MirStep (body : MirBody) (s : MirState)
    (r : StepResult MirState Unit MirVal) : Prop :=
  some r = evalMirStepOpt body s

inductive RequiresConst :
    (Nat → Nat) → MirBody → (Nat → Nat) → MirBody → Prop where
  | direct {tySizes : Nat → Nat} {body c : MirBody} :
      c ∈ body.requiredConsts →
      RequiresConst tySizes body tySizes c
  | nested {tySizes tySizes' : Nat → Nat} {body c' c : MirBody} :
      c' ∈ body.requiredConsts →
      RequiresConst tySizes c' tySizes' c →
      RequiresConst tySizes body tySizes' c
  | call1 {tySizes tySizes' : Nat → Nat} {body callee c : MirBody}
      {bb : BasicBlock} {dst : LocalId} {arg : Operand} {target : BlockId}
      {typeArgs : List MirTy} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst callee arg target typeArgs →
      RequiresConst (substTySizes tySizes typeArgs) callee tySizes' c →
      RequiresConst tySizes body tySizes' c

/-- Baseline CTFE success predicate (`Trusted/MirSemantics.lean` line 585). -/
def ConstSucceeds (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  ∃ (s₀ : MirState) (n : Nat) (tr : List Unit) (v : MirVal),
    s₀.tySizes = tySizes ∧
    initEntryState c s₀ ∧
    ReachesPrefix MirStep c n s₀ tr (.terminated (.normal v))

/-- Baseline monomorphization admission predicate (`Trusted/MirSemantics.lean`
    line 597). -/
def MonoAdmitted (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c, RequiresConst tySizes body tySizes' c → ConstSucceeds tySizes' c

/-- Baseline initial state predicate (`Trusted/MirSemantics.lean` line 611). -/
def initMirState (body : MirBody) (s : MirState) : Prop :=
  initEntryState body s ∧ MonoAdmitted s.tySizes body

def MirMachine : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step := MirStep

def MirLang : Language :=
  MirMachine.toLanguage

abbrev MirSem (body : MirBody) : MirLang.Behavior :=
  MirLang.sem body

def EnsuresRetLibInv (adtInv : AdtInv) (retTy : MirTy)
    (pre : ExecQuery MirState → Prop) : MirLang.Behavior :=
  MirLang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ret.satisfiesInv adtInv q.init.tySizes retTy)

def EnsuresEqArg (argLocal : Nat) : MirLang.Behavior :=
  MirLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      q.init.locals argLocal = some ret)

/-!
## 3. Question 2.1 (Part 1): Mechanization of the Negative-Polarity `.stuck` Fail-Open Inversion
-/

/-- A constant MIR body that encounters an unmodeled construct in `bb0`,
    stepping to `.stuck` via `ReachesPrefix.noStep`. -/
def unmodeledConst : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := [.unmodeled]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- A runtime MIR body that unconditionally executes `Terminator.unreachable`
    (immediate UB, stepping to `.failed` at step 1), guarded by
    `requiredConsts := [unmodeledConst]`. -/
def buggyRuntimeFn : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := []
      terminator := .unreachable }
  ]
  requiredConsts := [unmodeledConst]

/-- In positive position, `unmodeledConst` reaches `.stuck` at step 1 and is
    rejected by `MirLang.WellFormed` (fail-closed in positive polarity). -/
theorem unmodeledConst_rejected_in_positive_position :
    ¬ (MirSem unmodeledConst ≤ MirLang.WellFormed) := by
  intro hWF
  let s₀ : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hentry : initEntryState unmodeledConst s₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hmono : MonoAdmitted (fun _ => 0) unmodeledConst := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState unmodeledConst s₀ := ⟨hentry, hmono⟩
  have hnostep : ¬ ∃ r, MirStep unmodeledConst s₀ r := by
    intro ⟨r, hr⟩
    cases hr
  have hstuck : ReachesPrefix MirStep unmodeledConst 1 s₀ [] .stuck :=
    ReachesPrefix.noStep 0 s₀ hnostep
  have hdef := (hWF { init := s₀, steps := 1 } True.intro).1
  exact hdef hinit [] .stuck hstuck

/-- From any entry state `s₀` of `unmodeledConst`, every reachable prefix has
    outcome `.running` (at `n = 0`) or `.stuck` (at `n = k + 1`), never
    `.terminated (.normal v)`. -/
theorem unmodeledConst_never_succeeds (tySizes : Nat → Nat) :
    ¬ ConstSucceeds tySizes unmodeledConst := by
  intro ⟨s₀, n, tr, v, _, hentry, hreach⟩
  have hb : s₀.block = 0 := hentry.1
  have hs : s₀.stmtIdx = 0 := hentry.2.1
  have hc : s₀.curBody = none := hentry.2.2.1
  have hstep : evalMirStepOpt unmodeledConst s₀ = none := by
    cases s₀ with
    | mk locals block stmtIdx tySizes0 curBody stack =>
      dsimp at hb hs hc
      subst hb hs hc
      rfl
  cases hreach with
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt unmodeledConst s₀ := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : some _ = evalMirStepOpt unmodeledConst s₀ := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : some _ = evalMirStepOpt unmodeledConst s₀ := h1
    rw [hstep] at h1'; cases h1'

/-- Because `unmodeledConst ∈ buggyRuntimeFn.requiredConsts`, `MonoAdmitted` is
    `False` for every `tySizes`. -/
theorem buggyRuntimeFn_not_monoAdmitted (tySizes : Nat → Nat) :
    ¬ MonoAdmitted tySizes buggyRuntimeFn := by
  intro hmono
  exact unmodeledConst_never_succeeds tySizes
    (hmono tySizes unmodeledConst (.direct (.head _)))

/-- Consequently, `initMirState buggyRuntimeFn s` is `False` for every state `s`. -/
theorem buggyRuntimeFn_no_initMirState (s : MirState) :
    ¬ initMirState buggyRuntimeFn s := by
  intro ⟨_, hmono⟩
  exact buggyRuntimeFn_not_monoAdmitted s.tySizes hmono

/-- Pointwise at every query `q`, `MirSem buggyRuntimeFn q` collapses to
    `Partial.bot` (`defined = True`, `val = False`). -/
theorem buggyRuntimeFn_sem_eq_bot (q : ExecQuery MirState) :
    MirSem buggyRuntimeFn q ≤ Partial.bot ∧
    Partial.bot ≤ MirSem buggyRuntimeFn q := by
  constructor
  · intro _
    refine ⟨fun hinit => False.elim (buggyRuntimeFn_no_initMirState q.init hinit), ?_⟩
    intro out ⟨hinit, _⟩
    exact False.elim (buggyRuntimeFn_no_initMirState q.init hinit)
  · intro _
    exact ⟨True.intro, fun _ h => False.elim h⟩

/-- **Fail-Open Polarity Inversion Theorem:**
    Even though `buggyRuntimeFn`'s runtime body is `Terminator.unreachable`
    (unconditional UB), attaching `unmodeledConst` (which steps to `.stuck`)
    causes `buggyRuntimeFn` to vacuously satisfy `MirLang.WellFormed` and the
    absurd specification `MirLang.Spec (fun _ _ => False)`! -/
theorem buggyRuntimeFn_vacuously_satisfies_false_spec :
    MirSem buggyRuntimeFn ≤ MirLang.WellFormed ∧
    MirSem buggyRuntimeFn ≤ MirLang.Spec (fun _ _ => False) := by
  constructor
  · intro q _
    refine ⟨fun hinit => False.elim (buggyRuntimeFn_no_initMirState q.init hinit), ?_⟩
    intro _ _
    exact True.intro
  · intro q _
    refine ⟨fun hinit => False.elim (buggyRuntimeFn_no_initMirState q.init hinit), ?_⟩
    intro _ ⟨hinit, _⟩
    exact False.elim (buggyRuntimeFn_no_initMirState q.init hinit)

/-!
### Why `TotalStep` + `InhabitedDemonic` (`non_vacuity_at_every_depth`) Did Not Catch This Vacuity

In `theory/Anneal/StepResult.lean`, `TotalStep M` and `InhabitedDemonic M`
constrain only `M.step`, while `non_vacuity_at_every_depth` takes
`(h_init : M.initState p init)` as an assumed premise rather than proving
`∃ init, M.initState p init`.

We verify this directly on the unmodified deterministic `MirMachineDet` (where
every state steps deterministically without `none` or `.choice`, so `TotalStep`
and `InhabitedDemonic` hold globally across all programs and states).
-/

def evalMirStepDet (rootBody : MirBody) (s : MirState) :
    StepResult MirState Unit MirVal :=
  (evalMirStepOpt rootBody s).getD .failed

def MirMachineDet : SmallStepMachine MirBody MirState Unit MirVal where
  initState := initMirState
  step body s r := r = evalMirStepDet body s

def MirLangDet : Language :=
  MirMachineDet.toLanguage

theorem mirMachineDet_total : TotalStep MirMachineDet :=
  fun body s => ⟨evalMirStepDet body s, rfl⟩

theorem mirMachineDet_inhabitedDemonic : InhabitedDemonic MirMachineDet := by
  intro body s branches hstep
  have h : StepResult.choice branches = evalMirStepDet body s := hstep
  dsimp [evalMirStepDet, evalMirStepOpt] at h
  revert h
  cases (s.curBody.getD body).blocks[s.block]? with
  | none => intro h; cases h
  | some bb =>
    intro h
    dsimp at h
    revert h
    cases bb.stmts[s.stmtIdx]? with
    | none =>
      cases bb.terminator with
      | return_ =>
        dsimp [evalMirTerminator]
        cases s.locals 0 with
        | none => intro h; cases h
        | some _ =>
          cases s.stack <;> (intro h; cases h)
      | goto _ => intro h; cases h
      | unreachable => intro h; cases h
      | panic => intro h; cases h
      | switchInt discr _ _ =>
        dsimp [evalMirTerminator]
        cases evalOperand s.locals discr with
        | none => intro h; cases h
        | some p =>
          cases p with
          | mk v locals' =>
            cases v with
            | bool b => cases b <;> (intro h; cases h)
            | _ => intro h; cases h
      | callSizeOf _ _ _ => intro h; cases h
      | callTransmuteCopy _ _ _ op _ =>
        dsimp [evalMirTerminator]
        cases evalOperand s.locals op with
        | none => intro h; cases h
        | some p =>
          dsimp
          cases evalTransmuteCopy s.tySizes p.2 _ _ p.1 <;> (intro h; cases h)
      | call1 _ _ arg _ _ =>
        dsimp [evalMirTerminator]
        cases evalOperand s.locals arg <;> (intro h; cases h)
    | some stmt =>
      cases stmt with
      | assign _ rv =>
        cases rv with
        | use op =>
          dsimp [evalMirStmtOpt]
          cases evalOperand s.locals op <;> (intro h; cases h)
        | binaryOp op lhs rhs =>
          dsimp [evalMirStmtOpt]
          cases evalOperand s.locals lhs with
          | none => intro h; cases h
          | some p1 =>
            dsimp
            cases evalOperand p1.2 rhs with
            | none => intro h; cases h
            | some p2 =>
              dsimp
              cases evalBinOp op p1.1 p2.1 <;> (intro h; cases h)
        | aggregate _ op =>
          dsimp [evalMirStmtOpt]
          cases evalOperand s.locals op <;> (intro h; cases h)
        | field0 src =>
          dsimp [evalMirStmtOpt]
          cases s.locals src.index with
          | none => intro h; cases h
          | some v => cases v <;> (intro h; cases h)
        | ref src =>
          dsimp [evalMirStmtOpt]
          cases s.locals src.index <;> (intro h; cases h)
        | reborrow src =>
          dsimp [evalMirStmtOpt]
          cases s.locals src.index with
          | none => intro h; cases h
          | some v =>
            cases v with
            | ref target =>
              dsimp
              cases s.locals target.index <;> (intro h; cases h)
            | _ => intro h; cases h
      | storageLive _ => intro h; cases h
      | storageDead _ => intro h; cases h
      | nop => intro h; cases h
      | unmodeled => intro h; cases h

/-- Even though `TotalStep MirMachineDet` and `InhabitedDemonic MirMachineDet`
    hold globally (so `non_vacuity_at_every_depth` applies to `MirMachineDet`),
    `MirMachineDet.initState buggyRuntimeFn` is uninhabited (`¬ ∃ s, ...`) and
    `MirLangDet.sem buggyRuntimeFn` still vacuously satisfies
    `MirLangDet.Spec (fun _ _ => False)`! -/
theorem totalStep_and_inhabitedDemonic_do_not_catch_empty_initState :
    TotalStep MirMachineDet ∧
    InhabitedDemonic MirMachineDet ∧
    (¬ ∃ s, MirMachineDet.initState buggyRuntimeFn s) ∧
    (MirLangDet.sem buggyRuntimeFn ≤ MirLangDet.Spec (fun _ _ => False)) := by
  refine ⟨mirMachineDet_total, mirMachineDet_inhabitedDemonic, ?_, ?_⟩
  · intro ⟨s, hinit⟩
    exact buggyRuntimeFn_no_initMirState s hinit
  · intro q _
    refine ⟨fun hinit => False.elim (buggyRuntimeFn_no_initMirState q.init hinit), ?_⟩
    intro _ ⟨hinit, _⟩
    exact False.elim (buggyRuntimeFn_no_initMirState q.init hinit)

/-!
## 4. Question 2.1 (Part 2): Polar CTFE Evaluation, Conditional Stuckness, and Inhabitation

We now establish three design results for fixing the negative-polarity `.stuck`
inversion:

1. **Insufficiency of Entry Inhabitation Alone (`partiallyUnmodeledConst`):**
   A constant `partiallyUnmodeledConst` that terminates normally when
   `tySizes 0 = 8` (`bb2: return ()`) and hits `Stmt.unmodeled` (`.stuck`) when
   `tySizes 0 ≠ 8` (`bb3: unmodeled`) satisfies `∃ s, initMirState body s` (at
   `tySizes 0 = 8`), yet still masks runtime UB at `tySizes 0 = 4` under
   baseline `MirSem` because `.stuck` at `tySizes 0 = 4` makes `ConstSucceeds`
   false in negative position.
2. **Polar CTFE Semantics (`ConstNoStuck`, `MonoAdmittedPolar`, `PolarMirSem`):**
   - `ConstNoStuck tySizes c` requires that no finite prefix of `c` under
     `tySizes` reaches `.stuck`.
   - `MonoAdmittedPolar tySizes body` gates `ConstSucceeds` by `ConstNoStuck`
     (`ConstNoStuck tySizes' c → ConstSucceeds tySizes' c`), so a constant that
     can reach `.stuck` never excludes `tySizes'` from runtime verification.
   - `PolarMirSem body` additionally places `BodyConstsNoStuck` positively in
     `defined` outside the `MonoAdmittedPolar` guard, so `.stuck` in
     `requiredConsts` fails closed even when the runtime body is trivially safe.
3. **Positive Monomorphization Inhabitation (`MonoInhabited`):**
   Requiring `∃ s, initEntryState body s ∧ MonoAdmittedPolar s.tySizes body`
   additionally rejects functions whose `requiredConsts` deterministically
   panic or diverge across all `tySizes` (`const { assert!(false) }`), while
   preserving verification of legitimate PME-guarded functions
   (`transmuteToUsizeCheckedBody` with `sizeEq8ConstBody`).
-/

theorem reachesPrefix_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalMirStepOpt body s = some (.step () s'))
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out = .running ∨
      ∃ n' tr', ReachesPrefix MirStep body n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step n' _ s₂ _ tr' _ h1 hr =>
    have h1' : some (StepResult.step () s₂) = evalMirStepOpt body s := h1
    rw [hstep] at h1'
    injection h1' with hstep_eq
    injection hstep_eq with _ hs
    subst hs
    exact Or.inr ⟨n', tr', hr⟩
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_terminated
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {term : TerminationKind MirVal}
    (hstep : evalMirStepOpt body s = some (.terminated term))
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out = .running ∨ out = .terminated term := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : some (StepResult.terminated t) = evalMirStepOpt body s := h1
    rw [hstep] at h1'
    injection h1' with hterm
    injection hterm with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_not_normal_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {v : MirVal}
    (hstep : evalMirStepOpt body s = some (.step () s'))
    (hreach : ReachesPrefix MirStep body n s tr (.terminated (.normal v)))
    (hnext : ∀ n' tr',
      ReachesPrefix MirStep body n' s' tr' (.terminated (.normal v)) →
      False) :
    False := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => cases hrun
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_not_normal_of_unwind
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {v : MirVal}
    (hstep : evalMirStepOpt body s = some (.terminated .unwind))
    (hreach : ReachesPrefix MirStep body n s tr (.terminated (.normal v))) :
    False := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => cases hrun
  | inr hunw => cases hunw

theorem reachesPrefix_not_normal_of_none
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {v : MirVal}
    (hstep : evalMirStepOpt body s = none)
    (hreach : ReachesPrefix MirStep body n s tr (.terminated (.normal v))) :
    False := by
  cases hreach with
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'

/-- Conditional `.stuck` constant: returns `.unit` when `tySizes 0 = 8` (`bb2`),
    and executes `Stmt.unmodeled` (`.stuck`) when `tySizes 0 ≠ 8` (`bb3`). -/
def partiallyUnmodeledConst : MirBody where
  argTys := []
  retTy := .unit
  localCount := 3
  blocks := [
    { stmts := []
      terminator := .callSizeOf ⟨1⟩ (.param 0) ⟨1⟩ },
    { stmts := [.assign ⟨2⟩ (.binaryOp .eq (.move ⟨1⟩) (.constVal (.usize 8)))]
      terminator := .switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩ },
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ },
    { stmts := [.unmodeled]
      terminator := .return_ }
  ]

/-- Legitimate PME constant checking `size_of::<Src>() == 8`: returns `.unit`
    when `tySizes 0 = 8` (`bb2`), and executes `Terminator.panic`
    (`.terminated .unwind`) when `tySizes 0 ≠ 8` (`bb3`). -/
def sizeEq8ConstBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 3
  blocks := [
    { stmts := []
      terminator := .callSizeOf ⟨1⟩ (.param 0) ⟨1⟩ },
    { stmts := [.assign ⟨2⟩ (.binaryOp .eq (.move ⟨1⟩) (.constVal (.usize 8)))]
      terminator := .switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩ },
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ },
    { stmts := []
      terminator := .panic }
  ]

/-- Runtime body performing `transmute_copy::<Src, Param 1>(&_1)` where
    `Param 1` is instantiated alongside `partiallyUnmodeledConst`. -/
def transmuteWithFakePme : MirBody where
  argTys := [.param 0]
  retTy := .param 0
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.ref ⟨1⟩)]
      terminator := .callTransmuteCopy ⟨0⟩ (.param 0) .usize (.move ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]
  requiredConsts := [partiallyUnmodeledConst]

/-- Runtime body performing the same `transmute_copy::<Src, usize>(&_1)`,
    guarded by the legitimate PME `sizeEq8ConstBody`. -/
def transmuteToUsizeCheckedBody : MirBody where
  argTys := [.param 0]
  retTy := .param 0
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.ref ⟨1⟩)]
      terminator := .callTransmuteCopy ⟨0⟩ (.param 0) .usize (.move ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]
  requiredConsts := [sizeEq8ConstBody]

/-- `partiallyUnmodeledConst` succeeds at `tySizes = fun _ => 8`, proving that
    `transmuteWithFakePme` has a non-empty `initMirState` domain. -/
theorem partiallyUnmodeledConst_succeeds_at_8 :
    ConstSucceeds (fun _ => 8) partiallyUnmodeledConst := by
  let s0 : MirState := {
    locals := fun _ => none
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s1 : MirState := {
    locals := updateLocal (fun _ => none) 1 (some (.usize 8))
    block := 1
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s2 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 8))) 1 none) 2 (some (.bool true))
    block := 1
    stmtIdx := 1
    tySizes := fun _ => 8
  }
  let s3 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 8))) 1 none) 2 (some (.bool true))) 2 none
    block := 2
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s4 : MirState := {
    locals := updateLocal s3.locals 0 (some MirVal.unit)
    block := 2
    stmtIdx := 1
    tySizes := fun _ => 8
  }
  have hentry : initEntryState partiallyUnmodeledConst s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hr4 : ReachesPrefix MirStep partiallyUnmodeledConst 1 s4 [] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.terminated 0 s4 (.normal MirVal.unit) rfl
  have hr3 : ReachesPrefix MirStep partiallyUnmodeledConst 2 s3 [()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 1 s3 s4 () [] (.terminated (.normal MirVal.unit)) rfl hr4
  have hr2 : ReachesPrefix MirStep partiallyUnmodeledConst 3 s2 [(), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 2 s2 s3 () [()] (.terminated (.normal MirVal.unit)) rfl hr3
  have hr1 : ReachesPrefix MirStep partiallyUnmodeledConst 4 s1 [(), (), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 3 s1 s2 () [(), ()] (.terminated (.normal MirVal.unit)) rfl hr2
  have hr0 : ReachesPrefix MirStep partiallyUnmodeledConst 5 s0 [(), (), (), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 4 s0 s1 () [(), (), ()] (.terminated (.normal MirVal.unit)) rfl hr1
  exact ⟨s0, 5, [(), (), (), ()], .unit, rfl, hentry, hr0⟩

/-- Consequently, `transmuteWithFakePme` has an inhabited `initMirState`! -/
theorem transmuteWithFakePme_initMirState_inhabited :
    ∃ s, initMirState transmuteWithFakePme s := by
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.bytes 8 0))
  let s0 : MirState := {
    locals := locals0
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initEntryState transmuteWithFakePme s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 8 0, rfl, rfl⟩, hrest⟩⟩
  have hmono : MonoAdmitted (fun _ => 8) transmuteWithFakePme := by
    intro tySizes' c hreq
    cases hreq with
    | direct hmem =>
      cases hmem with
      | head => exact partiallyUnmodeledConst_succeeds_at_8
      | tail _ hnil => cases hnil
    | nested hmem hsub =>
      cases hmem with
      | head =>
        cases hsub with
        | direct hm => cases hm
        | nested hm _ => cases hm
        | call1 hbb hterm _ =>
          cases hbb with
          | head => cases hterm
          | tail _ h1 =>
            cases h1 with
            | head => cases hterm
            | tail _ h2 =>
              cases h2 with
              | head => cases hterm
              | tail _ h3 =>
                cases h3 with
                | head => cases hterm
                | tail _ hnil => cases hnil
      | tail _ hnil => cases hnil
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ h1 =>
        cases h1 with
        | head => cases hterm
        | tail _ hnil => cases hnil
  exact ⟨s0, hentry, hmono⟩

/-- Yet when `tySizes 0 ≠ 8`, `partiallyUnmodeledConst` reaches `.stuck` in
    `bb3`, which under baseline `ConstSucceeds` is indistinguishable from a
    confirmed PME panic (`ConstSucceeds` implies `tySizes 0 = 8`). -/
theorem constSucceeds_partiallyUnmodeledConst_imp_eq8 (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes partiallyUnmodeledConst) :
    tySizes 0 = 8 := by
  cases h with
  | intro s0 h1 =>
  cases s0 with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases h1 with
  | intro n h2 =>
  cases h2 with
  | intro tr h3 =>
  cases h3 with
  | intro v h4 =>
    have hts : tySizes0 = tySizes := h4.1
    have hinit := h4.2.1
    have hreach := h4.2.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hts hb hs hc hst
    cases hdec : decide (tySizes0 0 = 8) with
    | true => exact of_decide_eq_true hdec
    | false =>
      refine False.elim ?_
      refine reachesPrefix_not_normal_of_step rfl hreach (fun _ _ hr1 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr1 (fun _ _ hr2 => ?_)
      let l1 := updateLocal locals0 1 (some (.usize (tySizes0 0)))
      let l2 := updateLocal (updateLocal l1 1 none) 2 (some (.bool (decide (tySizes0 0 = 8))))
      let s_sw : MirState := {
        locals := l2
        block := 1
        stmtIdx := 1
        tySizes := tySizes0
      }
      let s_bb3 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool false))) 2 none
        block := 3
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt partiallyUnmodeledConst s_sw = some (.step () s_bb3) := by
        change some (evalMirTerminator partiallyUnmodeledConst s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb3)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_not_normal_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      exact reachesPrefix_not_normal_of_none rfl hr3

/-- **Clean Polar CTFE Definitions:**
    1. `ConstNoStuck tySizes c`: no reachable prefix of `c` under `tySizes` has
       outcome `.stuck`.
    2. `BodyConstsNoStuck tySizes body`: every constant `(tySizes', c)` in
       `RequiresConst tySizes body` satisfies `ConstNoStuck tySizes' c`.
    3. `MonoAdmittedPolar tySizes body`: for every constant `(tySizes', c)` in
       `RequiresConst tySizes body`, if `ConstNoStuck tySizes' c` holds, then
       `ConstSucceeds tySizes' c` holds (so a `.stuck` constant never makes
       `MonoAdmittedPolar` false!).
    4. `PolarMirSem body`: places `BodyConstsNoStuck` positively in `defined`
       outside the `MonoAdmittedPolar` guard. -/
def ConstNoStuck (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  ∀ (s₀ : MirState) (n : Nat) (tr : List Unit) (out : PrefixOutcome MirVal),
    s₀.tySizes = tySizes →
    initEntryState c s₀ →
    ReachesPrefix MirStep c n s₀ tr out →
    out ≠ .stuck

def BodyConstsNoStuck (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c, RequiresConst tySizes body tySizes' c → ConstNoStuck tySizes' c

def MonoAdmittedPolar (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c,
    RequiresConst tySizes body tySizes' c →
    (ConstNoStuck tySizes' c → ConstSucceeds tySizes' c)

def PolarMirSem (body : MirBody) : MirLang.Behavior :=
  fun q => {
    defined :=
      initEntryState body q.init →
        BodyConstsNoStuck q.init.tySizes body ∧
        (MonoAdmittedPolar q.init.tySizes body →
          ∀ tr out,
            ReachesPrefix MirStep body q.steps q.init tr out →
            out.isSafe)
    val := fun _ out =>
      initEntryState body q.init ∧
      MonoAdmittedPolar q.init.tySizes body ∧
      ReachesPrefix MirStep body q.steps q.init out.trace out.outcome
  }

/-- Positive monomorphization inhabitation obligation: there exists at least one
    entry state `s` whose monomorphization is admitted and whose constants are
    free of `.stuck`. -/
def MonoInhabited (body : MirBody) : Prop :=
  ∃ s : MirState,
    initEntryState body s ∧
    BodyConstsNoStuck s.tySizes body ∧
    MonoAdmittedPolar s.tySizes body

/-- `unmodeledConst` violates `ConstNoStuck` for every `tySizes`. -/
theorem unmodeledConst_not_constNoStuck (tySizes : Nat → Nat) :
    ¬ ConstNoStuck tySizes unmodeledConst := by
  intro hno
  let s₀ : MirState := {
    locals := fun _ => none
    block := 0
    stmtIdx := 0
    tySizes := tySizes
  }
  have hentry : initEntryState unmodeledConst s₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hnostep : ¬ ∃ r, MirStep unmodeledConst s₀ r := by
    intro ⟨r, hr⟩; cases hr
  have hstuck : ReachesPrefix MirStep unmodeledConst 1 s₀ [] .stuck :=
    ReachesPrefix.noStep 0 s₀ hnostep
  exact hno s₀ 1 [] .stuck rfl hentry hstuck rfl

/-- Under `MonoAdmittedPolar`, `unmodeledConst` does NOT exclude any `tySizes`:
    `MonoAdmittedPolar tySizes buggyRuntimeFn` is `True` for all `tySizes`! -/
theorem buggyRuntimeFn_monoAdmittedPolar_holds (tySizes : Nat → Nat) :
    MonoAdmittedPolar tySizes buggyRuntimeFn := by
  intro tySizes' c hreq hnostuck
  cases hreq with
  | direct hmem =>
    cases hmem with
    | head => exact False.elim (unmodeledConst_not_constNoStuck _ hnostuck)
    | tail _ hnil => cases hnil
  | nested hmem hsub =>
    cases hmem with
    | head =>
      cases hsub with
      | direct hm => cases hm
      | nested hm _ => cases hm
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ hnil => cases hnil
    | tail _ hnil => cases hnil
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ hnil => cases hnil

/-- **Theorem (Fix 1):** Under `PolarMirSem`, `buggyRuntimeFn` is REJECTED by
    `MirLang.WellFormed` (both because `BodyConstsNoStuck` fails and because
    `MonoAdmittedPolar` remains `True` so `unreachable` fails at step 1). -/
theorem buggyRuntimeFn_rejected_by_polarMirSem :
    ¬ (PolarMirSem buggyRuntimeFn ≤ MirLang.WellFormed) := by
  intro hWF
  let s₀ : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hentry : initEntryState buggyRuntimeFn s₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hdef := (hWF { init := s₀, steps := 1 } True.intro).1 hentry
  exact unmodeledConst_not_constNoStuck s₀.tySizes
    (hdef.1 s₀.tySizes unmodeledConst (.direct (.head _)))

/-- Safe identity function (`_0 = copy _1; return;`) with `unmodeledConst`
    attached in `requiredConsts`. -/
def idWithUnmodeledConst : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]
  requiredConsts := [unmodeledConst]

/-- **Theorem (Fix 2):** Even when the runtime body is completely safe
    (`idWithUnmodeledConst`), `PolarMirSem` rejects the function when its
    `requiredConsts` can reach `.stuck`. -/
theorem idWithUnmodeledConst_rejected_by_polarMirSem :
    ¬ (PolarMirSem idWithUnmodeledConst ≤ MirLang.WellFormed) := by
  intro hWF
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 42))
  let s₀ : MirState := { locals := locals0, block := 0, stmtIdx := 0 }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initEntryState idWithUnmodeledConst s₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩⟩
  have hdef := (hWF { init := s₀, steps := 1 } True.intro).1 hentry
  exact unmodeledConst_not_constNoStuck s₀.tySizes
    (hdef.1 s₀.tySizes unmodeledConst (.direct (.head _)))

/-- At `tySizes 0 = 4`, `partiallyUnmodeledConst` reaches `.stuck` in 4 steps. -/
theorem partiallyUnmodeledConst_not_constNoStuck_at_4 :
    ¬ ConstNoStuck (fun _ => 4) partiallyUnmodeledConst := by
  intro hno
  let s0 : MirState := {
    locals := fun _ => none
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  let s1 : MirState := {
    locals := updateLocal (fun _ => none) 1 (some (.usize 4))
    block := 1
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  let s2 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 4))) 1 none) 2 (some (.bool false))
    block := 1
    stmtIdx := 1
    tySizes := fun _ => 4
  }
  let s3 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 4))) 1 none) 2 (some (.bool false))) 2 none
    block := 3
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  have hentry : initEntryState partiallyUnmodeledConst s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hnostep3 : ¬ ∃ r, MirStep partiallyUnmodeledConst s3 r := by
    intro ⟨r, hr⟩; cases hr
  have hr3 : ReachesPrefix MirStep partiallyUnmodeledConst 1 s3 [] .stuck :=
    ReachesPrefix.noStep 0 s3 hnostep3
  have hr2 : ReachesPrefix MirStep partiallyUnmodeledConst 2 s2 [()] .stuck :=
    ReachesPrefix.step 1 s2 s3 () [] .stuck rfl hr3
  have hr1 : ReachesPrefix MirStep partiallyUnmodeledConst 3 s1 [(), ()] .stuck :=
    ReachesPrefix.step 2 s1 s2 () [()] .stuck rfl hr2
  have hr0 : ReachesPrefix MirStep partiallyUnmodeledConst 4 s0 [(), (), ()] .stuck :=
    ReachesPrefix.step 3 s0 s1 () [(), ()] .stuck rfl hr1
  exact hno s0 4 [(), (), ()] .stuck rfl hentry hr0 rfl

/-- **Theorem (Fix 3 — Conditional Stuckness Rejected):**
    Even though `transmuteWithFakePme` has an inhabited `initMirState` at
    `tySizes 0 = 8`, `PolarMirSem` rejects `transmuteWithFakePme` at
    `tySizes 0 = 4`! -/
theorem transmuteWithFakePme_rejected_by_polarMirSem :
    ¬ (PolarMirSem transmuteWithFakePme ≤ MirLang.WellFormed) := by
  intro hWF
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.bytes 4 0))
  let s₀ : MirState := {
    locals := locals0
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initEntryState transmuteWithFakePme s₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 4 0, rfl, rfl⟩, hrest⟩⟩
  have hdef := (hWF { init := s₀, steps := 1 } True.intro).1 hentry
  exact partiallyUnmodeledConst_not_constNoStuck_at_4
    (hdef.1 (fun _ => 4) partiallyUnmodeledConst (.direct (.head _)))

/-- Constant body `const { assert!(false) }` that unconditionally panics
    (`.terminated .unwind`). -/
def panicConst : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := []
      terminator := .panic }
  ]

/-- Buggy runtime function with an unconditional PME panic `panicConst` in
    `requiredConsts`. -/
def buggyFnWithPanicConst : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := []
      terminator := .unreachable }
  ]
  requiredConsts := [panicConst]

/-- **Theorem (Fix 4 — `const { assert!(false) }` Rejected by `MonoInhabited`):**
    While `panicConst` never reaches `.stuck` (`ConstNoStuck` holds),
    `buggyFnWithPanicConst` has no admitted monomorphization and is rejected by
    `MonoInhabited`. -/
theorem panicConst_constNoStuck (tySizes : Nat → Nat) :
    ConstNoStuck tySizes panicConst := by
  intro s₀ n tr out _ hentry hreach
  have hb : s₀.block = 0 := hentry.1
  have hs : s₀.stmtIdx = 0 := hentry.2.1
  have hc : s₀.curBody = none := hentry.2.2.1
  have hst : s₀.stack = [] := hentry.2.2.2.1
  have hstep : evalMirStepOpt panicConst s₀ = some (.terminated .unwind) := by
    cases s₀ with
    | mk locals block stmtIdx tySizes0 curBody stack =>
      dsimp at hb hs hc hst
      subst hb hs hc hst
      rfl
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => rw [hrun]; intro h; cases h
  | inr hterm => rw [hterm]; intro h; cases h

theorem buggyFnWithPanicConst_rejected_by_monoInhabited :
    ¬ MonoInhabited buggyFnWithPanicConst := by
  intro ⟨s, _, _, hmono⟩
  have hsucc : ConstSucceeds s.tySizes panicConst :=
    hmono s.tySizes panicConst (.direct (.head _)) (panicConst_constNoStuck s.tySizes)
  cases hsucc with
  | intro s₀ h1 =>
  cases h1 with
  | intro n h2 =>
  cases h2 with
  | intro tr h3 =>
  cases h3 with
  | intro v h4 =>
    have hentry := h4.2.1
    have hreach := h4.2.2
    have hb : s₀.block = 0 := hentry.1
    have hs : s₀.stmtIdx = 0 := hentry.2.1
    have hc : s₀.curBody = none := hentry.2.2.1
    have hst : s₀.stack = [] := hentry.2.2.2.1
    have hstep : evalMirStepOpt panicConst s₀ = some (.terminated .unwind) := by
      cases s₀ with
      | mk locals block stmtIdx tySizes0 curBody stack =>
        dsimp at hb hs hc hst
        subst hb hs hc hst
        rfl
    exact reachesPrefix_not_normal_of_unwind hstep hreach

/-- **Theorem (Fix 5 — Legitimate PME Preserved):**
    The legitimate PME constant `sizeEq8ConstBody` satisfies `ConstNoStuck` for
    ALL `tySizes` (both `tySizes 0 = 8` where it returns `.unit`, and
    `tySizes 0 ≠ 8` where it panics with `.terminated .unwind`), and
    `transmuteToUsizeCheckedBody` satisfies both `PolarMirSem ≤ MirLang.WellFormed`
    and `MonoInhabited`! -/
theorem reachesPrefix_not_stuck_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalMirStepOpt body s = some (.step () s'))
    (hreach : ReachesPrefix MirStep body n s tr out)
    (hnext : ∀ n' tr', ReachesPrefix MirStep body n' s' tr' out → out ≠ .stuck) :
    out ≠ .stuck := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => rw [hrun]; intro h; cases h
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_not_stuck_of_terminated
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {term : TerminationKind MirVal}
    (hstep : evalMirStepOpt body s = some (.terminated term))
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out ≠ .stuck := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => rw [hrun]; intro h; cases h
  | inr hterm => rw [hterm]; intro h; cases h

theorem sizeEq8ConstBody_constNoStuck (tySizes : Nat → Nat) :
    ConstNoStuck tySizes sizeEq8ConstBody := by
  intro s₀ n tr out hts hentry hreach
  cases s₀ with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    subst hts hb hs hc hst
    refine reachesPrefix_not_stuck_of_step rfl hreach (fun _ _ hr1 => ?_)
    refine reachesPrefix_not_stuck_of_step rfl hr1 (fun _ _ hr2 => ?_)
    let l1 := updateLocal locals0 1 (some (.usize (tySizes0 0)))
    let l2 := updateLocal (updateLocal l1 1 none) 2 (some (.bool (decide (tySizes0 0 = 8))))
    let s_sw : MirState := {
      locals := l2
      block := 1
      stmtIdx := 1
      tySizes := tySizes0
    }
    cases hdec : decide (tySizes0 0 = 8) with
    | false =>
      let s_bb3 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool false))) 2 none
        block := 3
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt sizeEq8ConstBody s_sw = some (.step () s_bb3) := by
        change some (evalMirTerminator sizeEq8ConstBody s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb3)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_not_stuck_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      exact reachesPrefix_not_stuck_of_terminated rfl hr3
    | true =>
      let s_bb2 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool true))) 2 none
        block := 2
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt sizeEq8ConstBody s_sw = some (.step () s_bb2) := by
        change some (evalMirTerminator sizeEq8ConstBody s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb2)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_not_stuck_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      refine reachesPrefix_not_stuck_of_step rfl hr3 (fun _ _ hr4 => ?_)
      exact reachesPrefix_not_stuck_of_terminated rfl hr4

theorem constSucceeds_sizeEq8ConstBody_imp_eq8 (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes sizeEq8ConstBody) :
    tySizes 0 = 8 := by
  cases h with
  | intro s0 h1 =>
  cases s0 with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases h1 with
  | intro n h2 =>
  cases h2 with
  | intro tr h3 =>
  cases h3 with
  | intro v h4 =>
    have hts : tySizes0 = tySizes := h4.1
    have hinit := h4.2.1
    have hreach := h4.2.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hts hb hs hc hst
    cases hdec : decide (tySizes0 0 = 8) with
    | true => exact of_decide_eq_true hdec
    | false =>
      refine False.elim ?_
      refine reachesPrefix_not_normal_of_step rfl hreach (fun _ _ hr1 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr1 (fun _ _ hr2 => ?_)
      let l1 := updateLocal locals0 1 (some (.usize (tySizes0 0)))
      let l2 := updateLocal (updateLocal l1 1 none) 2 (some (.bool (decide (tySizes0 0 = 8))))
      let s_sw : MirState := {
        locals := l2
        block := 1
        stmtIdx := 1
        tySizes := tySizes0
      }
      let s_bb3 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool false))) 2 none
        block := 3
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt sizeEq8ConstBody s_sw = some (.step () s_bb3) := by
        change some (evalMirTerminator sizeEq8ConstBody s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb3)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_not_normal_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      exact reachesPrefix_not_normal_of_unwind rfl hr3

theorem sizeEq8ConstBody_succeeds_at_8 :
    ConstSucceeds (fun _ => 8) sizeEq8ConstBody := by
  let s0 : MirState := {
    locals := fun _ => none
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s1 : MirState := {
    locals := updateLocal (fun _ => none) 1 (some (.usize 8))
    block := 1
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s2 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 8))) 1 none) 2 (some (.bool true))
    block := 1
    stmtIdx := 1
    tySizes := fun _ => 8
  }
  let s3 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 8))) 1 none) 2 (some (.bool true))) 2 none
    block := 2
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s4 : MirState := {
    locals := updateLocal s3.locals 0 (some MirVal.unit)
    block := 2
    stmtIdx := 1
    tySizes := fun _ => 8
  }
  have hentry : initEntryState sizeEq8ConstBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hr4 : ReachesPrefix MirStep sizeEq8ConstBody 1 s4 [] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.terminated 0 s4 (.normal MirVal.unit) rfl
  have hr3 : ReachesPrefix MirStep sizeEq8ConstBody 2 s3 [()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 1 s3 s4 () [] (.terminated (.normal MirVal.unit)) rfl hr4
  have hr2 : ReachesPrefix MirStep sizeEq8ConstBody 3 s2 [(), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 2 s2 s3 () [()] (.terminated (.normal MirVal.unit)) rfl hr3
  have hr1 : ReachesPrefix MirStep sizeEq8ConstBody 4 s1 [(), (), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 3 s1 s2 () [(), ()] (.terminated (.normal MirVal.unit)) rfl hr2
  have hr0 : ReachesPrefix MirStep sizeEq8ConstBody 5 s0 [(), (), (), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 4 s0 s1 () [(), (), ()] (.terminated (.normal MirVal.unit)) rfl hr1
  exact ⟨s0, 5, [(), (), (), ()], .unit, rfl, hentry, hr0⟩

theorem transmuteToUsizeCheckedBody_constsNoStuck (tySizes : Nat → Nat) :
    BodyConstsNoStuck tySizes transmuteToUsizeCheckedBody := by
  intro tySizes' c hreq
  cases hreq with
  | direct hmem =>
    cases hmem with
    | head => exact sizeEq8ConstBody_constNoStuck _
    | tail _ hnil => cases hnil
  | nested hmem hsub =>
    cases hmem with
    | head =>
      cases hsub with
      | direct hm => cases hm
      | nested hm _ => cases hm
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ h1 =>
          cases h1 with
          | head => cases hterm
          | tail _ h2 =>
            cases h2 with
            | head => cases hterm
            | tail _ h3 =>
              cases h3 with
              | head => cases hterm
              | tail _ hnil => cases hnil
    | tail _ hnil => cases hnil
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ h1 =>
      cases h1 with
      | head => cases hterm
      | tail _ hnil => cases hnil

/-- Legitimate PME-guarded `transmuteToUsizeCheckedBody` satisfies both
    `PolarMirSem transmuteToUsizeCheckedBody ≤ MirLang.WellFormed` and
    `MonoInhabited transmuteToUsizeCheckedBody`! -/
theorem transmuteToUsizeCheckedBody_verified_polar :
    PolarMirSem transmuteToUsizeCheckedBody ≤ MirLang.WellFormed ∧
    MonoInhabited transmuteToUsizeCheckedBody := by
  constructor
  · intro q _
    refine ⟨?_, fun _ _ => True.intro⟩
    intro hentry
    refine ⟨transmuteToUsizeCheckedBody_constsNoStuck q.init.tySizes, ?_⟩
    intro hmono tr out hreach
    cases q with
    | mk init steps =>
    cases init with
    | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
      have hb : block0 = 0 := hentry.1
      have hs : stmtIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      have hst : stack0 = [] := hentry.2.2.2.1
      subst hb hs hc hst
      have hsucc : ConstSucceeds tySizes0 sizeEq8ConstBody :=
        hmono tySizes0 sizeEq8ConstBody (.direct (.head _))
          (sizeEq8ConstBody_constNoStuck tySizes0)
      have heq8 : tySizes0 0 = 8 :=
        constSucceeds_sizeEq8ConstBody_imp_eq8 tySizes0 hsucc
      cases hentry.2.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : locals0 1 = some v := hv.1
        have hvty : v.hasTy tySizes0 (.param 0) := hv.2
        cases v with
        | usize _ => cases hvty
        | bool _ => cases hvty
        | unit => cases hvty
        | adt _ _ => cases hvty
        | ref _ => cases hvty
        | bytes vSz bits =>
          have hvSz : vSz = tySizes0 0 := hvty
          subst hvSz
          let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
          let l1 := updateLocal locals0 2 (some (.ref ⟨1⟩))
          let s1 : MirState := { s0 with locals := l1, stmtIdx := 1 }
          have hstep0 : evalMirStepOpt transmuteToUsizeCheckedBody s0 = some (.step () s1) := by
            change evalMirStmtOpt s0 (.assign ⟨2⟩ (.ref ⟨1⟩)) = some (.step () s1)
            dsimp only [evalMirStmtOpt, s0]
            rw [hv1]
          cases reachesPrefix_of_step hstep0 hreach with
          | inl hrun => rw [hrun]; exact True.intro
          | inr hex1 =>
            cases hex1 with
            | intro n1 htr1 =>
              cases htr1 with
              | intro tr1 hr1 =>
                let l1_deinit := updateLocal l1 2 none
                have hl1_1 : l1_deinit 1 = some (.bytes (tySizes0 0) bits) := by
                  change (if 1 == 2 then none else if 1 == 2 then some (MirVal.ref ⟨1⟩) else locals0 1) = _
                  exact hv1
                have hdec8 : decide (tySizes0 0 = 8) = true := decide_eq_true heq8
                have hdec_refl : decide (tySizes0 0 = tySizes0 0) = true := decide_eq_true rfl
                let s2 : MirState := {
                  s1 with
                  locals := updateLocal l1_deinit 0 (some (.bytes 8 bits))
                  block := 1
                  stmtIdx := 0
                }
                have hstep1 : evalMirStepOpt transmuteToUsizeCheckedBody s1 = some (.step () s2) := by
                  change some (evalMirTerminator transmuteToUsizeCheckedBody s1
                    (.callTransmuteCopy ⟨0⟩ (.param 0) .usize (.move ⟨2⟩) ⟨1⟩)) = some (.step () s2)
                  dsimp only [evalMirTerminator, evalOperand, evalTransmuteCopy, evalTyByteSize, s1, l1]
                  change some (match (if decide (tySizes0 0 = 8) then
                      match l1_deinit 1 with
                      | some (.bytes vSz b) =>
                        if decide (vSz = tySizes0 0) then some (MirVal.bytes 8 b) else none
                      | _ => none
                    else none) with
                    | some outVal => StepResult.step () { s1 with locals := updateLocal l1_deinit 0 (some outVal), block := 1, stmtIdx := 0 }
                    | none => StepResult.failed) = some (.step () s2)
                  rw [hdec8, hl1_1]
                  dsimp only
                  rw [hdec_refl]
                  rfl
                cases reachesPrefix_of_step hstep1 hr1 with
                | inl hrun => rw [hrun]; exact True.intro
                | inr hex2 =>
                  cases hex2 with
                  | intro n2 htr2 =>
                    cases htr2 with
                    | intro tr2 hr2 =>
                      cases reachesPrefix_of_terminated (term := .normal (.bytes 8 bits)) rfl hr2 with
                      | inl hrun => rw [hrun]; exact True.intro
                      | inr hterm => rw [hterm]; exact True.intro
  · let locals0 : Nat → Option MirVal :=
      updateLocal (fun _ => none) 1 (some (.bytes 8 0))
    let s0 : MirState := {
      locals := locals0
      block := 0
      stmtIdx := 0
      tySizes := fun _ => 8
    }
    have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
      intro j hj
      cases j with
      | zero => cases hj
      | succ k =>
        cases k with
        | zero => cases hj with | step hle => cases hle
        | succ _ => rfl
    have hentry : initEntryState transmuteToUsizeCheckedBody s0 :=
      ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 8 0, rfl, rfl⟩, hrest⟩⟩
    have hmono : MonoAdmittedPolar (fun _ => 8) transmuteToUsizeCheckedBody := by
      intro tySizes' c hreq _
      cases hreq with
      | direct hmem =>
        cases hmem with
        | head => exact sizeEq8ConstBody_succeeds_at_8
        | tail _ hnil => cases hnil
      | nested hmem hsub =>
        cases hmem with
        | head =>
          cases hsub with
          | direct hm => cases hm
          | nested hm _ => cases hm
          | call1 hbb hterm _ =>
            cases hbb with
            | head => cases hterm
            | tail _ h1 =>
              cases h1 with
              | head => cases hterm
              | tail _ h2 =>
                cases h2 with
                | head => cases hterm
                | tail _ h3 =>
                  cases h3 with
                  | head => cases hterm
                  | tail _ hnil => cases hnil
        | tail _ hnil => cases hnil
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ h1 =>
          cases h1 with
          | head => cases hterm
          | tail _ hnil => cases hnil
    exact ⟨s0, hentry, transmuteToUsizeCheckedBody_constsNoStuck (fun _ => 8), hmono⟩

/-!
## 5. Infinite-Loop & Unwind Progress Collapse and Step-Dilated Prefix Simulation

We now mechanize the x86 target machine (`X86Ast.lean`, `X86Semantics.lean`, and
`Compiler/NaiveCodegen.lean` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`) and
prove:
1. **The Infinite-Loop and Unwind Codegen Exploits (`loopCodegen`, `unwindCodegen`):**
   Every `MirBody` compiled to `bb0: jmp 0` (`loopCodegen`) or `bb0: abortPanic`
   (`unwindCodegen`) satisfies `X86Lang.WellFormed`, `X86Lang.EnsuresRetLibInv`,
   `X86Lang.EnsuresEqArg`, and `X86Lang.EnsuresConst`, and a naive multi-step
   refinement relaxation (`π_naive_async`) that allows `.running` at arbitrary
   budgets admits `Compiles_naive_async (loopCodegen b) b` for every `b`.
2. **Fuel Absorption of Terminal Outcomes (`reachesPrefix_terminated_mono`):**
   Because `ReachesPrefix.terminated` is parameterized over arbitrary remaining
   fuel `n : Nat`, any terminal outcome reached at budget `m₀` persists at every
   budget `m ≥ m₀`.
3. **Constructive Step-Dilated Prefix Simulation (`π_dilated k`):**
   With zero `Classical.choice` and zero coinduction, `π_dilated k` is `Monotone`,
   rejects `loopCodegen` and `unwindCodegen` on every terminating source program
   for all `k ≥ 1`, admits $1 \to [1..k]$ instruction expansion (demonstrated on
   a 2x-expanding compiler `idCopyX86_2x` that lockstep `Compiles` rejects), and
   admits genuine source loops and unwinds.
4. **Step-Bounded Total Specifications (`EnsuresEqArgTotal`):**
   Strengthening `EnsuresEqArg` with a step-budget threshold `n₀` directly
   rejects `loopCodegen` and `unwindCodegen` at the specification layer.
-/

/-- Virtual register index (`Trusted/X86Ast.lean`). -/
structure VReg where
  idx : Nat

/-- Target x86 instruction subset (`Trusted/X86Ast.lean`). -/
inductive X86Instr where
  | movReg (dst : VReg) (src : VReg)
  | movImmUsize (dst : VReg) (val : Nat)
  | deinit (reg : VReg)

/-- Target x86 terminator (`Trusted/X86Ast.lean`). -/
inductive X86Terminator where
  | ret
  | jmp (target : BlockId)
  | abortPanic
  | ud2

/-- Target x86 basic block (`Trusted/X86Ast.lean`). -/
structure X86Block where
  instrs : List X86Instr
  terminator : X86Terminator

/-- Target x86 function body (`Trusted/X86Ast.lean`). -/
structure X86Body where
  argTys : List MirTy
  retTy : MirTy
  regCount : Nat
  blocks : List X86Block
  requiredConsts : List MirBody := []

/-- Target x86 execution state (`Trusted/X86Semantics.lean`). -/
structure X86State where
  regs : Nat → Option MirVal
  block : Nat
  instrIdx : Nat
  tySizes : Nat → Nat := fun _ => 8
  curBody : Option X86Body := none

/-- Update a single virtual register (`Trusted/X86Semantics.lean`). -/
def updateReg (regs : Nat → Option MirVal) (idx : Nat)
    (v : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == idx then v else regs i

/-- Initial x86 entry state predicate (`Trusted/X86Semantics.lean`). -/
def initX86EntryState (body : X86Body) (s : X86State) : Prop :=
  s.block = 0 ∧
  s.instrIdx = 0 ∧
  s.curBody = none ∧
  s.regs 0 = none ∧
  argsMatchLocals s.tySizes body.argTys s.regs

/-- Single-instruction x86 evaluator (`Trusted/X86Semantics.lean`). -/
def evalX86Instr (s : X86State) (instr : X86Instr) : StepResult X86State Unit MirVal :=
  match instr with
  | .movReg dst src =>
    match s.regs src.idx with
    | some v =>
      .step () { s with
        regs := updateReg s.regs dst.idx (some v)
        instrIdx := s.instrIdx + 1 }
    | none => .failed
  | .movImmUsize dst val =>
    .step () { s with
      regs := updateReg s.regs dst.idx (some (.usize val))
      instrIdx := s.instrIdx + 1 }
  | .deinit reg =>
    .step () { s with
      regs := updateReg s.regs reg.idx none
      instrIdx := s.instrIdx + 1 }

/-- Terminator x86 evaluator (`Trusted/X86Semantics.lean`). -/
def evalX86Terminator (s : X86State) (term : X86Terminator) :
    StepResult X86State Unit MirVal :=
  match term with
  | .ret =>
    match s.regs 0 with
    | some v => .terminated (.normal v)
    | none => .failed
  | .jmp target =>
    .step () { s with block := target.index, instrIdx := 0 }
  | .abortPanic => .terminated .unwind
  | .ud2 => .failed

/-- Total x86 step evaluator (`Trusted/X86Semantics.lean`). -/
def evalX86Step (prog : X86Body) (s : X86State) : StepResult X86State Unit MirVal :=
  let activeBody := s.curBody.getD prog
  match activeBody.blocks[s.block]? with
  | none => .failed
  | some bb =>
    match bb.instrs[s.instrIdx]? with
    | some instr => evalX86Instr s instr
    | none =>
      if s.instrIdx == bb.instrs.length then
        evalX86Terminator s bb.terminator
      else
        .failed

/-- Relational x86 step (`Trusted/X86Semantics.lean`). -/
def X86Step (prog : X86Body) (s : X86State)
    (res : StepResult X86State Unit MirVal) : Prop :=
  evalX86Step prog s = res

/-- Inversion lemma for `ReachesPrefix X86Step` on a `.step` transition. -/
theorem reachesPrefix_x86_of_step
    {prog : X86Body} {s s' : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalX86Step prog s = .step () s')
    (hreach : ReachesPrefix X86Step prog n s tr out) :
    (n = 0 ∧ tr = [] ∧ out = .running) ∨
    ∃ n' tr', n = n' + 1 ∧ tr = () :: tr' ∧
      ReachesPrefix X86Step prog n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl ⟨rfl, rfl, rfl⟩
  | terminated m _ term h =>
    have heq : StepResult.step () s' = StepResult.terminated term :=
      hstep.symm.trans h
    cases heq
  | failed m _ h =>
    have heq : StepResult.step () s' = StepResult.failed :=
      hstep.symm.trans h
    cases heq
  | step m _ s₂ e tr' _ h hr' =>
    have heq : StepResult.step () s' = StepResult.step e s₂ :=
      hstep.symm.trans h
    injection heq with _ hs
    subst hs
    exact Or.inr ⟨m, tr', rfl, rfl, hr'⟩
  | choice m _ _ branches _ _ h _ _ =>
    have heq : StepResult.step () s' = StepResult.choice branches :=
      hstep.symm.trans h
    cases heq
  | noStep m _ hno =>
    exact False.elim (hno ⟨.step () s', hstep⟩)
  | emptyChoice m _ P h _ =>
    have heq : StepResult.step () s' = StepResult.choice P :=
      hstep.symm.trans h
    cases heq

/-- Inversion lemma for `ReachesPrefix X86Step` on a `.terminated` transition. -/
theorem reachesPrefix_x86_of_terminated
    {prog : X86Body} {s : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {term : TerminationKind MirVal}
    (hstep : evalX86Step prog s = .terminated term)
    (hreach : ReachesPrefix X86Step prog n s tr out) :
    (n = 0 ∧ tr = [] ∧ out = .running) ∨
    (∃ m, n = m + 1 ∧ tr = [] ∧ out = .terminated term) := by
  cases hreach with
  | zero => exact Or.inl ⟨rfl, rfl, rfl⟩
  | terminated m _ term' h =>
    have heq : StepResult.terminated term = StepResult.terminated term' :=
      hstep.symm.trans h
    injection heq with hterm
    subst hterm
    exact Or.inr ⟨m, rfl, rfl, rfl⟩
  | failed m _ h =>
    have heq : StepResult.terminated term = StepResult.failed :=
      hstep.symm.trans h
    cases heq
  | step m _ s₂ e tr' _ h _ =>
    have heq : StepResult.terminated term = StepResult.step e s₂ :=
      hstep.symm.trans h
    cases heq
  | choice m _ _ branches _ _ h _ _ =>
    have heq : StepResult.terminated term = StepResult.choice branches :=
      hstep.symm.trans h
    cases heq
  | noStep m _ hno =>
    exact False.elim (hno ⟨.terminated term, hstep⟩)
  | emptyChoice m _ P h _ =>
    have heq : StepResult.terminated term = StepResult.choice P :=
      hstep.symm.trans h
    cases heq

/-- The x86 abstract machine (`Trusted/X86Semantics.lean`). -/
def X86Machine : SmallStepMachine X86Body X86State Unit MirVal where
  initState := initX86EntryState
  step := X86Step

/-- The x86 language (`Trusted/X86Semantics.lean`). -/
abbrev X86Lang : Language := X86Machine.toLanguage

/-- Denotational semantics of an `X86Body` (`Trusted/X86Semantics.lean`). -/
def X86Sem (prog : X86Body) : X86Lang.Behavior :=
  BehaviorOf X86Machine prog

/-- Functional specification combinator on `X86Lang` (`Trusted/X86Semantics.lean`
    lines 815–828). -/
def X86Lang.SpecOn (pre : X86State → Prop)
    (post : X86State → MirVal → Prop) : X86Lang.Behavior :=
  fun q =>
    { defined := pre q.init
      val := fun _ out =>
        out.outcome.isSafe ∧
        (∀ ret, out.outcome = .terminated (.normal ret) → post q.init ret) }

/-- Library return-type invariant contract on x86 (`Trusted/X86Semantics.lean`). -/
def X86Lang.EnsuresRetLibInv (retTy : MirTy) : X86Lang.Behavior :=
  X86Lang.SpecOn
    (fun _ => True)
    (fun s ret => ret.hasTy s.tySizes retTy)

/-- Equality-with-first-argument contract on x86 (`Trusted/X86Semantics.lean`). -/
def X86Lang.EnsuresEqArg : X86Lang.Behavior :=
  X86Lang.SpecOn
    (fun _ => True)
    (fun s ret => ∃ v, s.regs 1 = some v ∧ ret = v)

/-- Constant-return contract on x86 (`Trusted/X86Semantics.lean`). -/
def X86Lang.EnsuresConst (expected : MirVal) : X86Lang.Behavior :=
  X86Lang.SpecOn
    (fun _ => True)
    (fun _ ret => ret = expected)

/-- State matching relation between `MirState` and `X86State`
    (`Trusted/X86Semantics.lean` lines 830–841). -/
def matchQuery (s_mir : MirState) (s_x86 : X86State) : Prop :=
  s_mir.locals = s_x86.regs ∧
  s_mir.block = 0 ∧
  s_mir.stmtIdx = 0 ∧
  s_mir.tySizes = s_x86.tySizes ∧
  s_mir.curBody = none ∧
  s_mir.stack = [] ∧
  s_x86.block = 0 ∧
  s_x86.instrIdx = 0 ∧
  s_x86.curBody = none

/-- Baseline lockstep cross-language refinement injection `π`
    (`Trusted/X86Semantics.lean` lines 851–866). -/
def π (B : MirLang.Behavior) : X86Lang.Behavior :=
  fun q_tgt => {
    defined := ∀ q_src : MirLang.Query,
      matchQuery q_src.init q_tgt.init →
      q_src.steps = q_tgt.steps →
      (B q_src).defined
    val := fun h out =>
      ∃ q_src : MirLang.Query,
        ∃ h_match : matchQuery q_src.init q_tgt.init,
        ∃ h_steps : q_src.steps = q_tgt.steps,
        (B q_src).val (h q_src h_match h_steps) out
  }

/-- Baseline `CompilesX86` judgment (`Trusted/X86Semantics.lean` line 892). -/
def CompilesX86 (x86 : X86Body) (mir : MirBody) : Prop :=
  X86Sem x86 ≤ π (MirSem mir)

/-!
### 5.1 The Infinite-Loop and Unwind Codegen Exploits (`loopCodegen`, `unwindCodegen`)
-/

/-- **Exploit 1 (`loopCodegen`):** Compiles any `MirBody` to a 1-block x86 body
    whose sole basic block jumps to itself (`bb0: jmp 0`). -/
def loopCodegen (b : MirBody) : X86Body where
  argTys := b.argTys
  retTy := b.retTy
  regCount := b.localCount
  blocks := [{ instrs := [], terminator := .jmp ⟨0⟩ }]
  requiredConsts := b.requiredConsts

/-- **Exploit 2 (`unwindCodegen`):** Compiles any `MirBody` to a 1-block x86 body
    whose sole basic block unconditionally aborts/unwinds (`bb0: abortPanic`). -/
def unwindCodegen (b : MirBody) : X86Body where
  argTys := b.argTys
  retTy := b.retTy
  regCount := b.localCount
  blocks := [{ instrs := [], terminator := .abortPanic }]
  requiredConsts := b.requiredConsts

/-- At any step budget `n`, `loopCodegen b` starting at `block = 0, instrIdx = 0,
    curBody = none` always has outcome `.running`. -/
theorem loopCodegen_always_running (b : MirBody) :
    ∀ (n : Nat) (s : X86State) (tr : List Unit) (out : PrefixOutcome MirVal),
      s.block = 0 →
      s.instrIdx = 0 →
      s.curBody = none →
      ReachesPrefix X86Step (loopCodegen b) n s tr out →
      out = .running := by
  intro n
  induction n with
  | zero =>
    intro s tr out _ _ _ hreach
    cases hreach with
    | zero => rfl
  | succ m ih =>
    intro s tr out hb hi hc hreach
    have hstep : evalX86Step (loopCodegen b) s = .step () s := by
      cases s with
      | mk regs block instrIdx tySizes curBody =>
        dsimp at hb hi hc
        subst hb hi hc
        rfl
    cases reachesPrefix_x86_of_step hstep hreach with
    | inl h0 => exact h0.2.2
    | inr hex =>
      cases hex with
      | intro n' htr =>
        cases htr with
        | intro tr' hr' =>
          have hmn : m = n' := Nat.succ.inj hr'.1
          subst hmn
          exact ih s tr' out hb hi hc hr'.2.2

/-- **Theorem (Progress Exploit 1a):** For EVERY `b : MirBody`, `loopCodegen b`
    satisfies `X86Lang.WellFormed`. -/
theorem loopCodegen_satisfies_wellFormed (b : MirBody) :
    X86Sem (loopCodegen b) ≤ X86Lang.WellFormed := by
  intro q _
  refine ⟨?_, fun _ _ => True.intro⟩
  intro hentry tr out hreach
  have hout : out = .running :=
    loopCodegen_always_running b q.steps q.init tr out
      hentry.1 hentry.2.1 hentry.2.2.1 hreach
  rw [hout]
  exact True.intro

/-- **Theorem (Progress Exploit 1b):** For EVERY `b : MirBody` and every `pre`/`post`,
    `loopCodegen b` satisfies `X86Lang.SpecOn pre post` (and therefore
    `EnsuresRetLibInv`, `EnsuresEqArg`, and `EnsuresConst`). -/
theorem loopCodegen_satisfies_any_specOn (b : MirBody)
    (pre : X86State → Prop) (post : X86State → MirVal → Prop) :
    X86Sem (loopCodegen b) ≤ X86Lang.SpecOn pre post := by
  intro q _
  refine ⟨?_, ?_⟩
  · intro hentry tr out hreach
    have hout : out = .running :=
      loopCodegen_always_running b q.steps q.init tr out
        hentry.1 hentry.2.1 hentry.2.2.1 hreach
    rw [hout]
    exact True.intro
  · intro out hval
    dsimp [X86Lang.SpecOn]
    have hentry := hval.1
    have hreach := hval.2
    have hout : out.outcome = .running :=
      loopCodegen_always_running b q.steps q.init out.trace out.outcome
        hentry.1 hentry.2.1 hentry.2.2.1 hreach
    rw [hout]
    refine ⟨True.intro, ?_⟩
    intro ret hterm
    cases hterm

theorem loopCodegen_satisfies_ensuresRetLibInv (b : MirBody) (retTy : MirTy) :
    X86Sem (loopCodegen b) ≤ X86Lang.EnsuresRetLibInv retTy :=
  loopCodegen_satisfies_any_specOn b _ _

theorem loopCodegen_satisfies_ensuresEqArg (b : MirBody) :
    X86Sem (loopCodegen b) ≤ X86Lang.EnsuresEqArg :=
  loopCodegen_satisfies_any_specOn b _ _

theorem loopCodegen_satisfies_ensuresConst (b : MirBody) (v : MirVal) :
    X86Sem (loopCodegen b) ≤ X86Lang.EnsuresConst v :=
  loopCodegen_satisfies_any_specOn b _ _

/-- At any step budget `n`, `unwindCodegen b` starting at `block = 0, instrIdx = 0,
    curBody = none` always has outcome `.running` (when `n = 0`) or
    `.terminated .unwind` (when `n ≥ 1`). -/
theorem unwindCodegen_always_running_or_unwind (b : MirBody)
    (n : Nat) (s : X86State) (tr : List Unit) (out : PrefixOutcome MirVal)
    (hb : s.block = 0) (hi : s.instrIdx = 0) (hc : s.curBody = none)
    (hreach : ReachesPrefix X86Step (unwindCodegen b) n s tr out) :
    (n = 0 ∧ tr = [] ∧ out = .running) ∨
    (∃ m, n = m + 1 ∧ tr = [] ∧ out = .terminated .unwind) := by
  have hstep : evalX86Step (unwindCodegen b) s = .terminated .unwind := by
    cases s with
    | mk regs block instrIdx tySizes curBody =>
      dsimp at hb hi hc
      subst hb hi hc
      rfl
  exact reachesPrefix_x86_of_terminated hstep hreach

/-- **Theorem (Progress Exploit 2a):** For EVERY `b : MirBody`, `unwindCodegen b`
    satisfies `X86Lang.WellFormed`. -/
theorem unwindCodegen_satisfies_wellFormed (b : MirBody) :
    X86Sem (unwindCodegen b) ≤ X86Lang.WellFormed := by
  intro q _
  refine ⟨?_, fun _ _ => True.intro⟩
  intro hentry tr out hreach
  cases unwindCodegen_always_running_or_unwind b q.steps q.init tr out
    hentry.1 hentry.2.1 hentry.2.2.1 hreach with
  | inl hrun => rw [hrun.2.2]; exact True.intro
  | inr hunw =>
    cases hunw with
    | intro m hm => rw [hm.2.2]; exact True.intro

/-- **Theorem (Progress Exploit 2b):** For EVERY `b : MirBody` and every `pre`/`post`,
    `unwindCodegen b` satisfies `X86Lang.SpecOn pre post` (and therefore
    `EnsuresRetLibInv`, `EnsuresEqArg`, and `EnsuresConst`). -/
theorem unwindCodegen_satisfies_any_specOn (b : MirBody)
    (pre : X86State → Prop) (post : X86State → MirVal → Prop) :
    X86Sem (unwindCodegen b) ≤ X86Lang.SpecOn pre post := by
  intro q _
  refine ⟨?_, ?_⟩
  · intro hentry tr out hreach
    cases unwindCodegen_always_running_or_unwind b q.steps q.init tr out
      hentry.1 hentry.2.1 hentry.2.2.1 hreach with
    | inl hrun => rw [hrun.2.2]; exact True.intro
    | inr hunw =>
      cases hunw with
      | intro m hm => rw [hm.2.2]; exact True.intro
  · intro out hval
    dsimp [X86Lang.SpecOn]
    have hentry := hval.1
    have hreach := hval.2
    cases unwindCodegen_always_running_or_unwind b q.steps q.init out.trace out.outcome
      hentry.1 hentry.2.1 hentry.2.2.1 hreach with
    | inl hrun =>
      rw [hrun.2.2]
      refine ⟨True.intro, ?_⟩
      intro ret hterm
      cases hterm
    | inr hunw =>
      cases hunw with
      | intro m hm =>
        rw [hm.2.2]
        refine ⟨True.intro, ?_⟩
        intro ret hterm
        cases hterm

theorem unwindCodegen_satisfies_ensuresRetLibInv (b : MirBody) (retTy : MirTy) :
    X86Sem (unwindCodegen b) ≤ X86Lang.EnsuresRetLibInv retTy :=
  unwindCodegen_satisfies_any_specOn b _ _

theorem unwindCodegen_satisfies_ensuresEqArg (b : MirBody) :
    X86Sem (unwindCodegen b) ≤ X86Lang.EnsuresEqArg :=
  unwindCodegen_satisfies_any_specOn b _ _

theorem unwindCodegen_satisfies_ensuresConst (b : MirBody) (v : MirVal) :
    X86Sem (unwindCodegen b) ≤ X86Lang.EnsuresConst v :=
  unwindCodegen_satisfies_any_specOn b _ _

/-- **Naive Multi-Step Relaxation (`π_naive_async`):**
    Suppose a compiler author relaxes lockstep `π` to allow 1-to-many instruction
    expansion by permitting the target x86 execution at step budget `q_tgt.steps`
    to either match some source execution OR still be `.running` (`out.outcome =
    .running`). -/
def π_naive_async (B : MirLang.Behavior) : X86Lang.Behavior :=
  fun q_tgt => {
    defined := ∀ q_src : MirLang.Query,
      matchQuery q_src.init q_tgt.init →
      q_src.steps = q_tgt.steps →
      (B q_src).defined
    val := fun h out =>
      out.outcome = .running ∨
      ∃ q_src : MirLang.Query,
        ∃ h_match : matchQuery q_src.init q_tgt.init,
        ∃ h_steps : q_src.steps = q_tgt.steps,
        (B q_src).val (h q_src h_match h_steps) out
  }

def Compiles_naive_async (x86 : X86Body) (mir : MirBody) : Prop :=
  X86Sem x86 ≤ π_naive_async (MirSem mir)

/-- **Theorem (Progress Exploit 3 — `π_naive_async` Certifies `loopCodegen`):**
    Under `π_naive_async`, `loopCodegen b` is certified as a valid compilation of
    EVERY well-formed `MirBody b`! -/
theorem loopCodegen_compiles_under_π_naive_async (b : MirBody)
    (_hWF : MirSem b ≤ MirLang.WellFormed) :
    Compiles_naive_async (loopCodegen b) b := by
  intro q_tgt _
  refine ⟨?_, ?_⟩
  · intro hentry tr out hreach
    have hout : out = .running :=
      loopCodegen_always_running b q_tgt.steps q_tgt.init tr out
        hentry.1 hentry.2.1 hentry.2.2.1 hreach
    rw [hout]
    exact True.intro
  · intro out hval
    have hentry := hval.1
    have hreach := hval.2
    have hout : out.outcome = .running :=
      loopCodegen_always_running b q_tgt.steps q_tgt.init out.trace out.outcome
        hentry.1 hentry.2.1 hentry.2.2.1 hreach
    exact Or.inl hout

/-!
### 5.2 Fuel Absorption of Terminal Outcomes (`reachesPrefix_terminated_mono`)

Why can we enforce termination and progress constructively in `ReachesPrefix`
without `Classical.choice` or coinduction? Because in `Trusted/StepResult.lean`
(lines 158–160), the `terminated` constructor of `ReachesPrefix`:
```lean
| terminated (n : Nat) (s : State) (term : TerminationKind Val) :
    step p s (.terminated term) →
    ReachesPrefix step p (n + 1) s [] (.terminated term)
```
is parameterized over **arbitrary remaining fuel `n : Nat`**. Once an execution
reaches a state `s_term` where `step p s_term (.terminated term)` holds in `k`
steps (consuming `k + 1` total fuel), supplying any larger fuel `m ≥ m₀` simply
leaves `m - k - 1` unused fuel at `s_term` and produces the exact same trace
`tr` and outcome `.terminated term`!
-/

/-- Auxiliary lemma for `reachesPrefix_terminated_add_fuel`. -/
theorem reachesPrefix_terminated_add_fuel_aux
    {Prog State Obs Val : Type}
    {step : Prog → State → StepResult State Obs Val → Prop}
    {p : Prog} {m₀ : Nat} {s : State} {tr : List Obs}
    {out : PrefixOutcome Val}
    (h : ReachesPrefix step p m₀ s tr out) (d : Nat) :
    ∀ (term : TerminationKind Val),
      out = .terminated term →
      ReachesPrefix step p (m₀ + d) s tr (.terminated term) := by
  induction h with
  | zero =>
    intro _ hout; cases hout
  | terminated n s₀ term' hstep =>
    intro term hout
    injection hout with hterm
    subst hterm
    have heq : n + 1 + d = (n + d) + 1 := Nat.succ_add n d
    rw [heq]
    exact ReachesPrefix.terminated (n + d) s₀ term' hstep
  | failed _ _ _ =>
    intro _ hout; cases hout
  | step n s₁ s₂ e tr' out' hstep _ ih =>
    intro term hout
    have hih := ih term hout
    have heq : n + 1 + d = (n + d) + 1 := Nat.succ_add n d
    rw [heq]
    exact ReachesPrefix.step (n + d) s₁ s₂ e tr' (.terminated term) hstep hih
  | choice n s₁ s₂ branches tr' out' hstep hb _ ih =>
    intro term hout
    have hih := ih term hout
    have heq : n + 1 + d = (n + d) + 1 := Nat.succ_add n d
    rw [heq]
    exact ReachesPrefix.choice (n + d) s₁ s₂ branches tr' (.terminated term) hstep hb hih
  | noStep _ _ _ =>
    intro _ hout; cases hout
  | emptyChoice _ _ _ _ _ =>
    intro _ hout; cases hout

/-- Adding extra fuel `d : Nat` to a terminating `ReachesPrefix` derivation
    preserves both the trace `tr` and the terminal outcome `.terminated term`. -/
theorem reachesPrefix_terminated_add_fuel
    {Prog State Obs Val : Type}
    {step : Prog → State → StepResult State Obs Val → Prop}
    {p : Prog} {m₀ : Nat} {s : State} {tr : List Obs}
    {term : TerminationKind Val}
    (h : ReachesPrefix step p m₀ s tr (.terminated term)) (d : Nat) :
    ReachesPrefix step p (m₀ + d) s tr (.terminated term) :=
  reachesPrefix_terminated_add_fuel_aux h d term rfl

/-- **Fuel-Absorption Theorem (`reachesPrefix_terminated_mono`):**
    If `ReachesPrefix step p m₀ s tr (.terminated term)` holds, then for every
    step budget `m` with `m₀ ≤ m`, `ReachesPrefix step p m s tr (.terminated term)`
    also holds. -/
theorem reachesPrefix_terminated_mono
    {Prog State Obs Val : Type}
    {step : Prog → State → StepResult State Obs Val → Prop}
    {p : Prog} {m₀ m : Nat} {s : State} {tr : List Obs}
    {term : TerminationKind Val}
    (h : ReachesPrefix step p m₀ s tr (.terminated term))
    (hle : m₀ ≤ m) :
    ReachesPrefix step p m s tr (.terminated term) := by
  have hd : m₀ + (m - m₀) = m := Nat.add_sub_of_le hle
  rw [← hd]
  exact reachesPrefix_terminated_add_fuel h (m - m₀)

/-- General uniqueness of `ReachesPrefix` outcomes and traces for any
    deterministic step relation that does not use `.choice`. -/
theorem reachesPrefix_det_unique
    {Prog State Obs Val : Type}
    {step : Prog → State → StepResult State Obs Val → Prop}
    (hdet : ∀ p s r₁ r₂, step p s r₁ → step p s r₂ → r₁ = r₂)
    (hnochoice : ∀ p s P, ¬ step p s (.choice P))
    {p : Prog} {n : Nat} {s : State}
    {tr₁ tr₂ : List Obs} {out₁ out₂ : PrefixOutcome Val}
    (h₁ : ReachesPrefix step p n s tr₁ out₁)
    (h₂ : ReachesPrefix step p n s tr₂ out₂) :
    tr₁ = tr₂ ∧ out₁ = out₂ := by
  induction h₁ generalizing tr₂ out₂ with
  | zero s₀ =>
    cases h₂ with
    | zero => exact ⟨rfl, rfl⟩
  | terminated m s₀ term hstep =>
    cases h₂ with
    | terminated _ _ term' h₂ =>
      have heq := hdet p s₀ _ _ hstep h₂
      injection heq with hterm
      subst hterm
      exact ⟨rfl, rfl⟩
    | failed _ _ h₂ =>
      have heq := hdet p s₀ _ _ hstep h₂; cases heq
    | step _ _ _ _ _ _ h₂ _ =>
      have heq := hdet p s₀ _ _ hstep h₂; cases heq
    | choice _ _ _ P _ _ h₂ _ _ =>
      exact False.elim (hnochoice p s₀ P h₂)
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.terminated term, hstep⟩)
    | emptyChoice _ _ P h₂ _ =>
      exact False.elim (hnochoice p s₀ P h₂)
  | failed m s₀ hstep =>
    cases h₂ with
    | terminated _ _ _ h₂ =>
      have heq := hdet p s₀ _ _ hstep h₂; cases heq
    | failed _ _ _ => exact ⟨rfl, rfl⟩
    | step _ _ _ _ _ _ h₂ _ =>
      have heq := hdet p s₀ _ _ hstep h₂; cases heq
    | choice _ _ _ P _ _ h₂ _ _ =>
      exact False.elim (hnochoice p s₀ P h₂)
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.failed, hstep⟩)
    | emptyChoice _ _ P h₂ _ =>
      exact False.elim (hnochoice p s₀ P h₂)
  | step m s₁ s₂ e tr₁' out₁ hstep hrest ih =>
    cases h₂ with
    | terminated _ _ _ h₂ =>
      have heq := hdet p s₁ _ _ hstep h₂; cases heq
    | failed _ _ h₂ =>
      have heq := hdet p s₁ _ _ hstep h₂; cases heq
    | step _ _ s₂' e' tr₂' _ h₂ hr₂ =>
      have heq := hdet p s₁ _ _ hstep h₂
      injection heq with he hs
      subst he hs
      have hih := ih hr₂
      rw [hih.1, hih.2]
      exact ⟨rfl, rfl⟩
    | choice _ _ _ P _ _ h₂ _ _ =>
      exact False.elim (hnochoice p s₁ P h₂)
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.step e s₂, hstep⟩)
    | emptyChoice _ _ P h₂ _ =>
      exact False.elim (hnochoice p s₁ P h₂)
  | choice m s₁ s₂ P _ _ hstep _ _ _ =>
    exact False.elim (hnochoice p s₁ P hstep)
  | noStep m s₀ hno =>
    cases h₂ with
    | terminated _ _ term h₂ => exact False.elim (hno ⟨.terminated term, h₂⟩)
    | failed _ _ h₂ => exact False.elim (hno ⟨.failed, h₂⟩)
    | step _ _ s₂ e _ _ h₂ _ => exact False.elim (hno ⟨.step e s₂, h₂⟩)
    | choice _ _ _ P _ _ h₂ _ _ => exact False.elim (hno ⟨.choice P, h₂⟩)
    | noStep _ _ _ => exact ⟨rfl, rfl⟩
    | emptyChoice _ _ P h₂ _ => exact False.elim (hno ⟨.choice P, h₂⟩)
  | emptyChoice m s₀ P hstep _ =>
    exact False.elim (hnochoice p s₀ P hstep)

/-- Inversion lemma for `ReachesPrefix MirStep` on a `.step` transition,
    tracking step budget `n = n' + 1`. -/
theorem reachesPrefix_mir_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalMirStepOpt body s = some (.step () s'))
    (hreach : ReachesPrefix MirStep body n s tr out) :
    (n = 0 ∧ tr = [] ∧ out = .running) ∨
    ∃ n' tr', n = n' + 1 ∧ tr = () :: tr' ∧
      ReachesPrefix MirStep body n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl ⟨rfl, rfl, rfl⟩
  | step n' _ s₂ _ tr' _ h1 hr =>
    have h1' : some (StepResult.step () s₂) = evalMirStepOpt body s := h1
    rw [hstep] at h1'
    injection h1' with hstep_eq
    injection hstep_eq with _ hs
    subst hs
    exact Or.inr ⟨n', tr', rfl, rfl, hr⟩
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨.step () s', hstep.symm⟩)

/-- Inversion lemma for `ReachesPrefix MirStep` on a `.terminated` transition,
    tracking step budget `n = m + 1`. -/
theorem reachesPrefix_mir_of_terminated
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {term : TerminationKind MirVal}
    (hstep : evalMirStepOpt body s = some (.terminated term))
    (hreach : ReachesPrefix MirStep body n s tr out) :
    (n = 0 ∧ tr = [] ∧ out = .running) ∨
    (∃ m, n = m + 1 ∧ tr = [] ∧ out = .terminated term) := by
  cases hreach with
  | zero => exact Or.inl ⟨rfl, rfl, rfl⟩
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated m _ term' h1 =>
    have h1' : some (StepResult.terminated term') = evalMirStepOpt body s := h1
    rw [hstep] at h1'
    injection h1' with hterm
    injection hterm with heq
    subst heq
    exact Or.inr ⟨m, rfl, rfl, rfl⟩
  | failed _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨.terminated term, hstep.symm⟩)

/-!
### 5.3 Constructive Step-Dilated Prefix Simulation (`π_dilated k`)

We now define `π_dilated (k : Nat) : MirLang.Behavior → X86Lang.Behavior`.
A target step budget `n` corresponds to any source step budget `m` in the window
`DilationWindow k m n`:
- Either `n = 0 ∧ m = 0`, or
- `n ≤ k * m ∧ m ≤ n` (i.e., each source step expands to between `1` and `k`
  target steps, so `m` source steps correspond to `n ∈ [m, k * m]` target steps).

At target query `q_tgt`:
1. `(π_dilated k B q_tgt).defined` requires `(B q_src).defined` for all matching
   `q_src` whose step budget `q_src.steps` lies in `DilationWindow k q_src.steps q_tgt.steps`.
2. `(π_dilated k B q_tgt).val h out_tgt` requires that there exist a matching
   `q_src` with `DilationWindow k q_src.steps q_tgt.steps` and a source trace
   `tr_src : List Unit` such that `(B q_src).val ... ⟨tr_src, out_tgt.outcome⟩`
   holds.
-/

/-- Step-dilation window relating source step budget `m` and target step budget
    `n` under maximum expansion factor `k`. -/
def DilationWindow (k m n : Nat) : Prop :=
  (m = 0 ∧ n = 0) ∨ (n ≤ k * m ∧ m ≤ n)

/-- Constructive step-dilated cross-language refinement injection `π_dilated k`. -/
def π_dilated (k : Nat) (B : MirLang.Behavior) : X86Lang.Behavior :=
  fun q_tgt => {
    defined := ∀ q_src : MirLang.Query,
      matchQuery q_src.init q_tgt.init →
      DilationWindow k q_src.steps q_tgt.steps →
      (B q_src).defined
    val := fun h out_tgt =>
      ∃ q_src : MirLang.Query,
        ∃ h_match : matchQuery q_src.init q_tgt.init,
        ∃ h_win : DilationWindow k q_src.steps q_tgt.steps,
        ∃ tr_src : List Unit,
          (B q_src).val (h q_src h_match h_win)
            { trace := tr_src, outcome := out_tgt.outcome }
  }

/-- Step-dilated compilation judgment with expansion factor `k`. -/
def Compiles_dilated (k : Nat) (x86 : X86Body) (mir : MirBody) : Prop :=
  X86Sem x86 ≤ π_dilated k (MirSem mir)

/-- **Theorem (Constructive Monotonicity of `π_dilated`):**
    `π_dilated k` is `Monotone` for every `k : Nat`, proved constructively with
    zero `Classical.choice`. -/
theorem monotone_π_dilated (k : Nat) : Monotone (π_dilated k) := by
  intro B₁ B₂ hle q_tgt hdef₁
  refine ⟨?_, ?_⟩
  · intro q_src hmatch hwin
    exact (hle q_src (hdef₁ q_src hmatch hwin)).1
  · intro out_tgt hval₁
    cases hval₁ with
    | intro q_src h1 =>
    cases h1 with
    | intro hmatch h2 =>
    cases h2 with
    | intro hwin h3 =>
    cases h3 with
    | intro tr_src hval_src =>
      cases hle q_src (hdef₁ q_src hmatch hwin) with
      | intro _ hval_le =>
        exact ⟨q_src, hmatch, hwin, tr_src,
          hval_le { trace := tr_src, outcome := out_tgt.outcome } hval_src⟩

/-!
### 5.4 `π_dilated k` Rejects `loopCodegen` and `unwindCodegen` on Terminating Programs

Consider the terminating source MIR identity function `idCopyBody`:
```
fn id_copy(x: usize) -> usize {
    bb0: _0 = copy _1; return;
}
```
Starting from any valid entry state with `_1 = .usize 42`, `idCopyBody`
terminates normally with `.terminated (.normal (.usize 42))` at step budget
`m₀ = 2`. By fuel absorption (`reachesPrefix_mir_terminated_at_ge`), at EVERY
source budget `m ≥ 2`, `idCopyBody` has sole reachable outcome
`.terminated (.normal (.usize 42))`.

Now consider target step budget `n = 2 * k` (with `k ≥ 1`). For any source step
budget `m` in `DilationWindow k m (2 * k)`:
- Since `2 * k ≥ 2 > 0`, the `(m = 0 ∧ n = 0)` branch is impossible.
- In the `2 * k ≤ k * m ∧ m ≤ 2 * k` branch, since `k ≥ 1`, cancelling `k` yields
  `2 ≤ m`!
Therefore, every source budget `m` in the dilation window at `n = 2 * k` has `m ≥ 2`
and thus outcome `.terminated (.normal (.usize 42))`. Neither `loopCodegen`
(outcome `.running`) nor `unwindCodegen` (outcome `.terminated .unwind`) can
match this outcome!
-/

/-- Canonical terminating MIR identity function (`_0 = copy _1; return;`). -/
def idCopyBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- `idCopyBody` terminates at step 2 with `.terminated (.normal v)`. -/
theorem idCopyBody_terminates_at_2 (locals0 : Nat → Option MirVal)
    (tySizes0 : Nat → Nat) (v : MirVal)
    (hv1 : locals0 1 = some v) :
    let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
    ReachesPrefix MirStep idCopyBody 2 s0 [()] (.terminated (.normal v)) := by
  intro s0
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some v)
    block := 0
    stmtIdx := 1
    tySizes := tySizes0
  }
  have hstep0 : MirStep idCopyBody s0 (.step () s1) := by
    change some (.step () s1) = evalMirStmtOpt s0 (.assign ⟨0⟩ (.use (.copy ⟨1⟩)))
    dsimp only [evalMirStmtOpt, evalOperand, s0]
    rw [hv1]
  have hr1 : ReachesPrefix MirStep idCopyBody 1 s1 [] (.terminated (.normal v)) :=
    ReachesPrefix.terminated 0 s1 (.normal v) rfl
  exact ReachesPrefix.step 1 s0 s1 () [] (.terminated (.normal v)) hstep0 hr1

/-- For `idCopyBody`, at any step budget `m ≥ 2`, any `ReachesPrefix` from the
    initial state with `locals0 1 = some v` has outcome `.terminated (.normal v)`. -/
theorem idCopyBody_outcome_at_ge_2
    {locals0 : Nat → Option MirVal} {tySizes0 : Nat → Nat} {v : MirVal}
    {m : Nat} {tr : List Unit} {out : PrefixOutcome MirVal}
    (hv1 : locals0 1 = some v)
    (hle : 2 ≤ m)
    (hreach : ReachesPrefix MirStep idCopyBody m
      { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 } tr out) :
    out = .terminated (.normal v) := by
  let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
  let s1 : MirState := {
    locals := updateLocal locals0 0 (some v)
    block := 0
    stmtIdx := 1
    tySizes := tySizes0
  }
  have hstep0 : evalMirStepOpt idCopyBody s0 = some (.step () s1) := by
    change evalMirStmtOpt s0 (.assign ⟨0⟩ (.use (.copy ⟨1⟩))) = some (.step () s1)
    dsimp only [evalMirStmtOpt, evalOperand, s0]
    rw [hv1]
  cases reachesPrefix_mir_of_step hstep0 hreach with
  | inl h0 =>
    have hm0 : m = 0 := h0.1
    subst hm0
    cases hle
  | inr hex =>
    cases hex with
    | intro m1 htr1 =>
      cases htr1 with
      | intro tr1 hr1 =>
        have hstep1 : evalMirStepOpt idCopyBody s1 = some (.terminated (.normal v)) := rfl
        cases reachesPrefix_mir_of_terminated hstep1 hr1.2.2 with
        | inl h1 =>
          have hm1 : m1 = 0 := h1.1
          have hm : m = m1 + 1 := hr1.1
          subst hm1
          subst hm
          cases hle with
          | step hle1 => cases hle1
        | inr hterm =>
          cases hterm with
          | intro m2 hm2 => exact hm2.2.2

/-- Helper arithmetic lemma: if `1 ≤ k` and `2 * k ≤ k * m`, then `2 ≤ m`. -/
theorem two_le_of_two_mul_le_mul {k m : Nat} (hk : 1 ≤ k) (h : 2 * k ≤ k * m) :
    2 ≤ m := by
  cases m with
  | zero =>
    rw [Nat.mul_zero] at h
    have h2k : 2 ≤ 2 * k := Nat.mul_le_mul_left 2 hk
    have h0 : 2 ≤ 0 := Nat.le_trans h2k h
    cases h0
  | succ m' =>
    cases m' with
    | zero =>
      rw [Nat.mul_one] at h
      cases k with
      | zero => cases hk
      | succ k' =>
        have h2 : 2 * (k' + 1) = (k' + 1) + (k' + 1) := Nat.two_mul (k' + 1)
        rw [h2] at h
        have hlt : k' + 1 < (k' + 1) + (k' + 1) :=
          Nat.lt_add_of_pos_right (Nat.succ_pos k')
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt h))
    | succ m'' =>
      exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m''))

/-- Any `m` in `DilationWindow k m (2 * k)` for `1 ≤ k` satisfies `2 ≤ m`. -/
theorem two_le_of_dilationWindow_two_mul {k m : Nat} (hk : 1 ≤ k)
    (hwin : DilationWindow k m (2 * k)) : 2 ≤ m := by
  cases hwin with
  | inl h0 =>
    have h2k : 2 * k = 0 := h0.2
    cases k with
    | zero => cases hk
    | succ k' =>
      have hpos : 0 < 2 * (k' + 1) := Nat.mul_pos (by decide) (Nat.succ_pos k')
      rw [h2k] at hpos
      cases hpos
  | inr hbounds =>
    exact two_le_of_two_mul_le_mul hk hbounds.1

/-- `MonoAdmitted tySizes idCopyBody` holds unconditionally because `idCopyBody`
    has no `requiredConsts` and no call terminators. -/
theorem idCopyBody_monoAdmitted (tySizes : Nat → Nat) :
    MonoAdmitted tySizes idCopyBody := by
  intro tySizes' c hreq
  cases hreq with
  | direct hmem => cases hmem
  | nested hmem _ => cases hmem
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ hnil => cases hnil

/-- Any query on `idCopyBody` from the standard entry state with `_1 = .usize 42`
    is `.defined` in `MirSem idCopyBody`. -/
theorem idCopyBody_defined_at (steps : Nat) (s : MirState)
    (hentry : initEntryState idCopyBody s) :
    (MirSem idCopyBody { init := s, steps := steps }).defined := by
  intro ⟨_, _⟩ tr out hreach
  cases s with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    subst hb hs hc hst
    cases hentry.2.2.2.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
      let s1 : MirState := {
        locals := updateLocal locals0 0 (some v)
        block := 0
        stmtIdx := 1
        tySizes := tySizes0
      }
      have hstep0 : evalMirStepOpt idCopyBody s0 = some (.step () s1) := by
        change evalMirStmtOpt s0 (.assign ⟨0⟩ (.use (.copy ⟨1⟩))) = some (.step () s1)
        dsimp only [evalMirStmtOpt, evalOperand, s0]
        rw [hv1]
      cases reachesPrefix_of_step hstep0 hreach with
      | inl hrun => rw [hrun]; exact True.intro
      | inr hex =>
        cases hex with
        | intro n1 htr1 =>
          cases htr1 with
          | intro tr1 hr1 =>
            cases reachesPrefix_of_terminated (term := .normal v) rfl hr1 with
            | inl hrun => rw [hrun]; exact True.intro
            | inr hterm => rw [hterm]; exact True.intro

/-- **Theorem (Progress Fix 1 — `π_dilated k` Rejects `loopCodegen` for all `k ≥ 1`):**
    For every dilation factor `k ≥ 1`, `loopCodegen idCopyBody` does NOT refine
    `idCopyBody` under `π_dilated k`! -/
theorem π_dilated_rejects_loopCodegen (k : Nat) (hk : 1 ≤ k) :
    ¬ Compiles_dilated k (loopCodegen idCopyBody) idCopyBody := by
  intro hcomp
  let regs0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 42))
  let s_x86 : X86State := {
    regs := regs0
    block := 0
    instrIdx := 0
  }
  have hrest : ∀ j, 2 ≤ j → regs0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ m =>
      cases m with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry_x86 : initX86EntryState (loopCodegen idCopyBody) s_x86 :=
    ⟨rfl, rfl, rfl, rfl, ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩⟩
  let q_tgt : X86Lang.Query := { init := s_x86, steps := 2 * k }
  have hdef_src : (π_dilated k (MirSem idCopyBody) q_tgt).defined := by
    intro q_src hmatch _
    have hentry_src : initEntryState idCopyBody q_src.init := by
      refine ⟨hmatch.2.1, hmatch.2.2.1, hmatch.2.2.2.2.1, hmatch.2.2.2.2.2.1, ?_, ?_⟩
      · rw [hmatch.1]; exact rfl
      · rw [hmatch.1, hmatch.2.2.2.1]
        exact ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩
    exact idCopyBody_defined_at q_src.steps q_src.init hentry_src
  cases hcomp q_tgt hdef_src with
  | intro hdef_tgt hval_le =>
    -- Construct the 2*k-step execution of `loopCodegen idCopyBody`
    have hloop_reach : ∃ tr, ReachesPrefix X86Step (loopCodegen idCopyBody) (2 * k) s_x86 tr .running := by
      generalize hN : 2 * k = N
      clear hN
      induction N with
      | zero => exact ⟨[], ReachesPrefix.zero s_x86⟩
      | succ m ih =>
        cases ih with
        | intro tr htr =>
          exact ⟨() :: tr, ReachesPrefix.step m s_x86 s_x86 () tr .running rfl htr⟩
    cases hloop_reach with
    | intro tr_tgt hreach_tgt =>
      have hval_tgt : (X86Sem (loopCodegen idCopyBody) q_tgt).val hdef_tgt
          { trace := tr_tgt, outcome := .running } :=
        ⟨hentry_x86, hreach_tgt⟩
      have hval_dil := hval_le { trace := tr_tgt, outcome := .running } hval_tgt
      cases hval_dil with
      | intro q_src h1 =>
      cases h1 with
      | intro hmatch h2 =>
      cases h2 with
      | intro hwin h3 =>
      cases h3 with
      | intro tr_src hval_src =>
        have h2le : 2 ≤ q_src.steps := two_le_of_dilationWindow_two_mul hk hwin
        have hreach_src : ReachesPrefix MirStep idCopyBody q_src.steps q_src.init tr_src .running :=
          hval_src.2
        cases q_src with
        | mk init_src steps_src =>
        cases init_src with
        | mk locals_s block_s stmtIdx_s tySizes_s curBody_s stack_s =>
          have hloc : locals_s = regs0 := hmatch.1
          have hb : block_s = 0 := hmatch.2.1
          have hs : stmtIdx_s = 0 := hmatch.2.2.1
          have hc : curBody_s = none := hmatch.2.2.2.2.1
          have hst : stack_s = [] := hmatch.2.2.2.2.2.1
          subst hloc hb hs hc hst
          have hout_eq := idCopyBody_outcome_at_ge_2 (v := .usize 42) rfl h2le hreach_src
          cases hout_eq

/-- **Theorem (Progress Fix 2 — `π_dilated k` Rejects `unwindCodegen` for all `k ≥ 1`):**
    For every dilation factor `k ≥ 1`, `unwindCodegen idCopyBody` does NOT refine
    `idCopyBody` under `π_dilated k`! -/
theorem π_dilated_rejects_unwindCodegen (k : Nat) (hk : 1 ≤ k) :
    ¬ Compiles_dilated k (unwindCodegen idCopyBody) idCopyBody := by
  intro hcomp
  let regs0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 42))
  let s_x86 : X86State := {
    regs := regs0
    block := 0
    instrIdx := 0
  }
  have hrest : ∀ j, 2 ≤ j → regs0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ m =>
      cases m with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry_x86 : initX86EntryState (unwindCodegen idCopyBody) s_x86 :=
    ⟨rfl, rfl, rfl, rfl, ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩⟩
  let q_tgt : X86Lang.Query := { init := s_x86, steps := 2 * k }
  have hdef_src : (π_dilated k (MirSem idCopyBody) q_tgt).defined := by
    intro q_src hmatch _
    have hentry_src : initEntryState idCopyBody q_src.init := by
      refine ⟨hmatch.2.1, hmatch.2.2.1, hmatch.2.2.2.2.1, hmatch.2.2.2.2.2.1, ?_, ?_⟩
      · rw [hmatch.1]; exact rfl
      · rw [hmatch.1, hmatch.2.2.2.1]
        exact ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩
    exact idCopyBody_defined_at q_src.steps q_src.init hentry_src
  cases hcomp q_tgt hdef_src with
  | intro hdef_tgt hval_le =>
    have h2k_pos : ∃ m, 2 * k = m + 1 := by
      cases k with
      | zero => cases hk
      | succ k' => exact ⟨2 * k' + 1, rfl⟩
    cases h2k_pos with
    | intro m hm =>
      have hreach_tgt : ReachesPrefix X86Step (unwindCodegen idCopyBody) (2 * k) s_x86 [] (.terminated .unwind) := by
        rw [hm]
        exact ReachesPrefix.terminated m s_x86 .unwind rfl
      have hval_tgt : (X86Sem (unwindCodegen idCopyBody) q_tgt).val hdef_tgt
          { trace := [], outcome := .terminated .unwind } :=
        ⟨hentry_x86, hreach_tgt⟩
      have hval_dil := hval_le { trace := [], outcome := .terminated .unwind } hval_tgt
      cases hval_dil with
      | intro q_src h1 =>
      cases h1 with
      | intro hmatch h2 =>
      cases h2 with
      | intro hwin h3 =>
      cases h3 with
      | intro tr_src hval_src =>
        have h2le : 2 ≤ q_src.steps := two_le_of_dilationWindow_two_mul hk hwin
        have hreach_src : ReachesPrefix MirStep idCopyBody q_src.steps q_src.init tr_src (.terminated .unwind) :=
          hval_src.2
        cases q_src with
        | mk init_src steps_src =>
        cases init_src with
        | mk locals_s block_s stmtIdx_s tySizes_s curBody_s stack_s =>
          have hloc : locals_s = regs0 := hmatch.1
          have hb : block_s = 0 := hmatch.2.1
          have hs : stmtIdx_s = 0 := hmatch.2.2.1
          have hc : curBody_s = none := hmatch.2.2.2.2.1
          have hst : stack_s = [] := hmatch.2.2.2.2.2.1
          subst hloc hb hs hc hst
          have hout_eq := idCopyBody_outcome_at_ge_2 (v := .usize 42) rfl h2le hreach_src
          cases hout_eq

/-!
### 5.5 `π_dilated 2` Admits $1 \to 2$ Instruction Expansion While Lockstep `π` Rejects It

To verify that `π_dilated k` genuinely supports multi-instruction codegen
expansion (where 1 MIR step compiles to up to `k` x86 steps), consider
`idCopyX86_2x`, which lowers `_0 = copy _1` into two `movReg` instructions
(`mov r1, r1; mov r0, r1; ret`).
- At `n = 2`, `idCopyBody` has already terminated (`outcome = .terminated (.normal v)`),
  whereas `idCopyX86_2x` is still `.running` (`trace = [(), ()]`).
- Therefore, lockstep `Compiles idCopyX86_2x idCopyBody` is **FALSE**!
- Under `Compiles_dilated 2 idCopyX86_2x idCopyBody`, however:
  - At `n = 0`, `m = 0` matches `.running`.
  - At `n = 1`, `m = 1` (`1 ≤ 2 * 1 ∧ 1 ≤ 1`) matches `.running`.
  - At `n = 2`, `m = 1` (`2 ≤ 2 * 1 ∧ 1 ≤ 2`) matches `.running`!
  - At `n ≥ 3`, `m = n` (`n ≤ 2 * n ∧ n ≤ n`) matches `.terminated (.normal v)`!
-/

/-- 2x-expanded x86 compilation of `idCopyBody`:
    `bb0: mov r1, r1; mov r0, r1; ret`. -/
def idCopyX86_2x : X86Body where
  argTys := [.usize]
  retTy := .usize
  regCount := 2
  blocks := [
    { instrs := [.movReg ⟨1⟩ ⟨1⟩, .movReg ⟨0⟩ ⟨1⟩]
      terminator := .ret }
  ]
  requiredConsts := []

/-- Lockstep `CompilesX86` REJECTS the 2x-expanded compilation `idCopyX86_2x`! -/
theorem lockstep_compiles_rejects_idCopyX86_2x :
    ¬ CompilesX86 idCopyX86_2x idCopyBody := by
  intro hcomp
  let regs0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 42))
  let s_x86 : X86State := { regs := regs0, block := 0, instrIdx := 0 }
  have hrest : ∀ j, 2 ≤ j → regs0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ m =>
      cases m with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry_x86 : initX86EntryState idCopyX86_2x s_x86 :=
    ⟨rfl, rfl, rfl, rfl, ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩⟩
  let q_tgt : X86Lang.Query := { init := s_x86, steps := 2 }
  have hdef_src : (π (MirSem idCopyBody) q_tgt).defined := by
    intro q_src hmatch _
    have hentry_src : initEntryState idCopyBody q_src.init := by
      refine ⟨hmatch.2.1, hmatch.2.2.1, hmatch.2.2.2.2.1, hmatch.2.2.2.2.2.1, ?_, ?_⟩
      · rw [hmatch.1]; exact rfl
      · rw [hmatch.1, hmatch.2.2.2.1]
        exact ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩
    exact idCopyBody_defined_at q_src.steps q_src.init hentry_src
  cases hcomp q_tgt hdef_src with
  | intro hdef_tgt hval_le =>
    let s1 : X86State := { regs := updateReg regs0 1 (some (.usize 42)), block := 0, instrIdx := 1 }
    let s2 : X86State := { regs := updateReg s1.regs 0 (some (.usize 42)), block := 0, instrIdx := 2 }
    have hr2 : ReachesPrefix X86Step idCopyX86_2x 0 s2 [] .running := ReachesPrefix.zero s2
    have hr1 : ReachesPrefix X86Step idCopyX86_2x 1 s1 [()] .running :=
      ReachesPrefix.step 0 s1 s2 () [] .running rfl hr2
    have hr0 : ReachesPrefix X86Step idCopyX86_2x 2 s_x86 [(), ()] .running :=
      ReachesPrefix.step 1 s_x86 s1 () [()] .running rfl hr1
    have hval_tgt : (X86Sem idCopyX86_2x q_tgt).val hdef_tgt { trace := [(), ()], outcome := .running } :=
      ⟨hentry_x86, hr0⟩
    have hval_pi := hval_le { trace := [(), ()], outcome := .running } hval_tgt
    cases hval_pi with
    | intro q_src h1 =>
    cases h1 with
    | intro hmatch h2 =>
    cases h2 with
    | intro hsteps hval_src =>
      have hreach_src := hval_src.2
      cases q_src with
      | mk init_src steps_src =>
      cases init_src with
      | mk locals_s block_s stmtIdx_s tySizes_s curBody_s stack_s =>
        dsimp at hsteps
        have hloc : locals_s = regs0 := hmatch.1
        have hb : block_s = 0 := hmatch.2.1
        have hs : stmtIdx_s = 0 := hmatch.2.2.1
        have hc : curBody_s = none := hmatch.2.2.2.2.1
        have hst : stack_s = [] := hmatch.2.2.2.2.2.1
        subst hsteps hloc hb hs hc hst
        have hout_eq := idCopyBody_outcome_at_ge_2 (v := .usize 42) rfl (Nat.le_refl 2) hreach_src
        cases hout_eq

/-- **Theorem (Progress Fix 3 — `π_dilated 2` Admits 2x Instruction Expansion):**
    `idCopyX86_2x` is a verified compilation of `idCopyBody` under
    `Compiles_dilated 2 idCopyX86_2x idCopyBody`! -/
theorem idCopyX86_2x_compiles_dilated_2 :
    Compiles_dilated 2 idCopyX86_2x idCopyBody := by
  intro q_tgt hdef_pi
  refine ⟨?_, ?_⟩
  · intro hentry tr out hreach
    cases q_tgt with
    | mk init_tgt steps_tgt =>
    cases init_tgt with
    | mk regs0 block0 instrIdx0 tySizes0 curBody0 =>
      have hb : block0 = 0 := hentry.1
      have hi : instrIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      subst hb hi hc
      cases hentry.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : regs0 1 = some v := hv.1
        let s0 : X86State := { regs := regs0, block := 0, instrIdx := 0, tySizes := tySizes0 }
        let s1 : X86State := { regs := updateReg regs0 1 (some v), block := 0, instrIdx := 1, tySizes := tySizes0 }
        let s2 : X86State := { regs := updateReg s1.regs 0 (some v), block := 0, instrIdx := 2, tySizes := tySizes0 }
        have hstep0 : evalX86Step idCopyX86_2x s0 = .step () s1 := by
          change evalX86Instr s0 (.movReg ⟨1⟩ ⟨1⟩) = .step () s1
          dsimp only [evalX86Instr, s0]
          rw [hv1]
        have hs1_1 : s1.regs 1 = some v := rfl
        have hstep1 : evalX86Step idCopyX86_2x s1 = .step () s2 := by
          change evalX86Instr s1 (.movReg ⟨0⟩ ⟨1⟩) = .step () s2
          dsimp only [evalX86Instr, s1, updateReg]
          rfl
        have hstep2 : evalX86Step idCopyX86_2x s2 = .terminated (.normal v) := rfl
        cases reachesPrefix_x86_of_step hstep0 hreach with
        | inl h0 => rw [h0.2.2]; exact True.intro
        | inr hex1 =>
          cases hex1 with
          | intro n1 htr1 =>
            cases htr1 with
            | intro tr1 hr1 =>
              cases reachesPrefix_x86_of_step hstep1 hr1.2.2 with
              | inl h1 => rw [h1.2.2]; exact True.intro
              | inr hex2 =>
                cases hex2 with
                | intro n2 htr2 =>
                  cases htr2 with
                  | intro tr2 hr2 =>
                    cases reachesPrefix_x86_of_terminated hstep2 hr2.2.2 with
                    | inl h2 => rw [h2.2.2]; exact True.intro
                    | inr hterm =>
                      cases hterm with
                      | intro m hm => rw [hm.2.2]; exact True.intro
  · intro out_tgt hval_tgt
    dsimp [π_dilated, MirSem, MirLang, SmallStepMachine.toLanguage, BehaviorOf]
    have hentry := hval_tgt.1
    have hreach := hval_tgt.2
    cases q_tgt with
    | mk init_tgt steps_tgt =>
    cases init_tgt with
    | mk regs0 block0 instrIdx0 tySizes0 curBody0 =>
      have hb : block0 = 0 := hentry.1
      have hi : instrIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      subst hb hi hc
      let s_mir : MirState := {
        locals := regs0
        block := 0
        stmtIdx := 0
        tySizes := tySizes0
        curBody := none
        stack := []
      }
      have hmatch : matchQuery s_mir { regs := regs0, block := 0, instrIdx := 0, tySizes := tySizes0, curBody := none } :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hentry_mir : initEntryState idCopyBody s_mir :=
        ⟨rfl, rfl, rfl, rfl, hentry.2.2.2.1, hentry.2.2.2.2⟩
      have hinit_mir : initMirState idCopyBody s_mir :=
        ⟨hentry_mir, idCopyBody_monoAdmitted tySizes0⟩
      cases hentry.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : regs0 1 = some v := hv.1
        let s0 : X86State := { regs := regs0, block := 0, instrIdx := 0, tySizes := tySizes0 }
        let s1 : X86State := { regs := updateReg regs0 1 (some v), block := 0, instrIdx := 1, tySizes := tySizes0 }
        let s2 : X86State := { regs := updateReg s1.regs 0 (some v), block := 0, instrIdx := 2, tySizes := tySizes0 }
        have hstep0 : evalX86Step idCopyX86_2x s0 = .step () s1 := by
          change evalX86Instr s0 (.movReg ⟨1⟩ ⟨1⟩) = .step () s1
          dsimp only [evalX86Instr, s0]
          rw [hv1]
        have hstep1 : evalX86Step idCopyX86_2x s1 = .step () s2 := by
          change evalX86Instr s1 (.movReg ⟨0⟩ ⟨1⟩) = .step () s2
          dsimp only [evalX86Instr, s1, updateReg]
          rfl
        have hstep2 : evalX86Step idCopyX86_2x s2 = .terminated (.normal v) := rfl
        let s_mir1 : MirState := {
          locals := updateLocal regs0 0 (some v)
          block := 0
          stmtIdx := 1
          tySizes := tySizes0
        }
        have hmir_step0 : MirStep idCopyBody s_mir (.step () s_mir1) := by
          change some (.step () s_mir1) = evalMirStmtOpt s_mir (.assign ⟨0⟩ (.use (.copy ⟨1⟩)))
          dsimp only [evalMirStmtOpt, evalOperand, s_mir]
          rw [hv1]
        have hmir_reach1 : ReachesPrefix MirStep idCopyBody 1 s_mir [()] .running :=
          ReachesPrefix.step 0 s_mir s_mir1 () [] .running hmir_step0 (ReachesPrefix.zero s_mir1)
        cases reachesPrefix_x86_of_step hstep0 hreach with
        | inl h0 =>
          have hst0 : steps_tgt = 0 := h0.1
          subst hst0
          rw [h0.2.2]
          have hwin0 : DilationWindow 2 0 0 := Or.inl ⟨rfl, rfl⟩
          exact ⟨{ init := s_mir, steps := 0 }, hmatch, hwin0, [],
            ⟨hinit_mir, ReachesPrefix.zero s_mir⟩⟩
        | inr hex1 =>
          cases hex1 with
          | intro n1 htr1 =>
            cases htr1 with
            | intro tr1 hr1 =>
              cases reachesPrefix_x86_of_step hstep1 hr1.2.2 with
              | inl h1 =>
                have hn1 : n1 = 0 := h1.1
                subst hn1
                have hst1 : steps_tgt = 1 := hr1.1
                subst hst1
                rw [h1.2.2]
                have hwin1 : DilationWindow 2 1 1 := Or.inr ⟨by decide, by decide⟩
                exact ⟨{ init := s_mir, steps := 1 }, hmatch, hwin1, [()],
                  ⟨hinit_mir, hmir_reach1⟩⟩
              | inr hex2 =>
                cases hex2 with
                | intro n2 htr2 =>
                  cases htr2 with
                  | intro tr2 hr2 =>
                    cases reachesPrefix_x86_of_terminated hstep2 hr2.2.2 with
                    | inl h2 =>
                      have hn2 : n2 = 0 := h2.1
                      subst hn2
                      have hn1 : n1 = 1 := hr2.1
                      subst hn1
                      have hst2 : steps_tgt = 2 := hr1.1
                      subst hst2
                      rw [h2.2.2]
                      have hwin2 : DilationWindow 2 1 2 := Or.inr ⟨by decide, by decide⟩
                      exact ⟨{ init := s_mir, steps := 1 }, hmatch, hwin2, [()],
                        ⟨hinit_mir, hmir_reach1⟩⟩
                    | inr hterm =>
                      cases hterm with
                      | intro m hm =>
                        have h3 : n2 = m + 1 := hm.1
                        subst h3
                        have h2 : n1 = m + 1 + 1 := hr2.1
                        subst h2
                        have h1 : steps_tgt = m + 1 + 1 + 1 := hr1.1
                        subst h1
                        have hge2 : 2 ≤ m + 1 + 1 + 1 :=
                          Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le (m + 1)))
                        rw [hm.2.2]
                        have hwin_m : DilationWindow 2 (m + 1 + 1 + 1) (m + 1 + 1 + 1) :=
                          Or.inr ⟨Nat.le_mul_of_pos_left _ (by decide), Nat.le_refl _⟩
                        have hmir_term2 := idCopyBody_terminates_at_2 regs0 tySizes0 v hv1
                        have hmir_term_m := reachesPrefix_terminated_mono hmir_term2 hge2
                        exact ⟨{ init := s_mir, steps := m + 1 + 1 + 1 }, hmatch, hwin_m, [()],
                          ⟨hinit_mir, hmir_term_m⟩⟩

/-!
### 5.6 `π_dilated k` Admits Legitimate Source Infinite Loops and Unwinds

When the source MIR program itself loops (`mirLoopBody : bb0: goto bb0`) or
panics (`panicConst : bb0: panic`), `Compiles_dilated k` holds for every `k ≥ 1`.
-/

/-- Legitimate source MIR infinite loop (`bb0: goto 0`). -/
def mirLoopBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [
    { stmts := []
      terminator := .goto ⟨0⟩ }
  ]

/-- `mirLoopBody` can reach `.running` at every step budget `m`. -/
theorem mirLoopBody_reaches_running (m : Nat) (s : MirState)
    (hb : s.block = 0) (hs : s.stmtIdx = 0) (hc : s.curBody = none) :
    ∃ tr, ReachesPrefix MirStep mirLoopBody m s tr .running := by
  induction m with
  | zero => exact ⟨[], ReachesPrefix.zero s⟩
  | succ m' ih =>
    cases ih with
    | intro tr htr =>
      have hstep : MirStep mirLoopBody s (.step () s) := by
        cases s with
        | mk locals block stmtIdx tySizes curBody stack =>
          dsimp at hb hs hc
          subst hb hs hc
          rfl
      exact ⟨() :: tr, ReachesPrefix.step m' s s () tr .running hstep htr⟩

/-- `MonoAdmitted tySizes mirLoopBody` holds for all `tySizes`. -/
theorem mirLoopBody_monoAdmitted (tySizes : Nat → Nat) :
    MonoAdmitted tySizes mirLoopBody := by
  intro tySizes' c hreq
  cases hreq with
  | direct hmem => cases hmem
  | nested hmem _ => cases hmem
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ hnil => cases hnil

/-- **Theorem (Progress Fix 4 — Legitimate Source Loop Admitted):**
    When the source MIR function is `mirLoopBody`, `loopCodegen mirLoopBody`
    satisfies `Compiles_dilated k (loopCodegen mirLoopBody) mirLoopBody` for all
    `k ≥ 1`! -/
theorem mirLoopBody_compiles_dilated (k : Nat) (hk : 1 ≤ k) :
    Compiles_dilated k (loopCodegen mirLoopBody) mirLoopBody := by
  intro q_tgt _
  refine ⟨?_, ?_⟩
  · intro hentry tr out hreach
    have hout := loopCodegen_always_running mirLoopBody q_tgt.steps q_tgt.init tr out
      hentry.1 hentry.2.1 hentry.2.2.1 hreach
    rw [hout]
    exact True.intro
  · intro out_tgt hval_tgt
    dsimp [π_dilated]
    have hentry := hval_tgt.1
    have hreach := hval_tgt.2
    have hout := loopCodegen_always_running mirLoopBody q_tgt.steps q_tgt.init
      out_tgt.trace out_tgt.outcome hentry.1 hentry.2.1 hentry.2.2.1 hreach
    rw [hout]
    let s_mir : MirState := {
      locals := q_tgt.init.regs
      block := 0
      stmtIdx := 0
      tySizes := q_tgt.init.tySizes
      curBody := none
      stack := []
    }
    have hmatch : matchQuery s_mir q_tgt.init :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, hentry.1, hentry.2.1, hentry.2.2.1⟩
    have hentry_mir : initEntryState mirLoopBody s_mir :=
      ⟨rfl, rfl, rfl, rfl, hentry.2.2.2.1, hentry.2.2.2.2⟩
    have hinit_mir : initMirState mirLoopBody s_mir :=
      ⟨hentry_mir, mirLoopBody_monoAdmitted q_tgt.init.tySizes⟩
    have hwin : DilationWindow k q_tgt.steps q_tgt.steps := by
      cases q_tgt.steps with
      | zero => exact Or.inl ⟨rfl, rfl⟩
      | succ n' =>
        exact Or.inr ⟨Nat.le_mul_of_pos_left (n' + 1) hk, Nat.le_refl (n' + 1)⟩
    cases mirLoopBody_reaches_running q_tgt.steps s_mir rfl rfl rfl with
    | intro tr_src hreach_src =>
      exact ⟨{ init := s_mir, steps := q_tgt.steps }, hmatch, hwin, tr_src,
        ⟨hinit_mir, hreach_src⟩⟩

/-- `MonoAdmitted tySizes panicConst` holds for all `tySizes`. -/
theorem panicConst_monoAdmitted (tySizes : Nat → Nat) :
    MonoAdmitted tySizes panicConst := by
  intro tySizes' c hreq
  cases hreq with
  | direct hmem => cases hmem
  | nested hmem _ => cases hmem
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ hnil => cases hnil

/-- **Theorem (Progress Fix 5 — Legitimate Source Unwind Admitted):**
    When the source MIR function is `panicConst` (`bb0: panic`),
    `unwindCodegen panicConst` satisfies
    `Compiles_dilated k (unwindCodegen panicConst) panicConst` for all `k ≥ 1`! -/
theorem panicConst_compiles_dilated (k : Nat) (hk : 1 ≤ k) :
    Compiles_dilated k (unwindCodegen panicConst) panicConst := by
  intro q_tgt _
  refine ⟨?_, ?_⟩
  · intro hentry tr out hreach
    cases unwindCodegen_always_running_or_unwind panicConst q_tgt.steps q_tgt.init
      tr out hentry.1 hentry.2.1 hentry.2.2.1 hreach with
    | inl hrun => rw [hrun.2.2]; exact True.intro
    | inr hunw =>
      cases hunw with
      | intro m hm => rw [hm.2.2]; exact True.intro
  · intro out_tgt hval_tgt
    dsimp [π_dilated]
    have hentry := hval_tgt.1
    have hreach := hval_tgt.2
    let s_mir : MirState := {
      locals := q_tgt.init.regs
      block := 0
      stmtIdx := 0
      tySizes := q_tgt.init.tySizes
      curBody := none
      stack := []
    }
    have hmatch : matchQuery s_mir q_tgt.init :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, hentry.1, hentry.2.1, hentry.2.2.1⟩
    have hentry_mir : initEntryState panicConst s_mir :=
      ⟨rfl, rfl, rfl, rfl, hentry.2.2.2.1, hentry.2.2.2.2⟩
    have hinit_mir : initMirState panicConst s_mir :=
      ⟨hentry_mir, panicConst_monoAdmitted q_tgt.init.tySizes⟩
    cases unwindCodegen_always_running_or_unwind panicConst q_tgt.steps q_tgt.init
      out_tgt.trace out_tgt.outcome hentry.1 hentry.2.1 hentry.2.2.1 hreach with
    | inl hrun =>
      rw [hrun.2.2]
      have hwin0 : DilationWindow k 0 q_tgt.steps := Or.inl ⟨rfl, hrun.1⟩
      exact ⟨{ init := s_mir, steps := 0 }, hmatch, hwin0, [],
        ⟨hinit_mir, ReachesPrefix.zero s_mir⟩⟩
    | inr hunw =>
      cases hunw with
      | intro m hm =>
        rw [hm.2.2]
        have hwin : DilationWindow k (m + 1) q_tgt.steps := by
          rw [hm.1]
          exact Or.inr ⟨Nat.le_mul_of_pos_left (m + 1) hk, Nat.le_refl (m + 1)⟩
        have hstep_mir : MirStep panicConst s_mir (.terminated .unwind) := rfl
        have hreach_src : ReachesPrefix MirStep panicConst (m + 1) s_mir [] (.terminated .unwind) :=
          ReachesPrefix.terminated m s_mir .unwind hstep_mir
        exact ⟨{ init := s_mir, steps := m + 1 }, hmatch, hwin, [],
          ⟨hinit_mir, hreach_src⟩⟩

/-!
### 5.7 Step-Bounded Total Specifications (`X86Lang.EnsuresEqArgTotal n₀`)

Complementing `π_dilated k` at the refinement boundary, we can also strengthen
top-level specifications from partial correctness (`EnsuresEqArg`) to
step-bounded total correctness (`EnsuresEqArgTotal n₀`), requiring that at any
step budget `q.steps ≥ n₀`, every execution in `val` has terminated normally with
the expected return value.
-/

/-- Step-bounded total specification on `X86Lang`: requires that at any step
    budget `q.steps ≥ n₀`, the execution outcome is `.terminated (.normal ret)`
    with `ret` equal to argument register 1. -/
def X86Lang.EnsuresEqArgTotal (n₀ : Nat) : X86Lang.Behavior :=
  fun q => {
    defined := True
    val := fun _ out =>
      out.outcome.isSafe ∧
      (n₀ ≤ q.steps →
        ∃ ret v,
          out.outcome = .terminated (.normal ret) ∧
          q.init.regs 1 = some v ∧
          ret = v)
  }

/-- `EnsuresEqArgTotal n₀` directly REJECTS `loopCodegen idCopyBody` for every
    step bound `n₀`! -/
theorem loopCodegen_rejected_by_ensuresEqArgTotal (n₀ : Nat) :
    ¬ (X86Sem (loopCodegen idCopyBody) ≤ X86Lang.EnsuresEqArgTotal n₀) := by
  intro htot
  let regs0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 42))
  let s_x86 : X86State := { regs := regs0, block := 0, instrIdx := 0 }
  have hrest : ∀ j, 2 ≤ j → regs0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ m =>
      cases m with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initX86EntryState (loopCodegen idCopyBody) s_x86 :=
    ⟨rfl, rfl, rfl, rfl, ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩⟩
  let q : X86Lang.Query := { init := s_x86, steps := n₀ }
  cases htot q True.intro with
  | intro hdef_tgt hval_le =>
    have hloop_reach : ∃ tr, ReachesPrefix X86Step (loopCodegen idCopyBody) n₀ s_x86 tr .running := by
      generalize hN : n₀ = N
      clear hN
      induction N with
      | zero => exact ⟨[], ReachesPrefix.zero s_x86⟩
      | succ m ih =>
        cases ih with
        | intro tr htr =>
          exact ⟨() :: tr, ReachesPrefix.step m s_x86 s_x86 () tr .running rfl htr⟩
    cases hloop_reach with
    | intro tr hreach =>
      have hval_tgt : (X86Sem (loopCodegen idCopyBody) q).val hdef_tgt
          { trace := tr, outcome := .running } :=
        ⟨hentry, hreach⟩
      have hval_spec := hval_le { trace := tr, outcome := .running } hval_tgt
      cases hval_spec.2 (Nat.le_refl n₀) with
      | intro ret hret =>
        cases hret with
        | intro v hv => cases hv.1

/-- `EnsuresEqArgTotal n₀` directly REJECTS `unwindCodegen idCopyBody` for every
    step bound `n₀`! -/
theorem unwindCodegen_rejected_by_ensuresEqArgTotal (n₀ : Nat) :
    ¬ (X86Sem (unwindCodegen idCopyBody) ≤ X86Lang.EnsuresEqArgTotal n₀) := by
  intro htot
  let regs0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.usize 42))
  let s_x86 : X86State := { regs := regs0, block := 0, instrIdx := 0 }
  have hrest : ∀ j, 2 ≤ j → regs0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ m =>
      cases m with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initX86EntryState (unwindCodegen idCopyBody) s_x86 :=
    ⟨rfl, rfl, rfl, rfl, ⟨⟨.usize 42, rfl, True.intro⟩, hrest⟩⟩
  let q : X86Lang.Query := { init := s_x86, steps := n₀ + 1 }
  cases htot q True.intro with
  | intro hdef_tgt hval_le =>
    have hreach : ReachesPrefix X86Step (unwindCodegen idCopyBody) (n₀ + 1) s_x86 [] (.terminated .unwind) :=
      ReachesPrefix.terminated n₀ s_x86 .unwind rfl
    have hval_tgt : (X86Sem (unwindCodegen idCopyBody) q).val hdef_tgt
        { trace := [], outcome := .terminated .unwind } :=
      ⟨hentry, hreach⟩
    have hval_spec := hval_le { trace := [], outcome := .terminated .unwind } hval_tgt
    have hle : n₀ ≤ n₀ + 1 := Nat.le_succ n₀
    cases hval_spec.2 hle with
    | intro ret hret =>
      cases hret with
      | intro v hv => cases hv.1

/-- Conversely, the legitimate 2x-expanded compilation `idCopyX86_2x`
    SATISFIES `X86Lang.EnsuresEqArgTotal 3`! -/
theorem idCopyX86_2x_satisfies_ensuresEqArgTotal_3 :
    X86Sem idCopyX86_2x ≤ X86Lang.EnsuresEqArgTotal 3 := by
  intro q _
  refine ⟨?_, ?_⟩
  · intro hentry tr out hreach
    cases q with
    | mk init_tgt steps_tgt =>
    cases init_tgt with
    | mk regs0 block0 instrIdx0 tySizes0 curBody0 =>
      have hb : block0 = 0 := hentry.1
      have hi : instrIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      subst hb hi hc
      cases hentry.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : regs0 1 = some v := hv.1
        let s0 : X86State := { regs := regs0, block := 0, instrIdx := 0, tySizes := tySizes0 }
        let s1 : X86State := { regs := updateReg regs0 1 (some v), block := 0, instrIdx := 1, tySizes := tySizes0 }
        let s2 : X86State := { regs := updateReg s1.regs 0 (some v), block := 0, instrIdx := 2, tySizes := tySizes0 }
        have hstep0 : evalX86Step idCopyX86_2x s0 = .step () s1 := by
          change evalX86Instr s0 (.movReg ⟨1⟩ ⟨1⟩) = .step () s1
          dsimp only [evalX86Instr, s0]
          rw [hv1]
        have hstep1 : evalX86Step idCopyX86_2x s1 = .step () s2 := by
          change evalX86Instr s1 (.movReg ⟨0⟩ ⟨1⟩) = .step () s2
          dsimp only [evalX86Instr, s1, updateReg]
          rfl
        have hstep2 : evalX86Step idCopyX86_2x s2 = .terminated (.normal v) := rfl
        cases reachesPrefix_x86_of_step hstep0 hreach with
        | inl h0 => rw [h0.2.2]; exact True.intro
        | inr hex1 =>
          cases hex1 with
          | intro n1 htr1 =>
            cases htr1 with
            | intro tr1 hr1 =>
              cases reachesPrefix_x86_of_step hstep1 hr1.2.2 with
              | inl h1 => rw [h1.2.2]; exact True.intro
              | inr hex2 =>
                cases hex2 with
                | intro n2 htr2 =>
                  cases htr2 with
                  | intro tr2 hr2 =>
                    cases reachesPrefix_x86_of_terminated hstep2 hr2.2.2 with
                    | inl h2 => rw [h2.2.2]; exact True.intro
                    | inr hterm =>
                      cases hterm with
                      | intro m hm => rw [hm.2.2]; exact True.intro
  · intro out hval
    dsimp [X86Lang.EnsuresEqArgTotal]
    have hentry := hval.1
    have hreach := hval.2
    cases q with
    | mk init_tgt steps_tgt =>
    cases init_tgt with
    | mk regs0 block0 instrIdx0 tySizes0 curBody0 =>
      have hb : block0 = 0 := hentry.1
      have hi : instrIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      subst hb hi hc
      cases hentry.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : regs0 1 = some v := hv.1
        let s0 : X86State := { regs := regs0, block := 0, instrIdx := 0, tySizes := tySizes0 }
        let s1 : X86State := { regs := updateReg regs0 1 (some v), block := 0, instrIdx := 1, tySizes := tySizes0 }
        let s2 : X86State := { regs := updateReg s1.regs 0 (some v), block := 0, instrIdx := 2, tySizes := tySizes0 }
        have hstep0 : evalX86Step idCopyX86_2x s0 = .step () s1 := by
          change evalX86Instr s0 (.movReg ⟨1⟩ ⟨1⟩) = .step () s1
          dsimp only [evalX86Instr, s0]
          rw [hv1]
        have hstep1 : evalX86Step idCopyX86_2x s1 = .step () s2 := by
          change evalX86Instr s1 (.movReg ⟨0⟩ ⟨1⟩) = .step () s2
          dsimp only [evalX86Instr, s1, updateReg]
          rfl
        have hstep2 : evalX86Step idCopyX86_2x s2 = .terminated (.normal v) := rfl
        cases reachesPrefix_x86_of_step hstep0 hreach with
        | inl h0 =>
          have hst0 : steps_tgt = 0 := h0.1
          subst hst0
          rw [h0.2.2]
          refine ⟨True.intro, fun hle => ?_⟩
          cases hle
        | inr hex1 =>
          cases hex1 with
          | intro n1 htr1 =>
            cases htr1 with
            | intro tr1 hr1 =>
              cases reachesPrefix_x86_of_step hstep1 hr1.2.2 with
              | inl h1 =>
                have hn1 : n1 = 0 := h1.1
                subst hn1
                have hst1 : steps_tgt = 1 := hr1.1
                subst hst1
                rw [h1.2.2]
                refine ⟨True.intro, fun hle => ?_⟩
                cases hle with
                | step hle1 => cases hle1
              | inr hex2 =>
                cases hex2 with
                | intro n2 htr2 =>
                  cases htr2 with
                  | intro tr2 hr2 =>
                    cases reachesPrefix_x86_of_terminated hstep2 hr2.2.2 with
                    | inl h2 =>
                      have hn2 : n2 = 0 := h2.1
                      subst hn2
                      have hn1 : n1 = 1 := hr2.1
                      subst hn1
                      have hst2 : steps_tgt = 2 := hr1.1
                      subst hst2
                      rw [h2.2.2]
                      refine ⟨True.intro, fun hle => ?_⟩
                      cases hle with
                      | step hle1 =>
                        cases hle1 with
                        | step hle2 => cases hle2
                    | inr hterm =>
                      cases hterm with
                      | intro m hm =>
                        rw [hm.2.2]
                        refine ⟨True.intro, fun _ => ⟨v, v, rfl, hv1, rfl⟩⟩

/-!
## 6. Unmodeled CTFE Operations Returning `.failed` vs. Explicit PME `.terminated .unwind` (`ConstIsSafe`)

In `Trusted/MirSemantics.lean` (lines 296–302, 497–571) and
`theory/Anneal/MirSemantics.lean` (lines 112–162), `evalMirStep` returns
`StepResult.failed` (`PrefixOutcome.failed`) not only on genuine CTFE undefined
behavior, but also when a modeled statement or terminator encounters an
unmodeled sub-case—such as `evalBinOp` returning `none` on `.bytes` or `.adt`
operands (e.g. comparing two byte arrays or structs in a `const` block). By
contrast, an explicit post-monomorphization error (`const { assert!(...) }`)
lowers to `Terminator.panic` and terminates with `.terminated .unwind`.

We prove two theorems resolving this seam:

1. **Residual Fail-Open Hole Under `ConstNoStuck` Alone:**
   Because `PrefixOutcome.failed ≠ PrefixOutcome.stuck`, a constant
   `partiallyFailedConst` that returns `.unit` when `tySizes 0 = 8` (`bb2`) and
   executes an unmodeled binary operation on `.bytes` values when `tySizes 0 ≠ 8`
   (`bb3`, stepping to `.failed`) satisfies `ConstNoStuck` for **all** `tySizes`,
   while `ConstSucceeds` is false whenever `tySizes 0 ≠ 8`. Consequently,
   `transmuteWithFailedConst` passes **both**
   `PolarMirSem transmuteWithFailedConst ≤ MirLang.WellFormed` and
   `MonoInhabited transmuteWithFailedConst`, even though its runtime body has
   size-mismatch UB at `tySizes 0 = 4` and its constant failed due to an
   unmodeled CTFE operation rather than an explicit PME panic!
2. **Complete Closure Under `ConstIsSafe` (`SafePolarMirSem`):**
   Strengthening `ConstNoStuck` (`out ≠ .stuck`) to `ConstIsSafe` (`out.isSafe`,
   which rejects both `.stuck` and `.failed` while permitting `.running`,
   `.terminated (.normal v)`, and `.terminated .unwind`) closes this residual
   hole:
   - `SafePolarMirSem` rejects `transmuteWithFailedConst` because
     `partiallyFailedConst` reaches `.failed` (`out.isSafe = False`) at
     `tySizes 0 = 4`.
   - `sizeEq8ConstBody` (which terminates with `.terminated .unwind` when
     `tySizes 0 ≠ 8`) satisfies `ConstIsSafe` for **all** `tySizes`, so
     `transmuteToUsizeCheckedBody` remains verified under both
     `SafePolarMirSem ≤ MirLang.WellFormed` and `MonoInhabitedSafe`.
-/

theorem reachesPrefix_of_failed
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalMirStepOpt body s = some .failed)
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out = .running ∨ out = .failed := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : some _ = evalMirStepOpt body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ h1 =>
    exact Or.inr rfl
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_not_normal_of_failed
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {v : MirVal}
    (hstep : evalMirStepOpt body s = some .failed)
    (hreach : ReachesPrefix MirStep body n s tr (.terminated (.normal v))) :
    False := by
  cases reachesPrefix_of_failed hstep hreach with
  | inl hrun => cases hrun
  | inr hfail => cases hfail

theorem reachesPrefix_not_stuck_of_failed
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalMirStepOpt body s = some .failed)
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out ≠ .stuck := by
  cases reachesPrefix_of_failed hstep hreach with
  | inl hrun => rw [hrun]; intro h; cases h
  | inr hfail => rw [hfail]; intro h; cases h

theorem reachesPrefix_isSafe_of_step
    {body : MirBody} {s s' : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal}
    (hstep : evalMirStepOpt body s = some (.step () s'))
    (hreach : ReachesPrefix MirStep body n s tr out)
    (hnext : ∀ n' tr', ReachesPrefix MirStep body n' s' tr' out → out.isSafe) :
    out.isSafe := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => rw [hrun]; exact True.intro
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_isSafe_of_terminated
    {body : MirBody} {s : MirState} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome MirVal} {term : TerminationKind MirVal}
    (hstep : evalMirStepOpt body s = some (.terminated term))
    (hreach : ReachesPrefix MirStep body n s tr out) :
    out.isSafe := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => rw [hrun]; exact True.intro
  | inr hterm => rw [hterm]; exact True.intro

/-- A constant MIR body that returns `.unit` when `tySizes 0 = 8` (`bb2`), and
    when `tySizes 0 ≠ 8` (`bb3`) executes an unmodeled binary operation
    `evalBinOp .eq (.bytes 8 0) (.bytes 8 0) = none`, which `evalMirStmtOpt`
    maps to `some .failed` (`StepResult.failed`) rather than `none` (`.stuck`). -/
def partiallyFailedConst : MirBody where
  argTys := []
  retTy := .unit
  localCount := 3
  blocks := [
    { stmts := []
      terminator := .callSizeOf ⟨1⟩ (.param 0) ⟨1⟩ },
    { stmts := [.assign ⟨2⟩ (.binaryOp .eq (.move ⟨1⟩) (.constVal (.usize 8)))]
      terminator := .switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩ },
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ },
    { stmts := [.assign ⟨2⟩ (.binaryOp .eq (.constVal (.bytes 8 0)) (.constVal (.bytes 8 0)))]
      terminator := .return_ }
  ]

/-- Runtime body performing `transmute_copy::<Param 0, usize>(&_1)`, guarded by
    `partiallyFailedConst`. -/
def transmuteWithFailedConst : MirBody where
  argTys := [.param 0]
  retTy := .param 0
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.ref ⟨1⟩)]
      terminator := .callTransmuteCopy ⟨0⟩ (.param 0) .usize (.move ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]
  requiredConsts := [partiallyFailedConst]

/-- Because `bb3` steps to `.failed` rather than `.stuck`, `partiallyFailedConst`
    satisfies `ConstNoStuck` for EVERY `tySizes`! -/
theorem partiallyFailedConst_constNoStuck (tySizes : Nat → Nat) :
    ConstNoStuck tySizes partiallyFailedConst := by
  intro s₀ n tr out hts hentry hreach
  cases s₀ with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    subst hts hb hs hc hst
    refine reachesPrefix_not_stuck_of_step rfl hreach (fun _ _ hr1 => ?_)
    refine reachesPrefix_not_stuck_of_step rfl hr1 (fun _ _ hr2 => ?_)
    let l1 := updateLocal locals0 1 (some (.usize (tySizes0 0)))
    let l2 := updateLocal (updateLocal l1 1 none) 2 (some (.bool (decide (tySizes0 0 = 8))))
    let s_sw : MirState := {
      locals := l2
      block := 1
      stmtIdx := 1
      tySizes := tySizes0
    }
    cases hdec : decide (tySizes0 0 = 8) with
    | false =>
      let s_bb3 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool false))) 2 none
        block := 3
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt partiallyFailedConst s_sw = some (.step () s_bb3) := by
        change some (evalMirTerminator partiallyFailedConst s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb3)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_not_stuck_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      exact reachesPrefix_not_stuck_of_failed rfl hr3
    | true =>
      let s_bb2 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool true))) 2 none
        block := 2
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt partiallyFailedConst s_sw = some (.step () s_bb2) := by
        change some (evalMirTerminator partiallyFailedConst s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb2)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_not_stuck_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      refine reachesPrefix_not_stuck_of_step rfl hr3 (fun _ _ hr4 => ?_)
      exact reachesPrefix_not_stuck_of_terminated rfl hr4

theorem constSucceeds_partiallyFailedConst_imp_eq8 (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes partiallyFailedConst) :
    tySizes 0 = 8 := by
  cases h with
  | intro s0 h1 =>
  cases s0 with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
  cases h1 with
  | intro n h2 =>
  cases h2 with
  | intro tr h3 =>
  cases h3 with
  | intro v h4 =>
    have hts : tySizes0 = tySizes := h4.1
    have hinit := h4.2.1
    have hreach := h4.2.2
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    subst hts hb hs hc hst
    cases hdec : decide (tySizes0 0 = 8) with
    | true => exact of_decide_eq_true hdec
    | false =>
      refine False.elim ?_
      refine reachesPrefix_not_normal_of_step rfl hreach (fun _ _ hr1 => ?_)
      refine reachesPrefix_not_normal_of_step rfl hr1 (fun _ _ hr2 => ?_)
      let l1 := updateLocal locals0 1 (some (.usize (tySizes0 0)))
      let l2 := updateLocal (updateLocal l1 1 none) 2 (some (.bool (decide (tySizes0 0 = 8))))
      let s_sw : MirState := {
        locals := l2
        block := 1
        stmtIdx := 1
        tySizes := tySizes0
      }
      let s_bb3 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool false))) 2 none
        block := 3
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt partiallyFailedConst s_sw = some (.step () s_bb3) := by
        change some (evalMirTerminator partiallyFailedConst s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb3)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_not_normal_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      exact reachesPrefix_not_normal_of_failed rfl hr3

theorem partiallyFailedConst_succeeds_at_8 :
    ConstSucceeds (fun _ => 8) partiallyFailedConst := by
  let s0 : MirState := {
    locals := fun _ => none
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s1 : MirState := {
    locals := updateLocal (fun _ => none) 1 (some (.usize 8))
    block := 1
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s2 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 8))) 1 none) 2 (some (.bool true))
    block := 1
    stmtIdx := 1
    tySizes := fun _ => 8
  }
  let s3 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 8))) 1 none) 2 (some (.bool true))) 2 none
    block := 2
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s4 : MirState := {
    locals := updateLocal s3.locals 0 (some MirVal.unit)
    block := 2
    stmtIdx := 1
    tySizes := fun _ => 8
  }
  have hentry : initEntryState partiallyFailedConst s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hr4 : ReachesPrefix MirStep partiallyFailedConst 1 s4 [] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.terminated 0 s4 (.normal MirVal.unit) rfl
  have hr3 : ReachesPrefix MirStep partiallyFailedConst 2 s3 [()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 1 s3 s4 () [] (.terminated (.normal MirVal.unit)) rfl hr4
  have hr2 : ReachesPrefix MirStep partiallyFailedConst 3 s2 [(), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 2 s2 s3 () [()] (.terminated (.normal MirVal.unit)) rfl hr3
  have hr1 : ReachesPrefix MirStep partiallyFailedConst 4 s1 [(), (), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 3 s1 s2 () [(), ()] (.terminated (.normal MirVal.unit)) rfl hr2
  have hr0 : ReachesPrefix MirStep partiallyFailedConst 5 s0 [(), (), (), ()] (.terminated (.normal MirVal.unit)) :=
    ReachesPrefix.step 4 s0 s1 () [(), (), ()] (.terminated (.normal MirVal.unit)) rfl hr1
  exact ⟨s0, 5, [(), (), (), ()], .unit, rfl, hentry, hr0⟩

theorem transmuteWithFailedConst_constsNoStuck (tySizes : Nat → Nat) :
    BodyConstsNoStuck tySizes transmuteWithFailedConst := by
  intro tySizes' c hreq
  cases hreq with
  | direct hmem =>
    cases hmem with
    | head => exact partiallyFailedConst_constNoStuck _
    | tail _ hnil => cases hnil
  | nested hmem hsub =>
    cases hmem with
    | head =>
      cases hsub with
      | direct hm => cases hm
      | nested hm _ => cases hm
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ h1 =>
          cases h1 with
          | head => cases hterm
          | tail _ h2 =>
            cases h2 with
            | head => cases hterm
            | tail _ h3 =>
              cases h3 with
              | head => cases hterm
              | tail _ hnil => cases hnil
    | tail _ hnil => cases hnil
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ h1 =>
      cases h1 with
      | head => cases hterm
      | tail _ hnil => cases hnil

/-- **Theorem (Section 6.a — Residual `.failed` Hole Under `ConstNoStuck`):**
    Because `ConstNoStuck` only forbids `.stuck` (`out ≠ .stuck`), the unmodeled
    `evalBinOp` on `.bytes` in `partiallyFailedConst` (which returns `.failed`)
    allows `transmuteWithFailedConst` to pass BOTH `PolarMirSem ≤ MirLang.WellFormed`
    and `MonoInhabited`, masking the runtime size-mismatch UB at `tySizes 0 = 4`! -/
theorem transmuteWithFailedConst_passes_polarMirSem_and_monoInhabited :
    PolarMirSem transmuteWithFailedConst ≤ MirLang.WellFormed ∧
    MonoInhabited transmuteWithFailedConst := by
  constructor
  · intro q _
    refine ⟨?_, fun _ _ => True.intro⟩
    intro hentry
    refine ⟨transmuteWithFailedConst_constsNoStuck q.init.tySizes, ?_⟩
    intro hmono tr out hreach
    cases q with
    | mk init steps =>
    cases init with
    | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
      have hb : block0 = 0 := hentry.1
      have hs : stmtIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      have hst : stack0 = [] := hentry.2.2.2.1
      subst hb hs hc hst
      have hsucc : ConstSucceeds tySizes0 partiallyFailedConst :=
        hmono tySizes0 partiallyFailedConst (.direct (.head _))
          (partiallyFailedConst_constNoStuck tySizes0)
      have heq8 : tySizes0 0 = 8 :=
        constSucceeds_partiallyFailedConst_imp_eq8 tySizes0 hsucc
      cases hentry.2.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : locals0 1 = some v := hv.1
        have hvty : v.hasTy tySizes0 (.param 0) := hv.2
        cases v with
        | usize _ => cases hvty
        | bool _ => cases hvty
        | unit => cases hvty
        | adt _ _ => cases hvty
        | ref _ => cases hvty
        | bytes vSz bits =>
          have hvSz : vSz = tySizes0 0 := hvty
          subst hvSz
          let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
          let l1 := updateLocal locals0 2 (some (.ref ⟨1⟩))
          let s1 : MirState := { s0 with locals := l1, stmtIdx := 1 }
          have hstep0 : evalMirStepOpt transmuteWithFailedConst s0 = some (.step () s1) := by
            change evalMirStmtOpt s0 (.assign ⟨2⟩ (.ref ⟨1⟩)) = some (.step () s1)
            dsimp only [evalMirStmtOpt, s0]
            rw [hv1]
          cases reachesPrefix_of_step hstep0 hreach with
          | inl hrun => rw [hrun]; exact True.intro
          | inr hex1 =>
            cases hex1 with
            | intro n1 htr1 =>
              cases htr1 with
              | intro tr1 hr1 =>
                let l1_deinit := updateLocal l1 2 none
                have hl1_1 : l1_deinit 1 = some (.bytes (tySizes0 0) bits) := by
                  change (if 1 == 2 then none else if 1 == 2 then some (MirVal.ref ⟨1⟩) else locals0 1) = _
                  exact hv1
                have hdec8 : decide (tySizes0 0 = 8) = true := decide_eq_true heq8
                have hdec_refl : decide (tySizes0 0 = tySizes0 0) = true := decide_eq_true rfl
                let s2 : MirState := {
                  s1 with
                  locals := updateLocal l1_deinit 0 (some (.bytes 8 bits))
                  block := 1
                  stmtIdx := 0
                }
                have hstep1 : evalMirStepOpt transmuteWithFailedConst s1 = some (.step () s2) := by
                  change some (evalMirTerminator transmuteWithFailedConst s1
                    (.callTransmuteCopy ⟨0⟩ (.param 0) .usize (.move ⟨2⟩) ⟨1⟩)) = some (.step () s2)
                  dsimp only [evalMirTerminator, evalOperand, evalTransmuteCopy, evalTyByteSize, s1, l1]
                  change some (match (if decide (tySizes0 0 = 8) then
                      match l1_deinit 1 with
                      | some (.bytes vSz b) =>
                        if decide (vSz = tySizes0 0) then some (MirVal.bytes 8 b) else none
                      | _ => none
                    else none) with
                    | some outVal => StepResult.step () { s1 with locals := updateLocal l1_deinit 0 (some outVal), block := 1, stmtIdx := 0 }
                    | none => StepResult.failed) = some (.step () s2)
                  rw [hdec8, hl1_1]
                  dsimp only
                  rw [hdec_refl]
                  rfl
                cases reachesPrefix_of_step hstep1 hr1 with
                | inl hrun => rw [hrun]; exact True.intro
                | inr hex2 =>
                  cases hex2 with
                  | intro n2 htr2 =>
                    cases htr2 with
                    | intro tr2 hr2 =>
                      cases reachesPrefix_of_terminated (term := .normal (.bytes 8 bits)) rfl hr2 with
                      | inl hrun => rw [hrun]; exact True.intro
                      | inr hterm => rw [hterm]; exact True.intro
  · let locals0 : Nat → Option MirVal :=
      updateLocal (fun _ => none) 1 (some (.bytes 8 0))
    let s₀ : MirState := {
      locals := locals0
      block := 0
      stmtIdx := 0
      tySizes := fun _ => 8
    }
    have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
      intro j hj
      cases j with
      | zero => cases hj
      | succ k =>
        cases k with
        | zero => cases hj with | step hle => cases hle
        | succ _ => rfl
    have hentry : initEntryState transmuteWithFailedConst s₀ :=
      ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 8 0, rfl, rfl⟩, hrest⟩⟩
    have hmono : MonoAdmittedPolar (fun _ => 8) transmuteWithFailedConst := by
      intro tySizes' c hreq _
      cases hreq with
      | direct hmem =>
        cases hmem with
        | head => exact partiallyFailedConst_succeeds_at_8
        | tail _ hnil => cases hnil
      | nested hmem hsub =>
        cases hmem with
        | head =>
          cases hsub with
          | direct hm => cases hm
          | nested hm _ => cases hm
          | call1 hbb hterm _ =>
            cases hbb with
            | head => cases hterm
            | tail _ h1 =>
              cases h1 with
              | head => cases hterm
              | tail _ h2 =>
                cases h2 with
                | head => cases hterm
                | tail _ h3 =>
                  cases h3 with
                  | head => cases hterm
                  | tail _ hnil => cases hnil
        | tail _ hnil => cases hnil
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ h1 =>
          cases h1 with
          | head => cases hterm
          | tail _ hnil => cases hnil
    exact ⟨s₀, hentry, transmuteWithFailedConst_constsNoStuck (fun _ => 8), hmono⟩

/-- **Strengthened Polar CTFE Safety (`ConstIsSafe`):**
    Every reachable prefix of constant `c` under `tySizes` must satisfy
    `out.isSafe` (forbidding BOTH `.stuck` and `.failed`, while permitting
    `.running`, `.terminated (.normal v)`, and explicit PME panic
    `.terminated .unwind`). -/
def ConstIsSafe (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  ∀ (s₀ : MirState) (n : Nat) (tr : List Unit) (out : PrefixOutcome MirVal),
    s₀.tySizes = tySizes →
    initEntryState c s₀ →
    ReachesPrefix MirStep c n s₀ tr out →
    out.isSafe

def BodyConstsSafe (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c, RequiresConst tySizes body tySizes' c → ConstIsSafe tySizes' c

def MonoAdmittedSafe (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ tySizes' c,
    RequiresConst tySizes body tySizes' c →
    (ConstIsSafe tySizes' c → ConstSucceeds tySizes' c)

def SafePolarMirSem (body : MirBody) : MirLang.Behavior :=
  fun q => {
    defined :=
      initEntryState body q.init →
        BodyConstsSafe q.init.tySizes body ∧
        (MonoAdmittedSafe q.init.tySizes body →
          ∀ tr out,
            ReachesPrefix MirStep body q.steps q.init tr out →
            out.isSafe)
    val := fun _ out =>
      initEntryState body q.init ∧
      MonoAdmittedSafe q.init.tySizes body ∧
      ReachesPrefix MirStep body q.steps q.init out.trace out.outcome
  }

def MonoInhabitedSafe (body : MirBody) : Prop :=
  ∃ s : MirState,
    initEntryState body s ∧
    BodyConstsSafe s.tySizes body ∧
    MonoAdmittedSafe s.tySizes body

/-- At `tySizes 0 = 4`, `partiallyFailedConst` reaches `.failed` in 4 steps and
    violates `ConstIsSafe`. -/
theorem partiallyFailedConst_not_constIsSafe_at_4 :
    ¬ ConstIsSafe (fun _ => 4) partiallyFailedConst := by
  intro hsafe
  let s0 : MirState := {
    locals := fun _ => none
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  let s1 : MirState := {
    locals := updateLocal (fun _ => none) 1 (some (.usize 4))
    block := 1
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  let s2 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 4))) 1 none) 2 (some (.bool false))
    block := 1
    stmtIdx := 1
    tySizes := fun _ => 4
  }
  let s3 : MirState := {
    locals := updateLocal (updateLocal (updateLocal (updateLocal (fun _ => none) 1 (some (.usize 4))) 1 none) 2 (some (.bool false))) 2 none
    block := 3
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  have hentry : initEntryState partiallyFailedConst s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hr3 : ReachesPrefix MirStep partiallyFailedConst 1 s3 [] .failed :=
    ReachesPrefix.failed 0 s3 rfl
  have hr2 : ReachesPrefix MirStep partiallyFailedConst 2 s2 [()] .failed :=
    ReachesPrefix.step 1 s2 s3 () [] .failed rfl hr3
  have hr1 : ReachesPrefix MirStep partiallyFailedConst 3 s1 [(), ()] .failed :=
    ReachesPrefix.step 2 s1 s2 () [()] .failed rfl hr2
  have hr0 : ReachesPrefix MirStep partiallyFailedConst 4 s0 [(), (), ()] .failed :=
    ReachesPrefix.step 3 s0 s1 () [(), ()] .failed rfl hr1
  exact hsafe s0 4 [(), (), ()] .failed rfl hentry hr0

/-- **Theorem (Section 6.b — `SafePolarMirSem` Rejects `transmuteWithFailedConst`):**
    Strengthening `ConstNoStuck` to `ConstIsSafe` rejects `transmuteWithFailedConst`
    because `partiallyFailedConst` reaches `.failed` at `tySizes 0 = 4`. -/
theorem transmuteWithFailedConst_rejected_by_safePolarMirSem :
    ¬ (SafePolarMirSem transmuteWithFailedConst ≤ MirLang.WellFormed) := by
  intro hWF
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.bytes 4 0))
  let s₀ : MirState := {
    locals := locals0
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 4
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initEntryState transmuteWithFailedConst s₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 4 0, rfl, rfl⟩, hrest⟩⟩
  have hdef := (hWF { init := s₀, steps := 1 } True.intro).1 hentry
  exact partiallyFailedConst_not_constIsSafe_at_4
    (hdef.1 (fun _ => 4) partiallyFailedConst (.direct (.head _)))

/-- Meanwhile, `sizeEq8ConstBody` satisfies `ConstIsSafe` for ALL `tySizes`
    (because its failure branch uses `Terminator.panic`, which steps to
    `.terminated .unwind`, and `(.terminated .unwind).isSafe = True`). -/
theorem sizeEq8ConstBody_constIsSafe (tySizes : Nat → Nat) :
    ConstIsSafe tySizes sizeEq8ConstBody := by
  intro s₀ n tr out hts hentry hreach
  cases s₀ with
  | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    subst hts hb hs hc hst
    refine reachesPrefix_isSafe_of_step rfl hreach (fun _ _ hr1 => ?_)
    refine reachesPrefix_isSafe_of_step rfl hr1 (fun _ _ hr2 => ?_)
    let l1 := updateLocal locals0 1 (some (.usize (tySizes0 0)))
    let l2 := updateLocal (updateLocal l1 1 none) 2 (some (.bool (decide (tySizes0 0 = 8))))
    let s_sw : MirState := {
      locals := l2
      block := 1
      stmtIdx := 1
      tySizes := tySizes0
    }
    cases hdec : decide (tySizes0 0 = 8) with
    | false =>
      let s_bb3 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool false))) 2 none
        block := 3
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt sizeEq8ConstBody s_sw = some (.step () s_bb3) := by
        change some (evalMirTerminator sizeEq8ConstBody s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb3)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_isSafe_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      exact reachesPrefix_isSafe_of_terminated rfl hr3
    | true =>
      let s_bb2 : MirState := {
        locals := updateLocal (updateLocal (updateLocal l1 1 none) 2 (some (.bool true))) 2 none
        block := 2
        stmtIdx := 0
        tySizes := tySizes0
      }
      have hstep2 : evalMirStepOpt sizeEq8ConstBody s_sw = some (.step () s_bb2) := by
        change some (evalMirTerminator sizeEq8ConstBody s_sw (.switchInt (.move ⟨2⟩) ⟨3⟩ ⟨2⟩)) =
          some (.step () s_bb2)
        dsimp only [evalMirTerminator, evalOperand, s_sw, l2]
        rw [hdec]
        rfl
      refine reachesPrefix_isSafe_of_step hstep2 hr2 (fun _ _ hr3 => ?_)
      refine reachesPrefix_isSafe_of_step rfl hr3 (fun _ _ hr4 => ?_)
      exact reachesPrefix_isSafe_of_terminated rfl hr4

theorem transmuteToUsizeCheckedBody_constsSafe (tySizes : Nat → Nat) :
    BodyConstsSafe tySizes transmuteToUsizeCheckedBody := by
  intro tySizes' c hreq
  cases hreq with
  | direct hmem =>
    cases hmem with
    | head => exact sizeEq8ConstBody_constIsSafe _
    | tail _ hnil => cases hnil
  | nested hmem hsub =>
    cases hmem with
    | head =>
      cases hsub with
      | direct hm => cases hm
      | nested hm _ => cases hm
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ h1 =>
          cases h1 with
          | head => cases hterm
          | tail _ h2 =>
            cases h2 with
            | head => cases hterm
            | tail _ h3 =>
              cases h3 with
              | head => cases hterm
              | tail _ hnil => cases hnil
    | tail _ hnil => cases hnil
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ h1 =>
      cases h1 with
      | head => cases hterm
      | tail _ hnil => cases hnil

/-- **Theorem (Section 6.c — Legitimate PME Preserved Under `SafePolarMirSem`):**
    `transmuteToUsizeCheckedBody` satisfies both
    `SafePolarMirSem transmuteToUsizeCheckedBody ≤ MirLang.WellFormed` and
    `MonoInhabitedSafe transmuteToUsizeCheckedBody`! -/
theorem transmuteToUsizeCheckedBody_verified_safePolar :
    SafePolarMirSem transmuteToUsizeCheckedBody ≤ MirLang.WellFormed ∧
    MonoInhabitedSafe transmuteToUsizeCheckedBody := by
  constructor
  · intro q _
    refine ⟨?_, fun _ _ => True.intro⟩
    intro hentry
    refine ⟨transmuteToUsizeCheckedBody_constsSafe q.init.tySizes, ?_⟩
    intro hmono tr out hreach
    cases q with
    | mk init steps =>
    cases init with
    | mk locals0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
      have hb : block0 = 0 := hentry.1
      have hs : stmtIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      have hst : stack0 = [] := hentry.2.2.2.1
      subst hb hs hc hst
      have hsucc : ConstSucceeds tySizes0 sizeEq8ConstBody :=
        hmono tySizes0 sizeEq8ConstBody (.direct (.head _))
          (sizeEq8ConstBody_constIsSafe tySizes0)
      have heq8 : tySizes0 0 = 8 :=
        constSucceeds_sizeEq8ConstBody_imp_eq8 tySizes0 hsucc
      cases hentry.2.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : locals0 1 = some v := hv.1
        have hvty : v.hasTy tySizes0 (.param 0) := hv.2
        cases v with
        | usize _ => cases hvty
        | bool _ => cases hvty
        | unit => cases hvty
        | adt _ _ => cases hvty
        | ref _ => cases hvty
        | bytes vSz bits =>
          have hvSz : vSz = tySizes0 0 := hvty
          subst hvSz
          let s0 : MirState := { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
          let l1 := updateLocal locals0 2 (some (.ref ⟨1⟩))
          let s1 : MirState := { s0 with locals := l1, stmtIdx := 1 }
          have hstep0 : evalMirStepOpt transmuteToUsizeCheckedBody s0 = some (.step () s1) := by
            change evalMirStmtOpt s0 (.assign ⟨2⟩ (.ref ⟨1⟩)) = some (.step () s1)
            dsimp only [evalMirStmtOpt, s0]
            rw [hv1]
          cases reachesPrefix_of_step hstep0 hreach with
          | inl hrun => rw [hrun]; exact True.intro
          | inr hex1 =>
            cases hex1 with
            | intro n1 htr1 =>
              cases htr1 with
              | intro tr1 hr1 =>
                let l1_deinit := updateLocal l1 2 none
                have hl1_1 : l1_deinit 1 = some (.bytes (tySizes0 0) bits) := by
                  change (if 1 == 2 then none else if 1 == 2 then some (MirVal.ref ⟨1⟩) else locals0 1) = _
                  exact hv1
                have hdec8 : decide (tySizes0 0 = 8) = true := decide_eq_true heq8
                have hdec_refl : decide (tySizes0 0 = tySizes0 0) = true := decide_eq_true rfl
                let s2 : MirState := {
                  s1 with
                  locals := updateLocal l1_deinit 0 (some (.bytes 8 bits))
                  block := 1
                  stmtIdx := 0
                }
                have hstep1 : evalMirStepOpt transmuteToUsizeCheckedBody s1 = some (.step () s2) := by
                  change some (evalMirTerminator transmuteToUsizeCheckedBody s1
                    (.callTransmuteCopy ⟨0⟩ (.param 0) .usize (.move ⟨2⟩) ⟨1⟩)) = some (.step () s2)
                  dsimp only [evalMirTerminator, evalOperand, evalTransmuteCopy, evalTyByteSize, s1, l1]
                  change some (match (if decide (tySizes0 0 = 8) then
                      match l1_deinit 1 with
                      | some (.bytes vSz b) =>
                        if decide (vSz = tySizes0 0) then some (MirVal.bytes 8 b) else none
                      | _ => none
                    else none) with
                    | some outVal => StepResult.step () { s1 with locals := updateLocal l1_deinit 0 (some outVal), block := 1, stmtIdx := 0 }
                    | none => StepResult.failed) = some (.step () s2)
                  rw [hdec8, hl1_1]
                  dsimp only
                  rw [hdec_refl]
                  rfl
                cases reachesPrefix_of_step hstep1 hr1 with
                | inl hrun => rw [hrun]; exact True.intro
                | inr hex2 =>
                  cases hex2 with
                  | intro n2 htr2 =>
                    cases htr2 with
                    | intro tr2 hr2 =>
                      cases reachesPrefix_of_terminated (term := .normal (.bytes 8 bits)) rfl hr2 with
                      | inl hrun => rw [hrun]; exact True.intro
                      | inr hterm => rw [hterm]; exact True.intro
  · let locals0 : Nat → Option MirVal :=
      updateLocal (fun _ => none) 1 (some (.bytes 8 0))
    let s₀ : MirState := {
      locals := locals0
      block := 0
      stmtIdx := 0
      tySizes := fun _ => 8
    }
    have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
      intro j hj
      cases j with
      | zero => cases hj
      | succ k =>
        cases k with
        | zero => cases hj with | step hle => cases hle
        | succ _ => rfl
    have hentry : initEntryState transmuteToUsizeCheckedBody s₀ :=
      ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 8 0, rfl, rfl⟩, hrest⟩⟩
    have hmono : MonoAdmittedSafe (fun _ => 8) transmuteToUsizeCheckedBody := by
      intro tySizes' c hreq _
      cases hreq with
      | direct hmem =>
        cases hmem with
        | head => exact sizeEq8ConstBody_succeeds_at_8
        | tail _ hnil => cases hnil
      | nested hmem hsub =>
        cases hmem with
        | head =>
          cases hsub with
          | direct hm => cases hm
          | nested hm _ => cases hm
          | call1 hbb hterm _ =>
            cases hbb with
            | head => cases hterm
            | tail _ h1 =>
              cases h1 with
              | head => cases hterm
              | tail _ h2 =>
                cases h2 with
                | head => cases hterm
                | tail _ h3 =>
                  cases h3 with
                  | head => cases hterm
                  | tail _ hnil => cases hnil
        | tail _ hnil => cases hnil
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ h1 =>
          cases h1 with
          | head => cases hterm
          | tail _ hnil => cases hnil
    exact ⟨s₀, hentry, transmuteToUsizeCheckedBody_constsSafe (fun _ => 8), hmono⟩

/-!
## 7. Transitive `RequiresConst` and `substTySizes` Closure Gap in `mir-to-x86`

We now compare the three `RequiresConst` / `MonoAdmitted` designs across the
worktrees on a generic caller `callerWithSubstCall` (`fn caller<U>(x: U) -> bool`
with `requiredConsts = []`) that invokes `transmuteToUsizeCheckedBody::<bool>(true)`
with `typeArgs = [.bool]`:

1. **Direct-Only Membership (`MonoAdmittedDirect`):**
   Checks only `c ∈ body.requiredConsts`, missing callee constants entirely.
2. **Un-substituted 2-Place `RequiresConst` (`RequiresConstUnsubst` / `MonoAdmittedUnsubst`):**
   Matches `mir-to-x86:trusted/lean/Trusted/X86Semantics.lean` (lines 513–559)
   and `mir-to-x86:theory/Anneal/MirSemantics.lean` (lines 328–355), where
   `RequiresConst : Body → Body → Prop` traverses into `.call1` callees without
   substituting `substTySizes tySizes typeArgs`, and `MonoAdmitted` checks
   `ConstSucceeds tySizes c` at the **caller's** `tySizes`.
3. **Substituted 4-Place `RequiresConst` (`RequiresConst` / `MonoAdmitted` / `MonoAdmittedSafe`):**
   Matches `trusted-core:trusted/lean/Trusted/MirSemantics.lean` (lines 550–598),
   which substitutes `substTySizes tySizes typeArgs` at every `.call1` site.

We prove that at `tySizes = fun _ => 8` (where the caller's `U` has size 8,
while the callee's `Src = bool` has size `substTySizes (fun _ => 8) [.bool] 0 = 1`):
- Both `MonoAdmittedDirect (fun _ => 8) callerWithSubstCall` and
  `MonoAdmittedUnsubst (fun _ => 8) callerWithSubstCall` evaluate to `True`
  (falsely admitting the caller even though the callee executes
  `transmute_copy::<bool, usize>` and hits `PrefixOutcome.failed` at step 3!).
- Both `MonoAdmitted (fun _ => 8) callerWithSubstCall` and
  `MonoAdmittedSafe (fun _ => 8) callerWithSubstCall` evaluate to `False`
  (properly rejecting the invalid cross-monomorphization call).
-/

/-- Direct-only constant admission (checks only `c ∈ body.requiredConsts`). -/
def MonoAdmittedDirect (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ c, c ∈ body.requiredConsts → ConstSucceeds tySizes c

/-- Un-substituted 2-place transitive constant requirement relation matching
    `mir-to-x86:trusted/lean/Trusted/X86Semantics.lean` (lines 513–539) and
    `mir-to-x86:theory/Anneal/MirSemantics.lean` (lines 328–347). -/
inductive RequiresConstUnsubst : MirBody → MirBody → Prop where
  | direct {body c : MirBody} :
      c ∈ body.requiredConsts →
      RequiresConstUnsubst body c
  | nested {body c₁ c₂ : MirBody} :
      c₁ ∈ body.requiredConsts →
      RequiresConstUnsubst c₁ c₂ →
      RequiresConstUnsubst body c₂
  | call1 {body callee c : MirBody} {bb : BasicBlock}
      {dst : LocalId} {arg : Operand} {target : BlockId} {typeArgs : List MirTy} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst callee arg target typeArgs →
      RequiresConstUnsubst callee c →
      RequiresConstUnsubst body c

/-- Un-substituted monomorphization admission matching
    `mir-to-x86:trusted/lean/Trusted/X86Semantics.lean` (lines 555–559) and
    `mir-to-x86:theory/Anneal/MirSemantics.lean` (lines 352–355). -/
def MonoAdmittedUnsubst (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ c, RequiresConstUnsubst body c → ConstSucceeds tySizes c

/-- A generic caller `fn caller<U>(x: U) -> bool` (`requiredConsts = []`) that
    invokes `transmuteToUsizeCheckedBody::<bool>(true)` (`typeArgs = [.bool]`). -/
def callerWithSubstCall : MirBody where
  argTys := [.param 0]
  retTy := .bool
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.use (.constVal (.bool true)))]
      terminator := .call1 ⟨0⟩ transmuteToUsizeCheckedBody (.move ⟨2⟩) ⟨1⟩ [.bool] },
    { stmts := []
      terminator := .return_ }
  ]
  requiredConsts := []

/-- **Theorem (Section 7.a — Direct Membership Falsely Admits `callerWithSubstCall`):**
    Because `callerWithSubstCall.requiredConsts = []`, `MonoAdmittedDirect`
    trivially admits `tySizes = fun _ => 8`. -/
theorem callerWithSubstCall_admitted_by_direct :
    MonoAdmittedDirect (fun _ => 8) callerWithSubstCall := by
  intro _ hmem
  cases hmem

/-- **Theorem (Section 7.b — `mir-to-x86`'s Un-substituted `RequiresConst` ALSO
    Falsely Admits `callerWithSubstCall` at `tySizes = fun _ => 8`):**
    Even though `RequiresConstUnsubst` finds `sizeEq8ConstBody` inside the
    callee `transmuteToUsizeCheckedBody`, `MonoAdmittedUnsubst` evaluates
    `ConstSucceeds (fun _ => 8) sizeEq8ConstBody` at the **caller's**
    `tySizes = fun _ => 8` (where `sizeEq8ConstBody` succeeds!) rather than at
    the callee's substituted `substTySizes (fun _ => 8) [.bool]` (`0 ↦ 1`). -/
theorem callerWithSubstCall_admitted_by_unsubst :
    MonoAdmittedUnsubst (fun _ => 8) callerWithSubstCall := by
  intro c hreq
  cases hreq with
  | direct hmem => cases hmem
  | nested hmem _ => cases hmem
  | call1 hbb hterm hcallee =>
    cases hbb with
    | head =>
      injection hterm with _ hcal _ _ _
      subst hcal
      cases hcallee with
      | direct hm =>
        cases hm with
        | head => exact sizeEq8ConstBody_succeeds_at_8
        | tail _ hnil => cases hnil
      | nested hm hsub =>
        cases hm with
        | head =>
          cases hsub with
          | direct hm2 => cases hm2
          | nested hm2 _ => cases hm2
          | call1 hbb2 hterm2 _ =>
            cases hbb2 with
            | head => cases hterm2
            | tail _ h1 =>
              cases h1 with
              | head => cases hterm2
              | tail _ h2 =>
                cases h2 with
                | head => cases hterm2
                | tail _ h3 =>
                  cases h3 with
                  | head => cases hterm2
                  | tail _ hnil => cases hnil
        | tail _ hnil => cases hnil
      | call1 hbb2 hterm2 _ =>
        cases hbb2 with
        | head => cases hterm2
        | tail _ h1 =>
          cases h1 with
          | head => cases hterm2
          | tail _ hnil => cases hnil
    | tail _ h1 =>
      cases h1 with
      | head => cases hterm
      | tail _ hnil => cases hnil

/-- **Theorem (Section 7.c — 4-Place `RequiresConst` with `substTySizes` Rejects
    `callerWithSubstCall` at `tySizes = fun _ => 8`):**
    Under `trusted-core`'s 4-place `RequiresConst`, the `.call1` rule
    substitutes `substTySizes (fun _ => 8) [.bool]` (`0 ↦ 1`), where
    `sizeEq8ConstBody` fails `ConstSucceeds` (`1 ≠ 8`), so both `MonoAdmitted`
    and `MonoAdmittedSafe` reject `callerWithSubstCall` at `fun _ => 8`! -/
theorem callerWithSubstCall_rejected_by_subst_requiresConst :
    ¬ MonoAdmitted (fun _ => 8) callerWithSubstCall ∧
    ¬ MonoAdmittedSafe (fun _ => 8) callerWithSubstCall := by
  have hreq :
      RequiresConst (fun _ => 8) callerWithSubstCall
        (substTySizes (fun _ => 8) [MirTy.bool]) sizeEq8ConstBody :=
    RequiresConst.call1 (.head _) rfl (RequiresConst.direct (.head _))
  have hnotsucc :
      ¬ ConstSucceeds (substTySizes (fun _ => 8) [MirTy.bool]) sizeEq8ConstBody := by
    intro hsucc
    have heq8 : substTySizes (fun _ => 8) [MirTy.bool] 0 = 8 :=
      constSucceeds_sizeEq8ConstBody_imp_eq8 _ hsucc
    change (1 : Nat) = 8 at heq8
    cases heq8
  constructor
  · intro hmono
    exact hnotsucc (hmono _ _ hreq)
  · intro hmonoSafe
    exact hnotsucc
      (hmonoSafe _ _ hreq
        (sizeEq8ConstBody_constIsSafe (substTySizes (fun _ => 8) [MirTy.bool])))

/-- **Theorem (Section 7.d — Runtime Failure of `callerWithSubstCall` at `fun _ => 8`):**
    From an entry state `s₀` with `s₀.tySizes = fun _ => 8`, `callerWithSubstCall`
    steps into `transmuteToUsizeCheckedBody` with `s₂.tySizes = substTySizes (fun _ => 8) [.bool]`
    and reaches `PrefixOutcome.failed` in 4 steps when `callTransmuteCopy` checks
    `srcSz == dstSz` (`1 == 8`). -/
theorem callerWithSubstCall_fails_at_runtime :
    ∃ s₀ : MirState,
      s₀.tySizes = (fun _ => 8) ∧
      initEntryState callerWithSubstCall s₀ ∧
      ReachesPrefix MirStep callerWithSubstCall 4 s₀ [(), (), ()] .failed := by
  let locals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.bytes 8 0))
  let s0 : MirState := {
    locals := locals0
    block := 0
    stmtIdx := 0
    tySizes := fun _ => 8
  }
  let s1 : MirState := {
    locals := updateLocal locals0 2 (some (.bool true))
    block := 0
    stmtIdx := 1
    tySizes := fun _ => 8
  }
  let calleeLocals0 : Nat → Option MirVal :=
    updateLocal (fun _ => none) 1 (some (.bool true))
  let frame0 : StackFrame := {
    callerBody := callerWithSubstCall
    callerLocals := updateLocal (updateLocal locals0 2 (some (.bool true))) 2 none
    callerTySizes := fun _ => 8
    retDst := ⟨0⟩
    retBlock := 1
  }
  let s2 : MirState := {
    locals := calleeLocals0
    block := 0
    stmtIdx := 0
    tySizes := substTySizes (fun _ => 8) [MirTy.bool]
    curBody := some transmuteToUsizeCheckedBody
    stack := [frame0]
  }
  let s3 : MirState := {
    locals := updateLocal calleeLocals0 2 (some (.ref ⟨1⟩))
    block := 0
    stmtIdx := 1
    tySizes := substTySizes (fun _ => 8) [MirTy.bool]
    curBody := some transmuteToUsizeCheckedBody
    stack := [frame0]
  }
  have hrest : ∀ j, 2 ≤ j → locals0 j = none := by
    intro j hj
    cases j with
    | zero => cases hj
    | succ k =>
      cases k with
      | zero => cases hj with | step hle => cases hle
      | succ _ => rfl
  have hentry : initEntryState callerWithSubstCall s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.bytes 8 0, rfl, rfl⟩, hrest⟩⟩
  have hr3 : ReachesPrefix MirStep callerWithSubstCall 1 s3 [] .failed :=
    ReachesPrefix.failed 0 s3 rfl
  have hr2 : ReachesPrefix MirStep callerWithSubstCall 2 s2 [()] .failed :=
    ReachesPrefix.step 1 s2 s3 () [] .failed rfl hr3
  have hr1 : ReachesPrefix MirStep callerWithSubstCall 3 s1 [(), ()] .failed :=
    ReachesPrefix.step 2 s1 s2 () [()] .failed rfl hr2
  have hr0 : ReachesPrefix MirStep callerWithSubstCall 4 s0 [(), (), ()] .failed :=
    ReachesPrefix.step 3 s0 s1 () [(), ()] .failed rfl hr1
  exact ⟨s0, rfl, hentry, hr0⟩

/-!
## 8. Axiom Audit (`#print axioms`)

Every theorem in this mechanization is proved constructively without `sorryAx`,
`Lean.ofReduceBool`, or `Classical.choice`.
-/

#print axioms unmodeledConst_rejected_in_positive_position
#print axioms buggyRuntimeFn_no_initMirState
#print axioms buggyRuntimeFn_sem_eq_bot
#print axioms buggyRuntimeFn_vacuously_satisfies_false_spec
#print axioms totalStep_and_inhabitedDemonic_do_not_catch_empty_initState
#print axioms transmuteWithFakePme_initMirState_inhabited
#print axioms buggyRuntimeFn_rejected_by_polarMirSem
#print axioms idWithUnmodeledConst_rejected_by_polarMirSem
#print axioms transmuteWithFakePme_rejected_by_polarMirSem
#print axioms buggyFnWithPanicConst_rejected_by_monoInhabited
#print axioms transmuteToUsizeCheckedBody_verified_polar
#print axioms loopCodegen_satisfies_wellFormed
#print axioms loopCodegen_satisfies_ensuresEqArg
#print axioms unwindCodegen_satisfies_wellFormed
#print axioms unwindCodegen_satisfies_ensuresEqArg
#print axioms loopCodegen_compiles_under_π_naive_async
#print axioms reachesPrefix_terminated_mono
#print axioms idCopyBody_outcome_at_ge_2
#print axioms monotone_π_dilated
#print axioms π_dilated_rejects_loopCodegen
#print axioms π_dilated_rejects_unwindCodegen
#print axioms lockstep_compiles_rejects_idCopyX86_2x
#print axioms idCopyX86_2x_compiles_dilated_2
#print axioms mirLoopBody_compiles_dilated
#print axioms panicConst_compiles_dilated
#print axioms loopCodegen_rejected_by_ensuresEqArgTotal
#print axioms unwindCodegen_rejected_by_ensuresEqArgTotal
#print axioms idCopyX86_2x_satisfies_ensuresEqArgTotal_3
#print axioms partiallyFailedConst_constNoStuck
#print axioms transmuteWithFailedConst_passes_polarMirSem_and_monoInhabited
#print axioms partiallyFailedConst_not_constIsSafe_at_4
#print axioms transmuteWithFailedConst_rejected_by_safePolarMirSem
#print axioms sizeEq8ConstBody_constIsSafe
#print axioms transmuteToUsizeCheckedBody_verified_safePolar
#print axioms callerWithSubstCall_admitted_by_direct
#print axioms callerWithSubstCall_admitted_by_unsubst
#print axioms callerWithSubstCall_rejected_by_subst_requiresConst
#print axioms callerWithSubstCall_fails_at_runtime

end PolarEvaluationAndProgress
