-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Cluster B Probe: Variable-Step-Count Optimizations Under `ExecQuery` and `ReachesPrefix`

This standalone Lean 4.34.1 file reproduces the exact core definitions from
`Trusted/Refinement.lean`, `Trusted/StepResult.lean`, `Trusted/X86Ast.lean`, and
`Trusted/X86Semantics.lean` and proves:

1. **Exact Anatomy of `ReachesPrefix` on Step-Count Changes:**
   - Terminal stabilization (`reachesPrefix_add_of_terminated`): once a machine
     reaches `.terminated term` at step budget `n`, it reaches `.terminated term`
     with the identical observation trace at every step budget `n + d`.
   - Exact characterization of deterministic `Obs = Unit` executions
     (`StepsToTerminated`, `reachesPrefix_iff_of_steps_le`,
     `reachesPrefix_iff_of_steps_gt`).
   - Impossibility of lockstep and trace-preserving query morphisms when pass
     step counts differ (`not_compiles_lockstep_nop_deletion`,
     `not_compiles_any_trace_preserving_query_map`).
2. **Step-Elastic (`π_elastic`) and Bounded-Progress (`π_progress`, `π_opt`,
   `π_bounded`) Behavior Morphisms in `theory/` (Zero Changes to `trusted/`):**
   - Monotonicity, extensiveness (`b ≤ π b`), idempotence (`π (π b) ≤ π b`),
     and pipeline composition (`π_progress_comp`).
   - Termination preservation under `π_opt` and `π_progress K`: refutes
     compiling a terminating program into an infinite loop
     (`not_compiles_π_opt_infinite_loop`).
   - Specification invariance (`π (SpecOn pre post) ≡ SpecOn pre post`) for
     `WellFormed`, `WellFormedOn`, `EnsuresRetLibInv`, `EnsuresEqArg`,
     `EnsuresConst`, and `EnsuresBinOp`.
3. **Pass A — Instruction Deletion (`stripNops`):**
   - Universal proof that stripping `.nop` instructions from all basic blocks
     (and static `.call1` callees) satisfies `Compiles X86Lang X86Lang π_x86_opt`
     and `Compiles X86Lang X86Lang π_x86_elastic` for every `body : X86Body`.
4. **Pass B — 1-to-Many Instruction Expansion (`expandImmMov`):**
   - Universal proof that expanding `.mov dst (.imm v)` into the 2-instruction
     sequence `[.allocSlot dst, .mov dst (.imm v)]` across all basic blocks
     satisfies `Compiles X86Lang X86Lang (π_progress 2 id id)` and
     `Compiles X86Lang X86Lang π_x86_elastic` for every `body : X86Body`.
-/

namespace ClusterBProbe

/-!
## 0. Exact Verbatim Definitions from `trusted/lean/Trusted/`
-/

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
  ClusterBProbe.Behavior L.Query L.Out

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

structure SlotId where
  index : Nat

structure BlockLabel where
  index : Nat

inductive X86Ty where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | refParam (idx : Nat)

inductive X86Val where
  | word64 (bits : Nat)
  | boolVal (b : Bool)
  | unit
  | adt (id : Nat) (inner : X86Val)
  | bytes (sz : Nat) (bits : Nat)
  | stackPtr (slot : SlotId)

inductive X86Operand where
  | stackSlot (slot : SlotId) (consume : Bool := false)
  | imm (val : X86Val)

inductive X86BinOp where
  | add | sub | mul | bitAnd | bitOr | bitXor | shl | shr
  | eq | ne | lt | le | gt | ge

inductive X86Instr where
  | mov (dst : SlotId) (src : X86Operand)
  | alu (op : X86BinOp) (dst : SlotId) (lhs : X86Operand) (rhs : X86Operand)
  | wrapAdt (adtId : Nat) (dst : SlotId) (src : X86Operand)
  | extractField0 (dst : SlotId) (src : SlotId)
  | leaSlot (dst : SlotId) (target : SlotId)
  | reborrowSlot (dst : SlotId) (srcPtr : SlotId)
  | allocSlot (slot : SlotId)
  | deallocSlot (slot : SlotId)
  | nop

mutual
  inductive X86Term where
    | ret
    | jmp (target : BlockLabel)
    | jccBool (cond : X86Operand) (falseTarget : BlockLabel)
        (trueTarget : BlockLabel)
    | ud2
    | abortPanic
    | movSizeOfJmp (dst : SlotId) (ty : X86Ty) (target : BlockLabel)
    | repMovsbJmp (dst : SlotId) (srcTy dstTy : X86Ty) (ptrOp : X86Operand)
        (target : BlockLabel)
    | call1 (dst : SlotId) (callee : X86Body) (arg : X86Operand)
        (target : BlockLabel)

  structure X86Block where
    instrs : List X86Instr
    term : X86Term

  structure X86Body where
    argTys : List X86Ty
    retTy : X86Ty
    slotCount : Nat
    blocks : List X86Block
    requiredConsts : List X86Body := []
end

structure X86CallFrame where
  callerBody : Option X86Body
  callerMem : Nat → Option X86Val
  retSlot : SlotId
  retBlock : Nat

structure X86State where
  mem : Nat → Option X86Val
  bb : Nat
  ip : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option X86Body := none
  stack : List X86CallFrame := []

def updateSlot (mem : Nat → Option X86Val) (target : Nat)
    (val : Option X86Val) : Nat → Option X86Val :=
  fun i => if i == target then val else mem i

def evalX86TyByteSize (tySizes : Nat → Nat) (ty : X86Ty) : Nat :=
  match ty with
  | .usize => 8
  | .bool => 1
  | .unit => 0
  | .adt _ => 8
  | .param idx => tySizes idx
  | .refParam _ => 8

def X86Val.hasTy (tySizes : Nat → Nat) (v : X86Val) (ty : X86Ty) : Prop :=
  match ty, v with
  | .usize, .word64 _ => True
  | .bool, .boolVal _ => True
  | .unit, .unit => True
  | .adt tyId, .adt vId (.word64 _) => vId = tyId
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .refParam _, .stackPtr _ => True
  | _, _ => False

def argsMatchStack (tySizes : Nat → Nat) (argTys : List X86Ty)
    (mem : Nat → Option X86Val) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, mem k = some v ∧ v.hasTy tySizes ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → mem j = none)
    1

def initX86State (body : X86Body) (s : X86State) : Prop :=
  s.bb = 0 ∧
  s.ip = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.mem 0 = none ∧
  argsMatchStack s.tySizes body.argTys s.mem

def evalX86Operand (mem : Nat → Option X86Val) (op : X86Operand) :
    Option (X86Val × (Nat → Option X86Val)) :=
  match op with
  | .stackSlot slot false =>
    match mem slot.index with
    | some v => some (v, mem)
    | none => none
  | .stackSlot slot true =>
    match mem slot.index with
    | some v => some (v, updateSlot mem slot.index none)
    | none => none
  | .imm v => some (v, mem)

def evalX86BinOp (op : X86BinOp) (lhs rhs : X86Val) : Option X86Val :=
  match op, lhs, rhs with
  | .add, .word64 a, .word64 b => some (.word64 (a + b))
  | .sub, .word64 a, .word64 b => some (.word64 (a - b))
  | .mul, .word64 a, .word64 b => some (.word64 (a * b))
  | .bitAnd, .word64 a, .word64 b => some (.word64 (Nat.land a b))
  | .bitOr, .word64 a, .word64 b => some (.word64 (Nat.lor a b))
  | .bitXor, .word64 a, .word64 b => some (.word64 (Nat.xor a b))
  | .shl, .word64 a, .word64 b => some (.word64 (a <<< b))
  | .shr, .word64 a, .word64 b => some (.word64 (a >>> b))
  | .eq, .word64 a, .word64 b => some (.boolVal (decide (a = b)))
  | .ne, .word64 a, .word64 b => some (.boolVal (decide (a ≠ b)))
  | .lt, .word64 a, .word64 b => some (.boolVal (decide (a < b)))
  | .le, .word64 a, .word64 b => some (.boolVal (decide (a ≤ b)))
  | .gt, .word64 a, .word64 b => some (.boolVal (decide (b < a)))
  | .ge, .word64 a, .word64 b => some (.boolVal (decide (b ≤ a)))
  | .eq, .boolVal a, .boolVal b => some (.boolVal (decide (a = b)))
  | .ne, .boolVal a, .boolVal b => some (.boolVal (decide (a ≠ b)))
  | .bitAnd, .boolVal a, .boolVal b => some (.boolVal (a && b))
  | .bitOr, .boolVal a, .boolVal b => some (.boolVal (a || b))
  | .bitXor, .boolVal a, .boolVal b => some (.boolVal (bne a b))
  | .eq, .unit, .unit => some (.boolVal true)
  | .ne, .unit, .unit => some (.boolVal false)
  | _, _, _ => none

def evalX86Instr (s : X86State) (instr : X86Instr) :
    StepResult X86State Unit X86Val :=
  match instr with
  | .mov dst src =>
    match evalX86Operand s.mem src with
    | some (v, mem') =>
      .step () { s with
        mem := updateSlot mem' dst.index (some v)
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .alu op dst lhs rhs =>
    match evalX86Operand s.mem lhs with
    | some (v1, mem1) =>
      match evalX86Operand mem1 rhs with
      | some (v2, mem2) =>
        match evalX86BinOp op v1 v2 with
        | some outVal =>
          .step () { s with
            mem := updateSlot mem2 dst.index (some outVal)
            ip := s.ip + 1
          }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .wrapAdt adtId dst src =>
    match evalX86Operand s.mem src with
    | some (v, mem') =>
      .step () { s with
        mem := updateSlot mem' dst.index (some (.adt adtId v))
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .extractField0 dst src =>
    match s.mem src.index with
    | some (.adt _ inner) =>
      .step () { s with
        mem := updateSlot s.mem dst.index (some inner)
        ip := s.ip + 1
      }
    | _ => .failed .ub
  | .leaSlot dst target =>
    match s.mem target.index with
    | some _ =>
      .step () { s with
        mem := updateSlot s.mem dst.index (some (.stackPtr target))
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .reborrowSlot dst srcPtr =>
    match s.mem srcPtr.index with
    | some (.stackPtr target) =>
      match s.mem target.index with
      | some _ =>
        .step () { s with
          mem := updateSlot s.mem dst.index (some (.stackPtr target))
          ip := s.ip + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
  | .allocSlot slot =>
    .step () { s with
      mem := updateSlot s.mem slot.index none
      ip := s.ip + 1
    }
  | .deallocSlot slot =>
    .step () { s with
      mem := updateSlot s.mem slot.index none
      ip := s.ip + 1
    }
  | .nop =>
    .step () { s with ip := s.ip + 1 }

def evalRepMovsb (tySizes : Nat → Nat) (mem : Nat → Option X86Val)
    (srcTy dstTy : X86Ty) (ptrVal : X86Val) : Option X86Val :=
  let srcSz := evalX86TyByteSize tySizes srcTy
  let dstSz := evalX86TyByteSize tySizes dstTy
  if decide (srcSz = dstSz) then
    match ptrVal with
    | .stackPtr target =>
      match mem target.index with
      | some (.bytes vSz bits) =>
        if decide (vSz = srcSz) then
          some (.bytes dstSz bits)
        else
          none
      | _ => none
    | _ => none
  else
    none

def evalX86Term (s : X86State) (term : X86Term) :
    StepResult X86State Unit X86Val :=
  match term with
  | .ret =>
    match s.mem 0 with
    | none => .failed .ub
    | some retVal =>
      match s.stack with
      | [] => .terminated (.normal retVal)
      | frame :: restStack =>
        .step () {
          mem := updateSlot frame.callerMem frame.retSlot.index (some retVal)
          bb := frame.retBlock
          ip := 0
          tySizes := s.tySizes
          curBody := frame.callerBody
          stack := restStack
        }
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .abortPanic =>
    .terminated .unwind
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some (.boolVal false, mem') =>
      .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
    | some (.boolVal true, mem') =>
      .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
    | _ => .failed .ub
  | .movSizeOfJmp dst ty target =>
    let sz := evalX86TyByteSize s.tySizes ty
    .step () { s with
      mem := updateSlot s.mem dst.index (some (.word64 sz))
      bb := target.index
      ip := 0
    }
  | .repMovsbJmp dst srcTy dstTy ptrOp target =>
    match evalX86Operand s.mem ptrOp with
    | some (ptrVal, mem') =>
      match evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal with
      | some outVal =>
        .step () { s with
          mem := updateSlot mem' dst.index (some outVal)
          bb := target.index
          ip := 0
        }
      | none => .failed .ub
    | none => .failed .ub
  | .call1 dst callee arg target =>
    match evalX86Operand s.mem arg with
    | some (argVal, callerMem') =>
      let calleeMem : Nat → Option X86Val :=
        updateSlot (fun _ => none) 1 (some argVal)
      let frame : X86CallFrame := {
        callerBody := s.curBody
        callerMem := callerMem'
        retSlot := dst
        retBlock := target.index
      }
      .step () {
        mem := calleeMem
        bb := 0
        ip := 0
        tySizes := s.tySizes
        curBody := some callee
        stack := frame :: s.stack
      }
    | none => .failed .ub

def evalX86Step (rootBody : X86Body) (s : X86State) :
    StepResult X86State Unit X86Val :=
  let active := s.curBody.getD rootBody
  match active.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalX86Instr s instr
    | none => evalX86Term s blk.term

def X86Machine : SmallStepMachine X86Body X86State Unit X86Val where
  initState := initX86State
  step body s r := r = evalX86Step body s

def X86Lang : Language :=
  X86Machine.toLanguage

abbrev X86Sem (body : X86Body) : X86Lang.Behavior :=
  X86Lang.sem body

abbrev LibInv := (Nat → Nat) → X86Ty → X86Val → Prop

def EnsuresRetLibInv (libInv : LibInv) (retTy : X86Ty)
    (pre : ExecQuery X86State → Prop) : X86Lang.Behavior :=
  X86Lang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

def EnsuresEqArg (argSlot : Nat) : X86Lang.Behavior :=
  X86Lang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      q.init.mem argSlot = some ret)

def EnsuresConst (expected : X86Val) : X86Lang.Behavior :=
  X86Lang.Spec (fun _ out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ret = expected)

def EnsuresBinOp (op : X86BinOp) (arg1Slot arg2Slot : Nat) : X86Lang.Behavior :=
  X86Lang.Spec (fun q out =>
    ∀ ret,
      out.outcome = .terminated (.normal ret) →
      ∀ v1 v2,
        q.init.mem arg1Slot = some v1 →
        q.init.mem arg2Slot = some v2 →
        evalX86BinOp op v1 v2 = some ret)

/-!
## 1. Exact Anatomy of `ReachesPrefix` and Why Lockstep Morphisms Fail
-/

/-- Terminal stabilization of `ReachesPrefix`: once a prefix reaches
    `.terminated term` at step budget `n`, increasing the step budget by any
    `d : Nat` reaches `.terminated term` with the exact same trace `tr`.

    This property holds because `ReachesPrefix.terminated` is parameterized by
    an arbitrary remaining fuel `n + 1`. -/
theorem reachesPrefix_add_of_terminated
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} {init : State}
    {n : Nat} {s : State} {tr : List Obs} {term : TerminationKind Val}
    (h : ReachesPrefix M p init n s tr (.terminated term)) (d : Nat) :
    ReachesPrefix M p init (n + d) s tr (.terminated term) := by
  generalize hout : PrefixOutcome.terminated term = out at h
  induction h with
  | zero => cases hout
  | step k s₁ s₂ obs tr' out' hstep _ ih =>
    subst hout
    have hsum : k + 1 + d = (k + d) + 1 := Nat.succ_add k d
    rw [hsum]
    exact ReachesPrefix.step (k + d) s₁ s₂ obs tr' (.terminated term) hstep (ih rfl)
  | choice k kind s₁ s₂ branches tr' out' hstep hbr _ ih =>
    subst hout
    have hsum : k + 1 + d = (k + d) + 1 := Nat.succ_add k d
    rw [hsum]
    exact ReachesPrefix.choice (k + d) kind s₁ s₂ branches tr' (.terminated term)
      hstep hbr (ih rfl)
  | emptyChoice => cases hout
  | terminated k s₁ term' hstep =>
    injection hout with hterm
    subst hterm
    have hsum : k + 1 + d = (k + d) + 1 := Nat.succ_add k d
    rw [hsum]
    exact ReachesPrefix.terminated (k + d) s₁ term hstep
  | failed => cases hout
  | noStep => cases hout

/-- Inductive characterization of a deterministic `Obs = Unit` execution path
    that takes `k` transitions of `.step ()` from `s` to a terminal state that
    emits `.terminated term`. -/
inductive StepsToTerminated {Prog State Val : Type}
    (evalStep : Prog → State → StepResult State Unit Val) (p : Prog) :
    Nat → State → TerminationKind Val → Prop where
  | done (s : State) (term : TerminationKind Val) :
      evalStep p s = .terminated term →
      StepsToTerminated evalStep p 0 s term
  | step (k : Nat) (s s' : State) (term : TerminationKind Val) :
      evalStep p s = .step () s' →
      StepsToTerminated evalStep p k s' term →
      StepsToTerminated evalStep p (k + 1) s term

/-- Functional small-step machine induced by a total deterministic step function
    `evalStep`. -/
def detMachine {Prog State Val : Type} (initPred : Prog → State → Prop)
    (evalStep : Prog → State → StepResult State Unit Val) :
    SmallStepMachine Prog State Unit Val where
  initState := initPred
  step p s r := r = evalStep p s

/-- Exact characterization of `ReachesPrefix` when `steps ≤ k` along a
    `k`-step terminating path: the prefix is `.running` and its trace is
    `List.replicate steps ()`. -/
theorem reachesPrefix_iff_of_steps_le {Prog State Val : Type}
    {initPred : Prog → State → Prop}
    {evalStep : Prog → State → StepResult State Unit Val}
    {p : Prog} {init : State} {k : Nat} {s : State} {term : TerminationKind Val}
    (hpath : StepsToTerminated evalStep p k s term) :
    ∀ {steps : Nat} (_ : steps ≤ k) (tr : List Unit) (out : PrefixOutcome Val),
      ReachesPrefix (detMachine initPred evalStep) p init steps s tr out ↔
        tr = List.replicate steps () ∧ out = .running := by
  induction hpath with
  | done s₀ term₀ hterm =>
    intro steps hle tr out
    have hzero : steps = 0 := Nat.eq_zero_of_le_zero hle
    subst hzero
    constructor
    · intro hr
      cases hr with
      | zero => exact ⟨rfl, rfl⟩
    · intro h
      rw [h.1, h.2]
      exact ReachesPrefix.zero s₀
  | step k' s₀ s₁ term₀ hstep _ ih =>
    intro steps hle tr out
    cases steps with
    | zero =>
      constructor
      · intro hr
        cases hr with
        | zero => exact ⟨rfl, rfl⟩
      · intro h
        rw [h.1, h.2]
        exact ReachesPrefix.zero s₀
    | succ m =>
      have hm : m ≤ k' := Nat.le_of_succ_le_succ hle
      constructor
      · intro hr
        cases hr with
        | step _ _ s' obs tr' _ hst hr' =>
          dsimp [detMachine] at hst
          rw [hstep] at hst
          injection hst with hobs hs'
          subst hobs hs'
          have hsub := (ih hm tr' out).mp hr'
          refine ⟨?_, hsub.2⟩
          rw [hsub.1]
          rfl
        | choice _ _ _ _ _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | emptyChoice _ _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | terminated _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | failed _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | noStep _ _ hno =>
          exact False.elim (hno ⟨_, rfl⟩)
      · intro h
        rw [h.1, h.2]
        have hr' := (ih hm (List.replicate m ()) .running).mpr ⟨rfl, rfl⟩
        exact ReachesPrefix.step m s₀ s₁ () (List.replicate m ()) .running
          hstep.symm hr'

/-- Exact characterization of `ReachesPrefix` when `k + 1 ≤ steps` along a
    `k`-step terminating path: the prefix is `.terminated term` and its trace
    is fixed at `List.replicate k ()` regardless of how large `steps` is. -/
theorem reachesPrefix_iff_of_steps_gt {Prog State Val : Type}
    {initPred : Prog → State → Prop}
    {evalStep : Prog → State → StepResult State Unit Val}
    {p : Prog} {init : State} {k : Nat} {s : State} {term : TerminationKind Val}
    (hpath : StepsToTerminated evalStep p k s term) :
    ∀ {steps : Nat} (_ : k + 1 ≤ steps) (tr : List Unit) (out : PrefixOutcome Val),
      ReachesPrefix (detMachine initPred evalStep) p init steps s tr out ↔
        tr = List.replicate k () ∧ out = .terminated term := by
  induction hpath with
  | done s₀ term₀ hterm =>
    intro steps hge tr out
    cases steps with
    | zero => cases hge
    | succ m =>
      constructor
      · intro hr
        cases hr with
        | step _ _ _ _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hterm] at hst; cases hst
        | choice _ _ _ _ _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hterm] at hst; cases hst
        | emptyChoice _ _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hterm] at hst; cases hst
        | terminated _ _ term' hst =>
          dsimp [detMachine] at hst
          rw [hterm] at hst
          injection hst with hterm'
          subst hterm'
          exact ⟨rfl, rfl⟩
        | failed _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hterm] at hst; cases hst
        | noStep _ _ hno =>
          exact False.elim (hno ⟨_, rfl⟩)
      · intro h
        rw [h.1, h.2]
        exact ReachesPrefix.terminated m s₀ term₀ hterm.symm
  | step k' s₀ s₁ term₀ hstep _ ih =>
    intro steps hge tr out
    cases steps with
    | zero => cases hge
    | succ m =>
      have hm : k' + 1 ≤ m := Nat.le_of_succ_le_succ hge
      constructor
      · intro hr
        cases hr with
        | step _ _ s' obs tr' _ hst hr' =>
          dsimp [detMachine] at hst
          rw [hstep] at hst
          injection hst with hobs hs'
          subst hobs hs'
          have hsub := (ih hm tr' out).mp hr'
          refine ⟨?_, hsub.2⟩
          rw [hsub.1]
          rfl
        | choice _ _ _ _ _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | emptyChoice _ _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | terminated _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | failed _ _ _ hst =>
          dsimp [detMachine] at hst; rw [hstep] at hst; cases hst
        | noStep _ _ hno =>
          exact False.elim (hno ⟨_, rfl⟩)
      · intro h
        rw [h.1, h.2]
        have hr' := (ih hm (List.replicate k' ()) (.terminated term₀)).mpr ⟨rfl, rfl⟩
        exact ReachesPrefix.step m s₀ s₁ () (List.replicate k' ())
          (.terminated term₀) hstep.symm hr'

/-- Source program taking `k₁ = 2` steps (`nop; mov [rbp-8], 42; ret`). -/
def progWithNop : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [{
    instrs := [.nop, .mov ⟨0⟩ (.imm (.word64 42))]
    term := .ret
  }]

/-- Optimized target program taking `k₂ = 1` step (`mov [rbp-8], 42; ret`). -/
def progWithoutNop : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [{
    instrs := [.mov ⟨0⟩ (.imm (.word64 42))]
    term := .ret
  }]

/-- Valid initial state for 0-argument `X86Body` procedures. -/
def emptyInitX86State : X86State where
  mem := fun _ => none
  bb := 0
  ip := 0

theorem init_progWithNop : initX86State progWithNop emptyInitX86State :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem init_progWithoutNop : initX86State progWithoutNop emptyInitX86State :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem path_progWithNop :
    StepsToTerminated evalX86Step progWithNop 2 emptyInitX86State
      (.normal (.word64 42)) := by
  refine StepsToTerminated.step (evalStep := evalX86Step) 1 emptyInitX86State
    { emptyInitX86State with ip := 1 } (.normal (X86Val.word64 42)) rfl ?_
  refine StepsToTerminated.step (evalStep := evalX86Step) 0
    { emptyInitX86State with ip := 1 }
    { emptyInitX86State with
      mem := updateSlot emptyInitX86State.mem 0 (some (X86Val.word64 42)), ip := 2 }
    (.normal (X86Val.word64 42)) rfl ?_
  exact StepsToTerminated.done (evalStep := evalX86Step) _ _ rfl

theorem path_progWithoutNop :
    StepsToTerminated evalX86Step progWithoutNop 1 emptyInitX86State
      (.normal (.word64 42)) := by
  refine StepsToTerminated.step 0 emptyInitX86State
    { emptyInitX86State with
      mem := updateSlot emptyInitX86State.mem 0 (some (X86Val.word64 42)), ip := 1 }
    (.normal (X86Val.word64 42)) rfl ?_
  exact StepsToTerminated.done _ _ rfl

theorem progWithNop_defined (n : Nat) :
    (X86Sem progWithNop ⟨emptyInitX86State, n⟩).defined := by
  intro _ tr out hr
  by_cases hle : n ≤ 2
  · have h := (reachesPrefix_iff_of_steps_le path_progWithNop hle tr out).mp hr
    rw [h.2]
    exact True.intro
  · have hgt : 2 + 1 ≤ n := Nat.gt_of_not_le hle
    have h := (reachesPrefix_iff_of_steps_gt path_progWithNop hgt tr out).mp hr
    rw [h.2]
    exact True.intro

/-- Impossibility theorem 1: Under the identity/lockstep behavior morphism
    `fun b => b`, removing a single `.nop` does NOT satisfy `Compiles`. -/
theorem not_compiles_lockstep_nop_deletion :
    ¬ Compiles X86Lang X86Lang (fun b => b) progWithNop progWithoutNop := by
  intro hcomp
  let q : ExecQuery X86State := ⟨emptyInitX86State, 2⟩
  have hdef_src : (X86Sem progWithNop q).defined := progWithNop_defined 2
  cases hcomp q hdef_src with
  | intro hdef_tgt hval =>
    have hreach_tgt :
        ReachesPrefix X86Machine progWithoutNop emptyInitX86State 2
          emptyInitX86State [()] (.terminated (.normal (.word64 42))) :=
      (reachesPrefix_iff_of_steps_gt path_progWithoutNop (Nat.le_refl 2)
        [()] (.terminated (.normal (.word64 42)))).mpr ⟨rfl, rfl⟩
    have hsrc_out := hval ⟨[()], .terminated (.normal (.word64 42))⟩
      ⟨init_progWithoutNop, hreach_tgt⟩
    have hchar := (reachesPrefix_iff_of_steps_le path_progWithNop
      (Nat.le_refl 2) [()] (.terminated (.normal (.word64 42)))).mp hsrc_out.2
    cases hchar.2

/-- Impossibility theorem 2: Even if we re-index queries via an arbitrary
    function `f : ExecQuery X86State → ExecQuery X86State` (preserving
    `q.init = emptyInitX86State` while choosing any source step count
    `(f q).steps`), any trace-preserving behavior map
    `π_query f b q := b (f q)` STILL fails `Compiles` for `.nop` deletion
    because the terminal `Unit` trace length changes from `[(), ()]` to `[()]`. -/
theorem not_compiles_any_trace_preserving_query_map
    (stepsMap : Nat → Nat) :
    let π_q : X86Lang.Behavior → X86Lang.Behavior :=
      fun b q => b ⟨q.init, stepsMap q.steps⟩
    ¬ Compiles X86Lang X86Lang π_q progWithNop progWithoutNop := by
  intro π_q hcomp
  let q : ExecQuery X86State := ⟨emptyInitX86State, 2⟩
  have hdef_src : (π_q (X86Sem progWithNop) q).defined :=
    progWithNop_defined (stepsMap 2)
  cases hcomp q hdef_src with
  | intro hdef_tgt hval =>
    have hreach_tgt :
        ReachesPrefix X86Machine progWithoutNop emptyInitX86State 2
          emptyInitX86State [()] (.terminated (.normal (.word64 42))) :=
      (reachesPrefix_iff_of_steps_gt path_progWithoutNop (Nat.le_refl 2)
        [()] (.terminated (.normal (.word64 42)))).mpr ⟨rfl, rfl⟩
    have hsrc_out := hval ⟨[()], .terminated (.normal (.word64 42))⟩
      ⟨init_progWithoutNop, hreach_tgt⟩
    by_cases hle : stepsMap 2 ≤ 2
    · have hchar := (reachesPrefix_iff_of_steps_le path_progWithNop hle
        [()] (.terminated (.normal (.word64 42)))).mp hsrc_out.2
      cases hchar.2
    · have hgt : 2 + 1 ≤ stepsMap 2 := Nat.gt_of_not_le hle
      have hchar := (reachesPrefix_iff_of_steps_gt path_progWithNop hgt
        [()] (.terminated (.normal (.word64 42)))).mp hsrc_out.2
      cases hchar.1

/-!
## 2. Step-Elastic (`π_elastic`) and Bounded-Progress (`π_progress`, `π_opt`, `π_bounded`) Morphisms
-/

/-- Unconstrained step-elastic behavior morphism (`π_elastic`):
    - `defined`: requires the source behavior to be defined across all step
      budgets `n₁ : Nat` from `decompileInit q₂.init`.
    - `val`: requires `decompileOutcome out₂.outcome` to be reachable in the
      source behavior at some step budget `n₁ : Nat` with some `Unit` trace
      `tr₁ : List Unit`. -/
def π_elastic {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    Behavior (ExecQuery State₂) (ExecOut Unit Val₂) :=
  fun q₂ => {
    defined := ∀ n₁ : Nat, (b ⟨decompileInit q₂.init, n₁⟩).defined
    val := fun hdef out₂ =>
      ∃ (n₁ : Nat) (tr₁ : List Unit),
        (b ⟨decompileInit q₂.init, n₁⟩).val (hdef n₁)
          ⟨tr₁, decompileOutcome out₂.outcome⟩
  }

/-- Progress-preserving step-elastic behavior morphism (`π_progress K`) with
    step-expansion bound `K ≥ 1`:
    - `defined`: requires the source behavior to be defined across all step
      budgets `n₁ : Nat` from `decompileInit q₂.init`.
    - `val`: requires `decompileOutcome out₂.outcome` to be reachable in the
      source behavior at some step budget `n₁ : Nat` satisfying
      `q₂.steps ≤ K * n₁ + (K - 1)`.

    Because `ReachesPrefix.terminated` holds for all `n₁ ≥ k₁ + 1` once the
    source program terminates in `k₁` steps, any terminating target program can
    choose `n₁ = (k₁ + 1) + q₂.steps ≥ q₂.steps` regardless of how many steps
    were deleted (`k₂ ≪ k₁`), while a diverging target program is forced to
    advance `n₁` as `q₂.steps → ∞` and therefore cannot refine a terminating
    source program. -/
def π_progress {State₁ Val₁ State₂ Val₂ : Type} (K : Nat)
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    Behavior (ExecQuery State₂) (ExecOut Unit Val₂) :=
  fun q₂ => {
    defined := ∀ n₁ : Nat, (b ⟨decompileInit q₂.init, n₁⟩).defined
    val := fun hdef out₂ =>
      ∃ (n₁ : Nat) (tr₁ : List Unit),
        q₂.steps ≤ K * n₁ + (K - 1) ∧
        (b ⟨decompileInit q₂.init, n₁⟩).val (hdef n₁)
          ⟨tr₁, decompileOutcome out₂.outcome⟩
  }

/-- Specialization of `π_progress` to `K = 1` (`q₂.steps ≤ n₁`) for
    step-non-increasing (optimizing / instruction-deleting) compiler passes. -/
def π_opt {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    Behavior (ExecQuery State₂) (ExecOut Unit Val₂) :=
  fun q₂ => {
    defined := ∀ n₁ : Nat, (b ⟨decompileInit q₂.init, n₁⟩).defined
    val := fun hdef out₂ =>
      ∃ (n₁ : Nat) (tr₁ : List Unit),
        q₂.steps ≤ n₁ ∧
        (b ⟨decompileInit q₂.init, n₁⟩).val (hdef n₁)
          ⟨tr₁, decompileOutcome out₂.outcome⟩
  }

/-- Bounded-horizon step-elastic behavior morphism (`π_bounded scale offset`):
    restricts both `.defined` and `.val` to source step budgets
    `n₁ ≤ scale * q₂.steps + offset`, preserving finite-prefix definedness
    prior to a later UB step when a compiler pass deletes at most `scale`
    source steps per target step. -/
def π_bounded {State₁ Val₁ State₂ Val₂ : Type} (scale offset : Nat)
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    Behavior (ExecQuery State₂) (ExecOut Unit Val₂) :=
  fun q₂ => {
    defined :=
      ∀ n₁ : Nat, n₁ ≤ scale * q₂.steps + offset →
        (b ⟨decompileInit q₂.init, n₁⟩).defined
    val := fun hdef out₂ =>
      ∃ (n₁ : Nat) (hbound : n₁ ≤ scale * q₂.steps + offset) (tr₁ : List Unit),
        (b ⟨decompileInit q₂.init, n₁⟩).val (hdef n₁ hbound)
          ⟨tr₁, decompileOutcome out₂.outcome⟩
  }

abbrev π_x86_elastic : X86Lang.Behavior → X86Lang.Behavior :=
  π_elastic id id

abbrev π_x86_opt : X86Lang.Behavior → X86Lang.Behavior :=
  π_opt id id

/-- `π_elastic` is monotone for any `decompileInit` and `decompileOutcome`. -/
theorem monotone_π_elastic {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁) :
    Monotone (π_elastic decompileInit decompileOutcome) := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun n₁ => (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).1, ?_⟩
  intro out₂ hout
  cases hout with
  | intro n₁ hrest =>
    cases hrest with
    | intro tr₁ hval₁ =>
      refine ⟨n₁, tr₁, ?_⟩
      exact (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).2
        ⟨tr₁, decompileOutcome out₂.outcome⟩ hval₁

/-- `π_progress K` is monotone for any `K`, `decompileInit`, and
    `decompileOutcome`. -/
theorem monotone_π_progress {State₁ Val₁ State₂ Val₂ : Type} (K : Nat)
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁) :
    Monotone (π_progress K decompileInit decompileOutcome) := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun n₁ => (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).1, ?_⟩
  intro out₂ hout
  cases hout with
  | intro n₁ hrest =>
    cases hrest with
    | intro tr₁ hpair =>
      refine ⟨n₁, tr₁, hpair.1, ?_⟩
      exact (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).2
        ⟨tr₁, decompileOutcome out₂.outcome⟩ hpair.2

/-- `π_opt` is monotone for any `decompileInit` and `decompileOutcome`. -/
theorem monotone_π_opt {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁) :
    Monotone (π_opt decompileInit decompileOutcome) := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun n₁ => (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).1, ?_⟩
  intro out₂ hout
  cases hout with
  | intro n₁ hrest =>
    cases hrest with
    | intro tr₁ hpair =>
      refine ⟨n₁, tr₁, hpair.1, ?_⟩
      exact (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).2
        ⟨tr₁, decompileOutcome out₂.outcome⟩ hpair.2

/-- `π_bounded scale offset` is monotone for any `scale`, `offset`,
    `decompileInit`, and `decompileOutcome`. -/
theorem monotone_π_bounded {State₁ Val₁ State₂ Val₂ : Type} (scale offset : Nat)
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁) :
    Monotone (π_bounded scale offset decompileInit decompileOutcome) := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun n₁ hb => (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁ hb)).1, ?_⟩
  intro out₂ hout
  cases hout with
  | intro n₁ hrest =>
    cases hrest with
    | intro hb hrest₂ =>
      cases hrest₂ with
      | intro tr₁ hval₁ =>
        refine ⟨n₁, hb, tr₁, ?_⟩
        exact (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁ hb)).2
          ⟨tr₁, decompileOutcome out₂.outcome⟩ hval₁

/-- Every `π_opt` behavior refines the corresponding `π_elastic` behavior. -/
theorem π_opt_le_π_elastic {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    π_opt decompileInit decompileOutcome b ≤
      π_elastic decompileInit decompileOutcome b := by
  intro q₂ hdef
  refine ⟨hdef, ?_⟩
  intro out₂ hout
  cases hout with
  | intro n₁ hrest =>
    cases hrest with
    | intro tr₁ hpair =>
      exact ⟨n₁, tr₁, hpair.2⟩

/-- Every `π_progress K` behavior refines the corresponding `π_elastic`
    behavior. -/
theorem π_progress_le_π_elastic {State₁ Val₁ State₂ Val₂ : Type} (K : Nat)
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    π_progress K decompileInit decompileOutcome b ≤
      π_elastic decompileInit decompileOutcome b := by
  intro q₂ hdef
  refine ⟨hdef, ?_⟩
  intro out₂ hout
  cases hout with
  | intro n₁ hrest =>
    cases hrest with
    | intro tr₁ hpair =>
      exact ⟨n₁, tr₁, hpair.2⟩

/-- Closure law 1 (Extensiveness): every behavior `b` refines `π_x86_opt b`
    (and hence `π_x86_elastic b`). -/
theorem le_π_x86_opt (b : X86Lang.Behavior) :
    b ≤ π_x86_opt b := by
  intro q hdef
  refine ⟨hdef q.steps, ?_⟩
  intro out hout
  exact ⟨q.steps, out.trace, Nat.le_refl q.steps, hout⟩

theorem le_π_x86_elastic (b : X86Lang.Behavior) :
    b ≤ π_x86_elastic b :=
  Preorder.le_trans (le_π_x86_opt b) (π_opt_le_π_elastic id id b)

/-- Closure law 2 (Idempotence of `π_x86_elastic`): composing two elastic passes
    collapses to a single `π_x86_elastic`. -/
theorem π_x86_elastic_idem (b : X86Lang.Behavior) :
    π_x86_elastic (π_x86_elastic b) ≤ π_x86_elastic b := by
  intro q hdef
  refine ⟨fun _ => hdef, ?_⟩
  intro out hout
  cases hout with
  | intro n₂ hrest₂ =>
    cases hrest₂ with
    | intro tr₂ hinner =>
      cases hinner with
      | intro n₁ hrest₁ =>
        cases hrest₁ with
        | intro tr₁ hval =>
          exact ⟨n₁, tr₁, hval⟩

/-- Closure law 2' (Idempotence of `π_x86_opt`): composing two optimizing passes
    collapses to a single `π_x86_opt` by transitivity of `≤` on step counts. -/
theorem π_x86_opt_idem (b : X86Lang.Behavior) :
    π_x86_opt (π_x86_opt b) ≤ π_x86_opt b := by
  intro q hdef
  refine ⟨fun _ => hdef, ?_⟩
  intro out hout
  cases hout with
  | intro n₂ hrest₂ =>
    cases hrest₂ with
    | intro tr₂ hpair₂ =>
      cases hpair₂.2 with
      | intro n₁ hrest₁ =>
        cases hrest₁ with
        | intro tr₁ hpair₁ =>
          exact ⟨n₁, tr₁, Nat.le_trans hpair₂.1 hpair₁.1, hpair₁.2⟩

/-- Infinite-looping target program (`bb0: jmp bb0`). -/
def progLoop : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [{
    instrs := []
    term := .jmp ⟨0⟩
  }]

theorem init_progLoop : initX86State progLoop emptyInitX86State :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem progWithoutNop_defined (n : Nat) :
    (X86Sem progWithoutNop ⟨emptyInitX86State, n⟩).defined := by
  intro _ tr out hr
  by_cases hle : n ≤ 1
  · have h := (reachesPrefix_iff_of_steps_le path_progWithoutNop hle tr out).mp hr
    rw [h.2]
    exact True.intro
  · have hgt : 1 + 1 ≤ n := Nat.gt_of_not_le hle
    have h := (reachesPrefix_iff_of_steps_gt path_progWithoutNop hgt tr out).mp hr
    rw [h.2]
    exact True.intro

theorem progLoop_reaches_running (n : Nat) :
    ReachesPrefix X86Machine progLoop emptyInitX86State n
      emptyInitX86State (List.replicate n ()) .running := by
  induction n with
  | zero => exact ReachesPrefix.zero emptyInitX86State
  | succ k ih =>
    exact ReachesPrefix.step k emptyInitX86State emptyInitX86State ()
      (List.replicate k ()) .running rfl ih

/-- Termination-preservation theorem: `π_x86_opt` forbids compiling the
    terminating program `progWithoutNop` into the infinite loop `progLoop`. -/
theorem not_compiles_π_opt_infinite_loop :
    ¬ Compiles X86Lang X86Lang π_x86_opt progWithoutNop progLoop := by
  intro hcomp
  let q : ExecQuery X86State := ⟨emptyInitX86State, 2⟩
  have hdef_src : (π_x86_opt (X86Sem progWithoutNop) q).defined :=
    progWithoutNop_defined
  cases hcomp q hdef_src with
  | intro _ hval =>
    have hloop := hval ⟨[(), ()], .running⟩
      ⟨init_progLoop, progLoop_reaches_running 2⟩
    cases hloop with
    | intro n₁ hrest =>
      cases hrest with
      | intro tr₁ hpair =>
        have hchar := (reachesPrefix_iff_of_steps_gt path_progWithoutNop
          hpair.1 tr₁ .running).mp hpair.2.2
        cases hchar.2

/-!
## 3. Specification Preservation Across `π_elastic` and `π_progress`
-/

/-- General specification-transport theorem for `π_elastic`:
    any `L₁.SpecOn` whose precondition depends only on `q.init` and whose
    postcondition depends only on `q.init` and `out.outcome` maps under
    `π_elastic` directly to the corresponding `L₂.SpecOn`. -/
theorem π_elastic_specOn_le
    {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (P : State₁ → Prop)
    (Q : State₁ → PrefixOutcome Val₁ → Prop) :
    π_elastic decompileInit decompileOutcome
      (fun q₁ => {
        defined := P q₁.init
        val := fun _ out₁ => Q q₁.init out₁.outcome
      }) ≤
      (fun q₂ => {
        defined := P (decompileInit q₂.init)
        val := fun _ out₂ => Q (decompileInit q₂.init) (decompileOutcome out₂.outcome)
      }) := by
  intro q₂ hpre
  refine ⟨fun _ => hpre, ?_⟩
  intro out₂ hout
  cases hout with
  | intro _ hrest =>
    cases hrest with
    | intro _ hQ => exact hQ

/-- General reverse specification-transport theorem for `π_elastic`:
    `π_elastic` and `SpecOn` are mutually refinement-equivalent (`≡`) on
    step-and-trace-independent specifications. -/
theorem specOn_le_π_elastic
    {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (P : State₁ → Prop)
    (Q : State₁ → PrefixOutcome Val₁ → Prop) :
    (fun (q₂ : ExecQuery State₂) => ({
      defined := P (decompileInit q₂.init)
      val := fun _ (out₂ : ExecOut Unit Val₂) =>
        Q (decompileInit q₂.init) (decompileOutcome out₂.outcome)
    } : Partial (ExecOut Unit Val₂ → Prop))) ≤
      π_elastic decompileInit decompileOutcome
        (fun q₁ => {
          defined := P q₁.init
          val := fun _ out₁ => Q q₁.init out₁.outcome
        }) := by
  intro q₂ hdef
  refine ⟨hdef 0, ?_⟩
  intro out₂ hQ
  exact ⟨0, [], hQ⟩

/-- Specialization of specification transport to `X86Lang.SpecOn`: whenever
    `pre` is step-budget-independent (`∀ init n₁ n₂, pre ⟨init, n₁⟩ → pre ⟨init, n₂⟩`)
    and `post` is step-and-trace-independent, `π_x86_elastic (X86Lang.SpecOn pre post)`
    refines `X86Lang.SpecOn pre post`. -/
theorem π_x86_elastic_specOn_le
    {pre : ExecQuery X86State → Prop}
    {post : ExecQuery X86State → ExecOut Unit X86Val → Prop}
    (hpre : ∀ init n₁ n₂, pre ⟨init, n₁⟩ → pre ⟨init, n₂⟩)
    (hpost : ∀ init n₁ n₂ tr₁ tr₂ oc,
      post ⟨init, n₁⟩ ⟨tr₁, oc⟩ → post ⟨init, n₂⟩ ⟨tr₂, oc⟩) :
    π_x86_elastic (X86Lang.SpecOn pre post) ≤ X86Lang.SpecOn pre post := by
  intro q hq
  refine ⟨fun n₁ => hpre q.init q.steps n₁ hq, ?_⟩
  intro out hout
  cases hout with
  | intro n₁ hrest =>
    cases hrest with
    | intro tr₁ hp =>
      exact hpost q.init n₁ q.steps tr₁ out.trace out.outcome hp

/-- Every specification in `Trusted/X86Semantics.lean` is preserved by
    `π_x86_elastic` (and therefore also by `π_x86_opt` and `π_progress K`). -/
theorem π_x86_elastic_wellFormedOn_le
    {pre : ExecQuery X86State → Prop}
    (hpre : ∀ init n₁ n₂, pre ⟨init, n₁⟩ → pre ⟨init, n₂⟩) :
    π_x86_elastic (X86Lang.WellFormedOn pre) ≤ X86Lang.WellFormedOn pre :=
  π_x86_elastic_specOn_le hpre (fun _ _ _ _ _ _ h => h)

theorem π_x86_elastic_wellFormed_le :
    π_x86_elastic X86Lang.WellFormed ≤ X86Lang.WellFormed :=
  π_x86_elastic_wellFormedOn_le (fun _ _ _ h => h)

theorem π_x86_elastic_ensuresRetLibInv_le
    (libInv : LibInv) (retTy : X86Ty)
    {pre : ExecQuery X86State → Prop}
    (hpre : ∀ init n₁ n₂, pre ⟨init, n₁⟩ → pre ⟨init, n₂⟩) :
    π_x86_elastic (EnsuresRetLibInv libInv retTy pre) ≤
      EnsuresRetLibInv libInv retTy pre :=
  π_x86_elastic_specOn_le hpre (fun _ _ _ _ _ _ h => h)

theorem π_x86_elastic_ensuresEqArg_le (argSlot : Nat) :
    π_x86_elastic (EnsuresEqArg argSlot) ≤ EnsuresEqArg argSlot :=
  π_x86_elastic_specOn_le (fun _ _ _ h => h) (fun _ _ _ _ _ _ h => h)

theorem π_x86_elastic_ensuresConst_le (expected : X86Val) :
    π_x86_elastic (EnsuresConst expected) ≤ EnsuresConst expected :=
  π_x86_elastic_specOn_le (fun _ _ _ h => h) (fun _ _ _ _ _ _ h => h)

theorem π_x86_elastic_ensuresBinOp_le (op : X86BinOp) (arg1Slot arg2Slot : Nat) :
    π_x86_elastic (EnsuresBinOp op arg1Slot arg2Slot) ≤
      EnsuresBinOp op arg1Slot arg2Slot :=
  π_x86_elastic_specOn_le (fun _ _ _ h => h) (fun _ _ _ _ _ _ h => h)

/-- End-to-end verification bridge across any variable-step `X86Body` pass:
    if `body` satisfies `spec`, `pass body` compiles from `body` under
    `π_x86_elastic` (or `π_x86_opt` / `π_progress K`), and `π_x86_elastic spec ≤ spec`,
    then `pass body` satisfies `spec` directly in `X86Lang` and discharges
    `C.Verified (pass body) spec` for any downstream compiler `C` (such as
    `AssemblerCompiler`). -/
theorem verify_across_variable_step_pass
    {L_tgt : Language} {C : Compiler X86Lang L_tgt}
    {body optBody : X86Body} {spec : X86Lang.Behavior}
    (h_src : X86Sem body ≤ spec)
    (h_pass : Compiles X86Lang X86Lang π_x86_elastic body optBody)
    (h_spec : π_x86_elastic spec ≤ spec)
    (h_asm : C.SoundOn optBody) :
    C.Verified optBody spec := by
  have h_opt : X86Sem optBody ≤ spec :=
    Preorder.le_trans h_pass
      (Preorder.le_trans (monotone_π_elastic id id h_src) h_spec)
  exact ⟨h_opt, h_asm.2, Preorder.le_trans h_asm.2 (h_asm.1 h_opt)⟩

/-!
## 4. List Drop and Generic State-Mapping Infrastructure for Block-Suffix Simulation
-/

theorem getElem?_of_drop_eq_nil {α : Type} :
    ∀ (xs : List α) (ip : Nat),
      xs.drop ip = [] → xs[ip]? = none
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => by cases h
  | _ :: rest, ip + 1, h => getElem?_of_drop_eq_nil rest ip h

theorem getElem?_of_drop_eq_cons {α : Type} :
    ∀ (xs : List α) (ip : Nat) (x : α) (rem : List α),
      xs.drop ip = x :: rem → xs[ip]? = some x
  | [], 0, _, _, h => by cases h
  | [], _ + 1, _, _, h => by cases h
  | y :: _, 0, x, _, h => by
    injection h with hy _
    rw [hy]
    rfl
  | _ :: rest, ip + 1, x, rem, h => getElem?_of_drop_eq_cons rest ip x rem h

theorem drop_succ_of_drop_eq_cons {α : Type} :
    ∀ (xs : List α) (ip : Nat) (x : α) (rem : List α),
      xs.drop ip = x :: rem → xs.drop (ip + 1) = rem
  | [], 0, _, _, h => by cases h
  | [], _ + 1, _, _, h => by cases h
  | _ :: _, 0, _, _, h => by injection h
  | _ :: rest, ip + 1, x, rem, h => drop_succ_of_drop_eq_cons rest ip x rem h

def mapFrame (fBody : X86Body → X86Body) (f : X86CallFrame) : X86CallFrame where
  callerBody := f.callerBody.map fBody
  callerMem := f.callerMem
  retSlot := f.retSlot
  retBlock := f.retBlock

def mapX86State (fBody : X86Body → X86Body) (s : X86State) : X86State where
  mem := s.mem
  bb := s.bb
  ip := s.ip
  tySizes := s.tySizes
  curBody := s.curBody.map fBody
  stack := s.stack.map (mapFrame fBody)

def mapStepState (f : X86State → X86State)
    (r : StepResult X86State Unit X86Val) : StepResult X86State Unit X86Val :=
  match r with
  | .step obs s' => .step obs (f s')
  | .choice kind branches =>
    .choice kind (fun s₂ => ∃ s₁, branches s₁ ∧ f s₁ = s₂)
  | .terminated t => .terminated t
  | .failed fk => .failed fk

theorem evalX86Instr_mapX86State (fBody : X86Body → X86Body)
    (s : X86State) (ip_tgt : Nat) (instr : X86Instr) :
    evalX86Instr { mapX86State fBody s with ip := ip_tgt } instr =
      mapStepState (fun s' => { mapX86State fBody s' with ip := ip_tgt + 1 })
        (evalX86Instr s instr) := by
  cases instr with
  | mov dst src =>
    dsimp [evalX86Instr, mapX86State]
    cases evalX86Operand s.mem src <;> rfl
  | alu op dst lhs rhs =>
    dsimp [evalX86Instr, mapX86State]
    cases evalX86Operand s.mem lhs with
    | none => rfl
    | some p1 =>
      cases p1 with
      | mk v1 mem1 =>
        dsimp only
        cases evalX86Operand mem1 rhs with
        | none => rfl
        | some p2 =>
          cases p2 with
          | mk v2 mem2 =>
            dsimp only
            cases evalX86BinOp op v1 v2 <;> rfl
  | wrapAdt adtId dst src =>
    dsimp [evalX86Instr, mapX86State]
    cases evalX86Operand s.mem src <;> rfl
  | extractField0 dst src =>
    dsimp [evalX86Instr, mapX86State]
    cases s.mem src.index with
    | none => rfl
    | some v => cases v <;> rfl
  | leaSlot dst target =>
    dsimp [evalX86Instr, mapX86State]
    cases s.mem target.index <;> rfl
  | reborrowSlot dst srcPtr =>
    dsimp [evalX86Instr, mapX86State]
    cases s.mem srcPtr.index with
    | none => rfl
    | some v =>
      cases v with
      | stackPtr target =>
        dsimp only
        cases s.mem target.index <;> rfl
      | _ => rfl
  | allocSlot _ => rfl
  | deallocSlot _ => rfl
  | nop => rfl

/-- Every `X86Instr` evaluation either fails with `.ub` or steps by advancing
    `ip` by `1` and updating `mem` (preserving `bb`, `tySizes`, `curBody`,
    and `stack`). -/
theorem evalX86Instr_cases (s : X86State) (instr : X86Instr) :
    evalX86Instr s instr = .failed .ub ∨
    ∃ mem', evalX86Instr s instr =
      .step () { s with mem := mem', ip := s.ip + 1 } := by
  cases instr with
  | mov dst src =>
    dsimp [evalX86Instr]
    cases evalX86Operand s.mem src with
    | none => exact Or.inl rfl
    | some p => exact Or.inr ⟨_, rfl⟩
  | alu op dst lhs rhs =>
    dsimp [evalX86Instr]
    cases evalX86Operand s.mem lhs with
    | none => exact Or.inl rfl
    | some p1 =>
      cases p1 with
      | mk v1 m1 =>
        dsimp only
        cases evalX86Operand m1 rhs with
        | none => exact Or.inl rfl
        | some p2 =>
          cases p2 with
          | mk v2 m2 =>
            dsimp only
            cases evalX86BinOp op v1 v2 with
            | none => exact Or.inl rfl
            | some outVal => exact Or.inr ⟨_, rfl⟩
  | wrapAdt adtId dst src =>
    dsimp [evalX86Instr]
    cases evalX86Operand s.mem src with
    | none => exact Or.inl rfl
    | some p => exact Or.inr ⟨_, rfl⟩
  | extractField0 dst src =>
    dsimp [evalX86Instr]
    cases s.mem src.index with
    | none => exact Or.inl rfl
    | some v =>
      cases v with
      | adt _ field0 => exact Or.inr ⟨_, rfl⟩
      | _ => exact Or.inl rfl
  | leaSlot dst target =>
    dsimp [evalX86Instr]
    cases s.mem target.index with
    | none => exact Or.inl rfl
    | some _ => exact Or.inr ⟨_, rfl⟩
  | reborrowSlot dst srcPtr =>
    dsimp [evalX86Instr]
    cases s.mem srcPtr.index with
    | none => exact Or.inl rfl
    | some v =>
      cases v with
      | stackPtr target =>
        dsimp only
        cases s.mem target.index with
        | none => exact Or.inl rfl
        | some _ => exact Or.inr ⟨_, rfl⟩
      | _ => exact Or.inl rfl
  | allocSlot dst => exact Or.inr ⟨_, rfl⟩
  | deallocSlot dst => exact Or.inr ⟨_, rfl⟩
  | nop => exact Or.inr ⟨s.mem, rfl⟩

/-- `evalX86Term` is deterministic and never produces `.choice`. -/
theorem evalX86Term_not_choice (s : X86State) (term : X86Term)
    (kind : ChoiceKind) (branches : X86State → Prop) :
    evalX86Term s term ≠ .choice kind branches := by
  intro h
  cases term with
  | ret =>
    dsimp [evalX86Term] at h
    cases hm : s.mem 0 with
    | none => rw [hm] at h; cases h
    | some rv =>
      rw [hm] at h
      cases hst : s.stack <;> (rw [hst] at h; cases h)
  | jmp _ | ud2 | abortPanic | movSizeOfJmp _ _ _ => cases h
  | jccBool cond _ _ =>
    dsimp [evalX86Term] at h
    cases hop : evalX86Operand s.mem cond with
    | none => rw [hop] at h; cases h
    | some p =>
      rw [hop] at h
      cases p with
      | mk v _ =>
        cases v with
        | boolVal b => cases b <;> cases h
        | _ => cases h
  | repMovsbJmp _ srcTy dstTy ptrOp _ =>
    dsimp [evalX86Term] at h
    cases hop : evalX86Operand s.mem ptrOp with
    | none => rw [hop] at h; cases h
    | some p =>
      rw [hop] at h
      cases p with
      | mk ptrVal mem' =>
        dsimp only at h
        cases hrep : evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal <;>
          (rw [hrep] at h; cases h)
  | call1 _ _ arg _ =>
    dsimp [evalX86Term] at h
    cases hop : evalX86Operand s.mem arg <;> (rw [hop] at h; cases h)

theorem evalX86Term_step_ip_zero (s s' : X86State) (term : X86Term)
    (h : evalX86Term s term = .step () s') :
    s'.ip = 0 := by
  cases term with
  | ret =>
    dsimp [evalX86Term] at h
    cases hm : s.mem 0 with
    | none => rw [hm] at h; cases h
    | some retVal =>
      rw [hm] at h
      cases hst : s.stack with
      | nil => rw [hst] at h; cases h
      | cons frame rest =>
        rw [hst] at h
        injection h with _ hs'
        rw [← hs']
  | jmp target =>
    injection h with _ hs'
    rw [← hs']
  | ud2 => cases h
  | abortPanic => cases h
  | jccBool cond falseTarget trueTarget =>
    dsimp [evalX86Term] at h
    cases hop : evalX86Operand s.mem cond with
    | none => rw [hop] at h; cases h
    | some p =>
      rw [hop] at h
      cases p with
      | mk v mem' =>
        cases v with
        | boolVal b =>
          cases b with
          | false => injection h with _ hs'; rw [← hs']
          | true => injection h with _ hs'; rw [← hs']
        | _ => cases h
  | movSizeOfJmp dst ty target =>
    injection h with _ hs'
    rw [← hs']
  | repMovsbJmp dst srcTy dstTy ptrOp target =>
    dsimp [evalX86Term] at h
    cases hop : evalX86Operand s.mem ptrOp with
    | none => rw [hop] at h; cases h
    | some p =>
      rw [hop] at h
      cases p with
      | mk ptrVal mem' =>
        dsimp only at h
        cases hrep : evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal with
        | none => rw [hrep] at h; cases h
        | some outVal =>
          rw [hrep] at h
          injection h with _ hs'
          rw [← hs']
  | call1 dst callee arg target =>
    dsimp [evalX86Term] at h
    cases hop : evalX86Operand s.mem arg with
    | none => rw [hop] at h; cases h
    | some p =>
      rw [hop] at h
      injection h with _ hs'
      rw [← hs']

/-!
## 5. Pass A: Universal Correctness of Instruction Deletion (`stripNops`)
-/

def stripNopsInstrs : List X86Instr → List X86Instr
  | [] => []
  | .nop :: rest => stripNopsInstrs rest
  | i :: rest => i :: stripNopsInstrs rest

mutual
  def stripNopsTerm : X86Term → X86Term
    | .call1 dst callee arg target =>
      .call1 dst (stripNops callee) arg target
    | term => term

  def stripNopsBlock (blk : X86Block) : X86Block :=
    match blk with
    | ⟨instrs, term⟩ => {
        instrs := stripNopsInstrs instrs
        term := stripNopsTerm term
      }

  def stripNopsBlockList : List X86Block → List X86Block
    | [] => []
    | blk :: rest => stripNopsBlock blk :: stripNopsBlockList rest

  def stripNops (body : X86Body) : X86Body :=
    match body with
    | ⟨argTys, retTy, slotCount, blocks, requiredConsts⟩ => {
        argTys := argTys
        retTy := retTy
        slotCount := slotCount
        blocks := stripNopsBlockList blocks
        requiredConsts := requiredConsts
      }
end

theorem stripNopsBlockList_getElem? (bbs : List X86Block) (idx : Nat) :
    (stripNopsBlockList bbs)[idx]? = (bbs[idx]?).map stripNopsBlock := by
  induction bbs generalizing idx with
  | nil => rfl
  | cons bb rest ih =>
    cases idx with
    | zero => rfl
    | succ k => exact ih k

theorem evalX86Term_stripNops (s : X86State) (ip_tgt : Nat) (term : X86Term) :
    evalX86Term { mapX86State stripNops s with ip := ip_tgt }
      (stripNopsTerm term) =
      mapStepState (mapX86State stripNops) (evalX86Term s term) := by
  cases term with
  | ret =>
    dsimp [stripNopsTerm, evalX86Term, mapX86State]
    cases s.mem 0 with
    | none => rfl
    | some retVal =>
      cases s.stack <;> rfl
  | jmp _ => rfl
  | ud2 => rfl
  | abortPanic => rfl
  | jccBool cond _ _ =>
    dsimp [stripNopsTerm, evalX86Term, mapX86State]
    cases evalX86Operand s.mem cond with
    | none => rfl
    | some p =>
      cases p with
      | mk v _ =>
        cases v with
        | boolVal b => cases b <;> rfl
        | _ => rfl
  | movSizeOfJmp _ _ _ => rfl
  | repMovsbJmp _ srcTy dstTy ptrOp _ =>
    dsimp [stripNopsTerm, evalX86Term, mapX86State]
    cases evalX86Operand s.mem ptrOp with
    | none => rfl
    | some p =>
      cases p with
      | mk ptrVal mem' =>
        dsimp only
        cases evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal <;> rfl
  | call1 _ _ arg _ =>
    dsimp [stripNopsTerm, evalX86Term, mapX86State]
    cases evalX86Operand s.mem arg <;> rfl

/-- Simulation relation between a target state `s_tgt` (running `stripNops root`)
    and a source state `s_src` (running `root`):
    - `s_tgt` equals `mapX86State stripNops s_src` with instruction pointer
      `s_tgt.ip`.
    - In any valid basic block `blk_src`, the remaining target instructions
      `(stripNopsBlock blk_src).instrs.drop s_tgt.ip` equal `stripNopsInstrs`
      of the remaining source instructions `blk_src.instrs.drop s_src.ip`. -/
def SimStripNops (root : X86Body) (s_tgt s_src : X86State) : Prop :=
  s_tgt = { mapX86State stripNops s_src with ip := s_tgt.ip } ∧
  ∀ blk_src,
    (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src →
    (stripNopsBlock blk_src).instrs.drop s_tgt.ip =
      stripNopsInstrs (blk_src.instrs.drop s_src.ip)

theorem simStripNops_of_mapX86State_ip_zero (root : X86Body) (s_src : X86State)
    (hip : s_src.ip = 0) :
    SimStripNops root (mapX86State stripNops s_src) s_src := by
  refine ⟨rfl, ?_⟩
  intro blk_src _
  have hip_tgt : (mapX86State stripNops s_src).ip = 0 := hip
  rw [hip_tgt, hip]
  cases blk_src
  rfl

theorem curBody_mapX86State_stripNops (root : X86Body) (s : X86State) (ip : Nat) :
    ({ mapX86State stripNops s with ip := ip } : X86State).curBody.getD
      (stripNops root) =
      stripNops (s.curBody.getD root) := by
  dsimp [mapX86State]
  cases s.curBody <;> rfl

theorem blocks_stripNops (body : X86Body) :
    (stripNops body).blocks = stripNopsBlockList body.blocks := by
  cases body
  rfl

theorem evalX86Step_of_block_none (body : X86Body) (s : X86State)
    (hnone : (s.curBody.getD body).blocks[s.bb]? = none) :
    evalX86Step body s = .failed .ub := by
  dsimp [evalX86Step]
  rw [hnone]

theorem evalX86Step_of_instr_none (body : X86Body) (s : X86State) (blk : X86Block)
    (hblk : (s.curBody.getD body).blocks[s.bb]? = some blk)
    (hinstr : blk.instrs[s.ip]? = none) :
    evalX86Step body s = evalX86Term s blk.term := by
  dsimp [evalX86Step]
  rw [hblk]
  dsimp only
  rw [hinstr]

theorem evalX86Step_of_instr_some (body : X86Body) (s : X86State) (blk : X86Block)
    (instr : X86Instr)
    (hblk : (s.curBody.getD body).blocks[s.bb]? = some blk)
    (hinstr : blk.instrs[s.ip]? = some instr) :
    evalX86Step body s = evalX86Instr s instr := by
  dsimp [evalX86Step]
  rw [hblk]
  dsimp only
  rw [hinstr]

/-- Single-target-step simulation lemma for `stripNops`: one step of
    `stripNops root` from `s_tgt` is matched by `k + 1` steps of `root` from
    `s_src` (consuming `k` leading `.nop` instructions followed by the matching
    non-`nop` instruction or block terminator). -/
theorem step_stripNops_simulation (root : X86Body) (init : X86State) :
    ∀ (s_tgt s_src : X86State),
      SimStripNops root s_tgt s_src →
      (∃ term,
        evalX86Step (stripNops root) s_tgt = .terminated term ∧
        ∃ k, ∀ m,
          ReachesPrefix X86Machine root init (m + k + 1) s_src
            (List.replicate k ()) (.terminated term)) ∨
      (∃ fk,
        evalX86Step (stripNops root) s_tgt = .failed fk ∧
        ∃ k, ∀ m,
          ReachesPrefix X86Machine root init (m + k + 1) s_src
            (List.replicate k ()) (.failed fk)) ∨
      (∃ s_tgt' s_src' k,
        evalX86Step (stripNops root) s_tgt = .step () s_tgt' ∧
        SimStripNops root s_tgt' s_src' ∧
        ∀ n tr out,
          ReachesPrefix X86Machine root init n s_src' tr out →
          ReachesPrefix X86Machine root init (n + k + 1) s_src
            (List.replicate (k + 1) () ++ tr) out) := by
  intro s_tgt s_src hsim
  rcases hsim with ⟨hs_eq, hrem⟩
  cases hblk : (s_src.curBody.getD root).blocks[s_src.bb]? with
  | none =>
    have hblk_tgt :
        (s_tgt.curBody.getD (stripNops root)).blocks[s_tgt.bb]? = none := by
      rw [hs_eq, curBody_mapX86State_stripNops, blocks_stripNops]
      dsimp [mapX86State]
      rw [stripNopsBlockList_getElem?, hblk]
      rfl
    refine Or.inr (Or.inl ⟨.ub,
      evalX86Step_of_block_none (stripNops root) s_tgt hblk_tgt,
      0, fun m => ReachesPrefix.failed m s_src .ub
        (evalX86Step_of_block_none root s_src hblk).symm⟩)
  | some blk_src =>
    have hdrop := hrem blk_src hblk
    generalize hrem_src : blk_src.instrs.drop s_src.ip = rem_src at hdrop
    induction rem_src generalizing s_src with
    | nil =>
      have hip_src : blk_src.instrs[s_src.ip]? = none :=
        getElem?_of_drop_eq_nil blk_src.instrs s_src.ip hrem_src
      have hip_tgt : (stripNopsBlock blk_src).instrs[s_tgt.ip]? = none :=
        getElem?_of_drop_eq_nil (stripNopsBlock blk_src).instrs s_tgt.ip hdrop
      have hblk_tgt :
          (s_tgt.curBody.getD (stripNops root)).blocks[s_tgt.bb]? =
            some (stripNopsBlock blk_src) := by
        rw [hs_eq, curBody_mapX86State_stripNops, blocks_stripNops]
        dsimp [mapX86State]
        rw [stripNopsBlockList_getElem?, hblk]
        rfl
      have hstep_tgt :
          evalX86Step (stripNops root) s_tgt =
            mapStepState (mapX86State stripNops)
              (evalX86Term s_src blk_src.term) := by
        rw [evalX86Step_of_instr_none (stripNops root) s_tgt
          (stripNopsBlock blk_src) hblk_tgt hip_tgt]
        have hterm_eq : (stripNopsBlock blk_src).term = stripNopsTerm blk_src.term := by
          cases blk_src; rfl
        rw [hterm_eq, hs_eq, evalX86Term_stripNops]
      have hstep_src :
          evalX86Step root s_src = evalX86Term s_src blk_src.term :=
        evalX86Step_of_instr_none root s_src blk_src hblk hip_src
      cases hterm_res : evalX86Term s_src blk_src.term with
      | terminated term =>
        rw [hterm_res] at hstep_tgt hstep_src
        exact Or.inl ⟨term, hstep_tgt, 0,
          fun m => ReachesPrefix.terminated m s_src term hstep_src.symm⟩
      | failed fk =>
        rw [hterm_res] at hstep_tgt hstep_src
        exact Or.inr (Or.inl ⟨fk, hstep_tgt, 0,
          fun m => ReachesPrefix.failed m s_src fk hstep_src.symm⟩)
      | step obs s_src' =>
        cases obs
        have hip_zero : s_src'.ip = 0 :=
          evalX86Term_step_ip_zero s_src s_src' blk_src.term hterm_res
        rw [hterm_res] at hstep_tgt hstep_src
        refine Or.inr (Or.inr ⟨mapX86State stripNops s_src', s_src', 0,
          hstep_tgt,
          simStripNops_of_mapX86State_ip_zero root s_src' hip_zero,
          fun n tr out hr =>
            ReachesPrefix.step n s_src s_src' () tr out hstep_src.symm hr⟩)
      | choice kind branches =>
        exact False.elim (evalX86Term_not_choice s_src blk_src.term kind branches hterm_res)
    | cons instr rest ih =>
      have hip_src : blk_src.instrs[s_src.ip]? = some instr :=
        getElem?_of_drop_eq_cons blk_src.instrs s_src.ip instr rest hrem_src
      have hdrop_next : blk_src.instrs.drop (s_src.ip + 1) = rest :=
        drop_succ_of_drop_eq_cons blk_src.instrs s_src.ip instr rest hrem_src
      cases hinstr : instr with
      | nop =>
        rw [hinstr] at hip_src hdrop
        dsimp [stripNopsInstrs] at hdrop
        let s_src₁ : X86State := { s_src with ip := s_src.ip + 1 }
        have hstep_nop : evalX86Step root s_src = .step () s_src₁ :=
          evalX86Step_of_instr_some root s_src blk_src .nop hblk hip_src
        have hsub := ih s_src₁ hs_eq
          (fun b hb => by
            dsimp [s_src₁] at hb
            rw [hblk] at hb
            injection hb with hb_eq
            subst hb_eq
            dsimp [s_src₁]
            rw [hdrop_next]
            exact hdrop)
          hblk hdrop_next hdrop
        rcases hsub with ⟨term, ht, k, hk⟩ | ⟨fk, hf, k, hk⟩ |
          ⟨s_tgt', s_src', k, ht, hsim', hreach⟩
        · refine Or.inl ⟨term, ht, k + 1, fun m => ?_⟩
          have hsum : m + (k + 1) + 1 = (m + k + 1) + 1 := by omega
          rw [hsum]
          exact ReachesPrefix.step (m + k + 1) s_src s_src₁ ()
            (List.replicate k ()) (.terminated term) hstep_nop.symm (hk m)
        · refine Or.inr (Or.inl ⟨fk, hf, k + 1, fun m => ?_⟩)
          have hsum : m + (k + 1) + 1 = (m + k + 1) + 1 := by omega
          rw [hsum]
          exact ReachesPrefix.step (m + k + 1) s_src s_src₁ ()
            (List.replicate k ()) (.failed fk) hstep_nop.symm (hk m)
        · refine Or.inr (Or.inr ⟨s_tgt', s_src', k + 1, ht, hsim', ?_⟩)
          intro n tr out hr
          have hsum : n + (k + 1) + 1 = (n + k + 1) + 1 := by omega
          rw [hsum]
          exact ReachesPrefix.step (n + k + 1) s_src s_src₁ ()
            (List.replicate (k + 1) () ++ tr) out hstep_nop.symm
            (hreach n tr out hr)
      | mov dst src | alu _ dst _ _ | wrapAdt _ dst src
      | extractField0 dst _ | leaSlot dst _ | reborrowSlot dst _
      | allocSlot dst | deallocSlot dst =>
        rw [hinstr] at hip_src hdrop
        dsimp [stripNopsInstrs] at hdrop
        have hip_tgt : (stripNopsBlock blk_src).instrs[s_tgt.ip]? = some instr := by
          rw [hinstr]
          exact getElem?_of_drop_eq_cons (stripNopsBlock blk_src).instrs
            s_tgt.ip _ (stripNopsInstrs rest) hdrop
        have hdrop_tgt_next :
            (stripNopsBlock blk_src).instrs.drop (s_tgt.ip + 1) =
              stripNopsInstrs rest :=
          drop_succ_of_drop_eq_cons (stripNopsBlock blk_src).instrs
            s_tgt.ip _ (stripNopsInstrs rest) hdrop
        have hblk_tgt :
            (s_tgt.curBody.getD (stripNops root)).blocks[s_tgt.bb]? =
              some (stripNopsBlock blk_src) := by
          rw [hs_eq, curBody_mapX86State_stripNops, blocks_stripNops]
          dsimp [mapX86State]
          rw [stripNopsBlockList_getElem?, hblk]
          rfl
        have hstep_tgt :
            evalX86Step (stripNops root) s_tgt =
              mapStepState
                (fun s' => { mapX86State stripNops s' with ip := s_tgt.ip + 1 })
                (evalX86Instr s_src instr) := by
          rw [evalX86Step_of_instr_some (stripNops root) s_tgt
            (stripNopsBlock blk_src) instr hblk_tgt hip_tgt]
          conv => lhs; rw [hs_eq]
          exact evalX86Instr_mapX86State stripNops s_src s_tgt.ip instr
        have hstep_src :
            evalX86Step root s_src = evalX86Instr s_src instr := by
          rw [← hinstr] at hip_src
          exact evalX86Step_of_instr_some root s_src blk_src instr hblk hip_src
        rcases evalX86Instr_cases s_src instr with hinstr_fail | ⟨mem', hinstr_step⟩
        · rw [hinstr_fail] at hstep_tgt hstep_src
          exact Or.inr (Or.inl ⟨.ub, hstep_tgt, 0,
            fun m => ReachesPrefix.failed m s_src .ub hstep_src.symm⟩)
        · rw [hinstr_step] at hstep_tgt hstep_src
          let s_src' : X86State := { s_src with mem := mem', ip := s_src.ip + 1 }
          refine Or.inr (Or.inr ⟨{ mapX86State stripNops s_src' with ip := s_tgt.ip + 1 },
            s_src', 0, hstep_tgt, ?_, ?_⟩)
          · refine ⟨rfl, ?_⟩
            intro b hb
            dsimp [s_src'] at hb
            rw [hblk] at hb
            injection hb with hb_eq
            subst hb_eq
            dsimp [s_src']
            rw [hdrop_tgt_next, hdrop_next]
          · intro n tr out hr
            exact ReachesPrefix.step n s_src s_src' () tr out hstep_src.symm hr

/-- Multi-step backward prefix simulation for `stripNops`: every `n`-step
    target prefix of `stripNops root` from `s_tgt` is matched by an `n₁`-step
    source prefix of `root` from `s_src` with `n ≤ n₁` and identical
    `PrefixOutcome`. -/
theorem reachesPrefix_stripNops (root : X86Body) (init : X86State) (n : Nat) :
    ∀ (s_tgt s_src : X86State) (tr : List Unit) (out : PrefixOutcome X86Val),
      SimStripNops root s_tgt s_src →
      ReachesPrefix X86Machine (stripNops root) init n s_tgt tr out →
      ∃ n₁ tr₁,
        n ≤ n₁ ∧
        ReachesPrefix X86Machine root init n₁ s_src tr₁ out := by
  induction n with
  | zero =>
    intro s_tgt s_src tr out _ hr
    cases hr with
    | zero => exact ⟨0, [], Nat.le_refl 0, ReachesPrefix.zero s_src⟩
  | succ m ih =>
    intro s_tgt s_src tr out hsim hr
    rcases step_stripNops_simulation root init s_tgt s_src hsim with
      ⟨term, hterm, k, hk⟩ | ⟨fk, hfail, k, hk⟩ |
      ⟨s_tgt', s_src', k, hstep, hsim', hprepend⟩
    · cases hr with
      | step _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hterm] at hst; cases hst
      | choice _ _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hterm] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hterm] at hst; cases hst
      | terminated _ _ term' hst =>
        dsimp [X86Machine] at hst
        rw [hterm] at hst
        injection hst with hterm_eq
        subst hterm_eq
        exact ⟨m + k + 1, List.replicate k (), by omega, hk m⟩
      | failed _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hterm] at hst; cases hst
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
    · cases hr with
      | step _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hfail] at hst; cases hst
      | choice _ _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hfail] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hfail] at hst; cases hst
      | terminated _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hfail] at hst; cases hst
      | failed _ _ fk' hst =>
        dsimp [X86Machine] at hst
        rw [hfail] at hst
        injection hst with hfk_eq
        subst hfk_eq
        exact ⟨m + k + 1, List.replicate k (), by omega, hk m⟩
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
    · cases hr with
      | step _ _ s₂ obs tr' _ hst hr' =>
        dsimp [X86Machine] at hst
        rw [hstep] at hst
        injection hst with hobs hs₂
        cases hobs
        rw [hs₂] at hr'
        rcases ih s_tgt' s_src' tr' out hsim' hr' with ⟨n₁', tr₁', hle', hr_src'⟩
        exact ⟨n₁' + k + 1, List.replicate (k + 1) () ++ tr₁',
          by omega, hprepend n₁' tr₁' out hr_src'⟩
      | choice _ _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hstep] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hstep] at hst; cases hst
      | terminated _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hstep] at hst; cases hst
      | failed _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hstep] at hst; cases hst
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)

theorem initX86State_stripNops (body : X86Body) (s : X86State) :
    initX86State (stripNops body) s ↔ initX86State body s := by
  cases body
  rfl

theorem mapX86State_eq_self_of_init (fBody : X86Body → X86Body)
    (body : X86Body) (s : X86State) (hinit : initX86State body s) :
    mapX86State fBody s = s := by
  cases s with
  | mk mem bb ip tySizes curBody stack =>
    have hcur : curBody = none := hinit.2.2.1
    have hst : stack = [] := hinit.2.2.2.1
    subst hcur hst
    rfl

/-- Pass A Universal Correctness Theorem: For every `body : X86Body`,
    `stripNops body` compiles from `body` under the progress-preserving
    optimizing morphism `π_x86_opt` (`q.steps ≤ n₁`). -/
theorem stripNops_compiles_opt (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_opt body (stripNops body) := by
  intro q hdef
  have hsim0 : ∀ (hinit : initX86State body q.init),
      SimStripNops body q.init q.init := by
    intro hinit
    have hmap := mapX86State_eq_self_of_init stripNops body q.init hinit
    have h := simStripNops_of_mapX86State_ip_zero body q.init hinit.2.1
    rw [hmap] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro hinit_tgt tr out hr
    have hinit_src := (initX86State_stripNops body q.init).mp hinit_tgt
    rcases reachesPrefix_stripNops body q.init q.steps q.init q.init tr out
      (hsim0 hinit_src) hr with ⟨n₁, tr₁, _, hr_src⟩
    exact hdef n₁ hinit_src tr₁ out hr_src
  · intro out hout
    have hinit_src := (initX86State_stripNops body q.init).mp hout.1
    rcases reachesPrefix_stripNops body q.init q.steps q.init q.init
      out.trace out.outcome (hsim0 hinit_src) hout.2 with ⟨n₁, tr₁, hle, hr_src⟩
    exact ⟨n₁, tr₁, hle, hinit_src, hr_src⟩

/-- Pass A also compiles under `π_x86_elastic`. -/
theorem stripNops_compiles_elastic (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_elastic body (stripNops body) :=
  Preorder.le_trans (stripNops_compiles_opt body)
    (π_opt_le_π_elastic id id (X86Sem body))

/-!
## 6. Pass B: Universal Correctness of 1-to-Many Instruction Expansion (`expandImmMov`)
-/

/-- Expand every immediate move `.mov dst (.imm v)` into the 2-instruction
    sequence `[.allocSlot dst, .mov dst (.imm v)]`, increasing basic-block step
    counts by the number of immediate moves executed along each branch. -/
def expandInstr : X86Instr → List X86Instr
  | .mov dst (.imm v) => [.allocSlot dst, .mov dst (.imm v)]
  | instr => [instr]

def expandInstrList : List X86Instr → List X86Instr
  | [] => []
  | instr :: rest => expandInstr instr ++ expandInstrList rest

mutual
  def expandTerm : X86Term → X86Term
    | .call1 dst callee arg target =>
      .call1 dst (expandImmMov callee) arg target
    | term => term

  def expandBlock (blk : X86Block) : X86Block :=
    match blk with
    | ⟨instrs, term⟩ => {
        instrs := expandInstrList instrs
        term := expandTerm term
      }

  def expandBlockList : List X86Block → List X86Block
    | [] => []
    | blk :: rest => expandBlock blk :: expandBlockList rest

  def expandImmMov (body : X86Body) : X86Body :=
    match body with
    | ⟨argTys, retTy, slotCount, blocks, requiredConsts⟩ => {
        argTys := argTys
        retTy := retTy
        slotCount := slotCount
        blocks := expandBlockList blocks
        requiredConsts := requiredConsts
      }
end

theorem expandBlockList_getElem? (bbs : List X86Block) (idx : Nat) :
    (expandBlockList bbs)[idx]? = (bbs[idx]?).map expandBlock := by
  induction bbs generalizing idx with
  | nil => rfl
  | cons bb rest ih =>
    cases idx with
    | zero => rfl
    | succ k => exact ih k

theorem evalX86Term_expand (s : X86State) (ip_tgt : Nat) (term : X86Term) :
    evalX86Term { mapX86State expandImmMov s with ip := ip_tgt }
      (expandTerm term) =
      mapStepState (mapX86State expandImmMov) (evalX86Term s term) := by
  cases term with
  | ret =>
    dsimp [expandTerm, evalX86Term, mapX86State]
    cases s.mem 0 with
    | none => rfl
    | some retVal =>
      cases s.stack <;> rfl
  | jmp _ => rfl
  | ud2 => rfl
  | abortPanic => rfl
  | jccBool cond _ _ =>
    dsimp [expandTerm, evalX86Term, mapX86State]
    cases evalX86Operand s.mem cond with
    | none => rfl
    | some p =>
      cases p with
      | mk v _ =>
        cases v with
        | boolVal b => cases b <;> rfl
        | _ => rfl
  | movSizeOfJmp _ _ _ => rfl
  | repMovsbJmp _ srcTy dstTy ptrOp _ =>
    dsimp [expandTerm, evalX86Term, mapX86State]
    cases evalX86Operand s.mem ptrOp with
    | none => rfl
    | some p =>
      cases p with
      | mk ptrVal mem' =>
        dsimp only
        cases evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal <;> rfl
  | call1 _ _ arg _ =>
    dsimp [expandTerm, evalX86Term, mapX86State]
    cases evalX86Operand s.mem arg <;> rfl

def SimExpand (root : X86Body) (s_tgt s_src : X86State) : Prop :=
  s_tgt = { mapX86State expandImmMov s_src with ip := s_tgt.ip } ∧
  ∀ blk_src,
    (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src →
    (expandBlock blk_src).instrs.drop s_tgt.ip =
      expandInstrList (blk_src.instrs.drop s_src.ip)

theorem simExpand_of_mapX86State_ip_zero (root : X86Body) (s_src : X86State)
    (hip : s_src.ip = 0) :
    SimExpand root (mapX86State expandImmMov s_src) s_src := by
  refine ⟨rfl, ?_⟩
  intro blk_src _
  have hip_tgt : (mapX86State expandImmMov s_src).ip = 0 := hip
  rw [hip_tgt, hip]
  cases blk_src
  rfl

theorem curBody_mapX86State_expand (root : X86Body) (s : X86State) (ip : Nat) :
    ({ mapX86State expandImmMov s with ip := ip } : X86State).curBody.getD
      (expandImmMov root) =
      expandImmMov (s.curBody.getD root) := by
  dsimp [mapX86State]
  cases s.curBody <;> rfl

theorem blocks_expand (body : X86Body) :
    (expandImmMov body).blocks = expandBlockList body.blocks := by
  cases body
  rfl

theorem updateSlot_idem (mem : Nat → Option X86Val) (target : Nat)
    (v₁ v₂ : Option X86Val) :
    updateSlot (updateSlot mem target v₁) target v₂ =
      updateSlot mem target v₂ := by
  funext i
  dsimp [updateSlot]
  cases i == target <;> rfl

/-- Single-step / two-step decomposition for `expandImmMov`:
    from any aligned state `SimExpand root s_tgt s_src`, either:
    1. `s_tgt` terminates in 1 step and `s_src` terminates in 1 step,
    2. `s_tgt` fails in 1 step and `s_src` fails in 1 step,
    3. `s_tgt` takes 1 step to `s_tgt'` and `s_src` takes 1 step to `s_src'`
       preserving `SimExpand`, or
    4. `s_tgt` is at the expanded 2-instruction sequence
       `[.allocSlot dst, .mov dst (.imm v)]`, where 1 step of `s_tgt` reaches an
       intermediate state whose next step reaches `s_tgt''` matching 1 step of
       `s_src` to `s_src'` preserving `SimExpand`. -/
theorem step_expand_simulation (root : X86Body) :
    ∀ (s_tgt s_src : X86State),
      SimExpand root s_tgt s_src →
      (∃ term,
        evalX86Step (expandImmMov root) s_tgt = .terminated term ∧
        evalX86Step root s_src = .terminated term) ∨
      (∃ fk,
        evalX86Step (expandImmMov root) s_tgt = .failed fk ∧
        evalX86Step root s_src = .failed fk) ∨
      (∃ s_tgt' s_src',
        evalX86Step (expandImmMov root) s_tgt = .step () s_tgt' ∧
        evalX86Step root s_src = .step () s_src' ∧
        SimExpand root s_tgt' s_src') ∨
      (∃ s_mid s_tgt'' s_src',
        evalX86Step (expandImmMov root) s_tgt = .step () s_mid ∧
        evalX86Step (expandImmMov root) s_mid = .step () s_tgt'' ∧
        evalX86Step root s_src = .step () s_src' ∧
        SimExpand root s_tgt'' s_src') := by
  intro s_tgt s_src hsim
  rcases hsim with ⟨hs_eq, hrem⟩
  cases hblk : (s_src.curBody.getD root).blocks[s_src.bb]? with
  | none =>
    have hblk_tgt :
        (s_tgt.curBody.getD (expandImmMov root)).blocks[s_tgt.bb]? = none := by
      rw [hs_eq, curBody_mapX86State_expand, blocks_expand]
      dsimp [mapX86State]
      rw [expandBlockList_getElem?, hblk]
      rfl
    exact Or.inr (Or.inl ⟨.ub,
      evalX86Step_of_block_none (expandImmMov root) s_tgt hblk_tgt,
      evalX86Step_of_block_none root s_src hblk⟩)
  | some blk_src =>
    have hdrop := hrem blk_src hblk
    cases hrem_src : blk_src.instrs.drop s_src.ip with
    | nil =>
      rw [hrem_src] at hdrop
      dsimp [expandInstrList] at hdrop
      have hip_src : blk_src.instrs[s_src.ip]? = none :=
        getElem?_of_drop_eq_nil blk_src.instrs s_src.ip hrem_src
      have hip_tgt : (expandBlock blk_src).instrs[s_tgt.ip]? = none :=
        getElem?_of_drop_eq_nil (expandBlock blk_src).instrs s_tgt.ip hdrop
      have hblk_tgt :
          (s_tgt.curBody.getD (expandImmMov root)).blocks[s_tgt.bb]? =
            some (expandBlock blk_src) := by
        rw [hs_eq, curBody_mapX86State_expand, blocks_expand]
        dsimp [mapX86State]
        rw [expandBlockList_getElem?, hblk]
        rfl
      have hstep_tgt :
          evalX86Step (expandImmMov root) s_tgt =
            mapStepState (mapX86State expandImmMov)
              (evalX86Term s_src blk_src.term) := by
        rw [evalX86Step_of_instr_none (expandImmMov root) s_tgt
          (expandBlock blk_src) hblk_tgt hip_tgt]
        have hterm_eq : (expandBlock blk_src).term = expandTerm blk_src.term := by
          cases blk_src; rfl
        rw [hterm_eq, hs_eq, evalX86Term_expand]
      have hstep_src :
          evalX86Step root s_src = evalX86Term s_src blk_src.term :=
        evalX86Step_of_instr_none root s_src blk_src hblk hip_src
      cases hterm_res : evalX86Term s_src blk_src.term with
      | terminated term =>
        rw [hterm_res] at hstep_tgt hstep_src
        exact Or.inl ⟨term, hstep_tgt, hstep_src⟩
      | failed fk =>
        rw [hterm_res] at hstep_tgt hstep_src
        exact Or.inr (Or.inl ⟨fk, hstep_tgt, hstep_src⟩)
      | step obs s_src' =>
        cases obs
        have hip_zero : s_src'.ip = 0 :=
          evalX86Term_step_ip_zero s_src s_src' blk_src.term hterm_res
        rw [hterm_res] at hstep_tgt hstep_src
        exact Or.inr (Or.inr (Or.inl ⟨mapX86State expandImmMov s_src', s_src',
          hstep_tgt, hstep_src,
          simExpand_of_mapX86State_ip_zero root s_src' hip_zero⟩))
      | choice kind branches =>
        exact False.elim (evalX86Term_not_choice s_src blk_src.term kind branches hterm_res)
    | cons instr rest =>
      rw [hrem_src] at hdrop
      have hip_src : blk_src.instrs[s_src.ip]? = some instr :=
        getElem?_of_drop_eq_cons blk_src.instrs s_src.ip instr rest hrem_src
      have hdrop_next : blk_src.instrs.drop (s_src.ip + 1) = rest :=
        drop_succ_of_drop_eq_cons blk_src.instrs s_src.ip instr rest hrem_src
      have hblk_tgt :
          (s_tgt.curBody.getD (expandImmMov root)).blocks[s_tgt.bb]? =
            some (expandBlock blk_src) := by
        rw [hs_eq, curBody_mapX86State_expand, blocks_expand]
        dsimp [mapX86State]
        rw [expandBlockList_getElem?, hblk]
        rfl
      cases hinstr : instr with
      | mov dst src =>
        cases hsrc : src with
        | imm v =>
          rw [hinstr, hsrc] at hdrop hip_src
          dsimp [expandInstrList, expandInstr] at hdrop
          have hip_tgt1 :
              (expandBlock blk_src).instrs[s_tgt.ip]? = some (.allocSlot dst) :=
            getElem?_of_drop_eq_cons (expandBlock blk_src).instrs s_tgt.ip
              (.allocSlot dst) (.mov dst (.imm v) :: expandInstrList rest) hdrop
          have hdrop_tgt1 :
              (expandBlock blk_src).instrs.drop (s_tgt.ip + 1) =
                .mov dst (.imm v) :: expandInstrList rest :=
            drop_succ_of_drop_eq_cons (expandBlock blk_src).instrs s_tgt.ip
              (.allocSlot dst) (.mov dst (.imm v) :: expandInstrList rest) hdrop
          have hip_tgt2 :
              (expandBlock blk_src).instrs[s_tgt.ip + 1]? =
                some (.mov dst (.imm v)) :=
            getElem?_of_drop_eq_cons (expandBlock blk_src).instrs (s_tgt.ip + 1)
              (.mov dst (.imm v)) (expandInstrList rest) hdrop_tgt1
          have hdrop_tgt2 :
              (expandBlock blk_src).instrs.drop (s_tgt.ip + 1 + 1) =
                expandInstrList rest :=
            drop_succ_of_drop_eq_cons (expandBlock blk_src).instrs (s_tgt.ip + 1)
              (.mov dst (.imm v)) (expandInstrList rest) hdrop_tgt1
          let s_mid : X86State := {
            s_tgt with
            mem := updateSlot s_tgt.mem dst.index none
            ip := s_tgt.ip + 1
          }
          let s_tgt'' : X86State := {
            s_mid with
            mem := updateSlot s_mid.mem dst.index (some v)
            ip := s_mid.ip + 1
          }
          let s_src' : X86State := {
            s_src with
            mem := updateSlot s_src.mem dst.index (some v)
            ip := s_src.ip + 1
          }
          have hblk_mid :
              (s_mid.curBody.getD (expandImmMov root)).blocks[s_mid.bb]? =
                some (expandBlock blk_src) := hblk_tgt
          refine Or.inr (Or.inr (Or.inr ⟨s_mid, s_tgt'', s_src', ?_, ?_, ?_, ?_⟩))
          · exact evalX86Step_of_instr_some (expandImmMov root) s_tgt
              (expandBlock blk_src) (.allocSlot dst) hblk_tgt hip_tgt1
          · exact evalX86Step_of_instr_some (expandImmMov root) s_mid
              (expandBlock blk_src) (.mov dst (.imm v)) hblk_mid hip_tgt2
          · exact evalX86Step_of_instr_some root s_src blk_src
              (.mov dst (.imm v)) hblk hip_src
          · refine ⟨?_, ?_⟩
            · dsimp [s_tgt'', s_mid, s_src', mapX86State]
              rw [updateSlot_idem]
              have hmem : s_tgt.mem = s_src.mem := by rw [hs_eq]; rfl
              have hbb : s_tgt.bb = s_src.bb := by rw [hs_eq]; rfl
              have hty : s_tgt.tySizes = s_src.tySizes := by rw [hs_eq]; rfl
              have hcur : s_tgt.curBody = s_src.curBody.map expandImmMov := by
                rw [hs_eq]; rfl
              have hst : s_tgt.stack = s_src.stack.map (mapFrame expandImmMov) := by
                rw [hs_eq]; rfl
              rw [hmem, hbb, hty, hcur, hst]
            · intro b hb
              dsimp [s_src'] at hb
              rw [hblk] at hb
              injection hb with hb_eq
              subst hb_eq
              dsimp [s_tgt'', s_mid, s_src']
              rw [hdrop_tgt2, hdrop_next]
        | stackSlot slot consume =>
          rw [hinstr, hsrc] at hdrop hip_src
          dsimp [expandInstrList, expandInstr] at hdrop
          have hip_tgt :
              (expandBlock blk_src).instrs[s_tgt.ip]? =
                some (.mov dst (.stackSlot slot consume)) :=
            getElem?_of_drop_eq_cons (expandBlock blk_src).instrs s_tgt.ip
              _ (expandInstrList rest) hdrop
          have hdrop_tgt_next :
              (expandBlock blk_src).instrs.drop (s_tgt.ip + 1) =
                expandInstrList rest :=
            drop_succ_of_drop_eq_cons (expandBlock blk_src).instrs s_tgt.ip
              _ (expandInstrList rest) hdrop
          have hstep_tgt :
              evalX86Step (expandImmMov root) s_tgt =
                mapStepState
                  (fun s' => { mapX86State expandImmMov s' with ip := s_tgt.ip + 1 })
                  (evalX86Instr s_src (.mov dst (.stackSlot slot consume))) := by
            rw [evalX86Step_of_instr_some (expandImmMov root) s_tgt
              (expandBlock blk_src) (.mov dst (.stackSlot slot consume))
              hblk_tgt hip_tgt]
            conv => lhs; rw [hs_eq]
            exact evalX86Instr_mapX86State expandImmMov s_src s_tgt.ip
              (.mov dst (.stackSlot slot consume))
          have hstep_src :
              evalX86Step root s_src =
                evalX86Instr s_src (.mov dst (.stackSlot slot consume)) :=
            evalX86Step_of_instr_some root s_src blk_src
              (.mov dst (.stackSlot slot consume)) hblk hip_src
          dsimp [evalX86Instr] at hstep_tgt hstep_src
          cases hop : evalX86Operand s_src.mem (.stackSlot slot consume) with
          | none =>
            rw [hop] at hstep_tgt hstep_src
            exact Or.inr (Or.inl ⟨.ub, hstep_tgt, hstep_src⟩)
          | some p =>
            rw [hop] at hstep_tgt hstep_src
            refine Or.inr (Or.inr (Or.inl ⟨_, _, hstep_tgt, hstep_src, ?_⟩))
            refine ⟨rfl, ?_⟩
            intro b hb
            dsimp at hb
            rw [hblk] at hb
            injection hb with hb_eq
            subst hb_eq
            dsimp
            rw [hdrop_tgt_next, hdrop_next]
      | alu _ _ _ _ | wrapAdt _ _ _ | extractField0 _ _
      | leaSlot _ _ | reborrowSlot _ _ | allocSlot _ | deallocSlot _ | nop =>
        rw [hinstr] at hdrop
        dsimp [expandInstrList, expandInstr] at hdrop
        have hip_tgt :
            (expandBlock blk_src).instrs[s_tgt.ip]? = some instr := by
          rw [hinstr]
          exact getElem?_of_drop_eq_cons (expandBlock blk_src).instrs s_tgt.ip
            _ (expandInstrList rest) hdrop
        have hdrop_tgt_next :
            (expandBlock blk_src).instrs.drop (s_tgt.ip + 1) =
              expandInstrList rest :=
          drop_succ_of_drop_eq_cons (expandBlock blk_src).instrs s_tgt.ip
            _ (expandInstrList rest) hdrop
        have hstep_tgt :
            evalX86Step (expandImmMov root) s_tgt =
              mapStepState
                (fun s' => { mapX86State expandImmMov s' with ip := s_tgt.ip + 1 })
                (evalX86Instr s_src instr) := by
          rw [evalX86Step_of_instr_some (expandImmMov root) s_tgt
            (expandBlock blk_src) instr hblk_tgt hip_tgt]
          conv => lhs; rw [hs_eq]
          exact evalX86Instr_mapX86State expandImmMov s_src s_tgt.ip instr
        have hstep_src :
            evalX86Step root s_src = evalX86Instr s_src instr :=
          evalX86Step_of_instr_some root s_src blk_src instr hblk hip_src
        rcases evalX86Instr_cases s_src instr with hinstr_fail | ⟨mem', hinstr_step⟩
        · rw [hinstr_fail] at hstep_tgt hstep_src
          exact Or.inr (Or.inl ⟨.ub, hstep_tgt, hstep_src⟩)
        · rw [hinstr_step] at hstep_tgt hstep_src
          let s_src' : X86State := { s_src with mem := mem', ip := s_src.ip + 1 }
          refine Or.inr (Or.inr (Or.inl
            ⟨{ mapX86State expandImmMov s_src' with ip := s_tgt.ip + 1 },
             s_src', hstep_tgt, hstep_src, ?_⟩))
          refine ⟨rfl, ?_⟩
          intro b hb
          dsimp [s_src'] at hb
          rw [hblk] at hb
          injection hb with hb_eq
          subst hb_eq
          dsimp [s_src']
          rw [hdrop_tgt_next, hdrop_next]

/-- Multi-step backward prefix simulation for `expandImmMov`: every `n`-step
    target prefix of `expandImmMov root` from `s_tgt` is matched by an `n₁`-step
    source prefix of `root` from `s_src` with `n ≤ 2 * n₁ + 1` and identical
    `PrefixOutcome`. -/
theorem reachesPrefix_expandImmMov (root : X86Body) (init : X86State) :
    ∀ (n : Nat) (s_tgt s_src : X86State) (tr : List Unit) (out : PrefixOutcome X86Val),
      SimExpand root s_tgt s_src →
      ReachesPrefix X86Machine (expandImmMov root) init n s_tgt tr out →
      ∃ n₁ tr₁,
        n ≤ 2 * n₁ + 1 ∧
        ReachesPrefix X86Machine root init n₁ s_src tr₁ out
  | 0, _, s_src, _, _, _, hr => by
    cases hr with
    | zero => exact ⟨0, [], by omega, ReachesPrefix.zero s_src⟩
  | n + 1, s_tgt, s_src, tr, out, hsim, hr => by
    rcases step_expand_simulation root s_tgt s_src hsim with
      ⟨term, ht_tgt, ht_src⟩ | ⟨fk, hf_tgt, hf_src⟩ |
      ⟨s_tgt', s_src', h1_tgt, h1_src, hsim'⟩ |
      ⟨s_mid, s_tgt'', s_src', h1_tgt, h2_tgt, h1_src, hsim''⟩
    · cases hr with
      | step _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [ht_tgt] at hst; cases hst
      | choice _ _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [ht_tgt] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [ht_tgt] at hst; cases hst
      | terminated _ _ term' hst =>
        dsimp [X86Machine] at hst
        rw [ht_tgt] at hst
        injection hst with hterm_eq
        rw [hterm_eq]
        exact ⟨n + 1, [], by omega,
          ReachesPrefix.terminated n s_src term ht_src.symm⟩
      | failed _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [ht_tgt] at hst; cases hst
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
    · cases hr with
      | step _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hf_tgt] at hst; cases hst
      | choice _ _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hf_tgt] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hf_tgt] at hst; cases hst
      | terminated _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [hf_tgt] at hst; cases hst
      | failed _ _ fk' hst =>
        dsimp [X86Machine] at hst
        rw [hf_tgt] at hst
        injection hst with hfk_eq
        rw [hfk_eq]
        exact ⟨n + 1, [], by omega,
          ReachesPrefix.failed n s_src fk hf_src.symm⟩
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
    · cases hr with
      | step _ _ s₂ obs tr' _ hst hr' =>
        dsimp [X86Machine] at hst
        rw [h1_tgt] at hst
        injection hst with hobs hs₂
        cases hobs
        rw [hs₂] at hr'
        rcases reachesPrefix_expandImmMov root init n s_tgt' s_src' tr' out
          hsim' hr' with ⟨n₁', tr₁', hbound', hr_src'⟩
        exact ⟨n₁' + 1, () :: tr₁', by omega,
          ReachesPrefix.step n₁' s_src s_src' () tr₁' out h1_src.symm hr_src'⟩
      | choice _ _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | terminated _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | failed _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
    · cases hr with
      | step _ _ s₂ obs tr' _ hst hr' =>
        dsimp [X86Machine] at hst
        rw [h1_tgt] at hst
        injection hst with hobs hs₂
        cases hobs
        rw [hs₂] at hr'
        cases n with
        | zero =>
          cases hr' with
          | zero =>
            exact ⟨0, [], by omega, ReachesPrefix.zero s_src⟩
        | succ k =>
          cases hr' with
          | step _ _ s₃ obs₂ tr'' _ hst₂ hr'' =>
            dsimp [X86Machine] at hst₂
            rw [h2_tgt] at hst₂
            injection hst₂ with hobs₂ hs₃
            cases hobs₂
            rw [hs₃] at hr''
            rcases reachesPrefix_expandImmMov root init k s_tgt'' s_src' tr'' out
              hsim'' hr'' with ⟨n₁', tr₁', hbound', hr_src'⟩
            exact ⟨n₁' + 1, () :: tr₁', by omega,
              ReachesPrefix.step n₁' s_src s_src' () tr₁' out h1_src.symm hr_src'⟩
          | choice _ _ _ _ _ _ _ hst₂ =>
            dsimp [X86Machine] at hst₂; rw [h2_tgt] at hst₂; cases hst₂
          | emptyChoice _ _ _ _ hst₂ =>
            dsimp [X86Machine] at hst₂; rw [h2_tgt] at hst₂; cases hst₂
          | terminated _ _ _ hst₂ =>
            dsimp [X86Machine] at hst₂; rw [h2_tgt] at hst₂; cases hst₂
          | failed _ _ _ hst₂ =>
            dsimp [X86Machine] at hst₂; rw [h2_tgt] at hst₂; cases hst₂
          | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
      | choice _ _ _ _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | emptyChoice _ _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | terminated _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | failed _ _ _ hst =>
        dsimp [X86Machine] at hst; rw [h1_tgt] at hst; cases hst
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)

theorem initX86State_expandImmMov (body : X86Body) (s : X86State) :
    initX86State (expandImmMov body) s ↔ initX86State body s := by
  cases body
  rfl

/-- Pass B Universal Correctness Theorem: For every `body : X86Body`,
    `expandImmMov body` compiles from `body` under the bounded-progress
    morphism `π_progress 2 id id` (`q.steps ≤ 2 * n₁ + 1`). -/
theorem expandImmMov_compiles_progress (body : X86Body) :
    Compiles X86Lang X86Lang (π_progress 2 id id) body (expandImmMov body) := by
  intro q hdef
  have hsim0 : ∀ (hinit : initX86State body q.init),
      SimExpand body q.init q.init := by
    intro hinit
    have hmap := mapX86State_eq_self_of_init expandImmMov body q.init hinit
    have h := simExpand_of_mapX86State_ip_zero body q.init hinit.2.1
    rw [hmap] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro hinit_tgt tr out hr
    have hinit_src := (initX86State_expandImmMov body q.init).mp hinit_tgt
    rcases reachesPrefix_expandImmMov body q.init q.steps q.init q.init tr out
      (hsim0 hinit_src) hr with ⟨n₁, tr₁, _, hr_src⟩
    exact hdef n₁ hinit_src tr₁ out hr_src
  · intro out hout
    have hinit_src := (initX86State_expandImmMov body q.init).mp hout.1
    rcases reachesPrefix_expandImmMov body q.init q.steps q.init q.init
      out.trace out.outcome (hsim0 hinit_src) hout.2 with ⟨n₁, tr₁, hle, hr_src⟩
    exact ⟨n₁, tr₁, hle, hinit_src, hr_src⟩

/-- Pass B also compiles under `π_x86_elastic`. -/
theorem expandImmMov_compiles_elastic (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_elastic body (expandImmMov body) :=
  Preorder.le_trans (expandImmMov_compiles_progress body)
    (π_progress_le_π_elastic 2 id id (X86Sem body))

/-- Bounded-progress morphisms compose by multiplying expansion factors:
    if pass 1 has expansion factor `K₁ ≥ 1` (`n₂ ≤ K₁ * n₁ + (K₁ - 1)`) and
    pass 2 has expansion factor `K₂ ≥ 1` (`n₃ ≤ K₂ * n₂ + (K₂ - 1)`), then
    their composition satisfies `n₃ ≤ (K₂ * K₁) * n₁ + (K₂ * K₁ - 1)`. -/
theorem π_progress_comp
    {State₁ State₂ State₃ Val₁ Val₂ Val₃ : Type}
    (K₁ K₂ : Nat) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (decompileInit₁ : State₂ → State₁) (decompileInit₂ : State₃ → State₂)
    (decompileOutcome₁ : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (decompileOutcome₂ : PrefixOutcome Val₃ → PrefixOutcome Val₂)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    π_progress K₂ decompileInit₂ decompileOutcome₂
        (π_progress K₁ decompileInit₁ decompileOutcome₁ b) ≤
      π_progress (K₂ * K₁) (decompileInit₁ ∘ decompileInit₂)
        (decompileOutcome₁ ∘ decompileOutcome₂) b := by
  intro q₃ hdef
  have hdef₁ : ∀ n₁, (b ⟨decompileInit₁ (decompileInit₂ q₃.init), n₁⟩).defined :=
    hdef
  have hdef₂ : ∀ n₂,
      (π_progress K₁ decompileInit₁ decompileOutcome₁ b
        ⟨decompileInit₂ q₃.init, n₂⟩).defined :=
    fun _ => hdef₁
  refine ⟨hdef₂, fun out₃ hout₃ => ?_⟩
  rcases hout₃ with ⟨n₂, tr₂, hle₂, hout₂⟩
  rcases hout₂ with ⟨n₁, tr₁, hle₁, hout₁⟩
  dsimp at hle₁
  have hmul : q₃.steps ≤ (K₂ * K₁) * n₁ + (K₂ * K₁ - 1) := by
    have h1 : n₂ + 1 ≤ K₁ * (n₁ + 1) := by
      have : K₁ * (n₁ + 1) = K₁ * n₁ + K₁ := by rw [Nat.mul_add, Nat.mul_one]
      omega
    have h2 : q₃.steps + 1 ≤ K₂ * (n₂ + 1) := by
      have : K₂ * (n₂ + 1) = K₂ * n₂ + K₂ := by rw [Nat.mul_add, Nat.mul_one]
      omega
    have h3 : K₂ * (n₂ + 1) ≤ K₂ * (K₁ * (n₁ + 1)) :=
      Nat.mul_le_mul_left K₂ h1
    have h4 : K₂ * (K₁ * (n₁ + 1)) = (K₂ * K₁) * n₁ + K₂ * K₁ := by
      rw [← Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
    have hpos : 1 ≤ K₂ * K₁ := by
      calc 1 = 1 * 1 := rfl
      _ ≤ K₂ * K₁ := Nat.mul_le_mul hK₂ hK₁
    omega
  exact ⟨n₁, tr₁, hmul, hout₁⟩

/-- Since `π_x86_opt` is definitionally equivalent to `π_progress 1 id id`,
    composing Pass A (`stripNops`, factor `1`) and Pass B (`expandImmMov`,
    factor `2`) compiles under the termination-preserving bounded-progress
    morphism `π_progress 2 id id`! -/
theorem stripNops_compiles_progress_one (body : X86Body) :
    Compiles X86Lang X86Lang (π_progress 1 id id) body (stripNops body) := by
  intro q hdef
  have h := stripNops_compiles_opt body q hdef
  refine ⟨h.1, fun out hout => ?_⟩
  rcases h.2 out hout with ⟨n₁, tr₁, hle, hr⟩
  exact ⟨n₁, tr₁, by omega, hr⟩

theorem stripNops_then_expandImmMov_compiles_progress (body : X86Body) :
    Compiles X86Lang X86Lang (π_progress 2 id id) body
      (expandImmMov (stripNops body)) := by
  have h1 := stripNops_compiles_progress_one body
  have h2 := expandImmMov_compiles_progress (stripNops body)
  have hcomp : X86Sem (expandImmMov (stripNops body)) ≤
      π_progress 2 id id (π_progress 1 id id (X86Sem body)) :=
    Preorder.le_trans h2 (monotone_π_progress 2 id id h1)
  exact Preorder.le_trans hcomp
    (π_progress_comp 1 2 (by omega) (by omega) id id id id (X86Sem body))

/-- Composing Pass A (`stripNops`) and Pass B (`expandImmMov`) in a two-pass
    pipeline that both deletes `.nop`s and expands immediate moves also refines
    `body` under `π_x86_elastic`. -/
theorem stripNops_then_expandImmMov_compiles (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_elastic body
      (expandImmMov (stripNops body)) :=
  Preorder.le_trans (stripNops_then_expandImmMov_compiles_progress body)
    (π_progress_le_π_elastic 2 id id (X86Sem body))

/-- Concrete branching example: `progBranchWithNops` branches on boolean argument
    slot 1 (`jccBool`). The `true` branch (block 2) contains two `.nop`
    instructions before moving `42` into return slot 0, whereas the `false`
    branch (block 1) contains zero `.nop` instructions. Consequently, the number
    of steps eliminated by `stripNops` depends dynamically on the runtime branch
    taken (`2` steps eliminated when `arg₀ = true`, `0` steps eliminated when
    `arg₀ = false`). -/
def progBranchWithNops : X86Body where
  argTys := [.bool]
  retTy := .usize
  slotCount := 2
  blocks := [
    -- Block 0: branch on slot 1 (false -> block 1, true -> block 2)
    { instrs := []
      term := .jccBool (.stackSlot ⟨1⟩ false) ⟨1⟩ ⟨2⟩ },
    -- Block 1 (false branch): 0 nops, returns 42
    { instrs := [.mov ⟨0⟩ (.imm (.word64 42))]
      term := .ret },
    -- Block 2 (true branch): 2 nops, returns 42
    { instrs := [.nop, .nop, .mov ⟨0⟩ (.imm (.word64 42))]
      term := .ret }
  ]

/-- Universal theorem `stripNops_compiles_opt` immediately proves that the
    branch-dependent optimization `stripNops progBranchWithNops` compiles from
    `progBranchWithNops` under `π_x86_opt`. -/
theorem progBranchWithNops_stripNops_compiles :
    Compiles X86Lang X86Lang π_x86_opt
      progBranchWithNops (stripNops progBranchWithNops) :=
  stripNops_compiles_opt progBranchWithNops

end ClusterBProbe
