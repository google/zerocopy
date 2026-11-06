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
# Round 2 Probe (R2-2): Stateful Variable-Step Compiler Optimizations Under `π_opt` and `π_progress K`

This standalone, `prelude`-only Lean 4.34.1 module (`import Init.NotationExtra`
only; zero `sorry`, zero warnings, zero `isUnsafe || isPartial` constants)
establishes universal correctness (`Compiles X86Lang X86Lang π_x86_opt`) for
stateful variable-step compiler optimization passes whose source and target
executions diverge both in **step count** and in **intermediate and post-step
memory representations**:

1. **Extensional Memory Congruence (`MemExtEq`, `MemAgreesExcept`, `StateExtEq`,
   `StepResultExtEq`):**
   - Proves without `funext` that `evalX86Operand`, `evalRepMovsb`,
     `evalX86Instr`, `evalX86Term`, `evalX86Step`, and `ReachesPrefix` preserve
     extensional state equality (`StateExtEq`, including pairwise extensional
     equality of saved caller memories in `X86CallFrame` stacks).
   - Introduces `MemAgreesExcept deadSlot m₁ m₂` (`∀ i, i ≠ deadSlot →
     m₁ i = m₂ i`) to track temporary memory divergence on a dead scratch slot
     and proves the reconvergence theorem
     `memExtEq_of_memAgreesExcept_updateSlot`: once both executions clear
     `deadSlot` (via `.deallocSlot`), `MemAgreesExcept` reconverges to full
     `MemExtEq`.
2. **Unified Multi-Step Peephole Simulation Engine (`mapBodyInstrs`, `SimPass`,
   `StepSimOutcome`, `reachesPrefix_of_stepSim`):**
   - Factors the block-suffix (`blk.instrs.drop s.ip`) and `StateExtEq`
     simulation invariant across arbitrary control-flow graphs (`jmp`,
     `jccBool`, loops, and inter-procedural `call1` / `ret`) into a single
     reusable engine parameterized by `fInstrs : List X86Instr → List X86Instr`.
3. **Stateful Variable-Step Pass 1 — Dead Store + Dealloc Elimination
   (`elimDeadStoreDealloc`):**
   - Compresses `.mov tmp (.imm v) :: .deallocSlot tmp :: rest` into
     `.deallocSlot tmp :: rest` (2-to-1 compression) and proves universal
     refinement `elimDeadStoreDealloc_compiles_opt` for all `body : X86Body`.
4. **Stateful Variable-Step Pass 2 — Copy Coalescing / Scratch-Reg Move Fusion
   (`fuseScratchMov`):**
   - Compresses `.mov tmp (.imm v) :: .mov dst (.stackSlot tmp consume) ::
     .deallocSlot tmp :: rest` (when `tmp.index ≠ 0` and `dst.index ≠ tmp.index`)
     into `.mov dst (.imm v) :: .deallocSlot tmp :: rest` (3-to-2 compression),
     handling mid-sequence prefix truncation at `.running` and proving universal
     refinement `fuseScratchMov_compiles_opt` for all `body : X86Body`.
5. **Full 3-Pass Variable-Step Optimization Pipeline (`optPipeline`):**
   - Composes `fuseScratchMov`, `elimDeadStoreDealloc`, and `stripNops` into
     `optPipeline : X86Body → X86Body`, proves `optPipeline_compiles_opt` for
     all `body : X86Body`, and proves end-to-end `AssemblerCompiler.Verified`
     preservation on a concrete Stage 0 `X86Body` containing scratch moves,
     dead temporary stores, and `nop`s.
-/

namespace R2StatefulVarStepProbe

/-!
## 0. Exact Core Definitions from `trusted/lean/Trusted/` and Round 1 `π_opt` / `π_progress`
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
  R2StatefulVarStepProbe.Behavior L.Query L.Out

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

/-- Convenience alias for a non-consuming stack-slot/virtual-register read. -/
abbrev X86Operand.reg (slot : SlotId) : X86Operand :=
  .stackSlot slot false

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

structure TargetArtifact where
  private mk ::
  unit : Unit

opaque assemble : X86Body → TargetArtifact := fun _ => { unit := () }

opaque TargetSem :
    TargetArtifact → ExecQuery X86State → Partial (ExecOut Unit X86Val → Prop) :=
  fun _ _ => Partial.ub

def TargetLang : Language where
  Prog := TargetArtifact
  Query := ExecQuery X86State
  Out := ExecOut Unit X86Val
  sem := TargetSem

opaque π_asm : X86Lang.Behavior → TargetLang.Behavior :=
  fun b => b

def AssemblerCompiler : Compiler X86Lang TargetLang where
  compile := assemble
  π := π_asm

/-- Unconstrained step-elastic behavior morphism (`π_elastic`). -/
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

/-- Bounded-progress behavior morphism (`π_progress K`). -/
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

/-- Optimizing (step-non-increasing) behavior morphism (`π_opt`, `q₂.steps ≤ n₁`). -/
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

abbrev π_x86_elastic : X86Lang.Behavior → X86Lang.Behavior :=
  π_elastic id id

abbrev π_x86_opt : X86Lang.Behavior → X86Lang.Behavior :=
  π_opt id id

theorem monotone_π_elastic {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁) :
    Monotone (π_elastic decompileInit decompileOutcome) := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun n₁ => (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).1, ?_⟩
  intro out₂ hout
  let ⟨n₁, tr₁, hval₁⟩ := hout
  exact ⟨n₁, tr₁,
    (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).2
      ⟨tr₁, decompileOutcome out₂.outcome⟩ hval₁⟩

theorem monotone_π_opt {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁) :
    Monotone (π_opt decompileInit decompileOutcome) := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun n₁ => (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).1, ?_⟩
  intro out₂ hout
  let ⟨n₁, tr₁, hle_steps, hval₁⟩ := hout
  exact ⟨n₁, tr₁, hle_steps,
    (hle ⟨decompileInit q₂.init, n₁⟩ (hdef₂ n₁)).2
      ⟨tr₁, decompileOutcome out₂.outcome⟩ hval₁⟩

theorem π_opt_le_π_elastic {State₁ Val₁ State₂ Val₂ : Type}
    (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Val₂ → PrefixOutcome Val₁)
    (b : Behavior (ExecQuery State₁) (ExecOut Unit Val₁)) :
    π_opt decompileInit decompileOutcome b ≤
      π_elastic decompileInit decompileOutcome b := by
  intro q₂ hdef
  refine ⟨hdef, fun out₂ hout => ?_⟩
  let ⟨n₁, tr₁, _, hval⟩ := hout
  exact ⟨n₁, tr₁, hval⟩

theorem π_x86_opt_idem (b : X86Lang.Behavior) :
    π_x86_opt (π_x86_opt b) ≤ π_x86_opt b := by
  intro q hdef
  refine ⟨fun _ => hdef, fun out hout => ?_⟩
  let ⟨n₂, tr₂, hle₂, n₁, tr₁, hle₁, hval₁⟩ := hout
  exact ⟨n₁, tr₁, Nat.le_trans hle₂ hle₁, hval₁⟩

/-- Transitive composition of two `π_x86_opt` compiler passes: since `π_x86_opt`
    is monotone and idempotent (`π_x86_opt (π_x86_opt b) ≤ π_x86_opt b`),
    composing two `π_x86_opt` passes yields a `π_x86_opt` pass. -/
theorem compiles_opt_trans {b₁ b₂ b₃ : X86Body}
    (h₁₂ : Compiles X86Lang X86Lang π_x86_opt b₁ b₂)
    (h₂₃ : Compiles X86Lang X86Lang π_x86_opt b₂ b₃) :
    Compiles X86Lang X86Lang π_x86_opt b₁ b₃ :=
  Preorder.le_trans h₂₃
    (Preorder.le_trans (monotone_π_opt id id h₁₂) (π_x86_opt_idem (X86Sem b₁)))

theorem π_x86_opt_specOn_le
    {pre : ExecQuery X86State → Prop}
    {post : ExecQuery X86State → ExecOut Unit X86Val → Prop}
    (hpre : ∀ init n₁ n₂, pre ⟨init, n₁⟩ → pre ⟨init, n₂⟩)
    (hpost : ∀ init n₁ n₂ tr₁ tr₂ oc,
      post ⟨init, n₁⟩ ⟨tr₁, oc⟩ → post ⟨init, n₂⟩ ⟨tr₂, oc⟩) :
    π_x86_opt (X86Lang.SpecOn pre post) ≤ X86Lang.SpecOn pre post := by
  intro q hq
  refine ⟨fun n₁ => hpre q.init q.steps n₁ hq, fun out hout => ?_⟩
  let ⟨n₁, tr₁, _, hp⟩ := hout
  exact hpost q.init n₁ q.steps tr₁ out.trace out.outcome hp

theorem verify_across_opt_pass
    {L_tgt : Language} {C : Compiler X86Lang L_tgt}
    {body optBody : X86Body} {spec : X86Lang.Behavior}
    (h_src : X86Sem body ≤ spec)
    (h_pass : Compiles X86Lang X86Lang π_x86_opt body optBody)
    (h_spec : π_x86_opt spec ≤ spec)
    (h_asm : C.SoundOn optBody) :
    C.Verified optBody spec := by
  have h_opt : X86Sem optBody ≤ spec :=
    Preorder.le_trans h_pass
      (Preorder.le_trans (monotone_π_opt id id h_src) h_spec)
  exact ⟨h_opt, h_asm.2, Preorder.le_trans h_asm.2 (h_asm.1 h_opt)⟩

/-!
## 1. Extensional Memory Congruence (`MemExtEq`, `MemAgreesExcept`, `StateExtEq`, `StepResultExtEq`)

In `Trusted/X86Semantics.lean`, stack-frame memory `s.mem` has function type
`Nat → Option X86Val`, and `updateSlot` constructs a new lambda closure
`fun i => if i == target then val else mem i`.

When a stateful optimization pass eliminates a temporary store or coalesces a
scratch-slot copy:
1. During intermediate steps (before `.deallocSlot tmp`), the source memory
   holds `some v` at `tmp.index` while the target memory has not written
   `tmp.index`. Thus the two memories satisfy `MemAgreesExcept tmp.index`
   (`∀ i, i ≠ tmp.index → m₁ i = m₂ i`).
2. Once `.deallocSlot tmp` executes in both programs, `tmp.index` is reset to
   `none` on both sides. However, the source memory has an extra nested
   `updateSlot` wrapper compared to the target memory, so they are
   **extensionally equal** (`MemExtEq m₁ m₂`, i.e., `∀ i, m₁ i = m₂ i`) rather
   than syntactically identical.

We prove below (without `funext`) that `MemAgreesExcept` reconverges to
`MemExtEq` upon `.deallocSlot`, and that every semantic operation in
`Trusted/X86Semantics.lean` (`argsMatchStack`, `initX86State`,
`evalX86Operand`, `evalRepMovsb`, `evalX86Instr`, `evalX86Term`, `evalX86Step`,
and `ReachesPrefix`) is congruent with respect to `MemExtEq` and `StateExtEq`.
-/

/-- Pointwise (extensional) equality of stack-frame memories. -/
def MemExtEq (m₁ m₂ : Nat → Option X86Val) : Prop :=
  ∀ i : Nat, m₁ i = m₂ i

theorem memExtEq_refl (m : Nat → Option X86Val) : MemExtEq m m :=
  fun _ => rfl

theorem memExtEq_symm {m₁ m₂ : Nat → Option X86Val} (h : MemExtEq m₁ m₂) :
    MemExtEq m₂ m₁ :=
  fun i => (h i).symm

theorem memExtEq_trans {m₁ m₂ m₃ : Nat → Option X86Val}
    (h₁₂ : MemExtEq m₁ m₂) (h₂₃ : MemExtEq m₂ m₃) :
    MemExtEq m₁ m₃ :=
  fun i => Eq.trans (h₁₂ i) (h₂₃ i)

/-- Pointwise agreement of two stack-frame memories at all slot indices except a
    dead temporary slot `deadSlot`. -/
def MemAgreesExcept (deadSlot : Nat) (m₁ m₂ : Nat → Option X86Val) : Prop :=
  ∀ i : Nat, i ≠ deadSlot → m₁ i = m₂ i

theorem memAgreesExcept_of_memExtEq (deadSlot : Nat)
    {m₁ m₂ : Nat → Option X86Val} (h : MemExtEq m₁ m₂) :
    MemAgreesExcept deadSlot m₁ m₂ :=
  fun i _ => h i

/-- Updating `target` with `val` on both sides preserves `MemExtEq`. -/
theorem memExtEq_updateSlot {m₁ m₂ : Nat → Option X86Val}
    (h : MemExtEq m₁ m₂) (target : Nat) (val : Option X86Val) :
    MemExtEq (updateSlot m₁ target val) (updateSlot m₂ target val) := by
  intro i
  dsimp [updateSlot]
  cases i == target with
  | true => rfl
  | false => exact h i

/-- Idempotence of `updateSlot` at the same slot index (`MemExtEq` without
    `funext`). -/
theorem memExtEq_updateSlot_idem (m : Nat → Option X86Val) (target : Nat)
    (v₁ v₂ : Option X86Val) :
    MemExtEq (updateSlot (updateSlot m target v₁) target v₂)
      (updateSlot m target v₂) := by
  intro i
  dsimp [updateSlot]
  cases i == target <;> rfl

/-- Commutativity of `updateSlot` at distinct slot indices (`t₁ ≠ t₂`, proved
    without `funext`). -/
theorem memExtEq_updateSlot_comm (m : Nat → Option X86Val) {t₁ t₂ : Nat}
    (hne : t₁ ≠ t₂) (v₁ v₂ : Option X86Val) :
    MemExtEq (updateSlot (updateSlot m t₁ v₁) t₂ v₂)
      (updateSlot (updateSlot m t₂ v₂) t₁ v₁) := by
  intro i
  dsimp [updateSlot]
  cases h2 : i == t₂ with
  | true =>
    have hi2 : i = t₂ := eq_of_beq h2
    subst hi2
    have h1 : (i == t₁) = false := beq_false_of_ne (Ne.symm hne)
    rw [h1]
    rfl
  | false =>
    cases h1 : i == t₁ <;> rfl

/-- Writing to `deadSlot` on the right preserves `MemAgreesExcept deadSlot`. -/
theorem memAgreesExcept_updateSlot_dead_right {m₁ m₂ : Nat → Option X86Val}
    {deadSlot : Nat} (h : MemAgreesExcept deadSlot m₁ m₂)
    (val : Option X86Val) :
    MemAgreesExcept deadSlot m₁ (updateSlot m₂ deadSlot val) := by
  intro i hne
  dsimp [updateSlot]
  have hbeq : (i == deadSlot) = false := beq_false_of_ne hne
  rw [hbeq]
  exact h i hne

/-- Writing to any slot `dst` with the same value `val` on both sides preserves
    `MemAgreesExcept deadSlot`. -/
theorem memAgreesExcept_updateSlot_both {m₁ m₂ : Nat → Option X86Val}
    {deadSlot : Nat} (h : MemAgreesExcept deadSlot m₁ m₂)
    (dst : Nat) (val : Option X86Val) :
    MemAgreesExcept deadSlot (updateSlot m₁ dst val) (updateSlot m₂ dst val) := by
  intro i hne
  dsimp [updateSlot]
  cases i == dst with
  | true => rfl
  | false => exact h i hne

/-- **Reconvergence Lemma:** If `m₁` and `m₂` agree at all slots except
    `deadSlot` (`MemAgreesExcept deadSlot m₁ m₂`), then overwriting `deadSlot`
    with the same value `val` (such as `none` on `.deallocSlot`) on both sides
    restores full extensional memory equality `MemExtEq`! -/
theorem memExtEq_of_memAgreesExcept_updateSlot {m₁ m₂ : Nat → Option X86Val}
    {deadSlot : Nat} (h : MemAgreesExcept deadSlot m₁ m₂)
    (val : Option X86Val) :
    MemExtEq (updateSlot m₁ deadSlot val) (updateSlot m₂ deadSlot val) := by
  intro i
  dsimp [updateSlot]
  cases heq : i == deadSlot with
  | true => rfl
  | false =>
    exact h i (ne_of_beq_false heq)

/-- Reading a slot `target` that was just written by `updateSlot m target val`
    returns `val`. -/
theorem updateSlot_same (m : Nat → Option X86Val) (target : Nat)
    (val : Option X86Val) :
    updateSlot m target val target = val := by
  dsimp [updateSlot]
  rw [beq_self_eq_true target]
  rfl

/-- Reading a slot `i ≠ target` across `updateSlot m target val` returns `m i`. -/
theorem updateSlot_of_ne (m : Nat → Option X86Val) {i target : Nat}
    (hne : i ≠ target) (val : Option X86Val) :
    updateSlot m target val i = m i := by
  dsimp [updateSlot]
  rw [beq_false_of_ne hne]
  rfl

/-- Extensional equality of saved caller stack frames (`X86CallFrame`). -/
def FrameExtEq (f₁ f₂ : X86CallFrame) : Prop :=
  f₁.callerBody = f₂.callerBody ∧
  MemExtEq f₁.callerMem f₂.callerMem ∧
  f₁.retSlot = f₂.retSlot ∧
  f₁.retBlock = f₂.retBlock

theorem frameExtEq_refl (f : X86CallFrame) : FrameExtEq f f :=
  ⟨rfl, memExtEq_refl f.callerMem, rfl, rfl⟩

theorem frameExtEq_symm {f₁ f₂ : X86CallFrame} (h : FrameExtEq f₁ f₂) :
    FrameExtEq f₂ f₁ :=
  ⟨h.1.symm, memExtEq_symm h.2.1, h.2.2.1.symm, h.2.2.2.symm⟩

theorem frameExtEq_trans {f₁ f₂ f₃ : X86CallFrame}
    (h₁₂ : FrameExtEq f₁ f₂) (h₂₃ : FrameExtEq f₂ f₃) :
    FrameExtEq f₁ f₃ :=
  ⟨Eq.trans h₁₂.1 h₂₃.1,
   memExtEq_trans h₁₂.2.1 h₂₃.2.1,
   Eq.trans h₁₂.2.2.1 h₂₃.2.2.1,
   Eq.trans h₁₂.2.2.2 h₂₃.2.2.2⟩

/-- Pointwise extensional equality of call stacks (`List X86CallFrame`). -/
inductive StackExtEq : List X86CallFrame → List X86CallFrame → Prop where
  | nil : StackExtEq [] []
  | cons {f₁ f₂ : X86CallFrame} {s₁ s₂ : List X86CallFrame} :
      FrameExtEq f₁ f₂ →
      StackExtEq s₁ s₂ →
      StackExtEq (f₁ :: s₁) (f₂ :: s₂)

theorem stackExtEq_refl : ∀ (st : List X86CallFrame), StackExtEq st st
  | [] => .nil
  | f :: rest => .cons (frameExtEq_refl f) (stackExtEq_refl rest)

theorem stackExtEq_symm {st₁ st₂ : List X86CallFrame}
    (h : StackExtEq st₁ st₂) : StackExtEq st₂ st₁ := by
  induction h with
  | nil => exact .nil
  | cons hf _ ih => exact .cons (frameExtEq_symm hf) ih

theorem stackExtEq_trans {st₁ st₂ st₃ : List X86CallFrame}
    (h₁₂ : StackExtEq st₁ st₂) (h₂₃ : StackExtEq st₂ st₃) :
    StackExtEq st₁ st₃ := by
  induction h₁₂ generalizing st₃ with
  | nil => exact h₂₃
  | cons hf₁₂ _ ih =>
    cases h₂₃ with
    | cons hf₂₃ hst₂₃ =>
      exact .cons (frameExtEq_trans hf₁₂ hf₂₃) (ih hst₂₃)

/-- Extensional equality of `X86State` configurations (`StateExtEq`). -/
def StateExtEq (s₁ s₂ : X86State) : Prop :=
  MemExtEq s₁.mem s₂.mem ∧
  s₁.bb = s₂.bb ∧
  s₁.ip = s₂.ip ∧
  s₁.tySizes = s₂.tySizes ∧
  s₁.curBody = s₂.curBody ∧
  StackExtEq s₁.stack s₂.stack

theorem stateExtEq_refl (s : X86State) : StateExtEq s s :=
  ⟨memExtEq_refl s.mem, rfl, rfl, rfl, rfl, stackExtEq_refl s.stack⟩

theorem stateExtEq_symm {s₁ s₂ : X86State} (h : StateExtEq s₁ s₂) :
    StateExtEq s₂ s₁ :=
  ⟨memExtEq_symm h.1, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm,
   h.2.2.2.2.1.symm, stackExtEq_symm h.2.2.2.2.2⟩

theorem stateExtEq_trans {s₁ s₂ s₃ : X86State}
    (h₁₂ : StateExtEq s₁ s₂) (h₂₃ : StateExtEq s₂ s₃) :
    StateExtEq s₁ s₃ :=
  ⟨memExtEq_trans h₁₂.1 h₂₃.1,
   Eq.trans h₁₂.2.1 h₂₃.2.1,
   Eq.trans h₁₂.2.2.1 h₂₃.2.2.1,
   Eq.trans h₁₂.2.2.2.1 h₂₃.2.2.2.1,
   Eq.trans h₁₂.2.2.2.2.1 h₂₃.2.2.2.2.1,
   stackExtEq_trans h₁₂.2.2.2.2.2 h₂₃.2.2.2.2.2⟩

/-- Extensional equality of deterministic `StepResult` outcomes. -/
inductive StepResultExtEq :
    StepResult X86State Unit X86Val →
    StepResult X86State Unit X86Val → Prop where
  | step {s₁' s₂' : X86State} :
      StateExtEq s₁' s₂' →
      StepResultExtEq (.step () s₁') (.step () s₂')
  | terminated (term : TerminationKind X86Val) :
      StepResultExtEq (.terminated term) (.terminated term)
  | failed (fk : FailureKind) :
      StepResultExtEq (.failed fk) (.failed fk)

theorem argsMatchStack_foldr_extEq (tySizes : Nat → Nat)
    (argTys : List X86Ty) {m₁ m₂ : Nat → Option X86Val}
    (hmem : MemExtEq m₁ m₂) :
    ∀ (k : Nat),
      argTys.foldr
        (fun ty rest idx =>
          (∃ v, m₁ idx = some v ∧ v.hasTy tySizes ty) ∧ rest (idx + 1))
        (fun idx => ∀ j, idx ≤ j → m₁ j = none)
        k →
      argTys.foldr
        (fun ty rest idx =>
          (∃ v, m₂ idx = some v ∧ v.hasTy tySizes ty) ∧ rest (idx + 1))
        (fun idx => ∀ j, idx ≤ j → m₂ j = none)
        k := by
  induction argTys with
  | nil =>
    intro k h j hj
    rw [← hmem j]
    exact h j hj
  | cons ty rest ih =>
    intro k h
    let ⟨⟨v, hv, hty⟩, hrest⟩ := h
    refine ⟨⟨v, ?_, hty⟩, ih (k + 1) hrest⟩
    rw [← hmem k]
    exact hv

/-- `argsMatchStack` is invariant under `MemExtEq`. -/
theorem argsMatchStack_extEq (tySizes : Nat → Nat) (argTys : List X86Ty)
    {m₁ m₂ : Nat → Option X86Val} (hmem : MemExtEq m₁ m₂) :
    argsMatchStack tySizes argTys m₁ ↔ argsMatchStack tySizes argTys m₂ :=
  ⟨argsMatchStack_foldr_extEq tySizes argTys hmem 1,
   argsMatchStack_foldr_extEq tySizes argTys (memExtEq_symm hmem) 1⟩

theorem stackExtEq_nil_right {st₂ : List X86CallFrame}
    (h : StackExtEq [] st₂) : st₂ = [] := by
  cases h
  rfl

theorem stackExtEq_nil_left {st₁ : List X86CallFrame}
    (h : StackExtEq st₁ []) : st₁ = [] := by
  cases h
  rfl

/-- `initX86State` is invariant under `StateExtEq`. -/
theorem initX86State_extEq (body : X86Body) {s₁ s₂ : X86State}
    (hs : StateExtEq s₁ s₂) :
    initX86State body s₁ ↔ initX86State body s₂ := by
  let ⟨hmem, hbb, hip, hty, hcur, hst⟩ := hs
  constructor
  · intro h
    let ⟨hb1, hi1, hc1, hst1, hm0, hargs⟩ := h
    have hst' : StackExtEq [] s₂.stack := by
      rw [← hst1]
      exact hst
    refine ⟨Eq.trans hbb.symm hb1, Eq.trans hip.symm hi1,
      Eq.trans hcur.symm hc1, stackExtEq_nil_right hst',
      Eq.trans (hmem 0).symm hm0, ?_⟩
    rw [← hty]
    exact (argsMatchStack_extEq s₁.tySizes body.argTys hmem).mp hargs
  · intro h
    let ⟨hb2, hi2, hc2, hst2, hm0, hargs⟩ := h
    have hst' : StackExtEq s₁.stack [] := by
      rw [← hst2]
      exact hst
    refine ⟨Eq.trans hbb hb2, Eq.trans hip hi2,
      Eq.trans hcur hc2, stackExtEq_nil_left hst',
      Eq.trans (hmem 0) hm0, ?_⟩
    rw [hty]
    exact (argsMatchStack_extEq s₂.tySizes body.argTys (memExtEq_symm hmem)).mp hargs

/-- Extensional memory congruence of `evalX86Operand`: evaluating `op` on
    extensionally equal memories `m₁` and `m₂` either fails on both or yields
    identical values `v` and extensionally equal updated memories `m₁'`, `m₂'`. -/
theorem evalX86Operand_extEq {m₁ m₂ : Nat → Option X86Val}
    (hmem : MemExtEq m₁ m₂) (op : X86Operand) :
    (evalX86Operand m₁ op = none ∧ evalX86Operand m₂ op = none) ∨
    ∃ v m₁' m₂',
      evalX86Operand m₁ op = some (v, m₁') ∧
      evalX86Operand m₂ op = some (v, m₂') ∧
      MemExtEq m₁' m₂' := by
  cases op with
  | stackSlot slot consume =>
    cases consume with
    | false =>
      dsimp [evalX86Operand]
      rw [← hmem slot.index]
      cases m₁ slot.index with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some v => exact Or.inr ⟨v, m₁, m₂, rfl, rfl, hmem⟩
    | true =>
      dsimp [evalX86Operand]
      rw [← hmem slot.index]
      cases m₁ slot.index with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some v =>
        exact Or.inr ⟨v,
          updateSlot m₁ slot.index none,
          updateSlot m₂ slot.index none,
          rfl, rfl, memExtEq_updateSlot hmem slot.index none⟩
  | imm v =>
    exact Or.inr ⟨v, m₁, m₂, rfl, rfl, hmem⟩

/-- Extensional memory congruence of `evalRepMovsb`. -/
theorem evalRepMovsb_extEq (tySizes : Nat → Nat)
    {m₁ m₂ : Nat → Option X86Val} (hmem : MemExtEq m₁ m₂)
    (srcTy dstTy : X86Ty) (ptrVal : X86Val) :
    evalRepMovsb tySizes m₁ srcTy dstTy ptrVal =
      evalRepMovsb tySizes m₂ srcTy dstTy ptrVal := by
  dsimp [evalRepMovsb]
  cases decide (evalX86TyByteSize tySizes srcTy = evalX86TyByteSize tySizes dstTy) with
  | false => rfl
  | true =>
    cases ptrVal with
    | stackPtr target =>
      dsimp only
      rw [hmem target.index]
    | _ => rfl

/-- Extensional state congruence of `evalX86Instr`: evaluating any `instr` on
    extensionally equal states `s₁` and `s₂` produces extensionally equal
    `StepResult`s. -/
theorem evalX86Instr_extEq {s₁ s₂ : X86State}
    (hs : StateExtEq s₁ s₂) (instr : X86Instr) :
    StepResultExtEq (evalX86Instr s₁ instr) (evalX86Instr s₂ instr) := by
  let ⟨hmem, hbb, hip, hty, hcur, hst⟩ := hs
  cases instr with
  | mov dst src =>
    dsimp [evalX86Instr]
    cases evalX86Operand_extEq hmem src with
    | inl hn =>
      rw [hn.1, hn.2]
      exact .failed .ub
    | inr hsome =>
      let ⟨v, m1', m2', h1, h2, hm'⟩ := hsome
      rw [h1, h2]
      exact .step ⟨memExtEq_updateSlot hm' dst.index (some v),
        hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
  | alu op dst lhs rhs =>
    dsimp [evalX86Instr]
    cases evalX86Operand_extEq hmem lhs with
    | inl hn =>
      rw [hn.1, hn.2]
      exact .failed .ub
    | inr hsome1 =>
      let ⟨v1, m1, m2, h1, h2, hm1⟩ := hsome1
      rw [h1, h2]
      dsimp only
      cases evalX86Operand_extEq hm1 rhs with
      | inl hn' =>
        rw [hn'.1, hn'.2]
        exact .failed .ub
      | inr hsome2 =>
        let ⟨v2, m1', m2', h1', h2', hm2⟩ := hsome2
        rw [h1', h2']
        dsimp only
        cases evalX86BinOp op v1 v2 with
        | none => exact .failed .ub
        | some outVal =>
          exact .step ⟨memExtEq_updateSlot hm2 dst.index (some outVal),
            hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
  | wrapAdt adtId dst src =>
    dsimp [evalX86Instr]
    cases evalX86Operand_extEq hmem src with
    | inl hn =>
      rw [hn.1, hn.2]
      exact .failed .ub
    | inr hsome =>
      let ⟨v, m1', m2', h1, h2, hm'⟩ := hsome
      rw [h1, h2]
      exact .step ⟨memExtEq_updateSlot hm' dst.index (some (.adt adtId v)),
        hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
  | extractField0 dst src =>
    dsimp [evalX86Instr]
    rw [← hmem src.index]
    cases s₁.mem src.index with
    | none => exact .failed .ub
    | some v =>
      cases v with
      | adt _ inner =>
        exact .step ⟨memExtEq_updateSlot hmem dst.index (some inner),
          hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
      | _ => exact .failed .ub
  | leaSlot dst target =>
    dsimp [evalX86Instr]
    rw [← hmem target.index]
    cases s₁.mem target.index with
    | none => exact .failed .ub
    | some _ =>
      exact .step ⟨memExtEq_updateSlot hmem dst.index (some (.stackPtr target)),
        hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
  | reborrowSlot dst srcPtr =>
    dsimp [evalX86Instr]
    rw [← hmem srcPtr.index]
    cases s₁.mem srcPtr.index with
    | none => exact .failed .ub
    | some v =>
      cases v with
      | stackPtr target =>
        dsimp only
        rw [← hmem target.index]
        cases s₁.mem target.index with
        | none => exact .failed .ub
        | some _ =>
          exact .step ⟨memExtEq_updateSlot hmem dst.index (some (.stackPtr target)),
            hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
      | _ => exact .failed .ub
  | allocSlot slot =>
    exact .step ⟨memExtEq_updateSlot hmem slot.index none,
      hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
  | deallocSlot slot =>
    exact .step ⟨memExtEq_updateSlot hmem slot.index none,
      hbb, congrArg (· + 1) hip, hty, hcur, hst⟩
  | nop =>
    exact .step ⟨hmem, hbb, congrArg (· + 1) hip, hty, hcur, hst⟩

/-- Extensional state congruence of `evalX86Term`: evaluating any `term` on
    extensionally equal states `s₁` and `s₂` produces extensionally equal
    `StepResult`s. -/
theorem evalX86Term_extEq {s₁ s₂ : X86State}
    (hs : StateExtEq s₁ s₂) (term : X86Term) :
    StepResultExtEq (evalX86Term s₁ term) (evalX86Term s₂ term) := by
  let ⟨hmem, hbb, _, hty, hcur, hst⟩ := hs
  cases term with
  | ret =>
    dsimp [evalX86Term]
    rw [← hmem 0]
    cases s₁.mem 0 with
    | none => exact .failed .ub
    | some retVal =>
      generalize hst1 : s₁.stack = st1 at hst
      generalize hst2 : s₂.stack = st2 at hst
      cases hst with
      | nil => exact .terminated (.normal retVal)
      | cons hf hrest =>
        let ⟨hf_body, hf_mem, hf_slot, hf_blk⟩ := hf
        refine .step ⟨?_, hf_blk, rfl, hty, hf_body, hrest⟩
        dsimp only
        rw [← hf_slot]
        exact memExtEq_updateSlot hf_mem _ (some retVal)
  | jmp target =>
    exact .step ⟨hmem, rfl, rfl, hty, hcur, hst⟩
  | ud2 =>
    exact .failed .ub
  | abortPanic =>
    exact .terminated .unwind
  | jccBool cond falseTarget trueTarget =>
    dsimp [evalX86Term]
    cases evalX86Operand_extEq hmem cond with
    | inl hn =>
      rw [hn.1, hn.2]
      exact .failed .ub
    | inr hsome =>
      let ⟨v, m1', m2', h1, h2, hm'⟩ := hsome
      rw [h1, h2]
      cases v with
      | boolVal b =>
        cases b with
        | false => exact .step ⟨hm', rfl, rfl, hty, hcur, hst⟩
        | true => exact .step ⟨hm', rfl, rfl, hty, hcur, hst⟩
      | _ => exact .failed .ub
  | movSizeOfJmp dst ty target =>
    dsimp [evalX86Term]
    have hsz : evalX86TyByteSize s₂.tySizes ty = evalX86TyByteSize s₁.tySizes ty := by
      rw [← hty]
    rw [hsz]
    exact .step ⟨memExtEq_updateSlot hmem dst.index
      (some (.word64 (evalX86TyByteSize s₁.tySizes ty))),
      rfl, rfl, hty, hcur, hst⟩
  | repMovsbJmp dst srcTy dstTy ptrOp target =>
    dsimp [evalX86Term]
    cases evalX86Operand_extEq hmem ptrOp with
    | inl hn =>
      rw [hn.1, hn.2]
      exact .failed .ub
    | inr hsome =>
      let ⟨ptrVal, m1', m2', h1, h2, hm'⟩ := hsome
      rw [h1, h2]
      dsimp only
      have hrep : evalRepMovsb s₂.tySizes m2' srcTy dstTy ptrVal =
          evalRepMovsb s₁.tySizes m1' srcTy dstTy ptrVal := by
        rw [← hty, evalRepMovsb_extEq s₁.tySizes hm' srcTy dstTy ptrVal]
      rw [hrep]
      cases evalRepMovsb s₁.tySizes m1' srcTy dstTy ptrVal with
      | none => exact .failed .ub
      | some outVal =>
        exact .step ⟨memExtEq_updateSlot hm' dst.index (some outVal),
          rfl, rfl, hty, hcur, hst⟩
  | call1 dst callee arg target =>
    dsimp [evalX86Term]
    cases evalX86Operand_extEq hmem arg with
    | inl hn =>
      rw [hn.1, hn.2]
      exact .failed .ub
    | inr hsome =>
      let ⟨argVal, m1', m2', h1, h2, hm'⟩ := hsome
      rw [h1, h2]
      exact .step ⟨memExtEq_refl _, rfl, rfl, hty, rfl,
        .cons ⟨hcur, hm', rfl, rfl⟩ hst⟩

/-- Extensional state congruence of `evalX86Step`. -/
theorem evalX86Step_extEq (rootBody : X86Body) {s₁ s₂ : X86State}
    (hs : StateExtEq s₁ s₂) :
    StepResultExtEq (evalX86Step rootBody s₁) (evalX86Step rootBody s₂) := by
  dsimp [evalX86Step]
  rw [← hs.2.2.2.2.1, ← hs.2.1]
  cases (s₁.curBody.getD rootBody).blocks[s₁.bb]? with
  | none => exact .failed .ub
  | some blk =>
    dsimp only
    rw [← hs.2.2.1]
    cases blk.instrs[s₁.ip]? with
    | some instr => exact evalX86Instr_extEq hs instr
    | none => exact evalX86Term_extEq hs blk.term

/-- Multi-step `ReachesPrefix` congruence under `StateExtEq`: extensionally
    equal states `s₁` and `s₂` reach the exact same `(tr, out)` prefixes for
    every fuel budget `n : Nat`. -/
theorem reachesPrefix_extEq (rootBody : X86Body) (init₁ init₂ : X86State) :
    ∀ (n : Nat) {s₁ s₂ : X86State} (tr : List Unit) (out : PrefixOutcome X86Val),
      StateExtEq s₁ s₂ →
      ReachesPrefix X86Machine rootBody init₁ n s₁ tr out →
      ReachesPrefix X86Machine rootBody init₂ n s₂ tr out
  | 0, _, s₂, _, _, _, hr => by
    cases hr with
    | zero => exact .zero s₂
  | n + 1, s₁, s₂, tr, out, hs, hr => by
    have hstep_ext := evalX86Step_extEq rootBody hs
    cases hr with
    | step _ _ s₁' obs tr' _ hst hr' =>
      have hst_eq : StepResult.step obs s₁' = evalX86Step rootBody s₁ := hst
      rw [← hst_eq] at hstep_ext
      generalize hres₂ : evalX86Step rootBody s₂ = res₂ at hstep_ext
      cases hstep_ext with
      | step hs' =>
        exact .step n s₂ _ () tr' out hres₂.symm
          (reachesPrefix_extEq rootBody init₁ init₂ n tr' out hs' hr')
    | choice _ kind _ _ branches _ _ hst =>
      have hst_eq : StepResult.choice kind branches = evalX86Step rootBody s₁ := hst
      rw [← hst_eq] at hstep_ext
      cases hstep_ext
    | emptyChoice _ kind _ branches hst =>
      have hst_eq : StepResult.choice kind branches = evalX86Step rootBody s₁ := hst
      rw [← hst_eq] at hstep_ext
      cases hstep_ext
    | terminated _ _ term hst =>
      have hst_eq : StepResult.terminated term = evalX86Step rootBody s₁ := hst
      rw [← hst_eq] at hstep_ext
      generalize hres₂ : evalX86Step rootBody s₂ = res₂ at hstep_ext
      cases hstep_ext with
      | terminated => exact .terminated n s₂ term hres₂.symm
    | failed _ _ fk hst =>
      have hst_eq : StepResult.failed fk = evalX86Step rootBody s₁ := hst
      rw [← hst_eq] at hstep_ext
      generalize hres₂ : evalX86Step rootBody s₂ = res₂ at hstep_ext
      cases hstep_ext with
      | failed => exact .failed n s₂ fk hres₂.symm
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, rfl⟩)

/-- Symmetry of `StepResultExtEq`. -/
theorem stepResultExtEq_symm {r₁ r₂ : StepResult X86State Unit X86Val}
    (h : StepResultExtEq r₁ r₂) : StepResultExtEq r₂ r₁ := by
  cases h with
  | step hs => exact .step (stateExtEq_symm hs)
  | terminated term => exact .terminated term
  | failed fk => exact .failed fk

/-- Transitivity of `StepResultExtEq`. -/
theorem stepResultExtEq_trans {r₁ r₂ r₃ : StepResult X86State Unit X86Val}
    (h₁₂ : StepResultExtEq r₁ r₂) (h₂₃ : StepResultExtEq r₂ r₃) :
    StepResultExtEq r₁ r₃ := by
  cases h₁₂ with
  | step hs₁₂ =>
    cases h₂₃ with
    | step hs₂₃ => exact .step (stateExtEq_trans hs₁₂ hs₂₃)
  | terminated term =>
    cases h₂₃ with
    | terminated => exact .terminated term
  | failed fk =>
    cases h₂₃ with
    | failed => exact .failed fk

/-- Full behavioral congruence of `X86Sem` under `StateExtEq`: if `StateExtEq s₁ s₂`,
    then for every step budget `n : Nat`, `(X86Sem body ⟨s₁, n⟩)` and
    `(X86Sem body ⟨s₂, n⟩)` have equivalent `defined` and `val` predicates. -/
theorem x86Sem_extEq (body : X86Body) {s₁ s₂ : X86State}
    (hs : StateExtEq s₁ s₂) (n : Nat) :
    ((X86Sem body ⟨s₁, n⟩).defined ↔ (X86Sem body ⟨s₂, n⟩).defined) ∧
    ∀ (h₁ : (X86Sem body ⟨s₁, n⟩).defined)
      (h₂ : (X86Sem body ⟨s₂, n⟩).defined)
      (out : ExecOut Unit X86Val),
      (X86Sem body ⟨s₁, n⟩).val h₁ out ↔ (X86Sem body ⟨s₂, n⟩).val h₂ out := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hdef₁ hinit₂ tr out hr₂
      have hinit₁ := (initX86State_extEq body hs).mpr hinit₂
      have hr₁ := reachesPrefix_extEq body s₂ s₁ n tr out (stateExtEq_symm hs) hr₂
      exact hdef₁ hinit₁ tr out hr₁
    · intro hdef₂ hinit₁ tr out hr₁
      have hinit₂ := (initX86State_extEq body hs).mp hinit₁
      have hr₂ := reachesPrefix_extEq body s₁ s₂ n tr out hs hr₁
      exact hdef₂ hinit₂ tr out hr₂
  · intro _ _ out
    constructor
    · intro hval₁
      exact ⟨(initX86State_extEq body hs).mp hval₁.1,
        reachesPrefix_extEq body s₁ s₂ n out.trace out.outcome hs hval₁.2⟩
    · intro hval₂
      exact ⟨(initX86State_extEq body hs).mpr hval₂.1,
        reachesPrefix_extEq body s₂ s₁ n out.trace out.outcome
          (stateExtEq_symm hs) hval₂.2⟩

/-!
## 2. Unified Multi-Step Peephole Simulation Engine (`mapBodyInstrs`, `SimPass`, `StepSimOutcome`)

Rather than duplicating basic-block lookup, terminator simulation, stack-frame
mapping, and `ReachesPrefix` induction across every compiler pass, we factor
them into a single parametric engine over any instruction-list transformer
`fInstrs : List X86Instr → List X86Instr`.
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

mutual
  noncomputable def mapTermInstrs (fInstrs : List X86Instr → List X86Instr) :
      X86Term → X86Term
    | .call1 dst callee arg target =>
      .call1 dst (mapBodyInstrs fInstrs callee) arg target
    | term => term

  noncomputable def mapBlockInstrs (fInstrs : List X86Instr → List X86Instr)
      (blk : X86Block) : X86Block :=
    match blk with
    | ⟨instrs, term⟩ => {
        instrs := fInstrs instrs
        term := mapTermInstrs fInstrs term
      }

  noncomputable def mapBlockListInstrs (fInstrs : List X86Instr → List X86Instr) :
      List X86Block → List X86Block
    | [] => []
    | blk :: rest => mapBlockInstrs fInstrs blk :: mapBlockListInstrs fInstrs rest

  noncomputable def mapBodyInstrs (fInstrs : List X86Instr → List X86Instr)
      (body : X86Body) : X86Body :=
    match body with
    | ⟨argTys, retTy, slotCount, blocks, requiredConsts⟩ => {
        argTys := argTys
        retTy := retTy
        slotCount := slotCount
        blocks := mapBlockListInstrs fInstrs blocks
        requiredConsts := requiredConsts
      }
end

theorem mapBlockListInstrs_getElem? (fInstrs : List X86Instr → List X86Instr)
    (bbs : List X86Block) (idx : Nat) :
    (mapBlockListInstrs fInstrs bbs)[idx]? =
      (bbs[idx]?).map (mapBlockInstrs fInstrs) := by
  induction bbs generalizing idx with
  | nil => rfl
  | cons bb rest ih =>
    cases idx with
    | zero => rfl
    | succ k => exact ih k

theorem blocks_mapBodyInstrs (fInstrs : List X86Instr → List X86Instr)
    (body : X86Body) :
    (mapBodyInstrs fInstrs body).blocks =
      mapBlockListInstrs fInstrs body.blocks := by
  cases body
  rfl

theorem initX86State_mapBodyInstrs (fInstrs : List X86Instr → List X86Instr)
    (body : X86Body) (s : X86State) :
    initX86State (mapBodyInstrs fInstrs body) s ↔ initX86State body s := by
  cases body
  rfl

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

theorem evalX86Term_mapTermInstrs (fInstrs : List X86Instr → List X86Instr)
    (s : X86State) (ip_tgt : Nat) (term : X86Term) :
    evalX86Term { mapX86State (mapBodyInstrs fInstrs) s with ip := ip_tgt }
      (mapTermInstrs fInstrs term) =
      mapStepState (mapX86State (mapBodyInstrs fInstrs)) (evalX86Term s term) := by
  cases term with
  | ret =>
    dsimp [mapTermInstrs, evalX86Term, mapX86State]
    cases s.mem 0 with
    | none => rfl
    | some retVal =>
      cases s.stack <;> rfl
  | jmp _ => rfl
  | ud2 => rfl
  | abortPanic => rfl
  | jccBool cond _ _ =>
    dsimp [mapTermInstrs, evalX86Term, mapX86State]
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
    dsimp [mapTermInstrs, evalX86Term, mapX86State]
    cases evalX86Operand s.mem ptrOp with
    | none => rfl
    | some p =>
      cases p with
      | mk ptrVal mem' =>
        dsimp only
        cases evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal <;> rfl
  | call1 _ _ arg _ =>
    dsimp [mapTermInstrs, evalX86Term, mapX86State]
    cases evalX86Operand s.mem arg <;> rfl

/-- Extensional state simulation relation between target state `s_tgt` (running
    `mapBodyInstrs fInstrs root`) and source state `s_src` (running `root`):
    `s_tgt` is extensionally equal (`StateExtEq`) to
    `{ mapX86State (mapBodyInstrs fInstrs) s_src with ip := s_tgt.ip }`. -/
def SimState (fBody : X86Body → X86Body) (s_tgt s_src : X86State) : Prop :=
  StateExtEq s_tgt { mapX86State fBody s_src with ip := s_tgt.ip }

/-- Full block-suffix and extensional-memory simulation relation for a pass
    `mapBodyInstrs fInstrs`. -/
def SimPass (fInstrs : List X86Instr → List X86Instr) (root : X86Body)
    (s_tgt s_src : X86State) : Prop :=
  SimState (mapBodyInstrs fInstrs) s_tgt s_src ∧
  ∀ blk_src,
    (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src →
    (mapBlockInstrs fInstrs blk_src).instrs.drop s_tgt.ip =
      fInstrs (blk_src.instrs.drop s_src.ip)

theorem simPass_of_stateExtEq_ip_zero (fInstrs : List X86Instr → List X86Instr)
    (root : X86Body) {s_tgt s_src : X86State}
    (hst : StateExtEq s_tgt (mapX86State (mapBodyInstrs fInstrs) s_src))
    (hip : s_src.ip = 0) :
    SimPass fInstrs root s_tgt s_src := by
  have hip_map : (mapX86State (mapBodyInstrs fInstrs) s_src).ip = 0 := hip
  have hip_tgt : s_tgt.ip = 0 := Eq.trans hst.2.2.1 hip_map
  refine ⟨?_, ?_⟩
  · refine ⟨hst.1, hst.2.1, rfl, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2⟩
  · intro blk_src _
    rw [hip_tgt, hip]
    cases blk_src
    rfl

theorem curBody_getD_of_simState (fInstrs : List X86Instr → List X86Instr)
    (root : X86Body) {s_tgt s_src : X86State}
    (hsim : SimState (mapBodyInstrs fInstrs) s_tgt s_src) :
    s_tgt.curBody.getD (mapBodyInstrs fInstrs root) =
      mapBodyInstrs fInstrs (s_src.curBody.getD root) := by
  have hcur := hsim.2.2.2.2.1
  dsimp [mapX86State] at hcur
  rw [hcur]
  cases s_src.curBody <;> rfl

theorem target_block_none_of_simState (fInstrs : List X86Instr → List X86Instr)
    (root : X86Body) {s_tgt s_src : X86State}
    (hsim : SimState (mapBodyInstrs fInstrs) s_tgt s_src)
    (hblk : (s_src.curBody.getD root).blocks[s_src.bb]? = none) :
    (s_tgt.curBody.getD (mapBodyInstrs fInstrs root)).blocks[s_tgt.bb]? = none := by
  rw [curBody_getD_of_simState fInstrs root hsim,
      blocks_mapBodyInstrs]
  have hbb : s_tgt.bb = s_src.bb := hsim.2.1
  rw [hbb, mapBlockListInstrs_getElem?, hblk]
  rfl

theorem target_block_some_of_simState (fInstrs : List X86Instr → List X86Instr)
    (root : X86Body) {s_tgt s_src : X86State} {blk_src : X86Block}
    (hsim : SimState (mapBodyInstrs fInstrs) s_tgt s_src)
    (hblk : (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src) :
    (s_tgt.curBody.getD (mapBodyInstrs fInstrs root)).blocks[s_tgt.bb]? =
      some (mapBlockInstrs fInstrs blk_src) := by
  rw [curBody_getD_of_simState fInstrs root hsim,
      blocks_mapBodyInstrs]
  have hbb : s_tgt.bb = s_src.bb := hsim.2.1
  rw [hbb, mapBlockListInstrs_getElem?, hblk]
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

/-- Three-way step-simulation outcome for a state relation `R` between target
    state `s_tgt` (running `tgtBody`) and source state `s_src` (running `srcBody`):
    1. 1-step target termination matched by `k + 1` source steps,
    2. 1-step target failure matched by `k + 1` source steps, or
    3. 1-step target transition matched by `k + 1` source steps restoring `R`. -/
def StepSimOutcome (R : X86State → X86State → Prop)
    (tgtBody srcBody : X86Body) (init s_tgt s_src : X86State) : Prop :=
  (∃ term,
    evalX86Step tgtBody s_tgt = .terminated term ∧
    ∃ k, ∀ m,
      ReachesPrefix X86Machine srcBody init (m + k + 1) s_src
        (List.replicate k ()) (.terminated term)) ∨
  (∃ fk,
    evalX86Step tgtBody s_tgt = .failed fk ∧
    ∃ k, ∀ m,
      ReachesPrefix X86Machine srcBody init (m + k + 1) s_src
        (List.replicate k ()) (.failed fk)) ∨
  (∃ s_tgt' s_src' k,
    evalX86Step tgtBody s_tgt = .step () s_tgt' ∧
    R s_tgt' s_src' ∧
    ∀ n tr out,
      ReachesPrefix X86Machine srcBody init n s_src' tr out →
      ReachesPrefix X86Machine srcBody init (n + k + 1) s_src
        (List.replicate (k + 1) () ++ tr) out)

/-- Reusable `StepSimOutcome` constructor when `(s_src.curBody.getD root).blocks[s_src.bb]? = none`. -/
theorem stepSim_of_block_none (fInstrs : List X86Instr → List X86Instr)
    (R : X86State → X86State → Prop)
    (root : X86Body) (init s_tgt s_src : X86State)
    (hsim : SimState (mapBodyInstrs fInstrs) s_tgt s_src)
    (hblk : (s_src.curBody.getD root).blocks[s_src.bb]? = none) :
    StepSimOutcome R (mapBodyInstrs fInstrs root) root init s_tgt s_src := by
  have hblk_tgt := target_block_none_of_simState fInstrs root hsim hblk
  exact Or.inr (Or.inl ⟨.ub,
    evalX86Step_of_block_none (mapBodyInstrs fInstrs root) s_tgt hblk_tgt,
    0, fun m => ReachesPrefix.failed m s_src .ub
      (evalX86Step_of_block_none root s_src hblk).symm⟩)

/-- Reusable `StepSimOutcome` constructor at a block terminator (`rem_src = []`). -/
theorem stepSim_of_term (fInstrs : List X86Instr → List X86Instr)
    (R : X86State → X86State → Prop) (root : X86Body)
    (hR : ∀ {s_tgt' s_src'}, SimPass fInstrs root s_tgt' s_src' → R s_tgt' s_src')
    (init s_tgt s_src : X86State) (blk_src : X86Block)
    (hsim : SimState (mapBodyInstrs fInstrs) s_tgt s_src)
    (hblk : (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src)
    (hdrop_src : blk_src.instrs.drop s_src.ip = [])
    (hdrop_tgt : (mapBlockInstrs fInstrs blk_src).instrs.drop s_tgt.ip = []) :
    StepSimOutcome R (mapBodyInstrs fInstrs root) root init s_tgt s_src := by
  have hip_src : blk_src.instrs[s_src.ip]? = none :=
    getElem?_of_drop_eq_nil blk_src.instrs s_src.ip hdrop_src
  have hip_tgt : (mapBlockInstrs fInstrs blk_src).instrs[s_tgt.ip]? = none :=
    getElem?_of_drop_eq_nil (mapBlockInstrs fInstrs blk_src).instrs s_tgt.ip hdrop_tgt
  have hblk_tgt := target_block_some_of_simState fInstrs root hsim hblk
  have hstep_src : evalX86Step root s_src = evalX86Term s_src blk_src.term :=
    evalX86Step_of_instr_none root s_src blk_src hblk hip_src
  have hstep_tgt_eq :
      evalX86Step (mapBodyInstrs fInstrs root) s_tgt =
        evalX86Term s_tgt (mapTermInstrs fInstrs blk_src.term) := by
    rw [evalX86Step_of_instr_none (mapBodyInstrs fInstrs root) s_tgt
      (mapBlockInstrs fInstrs blk_src) hblk_tgt hip_tgt]
    have hterm_eq :
        (mapBlockInstrs fInstrs blk_src).term =
          mapTermInstrs fInstrs blk_src.term := by
      cases blk_src; rfl
    rw [hterm_eq]
  have hext := evalX86Term_extEq hsim (mapTermInstrs fInstrs blk_src.term)
  rw [evalX86Term_mapTermInstrs fInstrs s_src s_tgt.ip blk_src.term] at hext
  cases hterm_res : evalX86Term s_src blk_src.term with
  | terminated term =>
    rw [hterm_res] at hext hstep_src
    dsimp [mapStepState] at hext
    generalize hres_tgt : evalX86Term s_tgt (mapTermInstrs fInstrs blk_src.term) = res_tgt at hext
    cases hext with
    | terminated =>
      rw [hres_tgt] at hstep_tgt_eq
      exact Or.inl ⟨term, hstep_tgt_eq, 0,
        fun m => ReachesPrefix.terminated m s_src term hstep_src.symm⟩
  | failed fk =>
    rw [hterm_res] at hext hstep_src
    dsimp [mapStepState] at hext
    generalize hres_tgt : evalX86Term s_tgt (mapTermInstrs fInstrs blk_src.term) = res_tgt at hext
    cases hext with
    | failed =>
      rw [hres_tgt] at hstep_tgt_eq
      exact Or.inr (Or.inl ⟨fk, hstep_tgt_eq, 0,
        fun m => ReachesPrefix.failed m s_src fk hstep_src.symm⟩)
  | step obs s_src' =>
    cases obs
    have hip_zero : s_src'.ip = 0 :=
      evalX86Term_step_ip_zero s_src s_src' blk_src.term hterm_res
    rw [hterm_res] at hext hstep_src
    dsimp [mapStepState] at hext
    generalize hres_tgt : evalX86Term s_tgt (mapTermInstrs fInstrs blk_src.term) = res_tgt at hext
    cases hext with
    | step hst' =>
      rw [hres_tgt] at hstep_tgt_eq
      exact Or.inr (Or.inr ⟨_, s_src', 0, hstep_tgt_eq,
        hR (simPass_of_stateExtEq_ip_zero fInstrs root hst' hip_zero),
        fun n tr out hr =>
          ReachesPrefix.step n s_src s_src' () tr out hstep_src.symm hr⟩)
  | choice kind branches =>
    exact False.elim (evalX86Term_not_choice s_src blk_src.term kind branches hterm_res)

/-- Reusable `StepSimOutcome` constructor for any passthrough instruction `instr`
    where both source and target execute `instr` in 1 step. -/
theorem stepSim_of_passthrough_instr (fInstrs : List X86Instr → List X86Instr)
    (R : X86State → X86State → Prop) (root : X86Body)
    (hR : ∀ {s_tgt' s_src'}, SimPass fInstrs root s_tgt' s_src' → R s_tgt' s_src')
    (init s_tgt s_src : X86State) (blk_src : X86Block)
    (instr : X86Instr) (rest : List X86Instr)
    (hsim : SimState (mapBodyInstrs fInstrs) s_tgt s_src)
    (hblk : (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src)
    (hdrop_src : blk_src.instrs.drop s_src.ip = instr :: rest)
    (hdrop_tgt :
      (mapBlockInstrs fInstrs blk_src).instrs.drop s_tgt.ip =
        instr :: fInstrs rest) :
    StepSimOutcome R (mapBodyInstrs fInstrs root) root init s_tgt s_src := by
  have hip_src : blk_src.instrs[s_src.ip]? = some instr :=
    getElem?_of_drop_eq_cons blk_src.instrs s_src.ip instr rest hdrop_src
  have hdrop_src_next : blk_src.instrs.drop (s_src.ip + 1) = rest :=
    drop_succ_of_drop_eq_cons blk_src.instrs s_src.ip instr rest hdrop_src
  have hip_tgt : (mapBlockInstrs fInstrs blk_src).instrs[s_tgt.ip]? = some instr :=
    getElem?_of_drop_eq_cons (mapBlockInstrs fInstrs blk_src).instrs
      s_tgt.ip instr (fInstrs rest) hdrop_tgt
  have hdrop_tgt_next :
      (mapBlockInstrs fInstrs blk_src).instrs.drop (s_tgt.ip + 1) =
        fInstrs rest :=
    drop_succ_of_drop_eq_cons (mapBlockInstrs fInstrs blk_src).instrs
      s_tgt.ip instr (fInstrs rest) hdrop_tgt
  have hblk_tgt := target_block_some_of_simState fInstrs root hsim hblk
  have hstep_src : evalX86Step root s_src = evalX86Instr s_src instr :=
    evalX86Step_of_instr_some root s_src blk_src instr hblk hip_src
  have hstep_tgt_eq :
      evalX86Step (mapBodyInstrs fInstrs root) s_tgt =
        evalX86Instr s_tgt instr :=
    evalX86Step_of_instr_some (mapBodyInstrs fInstrs root) s_tgt
      (mapBlockInstrs fInstrs blk_src) instr hblk_tgt hip_tgt
  have hext := evalX86Instr_extEq hsim instr
  rw [evalX86Instr_mapX86State (mapBodyInstrs fInstrs) s_src s_tgt.ip instr] at hext
  cases evalX86Instr_cases s_src instr with
  | inl hinstr_fail =>
    rw [hinstr_fail] at hext hstep_src
    dsimp [mapStepState] at hext
    generalize hres_tgt : evalX86Instr s_tgt instr = res_tgt at hext
    cases hext with
    | failed =>
      rw [hres_tgt] at hstep_tgt_eq
      exact Or.inr (Or.inl ⟨.ub, hstep_tgt_eq, 0,
        fun m => ReachesPrefix.failed m s_src .ub hstep_src.symm⟩)
  | inr hsome =>
    let ⟨mem', hinstr_step⟩ := hsome
    rw [hinstr_step] at hext hstep_src
    dsimp [mapStepState] at hext
    generalize hres_tgt : evalX86Instr s_tgt instr = res_tgt at hext
    cases hext with
    | step hst' =>
      rw [hres_tgt] at hstep_tgt_eq
      let s_src' : X86State := { s_src with mem := mem', ip := s_src.ip + 1 }
      refine Or.inr (Or.inr ⟨_, s_src', 0, hstep_tgt_eq, hR ?_, ?_⟩)
      · refine ⟨?_, ?_⟩
        · refine ⟨hst'.1, hst'.2.1, rfl, hst'.2.2.2.1, hst'.2.2.2.2.1, hst'.2.2.2.2.2⟩
        · intro b hb
          dsimp [s_src'] at hb
          rw [hblk] at hb
          injection hb with hb_eq
          subst hb_eq
          dsimp [s_src']
          rw [hst'.2.2.1, hdrop_tgt_next, hdrop_src_next]
      · intro n tr out hr
        exact ReachesPrefix.step n s_src s_src' () tr out hstep_src.symm hr

/-- Multi-step variable-step backward simulation along any relational invariant
    `R` satisfying `StepSimOutcome`. -/
theorem reachesPrefix_of_stepSim
    (R : X86State → X86State → Prop)
    (tgtBody srcBody : X86Body) (init : X86State)
    (hstepSim : ∀ s_tgt s_src,
      R s_tgt s_src →
      StepSimOutcome R tgtBody srcBody init s_tgt s_src)
    {n_tgt : Nat} {s_tgt : X86State} {tr_tgt : List Unit}
    {out : PrefixOutcome X86Val}
    (hr_tgt : ReachesPrefix X86Machine tgtBody init n_tgt s_tgt tr_tgt out) :
    ∀ {s_src : X86State},
      R s_tgt s_src →
      ∃ n_src tr_src,
        n_tgt ≤ n_src ∧
        ReachesPrefix X86Machine srcBody init n_src s_src tr_src out := by
  induction hr_tgt with
  | zero s_tgt =>
    intro s_src _
    exact ⟨0, [], Nat.le_refl 0, ReachesPrefix.zero s_src⟩
  | terminated m s_tgt term hstep_tgt =>
    intro s_src hR
    cases hstepSim s_tgt s_src hR with
    | inl hterm =>
      let ⟨term', hstep_tgt', k, hreach⟩ := hterm
      have heq : StepResult.terminated term = StepResult.terminated term' :=
        Eq.trans hstep_tgt hstep_tgt'
      injection heq with hterm_eq
      subst hterm_eq
      refine ⟨m + k + 1, List.replicate k (), ?_, hreach m⟩
      have hle : m ≤ m + k := Nat.le_add_right m k
      exact Nat.succ_le_succ hle
    | inr hrest =>
      cases hrest with
      | inl hfail =>
        let ⟨_, hstep_tgt', _⟩ := hfail
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
      | inr hstep =>
        let ⟨_, _, _, hstep_tgt', _⟩ := hstep
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
  | failed m s_tgt fk hstep_tgt =>
    intro s_src hR
    cases hstepSim s_tgt s_src hR with
    | inl hterm =>
      let ⟨_, hstep_tgt', _⟩ := hterm
      have hcontra := Eq.trans hstep_tgt hstep_tgt'
      cases hcontra
    | inr hrest =>
      cases hrest with
      | inl hfail =>
        let ⟨fk', hstep_tgt', k, hreach⟩ := hfail
        have heq : StepResult.failed fk = StepResult.failed fk' :=
          Eq.trans hstep_tgt hstep_tgt'
        injection heq with hfk_eq
        subst hfk_eq
        refine ⟨m + k + 1, List.replicate k (), ?_, hreach m⟩
        have hle : m ≤ m + k := Nat.le_add_right m k
        exact Nat.succ_le_succ hle
      | inr hstep =>
        let ⟨_, _, _, hstep_tgt', _⟩ := hstep
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
  | step n s_tgt s_tgt_next obs tr_rest out hstep_tgt hr_rest ih =>
    intro s_src hR
    cases hstepSim s_tgt s_src hR with
    | inl hterm =>
      let ⟨_, hstep_tgt', _⟩ := hterm
      have hcontra := Eq.trans hstep_tgt hstep_tgt'
      cases hcontra
    | inr hrest =>
      cases hrest with
      | inl hfail =>
        let ⟨_, hstep_tgt', _⟩ := hfail
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
      | inr hstep =>
        let ⟨s_tgt', s_src', k, hstep_tgt', hR', hprepend⟩ := hstep
        have heq : StepResult.step obs s_tgt_next = StepResult.step () s_tgt' :=
          Eq.trans hstep_tgt hstep_tgt'
        injection heq with _ hs_eq
        subst hs_eq
        let ⟨n_src, tr_src, hle, hr_src⟩ := ih hR'
        refine ⟨n_src + k + 1, List.replicate (k + 1) () ++ tr_src, ?_,
          hprepend n_src tr_src out hr_src⟩
        have hle1 : n ≤ n_src + k :=
          Nat.le_trans hle (Nat.le_add_right n_src k)
        exact Nat.succ_le_succ hle1
  | choice n kind s_tgt s_tgt_next branches tr_rest out hstep_tgt _ _ _ =>
    intro s_src hR
    cases hstepSim s_tgt s_src hR with
    | inl hterm =>
      let ⟨_, hstep_tgt', _⟩ := hterm
      have hcontra := Eq.trans hstep_tgt hstep_tgt'
      cases hcontra
    | inr hrest =>
      cases hrest with
      | inl hfail =>
        let ⟨_, hstep_tgt', _⟩ := hfail
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
      | inr hstep =>
        let ⟨_, _, _, hstep_tgt', _⟩ := hstep
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
  | emptyChoice n kind s_tgt branches hstep_tgt _ =>
    intro s_src hR
    cases hstepSim s_tgt s_src hR with
    | inl hterm =>
      let ⟨_, hstep_tgt', _⟩ := hterm
      have hcontra := Eq.trans hstep_tgt hstep_tgt'
      cases hcontra
    | inr hrest =>
      cases hrest with
      | inl hfail =>
        let ⟨_, hstep_tgt', _⟩ := hfail
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
      | inr hstep =>
        let ⟨_, _, _, hstep_tgt', _⟩ := hstep
        have hcontra := Eq.trans hstep_tgt hstep_tgt'
        cases hcontra
  | noStep n s_tgt hnostep =>
    intro _ _
    exact False.elim (hnostep ⟨evalX86Step tgtBody s_tgt, rfl⟩)

theorem initial_simPass (fInstrs : List X86Instr → List X86Instr)
    (root : X86Body) (s : X86State)
    (hinit : initX86State (mapBodyInstrs fInstrs root) s) :
    initX86State root s ∧ SimPass fInstrs root s s := by
  have hinit_src : initX86State root s :=
    (initX86State_mapBodyInstrs fInstrs root s).mp hinit
  have hip_zero : s.ip = 0 := hinit_src.2.1
  have hcur_none : s.curBody = none := hinit_src.2.2.1
  have hstack_nil : s.stack = [] := hinit_src.2.2.2.1
  have hst : StateExtEq s (mapX86State (mapBodyInstrs fInstrs) s) := by
    refine ⟨memExtEq_refl s.mem, rfl, rfl, rfl, ?_, ?_⟩
    · dsimp [mapX86State]; rw [hcur_none]; rfl
    · dsimp [mapX86State]; rw [hstack_nil]; exact StackExtEq.nil
  exact ⟨hinit_src, simPass_of_stateExtEq_ip_zero fInstrs root hst hip_zero⟩

/-- Generic `Compiles X86Lang X86Lang π_x86_opt` wrapper for any instruction-list
    pass `mapBodyInstrs fInstrs` equipped with a step simulation invariant `R`. -/
theorem compiles_opt_of_stepSim (fInstrs : List X86Instr → List X86Instr)
    (R : X86Body → X86State → X86State → Prop)
    (hR : ∀ root {s_tgt s_src}, SimPass fInstrs root s_tgt s_src → R root s_tgt s_src)
    (hstepSim : ∀ root init s_tgt s_src,
      R root s_tgt s_src →
      StepSimOutcome (R root) (mapBodyInstrs fInstrs root) root init s_tgt s_src)
    (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_opt body (mapBodyInstrs fInstrs body) := by
  intro q hdef_src
  refine ⟨?_, ?_⟩
  · intro hinit_tgt tr_tgt out hr_tgt
    let ⟨hinit_src, hsim₀⟩ := initial_simPass fInstrs body q.init hinit_tgt
    let ⟨n_src, tr_src, _, hr_src⟩ :=
      reachesPrefix_of_stepSim (R body) (mapBodyInstrs fInstrs body) body q.init
        (hstepSim body q.init) hr_tgt (hR body hsim₀)
    exact hdef_src n_src hinit_src tr_src out hr_src
  · intro out hout
    let ⟨hinit_tgt, hr_tgt⟩ := hout
    let ⟨hinit_src, hsim₀⟩ := initial_simPass fInstrs body q.init hinit_tgt
    let ⟨n_src, tr_src, hle, hr_src⟩ :=
      reachesPrefix_of_stepSim (R body) (mapBodyInstrs fInstrs body) body q.init
        (hstepSim body q.init) hr_tgt (hR body hsim₀)
    exact ⟨n_src, tr_src, hle, hinit_src, hr_src⟩


/-! ## Section 3: Pass 1 — Dead Store + Dealloc Elimination (`elimDeadStoreDealloc`)

Eliminates dead immediate stores immediately followed by deallocation of the
same slot:
  `.mov tmp (.imm v) :: .deallocSlot d :: rest` (when `tmp.index == d.index`)
  `↦ .deallocSlot d :: elimDeadStoreDeallocInstrs rest`

During the 2-to-1 macro-step, the source first executes `.mov tmp (.imm v)` to
reach an intermediate state `s_src₁` whose memory differs from `s_tgt.mem` on
`d.index` (`MemAgreesExcept d.index s_tgt.mem s_src₁.mem`). Both machines then
execute `.deallocSlot d`, which overwrites `d.index` with `none` and reconverges
`MemAgreesExcept d.index` to full `MemExtEq` via
`memExtEq_of_memAgreesExcept_updateSlot` without `funext`. -/

noncomputable def elimDeadStoreDeallocInstrs : List X86Instr → List X86Instr
  | [] => []
  | .mov tmp (.imm v) :: .deallocSlot d :: rest' =>
    if tmp.index == d.index then
      .deallocSlot d :: elimDeadStoreDeallocInstrs rest'
    else
      .mov tmp (.imm v) :: .deallocSlot d :: elimDeadStoreDeallocInstrs rest'
  | instr :: rest => instr :: elimDeadStoreDeallocInstrs rest

noncomputable def elimDeadStoreDealloc (body : X86Body) : X86Body :=
  mapBodyInstrs elimDeadStoreDeallocInstrs body

theorem stepSim_elimDeadStoreDealloc_matched
    (root : X86Body) (init s_tgt s_src : X86State) (blk_src : X86Block)
    (tmp d : SlotId) (v : X86Val) (rest' : List X86Instr)
    (hsim : SimState elimDeadStoreDealloc s_tgt s_src)
    (hblk : (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src)
    (hdrop_src :
      blk_src.instrs.drop s_src.ip =
        .mov tmp (.imm v) :: .deallocSlot d :: rest')
    (hdrop_tgt :
      (mapBlockInstrs elimDeadStoreDeallocInstrs blk_src).instrs.drop s_tgt.ip =
        .deallocSlot d :: elimDeadStoreDeallocInstrs rest')
    (hd : tmp.index = d.index) :
    StepSimOutcome (SimPass elimDeadStoreDeallocInstrs root)
      (elimDeadStoreDealloc root) root init s_tgt s_src := by
  have hip_src₀ : blk_src.instrs[s_src.ip]? = some (.mov tmp (.imm v)) :=
    getElem?_of_drop_eq_cons blk_src.instrs s_src.ip
      (.mov tmp (.imm v)) (.deallocSlot d :: rest') hdrop_src
  have hdrop_src₁ :
      blk_src.instrs.drop (s_src.ip + 1) = .deallocSlot d :: rest' :=
    drop_succ_of_drop_eq_cons blk_src.instrs s_src.ip
      (.mov tmp (.imm v)) (.deallocSlot d :: rest') hdrop_src
  have hip_src₁ : blk_src.instrs[s_src.ip + 1]? = some (.deallocSlot d) :=
    getElem?_of_drop_eq_cons blk_src.instrs (s_src.ip + 1)
      (.deallocSlot d) rest' hdrop_src₁
  have hdrop_src₂ : blk_src.instrs.drop (s_src.ip + 1 + 1) = rest' :=
    drop_succ_of_drop_eq_cons blk_src.instrs (s_src.ip + 1)
      (.deallocSlot d) rest' hdrop_src₁
  have hip_tgt :
      (mapBlockInstrs elimDeadStoreDeallocInstrs blk_src).instrs[s_tgt.ip]? =
        some (.deallocSlot d) :=
    getElem?_of_drop_eq_cons
      (mapBlockInstrs elimDeadStoreDeallocInstrs blk_src).instrs
      s_tgt.ip (.deallocSlot d) (elimDeadStoreDeallocInstrs rest') hdrop_tgt
  have hdrop_tgt₁ :
      (mapBlockInstrs elimDeadStoreDeallocInstrs blk_src).instrs.drop
        (s_tgt.ip + 1) =
        elimDeadStoreDeallocInstrs rest' :=
    drop_succ_of_drop_eq_cons
      (mapBlockInstrs elimDeadStoreDeallocInstrs blk_src).instrs
      s_tgt.ip (.deallocSlot d) (elimDeadStoreDeallocInstrs rest') hdrop_tgt
  have hblk_tgt :=
    target_block_some_of_simState elimDeadStoreDeallocInstrs root hsim hblk
  let s_tgt' : X86State := {
    s_tgt with
    mem := updateSlot s_tgt.mem d.index none
    ip := s_tgt.ip + 1
  }
  have hstep_tgt :
      evalX86Step (elimDeadStoreDealloc root) s_tgt = .step () s_tgt' := by
    rw [evalX86Step_of_instr_some (elimDeadStoreDealloc root) s_tgt
      (mapBlockInstrs elimDeadStoreDeallocInstrs blk_src) (.deallocSlot d)
      hblk_tgt hip_tgt]
    rfl
  let s_src₁ : X86State := {
    s_src with
    mem := updateSlot s_src.mem tmp.index (some v)
    ip := s_src.ip + 1
  }
  have hstep_src₁ : evalX86Step root s_src = .step () s_src₁ := by
    rw [evalX86Step_of_instr_some root s_src blk_src
      (.mov tmp (.imm v)) hblk hip_src₀]
    rfl
  let s_src₂ : X86State := {
    s_src₁ with
    mem := updateSlot s_src₁.mem d.index none
    ip := s_src.ip + 1 + 1
  }
  have hblk_src₁ : (s_src₁.curBody.getD root).blocks[s_src₁.bb]? = some blk_src :=
    hblk
  have hstep_src₂ : evalX86Step root s_src₁ = .step () s_src₂ := by
    rw [evalX86Step_of_instr_some root s_src₁ blk_src
      (.deallocSlot d) hblk_src₁ hip_src₁]
    rfl
  -- Intermediate divergence: `s_tgt.mem` and `s_src₁.mem` agree everywhere
  -- except `d.index` (`tmp.index = d.index`).
  have hmem_div : MemAgreesExcept d.index s_tgt.mem s_src₁.mem := by
    dsimp [s_src₁]
    rw [hd]
    exact memAgreesExcept_updateSlot_dead_right
      (memAgreesExcept_of_memExtEq d.index hsim.1) (some v)
  -- Reconvergence: executing `.deallocSlot d` in both machines overwrites
  -- `d.index` with `none`, restoring `MemExtEq` without `funext`.
  have hmem_reconv : MemExtEq s_tgt'.mem s_src₂.mem :=
    memExtEq_of_memAgreesExcept_updateSlot hmem_div none
  refine Or.inr (Or.inr ⟨s_tgt', s_src₂, 1, hstep_tgt, ?_, ?_⟩)
  · refine ⟨?_, ?_⟩
    · refine ⟨hmem_reconv, hsim.2.1, rfl, hsim.2.2.2.1, hsim.2.2.2.2.1, hsim.2.2.2.2.2⟩
    · intro b hb
      dsimp [s_src₂, s_src₁] at hb
      rw [hblk] at hb
      injection hb with hb_eq
      subst hb_eq
      dsimp [s_tgt', s_src₂]
      rw [hdrop_tgt₁, hdrop_src₂]
  · intro n tr out hr
    exact ReachesPrefix.step (n + 1) s_src s_src₁ () (() :: tr) out hstep_src₁.symm
      (ReachesPrefix.step n s_src₁ s_src₂ () tr out hstep_src₂.symm hr)

theorem step_elimDeadStoreDealloc_simulation
    (root : X86Body) (init s_tgt s_src : X86State)
    (hsim : SimPass elimDeadStoreDeallocInstrs root s_tgt s_src) :
    StepSimOutcome (SimPass elimDeadStoreDeallocInstrs root)
      (elimDeadStoreDealloc root) root init s_tgt s_src := by
  let ⟨hst, hdrop⟩ := hsim
  cases hblk : (s_src.curBody.getD root).blocks[s_src.bb]? with
  | none =>
    exact stepSim_of_block_none elimDeadStoreDeallocInstrs
      (SimPass elimDeadStoreDeallocInstrs root) root init s_tgt s_src hst hblk
  | some blk_src =>
    have hdrop_tgt := hdrop blk_src hblk
    cases hrem : blk_src.instrs.drop s_src.ip with
    | nil =>
      rw [hrem] at hdrop_tgt
      exact stepSim_of_term elimDeadStoreDeallocInstrs
        (SimPass elimDeadStoreDeallocInstrs root) root id
        init s_tgt s_src blk_src hst hblk hrem hdrop_tgt
    | cons instr rest =>
      rw [hrem] at hdrop_tgt
      cases instr with
      | mov tmp srcOp =>
        cases srcOp with
        | stackSlot s c =>
          exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
            (SimPass elimDeadStoreDeallocInstrs root) root id
            init s_tgt s_src blk_src (.mov tmp (.stackSlot s c)) rest
            hst hblk hrem hdrop_tgt
        | imm v =>
          cases rest with
          | nil =>
            exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
              (SimPass elimDeadStoreDeallocInstrs root) root id
              init s_tgt s_src blk_src (.mov tmp (.imm v)) []
              hst hblk hrem hdrop_tgt
          | cons instr₂ rest' =>
            cases instr₂ with
            | deallocSlot d =>
              dsimp [elimDeadStoreDeallocInstrs] at hdrop_tgt
              cases hcond : (tmp.index == d.index) with
              | false =>
                rw [hcond] at hdrop_tgt
                exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                  (SimPass elimDeadStoreDeallocInstrs root) root id
                  init s_tgt s_src blk_src (.mov tmp (.imm v)) (.deallocSlot d :: rest')
                  hst hblk hrem hdrop_tgt
              | true =>
                rw [hcond] at hdrop_tgt
                exact stepSim_elimDeadStoreDealloc_matched root init s_tgt s_src
                  blk_src tmp d v rest' hst hblk hrem hdrop_tgt (eq_of_beq hcond)
            | mov d2 s2 =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.mov d2 s2 :: rest')
                hst hblk hrem hdrop_tgt
            | alu op dst lhs rhs =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.alu op dst lhs rhs :: rest')
                hst hblk hrem hdrop_tgt
            | wrapAdt adtId dst src =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.wrapAdt adtId dst src :: rest')
                hst hblk hrem hdrop_tgt
            | extractField0 dst src =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.extractField0 dst src :: rest')
                hst hblk hrem hdrop_tgt
            | leaSlot dst target =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.leaSlot dst target :: rest')
                hst hblk hrem hdrop_tgt
            | reborrowSlot dst srcPtr =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.reborrowSlot dst srcPtr :: rest')
                hst hblk hrem hdrop_tgt
            | allocSlot slot =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.allocSlot slot :: rest')
                hst hblk hrem hdrop_tgt
            | nop =>
              exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
                (SimPass elimDeadStoreDeallocInstrs root) root id
                init s_tgt s_src blk_src (.mov tmp (.imm v)) (.nop :: rest')
                hst hblk hrem hdrop_tgt
      | alu op dst lhs rhs =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src (.alu op dst lhs rhs) rest
          hst hblk hrem hdrop_tgt
      | wrapAdt adtId dst src =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src (.wrapAdt adtId dst src) rest
          hst hblk hrem hdrop_tgt
      | extractField0 dst src =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src (.extractField0 dst src) rest
          hst hblk hrem hdrop_tgt
      | leaSlot dst target =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src (.leaSlot dst target) rest
          hst hblk hrem hdrop_tgt
      | reborrowSlot dst srcPtr =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src (.reborrowSlot dst srcPtr) rest
          hst hblk hrem hdrop_tgt
      | allocSlot slot =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src (.allocSlot slot) rest
          hst hblk hrem hdrop_tgt
      | deallocSlot slot =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src (.deallocSlot slot) rest
          hst hblk hrem hdrop_tgt
      | nop =>
        exact stepSim_of_passthrough_instr elimDeadStoreDeallocInstrs
          (SimPass elimDeadStoreDeallocInstrs root) root id
          init s_tgt s_src blk_src .nop rest
          hst hblk hrem hdrop_tgt

/-- Universal `Compiles` soundness theorem for Pass 1 (`elimDeadStoreDealloc`)
    under the optimizing behavior morphism `π_x86_opt` (`q.steps ≤ n₁`). -/
theorem elimDeadStoreDealloc_compiles_opt (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_opt body (elimDeadStoreDealloc body) :=
  compiles_opt_of_stepSim elimDeadStoreDeallocInstrs
    (SimPass elimDeadStoreDeallocInstrs)
    (fun _ {_ _} h => h)
    step_elimDeadStoreDealloc_simulation
    body


/-! ## Section 4: Pass 2 — Copy Coalescing / Scratch-Reg Fusion (`fuseScratchMov`)

Coalesces a temporary immediate load followed by a register/slot-to-slot copy
(consuming or non-consuming) and scratch-slot deallocation:
  `.mov tmp (.imm v) :: .mov dst (.stackSlot s consume) :: .deallocSlot d :: rest'`
  (when `tmp.index == s.index && tmp.index == d.index && !(dst.index == d.index)`)
  `↦ .mov dst (.imm v) :: .deallocSlot d :: fuseScratchMovInstrs rest'`

This 3-to-2 variable-step optimization uses a genuine two-phase relational
invariant `SimFuse root s_tgt s_src`:
- **Phase 1 (`SimPass`)**: `MemExtEq s_tgt.mem s_src.mem` holds and instruction
  suffixes are aligned by `fuseScratchMovInstrs`. When the 3-instruction window
  fires, 1 target step (`.mov dst (.imm v)`) is matched by 2 source steps
  (`.mov tmp (.imm v)` then `.mov dst (.stackSlot s consume)`), transitioning to
  `SimPendingDealloc`.
- **Phase 2 (`SimPendingDealloc`)**: `MemAgreesExcept d.index s_tgt.mem s_src.mem`
  holds (memories diverge on the scratch slot `d.index`), and both machines are
  poised at `.deallocSlot d`. On the next step, both execute `.deallocSlot d`
  (1 target step, 1 source step) and reconverge to `MemExtEq` (`SimPass`) via
  `memExtEq_of_memAgreesExcept_updateSlot`. -/

def fuseScratchMovCond (tmp s dst d : SlotId) : Bool :=
  (tmp.index == s.index) &&
  (tmp.index == d.index) &&
  !(dst.index == d.index)

theorem fuseScratchMovCond_true {tmp s dst d : SlotId}
    (h : fuseScratchMovCond tmp s dst d = true) :
    tmp.index = s.index ∧ tmp.index = d.index := by
  dsimp [fuseScratchMovCond] at h
  cases h1 : (tmp.index == s.index) with
  | false => rw [h1] at h; cases h
  | true =>
    cases h2 : (tmp.index == d.index) with
    | false => rw [h1, h2] at h; cases h
    | true => exact ⟨eq_of_beq h1, eq_of_beq h2⟩

noncomputable def fuseScratchMovInstrs : List X86Instr → List X86Instr
  | [] => []
  | .mov tmp (.imm v) :: .mov dst (.stackSlot s consume) :: .deallocSlot d :: rest' =>
    if fuseScratchMovCond tmp s dst d then
      .mov dst (.imm v) :: .deallocSlot d :: fuseScratchMovInstrs rest'
    else
      .mov tmp (.imm v) :: .mov dst (.stackSlot s consume) :: .deallocSlot d ::
        fuseScratchMovInstrs rest'
  | instr :: rest => instr :: fuseScratchMovInstrs rest

noncomputable def fuseScratchMov (body : X86Body) : X86Body :=
  mapBodyInstrs fuseScratchMovInstrs body

/-- Phase 2 of the `fuseScratchMov` simulation invariant: target and source
    memories agree everywhere except the scratch slot `d.index`, and both
    machines are positioned at `.deallocSlot d`. -/
def SimPendingDealloc (root : X86Body) (s_tgt s_src : X86State) : Prop :=
  ∃ (d : SlotId) (blk_src : X86Block) (rest' : List X86Instr),
    MemAgreesExcept d.index s_tgt.mem s_src.mem ∧
    s_tgt.bb = s_src.bb ∧
    s_tgt.tySizes = s_src.tySizes ∧
    s_tgt.curBody = s_src.curBody.map fuseScratchMov ∧
    StackExtEq s_tgt.stack (s_src.stack.map (mapFrame fuseScratchMov)) ∧
    (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src ∧
    blk_src.instrs.drop s_src.ip = .deallocSlot d :: rest' ∧
    (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs.drop s_tgt.ip =
      .deallocSlot d :: fuseScratchMovInstrs rest'

/-- Two-phase relational invariant for `fuseScratchMov`. -/
def SimFuse (root : X86Body) (s_tgt s_src : X86State) : Prop :=
  SimPass fuseScratchMovInstrs root s_tgt s_src ∨
  SimPendingDealloc root s_tgt s_src

theorem evalX86Instr_mov_stackSlot_after_imm
    (s_src : X86State) (tmp s dst : SlotId) (v : X86Val) (consume : Bool)
    (hts : tmp.index = s.index) :
    ∃ mem_op : Nat → Option X86Val,
      evalX86Instr
        { s_src with
          mem := updateSlot s_src.mem tmp.index (some v)
          ip := s_src.ip + 1 }
        (.mov dst (.stackSlot s consume)) =
      .step ()
        { s_src with
          mem := updateSlot mem_op dst.index (some v)
          ip := s_src.ip + 1 + 1 } ∧
      (∀ m_tgt,
        MemExtEq m_tgt s_src.mem →
        MemAgreesExcept tmp.index m_tgt mem_op) := by
  have hlookup :
      updateSlot s_src.mem tmp.index (some v) s.index = some v := by
    rw [← hts]
    exact updateSlot_same s_src.mem tmp.index (some v)
  cases consume with
  | false =>
    refine ⟨updateSlot s_src.mem tmp.index (some v), ?_, ?_⟩
    · dsimp [evalX86Instr, evalX86Operand]
      rw [hlookup]
    · intro m_tgt hm
      exact memAgreesExcept_updateSlot_dead_right
        (memAgreesExcept_of_memExtEq tmp.index hm) (some v)
  | true =>
    refine ⟨updateSlot (updateSlot s_src.mem tmp.index (some v)) s.index none, ?_, ?_⟩
    · dsimp [evalX86Instr, evalX86Operand]
      rw [hlookup]
    · intro m_tgt hm
      rw [← hts]
      exact memAgreesExcept_updateSlot_dead_right
        (memAgreesExcept_updateSlot_dead_right
          (memAgreesExcept_of_memExtEq tmp.index hm) (some v))
        none

/-- Transition A: from `SimPass` at a matched 3-instruction window, 1 target step
    (`.mov dst (.imm v)`) is matched by 2 source steps (`.mov tmp (.imm v)` then
    `.mov dst (.stackSlot s consume)`), landing in `SimPendingDealloc`. -/
theorem stepSim_fuseScratchMov_enter_pending
    (root : X86Body) (init s_tgt s_src : X86State) (blk_src : X86Block)
    (tmp dst s d : SlotId) (v : X86Val) (consume : Bool) (rest' : List X86Instr)
    (hsim : SimState fuseScratchMov s_tgt s_src)
    (hblk : (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src)
    (hdrop_src :
      blk_src.instrs.drop s_src.ip =
        .mov tmp (.imm v) :: .mov dst (.stackSlot s consume) :: .deallocSlot d :: rest')
    (hdrop_tgt :
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs.drop s_tgt.ip =
        .mov dst (.imm v) :: .deallocSlot d :: fuseScratchMovInstrs rest')
    (hcond : fuseScratchMovCond tmp s dst d = true) :
    StepSimOutcome (SimFuse root) (fuseScratchMov root) root init s_tgt s_src := by
  let ⟨hts, htd⟩ := fuseScratchMovCond_true hcond
  have hip_src₀ : blk_src.instrs[s_src.ip]? = some (.mov tmp (.imm v)) :=
    getElem?_of_drop_eq_cons blk_src.instrs s_src.ip
      (.mov tmp (.imm v))
      (.mov dst (.stackSlot s consume) :: .deallocSlot d :: rest') hdrop_src
  have hdrop_src₁ :
      blk_src.instrs.drop (s_src.ip + 1) =
        .mov dst (.stackSlot s consume) :: .deallocSlot d :: rest' :=
    drop_succ_of_drop_eq_cons blk_src.instrs s_src.ip
      (.mov tmp (.imm v))
      (.mov dst (.stackSlot s consume) :: .deallocSlot d :: rest') hdrop_src
  have hip_src₁ :
      blk_src.instrs[s_src.ip + 1]? = some (.mov dst (.stackSlot s consume)) :=
    getElem?_of_drop_eq_cons blk_src.instrs (s_src.ip + 1)
      (.mov dst (.stackSlot s consume)) (.deallocSlot d :: rest') hdrop_src₁
  have hdrop_src₂ :
      blk_src.instrs.drop (s_src.ip + 1 + 1) = .deallocSlot d :: rest' :=
    drop_succ_of_drop_eq_cons blk_src.instrs (s_src.ip + 1)
      (.mov dst (.stackSlot s consume)) (.deallocSlot d :: rest') hdrop_src₁
  have hip_tgt :
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs[s_tgt.ip]? =
        some (.mov dst (.imm v)) :=
    getElem?_of_drop_eq_cons
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs
      s_tgt.ip (.mov dst (.imm v))
      (.deallocSlot d :: fuseScratchMovInstrs rest') hdrop_tgt
  have hdrop_tgt₁ :
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs.drop (s_tgt.ip + 1) =
        .deallocSlot d :: fuseScratchMovInstrs rest' :=
    drop_succ_of_drop_eq_cons
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs
      s_tgt.ip (.mov dst (.imm v))
      (.deallocSlot d :: fuseScratchMovInstrs rest') hdrop_tgt
  have hblk_tgt :=
    target_block_some_of_simState fuseScratchMovInstrs root hsim hblk
  let s_mid : X86State := {
    s_tgt with
    mem := updateSlot s_tgt.mem dst.index (some v)
    ip := s_tgt.ip + 1
  }
  have hstep_tgt :
      evalX86Step (fuseScratchMov root) s_tgt = .step () s_mid := by
    rw [evalX86Step_of_instr_some (fuseScratchMov root) s_tgt
      (mapBlockInstrs fuseScratchMovInstrs blk_src) (.mov dst (.imm v))
      hblk_tgt hip_tgt]
    rfl
  let s_src₁ : X86State := {
    s_src with
    mem := updateSlot s_src.mem tmp.index (some v)
    ip := s_src.ip + 1
  }
  have hstep_src₁ : evalX86Step root s_src = .step () s_src₁ := by
    rw [evalX86Step_of_instr_some root s_src blk_src
      (.mov tmp (.imm v)) hblk hip_src₀]
    rfl
  let ⟨mem_op, hinstr_src₂, hmem_op⟩ :=
    evalX86Instr_mov_stackSlot_after_imm s_src tmp s dst v consume hts
  let s_src₂ : X86State := {
    s_src with
    mem := updateSlot mem_op dst.index (some v)
    ip := s_src.ip + 1 + 1
  }
  have hblk_src₁ : (s_src₁.curBody.getD root).blocks[s_src₁.bb]? = some blk_src :=
    hblk
  have hstep_src₂ : evalX86Step root s_src₁ = .step () s_src₂ := by
    rw [evalX86Step_of_instr_some root s_src₁ blk_src
      (.mov dst (.stackSlot s consume)) hblk_src₁ hip_src₁]
    exact hinstr_src₂
  have hmem_div_tmp : MemAgreesExcept tmp.index s_mid.mem s_src₂.mem :=
    memAgreesExcept_updateSlot_both (hmem_op s_tgt.mem hsim.1) dst.index (some v)
  have hmem_div_d : MemAgreesExcept d.index s_mid.mem s_src₂.mem := by
    rw [← htd]
    exact hmem_div_tmp
  refine Or.inr (Or.inr ⟨s_mid, s_src₂, 1, hstep_tgt, Or.inr ?_, ?_⟩)
  · exact ⟨d, blk_src, rest', hmem_div_d, hsim.2.1, hsim.2.2.2.1,
      hsim.2.2.2.2.1, hsim.2.2.2.2.2, hblk, hdrop_src₂, hdrop_tgt₁⟩
  · intro n tr out hr
    exact ReachesPrefix.step (n + 1) s_src s_src₁ () (() :: tr) out hstep_src₁.symm
      (ReachesPrefix.step n s_src₁ s_src₂ () tr out hstep_src₂.symm hr)

/-- Transition B: from `SimPendingDealloc`, both machines execute `.deallocSlot d`
    in 1 step (`k = 0`) and reconverge from `MemAgreesExcept d.index` back to
    `MemExtEq` (`SimPass`). -/
theorem stepSim_fuseScratchMov_exit_pending
    (root : X86Body) (init s_tgt s_src : X86State)
    (hpending : SimPendingDealloc root s_tgt s_src) :
    StepSimOutcome (SimFuse root) (fuseScratchMov root) root init s_tgt s_src := by
  let ⟨d, blk_src, rest', hmem_div, hbb, hty, hcur, hstack,
    hblk, hdrop_src, hdrop_tgt⟩ := hpending
  have hip_src : blk_src.instrs[s_src.ip]? = some (.deallocSlot d) :=
    getElem?_of_drop_eq_cons blk_src.instrs s_src.ip
      (.deallocSlot d) rest' hdrop_src
  have hdrop_src₁ : blk_src.instrs.drop (s_src.ip + 1) = rest' :=
    drop_succ_of_drop_eq_cons blk_src.instrs s_src.ip
      (.deallocSlot d) rest' hdrop_src
  have hip_tgt :
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs[s_tgt.ip]? =
        some (.deallocSlot d) :=
    getElem?_of_drop_eq_cons
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs
      s_tgt.ip (.deallocSlot d) (fuseScratchMovInstrs rest') hdrop_tgt
  have hdrop_tgt₁ :
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs.drop (s_tgt.ip + 1) =
        fuseScratchMovInstrs rest' :=
    drop_succ_of_drop_eq_cons
      (mapBlockInstrs fuseScratchMovInstrs blk_src).instrs
      s_tgt.ip (.deallocSlot d) (fuseScratchMovInstrs rest') hdrop_tgt
  have hcur_getD :
      s_tgt.curBody.getD (fuseScratchMov root) =
        fuseScratchMov (s_src.curBody.getD root) := by
    rw [hcur]
    cases s_src.curBody <;> rfl
  have hblk_tgt :
      (s_tgt.curBody.getD (fuseScratchMov root)).blocks[s_tgt.bb]? =
        some (mapBlockInstrs fuseScratchMovInstrs blk_src) := by
    rw [hcur_getD, fuseScratchMov, blocks_mapBodyInstrs, hbb,
      mapBlockListInstrs_getElem?, hblk]
    rfl
  let s_tgt' : X86State := {
    s_tgt with
    mem := updateSlot s_tgt.mem d.index none
    ip := s_tgt.ip + 1
  }
  have hstep_tgt :
      evalX86Step (fuseScratchMov root) s_tgt = .step () s_tgt' := by
    rw [evalX86Step_of_instr_some (fuseScratchMov root) s_tgt
      (mapBlockInstrs fuseScratchMovInstrs blk_src) (.deallocSlot d)
      hblk_tgt hip_tgt]
    rfl
  let s_src' : X86State := {
    s_src with
    mem := updateSlot s_src.mem d.index none
    ip := s_src.ip + 1
  }
  have hstep_src : evalX86Step root s_src = .step () s_src' := by
    rw [evalX86Step_of_instr_some root s_src blk_src
      (.deallocSlot d) hblk hip_src]
    rfl
  -- Reconvergence: `.deallocSlot d` overwrites `d.index` with `none` in both
  -- machines, restoring `MemExtEq` from `MemAgreesExcept d.index`.
  have hmem_reconv : MemExtEq s_tgt'.mem s_src'.mem :=
    memExtEq_of_memAgreesExcept_updateSlot hmem_div none
  refine Or.inr (Or.inr ⟨s_tgt', s_src', 0, hstep_tgt, Or.inl ?_, ?_⟩)
  · refine ⟨?_, ?_⟩
    · refine ⟨hmem_reconv, hbb, rfl, hty, hcur, hstack⟩
    · intro b hb
      dsimp [s_src'] at hb
      rw [hblk] at hb
      injection hb with hb_eq
      subst hb_eq
      dsimp [s_tgt', s_src']
      rw [hdrop_tgt₁, hdrop_src₁]
  · intro n tr out hr
    exact ReachesPrefix.step n s_src s_src' () tr out hstep_src.symm hr

theorem step_fuseScratchMov_simulation
    (root : X86Body) (init s_tgt s_src : X86State)
    (hsim : SimFuse root s_tgt s_src) :
    StepSimOutcome (SimFuse root) (fuseScratchMov root) root init s_tgt s_src := by
  cases hsim with
  | inr hpending =>
    exact stepSim_fuseScratchMov_exit_pending root init s_tgt s_src hpending
  | inl hpass =>
    let ⟨hst, hdrop⟩ := hpass
    cases hblk : (s_src.curBody.getD root).blocks[s_src.bb]? with
    | none =>
      exact stepSim_of_block_none fuseScratchMovInstrs
        (SimFuse root) root init s_tgt s_src hst hblk
    | some blk_src =>
      have hdrop_tgt := hdrop blk_src hblk
      cases hrem : blk_src.instrs.drop s_src.ip with
      | nil =>
        rw [hrem] at hdrop_tgt
        exact stepSim_of_term fuseScratchMovInstrs
          (SimFuse root) root Or.inl
          init s_tgt s_src blk_src hst hblk hrem hdrop_tgt
      | cons instr rest =>
        rw [hrem] at hdrop_tgt
        cases instr with
        | mov tmp srcOp =>
          cases srcOp with
          | stackSlot s c =>
            exact stepSim_of_passthrough_instr fuseScratchMovInstrs
              (SimFuse root) root Or.inl
              init s_tgt s_src blk_src (.mov tmp (.stackSlot s c)) rest
              hst hblk hrem hdrop_tgt
          | imm v =>
            cases rest with
            | nil =>
              exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                (SimFuse root) root Or.inl
                init s_tgt s_src blk_src (.mov tmp (.imm v)) []
                hst hblk hrem hdrop_tgt
            | cons instr₂ rest₁ =>
              cases instr₂ with
              | mov dst srcOp₂ =>
                cases srcOp₂ with
                | imm v₂ =>
                  exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                    (SimFuse root) root Or.inl
                    init s_tgt s_src blk_src (.mov tmp (.imm v))
                    (.mov dst (.imm v₂) :: rest₁)
                    hst hblk hrem hdrop_tgt
                | stackSlot s consume =>
                  cases rest₁ with
                  | nil =>
                    exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                      (SimFuse root) root Or.inl
                      init s_tgt s_src blk_src (.mov tmp (.imm v))
                      [.mov dst (.stackSlot s consume)]
                      hst hblk hrem hdrop_tgt
                  | cons instr₃ rest' =>
                    cases instr₃ with
                    | deallocSlot d =>
                      dsimp [fuseScratchMovInstrs] at hdrop_tgt
                      cases hcond : fuseScratchMovCond tmp s dst d with
                      | false =>
                        rw [hcond] at hdrop_tgt
                        exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                          (SimFuse root) root Or.inl
                          init s_tgt s_src blk_src (.mov tmp (.imm v))
                          (.mov dst (.stackSlot s consume) :: .deallocSlot d :: rest')
                          hst hblk hrem hdrop_tgt
                      | true =>
                        rw [hcond] at hdrop_tgt
                        exact stepSim_fuseScratchMov_enter_pending
                          root init s_tgt s_src blk_src tmp dst s d v consume rest'
                          hst hblk hrem hdrop_tgt hcond
                    | mov d3 s3 =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .mov d3 s3 :: rest')
                        hst hblk hrem hdrop_tgt
                    | alu op3 dst3 lhs3 rhs3 =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .alu op3 dst3 lhs3 rhs3 :: rest')
                        hst hblk hrem hdrop_tgt
                    | wrapAdt adtId3 dst3 src3 =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .wrapAdt adtId3 dst3 src3 :: rest')
                        hst hblk hrem hdrop_tgt
                    | extractField0 dst3 src3 =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .extractField0 dst3 src3 :: rest')
                        hst hblk hrem hdrop_tgt
                    | leaSlot dst3 target3 =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .leaSlot dst3 target3 :: rest')
                        hst hblk hrem hdrop_tgt
                    | reborrowSlot dst3 srcPtr3 =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .reborrowSlot dst3 srcPtr3 :: rest')
                        hst hblk hrem hdrop_tgt
                    | allocSlot slot3 =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .allocSlot slot3 :: rest')
                        hst hblk hrem hdrop_tgt
                    | nop =>
                      exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                        (SimFuse root) root Or.inl
                        init s_tgt s_src blk_src (.mov tmp (.imm v))
                        (.mov dst (.stackSlot s consume) :: .nop :: rest')
                        hst hblk hrem hdrop_tgt
              | alu op dst lhs rhs =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.alu op dst lhs rhs :: rest₁)
                  hst hblk hrem hdrop_tgt
              | wrapAdt adtId dst src =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.wrapAdt adtId dst src :: rest₁)
                  hst hblk hrem hdrop_tgt
              | extractField0 dst src =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.extractField0 dst src :: rest₁)
                  hst hblk hrem hdrop_tgt
              | leaSlot dst target =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.leaSlot dst target :: rest₁)
                  hst hblk hrem hdrop_tgt
              | reborrowSlot dst srcPtr =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.reborrowSlot dst srcPtr :: rest₁)
                  hst hblk hrem hdrop_tgt
              | allocSlot slot =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.allocSlot slot :: rest₁)
                  hst hblk hrem hdrop_tgt
              | deallocSlot slot =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.deallocSlot slot :: rest₁)
                  hst hblk hrem hdrop_tgt
              | nop =>
                exact stepSim_of_passthrough_instr fuseScratchMovInstrs
                  (SimFuse root) root Or.inl
                  init s_tgt s_src blk_src (.mov tmp (.imm v))
                  (.nop :: rest₁)
                  hst hblk hrem hdrop_tgt
        | alu op dst lhs rhs =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src (.alu op dst lhs rhs) rest
            hst hblk hrem hdrop_tgt
        | wrapAdt adtId dst src =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src (.wrapAdt adtId dst src) rest
            hst hblk hrem hdrop_tgt
        | extractField0 dst src =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src (.extractField0 dst src) rest
            hst hblk hrem hdrop_tgt
        | leaSlot dst target =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src (.leaSlot dst target) rest
            hst hblk hrem hdrop_tgt
        | reborrowSlot dst srcPtr =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src (.reborrowSlot dst srcPtr) rest
            hst hblk hrem hdrop_tgt
        | allocSlot slot =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src (.allocSlot slot) rest
            hst hblk hrem hdrop_tgt
        | deallocSlot slot =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src (.deallocSlot slot) rest
            hst hblk hrem hdrop_tgt
        | nop =>
          exact stepSim_of_passthrough_instr fuseScratchMovInstrs
            (SimFuse root) root Or.inl
            init s_tgt s_src blk_src .nop rest
            hst hblk hrem hdrop_tgt

/-- Universal `Compiles` soundness theorem for Pass 2 (`fuseScratchMov`)
    under the optimizing behavior morphism `π_x86_opt` (`q.steps ≤ n₁`). -/
theorem fuseScratchMov_compiles_opt (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_opt body (fuseScratchMov body) :=
  compiles_opt_of_stepSim fuseScratchMovInstrs
    SimFuse
    (fun _ {_ _} h => Or.inl h)
    step_fuseScratchMov_simulation
    body


/-! ## Section 5: Pass 3 (`stripNops`) and Full 3-Pass Variable-Step Optimization Pipeline (`optPipeline`)

Composes:
1. `fuseScratchMov` (Pass 2: 3-to-2 copy coalescing with two-phase `SimFuse`
   relational invariant),
2. `elimDeadStoreDealloc` (Pass 1: 2-to-1 dead-store + dealloc elimination with
   intra-step `MemAgreesExcept` reconvergence), and
3. `stripNops` (Pass 3: 1-to-0 instruction deletion)
into a unified variable-step optimization pipeline `optPipeline`, proving
universal soundness `optPipeline_compiles_opt` under `π_x86_opt` (`q.steps ≤ n₁`)
and end-to-end `Verified` preservation on a concrete Stage 0 `X86Body`. -/

noncomputable def stripNopsInstrs : List X86Instr → List X86Instr
  | [] => []
  | .nop :: rest => stripNopsInstrs rest
  | instr :: rest => instr :: stripNopsInstrs rest

noncomputable def stripNops (body : X86Body) : X86Body :=
  mapBodyInstrs stripNopsInstrs body

theorem stepSimOutcome_prepend_step
    {R : X86State → X86State → Prop}
    {tgtBody srcBody : X86Body} {init s_tgt s_src s_src₁ : X86State}
    (hstep₁ : evalX86Step srcBody s_src = .step () s_src₁)
    (hout : StepSimOutcome R tgtBody srcBody init s_tgt s_src₁) :
    StepSimOutcome R tgtBody srcBody init s_tgt s_src := by
  cases hout with
  | inl hterm =>
    let ⟨term, hstep_tgt, k, hreach⟩ := hterm
    refine Or.inl ⟨term, hstep_tgt, k + 1, fun m => ?_⟩
    have hsum : m + (k + 1) + 1 = (m + k + 1) + 1 := by
      rw [← Nat.add_assoc m k 1]
    rw [hsum]
    exact ReachesPrefix.step (m + k + 1) s_src s_src₁ ()
      (List.replicate k ()) (.terminated term) hstep₁.symm (hreach m)
  | inr hrest =>
    cases hrest with
    | inl hfail =>
      let ⟨fk, hstep_tgt, k, hreach⟩ := hfail
      refine Or.inr (Or.inl ⟨fk, hstep_tgt, k + 1, fun m => ?_⟩)
      have hsum : m + (k + 1) + 1 = (m + k + 1) + 1 := by
        rw [← Nat.add_assoc m k 1]
      rw [hsum]
      exact ReachesPrefix.step (m + k + 1) s_src s_src₁ ()
        (List.replicate k ()) (.failed fk) hstep₁.symm (hreach m)
    | inr hstep =>
      let ⟨s_tgt', s_src', k, hstep_tgt, hR', hprepend⟩ := hstep
      refine Or.inr (Or.inr ⟨s_tgt', s_src', k + 1, hstep_tgt, hR', ?_⟩)
      intro n tr out hr
      have hsum : n + (k + 1) + 1 = (n + k + 1) + 1 := by
        rw [← Nat.add_assoc n k 1]
      rw [hsum]
      exact ReachesPrefix.step (n + k + 1) s_src s_src₁ ()
        (List.replicate (k + 1) () ++ tr) out hstep₁.symm
        (hprepend n tr out hr)

theorem step_stripNops_simulation_rem
    (root : X86Body) (init s_tgt : X86State) (blk_src : X86Block)
    (rem_src : List X86Instr) :
    ∀ (s_src : X86State),
      SimState stripNops s_tgt s_src →
      (s_src.curBody.getD root).blocks[s_src.bb]? = some blk_src →
      blk_src.instrs.drop s_src.ip = rem_src →
      (mapBlockInstrs stripNopsInstrs blk_src).instrs.drop s_tgt.ip =
        stripNopsInstrs rem_src →
      StepSimOutcome (SimPass stripNopsInstrs root)
        (stripNops root) root init s_tgt s_src := by
  induction rem_src with
  | nil =>
    intro s_src hst hblk hrem hdrop_tgt
    exact stepSim_of_term stripNopsInstrs
      (SimPass stripNopsInstrs root) root id
      init s_tgt s_src blk_src hst hblk hrem hdrop_tgt
  | cons instr rest ih =>
    intro s_src hst hblk hrem hdrop_tgt
    cases instr with
    | nop =>
      have hip_src : blk_src.instrs[s_src.ip]? = some .nop :=
        getElem?_of_drop_eq_cons blk_src.instrs s_src.ip .nop rest hrem
      have hdrop_next : blk_src.instrs.drop (s_src.ip + 1) = rest :=
        drop_succ_of_drop_eq_cons blk_src.instrs s_src.ip .nop rest hrem
      let s_src₁ : X86State := { s_src with ip := s_src.ip + 1 }
      have hstep_nop : evalX86Step root s_src = .step () s_src₁ :=
        evalX86Step_of_instr_some root s_src blk_src .nop hblk hip_src
      have hst₁ : SimState stripNops s_tgt s_src₁ := hst
      have hblk₁ : (s_src₁.curBody.getD root).blocks[s_src₁.bb]? = some blk_src :=
        hblk
      dsimp [stripNopsInstrs] at hdrop_tgt
      exact stepSimOutcome_prepend_step hstep_nop
        (ih s_src₁ hst₁ hblk₁ hdrop_next hdrop_tgt)
    | mov dst src =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.mov dst src) rest hst hblk hrem hdrop_tgt
    | alu op dst lhs rhs =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.alu op dst lhs rhs) rest hst hblk hrem hdrop_tgt
    | wrapAdt adtId dst src =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.wrapAdt adtId dst src) rest hst hblk hrem hdrop_tgt
    | extractField0 dst src =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.extractField0 dst src) rest hst hblk hrem hdrop_tgt
    | leaSlot dst target =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.leaSlot dst target) rest hst hblk hrem hdrop_tgt
    | reborrowSlot dst srcPtr =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.reborrowSlot dst srcPtr) rest hst hblk hrem hdrop_tgt
    | allocSlot slot =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.allocSlot slot) rest hst hblk hrem hdrop_tgt
    | deallocSlot slot =>
      exact stepSim_of_passthrough_instr stripNopsInstrs
        (SimPass stripNopsInstrs root) root id
        init s_tgt s_src blk_src (.deallocSlot slot) rest hst hblk hrem hdrop_tgt

theorem step_stripNops_simulation
    (root : X86Body) (init s_tgt s_src : X86State)
    (hsim : SimPass stripNopsInstrs root s_tgt s_src) :
    StepSimOutcome (SimPass stripNopsInstrs root)
      (stripNops root) root init s_tgt s_src := by
  let ⟨hst, hdrop⟩ := hsim
  cases hblk : (s_src.curBody.getD root).blocks[s_src.bb]? with
  | none =>
    exact stepSim_of_block_none stripNopsInstrs
      (SimPass stripNopsInstrs root) root init s_tgt s_src hst hblk
  | some blk_src =>
    exact step_stripNops_simulation_rem root init s_tgt blk_src
      (blk_src.instrs.drop s_src.ip) s_src hst hblk rfl (hdrop blk_src hblk)

/-- Universal `Compiles` soundness theorem for Pass 3 (`stripNops`)
    under the optimizing behavior morphism `π_x86_opt` (`q.steps ≤ n₁`). -/
theorem stripNops_compiles_opt (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_opt body (stripNops body) :=
  compiles_opt_of_stepSim stripNopsInstrs
    (SimPass stripNopsInstrs)
    (fun _ {_ _} h => h)
    step_stripNops_simulation
    body

/-- Full 3-pass variable-step optimization pipeline:
    1. `fuseScratchMov` (3-to-2 copy coalescing with two-phase `SimFuse`),
    2. `elimDeadStoreDealloc` (2-to-1 dead-store + dealloc elimination), and
    3. `stripNops` (1-to-0 `nop` deletion). -/
noncomputable def optPipeline (body : X86Body) : X86Body :=
  stripNops (elimDeadStoreDealloc (fuseScratchMov body))

/-- Universal `Compiles` soundness theorem for the full 3-pass variable-step
    pipeline `optPipeline` under `π_x86_opt` (`q.steps ≤ n₁`), proved by
    composing `fuseScratchMov_compiles_opt`, `elimDeadStoreDealloc_compiles_opt`,
    and `stripNops_compiles_opt` via `compiles_opt_trans`. -/
theorem optPipeline_compiles_opt (body : X86Body) :
    Compiles X86Lang X86Lang π_x86_opt body (optPipeline body) :=
  compiles_opt_trans
    (compiles_opt_trans
      (fuseScratchMov_compiles_opt body)
      (elimDeadStoreDealloc_compiles_opt (fuseScratchMov body)))
    (stripNops_compiles_opt (elimDeadStoreDealloc (fuseScratchMov body)))

/-! ### Contract Invariance under `π_x86_opt` and End-to-End `Verified` Preservation -/

theorem π_x86_opt_ensuresRetLibInv_le (libInv : LibInv) (retTy : X86Ty)
    (pre : ExecQuery X86State → Prop)
    (hpre : ∀ init n₁ n₂, pre ⟨init, n₁⟩ → pre ⟨init, n₂⟩) :
    π_x86_opt (EnsuresRetLibInv libInv retTy pre) ≤
      EnsuresRetLibInv libInv retTy pre :=
  π_x86_opt_specOn_le hpre (fun _ _ _ _ _ _ h => h)

theorem π_x86_opt_ensuresEqArg_le (argSlot : Nat) :
    π_x86_opt (EnsuresEqArg argSlot) ≤ EnsuresEqArg argSlot :=
  π_x86_opt_specOn_le (fun _ _ _ h => h) (fun _ _ _ _ _ _ h => h)

theorem π_x86_opt_ensuresConst_le (expected : X86Val) :
    π_x86_opt (EnsuresConst expected) ≤ EnsuresConst expected :=
  π_x86_opt_specOn_le (fun _ _ _ h => h) (fun _ _ _ _ _ _ h => h)

theorem π_x86_opt_ensuresBinOp_le (op : X86BinOp) (arg1Slot arg2Slot : Nat) :
    π_x86_opt (EnsuresBinOp op arg1Slot arg2Slot) ≤
      EnsuresBinOp op arg1Slot arg2Slot :=
  π_x86_opt_specOn_le (fun _ _ _ h => h) (fun _ _ _ _ _ _ h => h)

/-- Concrete Stage 0 `X86Body` containing:
    - a 3-instruction scratch-slot immediate load + copy + dealloc
      (`.mov ⟨2⟩ (.imm (.word64 40))`, `.mov ⟨1⟩ (.stackSlot ⟨2⟩ false)`,
      `.deallocSlot ⟨2⟩`),
    - a 2-instruction dead immediate store + dealloc
      (`.mov ⟨3⟩ (.imm (.word64 99))`, `.deallocSlot ⟨3⟩`),
    - a `.nop` instruction, and
    - an ALU addition `.alu .add ⟨0⟩ (.stackSlot ⟨1⟩ false) (.imm (.word64 2))`
      followed by `.ret`. -/
def stage0Body : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [{
    instrs := [
      .mov ⟨2⟩ (.imm (.word64 40)),
      .mov ⟨1⟩ (.stackSlot ⟨2⟩ false),
      .deallocSlot ⟨2⟩,
      .mov ⟨3⟩ (.imm (.word64 99)),
      .deallocSlot ⟨3⟩,
      .nop,
      .alu .add ⟨0⟩ (.stackSlot ⟨1⟩ false) (.imm (.word64 2))
    ]
    term := .ret
  }]

/-- Expected optimized `X86Body` after running `optPipeline` (compressed from
    7 instructions / 8 steps to 4 instructions / 5 steps). -/
def expectedOptStage0Body : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 4
  blocks := [{
    instrs := [
      .mov ⟨1⟩ (.imm (.word64 40)),
      .deallocSlot ⟨2⟩,
      .deallocSlot ⟨3⟩,
      .alu .add ⟨0⟩ (.stackSlot ⟨1⟩ false) (.imm (.word64 2))
    ]
    term := .ret
  }]

/-- Closed-term kernel `rfl` reduction of the `noncomputable` 3-pass pipeline
    `optPipeline` on `stage0Body`. -/
theorem optPipeline_stage0Body_eq :
    optPipeline stage0Body = expectedOptStage0Body :=
  rfl

/-- Helper predicate for proving `X86Sem body ≤ EnsuresConst expected` by
    symbolic step reduction. -/
def SafeAndReturns (body : X86Body) (init s : X86State) (expected : X86Val) : Prop :=
  ∀ n tr out,
    ReachesPrefix X86Machine body init n s tr out →
    out.isSafe ∧ (∀ ret, out = .terminated (.normal ret) → ret = expected)

theorem safeAndReturns_of_terminated
    {body : X86Body} {init s : X86State} {expected : X86Val}
    (hterm : evalX86Step body s = .terminated (.normal expected)) :
    SafeAndReturns body init s expected := by
  intro n tr out hr
  cases hr with
  | zero => exact ⟨True.intro, fun _ h => by cases h⟩
  | step _ _ _ _ _ _ hst =>
    have hcontra := Eq.trans hst hterm; cases hcontra
  | choice _ _ _ _ _ _ _ hst =>
    have hcontra := Eq.trans hst hterm; cases hcontra
  | emptyChoice _ _ _ _ hst =>
    have hcontra := Eq.trans hst hterm; cases hcontra
  | terminated _ _ term hst =>
    have heq := Eq.trans hst hterm
    injection heq with hterm_eq
    subst hterm_eq
    refine ⟨True.intro, fun ret h => ?_⟩
    injection h with h1
    injection h1 with h2
    exact h2.symm
  | failed _ _ _ hst =>
    have hcontra := Eq.trans hst hterm; cases hcontra
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, rfl⟩)

theorem safeAndReturns_of_step
    {body : X86Body} {init s s' : X86State} {expected : X86Val}
    (hstep : evalX86Step body s = .step () s')
    (hnext : SafeAndReturns body init s' expected) :
    SafeAndReturns body init s expected := by
  intro n tr out hr
  cases hr with
  | zero => exact ⟨True.intro, fun _ h => by cases h⟩
  | step m _ s₂ _ tr' _ hst hr' =>
    have heq := Eq.trans hst hstep
    injection heq with _ hs_eq
    subst hs_eq
    exact hnext m tr' out hr'
  | choice _ _ _ _ _ _ _ hst =>
    have hcontra := Eq.trans hst hstep; cases hcontra
  | emptyChoice _ _ _ _ hst =>
    have hcontra := Eq.trans hst hstep; cases hcontra
  | terminated _ _ _ hst =>
    have hcontra := Eq.trans hst hstep; cases hcontra
  | failed _ _ _ hst =>
    have hcontra := Eq.trans hst hstep; cases hcontra
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, rfl⟩)

theorem x86Sem_le_ensuresConst_of_safeAndReturns
    {body : X86Body} {expected : X86Val}
    (h : ∀ s, initX86State body s → SafeAndReturns body s s expected) :
    X86Sem body ≤ EnsuresConst expected := by
  intro q _
  refine ⟨?_, ?_⟩
  · intro hinit tr out hr
    exact (h q.init hinit q.steps tr out hr).1
  · intro out hout
    let ⟨hinit, hr⟩ := hout
    exact (h q.init hinit q.steps out.trace out.outcome hr).2

theorem stage0Body_meets_spec :
    X86Sem stage0Body ≤ EnsuresConst (.word64 42) := by
  apply x86Sem_le_ensuresConst_of_safeAndReturns
  intro s hinit
  cases s with
  | mk mem bb ip tySizes curBody stack =>
    have hbb : bb = 0 := hinit.1
    have hip : ip = 0 := hinit.2.1
    have hcur : curBody = none := hinit.2.2.1
    have hstack : stack = [] := hinit.2.2.2.1
    subst hbb hip hcur hstack
    exact safeAndReturns_of_step rfl
      (safeAndReturns_of_step rfl
        (safeAndReturns_of_step rfl
          (safeAndReturns_of_step rfl
            (safeAndReturns_of_step rfl
              (safeAndReturns_of_step rfl
                (safeAndReturns_of_step rfl
                  (safeAndReturns_of_terminated rfl)))))))

/-- End-to-end verification across the 3-pass stateful variable-step optimization
    pipeline `optPipeline`: `stage0Body_meets_spec` (proved on the unoptimized
    8-step Stage 0 program) transfers across `optPipeline_compiles_opt` to
    yield `AssemblerCompiler.Verified (optPipeline stage0Body) (EnsuresConst (.word64 42))`. -/
theorem stage0Body_optPipeline_verified
    (h_asm : AssemblerCompiler.SoundOn (optPipeline stage0Body)) :
    AssemblerCompiler.Verified (optPipeline stage0Body)
      (EnsuresConst (.word64 42)) :=
  verify_across_opt_pass
    stage0Body_meets_spec
    (optPipeline_compiles_opt stage0Body)
    (π_x86_opt_ensuresConst_le (.word64 42))
    h_asm

/-! ### Bounded-Progress Hierarchy (`π_opt ≤ π_progress (k + 1)`) -/

abbrev π_x86_progress (K : Nat) : X86Lang.Behavior → X86Lang.Behavior :=
  π_progress K id id

private theorem nat_le_succ_mul_add (n k : Nat) :
    n ≤ (k + 1) * n + k := by
  have h1 : 1 * n = n := Nat.one_mul n
  have h2 : (k + 1) * n = k * n + n := by
    rw [Nat.add_mul k 1 n, h1]
  rw [h2]
  have h3 : n ≤ k * n + n := Nat.le_add_left n (k * n)
  exact Nat.le_trans h3 (Nat.le_add_right (k * n + n) k)

/-- Every `π_opt` behavior morphism refines `π_progress (k + 1)` for all `k : Nat`
    (with `k = 0` giving `K = 1`, where `1 * n₁ + 0 = n₁`). -/
theorem π_opt_le_π_progress (k : Nat) (b : X86Lang.Behavior) :
    π_x86_opt b ≤ π_x86_progress (k + 1) b := by
  intro q hdef
  refine ⟨hdef, fun out hout => ?_⟩
  let ⟨n₁, tr₁, hle, hval⟩ := hout
  have hbound : q.steps ≤ (k + 1) * n₁ + ((k + 1) - 1) :=
    Nat.le_trans hle (nat_le_succ_mul_add n₁ k)
  exact ⟨n₁, tr₁, hbound, hval⟩

theorem elimDeadStoreDealloc_compiles_progress (k : Nat) (body : X86Body) :
    Compiles X86Lang X86Lang (π_x86_progress (k + 1))
      body (elimDeadStoreDealloc body) :=
  Preorder.le_trans
    (elimDeadStoreDealloc_compiles_opt body)
    (π_opt_le_π_progress k (X86Sem body))

theorem fuseScratchMov_compiles_progress (k : Nat) (body : X86Body) :
    Compiles X86Lang X86Lang (π_x86_progress (k + 1))
      body (fuseScratchMov body) :=
  Preorder.le_trans
    (fuseScratchMov_compiles_opt body)
    (π_opt_le_π_progress k (X86Sem body))

theorem optPipeline_compiles_progress (k : Nat) (body : X86Body) :
    Compiles X86Lang X86Lang (π_x86_progress (k + 1))
      body (optPipeline body) :=
  Preorder.le_trans
    (optPipeline_compiles_opt body)
    (π_opt_le_π_progress k (X86Sem body))

end R2StatefulVarStepProbe
