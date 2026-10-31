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
# Deliverable 4: Universal Refinement Bridge Between Canonical-Spine State and `Trusted.X86Machine`

This file is a self-contained `prelude` + `Init.NotationExtra` formalization in
Lean 4.34.1 proving that:
1. We can keep `Trusted/X86Semantics.lean` completely unchanged (with
   `X86State.mem : Nat → Option X86Val` and `updateSlot`), preserving its minimal
   TCB footprint.
2. In `theory/`, we define a canonical-spine symbolic execution state
   `CanonX86State` whose memory `mem : BinTrie X86Val` (or `CanonList X86Val`)
   has a 100% concrete spine from step 0 (`BinTrie.initArgs [v1, v2]`) while
   keeping argument values `v1, v2 : X86Val` symbolic.
3. A single universal simulation theorem (`reachesPrefix_safeAndEnsures_of_canonSteps_step`
   and `reachesPrefix_safeAndEnsures_of_canonSteps_normal`) bridges multi-step
   canonical execution (`evalCanonSteps`) directly to
   `Trusted.ReachesPrefix X86Machine`, collapsing basic-block symbolic execution
   and CFG join-point merging into `rfl`.
-/

namespace RefinementBridge

/-!
## 1. Exact Mirror of `Trusted/StepResult.lean`, `Trusted/X86Ast.lean`, and `Trusted/X86Semantics.lean`
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

def PrefixOutcome.isSafe {Val : Type} : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) (p : Prog)
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
  | add
  | sub
  | mul
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | eq
  | ne
  | lt
  | le
  | gt
  | ge

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

/-!
## 2. Small-Step Prefix Helpers from `theory/Anneal/MirLemmas.lean`
-/

theorem reachesPrefix_of_step
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    out = .running ∨
      ∃ n' tr', ReachesPrefix X86Machine body init n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step n' _ s₂ _ tr' _ h1 hr =>
    have h1' : StepResult.step () s₂ = evalX86Step body s := h1
    rw [hstep] at h1'
    injection h1' with _ hs
    subst hs
    exact Or.inr ⟨n', tr', hr⟩
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_terminated
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val} {term : TerminationKind X86Val}
    (hstep : evalX86Step body s = .terminated term)
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    out = .running ∨ out = .terminated term := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : StepResult.terminated t = evalX86Step body s := h1
    rw [hstep] at h1'
    injection h1' with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

def SafeAndEnsures (P : X86Val → Prop) (out : PrefixOutcome X86Val) : Prop :=
  out.isSafe ∧ ∀ ret, out = .terminated (.normal ret) → P ret

theorem reachesPrefix_safeAndEnsures_of_step
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val} {P : X86Val → Prop}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hnext : ∀ n' tr', ReachesPrefix X86Machine body init n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_safeAndEnsures_of_normal
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val} {P : X86Val → Prop} {v : X86Val}
    (hstep : evalX86Step body s = .terminated (.normal v))
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hterm =>
    subst hterm
    refine ⟨True.intro, ?_⟩
    intro ret hret
    injection hret with h1
    injection h1 with h2
    subst h2
    exact hPv

/-!
## 3. Canonical Binary Radix Trie (`BinTrie`) and Canonical Machine (`CanonX86State`)
-/

inductive BinTrie (V : Type) where
  | leaf
  | node (val : Option V) (left right : BinTrie V)

def BinTrie.mkNode {V : Type} (v : Option V) (l r : BinTrie V) : BinTrie V :=
  match l, r with
  | .leaf, .leaf =>
    match v with
    | none => .leaf
    | some _ => .node v .leaf .leaf
  | .leaf, .node _ _ _ => .node v l r
  | .node _ _ _, .leaf => .node v l r
  | .node _ _ _, .node _ _ _ => .node v l r

def BinTrie.getBits {V : Type} : BinTrie V → List Bool → Option V
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l _, false :: bs => BinTrie.getBits l bs
  | .node _ _ r, true :: bs => BinTrie.getBits r bs

def BinTrie.setBits {V : Type} : BinTrie V → List Bool → Option V → BinTrie V
  | .leaf, [], val => BinTrie.mkNode val .leaf .leaf
  | .leaf, false :: bs, val =>
    BinTrie.mkNode none (BinTrie.setBits .leaf bs val) .leaf
  | .leaf, true :: bs, val =>
    BinTrie.mkNode none .leaf (BinTrie.setBits .leaf bs val)
  | .node _ l r, [], val => BinTrie.mkNode val l r
  | .node v l r, false :: bs, val =>
    BinTrie.mkNode v (BinTrie.setBits l bs val) r
  | .node v l r, true :: bs, val =>
    BinTrie.mkNode v l (BinTrie.setBits r bs val)

theorem BinTrie.getBits_mkNode {V : Type} (v : Option V) (l r : BinTrie V)
    (bs : List Bool) :
    BinTrie.getBits (BinTrie.mkNode v l r) bs =
      BinTrie.getBits (.node v l r) bs := by
  cases l with
  | node _ _ _ => cases r <;> rfl
  | leaf =>
    cases r with
    | node _ _ _ => rfl
    | leaf =>
      cases v with
      | some _ => rfl
      | none =>
        cases bs with
        | nil => rfl
        | cons b _ => cases b <;> rfl

theorem BinTrie.getBits_setBits {V : Type} (t : BinTrie V) (target : List Bool)
    (val : Option V) (bs : List Bool) :
    BinTrie.getBits (BinTrie.setBits t target val) bs =
      if bs == target then val else BinTrie.getBits t bs := by
  induction target generalizing t bs with
  | nil =>
    cases t <;> {
      dsimp [BinTrie.setBits]
      rw [BinTrie.getBits_mkNode]
      cases bs with
      | nil => rfl
      | cons b _ => cases b <;> rfl
    }
  | cons tb tbs ih =>
    cases tb with
    | false =>
      cases t with
      | leaf =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | true => rfl
          | false =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih .leaf bs'
      | node v l r =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | true => rfl
          | false =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih l bs'
    | true =>
      cases t with
      | leaf =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | false => rfl
          | true =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih .leaf bs'
      | node v l r =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | false => rfl
          | true =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih r bs'

def succBits : List Bool → List Bool
  | [] => [false]
  | false :: bs => true :: bs
  | true :: bs => false :: succBits bs

def natToBits : Nat → List Bool
  | 0 => []
  | n + 1 => succBits (natToBits n)

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

def bitsToNat : List Bool → Nat
  | [] => 0
  | false :: bs => double (bitsToNat bs) + 1
  | true :: bs => double (bitsToNat bs) + 2

theorem bitsToNat_succBits (bs : List Bool) :
    bitsToNat (succBits bs) = bitsToNat bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => rfl
    | true =>
      dsimp [succBits, bitsToNat]
      rw [ih]
      rfl

theorem bitsToNat_natToBits (n : Nat) :
    bitsToNat (natToBits n) = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [natToBits]
    rw [bitsToNat_succBits, ih]

theorem natToBits_injective {i j : Nat} (h : natToBits i = natToBits j) :
    i = j := by
  rw [← bitsToNat_natToBits i, ← bitsToNat_natToBits j, h]

theorem list_bool_beq_eq {bs1 bs2 : List Bool} :
    (bs1 == bs2) = decide (bs1 = bs2) := by
  induction bs1 generalizing bs2 with
  | nil =>
    cases bs2 <;> rfl
  | cons b1 r1 ih =>
    cases bs2 with
    | nil => rfl
    | cons b2 r2 =>
      cases b1 <;> cases b2
      · change (r1 == r2) = decide (false :: r1 = false :: r2)
        rw [ih]
        cases h : decide (r1 = r2) with
        | true =>
          have hr : r1 = r2 := of_decide_eq_true h
          subst hr
          exact (decide_eq_true rfl).symm
        | false =>
          have hne : r1 ≠ r2 := of_decide_eq_false h
          exact (decide_eq_false
            (fun hc => by injection hc with _ h'; exact hne h')).symm
      · rfl
      · rfl
      · change (r1 == r2) = decide (true :: r1 = true :: r2)
        rw [ih]
        cases h : decide (r1 = r2) with
        | true =>
          have hr : r1 = r2 := of_decide_eq_true h
          subst hr
          exact (decide_eq_true rfl).symm
        | false =>
          have hne : r1 ≠ r2 := of_decide_eq_false h
          exact (decide_eq_false
            (fun hc => by injection hc with _ h'; exact hne h')).symm

theorem natToBits_beq (i j : Nat) :
    (natToBits i == natToBits j) = (i == j) := by
  rw [list_bool_beq_eq]
  cases h : i == j with
  | true =>
    have hij : i = j := of_decide_eq_true h
    subst hij
    exact decide_eq_true rfl
  | false =>
    have hne : i ≠ j := of_decide_eq_false h
    exact decide_eq_false (fun hbits => hne (natToBits_injective hbits))

def BinTrie.empty {V : Type} : BinTrie V := .leaf

def BinTrie.get {V : Type} (t : BinTrie V) (idx : Nat) : Option V :=
  BinTrie.getBits t (natToBits idx)

def BinTrie.set {V : Type} (t : BinTrie V) (idx : Nat) (val : Option V) :
    BinTrie V :=
  BinTrie.setBits t (natToBits idx) val

theorem BinTrie.get_set {V : Type} (t : BinTrie V) (target : Nat)
    (val : Option V) (i : Nat) :
    BinTrie.get (BinTrie.set t target val) i =
      if i == target then val else BinTrie.get t i := by
  dsimp [BinTrie.get, BinTrie.set]
  rw [BinTrie.getBits_setBits, natToBits_beq]

/-!
### Canonical-Spine x86 State (`CanonX86State`)
-/

structure CanonCallFrame where
  callerBody : Option X86Body
  callerMem : BinTrie X86Val
  retSlot : SlotId
  retBlock : Nat

structure CanonX86State where
  mem : BinTrie X86Val
  bb : Nat
  ip : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option X86Body := none
  stack : List CanonCallFrame := []

def evalCanonOperand (mem : BinTrie X86Val) (op : X86Operand) :
    Option (X86Val × BinTrie X86Val) :=
  match op with
  | .stackSlot slot false =>
    match BinTrie.get mem slot.index with
    | some v => some (v, mem)
    | none => none
  | .stackSlot slot true =>
    match BinTrie.get mem slot.index with
    | some v => some (v, BinTrie.set mem slot.index none)
    | none => none
  | .imm v => some (v, mem)

def evalCanonInstr (cs : CanonX86State) (instr : X86Instr) :
    StepResult CanonX86State Unit X86Val :=
  match instr with
  | .mov dst src =>
    match evalCanonOperand cs.mem src with
    | some (v, mem') =>
      .step () { cs with
        mem := BinTrie.set mem' dst.index (some v)
        ip := cs.ip + 1
      }
    | none => .failed .ub
  | .alu op dst lhs rhs =>
    match evalCanonOperand cs.mem lhs with
    | some (v1, mem1) =>
      match evalCanonOperand mem1 rhs with
      | some (v2, mem2) =>
        match evalX86BinOp op v1 v2 with
        | some outVal =>
          .step () { cs with
            mem := BinTrie.set mem2 dst.index (some outVal)
            ip := cs.ip + 1
          }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .wrapAdt adtId dst src =>
    match evalCanonOperand cs.mem src with
    | some (v, mem') =>
      .step () { cs with
        mem := BinTrie.set mem' dst.index (some (.adt adtId v))
        ip := cs.ip + 1
      }
    | none => .failed .ub
  | .extractField0 dst src =>
    match BinTrie.get cs.mem src.index with
    | some (.adt _ inner) =>
      .step () { cs with
        mem := BinTrie.set cs.mem dst.index (some inner)
        ip := cs.ip + 1
      }
    | _ => .failed .ub
  | .leaSlot dst target =>
    match BinTrie.get cs.mem target.index with
    | some _ =>
      .step () { cs with
        mem := BinTrie.set cs.mem dst.index (some (.stackPtr target))
        ip := cs.ip + 1
      }
    | none => .failed .ub
  | .reborrowSlot dst srcPtr =>
    match BinTrie.get cs.mem srcPtr.index with
    | some (.stackPtr target) =>
      match BinTrie.get cs.mem target.index with
      | some _ =>
        .step () { cs with
          mem := BinTrie.set cs.mem dst.index (some (.stackPtr target))
          ip := cs.ip + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
  | .allocSlot slot =>
    .step () { cs with
      mem := BinTrie.set cs.mem slot.index none
      ip := cs.ip + 1
    }
  | .deallocSlot slot =>
    .step () { cs with
      mem := BinTrie.set cs.mem slot.index none
      ip := cs.ip + 1
    }
  | .nop =>
    .step () { cs with ip := cs.ip + 1 }

def evalCanonRepMovsb (tySizes : Nat → Nat) (mem : BinTrie X86Val)
    (srcTy dstTy : X86Ty) (ptrVal : X86Val) : Option X86Val :=
  let srcSz := evalX86TyByteSize tySizes srcTy
  let dstSz := evalX86TyByteSize tySizes dstTy
  if decide (srcSz = dstSz) then
    match ptrVal with
    | .stackPtr target =>
      match BinTrie.get mem target.index with
      | some (.bytes vSz bits) =>
        if decide (vSz = srcSz) then
          some (.bytes dstSz bits)
        else
          none
      | _ => none
    | _ => none
  else
    none

def evalCanonTerm (cs : CanonX86State) (term : X86Term) :
    StepResult CanonX86State Unit X86Val :=
  match term with
  | .ret =>
    match BinTrie.get cs.mem 0 with
    | none => .failed .ub
    | some retVal =>
      match cs.stack with
      | [] => .terminated (.normal retVal)
      | frame :: restStack =>
        .step () {
          mem := BinTrie.set frame.callerMem frame.retSlot.index (some retVal)
          bb := frame.retBlock
          ip := 0
          tySizes := cs.tySizes
          curBody := frame.callerBody
          stack := restStack
        }
  | .jmp target =>
    .step () { cs with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .abortPanic =>
    .terminated .unwind
  | .jccBool cond falseTarget trueTarget =>
    match evalCanonOperand cs.mem cond with
    | some (.boolVal false, mem') =>
      .step () { cs with mem := mem', bb := falseTarget.index, ip := 0 }
    | some (.boolVal true, mem') =>
      .step () { cs with mem := mem', bb := trueTarget.index, ip := 0 }
    | _ => .failed .ub
  | .movSizeOfJmp dst ty target =>
    let sz := evalX86TyByteSize cs.tySizes ty
    .step () { cs with
      mem := BinTrie.set cs.mem dst.index (some (.word64 sz))
      bb := target.index
      ip := 0
    }
  | .repMovsbJmp dst srcTy dstTy ptrOp target =>
    match evalCanonOperand cs.mem ptrOp with
    | some (ptrVal, mem') =>
      match evalCanonRepMovsb cs.tySizes mem' srcTy dstTy ptrVal with
      | some outVal =>
        .step () { cs with
          mem := BinTrie.set mem' dst.index (some outVal)
          bb := target.index
          ip := 0
        }
      | none => .failed .ub
    | none => .failed .ub
  | .call1 dst callee arg target =>
    match evalCanonOperand cs.mem arg with
    | some (argVal, callerMem') =>
      let calleeMem := BinTrie.set BinTrie.empty 1 (some argVal)
      let frame : CanonCallFrame := {
        callerBody := cs.curBody
        callerMem := callerMem'
        retSlot := dst
        retBlock := target.index
      }
      .step () {
        mem := calleeMem
        bb := 0
        ip := 0
        tySizes := cs.tySizes
        curBody := some callee
        stack := frame :: cs.stack
      }
    | none => .failed .ub

def evalCanonStep (rootBody : X86Body) (cs : CanonX86State) :
    StepResult CanonX86State Unit X86Val :=
  let active := cs.curBody.getD rootBody
  match active.blocks[cs.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[cs.ip]? with
    | some instr => evalCanonInstr cs instr
    | none => evalCanonTerm cs blk.term

/-- Multi-step canonical evaluator: executes `k` steps of `evalCanonStep` in a
single kernel reduction pass without constructing intermediate `ReachesPrefix`
proof obligations! -/
def evalCanonSteps (rootBody : X86Body) :
    Nat → CanonX86State → StepResult CanonX86State Unit X86Val
  | 0, cs => .step () cs
  | k + 1, cs =>
    match evalCanonStep rootBody cs with
    | .step () cs' => evalCanonSteps rootBody k cs'
    | .choice kind branches => .choice kind branches
    | .terminated term => .terminated term
    | .failed err => .failed err

/-!
## 4. Universal Simulation Between `CanonX86State` and `X86State`
-/

def MemSubsumed (cm : BinTrie X86Val) (m : Nat → Option X86Val) : Prop :=
  ∀ i v, BinTrie.get cm i = some v → m i = some v

theorem memSubsumed_set_some {cm : BinTrie X86Val} {m : Nat → Option X86Val}
    (hsub : MemSubsumed cm m) (dst : Nat) (val : X86Val) :
    MemSubsumed (BinTrie.set cm dst (some val))
      (updateSlot m dst (some val)) := by
  intro i v hget
  rw [BinTrie.get_set] at hget
  dsimp [updateSlot]
  cases h : i == dst with
  | true =>
    rw [h] at hget
    exact hget
  | false =>
    rw [h] at hget
    exact hsub i v hget

theorem memSubsumed_set_none {cm : BinTrie X86Val} {m : Nat → Option X86Val}
    (hsub : MemSubsumed cm m) (dst : Nat) :
    MemSubsumed (BinTrie.set cm dst none) (updateSlot m dst none) := by
  intro i v hget
  rw [BinTrie.get_set] at hget
  dsimp [updateSlot]
  cases h : i == dst with
  | true =>
    rw [h] at hget
    contradiction
  | false =>
    rw [h] at hget
    exact hsub i v hget

inductive StackSubsumed : List CanonCallFrame → List X86CallFrame → Prop where
  | nil : StackSubsumed [] []
  | cons {cf : CanonCallFrame} {f : X86CallFrame}
      {cfs : List CanonCallFrame} {fs : List X86CallFrame} :
      cf.callerBody = f.callerBody →
      MemSubsumed cf.callerMem f.callerMem →
      cf.retSlot = f.retSlot →
      cf.retBlock = f.retBlock →
      StackSubsumed cfs fs →
      StackSubsumed (cf :: cfs) (f :: fs)

structure StateSubsumed (cs : CanonX86State) (s : X86State) : Prop where
  mem_sub : MemSubsumed cs.mem s.mem
  bb_eq : cs.bb = s.bb
  ip_eq : cs.ip = s.ip
  tySizes_eq : cs.tySizes = s.tySizes
  curBody_eq : cs.curBody = s.curBody
  stack_sub : StackSubsumed cs.stack s.stack

theorem evalOperand_subsumed {cm : BinTrie X86Val} {m : Nat → Option X86Val}
    (hsub : MemSubsumed cm m) (op : X86Operand) (v : X86Val)
    (cm' : BinTrie X86Val)
    (heval : evalCanonOperand cm op = some (v, cm')) :
    ∃ m', evalX86Operand m op = some (v, m') ∧ MemSubsumed cm' m' := by
  cases op with
  | stackSlot slot consume =>
    cases consume with
    | false =>
      dsimp [evalCanonOperand] at heval
      cases hget : BinTrie.get cm slot.index with
      | none => rw [hget] at heval; contradiction
      | some val =>
        rw [hget] at heval
        injection heval with hp
        injection hp with hv hcm'
        subst hv hcm'
        have hm := hsub slot.index val hget
        refine ⟨m, ?_, hsub⟩
        dsimp [evalX86Operand]
        rw [hm]
    | true =>
      dsimp [evalCanonOperand] at heval
      cases hget : BinTrie.get cm slot.index with
      | none => rw [hget] at heval; contradiction
      | some val =>
        rw [hget] at heval
        injection heval with hp
        injection hp with hv hcm'
        subst hv hcm'
        have hm := hsub slot.index val hget
        refine ⟨updateSlot m slot.index none, ?_,
          memSubsumed_set_none hsub slot.index⟩
        dsimp [evalX86Operand]
        rw [hm]
  | imm val =>
    injection heval with hp
    injection hp with hv hcm'
    subst hv hcm'
    exact ⟨m, rfl, hsub⟩

theorem evalCanonInstr_simulates {cs : CanonX86State} {s : X86State}
    (hsub : StateSubsumed cs s) (instr : X86Instr) :
    (∀ cs', evalCanonInstr cs instr = .step () cs' →
      ∃ s', evalX86Instr s instr = .step () s' ∧ StateSubsumed cs' s') ∧
    (∀ term, evalCanonInstr cs instr = .terminated term →
      evalX86Instr s instr = .terminated term) := by
  constructor
  · intro cs' hstep
    cases instr with
    | mov dst src =>
      dsimp [evalCanonInstr] at hstep
      cases h1 : evalCanonOperand cs.mem src with
      | none => rw [h1] at hstep; contradiction
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk v cm' =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          cases evalOperand_subsumed hsub.mem_sub src v cm' h1 with
          | intro m' hm' =>
            refine ⟨{ s with mem := updateSlot m' dst.index (some v), ip := s.ip + 1 }, ?_⟩
            refine ⟨?_, ?_⟩
            · dsimp [evalX86Instr]; rw [hm'.1]
            · exact ⟨memSubsumed_set_some hm'.2 dst.index v,
                hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                hsub.curBody_eq, hsub.stack_sub⟩
    | alu op dst lhs rhs =>
      dsimp [evalCanonInstr] at hstep
      cases h1 : evalCanonOperand cs.mem lhs with
      | none => rw [h1] at hstep; contradiction
      | some p1 =>
        rw [h1] at hstep
        cases p1 with
        | mk v1 cm1 =>
          dsimp at hstep
          cases h2 : evalCanonOperand cm1 rhs with
          | none => rw [h2] at hstep; contradiction
          | some p2 =>
            rw [h2] at hstep
            cases p2 with
            | mk v2 cm2 =>
              dsimp at hstep
              cases h3 : evalX86BinOp op v1 v2 with
              | none => rw [h3] at hstep; contradiction
              | some outVal =>
                rw [h3] at hstep
                injection hstep with _ hcs'
                subst hcs'
                cases evalOperand_subsumed hsub.mem_sub lhs v1 cm1 h1 with
                | intro m1 hm1 =>
                  cases evalOperand_subsumed hm1.2 rhs v2 cm2 h2 with
                  | intro m2 hm2 =>
                    refine ⟨{ s with mem := updateSlot m2 dst.index (some outVal), ip := s.ip + 1 }, ?_⟩
                    refine ⟨?_, ?_⟩
                    · dsimp [evalX86Instr]; rw [hm1.1]; dsimp; rw [hm2.1]; dsimp; rw [h3]
                    · exact ⟨memSubsumed_set_some hm2.2 dst.index outVal,
                        hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                        hsub.curBody_eq, hsub.stack_sub⟩
    | wrapAdt adtId dst src =>
      dsimp [evalCanonInstr] at hstep
      cases h1 : evalCanonOperand cs.mem src with
      | none => rw [h1] at hstep; contradiction
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk v cm' =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          cases evalOperand_subsumed hsub.mem_sub src v cm' h1 with
          | intro m' hm' =>
            refine ⟨{ s with mem := updateSlot m' dst.index (some (.adt adtId v)), ip := s.ip + 1 }, ?_⟩
            refine ⟨?_, ?_⟩
            · dsimp [evalX86Instr]; rw [hm'.1]
            · exact ⟨memSubsumed_set_some hm'.2 dst.index (.adt adtId v),
                hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                hsub.curBody_eq, hsub.stack_sub⟩
    | extractField0 dst src =>
      dsimp [evalCanonInstr] at hstep
      cases h1 : BinTrie.get cs.mem src.index with
      | none => rw [h1] at hstep; contradiction
      | some v =>
        rw [h1] at hstep
        cases v with
        | adt adtId inner =>
          injection hstep with _ hcs'
          subst hcs'
          have hm1 := hsub.mem_sub src.index (.adt adtId inner) h1
          refine ⟨{ s with mem := updateSlot s.mem dst.index (some inner), ip := s.ip + 1 }, ?_⟩
          refine ⟨?_, ?_⟩
          · dsimp [evalX86Instr]; rw [hm1]
          · exact ⟨memSubsumed_set_some hsub.mem_sub dst.index inner,
              hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
              hsub.curBody_eq, hsub.stack_sub⟩
        | _ => contradiction
    | leaSlot dst target =>
      dsimp [evalCanonInstr] at hstep
      cases h1 : BinTrie.get cs.mem target.index with
      | none => rw [h1] at hstep; contradiction
      | some v =>
        rw [h1] at hstep
        injection hstep with _ hcs'
        subst hcs'
        have hm1 := hsub.mem_sub target.index v h1
        refine ⟨{ s with mem := updateSlot s.mem dst.index (some (.stackPtr target)), ip := s.ip + 1 }, ?_⟩
        refine ⟨?_, ?_⟩
        · dsimp [evalX86Instr]; rw [hm1]
        · exact ⟨memSubsumed_set_some hsub.mem_sub dst.index (.stackPtr target),
            hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
            hsub.curBody_eq, hsub.stack_sub⟩
    | reborrowSlot dst srcPtr =>
      dsimp [evalCanonInstr] at hstep
      cases h1 : BinTrie.get cs.mem srcPtr.index with
      | none => rw [h1] at hstep; contradiction
      | some pv =>
        rw [h1] at hstep
        cases pv with
        | stackPtr target =>
          dsimp at hstep
          cases h2 : BinTrie.get cs.mem target.index with
          | none => rw [h2] at hstep; contradiction
          | some tv =>
            rw [h2] at hstep
            injection hstep with _ hcs'
            subst hcs'
            have hm1 := hsub.mem_sub srcPtr.index (.stackPtr target) h1
            have hm2 := hsub.mem_sub target.index tv h2
            refine ⟨{ s with mem := updateSlot s.mem dst.index (some (.stackPtr target)), ip := s.ip + 1 }, ?_⟩
            refine ⟨?_, ?_⟩
            · dsimp [evalX86Instr]; rw [hm1]; dsimp; rw [hm2]
            · exact ⟨memSubsumed_set_some hsub.mem_sub dst.index
                  (.stackPtr target),
                hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                hsub.curBody_eq, hsub.stack_sub⟩
        | _ => contradiction
    | allocSlot slot =>
      dsimp [evalCanonInstr] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨memSubsumed_set_none hsub.mem_sub slot.index,
        hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
        hsub.curBody_eq, hsub.stack_sub⟩⟩
    | deallocSlot slot =>
      dsimp [evalCanonInstr] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨memSubsumed_set_none hsub.mem_sub slot.index,
        hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
        hsub.curBody_eq, hsub.stack_sub⟩⟩
    | nop =>
      dsimp [evalCanonInstr] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨hsub.mem_sub, hsub.bb_eq, by dsimp; rw [hsub.ip_eq],
        hsub.tySizes_eq, hsub.curBody_eq, hsub.stack_sub⟩⟩
  · intro term hterm
    cases instr with
    | mov dst src =>
      dsimp [evalCanonInstr] at hterm
      cases h1 : evalCanonOperand cs.mem src <;> rw [h1] at hterm <;> contradiction
    | alu op dst lhs rhs =>
      dsimp [evalCanonInstr] at hterm
      cases h1 : evalCanonOperand cs.mem lhs <;> rw [h1] at hterm
      · contradiction
      · rename_i p1
        cases p1 with
        | mk v1 cm1 =>
          dsimp at hterm
          cases h2 : evalCanonOperand cm1 rhs <;> rw [h2] at hterm
          · contradiction
          · rename_i p2
            cases p2 with
            | mk v2 cm2 =>
              dsimp at hterm
              cases h3 : evalX86BinOp op v1 v2 <;> rw [h3] at hterm <;> contradiction
    | wrapAdt adtId dst src =>
      dsimp [evalCanonInstr] at hterm
      cases h1 : evalCanonOperand cs.mem src <;> rw [h1] at hterm <;> contradiction
    | extractField0 dst src =>
      dsimp [evalCanonInstr] at hterm
      cases h1 : BinTrie.get cs.mem src.index <;> rw [h1] at hterm
      · contradiction
      · rename_i v; cases v <;> contradiction
    | leaSlot dst target =>
      dsimp [evalCanonInstr] at hterm
      cases h1 : BinTrie.get cs.mem target.index <;> rw [h1] at hterm <;> contradiction
    | reborrowSlot dst srcPtr =>
      dsimp [evalCanonInstr] at hterm
      cases h1 : BinTrie.get cs.mem srcPtr.index <;> rw [h1] at hterm
      · contradiction
      · rename_i pv
        cases pv <;> try contradiction
        rename_i target
        dsimp at hterm
        cases h2 : BinTrie.get cs.mem target.index <;> rw [h2] at hterm <;> contradiction
    | allocSlot _ => contradiction
    | deallocSlot _ => contradiction
    | nop => contradiction

theorem evalRepMovsb_subsumed {tySizes : Nat → Nat} {cm : BinTrie X86Val}
    {m : Nat → Option X86Val} (hsub : MemSubsumed cm m)
    (srcTy dstTy : X86Ty) (ptrVal outVal : X86Val)
    (heval : evalCanonRepMovsb tySizes cm srcTy dstTy ptrVal = some outVal) :
    evalRepMovsb tySizes m srcTy dstTy ptrVal = some outVal := by
  dsimp [evalCanonRepMovsb, evalRepMovsb] at heval ⊢
  cases hsz : decide (evalX86TyByteSize tySizes srcTy =
      evalX86TyByteSize tySizes dstTy) with
  | false => rw [hsz] at heval; contradiction
  | true =>
    rw [hsz] at heval
    dsimp at heval ⊢
    cases ptrVal with
    | stackPtr target =>
      dsimp at heval ⊢
      cases hget : BinTrie.get cm target.index with
      | none => rw [hget] at heval; contradiction
      | some v =>
        rw [hget] at heval
        have hm := hsub target.index v hget
        rw [hm]
        exact heval
    | _ => contradiction

theorem evalCanonTerm_simulates {cs : CanonX86State} {s : X86State}
    (hsub : StateSubsumed cs s) (term : X86Term) :
    (∀ cs', evalCanonTerm cs term = .step () cs' →
      ∃ s', evalX86Term s term = .step () s' ∧ StateSubsumed cs' s') ∧
    (∀ tk, evalCanonTerm cs term = .terminated tk →
      evalX86Term s term = .terminated tk) := by
  cases cs with
  | mk cmem cbb cip cty ccur cstack =>
  cases s with
  | mk smem sbb sip sty scur sstack =>
  cases hsub with
  | mk hmem_sub hbb_eq hip_eq hty_eq hcur_eq hstack_sub =>
  dsimp at hmem_sub hbb_eq hip_eq hty_eq hcur_eq hstack_sub
  subst hbb_eq hip_eq hty_eq hcur_eq
  constructor
  · intro cs' hstep
    cases term with
    | ret =>
      dsimp [evalCanonTerm] at hstep
      cases h0 : BinTrie.get cmem 0 with
      | none => rw [h0] at hstep; contradiction
      | some retVal =>
        rw [h0] at hstep
        have hm0 := hmem_sub 0 retVal h0
        cases hstack_sub with
        | nil => contradiction
        | @cons cf f cfs fs hbody hmem hslot hblk hrest =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          refine ⟨{ mem := updateSlot f.callerMem f.retSlot.index (some retVal),
                    bb := f.retBlock, ip := 0, tySizes := cty,
                    curBody := f.callerBody, stack := fs }, ?_⟩
          refine ⟨?_, ?_⟩
          · dsimp [evalX86Term]; rw [hm0]
          · exact ⟨by dsimp; rw [hslot]; exact memSubsumed_set_some hmem f.retSlot.index retVal,
              hblk, rfl, rfl, hbody, hrest⟩
    | jmp target =>
      dsimp [evalCanonTerm] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨hmem_sub, rfl, rfl, rfl, rfl, hstack_sub⟩⟩
    | ud2 => contradiction
    | abortPanic => contradiction
    | jccBool cond falseTarget trueTarget =>
      dsimp [evalCanonTerm] at hstep
      cases h1 : evalCanonOperand cmem cond with
      | none => rw [h1] at hstep; contradiction
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk cv cm' =>
          cases cv with
          | boolVal b =>
            cases b with
            | false =>
              dsimp at hstep
              injection hstep with _ hcs'
              subst hcs'
              cases evalOperand_subsumed hmem_sub cond (.boolVal false) cm' h1 with
              | intro m' hm' =>
                refine ⟨{ mem := m', bb := falseTarget.index, ip := 0,
                          tySizes := cty, curBody := ccur, stack := sstack }, ?_⟩
                refine ⟨?_, ?_⟩
                · dsimp [evalX86Term]; rw [hm'.1]
                · exact ⟨hm'.2, rfl, rfl, rfl, rfl, hstack_sub⟩
            | true =>
              dsimp at hstep
              injection hstep with _ hcs'
              subst hcs'
              cases evalOperand_subsumed hmem_sub cond (.boolVal true) cm' h1 with
              | intro m' hm' =>
                refine ⟨{ mem := m', bb := trueTarget.index, ip := 0,
                          tySizes := cty, curBody := ccur, stack := sstack }, ?_⟩
                refine ⟨?_, ?_⟩
                · dsimp [evalX86Term]; rw [hm'.1]
                · exact ⟨hm'.2, rfl, rfl, rfl, rfl, hstack_sub⟩
          | _ => contradiction
    | movSizeOfJmp dst ty target =>
      dsimp [evalCanonTerm] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨memSubsumed_set_some hmem_sub dst.index
          (.word64 (evalX86TyByteSize cty ty)),
        rfl, rfl, rfl, rfl, hstack_sub⟩⟩
    | repMovsbJmp dst srcTy dstTy ptrOp target =>
      dsimp [evalCanonTerm] at hstep
      cases h1 : evalCanonOperand cmem ptrOp with
      | none => rw [h1] at hstep; contradiction
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk ptrVal cm' =>
          dsimp at hstep
          cases h2 : evalCanonRepMovsb cty cm' srcTy dstTy ptrVal with
          | none => rw [h2] at hstep; contradiction
          | some outVal =>
            rw [h2] at hstep
            injection hstep with _ hcs'
            subst hcs'
            cases evalOperand_subsumed hmem_sub ptrOp ptrVal cm' h1 with
            | intro m' hm' =>
              have h2' := evalRepMovsb_subsumed hm'.2 srcTy dstTy ptrVal outVal h2
              refine ⟨{ mem := updateSlot m' dst.index (some outVal),
                        bb := target.index, ip := 0, tySizes := cty,
                        curBody := ccur, stack := sstack }, ?_⟩
              refine ⟨?_, ?_⟩
              · dsimp [evalX86Term]; rw [hm'.1]; dsimp; rw [h2']
              · exact ⟨memSubsumed_set_some hm'.2 dst.index outVal,
                  rfl, rfl, rfl, rfl, hstack_sub⟩
    | call1 dst callee arg target =>
      dsimp [evalCanonTerm] at hstep
      cases h1 : evalCanonOperand cmem arg with
      | none => rw [h1] at hstep; contradiction
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk argVal cm' =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          cases evalOperand_subsumed hmem_sub arg argVal cm' h1 with
          | intro m' hm' =>
            have hcallee : MemSubsumed
                (BinTrie.set BinTrie.empty 1 (some argVal))
                (updateSlot (fun _ => none) 1 (some argVal)) := by
              apply memSubsumed_set_some
              intro i v hget
              contradiction
            refine ⟨{ mem := updateSlot (fun _ => none) 1 (some argVal),
                      bb := 0, ip := 0, tySizes := cty,
                      curBody := some callee,
                      stack := { callerBody := ccur, callerMem := m',
                                 retSlot := dst, retBlock := target.index } :: sstack }, ?_⟩
            refine ⟨?_, ?_⟩
            · dsimp [evalX86Term]; rw [hm'.1]
            · exact ⟨hcallee, rfl, rfl, rfl, rfl,
                StackSubsumed.cons rfl hm'.2 rfl rfl hstack_sub⟩
  · intro tk hterm
    cases term with
    | ret =>
      dsimp [evalCanonTerm] at hterm
      cases h0 : BinTrie.get cmem 0 with
      | none => rw [h0] at hterm; contradiction
      | some retVal =>
        rw [h0] at hterm
        have hm0 := hmem_sub 0 retVal h0
        cases hstack_sub with
        | nil =>
          dsimp at hterm
          injection hterm with htk
          subst htk
          dsimp [evalX86Term]
          rw [hm0]
        | cons _ _ _ _ _ => contradiction
    | jmp _ => contradiction
    | ud2 => contradiction
    | abortPanic =>
      dsimp [evalCanonTerm] at hterm
      injection hterm with htk
      subst htk
      rfl
    | jccBool cond _ _ =>
      dsimp [evalCanonTerm] at hterm
      cases h1 : evalCanonOperand cmem cond <;> rw [h1] at hterm
      · contradiction
      · rename_i p
        cases p with
        | mk cv cm' =>
          cases cv <;> try contradiction
          rename_i b
          cases b <;> contradiction
    | movSizeOfJmp _ _ _ => contradiction
    | repMovsbJmp _ srcTy dstTy ptrOp _ =>
      dsimp [evalCanonTerm] at hterm
      cases h1 : evalCanonOperand cmem ptrOp <;> rw [h1] at hterm
      · contradiction
      · rename_i p
        cases p with
        | mk pv cm' =>
          dsimp at hterm
          cases h2 : evalCanonRepMovsb cty cm' srcTy dstTy pv <;>
            rw [h2] at hterm <;> contradiction
    | call1 _ _ arg _ =>
      dsimp [evalCanonTerm] at hterm
      cases h1 : evalCanonOperand cmem arg <;> rw [h1] at hterm <;> contradiction

theorem evalCanonStep_simulates (rootBody : X86Body) {cs : CanonX86State}
    {s : X86State} (hsub : StateSubsumed cs s) :
    (∀ cs', evalCanonStep rootBody cs = .step () cs' →
      ∃ s', evalX86Step rootBody s = .step () s' ∧ StateSubsumed cs' s') ∧
    (∀ tk, evalCanonStep rootBody cs = .terminated tk →
      evalX86Step rootBody s = .terminated tk) := by
  dsimp [evalCanonStep, evalX86Step]
  rw [← hsub.curBody_eq, ← hsub.bb_eq, ← hsub.ip_eq]
  cases (cs.curBody.getD rootBody).blocks[cs.bb]? with
  | none =>
    refine ⟨?_, ?_⟩ <;> intro _ h <;> contradiction
  | some blk =>
    dsimp
    cases blk.instrs[cs.ip]? with
    | some instr => exact evalCanonInstr_simulates hsub instr
    | none => exact evalCanonTerm_simulates hsub blk.term

/-- Multi-step bridge theorem 1: if `evalCanonSteps body k cs` terminates with
`.terminated (.normal v)` (checked by `rfl`!), then `SafeAndEnsures P out` holds
for the concrete `X86Machine`! -/
theorem reachesPrefix_safeAndEnsures_of_canonSteps_normal
    {body : X86Body} {init s : X86State} {cs : CanonX86State}
    {n : Nat} {tr : List Unit} {out : PrefixOutcome X86Val}
    {P : X86Val → Prop} {v : X86Val} (k : Nat)
    (hsub : StateSubsumed cs s)
    (hsteps : evalCanonSteps body k cs = .terminated (.normal v))
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  induction k generalizing cs s n tr with
  | zero => contradiction
  | succ k' ih =>
    dsimp [evalCanonSteps] at hsteps
    cases h1 : evalCanonStep body cs with
    | step u cs' =>
      rw [h1] at hsteps
      cases u
      cases (evalCanonStep_simulates body hsub).1 cs' h1 with
      | intro s' hs' =>
        exact reachesPrefix_safeAndEnsures_of_step hs'.1 hreach
          (fun n' tr' hr' => ih hs'.2 hsteps hr')
    | choice _ _ =>
      rw [h1] at hsteps; contradiction
    | terminated tk =>
      rw [h1] at hsteps
      injection hsteps with htk
      subst htk
      have hs_term := (evalCanonStep_simulates body hsub).2 (.normal v) h1
      exact reachesPrefix_safeAndEnsures_of_normal hs_term hreach hPv
    | failed _ =>
      rw [h1] at hsteps; contradiction

/-- Multi-step bridge theorem 2: if `evalCanonSteps body k cs = .step () cs'`
(checked by `rfl`!), then `SafeAndEnsures P out` reduces in one hop to
`cs'`! -/
theorem reachesPrefix_safeAndEnsures_of_canonSteps_step
    {body : X86Body} {init s : X86State} {cs cs' : CanonX86State}
    {n : Nat} {tr : List Unit} {out : PrefixOutcome X86Val}
    {P : X86Val → Prop} (k : Nat)
    (hsub : StateSubsumed cs s)
    (hsteps : evalCanonSteps body k cs = .step () cs')
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hnext : ∀ s' n' tr',
      StateSubsumed cs' s' →
      ReachesPrefix X86Machine body init n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  induction k generalizing cs s n tr with
  | zero =>
    injection hsteps with _ hcs
    subst hcs
    exact hnext s n tr hsub hreach
  | succ k' ih =>
    dsimp [evalCanonSteps] at hsteps
    cases h1 : evalCanonStep body cs with
    | step u cs_mid =>
      rw [h1] at hsteps
      cases u
      cases (evalCanonStep_simulates body hsub).1 cs_mid h1 with
      | intro s_mid hs_mid =>
        exact reachesPrefix_safeAndEnsures_of_step hs_mid.1 hreach
          (fun n' tr' hr' => ih hs_mid.2 hsteps hr')
    | choice _ _ =>
      rw [h1] at hsteps; contradiction
    | terminated _ =>
      rw [h1] at hsteps; contradiction
    | failed _ =>
      rw [h1] at hsteps; contradiction

/-!
## 5. Entry Frame Initialization (`initCanonState`)
-/

def BinTrie.initArgs (args : List X86Val) : BinTrie X86Val :=
  let rec loop : Nat → List X86Val → BinTrie X86Val → BinTrie X86Val
    | _, [], acc => acc
    | idx, a :: rest, acc => loop (idx + 1) rest (BinTrie.set acc idx (some a))
  loop 1 args BinTrie.empty

def initCanonState (tySizes : Nat → Nat) (args : List X86Val) :
    CanonX86State where
  mem := BinTrie.initArgs args
  bb := 0
  ip := 0
  tySizes := tySizes
  curBody := none
  stack := []

theorem initCanonState_subsumed_2 {s : X86State} {v1 v2 : X86Val}
    (hb : s.bb = 0) (hip : s.ip = 0) (hc : s.curBody = none)
    (hst : s.stack = [])
    (hv1 : s.mem 1 = some v1) (hv2 : s.mem 2 = some v2) :
    StateSubsumed (initCanonState s.tySizes [v1, v2]) s := by
  refine ⟨?_, hb.symm, hip.symm, rfl, hc.symm, ?_⟩
  · intro i v hget
    dsimp [initCanonState, BinTrie.initArgs, BinTrie.initArgs.loop] at hget
    rw [BinTrie.get_set] at hget
    cases h2 : i == 2 with
    | true =>
      rw [h2] at hget
      injection hget with hv
      subst hv
      have hi2 : i = 2 := of_decide_eq_true h2
      subst hi2
      exact hv2
    | false =>
      rw [h2] at hget
      rw [BinTrie.get_set] at hget
      cases h1 : i == 1 with
      | true =>
        rw [h1] at hget
        injection hget with hv
        subst hv
        have hi1 : i = 1 := of_decide_eq_true h1
        subst hi1
        exact hv1
      | false =>
        rw [h1] at hget
        contradiction
  · rw [hst]
    exact StackSubsumed.nil

/-!
## 6. End-to-End Proofs on `Trusted.X86Machine`

### Demo A: Exact `maxUsizeBody` from `MirLemmas.lean`

In `MirLemmas.lean` (lines 1263–1394), verifying `maxUsizeBody` took **132
lines** of manual `updateSlot` unfolding (`change (if 1 == 4 then none else ...)
= _`).
Using `CanonX86State` and `reachesPrefix_safeAndEnsures_of_canonSteps_*`, the
entire symbolic execution is **14 lines** with zero manual `updateSlot`
lemmas!
-/

def maxUsizeBody : X86Body where
  argTys := [.usize, .usize]
  retTy := .usize
  slotCount := 6
  blocks := [
    -- bb0:
    { instrs := [
        .allocSlot ⟨3⟩,
        .allocSlot ⟨4⟩,
        .mov ⟨4⟩ (.stackSlot ⟨1⟩ false),
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨2⟩ false),
        .alu .lt ⟨3⟩ (.stackSlot ⟨4⟩ true) (.stackSlot ⟨5⟩ true)
      ]
      term := .jccBool (.stackSlot ⟨3⟩ true) ⟨2⟩ ⟨1⟩ },
    -- bb1 (true branch: a < b):
    { instrs := [
        .deallocSlot ⟨5⟩,
        .deallocSlot ⟨4⟩,
        .mov ⟨0⟩ (.stackSlot ⟨2⟩ false)
      ]
      term := .jmp ⟨3⟩ },
    -- bb2 (false branch: ¬(a < b)):
    { instrs := [
        .deallocSlot ⟨5⟩,
        .deallocSlot ⟨4⟩,
        .mov ⟨0⟩ (.stackSlot ⟨1⟩ false)
      ]
      term := .jmp ⟨3⟩ },
    -- bb3 (join point):
    { instrs := [
        .deallocSlot ⟨3⟩
      ]
      term := .ret }
  ]

theorem maxUsize_canon_verified (init : X86State) (n : Nat) (tr : List Unit)
    (out : PrefixOutcome X86Val)
    (hinit : initX86State maxUsizeBody init)
    (hreach : ReachesPrefix X86Machine maxUsizeBody init n init tr out) :
    SafeAndEnsures (fun _ => True) out := by
  cases hinit.2.2.2.2.2.1 with
  | intro v1 hv1_pair =>
  cases hinit.2.2.2.2.2.2.1 with
  | intro v2 hv2_pair =>
    cases v1 with
    | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hv1_pair.2
    | word64 a =>
      cases v2 with
      | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hv2_pair.2
      | word64 b =>
        have hsub0 := initCanonState_subsumed_2 hinit.1 hinit.2.1 hinit.2.2.1
          hinit.2.2.2.1 hv1_pair.1 hv2_pair.1
        -- Execute all 6 instructions of bb0 in a single `rfl` step!
        refine reachesPrefix_safeAndEnsures_of_canonSteps_step 6 hsub0 rfl hreach
          (fun s_term n_term tr_term hsub_term hr_term => ?_)
        -- Split on the branch condition `decide (a < b)`: each branch executes
        -- its basic block + bb3 + `.ret` in a single `rfl` step!
        cases hlt : decide (a < b) with
        | false =>
          rw [hlt] at hsub_term
          exact reachesPrefix_safeAndEnsures_of_canonSteps_normal 7
            hsub_term rfl hr_term True.intro
        | true =>
          rw [hlt] at hsub_term
          exact reachesPrefix_safeAndEnsures_of_canonSteps_normal 7
            hsub_term rfl hr_term True.intro

/-!
### Demo B: Asymmetric Diamond CFG with Canonical Join-Point Merging by `rfl`

Consider a diamond CFG `diamondJoinBody` where:
- `bb0` compares `slot 1` (`a`) and `slot 2` (`b`) and branches to `bb1` or `bb2`.
- `bb1` allocates temporary `slot 4`, copies `slot 1` through `slot 4` into
  `slot 6`, deallocates `slot 4`, and jumps to `bb3`.
- `bb2` allocates a DIFFERENT temporary `slot 5`, copies `slot 1` through
  `slot 5` into `slot 6`, deallocates `slot 5`, and jumps to `bb3`.
- `bb3` (the shared post-join suffix block) deallocates `slot 3`, adds `slot 6`
  and `slot 2` into return `slot 0`, deallocates `slot 6`, and returns (`ret`).

At the entry to `bb3`, both branches (`bb1` and `bb2`) produce the **exact same
canonical `CanonX86State` by `rfl`**, so `bb3` is verified **only once**!
-/

def diamondJoinBody : X86Body where
  argTys := [.usize, .usize]
  retTy := .usize
  slotCount := 7
  blocks := [
    -- bb0:
    { instrs := [
        .allocSlot ⟨3⟩,
        .alu .lt ⟨3⟩ (.stackSlot ⟨1⟩ false) (.stackSlot ⟨2⟩ false)
      ]
      term := .jccBool (.stackSlot ⟨3⟩ true) ⟨2⟩ ⟨1⟩ },
    -- bb1 (uses temporary slot 4):
    { instrs := [
        .allocSlot ⟨4⟩,
        .mov ⟨4⟩ (.stackSlot ⟨1⟩ false),
        .allocSlot ⟨6⟩,
        .mov ⟨6⟩ (.stackSlot ⟨4⟩ true),
        .deallocSlot ⟨4⟩
      ]
      term := .jmp ⟨3⟩ },
    -- bb2 (uses temporary slot 5):
    { instrs := [
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨1⟩ false),
        .allocSlot ⟨6⟩,
        .mov ⟨6⟩ (.stackSlot ⟨5⟩ true),
        .deallocSlot ⟨5⟩
      ]
      term := .jmp ⟨3⟩ },
    -- bb3 (shared join-point suffix block):
    { instrs := [
        .deallocSlot ⟨3⟩,
        .alu .add ⟨0⟩ (.stackSlot ⟨6⟩ true) (.stackSlot ⟨2⟩ false),
        .deallocSlot ⟨6⟩
      ]
      term := .ret }
  ]

theorem diamondJoin_canon_verified (init : X86State) (n : Nat) (tr : List Unit)
    (out : PrefixOutcome X86Val)
    (hinit : initX86State diamondJoinBody init)
    (hreach : ReachesPrefix X86Machine diamondJoinBody init n init tr out) :
    SafeAndEnsures (fun _ => True) out := by
  cases hinit.2.2.2.2.2.1 with
  | intro v1 hv1_pair =>
  cases hinit.2.2.2.2.2.2.1 with
  | intro v2 hv2_pair =>
    cases v1 with
    | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hv1_pair.2
    | word64 a =>
      cases v2 with
      | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hv2_pair.2
      | word64 b =>
        have hsub0 := initCanonState_subsumed_2 hinit.1 hinit.2.1 hinit.2.2.1
          hinit.2.2.2.1 hv1_pair.1 hv2_pair.1
        -- Define the canonical state at join point `bb3` (`bb = 3, ip = 0`):
        let cs_bb3 : CanonX86State := {
          mem := BinTrie.set (BinTrie.initArgs [.word64 a, .word64 b]) 6
            (some (.word64 a))
          bb := 3
          ip := 0
          tySizes := init.tySizes
          curBody := none
          stack := []
        }
        -- Prove the shared post-join suffix `bb3` ONCE!
        have hJoin : ∀ s_bb3 n_bb3 tr_bb3,
            StateSubsumed cs_bb3 s_bb3 →
            ReachesPrefix X86Machine diamondJoinBody init n_bb3 s_bb3 tr_bb3 out →
            SafeAndEnsures (fun _ => True) out := by
          intro s_bb3 n_bb3 tr_bb3 hsub_bb3 hr_bb3
          exact reachesPrefix_safeAndEnsures_of_canonSteps_normal 4
            hsub_bb3 rfl hr_bb3 True.intro
        -- Step `bb0` (2 instructions)
        refine reachesPrefix_safeAndEnsures_of_canonSteps_step 2 hsub0 rfl hreach
          (fun s_br n_br tr_br hsub_br hr_br => ?_)
        -- Both branches step 7 instructions to `bb3` and unify with `cs_bb3`
        -- by `rfl`!
        cases hlt : decide (a < b) with
        | false =>
          rw [hlt] at hsub_br
          exact reachesPrefix_safeAndEnsures_of_canonSteps_step 7
            hsub_br rfl hr_br hJoin
        | true =>
          rw [hlt] at hsub_br
          exact reachesPrefix_safeAndEnsures_of_canonSteps_step 7
            hsub_br rfl hr_br hJoin

end RefinementBridge
