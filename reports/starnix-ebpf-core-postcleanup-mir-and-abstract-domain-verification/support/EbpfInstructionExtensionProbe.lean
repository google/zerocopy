-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

/-!
# Q-A2: Minimal Syntax & Operational Semantics Extension for `EbpfInstruction`

This self-contained Lean 4.34.1 probe mechanizes the exact minimal delta over
`Trusted.Mvp.Syntax` and `Trusted.Mvp.Semantics` required to capture, execute,
and verify the Fuchsia Starnix `ebpf_core::api::EbpfInstruction` bitfield
accessor and mutator suite (`get`, `code`, `set_code`, `dst_reg`, `set_dst_reg`,
`src_reg`, `set_src_reg`, `offset`, `set_offset`, `imm`, `set_imm`) from their
exact `Runtime(PostCleanup)` MIR (`candidate_mir_extracts.txt`, `def_id` 27–37).

## Summary of the Minimal Semantic Delta Over `Trusted.Mvp`
1. **Types (`Ty`)**:
   - `.struct1 (fieldTy : Ty)`: 1-field transparent/newtype struct (`EbpfInstruction(u64)`).
   - `.ref (isMut : Bool) (pointee : Ty)`: shared (`&T`) and mutable (`&mut T`)
     no-aliasing reference parameter slots.
2. **Places & Projections (`ProjectionElem`, `Place`, `Operand`)**:
   - `ProjectionElem`: `.deref` (`*p`) and `.field (index : Nat)` (`.0`).
   - `Place`: `{ localIdx : Local, projection : List ProjectionElem := [] }`.
3. **Rvalues & Statements (`UnOp.not`, `Rvalue.castInt`, `Rvalue.aggregateStruct1`, `Statement.assignPlace`)**:
   - `UnOp.not`: bitwise logical complement (`!0x00ff_u64`, `!0x0f00_u64`, etc.).
   - `Rvalue.castInt (targetTy : Ty) (operand : Operand)`: Rust Reference `IntToInt`
     numeric cast (`u64 -> u8`, `u64 -> u16 -> i16`, `u64 -> u32 -> i32`,
     `u8 -> u64`, `i16 -> u16 -> u64`, `i32 -> u32 -> u64`).
   - `Rvalue.aggregateStruct1 (structTy : Ty) (operand : Operand)`: 1-field
     ADT constructor `api::EbpfInstruction(move _4)`.
   - `Statement.assignPlace (dest : Place) (rvalue : Rvalue)`: supports both
     direct local assignment (`dest.projection = []`) and dereferenced `&mut`
     assignment (`(*_1) = move _3`, `dest = ⟨1, [.deref]⟩`).
   - `Terminator.panic`: models `core::panicking::panic(...) -> unwind continue`
     in the assertion-failure branches of `set_dst_reg` and `set_src_reg` as
     `.fault .assertionFailed`.
-/

namespace EbpfInstructionExtensionProbe

abbrev Word := BitVec 64
abbrev Local := Nat
abbrev BlockId := Nat

inductive Ty where
  | unit
  | bool
  | int (bits : Nat) (signed : Bool)
  | enumTy (discriminants : List (Nat × Word))
  | never
  | struct1 (fieldTy : Ty)
  | ref (isMut : Bool) (pointee : Ty)
  deriving DecidableEq, Repr

def tyEq : Ty → Ty → Bool
  | .unit, .unit => true
  | .bool, .bool => true
  | .int b1 s1, .int b2 s2 => b1 == b2 && s1 == s2
  | .never, .never => true
  | .struct1 t1, .struct1 t2 => tyEq t1 t2
  | .ref m1 t1, .ref m2 t2 => m1 == m2 && tyEq t1 t2
  | .enumTy d1, .enumTy d2 => d1 == d2
  | _, _ => false

instance : BEq Ty := ⟨tyEq⟩

inductive ProjectionElem where
  | deref
  | field (index : Nat)
  deriving DecidableEq, Repr

structure Place where
  localIdx : Local
  projection : List ProjectionElem := []
  deriving DecidableEq, Repr

def Place.ofLocal (idx : Local) : Place := ⟨idx, []⟩
def Place.derefLocal (idx : Local) : Place := ⟨idx, [.deref]⟩
def Place.derefField0 (idx : Local) : Place := ⟨idx, [.deref, .field 0]⟩

inductive Operand where
  | copy (place : Place)
  | move (place : Place)
  | constant (ty : Ty) (value : Word)
  deriving DecidableEq, Repr

def Operand.copyLocal (idx : Local) : Operand := .copy (Place.ofLocal idx)
def Operand.moveLocal (idx : Local) : Operand := .move (Place.ofLocal idx)

inductive BinOp where
  | add | sub | mul | div | rem
  | bitXor | bitAnd | bitOr | shl | shr
  | eq | lt | le | ne | ge | gt
  deriving DecidableEq, Repr

inductive UnOp where
  | neg
  | not
  deriving DecidableEq, Repr

inductive Rvalue where
  | use (operand : Operand) (preserveSource : Bool := false)
  | binary (op : BinOp) (left : Operand) (right : Operand)
  | unary (op : UnOp) (operand : Operand)
  | castInt (targetTy : Ty) (operand : Operand)
  | aggregateStruct1 (structTy : Ty) (operand : Operand)
  deriving DecidableEq, Repr

inductive Statement where
  | assign (dest : Place) (rvalue : Rvalue)
  | storageLive (slot : Local)
  | storageDead (slot : Local)
  | nop
  deriving DecidableEq, Repr

def Statement.assignLocal (dest : Local) (rvalue : Rvalue) : Statement :=
  .assign (Place.ofLocal dest) rvalue

inductive Terminator where
  | goto (target : BlockId)
  | switchInt (discr : Operand) (targets : List (Word × BlockId)) (otherwise : BlockId)
  | ret
  | panic
  | unreachable
  deriving DecidableEq, Repr

structure Block where
  statements : List Statement
  terminator : Terminator
  deriving DecidableEq, Repr

structure Body where
  argCount : Nat
  isUnsafe : Bool := false
  localTys : List Ty
  blocks : List Block
  deriving DecidableEq, Repr

inductive Slot where
  | dead
  | uninit
  | value (word : Word)
  deriving DecidableEq, Repr

structure State where
  block : BlockId
  stmt : Nat
  locals : List Slot
  deriving DecidableEq, Repr

inductive Fault where
  | malformedProgram
  | invalidControlFlow
  | invalidLocal
  | deadStorage
  | uninitialized
  | typeMismatch
  | invalidValue
  | overflow
  | divisionByZero
  | shiftOutOfBounds
  | assertionFailed
  | unreachableExecuted
  deriving DecidableEq, Repr

/-- Outcomes of a single small step, exposing both return slot `_0` and final
local slots so `&mut` parameter post-states (`locals[1]?`) can be observed. -/
inductive StepResult where
  | next (state : State)
  | ret (value : Word) (locals : List Slot)
  | fault (reason : Fault)
  deriving DecidableEq, Repr

def validIntBits (bits : Nat) : Bool :=
  bits == 8 || bits == 16 || bits == 32 || bits == 64

def tyWF : Ty → Bool
  | .unit | .bool | .never => true
  | .int bits _ => validIntBits bits
  | .enumTy discriminants => !discriminants.isEmpty
  | .struct1 fieldTy => tyWF fieldTy
  | .ref _ pointee => tyWF pointee

def castUnsigned (bits : Nat) (w : Word) : Word :=
  match bits with
  | 8 => w &&& 0xff#64
  | 16 => w &&& 0xffff#64
  | 32 => w &&& 0xffffffff#64
  | 64 => w
  | _ => (w.setWidth bits).zeroExtend 64

def castSigned (bits : Nat) (w : Word) : Word :=
  (w.setWidth bits).signExtend 64

def castIntWord (bits : Nat) (signed : Bool) (w : Word) : Word :=
  if signed then castSigned bits w else castUnsigned bits w

def rawValid : Ty → Word → Bool
  | .unit, value => value == 0
  | .bool, value => value == 0 || value == 1
  | .int bits false, value =>
      if bits == 64 then true else castUnsigned bits value == value
  | .int bits true, value =>
      if bits == 64 then true else castSigned bits value == value
  | .enumTy discriminants, value =>
      discriminants.any (fun entry => entry.2 == value)
  | .never, _ => false
  | .struct1 fieldTy, value => rawValid fieldTy value
  | .ref _ pointee, value => rawValid pointee value

def validValue (ty : Ty) (value : Word) : Bool :=
  tyWF ty && rawValid ty value

def boolWord (value : Bool) : Word :=
  if value then 1 else 0

/-- Resolve the projected type of `place` starting from `localTy`. -/
def projectTy : Ty → List ProjectionElem → Option Ty
  | ty, [] => some ty
  | .ref _ pointee, .deref :: rest => projectTy pointee rest
  | .struct1 fieldTy, .field 0 :: rest => projectTy fieldTy rest
  | _, _ => none

/-- Check whether `place` is writable starting from `localTy` and return the
written target type. Writing through `.deref` requires `.ref true` (`&mut`). -/
def writablePlaceTy : Ty → List ProjectionElem → Option Ty
  | ty, [] => some ty
  | .ref true pointee, [.deref] => some pointee
  | .ref true (.struct1 fieldTy), [.deref, .field 0] => some fieldTy
  | .struct1 fieldTy, [.field 0] => some fieldTy
  | _, _ => none

def readPlace (body : Body) (locals : List Slot) (place : Place) (move : Bool)
    (preserveMove : Bool := false) : Except Fault (Ty × Word × List Slot) :=
  match body.localTys[place.localIdx]?, locals[place.localIdx]? with
  | some localTy, some (.value value) =>
      match projectTy localTy place.projection with
      | some projTy =>
          if tyWF projTy then
            -- Moving a dereferenced projection (`*p` or `(*p).0`) copies the
            -- `Copy` scalar referent without invalidating the reference slot `p`.
            let nextLocals :=
              if move && place.projection.isEmpty && !preserveMove then
                locals.set place.localIdx .uninit
              else
                locals
            .ok (projTy, value, nextLocals)
          else
            .error .invalidValue
      | none => .error .typeMismatch
  | some _, some .uninit => .error .uninitialized
  | some _, some .dead => .error .deadStorage
  | _, _ => .error .invalidLocal

def writePlace (body : Body) (locals : List Slot) (place : Place) (ty : Ty)
    (value : Word) : Except Fault (List Slot) :=
  match body.localTys[place.localIdx]?, locals[place.localIdx]? with
  | some localTy, some slot =>
      match writablePlaceTy localTy place.projection with
      | some expectedTy =>
          -- Direct local assignment requires storage not `.dead`;
          -- deref assignment `(*_1) = ...` requires the `&mut` reference slot
          -- to hold a live `.value _` reference.
          let slotOk :=
            if place.projection.isEmpty then
              match slot with | .dead => false | _ => true
            else
              match slot with | .value _ => true | _ => false
          if !slotOk then
            .error .deadStorage
          else if expectedTy == ty then
            if tyWF expectedTy then
              .ok (locals.set place.localIdx (.value value))
            else
              .error .invalidValue
          else
            .error .typeMismatch
      | none => .error .typeMismatch
  | _, _ => .error .invalidLocal

def evalOperand (body : Body) (locals : List Slot) (operand : Operand)
    (preserveMove : Bool := false) : Except Fault (Ty × Word × List Slot) :=
  match operand with
  | .copy place => readPlace body locals place false
  | .move place => readPlace body locals place true preserveMove
  | .constant ty value =>
      if validValue ty value then
        .ok (ty, value, locals)
      else
        .error .invalidValue

def evalShift (op : BinOp) (bits : Nat) (signed : Bool) (left : Word)
    (rightTy : Ty) (right : Word) : Except Fault (Ty × Word) :=
  match rightTy with
  | .int rhsBits rhsSigned =>
      if !validIntBits bits || !validIntBits rhsBits then
        .error .typeMismatch
      else
        let shiftAmount := right.toNat
        if rhsSigned && right.toInt < 0 then
          .error .shiftOutOfBounds
        else if shiftAmount >= bits then
          .error .shiftOutOfBounds
        else
          let outTy := Ty.int bits signed
          let raw :=
            match op with
            | .shl => left <<< shiftAmount
            | .shr =>
                if signed then
                  BitVec.sshiftRight left shiftAmount
                else
                  left >>> shiftAmount
            | _ => left
          let result := castIntWord bits signed raw
          if tyWF outTy then
            .ok (outTy, result)
          else
            .error .invalidValue
  | _ => .error .typeMismatch

def evalBinary (op : BinOp) (leftTy : Ty) (left : Word)
    (rightTy : Ty) (right : Word) : Except Fault (Ty × Word) :=
  match op with
  | .shl | .shr =>
      match leftTy with
      | .int bits signed => evalShift op bits signed left rightTy right
      | _ => .error .typeMismatch
  | .bitAnd | .bitOr | .bitXor =>
      if leftTy != rightTy then
        .error .typeMismatch
      else
        match leftTy with
        | .bool =>
            let result :=
              match op with
              | .bitAnd => boolWord ((left == 1) && (right == 1))
              | .bitOr => boolWord ((left == 1) || (right == 1))
              | .bitXor => boolWord ((left == 1) != (right == 1))
              | _ => 0
            .ok (.bool, result)
        | .int bits signed =>
            let raw :=
              match op with
              | .bitAnd => left &&& right
              | .bitOr => left ||| right
              | .bitXor => left ^^^ right
              | _ => 0
            let result := castIntWord bits signed raw
            if tyWF leftTy then
              .ok (leftTy, result)
            else
              .error .invalidValue
        | _ => .error .typeMismatch
  | .lt | .le | .gt | .ge | .eq | .ne =>
      if leftTy != rightTy then
        .error .typeMismatch
      else
        match leftTy with
        | .int _ false =>
            let b :=
              match op with
              | .eq => left == right
              | .ne => left != right
              | .lt => decide (left.toNat < right.toNat)
              | .le => decide (left.toNat ≤ right.toNat)
              | .gt => decide (right.toNat < left.toNat)
              | .ge => decide (right.toNat ≤ left.toNat)
              | _ => false
            .ok (.bool, boolWord b)
        | _ => .error .typeMismatch
  | _ => .error .typeMismatch

def evalUnary (op : UnOp) (ty : Ty) (value : Word) : Except Fault (Ty × Word) :=
  match op, ty with
  | .not, .bool => .ok (.bool, boolWord (value == 0))
  | .not, .int bits signed =>
      if !validIntBits bits then
        .error .typeMismatch
      else
        let result := castIntWord bits signed (~~~value)
        if tyWF (.int bits signed) then
          .ok (.int bits signed, result)
        else
          .error .invalidValue
  | _, _ => .error .typeMismatch

def evalCastInt (srcTy targetTy : Ty) (value : Word) : Except Fault (Ty × Word) :=
  match srcTy, targetTy with
  | .int srcBits _, .int dstBits dstSigned =>
      if !validIntBits srcBits || !validIntBits dstBits then
        .error .typeMismatch
      else
        let result := castIntWord dstBits dstSigned value
        if tyWF targetTy then
          .ok (targetTy, result)
        else
          .error .invalidValue
  | _, _ => .error .typeMismatch

def evalRvalue (body : Body) (locals : List Slot) (rvalue : Rvalue) :
    Except Fault (Ty × Word × List Slot) :=
  match rvalue with
  | .use operand preserveSource => evalOperand body locals operand preserveSource
  | .binary op left right =>
      match evalOperand body locals left with
      | .ok (leftTy, leftVal, locals1) =>
          match evalOperand body locals1 right with
          | .ok (rightTy, rightVal, locals2) =>
              match evalBinary op leftTy leftVal rightTy rightVal with
              | .ok (ty, value) => .ok (ty, value, locals2)
              | .error err => .error err
          | .error err => .error err
      | .error err => .error err
  | .unary op operand =>
      match evalOperand body locals operand with
      | .ok (ty, val, locals1) =>
          match evalUnary op ty val with
          | .ok (outTy, outVal) => .ok (outTy, outVal, locals1)
          | .error err => .error err
      | .error err => .error err
  | .castInt targetTy operand =>
      match evalOperand body locals operand with
      | .ok (srcTy, val, locals1) =>
          match evalCastInt srcTy targetTy val with
          | .ok (outTy, outVal) => .ok (outTy, outVal, locals1)
          | .error err => .error err
      | .error err => .error err
  | .aggregateStruct1 structTy operand =>
      match structTy with
      | .struct1 fieldTy =>
          match evalOperand body locals operand with
          | .ok (opTy, val, locals1) =>
              if opTy == fieldTy && tyWF structTy then
                .ok (structTy, val, locals1)
              else
                .error .typeMismatch
          | .error err => .error err
      | _ => .error .typeMismatch

def execStatement (body : Body) (locals : List Slot) (stmt : Statement) :
    Except Fault (List Slot) :=
  match stmt with
  | .assign dest rvalue =>
      match evalRvalue body locals rvalue with
      | .ok (ty, value, nextLocals) => writePlace body nextLocals dest ty value
      | .error err => .error err
  | .storageLive slot =>
      if slot <= body.argCount || slot >= locals.length then
        .error .invalidLocal
      else
        .ok (locals.set slot .uninit)
  | .storageDead slot =>
      if slot <= body.argCount || slot >= locals.length then
        .error .invalidLocal
      else
        .ok (locals.set slot .dead)
  | .nop => .ok locals

def findSwitchTarget (value : Word) (targets : List (Word × BlockId))
    (otherwise : BlockId) : BlockId :=
  match targets.find? (fun entry => entry.1 == value) with
  | some (_, target) => target
  | none => otherwise

def execTerminator (body : Body) (locals : List Slot) (term : Terminator) :
    StepResult :=
  match term with
  | .goto target =>
      if target < body.blocks.length then
        .next { block := target, stmt := 0, locals }
      else
        .fault .invalidControlFlow
  | .switchInt discr targets otherwise =>
      match evalOperand body locals discr with
      | .ok (ty, value, nextLocals) =>
          match ty with
          | .bool | .int _ _ =>
              let target := findSwitchTarget value targets otherwise
              if target < body.blocks.length then
                .next { block := target, stmt := 0, locals := nextLocals }
              else
                .fault .invalidControlFlow
          | _ => .fault .typeMismatch
      | .error reason => .fault reason
  | .ret =>
      match readPlace body locals (Place.ofLocal 0) false with
      | .ok (_, value, _) => .ret value locals
      | .error reason => .fault reason
  | .panic => .fault .assertionFailed
  | .unreachable => .fault .unreachableExecuted

def step (body : Body) (state : State) : StepResult :=
  if state.locals.length != body.localTys.length then
    .fault .malformedProgram
  else
    match body.blocks[state.block]? with
    | none => .fault .invalidControlFlow
    | some block =>
        if state.stmt < block.statements.length then
          match block.statements[state.stmt]? with
          | some stmt =>
              match execStatement body state.locals stmt with
              | .ok locals =>
                  .next { block := state.block, stmt := state.stmt + 1, locals }
              | .error reason => .fault reason
          | none => .fault .invalidControlFlow
        else if state.stmt == block.statements.length then
          execTerminator body state.locals block.terminator
        else
          .fault .invalidControlFlow

def run (body : Body) (fuel : Nat) (state : State) : Option (Word × List Slot) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match step body state with
      | .next next => run body fuel next
      | .ret value locals => some (value, locals)
      | .fault _ => none

def mentionsSlot : Statement → Local → Bool
  | .storageLive slot, target => slot == target
  | .storageDead slot, target => slot == target
  | _, _ => false

def hasStorageMarkers (body : Body) (target : Local) : Bool :=
  body.blocks.any (fun block =>
    block.statements.any (fun stmt => mentionsSlot stmt target))

def initialSlot (body : Body) (args : List Word) (index : Local) : Slot :=
  if index == 0 then
    .uninit
  else
    match args[index - 1]? with
    | some value => .value value
    | none =>
        if hasStorageMarkers body index then .dead else .uninit

def initial (body : Body) (args : List Word) : State :=
  {
    block := 0
    stmt := 0
    locals := (List.range body.localTys.length).map (initialSlot body args)
  }

/-!
## Exact `PostCleanup` MIR Encodings from `candidate_mir_extracts.txt` (`def_id` 27–37)
-/

abbrev tyU8 : Ty := .int 8 false
abbrev tyU16 : Ty := .int 16 false
abbrev tyI16 : Ty := .int 16 true
abbrev tyU32 : Ty := .int 32 false
abbrev tyI32 : Ty := .int 32 true
abbrev tyU64 : Ty := .int 64 false
abbrev tyInsn : Ty := .struct1 tyU64
abbrev tyRefInsn : Ty := .ref false tyInsn
abbrev tyRefMutInsn : Ty := .ref true tyInsn

/-- `def_id = 37`: `api::EbpfInstruction::get(&self) -> u64` (1 block, 1 stmt) -/
def getBody : Body :=
  {
    argCount := 1
    localTys := [tyU64, tyRefInsn]
    blocks := [
      {
        statements := [
          .assignLocal 0 (.use (.copy (Place.derefField0 1)) true)
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 27`: `api::EbpfInstruction::code(&self) -> u8` (1 block, 4 stmts) -/
def codeBody : Body :=
  {
    argCount := 1
    localTys := [tyU8, tyRefInsn, tyU64]
    blocks := [
      {
        statements := [
          .storageLive 2,
          .assignLocal 2 (.use (.copy (Place.derefField0 1)) true),
          .assignLocal 0 (.castInt tyU8 (.moveLocal 2)),
          .storageDead 2
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 28`: `api::EbpfInstruction::set_code(&mut self, code: u8)` (1 block, 23 stmts) -/
def setCodeBody : Body :=
  {
    argCount := 2
    localTys := [.unit, tyRefMutInsn, tyU8, tyInsn, tyU64, tyU64, tyU64, tyU64, tyU64, tyU8]
    blocks := [
      {
        statements := [
          .storageLive 3,
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .assignLocal 6 (.use (.copy (Place.derefField0 1)) true),
          .storageLive 7,
          .assignLocal 7 (.unary .not (.constant tyU64 0xff#64)),
          .assignLocal 5 (.binary .bitAnd (.moveLocal 6) (.moveLocal 7)),
          .storageDead 7,
          .storageDead 6,
          .storageLive 8,
          .storageLive 9,
          .assignLocal 9 (.use (.copyLocal 2) true),
          .assignLocal 8 (.castInt tyU64 (.moveLocal 9)),
          .storageDead 9,
          .assignLocal 4 (.binary .bitOr (.moveLocal 5) (.moveLocal 8)),
          .storageDead 8,
          .storageDead 5,
          .assignLocal 3 (.aggregateStruct1 tyInsn (.moveLocal 4)),
          .storageDead 4,
          .assign (Place.derefLocal 1) (.use (.moveLocal 3)),
          .assignLocal 0 (.use (.constant .unit 0) true),
          .storageDead 3
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 29`: `api::EbpfInstruction::dst_reg(&self) -> u8` (1 block, 10 stmts) -/
def dstRegBody : Body :=
  {
    argCount := 1
    localTys := [tyU8, tyRefInsn, tyU64, tyU64, tyU64]
    blocks := [
      {
        statements := [
          .storageLive 2,
          .storageLive 3,
          .storageLive 4,
          .assignLocal 4 (.use (.copy (Place.derefField0 1)) true),
          .assignLocal 3 (.binary .bitAnd (.moveLocal 4) (.constant tyU64 0x0f00#64)),
          .storageDead 4,
          .assignLocal 2 (.binary .shr (.moveLocal 3) (.constant tyI32 8#64)),
          .storageDead 3,
          .assignLocal 0 (.castInt tyU8 (.moveLocal 2)),
          .storageDead 2
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 30`: `api::EbpfInstruction::set_dst_reg(&mut self, dst_reg: u8)` (3 blocks, 37 stmts) -/
def setDstRegBody : Body :=
  {
    argCount := 2
    localTys := [.unit, tyRefMutInsn, tyU8, .unit, .bool, tyU8, .never,
                 tyInsn, tyU64, tyU64, tyU64, tyU64, tyU64, tyU64, tyU8]
    blocks := [
      {
        statements := [
          .storageLive 3,
          .storageLive 4,
          .storageLive 5,
          .assignLocal 5 (.use (.copyLocal 2) true),
          .assignLocal 4 (.binary .lt (.moveLocal 5) (.constant tyU8 16#64))
        ]
        terminator := .switchInt (.moveLocal 4) [(0, 2)] 1
      },
      {
        statements := [
          .storageDead 5,
          .assignLocal 3 (.use (.constant .unit 0) true),
          .storageDead 4,
          .storageDead 3,
          .storageLive 7,
          .storageLive 8,
          .storageLive 9,
          .storageLive 10,
          .assignLocal 10 (.use (.copy (Place.derefField0 1)) true),
          .storageLive 11,
          .assignLocal 11 (.unary .not (.constant tyU64 0x0f00#64)),
          .assignLocal 9 (.binary .bitAnd (.moveLocal 10) (.moveLocal 11)),
          .storageDead 11,
          .storageDead 10,
          .storageLive 12,
          .storageLive 13,
          .storageLive 14,
          .assignLocal 14 (.use (.copyLocal 2) true),
          .assignLocal 13 (.castInt tyU64 (.moveLocal 14)),
          .storageDead 14,
          .assignLocal 12 (.binary .shl (.moveLocal 13) (.constant tyI32 8#64)),
          .storageDead 13,
          .assignLocal 8 (.binary .bitOr (.moveLocal 9) (.moveLocal 12)),
          .storageDead 12,
          .storageDead 9,
          .assignLocal 7 (.aggregateStruct1 tyInsn (.moveLocal 8)),
          .storageDead 8,
          .assign (Place.derefLocal 1) (.use (.moveLocal 7)),
          .assignLocal 0 (.use (.constant .unit 0) true),
          .storageDead 7
        ]
        terminator := .ret
      },
      {
        statements := [
          .storageDead 5,
          .storageLive 6
        ]
        terminator := .panic
      }
    ]
  }

/-- `def_id = 31`: `api::EbpfInstruction::src_reg(&self) -> u8` (1 block, 10 stmts) -/
def srcRegBody : Body :=
  {
    argCount := 1
    localTys := [tyU8, tyRefInsn, tyU64, tyU64, tyU64]
    blocks := [
      {
        statements := [
          .storageLive 2,
          .storageLive 3,
          .storageLive 4,
          .assignLocal 4 (.use (.copy (Place.derefField0 1)) true),
          .assignLocal 3 (.binary .bitAnd (.moveLocal 4) (.constant tyU64 0xf000#64)),
          .storageDead 4,
          .assignLocal 2 (.binary .shr (.moveLocal 3) (.constant tyI32 12#64)),
          .storageDead 3,
          .assignLocal 0 (.castInt tyU8 (.moveLocal 2)),
          .storageDead 2
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 32`: `api::EbpfInstruction::set_src_reg(&mut self, src_reg: u8)` (3 blocks, 37 stmts) -/
def setSrcRegBody : Body :=
  {
    argCount := 2
    localTys := [.unit, tyRefMutInsn, tyU8, .unit, .bool, tyU8, .never,
                 tyInsn, tyU64, tyU64, tyU64, tyU64, tyU64, tyU64, tyU8]
    blocks := [
      {
        statements := [
          .storageLive 3,
          .storageLive 4,
          .storageLive 5,
          .assignLocal 5 (.use (.copyLocal 2) true),
          .assignLocal 4 (.binary .lt (.moveLocal 5) (.constant tyU8 16#64))
        ]
        terminator := .switchInt (.moveLocal 4) [(0, 2)] 1
      },
      {
        statements := [
          .storageDead 5,
          .assignLocal 3 (.use (.constant .unit 0) true),
          .storageDead 4,
          .storageDead 3,
          .storageLive 7,
          .storageLive 8,
          .storageLive 9,
          .storageLive 10,
          .assignLocal 10 (.use (.copy (Place.derefField0 1)) true),
          .storageLive 11,
          .assignLocal 11 (.unary .not (.constant tyU64 0xf000#64)),
          .assignLocal 9 (.binary .bitAnd (.moveLocal 10) (.moveLocal 11)),
          .storageDead 11,
          .storageDead 10,
          .storageLive 12,
          .storageLive 13,
          .storageLive 14,
          .assignLocal 14 (.use (.copyLocal 2) true),
          .assignLocal 13 (.castInt tyU64 (.moveLocal 14)),
          .storageDead 14,
          .assignLocal 12 (.binary .shl (.moveLocal 13) (.constant tyI32 12#64)),
          .storageDead 13,
          .assignLocal 8 (.binary .bitOr (.moveLocal 9) (.moveLocal 12)),
          .storageDead 12,
          .storageDead 9,
          .assignLocal 7 (.aggregateStruct1 tyInsn (.moveLocal 8)),
          .storageDead 8,
          .assign (Place.derefLocal 1) (.use (.moveLocal 7)),
          .assignLocal 0 (.use (.constant .unit 0) true),
          .storageDead 7
        ]
        terminator := .ret
      },
      {
        statements := [
          .storageDead 5,
          .storageLive 6
        ]
        terminator := .panic
      }
    ]
  }

/-- `def_id = 33`: `api::EbpfInstruction::offset(&self) -> i16` (1 block, 10 stmts) -/
def offsetBody : Body :=
  {
    argCount := 1
    localTys := [tyI16, tyRefInsn, tyU16, tyU64, tyU64]
    blocks := [
      {
        statements := [
          .storageLive 2,
          .storageLive 3,
          .storageLive 4,
          .assignLocal 4 (.use (.copy (Place.derefField0 1)) true),
          .assignLocal 3 (.binary .shr (.moveLocal 4) (.constant tyI32 16#64)),
          .storageDead 4,
          .assignLocal 2 (.castInt tyU16 (.moveLocal 3)),
          .storageDead 3,
          .assignLocal 0 (.castInt tyI16 (.moveLocal 2)),
          .storageDead 2
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 34`: `api::EbpfInstruction::set_offset(&mut self, offset: i16)` (1 block, 29 stmts) -/
def setOffsetBody : Body :=
  {
    argCount := 2
    localTys := [.unit, tyRefMutInsn, tyI16, tyInsn, tyU64, tyU64, tyU64, tyU64, tyU64, tyU64, tyU16, tyI16]
    blocks := [
      {
        statements := [
          .storageLive 3,
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .assignLocal 6 (.use (.copy (Place.derefField0 1)) true),
          .storageLive 7,
          .assignLocal 7 (.unary .not (.constant tyU64 0xffff0000#64)),
          .assignLocal 5 (.binary .bitAnd (.moveLocal 6) (.moveLocal 7)),
          .storageDead 7,
          .storageDead 6,
          .storageLive 8,
          .storageLive 9,
          .storageLive 10,
          .storageLive 11,
          .assignLocal 11 (.use (.copyLocal 2) true),
          .assignLocal 10 (.castInt tyU16 (.moveLocal 11)),
          .storageDead 11,
          .assignLocal 9 (.castInt tyU64 (.moveLocal 10)),
          .storageDead 10,
          .assignLocal 8 (.binary .shl (.moveLocal 9) (.constant tyI32 16#64)),
          .storageDead 9,
          .assignLocal 4 (.binary .bitOr (.moveLocal 5) (.moveLocal 8)),
          .storageDead 8,
          .storageDead 5,
          .assignLocal 3 (.aggregateStruct1 tyInsn (.moveLocal 4)),
          .storageDead 4,
          .assign (Place.derefLocal 1) (.use (.moveLocal 3)),
          .assignLocal 0 (.use (.constant .unit 0) true),
          .storageDead 3
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 35`: `api::EbpfInstruction::imm(&self) -> i32` (1 block, 10 stmts) -/
def immBody : Body :=
  {
    argCount := 1
    localTys := [tyI32, tyRefInsn, tyU32, tyU64, tyU64]
    blocks := [
      {
        statements := [
          .storageLive 2,
          .storageLive 3,
          .storageLive 4,
          .assignLocal 4 (.use (.copy (Place.derefField0 1)) true),
          .assignLocal 3 (.binary .shr (.moveLocal 4) (.constant tyI32 32#64)),
          .storageDead 4,
          .assignLocal 2 (.castInt tyU32 (.moveLocal 3)),
          .storageDead 3,
          .assignLocal 0 (.castInt tyI32 (.moveLocal 2)),
          .storageDead 2
        ]
        terminator := .ret
      }
    ]
  }

/-- `def_id = 36`: `api::EbpfInstruction::set_imm(&mut self, imm: i32)` (1 block, 26 stmts) -/
def setImmBody : Body :=
  {
    argCount := 2
    localTys := [.unit, tyRefMutInsn, tyI32, tyInsn, tyU64, tyU64, tyU64, tyU64, tyU64, tyU32, tyI32]
    blocks := [
      {
        statements := [
          .storageLive 3,
          .storageLive 4,
          .storageLive 5,
          .storageLive 6,
          .assignLocal 6 (.use (.copy (Place.derefField0 1)) true),
          .assignLocal 5 (.binary .bitAnd (.moveLocal 6) (.constant tyU64 0x00000000ffffffff#64)),
          .storageDead 6,
          .storageLive 7,
          .storageLive 8,
          .storageLive 9,
          .storageLive 10,
          .assignLocal 10 (.use (.copyLocal 2) true),
          .assignLocal 9 (.castInt tyU32 (.moveLocal 10)),
          .storageDead 10,
          .assignLocal 8 (.castInt tyU64 (.moveLocal 9)),
          .storageDead 9,
          .assignLocal 7 (.binary .shl (.moveLocal 8) (.constant tyI32 32#64)),
          .storageDead 8,
          .assignLocal 4 (.binary .bitOr (.moveLocal 5) (.moveLocal 7)),
          .storageDead 7,
          .storageDead 5,
          .assignLocal 3 (.aggregateStruct1 tyInsn (.moveLocal 4)),
          .storageDead 4,
          .assign (Place.derefLocal 1) (.use (.moveLocal 3)),
          .assignLocal 0 (.use (.constant .unit 0) true),
          .storageDead 3
        ]
        terminator := .ret
      }
    ]
  }

/-!
## Execution & Fault Certificates (`Executes`, `FaultsWith`, `runN_executes`)
-/

inductive Executes (body : Body) : State → Word → List Slot → Prop where
  | ret {start : State} {value : Word} {locals : List Slot} :
      step body start = .ret value locals → Executes body start value locals
  | next {start next : State} {value : Word} {locals : List Slot} :
      step body start = .next next → Executes body next value locals →
      Executes body start value locals

inductive FaultsWith (body : Body) : State → Fault → Prop where
  | fault {start : State} {reason : Fault} :
      step body start = .fault reason → FaultsWith body start reason
  | next {start next : State} {reason : Fault} :
      step body start = .next next → FaultsWith body next reason →
      FaultsWith body start reason

def runN (body : Body) : Nat → State → Option State
  | 0, st => some st
  | n + 1, st =>
      match step body st with
      | .next next => runN body n next
      | _ => none

theorem runN_executes {body : Body} {n : Nat} {start mid : State} {value : Word} {locals : List Slot}
    (h1 : runN body n start = some mid) (h2 : Executes body mid value locals) :
    Executes body start value locals := by
  induction n generalizing start with
  | zero => cases h1; exact h2
  | succ k ih =>
      unfold runN at h1
      cases hstep : step body start with
      | next next => rw [hstep] at h1; exact .next hstep (ih h1)
      | ret _ _ => rw [hstep] at h1; cases h1
      | fault _ => rw [hstep] at h1; cases h1

theorem runN_faults {body : Body} {n : Nat} {start mid : State} {reason : Fault}
    (h1 : runN body n start = some mid) (h2 : FaultsWith body mid reason) :
    FaultsWith body start reason := by
  induction n generalizing start with
  | zero => cases h1; exact h2
  | succ k ih =>
      unfold runN at h1
      cases hstep : step body start with
      | next next => rw [hstep] at h1; exact .next hstep (ih h1)
      | ret _ _ => rw [hstep] at h1; cases h1
      | fault _ => rw [hstep] at h1; cases h1

theorem run_executes {body : Body} {fuel : Nat} {start : State} {value : Word} {locals : List Slot}
    (h : run body fuel start = some (value, locals)) : Executes body start value locals := by
  induction fuel generalizing start with
  | zero => simp [run] at h
  | succ f ih =>
      unfold run at h
      cases hstep : step body start with
      | next next => rw [hstep] at h; exact .next hstep (ih h)
      | ret v l => rw [hstep] at h; cases h; exact .ret hstep
      | fault r => rw [hstep] at h; cases h

/-!
## Pure Functional Specifications of the 11 `EbpfInstruction` Methods
-/

def getSpec (raw : Word) : Word := raw
def codeSpec (raw : Word) : Word := raw &&& 0xff#64
def setCodeSpec (raw c : Word) : Word := (raw &&& ~~~0xff#64) ||| c
def dstRegSpec (raw : Word) : Word := ((raw &&& 0x0f00#64) >>> (8 : Nat)) &&& 0xff#64
def setDstRegSpec (raw d : Word) : Word := (raw &&& ~~~0x0f00#64) ||| (d <<< (8 : Nat))
def srcRegSpec (raw : Word) : Word := ((raw &&& 0xf000#64) >>> (12 : Nat)) &&& 0xff#64
def setSrcRegSpec (raw s : Word) : Word := (raw &&& ~~~0xf000#64) ||| (s <<< (12 : Nat))
def offsetSpec (raw : Word) : Word := castSigned 16 ((raw >>> (16 : Nat)) &&& 0xffff#64)
def setOffsetSpec (raw off : Word) : Word := (raw &&& ~~~0xffff0000#64) ||| ((off &&& 0xffff#64) <<< (16 : Nat))
def immSpec (raw : Word) : Word := castSigned 32 ((raw >>> (32 : Nat)) &&& 0xffffffff#64)
def setImmSpec (raw im : Word) : Word := (raw &&& 0x00000000ffffffff#64) ||| ((im &&& 0xffffffff#64) <<< (32 : Nat))

/-!
## Symbolic MIR Execution Theorems for All 11 `EbpfInstruction` Methods
-/

theorem exec_get (raw : Word) :
    Executes getBody (initial getBody [raw]) (getSpec raw) [.value raw, .value raw] :=
  run_executes (fuel := 2) rfl

theorem exec_code (raw : Word) :
    Executes codeBody (initial codeBody [raw]) (codeSpec raw)
      [.value (codeSpec raw), .value raw, .dead] :=
  run_executes (fuel := 5) rfl

theorem exec_set_code (raw c : Word) :
    Executes setCodeBody (initial setCodeBody [raw, c]) 0
      [.value 0, .value (setCodeSpec raw c), .value c,
       .dead, .dead, .dead, .dead, .dead, .dead, .dead] := by
  have h0 : initial setCodeBody [raw, c] =
      ⟨0, 0, [.uninit, .value raw, .value c, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩ := rfl
  rw [h0]
  refine runN_executes (n := 5)
    (mid := ⟨0, 5, [.uninit, .value raw, .value c, .uninit, .uninit, .uninit, .value raw, .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 5)
    (mid := ⟨0, 10, [.uninit, .value raw, .value c, .uninit, .uninit, .value (raw &&& ~~~0xff#64), .dead, .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 5)
    (mid := ⟨0, 15, [.uninit, .value raw, .value c, .uninit, .uninit, .value (raw &&& ~~~0xff#64), .dead, .dead, .value c, .dead]⟩) rfl ?_
  refine runN_executes (n := 3)
    (mid := ⟨0, 18, [.uninit, .value raw, .value c, .uninit, .value (setCodeSpec raw c), .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  exact run_executes (fuel := 6) rfl

theorem exec_dst_reg (raw : Word) :
    Executes dstRegBody (initial dstRegBody [raw]) (dstRegSpec raw)
      [.value (dstRegSpec raw), .value raw, .dead, .dead, .dead] :=
  runN_executes (n := 6)
    (mid := ⟨0, 6, [.uninit, .value raw, .uninit, .value (raw &&& 0x0f00#64), .dead]⟩) rfl
    (run_executes (fuel := 5) rfl)

theorem exec_set_dst_reg_ok (raw d : Word) (hd : decide (d.toNat < 16) = true) :
    Executes setDstRegBody (initial setDstRegBody [raw, d]) 0
      [.value 0, .value (setDstRegSpec raw d), .value d,
       .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead] := by
  have h0 : initial setDstRegBody [raw, d] =
      ⟨0, 0, [.uninit, .value raw, .value d, .dead, .dead, .dead, .dead,
              .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩ := rfl
  rw [h0]
  refine runN_executes (n := 5)
    (mid := ⟨0, 5, [.uninit, .value raw, .value d, .uninit,
                    .value (boolWord (decide (d.toNat < (16#64).toNat))), .uninit, .dead,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  have h16 : (16#64).toNat = 16 := rfl
  have hb : boolWord (decide (d.toNat < (16#64).toNat)) = 1 := by
    rw [h16, hd]; rfl
  rw [hb]
  refine runN_executes (n := 5)
    (mid := ⟨1, 4, [.uninit, .value raw, .value d, .dead, .dead, .dead, .dead,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 7)
    (mid := ⟨1, 11, [.uninit, .value raw, .value d, .dead, .dead, .dead, .dead,
                     .uninit, .uninit, .uninit, .value raw, .value (~~~0x0f00#64), .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 6)
    (mid := ⟨1, 17, [.uninit, .value raw, .value d, .dead, .dead, .dead, .dead,
                     .uninit, .uninit, .value (raw &&& ~~~0x0f00#64), .dead, .dead, .uninit, .uninit, .uninit]⟩) rfl ?_
  refine runN_executes (n := 5)
    (mid := ⟨1, 22, [.uninit, .value raw, .value d, .dead, .dead, .dead, .dead,
                     .uninit, .uninit, .value (raw &&& ~~~0x0f00#64), .dead, .dead,
                     .value (d <<< (8 : Nat)), .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 3)
    (mid := ⟨1, 25, [.uninit, .value raw, .value d, .dead, .dead, .dead, .dead,
                     .uninit, .value (setDstRegSpec raw d),
                     .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  exact run_executes (fuel := 6) rfl

theorem exec_set_dst_reg_panic (raw d : Word) (hd : decide (d.toNat < 16) = false) :
    FaultsWith setDstRegBody (initial setDstRegBody [raw, d]) .assertionFailed := by
  have h0 : initial setDstRegBody [raw, d] =
      ⟨0, 0, [.uninit, .value raw, .value d, .dead, .dead, .dead, .dead,
              .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩ := rfl
  rw [h0]
  refine runN_faults (n := 5)
    (mid := ⟨0, 5, [.uninit, .value raw, .value d, .uninit,
                    .value (boolWord (decide (d.toNat < (16#64).toNat))), .uninit, .dead,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  have h16 : (16#64).toNat = 16 := rfl
  have hb : boolWord (decide (d.toNat < (16#64).toNat)) = 0 := by
    rw [h16, hd]; rfl
  rw [hb]
  refine runN_faults (n := 3)
    (mid := ⟨2, 2, [.uninit, .value raw, .value d, .uninit, .uninit, .dead, .uninit,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  exact .fault rfl

theorem exec_src_reg (raw : Word) :
    Executes srcRegBody (initial srcRegBody [raw]) (srcRegSpec raw)
      [.value (srcRegSpec raw), .value raw, .dead, .dead, .dead] :=
  runN_executes (n := 6)
    (mid := ⟨0, 6, [.uninit, .value raw, .uninit, .value (raw &&& 0xf000#64), .dead]⟩) rfl
    (run_executes (fuel := 5) rfl)

theorem exec_set_src_reg_ok (raw s : Word) (hs : decide (s.toNat < 16) = true) :
    Executes setSrcRegBody (initial setSrcRegBody [raw, s]) 0
      [.value 0, .value (setSrcRegSpec raw s), .value s,
       .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead] := by
  have h0 : initial setSrcRegBody [raw, s] =
      ⟨0, 0, [.uninit, .value raw, .value s, .dead, .dead, .dead, .dead,
              .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩ := rfl
  rw [h0]
  refine runN_executes (n := 5)
    (mid := ⟨0, 5, [.uninit, .value raw, .value s, .uninit,
                    .value (boolWord (decide (s.toNat < (16#64).toNat))), .uninit, .dead,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  have h16 : (16#64).toNat = 16 := rfl
  have hb : boolWord (decide (s.toNat < (16#64).toNat)) = 1 := by
    rw [h16, hs]; rfl
  rw [hb]
  refine runN_executes (n := 5)
    (mid := ⟨1, 4, [.uninit, .value raw, .value s, .dead, .dead, .dead, .dead,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 7)
    (mid := ⟨1, 11, [.uninit, .value raw, .value s, .dead, .dead, .dead, .dead,
                     .uninit, .uninit, .uninit, .value raw, .value (~~~0xf000#64), .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 6)
    (mid := ⟨1, 17, [.uninit, .value raw, .value s, .dead, .dead, .dead, .dead,
                     .uninit, .uninit, .value (raw &&& ~~~0xf000#64), .dead, .dead, .uninit, .uninit, .uninit]⟩) rfl ?_
  refine runN_executes (n := 5)
    (mid := ⟨1, 22, [.uninit, .value raw, .value s, .dead, .dead, .dead, .dead,
                     .uninit, .uninit, .value (raw &&& ~~~0xf000#64), .dead, .dead,
                     .value (s <<< (12 : Nat)), .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 3)
    (mid := ⟨1, 25, [.uninit, .value raw, .value s, .dead, .dead, .dead, .dead,
                     .uninit, .value (setSrcRegSpec raw s),
                     .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  exact run_executes (fuel := 6) rfl

theorem exec_set_src_reg_panic (raw s : Word) (hs : decide (s.toNat < 16) = false) :
    FaultsWith setSrcRegBody (initial setSrcRegBody [raw, s]) .assertionFailed := by
  have h0 : initial setSrcRegBody [raw, s] =
      ⟨0, 0, [.uninit, .value raw, .value s, .dead, .dead, .dead, .dead,
              .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩ := rfl
  rw [h0]
  refine runN_faults (n := 5)
    (mid := ⟨0, 5, [.uninit, .value raw, .value s, .uninit,
                    .value (boolWord (decide (s.toNat < (16#64).toNat))), .uninit, .dead,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  have h16 : (16#64).toNat = 16 := rfl
  have hb : boolWord (decide (s.toNat < (16#64).toNat)) = 0 := by
    rw [h16, hs]; rfl
  rw [hb]
  refine runN_faults (n := 3)
    (mid := ⟨2, 2, [.uninit, .value raw, .value s, .uninit, .uninit, .dead, .uninit,
                    .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  exact .fault rfl

theorem exec_offset (raw : Word) :
    Executes offsetBody (initial offsetBody [raw]) (offsetSpec raw)
      [.value (offsetSpec raw), .value raw, .dead, .dead, .dead] :=
  runN_executes (n := 6)
    (mid := ⟨0, 6, [.uninit, .value raw, .uninit, .value (raw >>> (16 : Nat)), .dead]⟩) rfl
    (run_executes (fuel := 5) rfl)

theorem exec_set_offset (raw off : Word) :
    Executes setOffsetBody (initial setOffsetBody [raw, off]) 0
      [.value 0, .value (setOffsetSpec raw off),
       .value off, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead] := by
  have h0 : initial setOffsetBody [raw, off] =
      ⟨0, 0, [.uninit, .value raw, .value off, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩ := rfl
  rw [h0]
  refine runN_executes (n := 5)
    (mid := ⟨0, 5, [.uninit, .value raw, .value off, .uninit, .uninit, .uninit, .value raw, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 5)
    (mid := ⟨0, 10, [.uninit, .value raw, .value off, .uninit, .uninit, .value (raw &&& ~~~0xffff0000#64), .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 6)
    (mid := ⟨0, 16, [.uninit, .value raw, .value off, .uninit, .uninit, .value (raw &&& ~~~0xffff0000#64), .dead, .dead, .uninit, .uninit, .value (off &&& 0xffff#64), .uninit]⟩) rfl ?_
  refine runN_executes (n := 5)
    (mid := ⟨0, 21, [.uninit, .value raw, .value off, .uninit, .uninit, .value (raw &&& ~~~0xffff0000#64), .dead, .dead, .value ((off &&& 0xffff#64) <<< (16 : Nat)), .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 3)
    (mid := ⟨0, 24, [.uninit, .value raw, .value off, .uninit, .value (setOffsetSpec raw off), .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  exact run_executes (fuel := 6) rfl

theorem exec_imm (raw : Word) :
    Executes immBody (initial immBody [raw]) (immSpec raw)
      [.value (immSpec raw), .value raw, .dead, .dead, .dead] :=
  runN_executes (n := 6)
    (mid := ⟨0, 6, [.uninit, .value raw, .uninit, .value (raw >>> (32 : Nat)), .dead]⟩) rfl
    (run_executes (fuel := 5) rfl)

theorem exec_set_imm (raw im : Word) :
    Executes setImmBody (initial setImmBody [raw, im]) 0
      [.value 0, .value (setImmSpec raw im),
       .value im, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead] := by
  have h0 : initial setImmBody [raw, im] =
      ⟨0, 0, [.uninit, .value raw, .value im, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩ := rfl
  rw [h0]
  refine runN_executes (n := 7)
    (mid := ⟨0, 7, [.uninit, .value raw, .value im, .uninit, .uninit, .value (raw &&& 0x00000000ffffffff#64), .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 6)
    (mid := ⟨0, 13, [.uninit, .value raw, .value im, .uninit, .uninit, .value (raw &&& 0x00000000ffffffff#64), .dead, .uninit, .uninit, .value (im &&& 0xffffffff#64), .uninit]⟩) rfl ?_
  refine runN_executes (n := 5)
    (mid := ⟨0, 18, [.uninit, .value raw, .value im, .uninit, .uninit, .value (raw &&& 0x00000000ffffffff#64), .dead, .value ((im &&& 0xffffffff#64) <<< (32 : Nat)), .dead, .dead, .dead]⟩) rfl ?_
  refine runN_executes (n := 3)
    (mid := ⟨0, 21, [.uninit, .value raw, .value im, .uninit, .value (setImmSpec raw im), .dead, .dead, .dead, .dead, .dead, .dead]⟩) rfl ?_
  exact run_executes (fuel := 6) rfl

/-!
## Bitfield Lens Laws (`Get-Put`, `Put-Get`, `Put-Put`), Frame Preservation, and Bounds
-/

theorem shift_extract_insert (w : Word) (k b : Nat) (hkb : k + b ≤ 64) :
    (((w <<< k) >>> k) &&& ((BitVec.allOnes b).setWidth 64)) =
      w &&& ((BitVec.allOnes b).setWidth 64) := by
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_setWidth,
        BitVec.getLsbD_shiftLeft]
  by_cases hib : i < b
  · have hik : k + i < 64 := by omega
    have hnk : ¬(k + i < k) := by omega
    simp [hib, hik, hnk, BitVec.getLsbD_eq_getElem hi]
  · simp [hib]

theorem shift_insert_extract (w : Word) (k b : Nat) :
    ((w >>> k) &&& ((BitVec.allOnes b).setWidth 64)) <<< k =
      w &&& (((BitVec.allOnes b).setWidth 64) <<< k) := by
  ext i hi
  simp [BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getLsbD_allOnes]
  by_cases hki : i < k
  · simp [hki]
  · have hsub : k + (i - k) = i := by omega
    simp [hki, hsub, BitVec.getLsbD_eq_getElem hi]

theorem setWidth_signExtend_mask (w : Word) (b : Nat) :
    ((w.setWidth b).signExtend 64) &&& ((BitVec.allOnes b).setWidth 64) =
      w &&& ((BitVec.allOnes b).setWidth 64) := by
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_signExtend, BitVec.getElem_setWidth]
  by_cases hib : i < b
  · simp [hib, BitVec.getLsbD_eq_getElem hi]
  · simp [hib]

theorem mask_setWidth_eq (w : Word) (b : Nat) (hb : b ≤ 64) :
    (w &&& ((BitVec.allOnes b).setWidth 64)).setWidth b = w.setWidth b := by
  ext i hi
  have hi64 : i < 64 := Nat.lt_of_lt_of_le hi hb
  simp [BitVec.getElem_setWidth, BitVec.getElem_and, BitVec.getElem_allOnes, hi, hi64]

theorem get_put_code (raw c : Word) (hc : c &&& 0xff#64 = c) :
    codeSpec (setCodeSpec raw c) = c := by
  unfold codeSpec setCodeSpec
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.not_and_self, hc]
  simp

theorem put_get_code (raw : Word) :
    setCodeSpec raw (codeSpec raw) = raw := by
  unfold setCodeSpec codeSpec
  rw [← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]

theorem put_put_code (raw c1 c2 : Word) (hc1 : c1 &&& 0xff#64 = c1) :
    setCodeSpec (setCodeSpec raw c1) c2 = setCodeSpec raw c2 := by
  unfold setCodeSpec
  have h1 : c1 &&& ~~~0xff#64 = 0#64 := by
    rw [← hc1, BitVec.and_assoc, BitVec.and_not_self]
    simp
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, h1, BitVec.or_zero]

theorem get_put_dst_reg (raw d : Word) (hd : d &&& 0x0f#64 = d) :
    dstRegSpec (setDstRegSpec raw d) = d := by
  unfold dstRegSpec setDstRegSpec
  have hd_shift : (d <<< (8 : Nat)) &&& 0x0f00#64 = d <<< (8 : Nat) := by
    rw [← hd, BitVec.shiftLeft_and_distrib, BitVec.and_assoc]; rfl
  have h1 : ((raw &&& ~~~0x0f00#64 ||| d <<< (8 : Nat)) &&& 0x0f00#64) = d <<< (8 : Nat) := by
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.not_and_self, hd_shift]
    simp
  rw [h1]
  have h8 : 0xff#64 = (BitVec.allOnes 8).setWidth 64 := rfl
  rw [h8, shift_extract_insert d 8 8 (by decide), ← h8, ← hd, BitVec.and_assoc]
  rfl

theorem put_get_dst_reg (raw : Word) :
    setDstRegSpec raw (dstRegSpec raw) = raw := by
  unfold setDstRegSpec dstRegSpec
  have h1 : ((raw &&& 0x0f00#64) >>> (8 : Nat)) &&& 0xff#64 =
      (raw >>> (8 : Nat)) &&& ((BitVec.allOnes 4).setWidth 64) := by
    rw [BitVec.ushiftRight_and_distrib, BitVec.and_assoc]; rfl
  rw [h1, shift_insert_extract raw 8 4]
  change (raw &&& ~~~0x0f00#64) ||| (raw &&& 0x0f00#64) = raw
  rw [← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]

theorem put_put_dst_reg (raw d1 d2 : Word) (hd1 : d1 &&& 0x0f#64 = d1) :
    setDstRegSpec (setDstRegSpec raw d1) d2 = setDstRegSpec raw d2 := by
  unfold setDstRegSpec
  have h1 : (d1 <<< (8 : Nat)) &&& ~~~0x0f00#64 = 0#64 := by
    rw [← hd1, BitVec.shiftLeft_and_distrib, BitVec.and_assoc]
    change (d1 <<< (8 : Nat)) &&& 0#64 = 0#64
    exact BitVec.and_zero
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, h1, BitVec.or_zero]

theorem get_put_src_reg (raw s : Word) (hs : s &&& 0x0f#64 = s) :
    srcRegSpec (setSrcRegSpec raw s) = s := by
  unfold srcRegSpec setSrcRegSpec
  have hs_shift : (s <<< (12 : Nat)) &&& 0xf000#64 = s <<< (12 : Nat) := by
    rw [← hs, BitVec.shiftLeft_and_distrib, BitVec.and_assoc]; rfl
  have h1 : ((raw &&& ~~~0xf000#64 ||| s <<< (12 : Nat)) &&& 0xf000#64) = s <<< (12 : Nat) := by
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.not_and_self, hs_shift]
    simp
  rw [h1]
  have h8 : 0xff#64 = (BitVec.allOnes 8).setWidth 64 := rfl
  rw [h8, shift_extract_insert s 12 8 (by decide), ← h8, ← hs, BitVec.and_assoc]
  rfl

theorem put_get_src_reg (raw : Word) :
    setSrcRegSpec raw (srcRegSpec raw) = raw := by
  unfold setSrcRegSpec srcRegSpec
  have h1 : ((raw &&& 0xf000#64) >>> (12 : Nat)) &&& 0xff#64 =
      (raw >>> (12 : Nat)) &&& ((BitVec.allOnes 4).setWidth 64) := by
    rw [BitVec.ushiftRight_and_distrib, BitVec.and_assoc]; rfl
  rw [h1, shift_insert_extract raw 12 4]
  change (raw &&& ~~~0xf000#64) ||| (raw &&& 0xf000#64) = raw
  rw [← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]

theorem put_put_src_reg (raw s1 s2 : Word) (hs1 : s1 &&& 0x0f#64 = s1) :
    setSrcRegSpec (setSrcRegSpec raw s1) s2 = setSrcRegSpec raw s2 := by
  unfold setSrcRegSpec
  have h1 : (s1 <<< (12 : Nat)) &&& ~~~0xf000#64 = 0#64 := by
    rw [← hs1, BitVec.shiftLeft_and_distrib, BitVec.and_assoc]
    change (s1 <<< (12 : Nat)) &&& 0#64 = 0#64
    exact BitVec.and_zero
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, h1, BitVec.or_zero]

theorem get_put_offset (raw off : Word) (hoff : castSigned 16 off = off) :
    offsetSpec (setOffsetSpec raw off) = off := by
  unfold offsetSpec setOffsetSpec
  rw [BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib,
      BitVec.and_or_distrib_right, BitVec.and_assoc]
  have hm0 : ((~~~0xffff0000#64) >>> (16 : Nat)) &&& 0xffff#64 = 0#64 := rfl
  rw [hm0, BitVec.and_zero, BitVec.zero_or]
  have h16 : 0xffff#64 = (BitVec.allOnes 16).setWidth 64 := rfl
  rw [h16, shift_extract_insert (off &&& (BitVec.allOnes 16).setWidth 64) 16 16 (by decide),
      BitVec.and_assoc, BitVec.and_self]
  unfold castSigned at hoff ⊢
  rw [mask_setWidth_eq off 16 (by decide), hoff]

theorem put_get_offset (raw : Word) :
    setOffsetSpec raw (offsetSpec raw) = raw := by
  unfold setOffsetSpec offsetSpec castSigned
  have h16 : 0xffff#64 = (BitVec.allOnes 16).setWidth 64 := rfl
  rw [h16, setWidth_signExtend_mask _ 16, BitVec.and_assoc, BitVec.and_self,
      shift_insert_extract raw 16 16]
  change (raw &&& ~~~0xffff0000#64) ||| (raw &&& 0xffff0000#64) = raw
  rw [← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]

theorem put_put_offset (raw o1 o2 : Word) :
    setOffsetSpec (setOffsetSpec raw o1) o2 = setOffsetSpec raw o2 := by
  unfold setOffsetSpec
  have h1 : ((o1 &&& 0xffff#64) <<< (16 : Nat)) &&& ~~~0xffff0000#64 = 0#64 := by
    rw [BitVec.shiftLeft_and_distrib, BitVec.and_assoc]
    change (o1 <<< (16 : Nat)) &&& 0#64 = 0#64
    exact BitVec.and_zero
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, h1, BitVec.or_zero]

theorem get_put_imm (raw im : Word) (him : castSigned 32 im = im) :
    immSpec (setImmSpec raw im) = im := by
  unfold immSpec setImmSpec
  rw [BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib,
      BitVec.and_or_distrib_right, BitVec.and_assoc]
  have hm0 : ((0x00000000ffffffff#64) >>> (32 : Nat)) &&& 0xffffffff#64 = 0#64 := rfl
  rw [hm0, BitVec.and_zero, BitVec.zero_or]
  have h32 : 0xffffffff#64 = (BitVec.allOnes 32).setWidth 64 := rfl
  rw [h32, shift_extract_insert (im &&& (BitVec.allOnes 32).setWidth 64) 32 32 (by decide),
      BitVec.and_assoc, BitVec.and_self]
  unfold castSigned at him ⊢
  rw [mask_setWidth_eq im 32 (by decide), him]

theorem put_get_imm (raw : Word) :
    setImmSpec raw (immSpec raw) = raw := by
  unfold setImmSpec immSpec castSigned
  have h32 : 0xffffffff#64 = (BitVec.allOnes 32).setWidth 64 := rfl
  rw [h32, setWidth_signExtend_mask _ 32, BitVec.and_assoc, BitVec.and_self,
      shift_insert_extract raw 32 32]
  change (raw &&& ~~~0xffffffff00000000#64) ||| (raw &&& 0xffffffff00000000#64) = raw
  rw [← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]

theorem put_put_imm (raw i1 i2 : Word) :
    setImmSpec (setImmSpec raw i1) i2 = setImmSpec raw i2 := by
  unfold setImmSpec
  have h1 : ((i1 &&& 0xffffffff#64) <<< (32 : Nat)) &&& 0x00000000ffffffff#64 = 0#64 := by
    rw [BitVec.shiftLeft_and_distrib, BitVec.and_assoc]
    change (i1 <<< (32 : Nat)) &&& 0#64 = 0#64
    exact BitVec.and_zero
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, h1, BitVec.or_zero]

/-!
## Cross-Field Frame Preservation & Unconditional `< 16` Register Bounds
-/

theorem set_code_preserves_dst_reg (raw c : Word) (hc : c &&& 0xff#64 = c) :
    dstRegSpec (setCodeSpec raw c) = dstRegSpec raw := by
  unfold dstRegSpec setCodeSpec
  have hmask : ~~~0xff#64 &&& 0x0f00#64 = 0x0f00#64 := rfl
  have hc0 : c &&& 0x0f00#64 = 0#64 := by
    rw [← hc, BitVec.and_assoc]
    change c &&& 0#64 = 0#64
    exact BitVec.and_zero
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, hmask, hc0, BitVec.or_zero]

theorem set_code_preserves_src_reg (raw c : Word) (hc : c &&& 0xff#64 = c) :
    srcRegSpec (setCodeSpec raw c) = srcRegSpec raw := by
  unfold srcRegSpec setCodeSpec
  have hmask : ~~~0xff#64 &&& 0xf000#64 = 0xf000#64 := rfl
  have hc0 : c &&& 0xf000#64 = 0#64 := by
    rw [← hc, BitVec.and_assoc]
    change c &&& 0#64 = 0#64
    exact BitVec.and_zero
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, hmask, hc0, BitVec.or_zero]

theorem set_code_preserves_offset (raw c : Word) (hc : c &&& 0xff#64 = c) :
    offsetSpec (setCodeSpec raw c) = offsetSpec raw := by
  unfold offsetSpec setCodeSpec
  have hinner : (((raw &&& ~~~0xff#64) ||| c) >>> (16 : Nat)) &&& 0xffff#64 =
      (raw >>> (16 : Nat)) &&& 0xffff#64 := by
    rw [BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib,
        BitVec.and_or_distrib_right, BitVec.and_assoc]
    have hm : ((~~~0xff#64) >>> (16 : Nat)) &&& 0xffff#64 = 0xffff#64 := rfl
    have hc16 : (c >>> (16 : Nat)) &&& 0xffff#64 = 0#64 := by
      rw [← hc, BitVec.ushiftRight_and_distrib, BitVec.and_assoc]
      change (c >>> (16 : Nat)) &&& 0#64 = 0#64
      exact BitVec.and_zero
    rw [hm, hc16, BitVec.or_zero]
  rw [hinner]

theorem set_code_preserves_imm (raw c : Word) (hc : c &&& 0xff#64 = c) :
    immSpec (setCodeSpec raw c) = immSpec raw := by
  unfold immSpec setCodeSpec
  have hinner : (((raw &&& ~~~0xff#64) ||| c) >>> (32 : Nat)) &&& 0xffffffff#64 =
      (raw >>> (32 : Nat)) &&& 0xffffffff#64 := by
    rw [BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib,
        BitVec.and_or_distrib_right, BitVec.and_assoc]
    have hm : ((~~~0xff#64) >>> (32 : Nat)) &&& 0xffffffff#64 = 0xffffffff#64 := rfl
    have hc32 : (c >>> (32 : Nat)) &&& 0xffffffff#64 = 0#64 := by
      rw [← hc, BitVec.ushiftRight_and_distrib, BitVec.and_assoc]
      change (c >>> (32 : Nat)) &&& 0#64 = 0#64
      exact BitVec.and_zero
    rw [hm, hc32, BitVec.or_zero]
  rw [hinner]

theorem dstRegSpec_lt_16 (raw : Word) : (dstRegSpec raw).toNat < 16 := by
  unfold dstRegSpec
  have h1 : ((raw &&& 0x0f00#64) >>> (8 : Nat)) &&& 0xff#64 =
      (raw >>> (8 : Nat)) &&& 0x0f#64 := by
    rw [BitVec.ushiftRight_and_distrib, BitVec.and_assoc]
    rfl
  rw [h1]
  have hle : ((raw >>> (8 : Nat)) &&& 0x0f#64).toNat ≤ (0x0f#64).toNat := by
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  have h15 : (0x0f#64).toNat = 15 := rfl
  omega

theorem srcRegSpec_lt_16 (raw : Word) : (srcRegSpec raw).toNat < 16 := by
  unfold srcRegSpec
  have h1 : ((raw &&& 0xf000#64) >>> (12 : Nat)) &&& 0xff#64 =
      (raw >>> (12 : Nat)) &&& 0x0f#64 := by
    rw [BitVec.ushiftRight_and_distrib, BitVec.and_assoc]
    rfl
  rw [h1]
  have hle : ((raw >>> (12 : Nat)) &&& 0x0f#64).toNat ≤ (0x0f#64).toNat := by
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  have h15 : (0x0f#64).toNat = 15 := rfl
  omega

end EbpfInstructionExtensionProbe
