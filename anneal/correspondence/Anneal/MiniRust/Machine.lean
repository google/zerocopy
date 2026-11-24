-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Anneal.MiniRust.Syntax
import Anneal.MiniRust.Memory

namespace Anneal.MiniRust

/-!
# MiniRust Small-Step Operational Machine (`Anneal.MiniRust.Machine`)

Total, constructive small-step operational semantics for MiniRust transcribed
from upstream `minirust/minirust` commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`:
- `spec/lang/machine.md`
- `spec/lang/step/expressions.md`
- `spec/lang/step/operators.md`
- `spec/lang/step/statements.md`
- `spec/lang/step/terminators.md`

Separates authentic upstream `throw_ub!` Undefined Behavior (`StepOutcome.ub`)
from static well-formedness / internal `panic!` / `assert!` violations
(`StepOutcome.illFormed`):
- Authentic UB (`StepOutcome.ub`): unchecked signed/unsigned arithmetic overflow
  (`AddUnchecked`, `SubUnchecked`, `MulUnchecked`), shift count `< 0` or
  `>= bits` (`ShlUnchecked`, `ShrUnchecked`), division/remainder by zero and
  signed `INT_MIN / -1` or `INT_MIN % -1`, invalid `bool`/enum discriminant byte
  decoding or `Transmute` size mismatch / target decoding, uninitialized or dead
  local access, `Terminator::Unreachable`, and `StackPopAction::BottomOfStack`
  `Return` (`"the start function must not return"`).
- Non-upstream harness return-observation hook: `MrTerminator.exitWith` reads
  the synthesized `0`-arg, `1`-ZST `start` wrapper function's return-slot local
  on halt (where upstream `IntrinsicOp::Exit` halts without a value payload).
-/

/-- Operational evaluation error separating authentic MiniRust `throw_ub!`
(`.ub`) from upstream `throw_ill_formed!` / `panic!` / `assert!` paths
(`.illFormed`). -/
inductive EvalError where
  | ub (reason : String)
  | illFormed (reason : String)

/-- Lift a `BasicMemory` error (all of which correspond to `throw_ub!` in
`spec/mem/basic.md`) into `EvalError.ub`. -/
def liftMemRes {α : Type} : Except String α → Except EvalError α
  | .ok v => .ok v
  | .error msg => .error (.ub msg)

/-! ## Mathematical Integer Helpers for Operators -/

/-- Truncated division toward zero on `Int`
(`spec/lang/step/operators.md`). -/
def mrIntTdiv : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.div m n)
  | .ofNat m, .negSucc n => Int.neg (.ofNat (Nat.div m (Nat.succ n)))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.div (Nat.succ m) n))
  | .negSucc m, .negSucc n => .ofNat (Nat.div (Nat.succ m) (Nat.succ n))

/-- Truncated remainder toward zero on `Int`
(`spec/lang/step/operators.md`). -/
def mrIntTmod : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.mod m n)
  | .ofNat m, .negSucc n => .ofNat (Nat.mod m (Nat.succ n))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.mod (Nat.succ m) n))
  | .negSucc m, .negSucc n => Int.neg (.ofNat (Nat.mod (Nat.succ m) (Nat.succ n)))

/-- Arithmetic right shift on mathematical `Int`. -/
def mrIntShiftRight : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftRight n s)
  | .negSucc n, s => .negSucc (Nat.shiftRight n s)

/-- Left shift on mathematical `Int`. -/
def mrIntShiftLeft : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftLeft n s)
  | .negSucc n, s => .negSucc (Nat.shiftLeft (n + 1) s - 1)

/-- Bitwise complement `!x = -x - 1` on mathematical `Int`. -/
def mrIntNot : Int → Int
  | .ofNat n => .negSucc n
  | .negSucc n => .ofNat n

/-- Count 1-bits in the low `n` bits of unsigned `u`. -/
def countOnesNat : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, u => Nat.mod u 2 + countOnesNat n (Nat.div u 2)

/-- Three-way ordering result (`-1`, `0`, `1`). -/
inductive MrOrd where
  | less
  | equal
  | greater

/-- Compare two mathematical integers. -/
def cmpInt (l r : Int) : MrOrd :=
  if decide (l < r) then .less
  else if l == r then .equal
  else .greater

/-- Compare two Booleans (`false < true`). -/
def cmpBool : Bool → Bool → MrOrd
  | false, true => .less
  | true, false => .greater
  | _, _ => .equal

/-! ## Operator and Cast Evaluation (`spec/lang/step/operators.md`) -/

/-- Evaluate `IntUnOp` (`spec/lang/step/operators.md`: `eval_int_un_op`). -/
def evalIntUnOp (op : IntUnOp) (operand : Int) (it : IntType) :
    Except EvalError (Int × IntType) :=
  match op with
  | .neg => .ok (it.bringInBounds (Neg.neg operand), it)
  | .bitNot => .ok (it.bringInBounds (mrIntNot operand), it)
  | .countOnes =>
    let u := intEmodNat operand (Nat.pow 2 it.bitWidth)
    .ok (Int.ofNat (countOnesNat it.bitWidth u), u32Ty)

/-- Transmute `val` from `oldTy` to `newTy` (`spec/lang/representation.md`:
`Machine::transmute`, `spec/lang/step/operators.md`: `CastOp::Transmute`). -/
def evalTransmute (val : MrValue) (oldTy newTy : MrType) :
    Except EvalError MrValue :=
  if !Nat.beq oldTy.size.bytes newTy.size.bytes then
    .error (.ub "transmute between types of different size")
  else
    match mrEncode oldTy val with
    | none => .error (.illFormed "transmute source value violates invariant")
    | some bytes =>
      match mrDecode newTy bytes with
      | none => .error (.ub "transmuted value is not valid at new type")
      | some val' => .ok val'

/-- Evaluate `CastOp` (`spec/lang/step/operators.md`: `eval_cast_op`). -/
def evalCastOp (castOp : CastOp) (operand : MrValue) (oldTy : MrType) :
    Except EvalError (MrValue × MrType) :=
  match castOp with
  | .intToInt targetIt =>
    match operand with
    | .int i => .ok (.int (targetIt.bringInBounds i), .int targetIt)
    | _ => .error (.illFormed "non-integer input to int-to-int cast")
  | .transmute newTy =>
    match evalTransmute operand oldTy newTy with
    | .error err => .error err
    | .ok val' => .ok (val', newTy)

/-- Evaluate `MrUnOp` (`spec/lang/step/operators.md`: `eval_un_op`). -/
def evalUnOp (op : MrUnOp) (operand : MrValue) (opTy : MrType) :
    Except EvalError (MrValue × MrType) :=
  match op with
  | .int iop =>
    match opTy, operand with
    | .int it, .int v =>
      match evalIntUnOp iop v it with
      | .error err => .error err
      | .ok (res, retIt) => .ok (.int res, .int retIt)
    | _, _ => .error (.illFormed "non-integer input to integer operation")
  | .cast cop => evalCastOp cop operand opTy

/-- Evaluate `IntBinOp` on mathematical integers (`spec/lang/step/operators.md`:
`eval_int_bin_op`). The caller wraps the result with `it.bringInBounds`. -/
def evalIntBinOp (op : IntBinOp) (left right : Int) (it : IntType) :
    Except EvalError Int :=
  match op with
  | .add => .ok (left + right)
  | .addUnchecked =>
    let res := left + right
    if !it.canRepresent res then .error (.ub "overflow in unchecked add")
    else .ok res
  | .sub => .ok (left - right)
  | .subUnchecked =>
    let res := left - right
    if !it.canRepresent res then .error (.ub "overflow in unchecked sub")
    else .ok res
  | .mul => .ok (left * right)
  | .mulUnchecked =>
    let res := left * right
    if !it.canRepresent res then .error (.ub "overflow in unchecked mul")
    else .ok res
  | .div =>
    if right == 0 then .error (.ub "division by zero")
    else
      let res := mrIntTdiv left right
      if !it.canRepresent res then .error (.ub "overflow in division")
      else .ok res
  | .divExact =>
    if right == 0 then .error (.ub "division by zero")
    else
      let res := mrIntTdiv left right
      if !it.canRepresent res then .error (.ub "overflow in division")
      else if !(mrIntTmod left right == 0) then
        .error (.ub "non-zero remainder in exact division")
      else .ok res
  | .rem =>
    if right == 0 then .error (.ub "modulus of remainder is zero")
    else if !it.canRepresent (mrIntTdiv left right) then
      .error (.ub "overflow in remainder")
    else .ok (mrIntTmod left right)
  | .shl =>
    let bits := it.bitWidth
    if Nat.beq bits 0 then .error (.illFormed "zero-width shift")
    else
      let off := intEmodNat right bits
      .ok (mrIntShiftLeft left off)
  | .shr =>
    let bits := it.bitWidth
    if Nat.beq bits 0 then .error (.illFormed "zero-width shift")
    else
      let off := intEmodNat right bits
      .ok (mrIntShiftRight left off)
  | .shlUnchecked =>
    let bits := it.bitWidth
    if decide (right < 0) || decide (Int.ofNat bits ≤ right) then
      .error (.ub "overflow in unchecked shift")
    else
      .ok (mrIntShiftLeft left right.toNat)
  | .shrUnchecked =>
    let bits := it.bitWidth
    if decide (right < 0) || decide (Int.ofNat bits ≤ right) then
      .error (.ub "overflow in unchecked shift")
    else
      .ok (mrIntShiftRight left right.toNat)
  | .bitAnd =>
    let m := Nat.pow 2 it.bitWidth
    .ok (Int.ofNat (Nat.land (intEmodNat left m) (intEmodNat right m)))
  | .bitOr =>
    let m := Nat.pow 2 it.bitWidth
    .ok (Int.ofNat (Nat.lor (intEmodNat left m) (intEmodNat right m)))
  | .bitXor =>
    let m := Nat.pow 2 it.bitWidth
    .ok (Int.ofNat (Nat.xor (intEmodNat left m) (intEmodNat right m)))

/-- Convert a three-way comparison result into a MiniRust value and type
(`spec/lang/step/operators.md`: `eval_rel_op`). -/
def evalRelOp (rel : RelOp) (ord : MrOrd) : MrValue × MrType :=
  match rel with
  | .lt => (.bool (match ord with | .less => true | _ => false), .bool)
  | .gt => (.bool (match ord with | .greater => true | _ => false), .bool)
  | .le => (.bool (match ord with | .greater => false | _ => true), .bool)
  | .ge => (.bool (match ord with | .less => false | _ => true), .bool)
  | .eq => (.bool (match ord with | .equal => true | _ => false), .bool)
  | .ne => (.bool (match ord with | .equal => false | _ => true), .bool)
  | .cmp =>
    let v : Int := match ord with
      | .less => Neg.neg 1
      | .equal => 0
      | .greater => 1
    (.int v, .int i8Ty)

/-- Evaluate `MrBinOp` (`spec/lang/step/operators.md`: `eval_bin_op`). -/
def evalBinOp (op : MrBinOp) (left : MrValue) (lTy : MrType)
    (right : MrValue) : Except EvalError (MrValue × MrType) :=
  match op with
  | .int iop =>
    match lTy, left, right with
    | .int it, .int l, .int r =>
      match evalIntBinOp iop l r it with
      | .error err => .error err
      | .ok rawRes => .ok (.int (it.bringInBounds rawRes), .int it)
    | _, _, _ => .error (.illFormed "non-integer input to integer operation")
  | .intWithOverflow wop =>
    match lTy, left, right with
    | .int it, .int l, .int r =>
      let rawRes := match wop with
        | .add => l + r
        | .sub => l - r
        | .mul => l * r
      let overflow := !it.canRepresent rawRes
      let wrapped := it.bringInBounds rawRes
      .ok (.tuple (.cons (.int wrapped) (.cons (.bool overflow) .nil)),
        it.withOverflow)
    | _, _, _ => .error (.illFormed "non-integer input to integer operation")
  | .rel rop =>
    match lTy, left, right with
    | .int _, .int l, .int r => .ok (evalRelOp rop (cmpInt l r))
    | .bool, .bool l, .bool r => .ok (evalRelOp rop (cmpBool l r))
    | _, _, _ => .error (.illFormed "relational operator on incomparable type")

/-! ## Machine State, Stack Frames, and Small-Step Execution -/

/-- Local-variable allocation map in a stack frame (`LocalName ↦ ThinPtr`). -/
abbrev LocalMap := List (LocalName × ThinPtr)

/-- Lookup a local's pointer in `LocalMap`. -/
def localMapGet? (id : LocalName) : LocalMap → Option ThinPtr
  | [] => none
  | (k, p) :: rest => if Nat.beq k id then some p else localMapGet? id rest

/-- Remove a local from `LocalMap`, returning its old pointer if present. -/
def localMapRemove (id : LocalName) : LocalMap → Option ThinPtr × LocalMap
  | [] => (none, [])
  | (k, p) :: rest =>
    if Nat.beq k id then (some p, rest)
    else
      let (old, rest') := localMapRemove id rest
      (old, (k, p) :: rest')

/-- Insert or replace a local's pointer in `LocalMap`. -/
def localMapInsert (id : LocalName) (p : ThinPtr) (m : LocalMap) : LocalMap :=
  (id, p) :: (localMapRemove id m).2

/-- Action performed when a stack frame pops on `Terminator::Return`
(`spec/lang/machine.md`: `StackPopAction`). -/
inductive StackPopAction where
  | bottomOfStack
  | backToCaller (retValPtr : ThinPtr) (nextBlock : Option BbName)

/-- Active call-stack frame (`spec/lang/machine.md`: `StackFrame`). -/
structure StackFrame where
  func : MrFunction
  locals : LocalMap
  stackPopAction : StackPopAction
  nextBlock : BbName
  nextStmt : Nat

/-- Complete MiniRust abstract machine state (`spec/lang/machine.md`:
`Machine`). `stack` has the active frame at the head (`cur :: callers`). -/
structure Machine where
  prog : MrProgram
  mem : MrMemory
  stack : List StackFrame

/-- Single-step outcome of the MiniRust abstract machine. -/
inductive StepOutcome where
  | step (next : Machine)
  | returned (val : MrValue)
  | ub (reason : String)
  | illFormed (reason : String)

/-- Convert an `EvalError` into its corresponding terminal `StepOutcome`. -/
def stepOutcomeOfError : EvalError → StepOutcome
  | .ub msg => .ub msg
  | .illFormed msg => .illFormed msg

/-- Typed load from memory
(`spec/lang/representation.md`: `Machine::typed_load`). -/
def typedLoad (mem : MrMemory) (ptr : ThinPtr) (ty : MrType) (al : Align) :
    Except EvalError MrValue :=
  match mem.load ptr ty.size al with
  | .error msg => .error (.ub msg)
  | .ok bytes =>
    match mrDecode ty bytes with
    | none =>
      .error (.ub
        "load at type but the data in memory violates the language invariant")
    | some v => .ok v

/-- Typed store to memory
(`spec/lang/representation.md`: `Machine::typed_store`). -/
def typedStore (mem : MrMemory) (ptr : ThinPtr) (val : MrValue) (ty : MrType)
    (al : Align) : Except EvalError MrMemory :=
  match mrEncode ty val with
  | none => .error (.illFormed "store of value violating language invariant")
  | some bytes => liftMemRes (mem.store ptr bytes al)

/-- Offset a thin pointer in bounds of its allocation
(`spec/lang/step/operators.md`: `ptr_offset_inbounds`). -/
def ptrOffsetInbounds (mem : MrMemory) (ptr : ThinPtr) (off : Nat) :
    Except EvalError ThinPtr :=
  match mem.checkPtr ptr ⟨off⟩ with
  | .error msg => .error (.ub msg)
  | .ok _ => .ok ⟨ptr.allocId, ptr.addr + off⟩

mutual
  /-- Lazily decode a `Discriminator` decision tree by loading only the tag
  bytes visited along the active branch (`spec/lang/representation.md`:
  `decode_discriminant`, `spec/lang/step/expressions.md`:
  `ValueExpr::GetDiscriminant`). -/
  def evalDiscriminantMem (mem : MrMemory) (basePtr : ThinPtr) :
      Discriminator → Except EvalError (Option Int)
    | .known val => .ok (some val)
    | .invalid => .ok none
    | .branch off valTy children fallback =>
      match ptrOffsetInbounds mem basePtr off with
      | .error err => .error err
      | .ok tagPtr =>
        match mem.load tagPtr valTy.size ⟨1⟩ with
        | .error msg => .error (.ub msg)
        | .ok tagBytes =>
          match decodeInt valTy tagBytes with
          | none => .ok none
          | some v =>
            match evalDiscrBranchesMem mem basePtr v children with
            | .error err => .error err
            | .ok (some res) => .ok res
            | .ok none => evalDiscriminantMem mem basePtr fallback

  /-- Evaluate the first matching `[lo, hi)` branch in `DiscrBranches`. -/
  def evalDiscrBranchesMem (mem : MrMemory) (basePtr : ThinPtr) (v : Int) :
      DiscrBranches → Except EvalError (Option (Option Int))
    | .nil => .ok none
    | .cons lo hi child rest =>
      if decide (lo ≤ v) && decide (v < hi) then
        match evalDiscriminantMem mem basePtr child with
        | .error err => .error err
        | .ok res => .ok (some res)
      else
        evalDiscrBranchesMem mem basePtr v rest
end

/-- Evaluate a constant literal
(`spec/lang/step/expressions.md`: `eval_constant`). -/
def evalConstant (c : MrConstant) : MrValue :=
  match c with
  | .int i => .int i
  | .bool b => .bool b

mutual
  /-- Evaluate a `PlaceExpr` in `frame` and `mem`
  (`spec/lang/step/expressions.md`: `eval_place`). -/
  def evalPlace (frame : StackFrame) (mem : MrMemory) :
      PlaceExpr → Except EvalError (MrPlace × MrType)
    | .local name =>
      match listGet? frame.func.locals name with
      | none => .error (.illFormed "access to unknown local")
      | some ty =>
        match localMapGet? name frame.locals with
        | none => .error (.ub "access to a dead local")
        | some ptr => .ok (⟨ptr, true⟩, ty)
    | .field root fieldIdx =>
      match evalPlace frame mem root with
      | .error err => .error err
      | .ok (place, ty) =>
        match ty with
        | .tuple fields _ _ =>
          match fields.get? fieldIdx with
          | none => .error (.illFormed "field projection to invalid field")
          | some (off, fieldTy) =>
            match ptrOffsetInbounds mem place.ptr off with
            | .error err => .error err
            | .ok ptr' => .ok ({ place with ptr := ptr' }, fieldTy)
        | _ => .error (.illFormed "field projection on non-projectable type")
    | .index root idxExpr =>
      match evalPlace frame mem root with
      | .error err => .error err
      | .ok (place, ty) =>
        match evalValue frame mem idxExpr with
        | .error err => .error err
        | .ok (.int idx, _) =>
          match ty with
          | .array elem count =>
            if decide (idx < 0) || decide (Int.ofNat count ≤ idx) then
              .error (.ub "access to out-of-bounds index")
            else
              let off := idx.toNat * elem.size.bytes
              match ptrOffsetInbounds mem place.ptr off with
              | .error err => .error err
              | .ok ptr' => .ok ({ place with ptr := ptr' }, elem)
          | _ => .error (.illFormed "index projection on non-indexable type")
        | .ok (_, _) =>
          .error (.illFormed "non-integer operand for array index")
    | .downcast root discr =>
      match evalPlace frame mem root with
      | .error err => .error err
      | .ok (place, ty) =>
        match ty with
        | .enum variants _ _ _ _ =>
          match variants.find? discr with
          | none =>
            .error (.illFormed "enum downcast to invalid discriminant")
          | some (varTy, _) => .ok (place, varTy)
        | _ => .error (.illFormed "enum downcast on non-enum")

  /-- Evaluate a `ValueExpr` in `frame` and `mem`
  (`spec/lang/step/expressions.md`: `eval_value`). -/
  def evalValue (frame : StackFrame) (mem : MrMemory) :
      ValueExpr → Except EvalError (MrValue × MrType)
    | .constant c ty => .ok (evalConstant c, ty)
    | .tuple exprs ty =>
      match evalValueList frame mem exprs with
      | .error err => .error err
      | .ok vals => .ok (.tuple vals, ty)
    | .variant discr data enumTy =>
      match enumTy with
      | .enum variants _ _ _ _ =>
        match variants.find? discr with
        | none => .error (.illFormed "ValueExpr::Variant: invalid discriminant")
        | some (varTy, _) =>
          match evalValue frame mem data with
          | .error err => .error err
          | .ok (v, dataTy) =>
            if MrType.beq dataTy varTy then
              .ok (.variant discr v, enumTy)
            else
              .error (.illFormed "ValueExpr::Variant: invalid type")
      | _ => .error (.illFormed "ValueExpr::Variant: invalid type")
    | .getDiscriminant placeExpr =>
      match evalPlace frame mem placeExpr with
      | .error err => .error err
      | .ok (place, ty) =>
        match ty with
        | .enum _ discr discrTy _ _ =>
          if !place.aligned then
            .error (.ub
              "Getting the discriminant of a place based on a misaligned pointer.")
          else
            match evalDiscriminantMem mem place.ptr discr with
            | .error err => .error err
            | .ok none =>
              .error (.ub
                "ValueExpr::GetDiscriminant encountered invalid discriminant.")
            | .ok (some d) => .ok (.int d, .int discrTy)
        | _ =>
          .error (.illFormed "ValueExpr::GetDiscriminant requires enum type")
    | .load source =>
      match evalPlace frame mem source with
      | .error err => .error err
      | .ok (place, ty) =>
        if !place.aligned then
          .error (.ub "loading from a place based on a misaligned pointer")
        else
          match typedLoad mem place.ptr ty ⟨1⟩ with
          | .error err => .error err
          | .ok v => .ok (v, ty)
    | .unOp operator operand =>
      match evalValue frame mem operand with
      | .error err => .error err
      | .ok (v, ty) => evalUnOp operator v ty
    | .binOp operator left right =>
      match evalValue frame mem left with
      | .error err => .error err
      | .ok (lv, lTy) =>
        match evalValue frame mem right with
        | .error err => .error err
        | .ok (rv, _) => evalBinOp operator lv lTy rv

  /-- Evaluate a list of value expressions left-to-right. -/
  def evalValueList (frame : StackFrame) (mem : MrMemory) :
      ValueExprList → Except EvalError MrValueList
    | .nil => .ok .nil
    | .cons e rest =>
      match evalValue frame mem e with
      | .error err => .error err
      | .ok (v, _) =>
        match evalValueList frame mem rest with
        | .error err => .error err
        | .ok vs => .ok (.cons v vs)
end

/-- `StackFrame::storage_dead` (`spec/lang/step/statements.md`). -/
def storageDeadFrame (frame : StackFrame) (mem : MrMemory)
    (localId : LocalName) : Except EvalError (StackFrame × MrMemory) :=
  match listGet? frame.func.locals localId with
  | none => .error (.illFormed "storage_dead on unknown local")
  | some ty =>
    let (oldPtr, locals') := localMapRemove localId frame.locals
    match oldPtr with
    | none => .ok ({ frame with locals := locals' }, mem)
    | some ptr =>
      match mem.deallocate ptr ty.size ty.align with
      | .error msg => .error (.ub msg)
      | .ok mem' => .ok ({ frame with locals := locals' }, mem')

/-- `StackFrame::storage_live` (`spec/lang/step/statements.md`). -/
def storageLiveFrame (frame : StackFrame) (mem : MrMemory)
    (localId : LocalName) : Except EvalError (StackFrame × MrMemory) :=
  match listGet? frame.func.locals localId with
  | none => .error (.illFormed "storage_live on unknown local")
  | some ty =>
    match storageDeadFrame frame mem localId with
    | .error err => .error err
    | .ok (frame1, mem1) =>
      match mem1.allocate ty.size ty.align with
      | .error msg => .error (.ub msg)
      | .ok (mem2, ptr) =>
        .ok ({ frame1 with locals := localMapInsert localId ptr frame1.locals },
          mem2)

/-- Deallocate all live locals remaining in a frame during `Return` teardown
(`spec/lang/step/terminators.md`). -/
def deallocateAllLocals (func : MrFunction) (mem : MrMemory) :
    LocalMap → Except EvalError MrMemory
  | [] => .ok mem
  | (localId, ptr) :: rest =>
    match listGet? func.locals localId with
    | none => .error (.illFormed "teardown unknown local")
    | some ty =>
      match mem.deallocate ptr ty.size ty.align with
      | .error msg => .error (.ub msg)
      | .ok mem' => deallocateAllLocals func mem' rest

/-- Execute one statement in active frame (`spec/lang/step/statements.md` and
`spec/lang/well-formed.md`). -/
def stepStatement (prog : MrProgram) (frame : StackFrame)
    (callers : List StackFrame) (mem : MrMemory) (stmt : MrStatement) :
    StepOutcome :=
  let advance (f' : StackFrame) (m' : MrMemory) : StepOutcome :=
    .step {
      prog := prog
      mem := m'
      stack := { f' with nextStmt := f'.nextStmt + 1 } :: callers
    }
  match stmt with
  | .assign dst src =>
    match evalPlace frame mem dst with
    | .error err => stepOutcomeOfError err
    | .ok (place, ty) =>
      match evalValue frame mem src with
      | .error err => stepOutcomeOfError err
      | .ok (val, _) =>
        if !place.aligned then
          .ub "storing to a place based on a misaligned pointer"
        else
          match typedStore mem place.ptr val ty ⟨1⟩ with
          | .error err => stepOutcomeOfError err
          | .ok mem' => advance frame mem'
  | .placeMention placeExpr =>
    match evalPlace frame mem placeExpr with
    | .error err => stepOutcomeOfError err
    | .ok _ => advance frame mem
  | .setDiscriminant dst value =>
    match evalPlace frame mem dst with
    | .error err => stepOutcomeOfError err
    | .ok (place, ty) =>
      match ty with
      | .enum variants _ _ _ _ =>
        if !place.aligned then
          .ub "setting the discriminant of a place based on a misaligned pointer"
        else
          match variants.find? value with
          | none => .illFormed "setting an invalid discriminant"
          | some (_, tagger) =>
            match mem.load place.ptr ty.size ⟨1⟩ with
            | .error msg => .ub msg
            | .ok oldBytes =>
              match encodeDiscriminant oldBytes tagger with
              | none => .illFormed "encoding invalid discriminant tag"
              | some newBytes =>
                match mem.store place.ptr newBytes ⟨1⟩ with
                | .error msg => .ub msg
                | .ok mem' => advance frame mem'
      | _ => .illFormed "setting the discriminant type of a non-enum"
  | .deinit placeExpr =>
    match evalPlace frame mem placeExpr with
    | .error err => stepOutcomeOfError err
    | .ok (place, ty) =>
      if !place.aligned then
        .ub "de-initializing a place based on a misaligned pointer"
      else
        match mem.deinit place.ptr ty.size ⟨1⟩ with
        | .error msg => .ub msg
        | .ok mem' => advance frame mem'
  | .storageLive localId =>
    match storageLiveFrame frame mem localId with
    | .error err => stepOutcomeOfError err
    | .ok (frame', mem') => advance frame' mem'
  | .storageDead localId =>
    if Nat.beq localId frame.func.ret || frame.func.args.any (Nat.beq localId) then
      .illFormed
        "Statement::StorageDead: trying to mark argument or return local as dead"
    else
      match storageDeadFrame frame mem localId with
      | .error err => stepOutcomeOfError err
      | .ok (frame', mem') => advance frame' mem'

/-- Lookup a switch target in `cases`, falling back to `fallback`. -/
def lookupSwitchCase (v : Int) (fallback : BbName) :
    List (Int × BbName) → BbName
  | [] => fallback
  | (k, target) :: rest =>
    if k == v then target else lookupSwitchCase v fallback rest

/-- Execute a basic block's terminator (`spec/lang/step/terminators.md`). -/
def stepTerminator (prog : MrProgram) (frame : StackFrame)
    (callers : List StackFrame) (mem : MrMemory) (term : MrTerminator) :
    StepOutcome :=
  match term with
  | .goto target =>
    if !Nat.blt target frame.func.blocks.length then
      .illFormed "goto out-of-bounds basic block"
    else
      .step {
        prog := prog
        mem := mem
        stack := { frame with nextBlock := target, nextStmt := 0 } :: callers
      }
  | .switch valExpr cases fallback =>
    match evalValue frame mem valExpr with
    | .error err => stepOutcomeOfError err
    | .ok (.int v, _) =>
      let target := lookupSwitchCase v fallback cases
      if !Nat.blt target frame.func.blocks.length then
        .illFormed "switch target out-of-bounds basic block"
      else
        .step {
          prog := prog
          mem := mem
          stack := { frame with nextBlock := target, nextStmt := 0 } :: callers
        }
    | .ok (_, _) => .illFormed "switch on a non-integer"
  | .unreachable => .ub "reached unreachable code"
  | .exitWith retLocal =>
    match listGet? frame.func.locals retLocal,
        localMapGet? retLocal frame.locals with
    | some ty, some ptr =>
      match typedLoad mem ptr ty ty.align with
      | .error err => stepOutcomeOfError err
      | .ok v => .returned v
    | _, _ => .illFormed "exitWith missing return local"
  | .return_ =>
    match listGet? frame.func.locals frame.func.ret,
        localMapGet? frame.func.ret frame.locals with
    | none, _ => .illFormed "return missing return local type"
    | _, none => .illFormed "return local is dead when returning"
    | some calleeTy, some retPtr =>
      match typedLoad mem retPtr calleeTy calleeTy.align with
      | .error err => stepOutcomeOfError err
      | .ok retVal =>
        match deallocateAllLocals frame.func mem frame.locals with
        | .error err => stepOutcomeOfError err
        | .ok mem1 =>
          match frame.stackPopAction with
          | .bottomOfStack => .ub "the start function must not return"
          | .backToCaller callerRetPtr nextBlk =>
            match callers with
            | [] => .illFormed "backToCaller with empty caller stack"
            | caller :: restCallers =>
              match typedStore mem1 callerRetPtr retVal calleeTy calleeTy.align with
              | .error err => stepOutcomeOfError err
              | .ok mem2 =>
                match nextBlk with
                | none =>
                  .ub "return from a function where caller did not specify next block"
                | some blk =>
                  if !Nat.blt blk caller.func.blocks.length then
                    .illFormed "return target out-of-bounds basic block"
                  else
                    .step {
                      prog := prog
                      mem := mem2
                      stack :=
                        { caller with nextBlock := blk, nextStmt := 0 } ::
                          restCallers
                    }

/-- Single small step of the MiniRust abstract machine
(`spec/lang/machine.md`: `Machine::step`). -/
def mrStep (m : Machine) : StepOutcome :=
  match m.stack with
  | [] => .illFormed "empty call stack"
  | frame :: callers =>
    match listGet? frame.func.blocks frame.nextBlock with
    | none => .illFormed "invalid basic block"
    | some bb =>
      match listGet? bb.statements frame.nextStmt with
      | some stmt => stepStatement m.prog frame callers m.mem stmt
      | none =>
        if Nat.beq frame.nextStmt bb.statements.length then
          stepTerminator m.prog frame callers m.mem bb.terminator
        else
          .illFormed "invalid statement index"

/-! ## Multi-Step Reachability and Observable Behaviors -/

/-- Reflexive-transitive closure of `mrStep m = .step m'`. -/
inductive MrReaches : Machine → Machine → Prop where
  | refl (m : Machine) : MrReaches m m
  | tail {m₁ m₂ m₃ : Machine} :
      MrReaches m₁ m₂ → mrStep m₂ = .step m₃ → MrReaches m₁ m₃

/-- MiniRust normal return behavior from `m₀`. -/
def MrBehavior (m₀ : Machine) (v : MrValue) : Prop :=
  ∃ m : Machine, MrReaches m₀ m ∧ mrStep m = .returned v

/-- MiniRust Undefined Behavior reachability from `m₀`. -/
def MrFaultsUB (m₀ : Machine) : Prop :=
  ∃ (m : Machine) (reason : String), MrReaches m₀ m ∧ mrStep m = .ub reason

/-- MiniRust ill-formedness reachability from `m₀` (proven unreachable for all
`MiniRustAdmitted` programs). -/
def MrIllFormed (m₀ : Machine) : Prop :=
  ∃ (m : Machine) (reason : String),
    MrReaches m₀ m ∧ mrStep m = .illFormed reason

/-- MiniRust infinite divergence trace from `m₀`. -/
def MrDiverges (m₀ : Machine) : Prop :=
  ∃ trace : Nat → Machine,
    trace 0 = m₀ ∧ ∀ n : Nat, mrStep (trace n) = .step (trace (n + 1))

/-- Transitivity of `MrReaches`. -/
theorem MrReaches.trans {m₁ m₂ m₃ : Machine}
    (h12 : MrReaches m₁ m₂) (h23 : MrReaches m₂ m₃) : MrReaches m₁ m₃ := by
  induction h23 with
  | refl => exact h12
  | tail _ hstep ih => exact MrReaches.tail ih hstep

/-- Single-step prefix constructor for `MrReaches`. -/
theorem MrReaches.head {m₁ m₂ m₃ : Machine}
    (hstep : mrStep m₁ = .step m₂) (h23 : MrReaches m₂ m₃) :
    MrReaches m₁ m₃ :=
  MrReaches.trans (MrReaches.tail (MrReaches.refl m₁) hstep) h23

/-- Head-step characterization of `MrReaches` for deterministic induction. -/
inductive MrReachesHead : Machine → Machine → Prop where
  | refl (m : Machine) : MrReachesHead m m
  | head {m₁ m₂ m₃ : Machine} :
      mrStep m₁ = .step m₂ → MrReachesHead m₂ m₃ → MrReachesHead m₁ m₃

theorem MrReachesHead.trans {m₁ m₂ m₃ : Machine}
    (h12 : MrReachesHead m₁ m₂) (h23 : MrReachesHead m₂ m₃) :
    MrReachesHead m₁ m₃ := by
  induction h12 with
  | refl => exact h23
  | head hstep _ ih => exact MrReachesHead.head hstep (ih h23)

theorem MrReaches.toHead {m₁ m₂ : Machine} (h : MrReaches m₁ m₂) :
    MrReachesHead m₁ m₂ := by
  induction h with
  | refl => exact MrReachesHead.refl _
  | tail _ hstep ih =>
    exact MrReachesHead.trans ih (MrReachesHead.head hstep (MrReachesHead.refl _))

theorem mrStep_deterministic_head {m₀ m₁ m₂ : Machine} {o₁ o₂ : StepOutcome}
    (hr1 : MrReachesHead m₀ m₁) (hs1 : mrStep m₁ = o₁)
    (hns1 : ∀ m', o₁ ≠ .step m')
    (hr2 : MrReachesHead m₀ m₂) (hs2 : mrStep m₂ = o₂)
    (hns2 : ∀ m', o₂ ≠ .step m') : o₁ = o₂ := by
  revert hr2 hs2 hns2
  induction hr1 generalizing m₂ o₂ with
  | refl =>
    intro hr2 hs2 hns2
    cases hr2 with
    | refl => rw [← hs1, ← hs2]
    | head hstep _ =>
      rw [hstep] at hs1
      exact False.elim (hns1 _ hs1.symm)
  | head hstep1 _ ih =>
    intro hr2 hs2 hns2
    cases hr2 with
    | refl =>
      rw [hstep1] at hs2
      exact False.elim (hns2 _ hs2.symm)
    | head hstep2 hr2' =>
      rw [hstep1] at hstep2
      injection hstep2 with heq
      subst heq
      exact ih hs1 hr2' hs2 hns2

/-- Determinism of `MrReaches`: if `m₀` reaches a non-step outcome, no
execution from `m₀` can reach a different outcome. -/
theorem mrStep_deterministic_reaches {m₀ m₁ m₂ : Machine} {o₁ o₂ : StepOutcome}
    (hr1 : MrReaches m₀ m₁) (hs1 : mrStep m₁ = o₁)
    (hns1 : ∀ m', o₁ ≠ .step m')
    (hr2 : MrReaches m₀ m₂) (hs2 : mrStep m₂ = o₂)
    (hns2 : ∀ m', o₂ ≠ .step m') : o₁ = o₂ :=
  mrStep_deterministic_head hr1.toHead hs1 hns1 hr2.toHead hs2 hns2

/-- Fuel-bounded deterministic runner for constructive executable witnesses. -/
def mrRunFuel : Nat → Machine → StepOutcome
  | 0, m => .step m
  | n + 1, m =>
    match mrStep m with
    | .step m' => mrRunFuel n m'
    | other => other

theorem mrRunFuel_returned {n : Nat} {m₀ : Machine} {v : MrValue}
    (h : mrRunFuel n m₀ = .returned v) : MrBehavior m₀ v := by
  induction n generalizing m₀ with
  | zero => cases h
  | succ k ih =>
    dsimp only [mrRunFuel] at h
    cases hs : mrStep m₀ with
    | step m' =>
      rw [hs] at h
      cases ih h with
      | intro mf hmf =>
        exact ⟨mf, MrReaches.head hs hmf.1, hmf.2⟩
    | returned v' =>
      rw [hs] at h
      injection h with hv
      subst hv
      exact ⟨m₀, MrReaches.refl m₀, hs⟩
    | ub _ => rw [hs] at h; cases h
    | illFormed _ => rw [hs] at h; cases h

theorem mrRunFuel_ub {n : Nat} {m₀ : Machine} {r : String}
    (h : mrRunFuel n m₀ = .ub r) : MrFaultsUB m₀ := by
  induction n generalizing m₀ with
  | zero => cases h
  | succ k ih =>
    dsimp only [mrRunFuel] at h
    cases hs : mrStep m₀ with
    | step m' =>
      rw [hs] at h
      cases ih h with
      | intro mf hmf =>
        cases hmf with
        | intro r' hr' =>
          exact ⟨mf, r', MrReaches.head hs hr'.1, hr'.2⟩
    | ub r' =>
      rw [hs] at h
      exact ⟨m₀, r', MrReaches.refl m₀, hs⟩
    | returned _ => rw [hs] at h; cases h
    | illFormed _ => rw [hs] at h; cases h

end Anneal.MiniRust
