-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Char.Basic
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Ops
import Trusted.MirSemantics.Enum
import Trusted.MirSemantics.State
import Anneal.MiniRust.Syntax
import Anneal.MiniRust.Memory
import Anneal.MiniRust.Machine

namespace Anneal.MiniRust

open Trusted.MirAst
open Trusted.MirSemantics

/-!
# Anneal MIR to MiniRust Translation and Admission (`Anneal.MiniRust.Translate`)

Total, constructive translation from `Trusted.MirAst` + `Trusted.MirModel`
(Profile v1 semantics) into `Anneal.MiniRust.Syntax` and
`Anneal.MiniRust.Machine`, paired with explicit static admission predicates:

- **`MiniRustBodyAdmitted` / `MiniRustAdmitted`**: the forward-simulation
  fragment (all Profile v1 scalars, `bool`, `char` lowered to `u32`, `Ordering`,
  fieldless enums, `(T, bool)` overflow pairs, `Use`/`Copy`/`Move`/`Constant`,
  all admitted unary/binary/shift/overflow/comparison/`Cmp` ops, `IntToInt`
  casts, `Discriminant`, `StorageLive`, non-argument/non-return `StorageDead`,
  `Nop`, `Goto`, unique-key `SwitchInt`, `Return`, `Unreachable`).
- **`MiniRustExactBodyAdmitted` / `MiniRustExactAdmitted`**: the exact
  bidirectional fault-equivalence sub-fragment
  (`Anneal .fault .undefined ↔ MiniRust .ub`), which additionally forbids
  `Operand.move` on non-ZST locals (separating Anneal's conservative
  move-deinitialization from MiniRust's non-destructive `ValueExpr::Load`) and
  excludes `MirTy.char` (separating Anneal's Unicode scalar validity checks from
  MiniRust's niche-free `u32` lowering).
-/

/-! ## Type and Value Translation -/

/-- Translate `IntWidth` + `signed` into a MiniRust `IntType`. -/
noncomputable def translateIntTy (w : IntWidth) (s : Bool) : IntType :=
  { signed := if s then .signed else .unsigned
    size := ⟨w.byteSize⟩ }

/-- Mathematical discriminant integer of raw bit pattern `d` at `(w, s)`. -/
noncomputable def discrIntOfNat (w : IntWidth) (s : Bool) (d : Nat) : Int :=
  decodeScalar ⟨w, s, truncateBits w (BitVec.ofNat 128 d)⟩

/-- Mathematical tag integer stored in memory for discriminant `d` at scalar tag
representation `(tagW, tagS)`. -/
noncomputable def tagIntOfNat (tagW : IntWidth) (tagS : Bool) (d : Nat) : Int :=
  decodeScalar ⟨tagW, tagS, truncateBits tagW (BitVec.ofNat 128 d)⟩

/-- Build MiniRust `EnumVariants` for a scalar-tagged fieldless enum. -/
noncomputable def buildEnumVariants (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) : List Nat → EnumVariants
  | [] => .nil
  | d :: rest =>
    let dInt := discrIntOfNat ety.discrWidth ety.discrSigned d
    let tInt := tagIntOfNat tagW tagS d
    let tagIt := translateIntTy tagW tagS
    let payload := emptySizedTy tagW.byteSize tagW.byteSize
    .cons dInt payload [⟨0, tagIt, tInt⟩] (buildEnumVariants ety tagW tagS rest)

/-- Build MiniRust `DiscrBranches` for a scalar-tagged fieldless enum. -/
noncomputable def buildEnumBranches (ety : EnumTy) (tagW : IntWidth)
    (tagS : Bool) : List Nat → DiscrBranches
  | [] => .nil
  | d :: rest =>
    let dInt := discrIntOfNat ety.discrWidth ety.discrSigned d
    let tInt := tagIntOfNat tagW tagS d
    .cons tInt (tInt + 1) (.known dInt) (buildEnumBranches ety tagW tagS rest)

/-- Translate a fieldless `EnumTy` into a MiniRust `MrType.enum`. -/
noncomputable def translateEnumTy (ety : EnumTy) : MrType :=
  let discrIt := translateIntTy ety.discrWidth ety.discrSigned
  match ety.tagRepr with
  | .zeroSized =>
    let d0 := match Trusted.MirSemantics.getElem? ety.discriminants 0 with | some d => d | none => 0
    let dInt := discrIntOfNat ety.discrWidth ety.discrSigned d0
    .enum (.cons dInt unitTy [] .nil) (.known dInt) discrIt ⟨0⟩ ⟨1⟩
  | .scalar tagW tagS =>
    let tagIt := translateIntTy tagW tagS
    let variants := buildEnumVariants ety tagW tagS ety.discriminants
    let branches := buildEnumBranches ety tagW tagS ety.discriminants
    .enum variants (.branch 0 tagIt branches .invalid) discrIt
      ⟨tagW.byteSize⟩ ⟨tagW.byteSize⟩

/-- Translate an Anneal `MirTy` into a MiniRust `MrType`. Rust `char` lowers to
`MrType.int u32Ty` (`spec/lang/types.md`, `tooling/minimize`). -/
noncomputable def translateTy : MirTy → MrType
  | .bool => .bool
  | .int w s => .int (translateIntTy w s)
  | .unit => unitTy
  | .never => neverTy
  | .char => .int u32Ty
  | .ordering => orderingTy
  | .enum ety => translateEnumTy ety
  | .tuple [.int w s, .bool] => (translateIntTy w s).withOverflow
  | _ => unitTy

/-- Translate a well-formed Anneal `Val` into a MiniRust `MrValue`. -/
noncomputable def translateVal : Val → MrValue
  | .scalar sv => .int (decodeScalar sv)
  | .bool b => .bool b
  | .char c => .int (Int.ofNat c.toNat)
  | .ordering .less => .variant (Neg.neg 1) unitValue
  | .ordering .equal => .variant 0 unitValue
  | .ordering .greater => .variant 1 unitValue
  | .unit => unitValue
  | .enumVal ety v =>
    let d := match Trusted.MirSemantics.getElem? ety.discriminants v with | some d => d | none => 0
    let dInt := discrIntOfNat ety.discrWidth ety.discrSigned d
    .variant dInt unitValue
  | .tuple [.scalar sv, .bool b] =>
    .tuple (.cons (.int (decodeScalar sv)) (.cons (.bool b) .nil))
  | _ => unitValue

/-- Check whether `ty` is an inhabited 0-byte ZST in Profile v1 (`.unit` or
admitted `.zeroSized` 1-variant enum). -/
noncomputable def isInhabitedZstTy : MirTy → Bool
  | .unit => true
  | .enum ety => isZstEnumTy ety
  | _ => false

/-! ## Static Type Inference & Translation for Operands, Rvalues, Statements -/

/-- Infer the static `MirTy` of an `Operand` in `bodyLocals`. -/
noncomputable def operandTy? (bodyLocals : List MirTy) :
    Operand → Option MirTy
  | .copy place | .move place =>
    if place.projection.isEmpty then Trusted.MirSemantics.getElem? bodyLocals place.localId
    else none
  | .constant c => some c.ty

/-- Translate a `ConstOperand` into a MiniRust `ValueExpr`. Invalid scalar bit
patterns for `bool`, `Ordering`, and scalar-tagged enums translate via MiniRust
`CastOp.transmute` so both machines agree on invalid-value UB; `char` lowers
directly to `u32Ty` per upstream MiniRust (`0 <= bits < 2^32`). -/
noncomputable def translateConst (c : ConstOperand) : ValueExpr :=
  match c.ty, c.lit with
  | .int w s, .scalar bits =>
    .constant (.int (decodeScalar ⟨w, s, bits⟩)) (.int (translateIntTy w s))
  | .bool, .scalar bits =>
    let v := UInt8.ofNat (truncateBits .i8 bits).toNat
    if v == 0 then .constant (.bool false) .bool
    else if v == 1 then .constant (.bool true) .bool
    else .unOp (.cast (.transmute .bool))
      (.constant (.int (Int.ofNat (truncateBits .i8 bits).toNat)) (.int u8Ty))
  | .unit, .zeroSized => .tuple .nil unitTy
  | .char, .scalar bits =>
    .constant (.int (Int.ofNat (truncateBits .i32 bits).toNat)) (.int u32Ty)
  | .ordering, .scalar bits =>
    match orderingOfTagBits bits.toNat with
    | some .less =>
      .variant (Neg.neg 1) (.tuple .nil (emptySizedTy 1 1)) orderingTy
    | some .equal =>
      .variant 0 (.tuple .nil (emptySizedTy 1 1)) orderingTy
    | some .greater =>
      .variant 1 (.tuple .nil (emptySizedTy 1 1)) orderingTy
    | none =>
      .unOp (.cast (.transmute orderingTy))
        (.constant (.int (decodeScalar ⟨.i8, true, bits⟩)) (.int i8Ty))
  | .enum ety, .zeroSized =>
    let d0 :=
      match Trusted.MirSemantics.getElem? ety.discriminants 0 with
      | some d => d
      | none => 0
    let dInt := discrIntOfNat ety.discrWidth ety.discrSigned d0
    let payloadTy :=
      match ety.tagRepr with
      | .zeroSized => unitTy
      | .scalar tagW _ => emptySizedTy tagW.byteSize tagW.byteSize
    .variant dInt (.tuple .nil payloadTy) (translateEnumTy ety)
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => .tuple .nil unitTy
    | .scalar tagW tagS =>
      let discrBits := tagBitsToDiscrBits tagW tagS ety.discrWidth bits
      match findDiscrVariant? discrBits ety.discriminants with
      | some v =>
        let d :=
          match Trusted.MirSemantics.getElem? ety.discriminants v with
          | some d => d
          | none => 0
        let dInt := discrIntOfNat ety.discrWidth ety.discrSigned d
        let payloadTy := emptySizedTy tagW.byteSize tagW.byteSize
        .variant dInt (.tuple .nil payloadTy) (translateEnumTy ety)
      | none =>
        .unOp (.cast (.transmute (translateEnumTy ety)))
          (.constant (.int (decodeScalar ⟨tagW, tagS, bits⟩))
            (.int (translateIntTy tagW tagS)))
  | _, _ => .tuple .nil unitTy

/-- Translate a MIR `Operand` into a MiniRust `ValueExpr` (note: in authentic
MiniRust, both `Copy` and `Move` translate to `ValueExpr.load`). -/
noncomputable def translateOperand : Operand → ValueExpr
  | .copy place => .load (.local place.localId)
  | .move place => .load (.local place.localId)
  | .constant c => translateConst c

/-- Translate a MIR integer `BinOp` into a MiniRust `IntBinOp`. -/
noncomputable def translateIntBinOp? : BinOp → Option IntBinOp
  | .add => some .add
  | .addUnchecked => some .addUnchecked
  | .sub => some .sub
  | .subUnchecked => some .subUnchecked
  | .mul => some .mul
  | .mulUnchecked => some .mulUnchecked
  | .div => some .div
  | .rem => some .rem
  | .shl => some .shl
  | .shlUnchecked => some .shlUnchecked
  | .shr => some .shr
  | .shrUnchecked => some .shrUnchecked
  | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr
  | .bitXor => some .bitXor
  | _ => none

/-- Translate a MIR overflowing `BinOp` to a MiniRust `IntBinOpWithOverflow`. -/
noncomputable def translateWithOverflowOp? : BinOp → Option IntBinOpWithOverflow
  | .addWithOverflow => some .add
  | .subWithOverflow => some .sub
  | .mulWithOverflow => some .mul
  | _ => none

/-- Translate a MIR relational `BinOp` into a MiniRust `RelOp`. -/
noncomputable def translateRelOp? : BinOp → Option RelOp
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .lt
  | .le => some .le
  | .gt => some .gt
  | .ge => some .ge
  | .cmp => some .cmp
  | _ => none

/-- Translate a MIR `Rvalue` into a MiniRust `ValueExpr`. -/
noncomputable def translateRvalue (bodyLocals : List MirTy) :
    Rvalue → ValueExpr
  | .use opnd => translateOperand opnd
  | .unaryOp op opnd =>
    let e := translateOperand opnd
    match op, operandTy? bodyLocals opnd with
    | .not, some .bool => .binOp (.rel .eq) e (.constant (.bool false) .bool)
    | .not, some (.int _ _) => .unOp (.int .bitNot) e
    | .neg, some (.int _ true) => .unOp (.int .neg) e
    | _, _ => e
  | .binaryOp op lhs rhs =>
    let le := translateOperand lhs
    let re := translateOperand rhs
    match operandTy? bodyLocals lhs with
    | some (.int _ _) =>
      match translateIntBinOp? op with
      | some iop => .binOp (.int iop) le re
      | none =>
        match translateWithOverflowOp? op with
        | some wop => .binOp (.intWithOverflow wop) le re
        | none =>
          match translateRelOp? op with
          | some .cmp =>
            .unOp (.cast (.transmute orderingTy)) (.binOp (.rel .cmp) le re)
          | some rop => .binOp (.rel rop) le re
          | none => le
    | some .bool =>
      match op with
      | .bitAnd =>
        .unOp (.cast (.transmute .bool))
          (.binOp (.int .bitAnd)
            (.unOp (.cast (.transmute (.int u8Ty))) le)
            (.unOp (.cast (.transmute (.int u8Ty))) re))
      | .bitOr =>
        .unOp (.cast (.transmute .bool))
          (.binOp (.int .bitOr)
            (.unOp (.cast (.transmute (.int u8Ty))) le)
            (.unOp (.cast (.transmute (.int u8Ty))) re))
      | .bitXor =>
        .unOp (.cast (.transmute .bool))
          (.binOp (.int .bitXor)
            (.unOp (.cast (.transmute (.int u8Ty))) le)
            (.unOp (.cast (.transmute (.int u8Ty))) re))
      | _ =>
        match translateRelOp? op with
        | some rop => .binOp (.rel rop) le re
        | none => le
    | some .char =>
      match translateRelOp? op with
      | some .cmp =>
        .unOp (.cast (.transmute orderingTy)) (.binOp (.rel .cmp) le re)
      | some rop => .binOp (.rel rop) le re
      | none => le
    | _ => le
  | .cast .intToInt opnd castTy =>
    let e := translateOperand opnd
    let eInt :=
      match operandTy? bodyLocals opnd with
      | some .bool => .unOp (.cast (.transmute (.int u8Ty))) e
      | _ => e
    match castTy with
    | .int w s => .unOp (.cast (.intToInt (translateIntTy w s))) eInt
    | .char => .unOp (.cast (.intToInt u32Ty)) eInt
    | _ => eInt
  | .discriminant place => .getDiscriminant (.local place.localId)
  | _ => .tuple .nil unitTy

/-- Translate a MIR `StatementKind` into a MiniRust `MrStatement`.
`StatementKind.nop` translates to `MrStatement.placeMention (.local 0)`
(since `_0` is always live in admitted bodies), maintaining 1-to-1 statement
lockstep with authentic MiniRust syntax. -/
noncomputable def translateStmt (bodyLocals : List MirTy) :
    StatementKind → MrStatement
  | .assign dst rv => .assign (.local dst.localId) (translateRvalue bodyLocals rv)
  | .storageLive id => .storageLive id
  | .storageDead id => .storageDead id
  | .nop => .placeMention (.local 0)
  | .unsupported => .placeMention (.local 0)

/-- Translate `SwitchTargets` branch entries for integer discriminant `(w, s)`,
shifting target basic-block indices by `+ 1` past the `initBlock`. -/
noncomputable def translateIntSwitchBranches (w : IntWidth) (s : Bool) :
    List (BitVec 128 × BasicBlockId) → List (Int × BbName)
  | [] => []
  | (bits, target) :: rest =>
    (decodeScalar ⟨w, s, bits⟩, target + 1) ::
      translateIntSwitchBranches w s rest

/-- Translate `SwitchTargets` branch entries for `bool` or `char` discriminant,
shifting target basic-block indices by `+ 1` past the `initBlock`. -/
noncomputable def translateNatSwitchBranches :
    List (BitVec 128 × BasicBlockId) → List (Int × BbName)
  | [] => []
  | (bits, target) :: rest =>
    (Int.ofNat bits.toNat, target + 1) :: translateNatSwitchBranches rest

/-- Translate a MIR `TerminatorKind` into a MiniRust `MrTerminator`, shifting
target basic-block indices by `+ 1` past `initBlock` (block `0`). -/
noncomputable def translateTerm (bodyLocals : List MirTy) :
    TerminatorKind → MrTerminator
  | .goto target => .goto (target + 1)
  | .return_ => .return_
  | .unreachable => .unreachable
  | .switchInt discr targets =>
    let de := translateOperand discr
    match operandTy? bodyLocals discr with
    | some (.int w s) =>
      .switch de (translateIntSwitchBranches w s targets.branches)
        (targets.otherwise + 1)
    | some .bool =>
      .switch (.unOp (.cast (.transmute (.int u8Ty))) de)
        (translateNatSwitchBranches targets.branches)
        (targets.otherwise + 1)
    | some .char =>
      .switch de
        (translateNatSwitchBranches targets.branches)
        (targets.otherwise + 1)
    | _ => .unreachable
  | _ => .unreachable

/-- Translate a MIR `BasicBlock` into a MiniRust `MrBasicBlock`. -/
noncomputable def translateBlock (bodyLocals : List MirTy)
    (bb : BasicBlock) : MrBasicBlock :=
  { statements := bb.statements.map (translateStmt bodyLocals)
    terminator := translateTerm bodyLocals bb.terminator }

/-- Collect the indices `idx` with `argCount < idx < locals.length` that have
no `StorageLive`/`StorageDead` annotation in `body` (always-live temporaries
allocated by `initBlock`). -/
noncomputable def alwaysLiveTempsAux (body : Body) :
    Nat → List MirTy → List LocalName
  | _, [] => []
  | idx, _ :: rest =>
    let tail := alwaysLiveTempsAux body (idx + 1) rest
    if Nat.blt body.argumentCount idx && !hasStorageAnnotation body idx then
      idx :: tail
    else
      tail

/-- Indices of always-live non-argument temporaries in `body`. -/
noncomputable def alwaysLiveTemps (body : Body) : List LocalName :=
  alwaysLiveTempsAux body 0 body.locals

/-- Build `[start, start + 1, ..., start + count - 1]`. -/
def rangeNat : Nat → Nat → List Nat
  | _, 0 => []
  | start, n + 1 => start :: rangeNat (start + 1) n

/-- Translate a MIR `Body` into a MiniRust `MrFunction` whose entry block `0`
(`initBlock`) allocates always-live temporaries and jumps to block `1` (the
translated MIR `bb0`). -/
noncomputable def translateBody (body : Body) : MrFunction :=
  let initBlock : MrBasicBlock := {
    statements := (alwaysLiveTemps body).map MrStatement.storageLive
    terminator := .goto 1
  }
  { locals := body.locals.map translateTy
    args := rangeNat 1 body.argumentCount
    ret := 0
    blocks := initBlock :: body.basicBlocks.map (translateBlock body.locals)
    start := 0 }

/-- Synthesized `0`-arg, `1`-ZST (`unitTy` at `ret := 1`) MiniRust `start`
wrapper function satisfying structural `start` well-formedness
(`spec/lang/well-formed.md`). `start` is not stepped from block `0`
(`Machine::new`); instead, `initMrMachine` directly constructs the post-`Call`
two-frame state with local `0` (`retTy`) live, and `MrTerminator.exitWith 0`
observes that slot on halt. -/
noncomputable def harnessCallerFunc (retTy : MrType) : MrFunction :=
  { locals := [retTy, unitTy]
    args := []
    ret := 1
    blocks := [{ statements := [], terminator := .exitWith 0 }]
    start := 0 }

/-- Translate an Anneal `Program` into a MiniRust `MrProgram` whose `start`
index names the structurally well-formed `0`-arg, `1`-ZST `harnessCallerFunc`
appended to `functions` (`spec/lang/well-formed.md`). -/
noncomputable def translateProg (p : Program) : MrProgram :=
  let retMrTy :=
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | some body =>
      match Trusted.MirSemantics.getElem? body.locals 0 with
      | some ty => translateTy ty
      | none => unitTy
    | none => unitTy
  { functions := p.bodies.map translateBody ++ [harnessCallerFunc retMrTy]
    start := p.bodies.length }

/-! ## MiniRust Machine Initialization -/

/-- Extract the human-readable reason string from `EvalError`. -/
def evalErrorMsg : EvalError → String
  | .ub msg => msg
  | .illFormed msg => msg

/-- Allocate and store argument locals `_1 .. _argCount` during frame entry. -/
noncomputable def initMrArgsLoop (frame : StackFrame) (mem : MrMemory) :
    Nat → List Val → Except String (StackFrame × MrMemory)
  | _, [] => .ok (frame, mem)
  | idx, v :: vs =>
    match storageLiveFrame frame mem idx with
    | .error err => .error (evalErrorMsg err)
    | .ok (frame1, mem1) =>
      match listGet? frame1.func.locals idx, localMapGet? idx frame1.locals with
      | some ty, some ptr =>
        match typedStore mem1 ptr (translateVal v) ty ty.align with
        | .error err => .error (evalErrorMsg err)
        | .ok mem2 => initMrArgsLoop frame1 mem2 (idx + 1) vs
      | _, _ => .error "initMrArgsLoop missing argument local"

/-- Construct the synthesized post-`Call` two-frame MiniRust state for `(p, q)`
(`start` is not stepped from block `0` / `Machine::new`; `checkArgsMatch` in
`MiniRustAdmitted` discharges `Call` ABI checks): a harness caller frame
holding a live return-value slot (`_0`) and a callee frame positioned at
`initBlock` (block `0`, stmt `0`) with `_0` and `_1.._argCount` live. -/
noncomputable def initMrMachine (p : Program) (q : Query) :
    Except String Machine :=
  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then
    .error "unsupported target pointer width or profile version"
  else if !q.callerMem.allocations.isEmpty then
    .error "unsupported non-empty caller memory"
  else
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => .error "missing entry body"
    | some body =>
      match Trusted.MirSemantics.getElem? body.locals 0 with
      | none => .error "missing return local"
      | some retMirTy =>
        let mrProg := translateProg p
        let calleeFunc := translateBody body
        let retMrTy := translateTy retMirTy
        let callerFunc := harnessCallerFunc retMrTy
        match MrMemory.empty.allocate retMrTy.size retMrTy.align with
        | .error msg => .error msg
        | .ok (mem1, callerRetPtr) =>
          let callerFrame : StackFrame := {
            func := callerFunc
            locals := [(0, callerRetPtr)]
            stackPopAction := .bottomOfStack
            nextBlock := 0
            nextStmt := 0
          }
          let calleeFrame0 : StackFrame := {
            func := calleeFunc
            locals := []
            stackPopAction := .backToCaller callerRetPtr (some 0)
            nextBlock := 0
            nextStmt := 0
          }
          match storageLiveFrame calleeFrame0 mem1 0 with
          | .error err => .error (evalErrorMsg err)
          | .ok (calleeFrame1, mem2) =>
            match initMrArgsLoop calleeFrame1 mem2 1 q.args with
            | .error msg => .error msg
            | .ok (calleeFrame2, mem3) =>
              .ok {
                prog := mrProg
                mem := mem3
                stack := [calleeFrame2, callerFrame]
              }

/-! ## Static Admission (`MiniRustAdmitted` vs `MiniRustExactAdmitted`) -/

/-- Exact-fragment local/constant type support: matches
`isSupportedScalarOrUnitTy` except `MirTy.char` is excluded (since upstream
MiniRust lowers `char` to niche-free `u32`). -/
noncomputable def isExactSupportedTy : MirTy → Bool
  | .char => false
  | ty => isSupportedScalarOrUnitTy ty

/-- Check that `c : ConstOperand` is admitted (will not produce
`FaultKind.unsupported` in `evalConstLit`; invalid `bool`/`Ordering`/enum tags
are admitted in both fragments, while `char` constants are admitted when
`exact = false` and excluded when `exact = true`). -/
noncomputable def constAdmitted (exact : Bool) (c : ConstOperand) : Bool :=
  match c.ty, c.lit with
  | .int w _, .scalar bits => truncateBits w bits == bits
  | .bool, .scalar bits => truncateBits .i8 bits == bits
  | .unit, .zeroSized => true
  | .char, .scalar bits => !exact && (truncateBits .i32 bits == bits)
  | .ordering, .scalar bits => truncateBits .i8 bits == bits
  | .enum ety, .zeroSized => isZstEnumTy ety
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => false
    | .scalar tagW _ => enumAdmitted ety && (truncateBits tagW bits == bits)
  | _, _ => false

/-- Check that `opnd` is admitted in `bodyLocals`. When `exact = true`,
`Operand.move` is restricted to inhabited ZST locals (where Anneal's
conservative move-deinitialization is a no-op, matching MiniRust's `Load`). -/
noncomputable def operandAdmitted (exact : Bool) (bodyLocals : List MirTy) :
    Operand → Bool
  | .copy place =>
    place.projection.isEmpty &&
      (Trusted.MirSemantics.getElem? bodyLocals place.localId).isSome
  | .move place =>
    if !place.projection.isEmpty then false
    else
      match Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => false
      | some ty => if exact then isInhabitedZstTy ty else true
  | .constant c => constAdmitted exact c

/-- Static result type of an admitted `BinOp` on operands `(lTy, rTy)`. -/
noncomputable def binOpResultTy? (op : BinOp) (lTy rTy : MirTy) : Option MirTy :=
  match lTy, rTy with
  | .int w s, .int _ _ =>
    if op.isShift then
      some (.int w s)
    else if !MirTy.beq lTy rTy then
      none
    else
      match op with
      | .eq | .ne | .lt | .le | .gt | .ge => some .bool
      | .cmp => some .ordering
      | .addWithOverflow | .subWithOverflow | .mulWithOverflow =>
        some (.tuple [.int w s, .bool])
      | .add | .sub | .mul | .div | .rem
      | .addUnchecked | .subUnchecked | .mulUnchecked
      | .bitAnd | .bitOr | .bitXor => some (.int w s)
      | _ => none
  | .bool, .bool =>
    match op with
    | .eq | .ne | .lt | .le | .gt | .ge
    | .bitAnd | .bitOr | .bitXor => some .bool
    | _ => none
  | .char, .char =>
    match op with
    | .eq | .ne | .lt | .le | .gt | .ge => some .bool
    | .cmp => some .ordering
    | _ => none
  | _, _ => none

/-- Check that `rv : Rvalue` is statically admitted and produces `dstTy`. -/
noncomputable def rvalueAdmitted (exact : Bool) (bodyLocals : List MirTy)
    (dstTy : MirTy) : Rvalue → Bool
  | .use opnd =>
    operandAdmitted exact bodyLocals opnd &&
      match operandTy? bodyLocals opnd with
      | some srcTy => MirTy.beq srcTy dstTy
      | none => false
  | .unaryOp op opnd =>
    operandAdmitted exact bodyLocals opnd &&
      match op, operandTy? bodyLocals opnd with
      | .not, some .bool => MirTy.beq dstTy .bool
      | .not, some (.int w s) => MirTy.beq dstTy (.int w s)
      | .neg, some (.int w true) => MirTy.beq dstTy (.int w true)
      | _, _ => false
  | .binaryOp op lhs rhs =>
    operandAdmitted exact bodyLocals lhs &&
      operandAdmitted exact bodyLocals rhs &&
      match operandTy? bodyLocals lhs, operandTy? bodyLocals rhs with
      | some lTy, some rTy =>
        match binOpResultTy? op lTy rTy with
        | some resTy => MirTy.beq resTy dstTy
        | none => false
      | _, _ => false
  | .cast .intToInt opnd castTy =>
    operandAdmitted exact bodyLocals opnd &&
      MirTy.beq castTy dstTy &&
      match operandTy? bodyLocals opnd, castTy with
      | some srcTy, .int _ _ => isIntLikeTy srcTy
      | some (.int .i8 false), .char => !exact
      | _, _ => false
  | .discriminant place =>
    place.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | some (.enum ety) =>
        enumAdmitted ety &&
          MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
      | some .ordering => MirTy.beq dstTy (.int .i8 true)
      | _ => false
  | _ => false

/-- Check that `stmt : StatementKind` is statically admitted in `bodyLocals`.
Per `spec/lang/well-formed.md`, `Statement::StorageDead` may never target the
return local `_0` or argument locals `_1 .. _argCount` (`argCount < id`). -/
noncomputable def stmtAdmitted (exact : Bool) (argCount : Nat)
    (bodyLocals : List MirTy) : StatementKind → Bool
  | .nop => true
  | .storageLive id => Nat.blt id bodyLocals.length
  | .storageDead id => Nat.blt argCount id && Nat.blt id bodyLocals.length
  | .assign dst rv =>
    dst.projection.isEmpty &&
      match Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => false
      | some dstTy => rvalueAdmitted exact bodyLocals dstTy rv
  | .unsupported => false

/-- Check that all branch targets in `branches` are in-bounds basic blocks and
all case keys are well-formed for `discrTy`. -/
noncomputable def switchBranchesAdmitted (numBlocks : Nat) (discrTy : MirTy) :
    List (BitVec 128 × BasicBlockId) → Bool
  | [] => true
  | (bits, target) :: rest =>
    Nat.blt target numBlocks &&
      (match discrTy with
      | .int w _ => truncateBits w bits == bits
      | .bool =>
        truncateBits .i8 bits == bits &&
          (Nat.beq bits.toNat 0 || Nat.beq bits.toNat 1)
      | .char =>
        truncateBits .i32 bits == bits && isUnicodeScalar bits.toNat
      | _ => false) &&
      switchBranchesAdmitted numBlocks discrTy rest

/-- Check that all `Switch` case keys are pairwise distinct, matching upstream
MiniRust `cases: Map<Int, BbName>` (`spec/lang/syntax.md`). -/
def switchCasesUnique : List (Int × BbName) → Bool
  | [] => true
  | (k, _) :: rest => !rest.any (fun p => p.1 == k) && switchCasesUnique rest

/-- Translate `SwitchInt` branch keys according to `discrTy`. -/
noncomputable def translateSwitchCasesForTy (dTy : MirTy)
    (branches : List (BitVec 128 × BasicBlockId)) : List (Int × BbName) :=
  match dTy with
  | .int w s => translateIntSwitchBranches w s branches
  | _ => translateNatSwitchBranches branches

/-- Check that `bb : BasicBlock` is statically admitted. -/
noncomputable def blockAdmitted (exact : Bool) (argCount : Nat)
    (bodyLocals : List MirTy) (numBlocks : Nat) (bb : BasicBlock) : Bool :=
  !bb.cleanup &&
    bb.statements.all (stmtAdmitted exact argCount bodyLocals) &&
    match bb.terminator with
    | .goto target => Nat.blt target numBlocks
    | .return_ => true
    | .unreachable => true
    | .switchInt discr targets =>
      operandAdmitted exact bodyLocals discr &&
        Nat.blt targets.otherwise numBlocks &&
        match operandTy? bodyLocals discr with
        | some dTy =>
          (match dTy with
          | .int _ _ | .bool => true
          | .char => !exact
          | _ => false) &&
            switchBranchesAdmitted numBlocks dTy targets.branches &&
            switchCasesUnique (translateSwitchCasesForTy dTy targets.branches)
        | none => false
    | _ => false

/-- Core static admission predicate on a `Body` (parameterized by `exact`). -/
noncomputable def bodyAdmittedWith (exact : Bool) (body : Body) : Bool :=
  !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    discriminantTypesValid body &&
    castTypesValid body &&
    body.locals.all
      (match exact with
      | true => isExactSupportedTy
      | false => isSupportedScalarOrUnitTy) &&
    body.basicBlocks.all
      (blockAdmitted exact body.argumentCount body.locals
        body.basicBlocks.length)

/-- Forward-simulation body admission predicate (allows `Operand.move` on
arbitrary admitted locals and `MirTy.char` lowered to `u32`). -/
noncomputable def MiniRustBodyAdmitted (body : Body) : Bool :=
  bodyAdmittedWith false body

/-- Exact bidirectional fault-equivalence body admission predicate (restricts
`Operand.move` to inhabited ZST locals and excludes `MirTy.char` so Anneal and
MiniRust agree identically on normal outcomes, UB, and divergence). -/
noncomputable def MiniRustExactBodyAdmitted (body : Body) : Bool :=
  bodyAdmittedWith true body

/-- Static program-level forward-simulation admission predicate. -/
noncomputable def MiniRustProgAdmitted (p : Program) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => false
    | some body => MiniRustBodyAdmitted body

/-- Static program-level exact admission predicate (bidirectional fault
equivalence). -/
noncomputable def MiniRustExactProgAdmitted (p : Program) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => false
    | some body => MiniRustExactBodyAdmitted body

/-- Full `(Program, Query)` admission predicate for forward simulation
(`MiniRustForwardSimClaim`). -/
def MiniRustAdmitted (p : Program) (q : Query) : Prop :=
  MiniRustProgAdmitted p = true ∧
    q.callerMem.allocations.isEmpty = true ∧
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => False
    | some body =>
      checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount) = true

/-- Full `(Program, Query)` admission predicate for bidirectional fault
equivalence (`MiniRustBiFaultEquivClaim`). -/
def MiniRustExactAdmitted (p : Program) (q : Query) : Prop :=
  MiniRustExactProgAdmitted p = true ∧
    q.callerMem.allocations.isEmpty = true ∧
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => False
    | some body =>
      checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount) = true

theorem isSupportedScalarOrUnitTy_of_exact (ty : MirTy)
    (h : isExactSupportedTy ty = true) :
    isSupportedScalarOrUnitTy ty = true := by
  cases ty <;> first | exact h | cases h

theorem constAdmitted_of_exact (c : ConstOperand)
    (h : constAdmitted true c = true) :
    constAdmitted false c = true := by
  cases c with
  | mk ty lit =>
    cases ty with
    | char =>
      cases lit <;> cases h
    | bool | int _ _ | unit | never | ordering | enum _ | ref _ _
    | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _
    | option _ | tuple _ | vec _ | box _ | unsupported =>
      cases lit <;> exact h

/-- Every exact-admitted operand is forward-admitted. -/
theorem operandAdmitted_of_exact (bodyLocals : List MirTy) (opnd : Operand)
    (h : operandAdmitted true bodyLocals opnd = true) :
    operandAdmitted false bodyLocals opnd = true := by
  cases opnd with
  | copy _ => exact h
  | constant c => exact constAdmitted_of_exact c h
  | move place =>
    dsimp only [operandAdmitted] at h; dsimp only [operandAdmitted]
    cases hp : place.projection.isEmpty with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp] at h
      cases hg : Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [hg] at h; cases h
      | some _ => rfl

/-- Every exact-admitted rvalue is forward-admitted. -/
theorem rvalueAdmitted_of_exact (bodyLocals : List MirTy) (dstTy : MirTy)
    (rv : Rvalue) (h : rvalueAdmitted true bodyLocals dstTy rv = true) :
    rvalueAdmitted false bodyLocals dstTy rv = true := by
  cases rv with
  | use opnd =>
    dsimp only [rvalueAdmitted] at h; dsimp only [rvalueAdmitted]
    cases ho : operandAdmitted true bodyLocals opnd with
    | false => rw [ho] at h; cases h
    | true =>
      rw [ho] at h
      rw [operandAdmitted_of_exact bodyLocals opnd ho]
      exact h
  | unaryOp op opnd =>
    dsimp only [rvalueAdmitted] at h; dsimp only [rvalueAdmitted]
    cases ho : operandAdmitted true bodyLocals opnd with
    | false => rw [ho] at h; cases h
    | true =>
      rw [ho] at h
      rw [operandAdmitted_of_exact bodyLocals opnd ho]
      exact h
  | binaryOp op lhs rhs =>
    dsimp only [rvalueAdmitted] at h; dsimp only [rvalueAdmitted]
    cases hl : operandAdmitted true bodyLocals lhs with
    | false => rw [hl] at h; cases h
    | true =>
      cases hr : operandAdmitted true bodyLocals rhs with
      | false => rw [hl, hr] at h; cases h
      | true =>
        rw [hl, hr] at h
        rw [operandAdmitted_of_exact bodyLocals lhs hl,
          operandAdmitted_of_exact bodyLocals rhs hr]
        exact h
  | cast kind opnd castTy =>
    cases kind with
    | ptrToPtr | intToPtr | unsize | boxAsRef | unsupported => cases h
    | intToInt =>
      dsimp only [rvalueAdmitted] at h; dsimp only [rvalueAdmitted]
      cases ho : operandAdmitted true bodyLocals opnd with
      | false => rw [ho] at h; cases h
      | true =>
        cases hm : MirTy.beq castTy dstTy with
        | false => rw [ho, hm] at h; cases h
        | true =>
          rw [ho, hm] at h
          rw [operandAdmitted_of_exact bodyLocals opnd ho]
          cases hop : operandTy? bodyLocals opnd with
          | none => rw [hop] at h; cases h
          | some srcTy =>
            rw [hop] at h
            cases castTy with
            | int _ _ => exact h
            | char => cases srcTy with
              | int w s => cases w <;> cases s <;> cases h
              | _ => cases h
            | _ => cases srcTy <;> cases h
  | discriminant _ => exact h
  | useRetag _ | ref _ _ | addressOf _ _ | fakeAddressOf _
  | aggregateTuple _ | aggregateArray _ _ | repeat_ _ _ _
  | aggregateRange _ _ _ | aggregateRangeTo _ _ | aggregateRangeFrom _ _
  | aggregateOption _ _ _ | unsupported =>
    cases h

/-- Every exact-admitted statement is forward-admitted. -/
theorem stmtAdmitted_of_exact (argCount : Nat) (bodyLocals : List MirTy)
    (stmt : StatementKind)
    (h : stmtAdmitted true argCount bodyLocals stmt = true) :
    stmtAdmitted false argCount bodyLocals stmt = true := by
  cases stmt with
  | nop => exact h
  | storageLive _ => exact h
  | storageDead _ => exact h
  | unsupported => cases h
  | assign dst rv =>
    dsimp only [stmtAdmitted] at h; dsimp only [stmtAdmitted]
    cases hp : dst.projection.isEmpty with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp] at h
      cases hg : Trusted.MirSemantics.getElem? bodyLocals dst.localId with
      | none => rw [hg] at h; cases h
      | some dstTy =>
        rw [hg] at h
        exact rvalueAdmitted_of_exact bodyLocals dstTy rv h

theorem list_all_imp {α : Type} (p q : α → Bool) (xs : List α)
    (himp : ∀ x, p x = true → q x = true) (hall : xs.all p = true) :
    xs.all q = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.all] at hall; dsimp only [List.all]
    cases hp : p x with
    | false => rw [hp] at hall; cases hall
    | true =>
      rw [hp] at hall
      rw [himp x hp]
      exact ih hall

/-- Every exact-admitted basic block is forward-admitted. -/
theorem blockAdmitted_of_exact (argCount : Nat) (bodyLocals : List MirTy)
    (numBlocks : Nat) (bb : BasicBlock)
    (h : blockAdmitted true argCount bodyLocals numBlocks bb = true) :
    blockAdmitted false argCount bodyLocals numBlocks bb = true := by
  dsimp only [blockAdmitted] at h; dsimp only [blockAdmitted]
  cases hc : bb.cleanup with
  | true => rw [hc] at h; cases h
  | false =>
    rw [hc] at h
    cases hs : bb.statements.all (stmtAdmitted true argCount bodyLocals) with
    | false => rw [hs] at h; cases h
    | true =>
      rw [hs] at h
      have hs' : bb.statements.all (stmtAdmitted false argCount bodyLocals) = true :=
        list_all_imp _ _ bb.statements
          (stmtAdmitted_of_exact argCount bodyLocals) hs
      rw [hs']
      cases ht : bb.terminator with
      | goto _ => rw [ht] at h; exact h
      | return_ => rfl
      | unreachable => rfl
      | switchInt discr targets =>
        rw [ht] at h
        dsimp only at h; dsimp only
        cases ho : operandAdmitted true bodyLocals discr with
        | false => rw [ho] at h; cases h
        | true =>
          cases hoth : Nat.blt targets.otherwise numBlocks with
          | false => rw [ho, hoth] at h; cases h
          | true =>
            rw [ho, hoth] at h
            rw [operandAdmitted_of_exact bodyLocals discr ho]
            cases hop : operandTy? bodyLocals discr with
            | none => rw [hop] at h; cases h
            | some dTy =>
              rw [hop] at h
              cases dTy <;> first | exact h | cases h
      | unwindResume => rw [ht] at h; cases h
      | assert _ _ _ _ _ => rw [ht] at h; cases h
      | call _ _ _ _ _ => rw [ht] at h; cases h
      | coreCall _ _ _ _ _ => rw [ht] at h; cases h
      | sysrootCall _ _ _ _ _ => rw [ht] at h; cases h
      | unsupported => rw [ht] at h; cases h

/-- `MiniRustExactAdmitted` implies `MiniRustAdmitted`. -/
theorem miniRustAdmitted_of_exact {p : Program} {q : Query}
    (h : MiniRustExactAdmitted p q) : MiniRustAdmitted p q := by
  cases h with
  | intro hprog hrest =>
    cases hrest with
    | intro hmem hargs =>
      refine ⟨?_, hmem, hargs⟩
      dsimp only [MiniRustProgAdmitted, MiniRustExactProgAdmitted] at hprog
      dsimp only [MiniRustProgAdmitted, MiniRustExactProgAdmitted]
      cases hw : Nat.beq p.pointerWidthBits 64 with
      | false => rw [hw] at hprog; cases hprog
      | true =>
        cases hv : Nat.beq p.mirProfileVersion 1 with
        | false => rw [hw, hv] at hprog; cases hprog
        | true =>
          rw [hw, hv] at hprog
          cases hb : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
          | none => rw [hb] at hprog; cases hprog
          | some body =>
            rw [hb] at hprog
            dsimp only [MiniRustBodyAdmitted, MiniRustExactBodyAdmitted,
              bodyAdmittedWith] at hprog
            dsimp only [MiniRustBodyAdmitted, MiniRustExactBodyAdmitted,
              bodyAdmittedWith]
            cases h1 : !body.basicBlocks.isEmpty with
            | false => rw [h1] at hprog; cases hprog
            | true =>
              cases h2 : Nat.blt body.argumentCount body.locals.length with
              | false => rw [h1, h2] at hprog; cases hprog
              | true =>
                cases h3 : storageAnnotationsInBounds body with
                | false => rw [h1, h2, h3] at hprog; cases hprog
                | true =>
                  cases h4 : discriminantTypesValid body with
                  | false => rw [h1, h2, h3, h4] at hprog; cases hprog
                  | true =>
                    cases h5 : castTypesValid body with
                    | false => rw [h1, h2, h3, h4, h5] at hprog; cases hprog
                    | true =>
                      cases h6 : body.locals.all isExactSupportedTy with
                      | false => rw [h1, h2, h3, h4, h5, h6] at hprog; cases hprog
                      | true =>
                        rw [h1, h2, h3, h4, h5, h6] at hprog
                        have h6' : body.locals.all isSupportedScalarOrUnitTy = true :=
                          list_all_imp _ _ body.locals
                            isSupportedScalarOrUnitTy_of_exact h6
                        rw [h6']
                        exact list_all_imp _ _ body.basicBlocks
                          (blockAdmitted_of_exact body.argumentCount
                            body.locals body.basicBlocks.length)
                          hprog

/-! ## Upstream Structural Well-Formedness (`spec/lang/well-formed.md`) -/

/-- Structural well-formedness of a `PlaceExpr` (`spec/lang/well-formed.md`). -/
def mrPlaceWellFormed (numLocals : Nat) : PlaceExpr → Bool
  | .local id => Nat.blt id numLocals
  | .field root _ => mrPlaceWellFormed numLocals root
  | .index root _ => mrPlaceWellFormed numLocals root
  | .downcast root _ => mrPlaceWellFormed numLocals root

/-- Static type of a self-typed `ValueExpr` when syntactically determined
without local context. -/
def mrSelfTypedExprTy? : ValueExpr → Option MrType
  | .constant _ ty => some ty
  | .tuple _ ty => some ty
  | .variant _ _ ty => some ty
  | .unOp (.cast (.transmute ty)) _ => some ty
  | .unOp (.cast (.intToInt it)) _ => some (.int it)
  | _ => none

mutual
  /-- Structural `ValueExpr::Variant` well-formedness inside `PlaceExpr`
  subexpressions (`spec/lang/well-formed.md`). -/
  def mrPlaceExprVariantWF : PlaceExpr → Bool
    | .local _ => true
    | .field root _ => mrPlaceExprVariantWF root
    | .index root idx => mrPlaceExprVariantWF root && mrValueExprVariantWF idx
    | .downcast root _ => mrPlaceExprVariantWF root

  /-- Structural `ValueExpr::Variant` well-formedness
  (`spec/lang/well-formed.md`), checking that every `.variant` subexpression
  targets an `MrType.enum` whose variant table contains `discriminant` and whose
  self-typed payload expression matches `varTy`. -/
  def mrValueExprVariantWF : ValueExpr → Bool
    | .constant _ _ => true
    | .tuple exprs _ => mrValueExprListVariantWF exprs
    | .variant discr data enumTy =>
      mrValueExprVariantWF data &&
        match enumTy with
        | .enum variants _ _ _ _ =>
          match variants.find? discr with
          | none => false
          | some (varTy, _) =>
            match mrSelfTypedExprTy? data with
            | some dataTy => MrType.beq dataTy varTy
            | none => true
        | _ => false
    | .getDiscriminant pl => mrPlaceExprVariantWF pl
    | .load pl => mrPlaceExprVariantWF pl
    | .unOp _ opnd => mrValueExprVariantWF opnd
    | .binOp _ lhs rhs =>
      mrValueExprVariantWF lhs && mrValueExprVariantWF rhs

  /-- Structural `ValueExpr::Variant` well-formedness across `ValueExprList`. -/
  def mrValueExprListVariantWF : ValueExprList → Bool
    | .nil => true
    | .cons hd tl =>
      mrValueExprVariantWF hd && mrValueExprListVariantWF tl
end

/-- Structural subset of `Statement::check_wf` (`spec/lang/well-formed.md`),
checking in-bounds local indices, `ValueExpr::Variant` payload/discriminant
well-formedness, and prohibiting `StorageDead` on `func.ret` or any argument in
`func.args` (remaining operand/assignment typing and non-overlapping `Assign`
rules are enforced by `MiniRustAdmitted` and `MirSemantics`). -/
def mrStmtWellFormed (fn : MrFunction) : MrStatement → Bool
  | .assign dst expr =>
    mrPlaceWellFormed fn.locals.length dst && mrValueExprVariantWF expr
  | .placeMention pl => mrPlaceWellFormed fn.locals.length pl
  | .setDiscriminant dst _ => mrPlaceWellFormed fn.locals.length dst
  | .deinit pl => mrPlaceWellFormed fn.locals.length pl
  | .storageLive id => Nat.blt id fn.locals.length
  | .storageDead id =>
    Nat.blt id fn.locals.length &&
      !Nat.beq id fn.ret &&
      !fn.args.any (Nat.beq id)

/-- Structural subset of `Terminator::check_wf` (`spec/lang/well-formed.md`),
checking `ValueExpr::Variant` well-formedness, in-bounds jump targets, and
unique `Switch` case keys (`cases: Map<Int, BbName>`). `allowExitWith` permits
the harness observation hook `exitWith` only inside `prog.start`, never inside
translated user MIR bodies. -/
def mrTermWellFormed (allowExitWith : Bool) (fn : MrFunction) :
    MrTerminator → Bool
  | .goto target => Nat.blt target fn.blocks.length
  | .switch expr cases fallback =>
    mrValueExprVariantWF expr &&
      Nat.blt fallback fn.blocks.length &&
      cases.all (fun p => Nat.blt p.2 fn.blocks.length) &&
      switchCasesUnique cases
  | .unreachable => true
  | .return_ => true
  | .exitWith retLocal => allowExitWith && Nat.blt retLocal fn.locals.length

/-- Structural subset of `Function::check_wf` (`spec/lang/well-formed.md`),
checking non-empty blocks, in-bounds `start`/`ret`/`args`, distinctness of
`args` from `ret`, and structural statement/terminator well-formedness. -/
def mrFuncWellFormed (allowExitWith : Bool) (fn : MrFunction) : Bool :=
  !fn.blocks.isEmpty &&
    Nat.blt fn.start fn.blocks.length &&
    Nat.blt fn.ret fn.locals.length &&
    fn.args.all (fun a => !Nat.beq a fn.ret && Nat.blt a fn.locals.length) &&
    fn.blocks.all (fun bb =>
      bb.statements.all (mrStmtWellFormed fn) &&
        mrTermWellFormed allowExitWith fn bb.terminator)

/-- Structural subset of `Program::check_wf` (`spec/lang/well-formed.md`) for
`prog.start` and the translated entry function at `entryFnIdx` (uncalled
non-entry bodies in `prog.functions` are not stepped; operand/assignment typing
and non-overlapping `Assign` rules are enforced by `MiniRustAdmitted` and
`MirSemantics`), checking that:
1. `prog.start` exists in `prog.functions`, takes `0` arguments, returns a
   `1`-ZST (`Size = 0, Align = 1`), and passes `mrFuncWellFormed true`; and
2. the translated user entry function at `entryFnIdx` exists in
   `prog.functions` and passes `mrFuncWellFormed false` (pure upstream
   terminators only). -/
def mrProgWellFormed (prog : MrProgram) (entryFnIdx : FnName) : Bool :=
  match listGet? prog.functions prog.start,
      listGet? prog.functions entryFnIdx with
  | some startFn, some entryFn =>
    startFn.args.isEmpty &&
      (match listGet? startFn.locals startFn.ret with
      | some rty => Nat.beq rty.size.bytes 0 && Nat.beq rty.align.bytes 1
      | none => false) &&
      mrFuncWellFormed true startFn &&
      mrFuncWellFormed false entryFn
  | _, _ => false

theorem list_length_map_tr {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    dsimp only [List.map, List.length]
    rw [ih]

theorem getElem_to_listGet? {α : Type} (xs : List α) (i : Nat) :
    Trusted.MirSemantics.getElem? xs i = listGet? xs i := by
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

theorem listGet?_map_tr {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    listGet? (xs.map f) i = (listGet? xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

theorem nat_lt_of_blt_tr {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem nat_blt_of_lt_tr {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

theorem rangeNat_all_bounds (start count limit : Nat)
    (hpos : 0 < start) (hle : start + count ≤ limit) :
    (rangeNat start count).all
      (fun a => !Nat.beq a 0 && Nat.blt a limit) = true := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp only [rangeNat, List.all]
    have hne0 : Nat.beq start 0 = false := by
      cases start with
      | zero => cases hpos
      | succ _ => rfl
    have hltLim : start < limit :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ k)) hle
    have hblt : Nat.blt start limit = true := nat_blt_of_lt_tr hltLim
    rw [hne0, hblt]
    have hle' : (start + 1) + k ≤ limit := by
      have heq : (start + 1) + k = start + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [heq]
      exact hle
    exact ih (start + 1) (Nat.zero_lt_succ start) hle'

theorem rangeNat_any_eq_false (start count id : Nat)
    (hub : start + count ≤ id) :
    (rangeNat start count).any (Nat.beq id) = false := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp only [rangeNat, List.any]
    have hlt : start < id :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ k)) hub
    have hbeq : Nat.beq id start = false := by
      cases hb : Nat.beq id start with
      | false => rfl
      | true =>
        have heq := Nat.eq_of_beq_eq_true hb
        subst heq
        exact False.elim (Nat.lt_irrefl id hlt)
    rw [hbeq, Bool.false_or]
    have hub' : (start + 1) + k ≤ id := by
      have heq : (start + 1) + k = start + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [heq]
      exact hub
    exact ih (start + 1) hub'

theorem alwaysLiveTempsAux_wf (body : Body) (fn : MrFunction)
    (hlen : fn.locals.length = body.locals.length) :
    ∀ (idx : Nat) (rem : List MirTy),
      idx + rem.length = body.locals.length →
      ((alwaysLiveTempsAux body idx rem).map MrStatement.storageLive).all
        (mrStmtWellFormed fn) = true := by
  intro idx rem
  induction rem generalizing idx with
  | nil => intro _; rfl
  | cons _ rest ih =>
    intro hsum
    dsimp only [alwaysLiveTempsAux]
    have hsum' : (idx + 1) + rest.length = body.locals.length := by
      dsimp only [List.length] at hsum
      rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
      exact hsum
    have htail := ih (idx + 1) hsum'
    cases Nat.blt body.argumentCount idx && !hasStorageAnnotation body idx with
    | false => exact htail
    | true =>
      have hif : (if true = true then idx :: alwaysLiveTempsAux body (idx + 1) rest
          else alwaysLiveTempsAux body (idx + 1) rest) =
          idx :: alwaysLiveTempsAux body (idx + 1) rest := rfl
      rw [hif]
      dsimp only [List.map, List.all, mrStmtWellFormed]
      have hlt : idx < fn.locals.length := by
        rw [hlen, ← hsum]
        dsimp only [List.length]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ rest.length)
      rw [nat_blt_of_lt_tr hlt, Bool.true_and]
      exact htail

theorem switchBranches_targets_wf (numBlocks fnBlocks : Nat)
    (hblocks : fnBlocks = 1 + numBlocks) (dTy : MirTy)
    (branches : List (BitVec 128 × BasicBlockId))
    (hadm : switchBranchesAdmitted numBlocks dTy branches = true) :
    (translateSwitchCasesForTy dTy branches).all
      (fun p => Nat.blt p.2 fnBlocks) = true := by
  induction branches with
  | nil =>
    cases dTy <;> rfl
  | cons hd rest ih =>
    cases hd with
    | mk bits target =>
      dsimp only [switchBranchesAdmitted] at hadm
      cases ht : Nat.blt target numBlocks with
      | false => rw [ht] at hadm; cases hadm
      | true =>
        rw [ht] at hadm
        cases hkey : (match dTy with
          | .int w _ => truncateBits w bits == bits
          | .bool =>
            truncateBits .i8 bits == bits &&
              (Nat.beq bits.toNat 0 || Nat.beq bits.toNat 1)
          | .char =>
            truncateBits .i32 bits == bits && isUnicodeScalar bits.toNat
          | _ => false) with
        | false => rw [hkey] at hadm; cases hadm
        | true =>
          rw [hkey] at hadm
          have hih := ih hadm
          have hlt : target + 1 < fnBlocks := by
            rw [hblocks, Nat.add_comm 1 numBlocks]
            exact Nat.add_lt_add_right (nat_lt_of_blt_tr ht) 1
          have hblt1 : Nat.blt (target + 1) fnBlocks = true :=
            nat_blt_of_lt_tr hlt
          cases dTy <;>
            (dsimp only [translateSwitchCasesForTy, translateIntSwitchBranches,
              translateNatSwitchBranches, List.all];
             rw [hblt1];
             exact hih)

theorem mrType_beq_emptySizedTy_self (sz al : Nat) :
    MrType.beq (emptySizedTy sz al) (emptySizedTy sz al) = true := by
  dsimp only [emptySizedTy, MrType.beq, TupleFields.beq, Size.beq, Align.beq]
  rw [Nat.beq_refl sz, Nat.beq_refl al]
  rfl

theorem findDiscrVariant?_lt (discrBits : BitVec 128) (ds : List Nat) (v : Nat)
    (h : findDiscrVariant? discrBits ds = some v) :
    v < ds.length ∧
    ∃ d, listGet? ds v = some d ∧ BitVec.ofNat 128 d = discrBits := by
  have haux : ∀ (xs : List Nat) (idx : Nat),
      findDiscrVariantAux idx discrBits xs = some v →
      idx ≤ v ∧ v < idx + xs.length ∧
      ∃ d, listGet? xs (v - idx) = some d ∧ BitVec.ofNat 128 d = discrBits := by
    intro xs
    induction xs with
    | nil => intro idx h1; cases h1
    | cons a as ih =>
      intro idx h1
      dsimp only [findDiscrVariantAux] at h1
      cases hbeq : (BitVec.ofNat 128 a == discrBits) with
      | true =>
        rw [hbeq] at h1
        injection h1 with hveq; subst hveq
        refine ⟨Nat.le_refl _, ?_, a, ?_, eq_of_beq hbeq⟩
        · dsimp only [List.length]; rw [Nat.add_succ]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
            (Nat.succ_le_succ (Nat.le_add_right _ _))
        · rw [Nat.sub_self]; rfl
      | false =>
        rw [hbeq] at h1
        cases ih (idx + 1) h1 with
        | intro hge hrest =>
          cases hrest with
          | intro hlt hd =>
            have hlenEq : idx + (a :: as).length = idx + 1 + as.length := by
              dsimp only [List.length]
              rw [Nat.add_assoc, Nat.add_comm 1 as.length]
            refine ⟨Nat.le_trans (Nat.le_succ _) hge, ?_, ?_⟩
            · rw [hlenEq]; exact hlt
            · cases hd with
              | intro d hdSpec =>
                refine ⟨d, ?_, hdSpec.2⟩
                have hpos : 0 < v - idx := Nat.sub_pos_of_lt hge
                have hsub : v - idx = (v - (idx + 1)) + 1 := by
                  rw [← Nat.sub_sub]; exact (Nat.sub_add_cancel hpos).symm
                rw [hsub]; exact hdSpec.1
  cases haux ds 0 h with
  | intro _ hrest =>
    rw [Nat.zero_add, Nat.sub_zero] at hrest
    exact hrest

theorem buildEnumVariants_find?_of_getElem? (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (ds : List Nat) (v d : Nat)
    (hg : Trusted.MirSemantics.getElem? ds v = some d) :
    ∃ tagger,
      (buildEnumVariants ety tagW tagS ds).find?
        (discrIntOfNat ety.discrWidth ety.discrSigned d) =
      some (emptySizedTy tagW.byteSize tagW.byteSize, tagger) := by
  rw [getElem_to_listGet?] at hg
  induction ds generalizing v with
  | nil => cases hg
  | cons x rest ih =>
    dsimp only [buildEnumVariants, EnumVariants.find?]
    cases heq : (discrIntOfNat ety.discrWidth ety.discrSigned x ==
        discrIntOfNat ety.discrWidth ety.discrSigned d) with
    | true => exact ⟨_, rfl⟩
    | false =>
      cases v with
      | zero =>
        dsimp only [listGet?] at hg
        injection hg with hxd
        subst hxd
        rw [beq_self_eq_true] at heq
        cases heq
      | succ v' =>
        dsimp only [listGet?] at hg
        exact ih v' hg

theorem evalValue_translateConst_enum_zeroSized (ety : EnumTy)
    (frame : StackFrame) (mem : MrMemory)
    (hrepr : ety.tagRepr = .zeroSized) :
    evalValue frame mem (translateConst ⟨.enum ety, .zeroSized⟩) =
      .ok (translateVal (.enumVal ety 0), translateTy (.enum ety)) := by
  dsimp only [translateConst, translateTy, translateEnumTy, translateVal]
  rw [hrepr]
  dsimp only [evalValue, EnumVariants.find?]
  rw [beq_self_eq_true]
  rfl

theorem evalValue_translateConst_enum_scalar (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (bits : BitVec 128) (v : Nat)
    (frame : StackFrame) (mem : MrMemory)
    (hrepr : ety.tagRepr = .scalar tagW tagS)
    (hfind : findDiscrVariant?
      (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
      ety.discriminants = some v) :
    evalValue frame mem (translateConst ⟨.enum ety, .scalar bits⟩) =
      .ok (translateVal (.enumVal ety v), translateTy (.enum ety)) := by
  cases findDiscrVariant?_lt _ _ _ hfind with
  | intro _ hdEx =>
    cases hdEx with
    | intro d hd =>
      have hd' : Trusted.MirSemantics.getElem? ety.discriminants v = some d := by
        rw [getElem_to_listGet?]
        exact hd.1
      cases buildEnumVariants_find?_of_getElem? ety tagW tagS
          ety.discriminants v d hd' with
      | intro tagger hvar =>
        dsimp only [translateConst, translateTy, translateEnumTy, translateVal]
        rw [hrepr]
        dsimp only
        rw [hfind]
        dsimp only [evalValue, evalValueList]
        rw [hd', hvar]
        dsimp only
        rw [mrType_beq_emptySizedTy_self]
        rfl

theorem translateConst_variantWF (c : ConstOperand)
    (hadm : constAdmitted false c = true) :
    mrValueExprVariantWF (translateConst c) = true := by
  cases c with
  | mk ty lit =>
    cases ty with
    | int w s =>
      cases lit with
      | scalar _ => rfl
      | _ => cases hadm
    | bool =>
      cases lit with
      | scalar bits =>
        dsimp only [translateConst]
        cases (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
        | true => rfl
        | false =>
          cases (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) <;> rfl
      | _ => cases hadm
    | unit =>
      cases lit with
      | zeroSized => rfl
      | _ => cases hadm
    | char =>
      cases lit with
      | scalar _ => rfl
      | _ => cases hadm
    | ordering =>
      cases lit with
      | scalar bits =>
        dsimp only [translateConst]
        cases orderingOfTagBits bits.toNat with
        | none => rfl
        | some ord => cases ord <;> rfl
      | _ => cases hadm
    | enum ety =>
      cases lit with
      | rodataBytes _ | rodataRef _ _ _ _ => cases hadm
      | zeroSized =>
        dsimp only [constAdmitted, isZstEnumTy] at hadm
        cases hrepr : ety.tagRepr with
        | scalar _ _ => rw [hrepr] at hadm; cases hadm
        | zeroSized =>
          dsimp only [translateConst, translateEnumTy]
          rw [hrepr]
          dsimp only [mrValueExprVariantWF, mrValueExprListVariantWF,
            EnumVariants.find?, mrSelfTypedExprTy?]
          rw [beq_self_eq_true]
          rfl
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        cases hrepr : ety.tagRepr with
        | zeroSized => rw [hrepr] at hadm; cases hadm
        | scalar tagW tagS =>
          dsimp only [translateConst, translateEnumTy]
          rw [hrepr]
          dsimp only
          cases hfind : findDiscrVariant?
              (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
              ety.discriminants with
          | none => rfl
          | some v =>
            cases findDiscrVariant?_lt _ _ _ hfind with
            | intro _ hdEx =>
              cases hdEx with
              | intro d hd =>
                have hd' :
                    Trusted.MirSemantics.getElem? ety.discriminants v =
                      some d := by
                  rw [getElem_to_listGet?]
                  exact hd.1
                cases buildEnumVariants_find?_of_getElem? ety tagW tagS
                    ety.discriminants v d hd' with
                | intro tagger hvar =>
                  dsimp only
                  rw [hd']
                  dsimp only [mrValueExprVariantWF, mrValueExprListVariantWF,
                    mrSelfTypedExprTy?]
                  rw [hvar]
                  dsimp only [Bool.true_and]
                  exact mrType_beq_emptySizedTy_self tagW.byteSize tagW.byteSize
    | never | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _
    | rangeFrom _ | option _ | tuple _ | vec _ | box _ | unsupported =>
      cases lit <;> cases hadm

theorem translateOperand_variantWF (bodyLocals : List MirTy) (opnd : Operand)
    (hadm : operandAdmitted false bodyLocals opnd = true) :
    mrValueExprVariantWF (translateOperand opnd) = true := by
  cases opnd with
  | copy _ => rfl
  | move _ => rfl
  | constant c => exact translateConst_variantWF c hadm

theorem translateRvalue_variantWF (bodyLocals : List MirTy) (dstTy : MirTy)
    (rv : Rvalue) (hadm : rvalueAdmitted false bodyLocals dstTy rv = true) :
    mrValueExprVariantWF (translateRvalue bodyLocals rv) = true := by
  cases rv with
  | use opnd =>
    dsimp only [rvalueAdmitted] at hadm
    cases hoa : operandAdmitted false bodyLocals opnd with
    | false => rw [hoa] at hadm; cases hadm
    | true => exact translateOperand_variantWF bodyLocals opnd hoa
  | unaryOp op opnd =>
    dsimp only [rvalueAdmitted] at hadm
    cases hoa : operandAdmitted false bodyLocals opnd with
    | false => rw [hoa] at hadm; cases hadm
    | true =>
      have hw := translateOperand_variantWF bodyLocals opnd hoa
      dsimp only [translateRvalue]
      cases op with
      | ptrMetadata => exact hw
      | not =>
        cases operandTy? bodyLocals opnd with
        | none => exact hw
        | some srcTy =>
          cases srcTy with
          | bool =>
            dsimp only [mrValueExprVariantWF]
            rw [hw]
            rfl
          | int _ _ | unit | never | char | ordering | enum _ | ref _ _
          | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _
          | option _ | tuple _ | vec _ | box _ | unsupported => exact hw
      | neg =>
        cases operandTy? bodyLocals opnd with
        | none => exact hw
        | some srcTy =>
          cases srcTy with
          | int _ s => cases s <;> exact hw
          | bool | unit | never | char | ordering | enum _ | ref _ _
          | rawPtr _ _ | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _
          | option _ | tuple _ | vec _ | box _ | unsupported => exact hw
  | binaryOp op lhs rhs =>
    dsimp only [rvalueAdmitted] at hadm
    cases hl : operandAdmitted false bodyLocals lhs with
    | false => rw [hl] at hadm; cases hadm
    | true =>
      cases hr : operandAdmitted false bodyLocals rhs with
      | false => rw [hl, hr] at hadm; cases hadm
      | true =>
        have hlw := translateOperand_variantWF bodyLocals lhs hl
        have hrw := translateOperand_variantWF bodyLocals rhs hr
        have hboth : (mrValueExprVariantWF (translateOperand lhs) &&
            mrValueExprVariantWF (translateOperand rhs)) = true := by
          rw [hlw, hrw]; rfl
        dsimp only [translateRvalue]
        cases operandTy? bodyLocals lhs with
        | none => exact hlw
        | some lTy =>
          cases lTy with
          | int _ _ => cases op <;> first | exact hboth | exact hlw
          | bool => cases op <;> first | exact hboth | exact hlw
          | char => cases op <;> first | exact hboth | exact hlw
          | unit | never | ordering | enum _ | ref _ _ | rawPtr _ _
          | slice _ | str | array _ _ | range _ | rangeTo _ | rangeFrom _ | option _
          | tuple _ | vec _ | box _ | unsupported =>
            exact hlw
  | cast kind opnd castTy =>
    cases kind with
    | ptrToPtr | intToPtr | unsize | boxAsRef | unsupported => cases hadm
    | intToInt =>
      dsimp only [rvalueAdmitted] at hadm
      cases hoa : operandAdmitted false bodyLocals opnd with
      | false => rw [hoa] at hadm; cases hadm
      | true =>
        have hw := translateOperand_variantWF bodyLocals opnd hoa
        have heInt :
            mrValueExprVariantWF
              (match operandTy? bodyLocals opnd with
              | some .bool =>
                .unOp (.cast (.transmute (.int u8Ty))) (translateOperand opnd)
              | _ => translateOperand opnd) = true := by
          cases operandTy? bodyLocals opnd with
          | none => exact hw
          | some srcTy => cases srcTy <;> exact hw
        dsimp only [translateRvalue]
        cases castTy <;> exact heInt
  | discriminant _ => rfl
  | useRetag _ | ref _ _ | addressOf _ _ | fakeAddressOf _
  | aggregateTuple _ | aggregateArray _ _ | repeat_ _ _ _
  | aggregateRange _ _ _ | aggregateRangeTo _ _ | aggregateRangeFrom _ _
  | aggregateOption _ _ _ | unsupported =>
    cases hadm

theorem translateStmt_wf (body : Body) (stmt : StatementKind)
    (h0 : 0 < body.locals.length)
    (hadm : stmtAdmitted false body.argumentCount body.locals stmt = true) :
    mrStmtWellFormed (translateBody body)
      (translateStmt body.locals stmt) = true := by
  have hlen : (translateBody body).locals.length = body.locals.length := by
    dsimp only [translateBody]
    exact list_length_map_tr translateTy body.locals
  cases stmt with
  | nop =>
    dsimp only [translateStmt, mrStmtWellFormed, mrPlaceWellFormed]
    rw [hlen]
    exact nat_blt_of_lt_tr h0
  | unsupported => cases hadm
  | storageLive id =>
    dsimp only [stmtAdmitted] at hadm
    dsimp only [translateStmt, mrStmtWellFormed]
    rw [hlen]
    exact hadm
  | storageDead id =>
    dsimp only [stmtAdmitted] at hadm
    cases harg : Nat.blt body.argumentCount id with
    | false => rw [harg] at hadm; cases hadm
    | true =>
      rw [harg, Bool.true_and] at hadm
      have hgtArg : body.argumentCount < id := nat_lt_of_blt_tr harg
      have hgt0 : 0 < id := Nat.lt_of_le_of_lt (Nat.zero_le _) hgtArg
      have hne0 : Nat.beq id 0 = false := by
        cases id with
        | zero => cases hgt0
        | succ _ => rfl
      have hle : 1 + body.argumentCount ≤ id := by
        rw [Nat.add_comm 1 body.argumentCount]
        exact hgtArg
      have hnotArg :
          (rangeNat 1 body.argumentCount).any (Nat.beq id) = false :=
        rangeNat_any_eq_false 1 body.argumentCount id hle
      dsimp only [translateStmt, mrStmtWellFormed, translateBody]
      rw [list_length_map_tr, hadm, hne0, hnotArg]
      rfl
  | assign dst rv =>
    dsimp only [stmtAdmitted] at hadm
    cases hp : dst.projection.isEmpty with
    | false => rw [hp] at hadm; cases hadm
    | true =>
      rw [hp] at hadm
      cases hg : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hg] at hadm; cases hadm
      | some dstTy =>
        rw [hg, Bool.true_and] at hadm
        have hlg : listGet? body.locals dst.localId = some dstTy := by
          rw [← getElem_to_listGet?]
          exact hg
        have hlt : dst.localId < body.locals.length :=
          listGet?_lt_length body.locals dst.localId dstTy hlg
        dsimp only [translateStmt, mrStmtWellFormed, mrPlaceWellFormed]
        rw [hlen, nat_blt_of_lt_tr hlt,
          translateRvalue_variantWF body.locals dstTy rv hadm]
        rfl

theorem list_all_map_wf {α β : Type} (f : α → β) (p : α → Bool) (q : β → Bool)
    (xs : List α) (himp : ∀ x, p x = true → q (f x) = true)
    (hall : xs.all p = true) :
    (xs.map f).all q = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [List.all] at hall
    dsimp only [List.map, List.all]
    cases hp : p x with
    | false => rw [hp] at hall; cases hall
    | true =>
      rw [hp] at hall
      rw [himp x hp]
      exact ih hall

/-- Every `MiniRustAdmitted` program translates to a structurally well-formed
MiniRust `MrProgram` (`spec/lang/well-formed.md`), with a `0`-arg, `1`-ZST
`start` function in `functions` and a pure-upstream-terminator entry body free
of `StorageDead` on return or argument locals and duplicate `Switch` keys. -/
theorem minirust_admitted_prog_wellFormed {p : Program} {q : Query}
    (hadm : MiniRustAdmitted p q) :
    mrProgWellFormed (translateProg p) p.entryDefId = true := by
  cases hadm with
  | intro hprog _ =>
    dsimp only [MiniRustProgAdmitted] at hprog
    cases hw : Nat.beq p.pointerWidthBits 64 with
    | false => rw [hw] at hprog; cases hprog
    | true =>
      cases hv : Nat.beq p.mirProfileVersion 1 with
      | false => rw [hw, hv] at hprog; cases hprog
      | true =>
        rw [hw, hv] at hprog
        cases hbody : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
        | none => rw [hbody] at hprog; cases hprog
        | some body =>
          rw [hbody] at hprog
          dsimp only [MiniRustBodyAdmitted, bodyAdmittedWith] at hprog
          cases h1 : !body.basicBlocks.isEmpty with
          | false => rw [h1] at hprog; cases hprog
          | true =>
            cases h2 : Nat.blt body.argumentCount body.locals.length with
            | false => rw [h1, h2] at hprog; cases hprog
            | true =>
              cases h3 : storageAnnotationsInBounds body with
              | false => rw [h1, h2, h3] at hprog; cases hprog
              | true =>
                cases h4 : discriminantTypesValid body with
                | false => rw [h1, h2, h3, h4] at hprog; cases hprog
                | true =>
                  cases h5 : castTypesValid body with
                  | false => rw [h1, h2, h3, h4, h5] at hprog; cases hprog
                  | true =>
                    cases h6 : body.locals.all isSupportedScalarOrUnitTy with
                    | false => rw [h1, h2, h3, h4, h5, h6] at hprog; cases hprog
                    | true =>
                      rw [h1, h2, h3, h4, h5, h6] at hprog
                      have hargLt : body.argumentCount < body.locals.length :=
                        nat_lt_of_blt_tr h2
                      have hlocPos : 0 < body.locals.length :=
                        Nat.lt_of_le_of_lt (Nat.zero_le _) hargLt
                      have hbbPos : 0 < body.basicBlocks.length := by
                        cases hbbs : body.basicBlocks with
                        | nil => rw [hbbs] at h1; cases h1
                        | cons _ _ => exact Nat.zero_lt_succ _
                      dsimp only [mrProgWellFormed, translateProg]
                      rw [hbody]
                      have hlenMap : (p.bodies.map translateBody).length =
                          p.bodies.length :=
                        list_length_map_tr translateBody p.bodies
                      have hstartGet :
                          listGet?
                            (p.bodies.map translateBody ++
                              [harnessCallerFunc
                                (match Trusted.MirSemantics.getElem? body.locals 0 with
                                | some ty => translateTy ty
                                | none => unitTy)])
                            p.bodies.length =
                          some (harnessCallerFunc
                            (match Trusted.MirSemantics.getElem? body.locals 0 with
                            | some ty => translateTy ty
                            | none => unitTy)) := by
                        rw [← hlenMap]
                        exact listGet?_append_singleton _ _
                      have hentryLg : listGet? p.bodies p.entryDefId = some body := by
                        rw [← getElem_to_listGet?]
                        exact hbody
                      have hentryGet :
                          listGet?
                            (p.bodies.map translateBody ++
                              [harnessCallerFunc
                                (match Trusted.MirSemantics.getElem? body.locals 0 with
                                | some ty => translateTy ty
                                | none => unitTy)])
                            p.entryDefId =
                          some (translateBody body) := by
                        apply listGet?_append_left
                        rw [listGet?_map_tr, hentryLg]
                        rfl
                      rw [hstartGet, hentryGet]
                      dsimp only
                      have hstartWf :
                          mrFuncWellFormed true
                            (harnessCallerFunc
                              (match Trusted.MirSemantics.getElem? body.locals 0 with
                              | some ty => translateTy ty
                              | none => unitTy)) = true := rfl
                      have hstartMeta :
                          (harnessCallerFunc
                            (match Trusted.MirSemantics.getElem? body.locals 0 with
                            | some ty => translateTy ty
                            | none => unitTy)).args.isEmpty = true := rfl
                      rw [hstartMeta, hstartWf]
                      dsimp only [harnessCallerFunc, listGet?, unitTy,
                        MrType.size, MrType.align]
                      have h00 : (Nat.beq 0 0 && Nat.beq 1 1) = true := rfl
                      rw [h00]
                      dsimp only [Bool.true_and, mrFuncWellFormed, translateBody]
                      have hfnLocLen :
                          (body.locals.map translateTy).length = body.locals.length :=
                        list_length_map_tr translateTy body.locals
                      have hfnBlkLen :
                          ({ statements := (alwaysLiveTemps body).map MrStatement.storageLive
                             terminator := MrTerminator.goto 1 } ::
                            body.basicBlocks.map (translateBlock body.locals)).length =
                          1 + body.basicBlocks.length := by
                        dsimp only [List.length]
                        rw [list_length_map_tr, Nat.add_comm]
                      have hretBlt : Nat.blt 0 (body.locals.map translateTy).length = true := by
                        rw [hfnLocLen]
                        exact nat_blt_of_lt_tr hlocPos
                      have hargsOk :
                          (rangeNat 1 body.argumentCount).all
                            (fun a => !Nat.beq a 0 &&
                              Nat.blt a (body.locals.map translateTy).length) = true := by
                        rw [hfnLocLen]
                        have hle : 1 + body.argumentCount ≤ body.locals.length := by
                          rw [Nat.add_comm 1 body.argumentCount]
                          exact hargLt
                        exact rangeNat_all_bounds 1 body.argumentCount
                          body.locals.length (Nat.zero_lt_succ 0) hle
                      have hinitStmts :
                          ((alwaysLiveTemps body).map MrStatement.storageLive).all
                            (mrStmtWellFormed (translateBody body)) = true := by
                        apply alwaysLiveTempsAux_wf body (translateBody body)
                        · dsimp only [translateBody]
                          exact hfnLocLen
                        · exact Nat.zero_add body.locals.length
                      have hgoto1 :
                          Nat.blt 1
                            (1 + (body.basicBlocks.map
                              (translateBlock body.locals)).length) = true := by
                        rw [list_length_map_tr]
                        exact nat_blt_of_lt_tr (Nat.add_lt_add_left hbbPos 1)
                      have hblocksOk :
                          (body.basicBlocks.map (translateBlock body.locals)).all
                            (fun bb =>
                              bb.statements.all (mrStmtWellFormed (translateBody body)) &&
                              mrTermWellFormed false (translateBody body) bb.terminator) =
                            true := by
                        apply list_all_map_wf (translateBlock body.locals)
                          (blockAdmitted false body.argumentCount body.locals
                            body.basicBlocks.length) _ body.basicBlocks _ hprog
                        intro bb hbb
                        dsimp only [blockAdmitted] at hbb
                        cases hcl : bb.cleanup with
                        | true => rw [hcl] at hbb; cases hbb
                        | false =>
                          rw [hcl] at hbb
                          cases hst : bb.statements.all
                              (stmtAdmitted false body.argumentCount body.locals) with
                          | false => rw [hst] at hbb; cases hbb
                          | true =>
                            rw [hst] at hbb
                            have hstWf :
                                (bb.statements.map (translateStmt body.locals)).all
                                  (mrStmtWellFormed (translateBody body)) = true :=
                              list_all_map_wf (translateStmt body.locals)
                                (stmtAdmitted false body.argumentCount body.locals)
                                (mrStmtWellFormed (translateBody body))
                                bb.statements
                                (fun st h => translateStmt_wf body st hlocPos h) hst
                            dsimp only [translateBlock]
                            rw [hstWf, Bool.true_and]
                            have hfbLen :
                                (translateBody body).blocks.length =
                                  1 + body.basicBlocks.length := by
                              dsimp only [translateBody, List.length]
                              rw [list_length_map_tr, Nat.add_comm]
                            cases htm : bb.terminator with
                            | return_ => rfl
                            | unreachable => rfl
                            | goto target =>
                              rw [htm] at hbb
                              dsimp only [translateTerm, mrTermWellFormed]
                              rw [hfbLen, Nat.add_comm 1 body.basicBlocks.length]
                              exact nat_blt_of_lt_tr
                                (Nat.add_lt_add_right (nat_lt_of_blt_tr hbb) 1)
                            | switchInt discr targets =>
                              rw [htm] at hbb
                              dsimp only at hbb
                              cases ho : operandAdmitted false body.locals discr with
                              | false => rw [ho] at hbb; cases hbb
                              | true =>
                                cases hoth : Nat.blt targets.otherwise
                                    body.basicBlocks.length with
                                | false => rw [ho, hoth] at hbb; cases hbb
                                | true =>
                                  rw [ho, hoth] at hbb
                                  cases hop : operandTy? body.locals discr with
                                  | none => rw [hop] at hbb; cases hbb
                                  | some dTy =>
                                    rw [hop] at hbb
                                    have hopWf :=
                                      translateOperand_variantWF body.locals
                                        discr ho
                                    have hothWf :
                                        Nat.blt (targets.otherwise + 1)
                                          (translateBody body).blocks.length = true := by
                                      rw [hfbLen, Nat.add_comm 1 body.basicBlocks.length]
                                      exact nat_blt_of_lt_tr
                                        (Nat.add_lt_add_right (nat_lt_of_blt_tr hoth) 1)
                                    cases dTy with
                                    | int w s =>
                                      dsimp only at hbb
                                      cases hsb : switchBranchesAdmitted
                                          body.basicBlocks.length (.int w s)
                                          targets.branches with
                                      | false => rw [hsb] at hbb; cases hbb
                                      | true =>
                                        rw [hsb] at hbb
                                        dsimp only [translateTerm]
                                        rw [hop]
                                        dsimp only [mrTermWellFormed]
                                        rw [hopWf, hothWf]
                                        have hcs := switchBranches_targets_wf
                                          body.basicBlocks.length
                                          (translateBody body).blocks.length
                                          hfbLen (.int w s) targets.branches hsb
                                        dsimp only [translateSwitchCasesForTy] at hcs
                                        dsimp only [translateSwitchCasesForTy] at hbb
                                        rw [hcs]
                                        exact hbb
                                    | bool =>
                                      dsimp only at hbb
                                      cases hsb : switchBranchesAdmitted
                                          body.basicBlocks.length .bool
                                          targets.branches with
                                      | false => rw [hsb] at hbb; cases hbb
                                      | true =>
                                        rw [hsb] at hbb
                                        dsimp only [translateTerm]
                                        rw [hop]
                                        dsimp only [mrTermWellFormed,
                                          mrValueExprVariantWF]
                                        rw [hopWf, hothWf]
                                        have hcs := switchBranches_targets_wf
                                          body.basicBlocks.length
                                          (translateBody body).blocks.length
                                          hfbLen .bool targets.branches hsb
                                        dsimp only [translateSwitchCasesForTy] at hcs
                                        dsimp only [translateSwitchCasesForTy] at hbb
                                        rw [hcs]
                                        exact hbb
                                    | char =>
                                      dsimp only at hbb
                                      cases hsb : switchBranchesAdmitted
                                          body.basicBlocks.length .char
                                          targets.branches with
                                      | false => rw [hsb] at hbb; cases hbb
                                      | true =>
                                        rw [hsb] at hbb
                                        dsimp only [translateTerm]
                                        rw [hop]
                                        dsimp only [mrTermWellFormed]
                                        rw [hopWf, hothWf]
                                        have hcs := switchBranches_targets_wf
                                          body.basicBlocks.length
                                          (translateBody body).blocks.length
                                          hfbLen .char targets.branches hsb
                                        dsimp only [translateSwitchCasesForTy] at hcs
                                        dsimp only [translateSwitchCasesForTy] at hbb
                                        rw [hcs]
                                        exact hbb
                                    | unit | never | ordering | enum _ | ref _ _
                                    | rawPtr _ _ | slice _ | str | array _ _
                                    | range _ | rangeTo _ | rangeFrom _
                                    | option _ | tuple _ | vec _ | box _ | unsupported =>
                                      cases hbb
                            | unwindResume => rw [htm] at hbb; cases hbb
                            | assert _ _ _ _ _ => rw [htm] at hbb; cases hbb
                            | call _ _ _ _ _ => rw [htm] at hbb; cases hbb
                            | coreCall _ _ _ _ _ => rw [htm] at hbb; cases hbb
                            | sysrootCall _ _ _ _ _ => rw [htm] at hbb; cases hbb
                            | unsupported => rw [htm] at hbb; cases hbb
                      dsimp only [List.isEmpty, Bool.not_false, List.length]
                      have h0lt : Nat.blt 0
                          ((body.basicBlocks.map
                            (translateBlock body.locals)).length + 1) = true :=
                        Nat.ble_eq_true_of_le (Nat.succ_le_succ (Nat.zero_le _))
                      rw [h0lt, hretBlt, hargsOk]
                      dsimp only [List.all]
                      change ((((alwaysLiveTemps body).map
                        MrStatement.storageLive).all
                        (mrStmtWellFormed (translateBody body)) &&
                        mrTermWellFormed false (translateBody body)
                          (MrTerminator.goto 1)) &&
                        (body.basicBlocks.map (translateBlock body.locals)).all
                          (fun bb =>
                            bb.statements.all (mrStmtWellFormed (translateBody body)) &&
                            mrTermWellFormed false (translateBody body)
                              bb.terminator)) = true
                      rw [hinitStmts, hblocksOk]
                      dsimp only [mrTermWellFormed, translateBody, List.length]
                      rw [Nat.add_comm _ 1]
                      rw [hgoto1]
                      rfl

end Anneal.MiniRust
