-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Miri.Interpreter.ExecutionMachine
import Trusted.MirAst
import Trusted.MirModel
import Trusted.Correspondence.Codec

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Reference Machine State, Layouts, AST Lowering, and Init
(`Trusted.Correspondence.State`)

Defines the real `Miri.Interpreter.MachineHooks.State`-backed reference state
(`RefUser`, `RefState`), `RefOutcome`, `Miri.ABI.LayoutData` adapters, real
`Miri.MIR.Body` lowering (`toMiriBody`), return-allocation initialization
(`refInitMemoryAndRetPlace`, `initRefState`), and return-value decoding
(`refReadReturnVal`). Imports only `Init.*`, `Miri.*`, `Trusted.MirAst`,
`Trusted.MirModel`, and `Trusted.Correspondence.Codec`, never
`Trusted.MirSemantics`.
-/

/-! ## Reference Machine State and Step Outcomes ($M_{\text{ref}}$) -/

/-- User payload embedded in `Miri.Interpreter.MachineHooks.MachineState Unit
RefUser`, carrying `TerminatorMachine.Control Unit` (stepped by
`beforeTerminatorWithChoice`) and `callerMem : CallerMemory`. -/
structure RefUser where
  control : Miri.Interpreter.TerminatorMachine.Control Unit
  callerMem : CallerMemory

/-- Initial deterministic terminator-control state for $M_{\text{ref}}$:
wrapping counters (`checkedArithmetic := false`), disabled GC
(`gcInterval := 0`), zero preemption rate, and virtual monotonic clock at `0`.
-/
noncomputable def refInitControl :
    Miri.Interpreter.TerminatorMachine.Control Unit := {
  basicBlockCount := 0
  sinceGc := 0
  gcInterval := 0
  monotonic := .virtual 0
  preemptionRateBits := 0
  checkedArithmetic := false
}

/-- One-terminator deterministic update of `TerminatorMachine.Control Unit`
matching `Miri.Interpreter.TerminatorMachine.beforeTerminatorWithChoice` under
`checkedArithmetic = false`, `gcInterval = 0`, and `fixedScheduling = true`. -/
noncomputable def advanceRefControl
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) :
    Miri.Interpreter.TerminatorMachine.Control Unit :=
  let nextMono :=
    match ctrl.monotonic with
    | .virtual n => .virtual (BitVec.ofNat 128 (n.toNat + 5000))
    | .host h => .host h
  { ctrl with
    basicBlockCount := ctrl.basicBlockCount + 1
    sinceGc := ctrl.sinceGc + 1
    monotonic := nextMono }

/-- Invariant on `TerminatorMachine.Control Unit` preserved across every
reference execution step. -/
def RefControlValid
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit) : Prop :=
  ctrl.gcInterval = 0 ∧
  ctrl.preemptionRateBits = 0 ∧
  ctrl.checkedArithmetic = false ∧
  ∃ n : Miri.ABI.U128, ctrl.monotonic = .virtual n

/-- Reference machine state for $M_{\text{ref}}$, directly wrapping
`Miri.Interpreter.MachineHooks.State Unit RefUser` stepped by
`Miri.Interpreter.ExecutionMachine.step`, paired with the entry function's
return type `retTy`, caller-owned return allocation `retPlace` in
`miri.machine.memory` (matching `Miri.Interpreter.callMain`), and explicit
outer step-budget counters `stepsExecuted` / `maxSteps`. -/
structure RefState where
  miri : Miri.Interpreter.MachineHooks.State Unit RefUser
  retTy : MirTy
  retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance
  stepsExecuted : Nat := 0
  maxSteps : Nat := 0

/-- Five-way reference step outcome translating
`Miri.Interpreter.ExecutionMachine.step`'s `StepResult (MachineHooks.State Unit
RefUser) Bool` together with explicit outer step-budget exhaustion
(`exhaustedStepLimit`). -/
inductive RefOutcome where
  | running (next : RefState)
  | returned (out : TerminalOut)
  | exhaustedStepLimit
  | ub
  | blocked

/-- Admissible demonic choice predicate in $M_{\text{ref}}$. -/
def ValidRefChoice (_rp : RefProg) (_rs : RefState)
    (c : Choice) : Prop :=
  c = 0

/-- Map $M_{\text{anneal}}$'s two fault poles to $M_{\text{ref}}$'s `.ub` and
`.blocked` outcomes. -/
noncomputable def faultToRefOutcome : FaultKind → RefOutcome
  | .undefined => .ub
  | .unsupported => .blocked

/-! ## Static Body Checks in $M_{\text{ref}}$ -/

/-- Whether `RefStatementKind` is a `StorageLive` or `StorageDead` annotation
for `localId`. -/
noncomputable def refStmtHasStorageMarker (localId : LocalId) :
    RefStatementKind → Bool
  | .storageLive id | .storageDead id => Nat.beq id localId
  | _ => false

/-- Whether `rbody` contains a `StorageLive` or `StorageDead` annotation for
`localId`. -/
noncomputable def refHasStorageAnnotation (rbody : RefBody)
    (localId : LocalId) : Bool :=
  rbody.basicBlocks.any (fun bb =>
    bb.statements.any (refStmtHasStorageMarker localId))

/-- Check that all `StorageLive` and `StorageDead` local indices in `rbody` are
in bounds (`< rbody.locals.length`). -/
noncomputable def refStorageAnnotationsInBounds (rbody : RefBody) : Bool :=
  let numLocals := rbody.locals.length
  rbody.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id numLocals
      | _ => true))

/-! ## Scalar, Integer, and Fieldless-Enum Adapters -/

/-- Map an Anneal `IntWidth` to its `Miri.ABI.Size` in bytes (`1`, `2`, `4`,
`8`, or `16` bytes on 64-bit targets). -/
noncomputable def toMiriSize : IntWidth → Miri.ABI.Size
  | .i8 => Miri.ABI.Size.ofBytes 1
  | .i16 => Miri.ABI.Size.ofBytes 2
  | .i32 => Miri.ABI.Size.ofBytes 4
  | .i64 => Miri.ABI.Size.ofBytes 8
  | .i128 => Miri.ABI.Size.ofBytes 16
  | .isize => Miri.ABI.Size.ofBytes 8

/-- Map `(w, signed)` to `Miri.MIR.IntegerKind`
(`vendor/lean-miri/Miri/MIR/Operators.lean`). -/
noncomputable def toMiriIntKind :
    IntWidth → Bool → Miri.MIR.IntegerKind
  | .i8, true => .i8
  | .i8, false => .u8
  | .i16, true => .i16
  | .i16, false => .u16
  | .i32, true => .i32
  | .i32, false => .u32
  | .i64, true => .i64
  | .i64, false => .u64
  | .i128, true => .i128
  | .i128, false => .u128
  | .isize, true => .isize
  | .isize, false => .usize

/-- Construct the `Miri.Interpreter.IntegerType` for `(w, signed)`. -/
noncomputable def toMiriIntType (w : IntWidth) (s : Bool) :
    Miri.Interpreter.IntegerType :=
  ⟨toMiriSize w, toMiriIntKind w s⟩

/-- Construct a `Miri.Memory.ScalarInt` at width `w` via
`Miri.Memory.ScalarInt.truncateFromUInt`. -/
noncomputable def miriScalar (w : IntWidth) (bits : BitVec 128) :
    Miri.Memory.ScalarInt :=
  match Miri.Memory.ScalarInt.truncateFromUInt bits (toMiriSize w) with
  | .ok (sc, _) => sc
  | .error _ => Miri.Memory.ScalarInt.ofUInt128 bits

/-- Lift a `ScalarVal` into a `Miri.Interpreter.IntegerValue`. -/
noncomputable def miriIntValue (sv : ScalarVal) :
    Miri.Interpreter.IntegerValue :=
  ⟨miriScalar sv.width sv.bits, toMiriIntType sv.width sv.signed⟩

/-- Map an Anneal `IntWidth` to its `Miri.ABI.Integer` on 64-bit targets. -/
noncomputable def toMiriInteger : IntWidth → Miri.ABI.Integer
  | .i8 => .I8
  | .i16 => .I16
  | .i32 => .I32
  | .i64 => .I64
  | .i128 => .I128
  | .isize => .I64

/-- Map a `Miri.ABI.Integer` back to a fixed-width `IntWidth`. -/
noncomputable def intWidthOfMiriInteger : Miri.ABI.Integer → IntWidth
  | .I8 => .i8
  | .I16 => .i16
  | .I32 => .i32
  | .I64 => .i64
  | .I128 => .i128

/-- Independent `List Nat` non-membership check in $M_{\text{ref}}$. -/
noncomputable def refNatNotElem (x : Nat) : List Nat → Bool
  | [] => true
  | y :: ys => !Nat.beq x y && refNatNotElem x ys

/-- Independent pairwise-distinctness check on `List Nat` in
$M_{\text{ref}}$. -/
noncomputable def refNatListPairwiseNe : List Nat → Bool
  | [] => true
  | x :: xs => refNatNotElem x xs && refNatListPairwiseNe xs

/-- Independent $M_{\text{ref}}$ tag-to-discriminant extension using
`Miri.ABI.Size.signExtend`, `BitVec.ofInt 128`, and `Miri.ABI.Size.truncate`
(`vendor/lean-miri/Miri/Interpreter/Discriminant.lean`). -/
noncomputable def refMiriTagToDiscrBits (tagW : IntWidth) (tagS : Bool)
    (discrW : IntWidth) (tagBits : BitVec 128) : Option (BitVec 128) :=
  let tagSz := toMiriSize tagW
  let discrSz := toMiriSize discrW
  let extOpt : Option (BitVec 128) :=
    if tagS then
      match tagSz.signExtend tagBits with
      | .ok integer => some (BitVec.ofInt 128 integer)
      | .error _ => none
    else
      match tagSz.truncate tagBits with
      | .ok trunc => some trunc
      | .error _ => none
  match extOpt with
  | some extended =>
    match discrSz.truncate extended with
    | .ok discrBits => some discrBits
    | .error _ => none
  | none => none

/-- Independent $M_{\text{ref}}$ fieldless-enum admission check using
`Miri.Memory.ScalarInt.tryFromUInt` and `Miri.ABI.Size` operations (never
sharing `Trusted.MirSemantics.enumAdmitted`). -/
noncomputable def refEnumAdmitted (ety : EnumTy) : Bool :=
  !ety.discriminants.isEmpty &&
    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&
    ety.discriminants.all (fun d =>
      Nat.blt d (Nat.pow 2 128) &&
        match Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 d)
            (toMiriSize ety.discrWidth) with
        | .ok (some _) => true
        | .ok none => false
        | .error _ => false) &&
    refNatListPairwiseNe ety.discriminants &&
    match ety.tagRepr with
    | .zeroSized => Nat.beq ety.discriminants.length 1
    | .scalar tagW tagS =>
      ety.discriminants.all (fun d =>
        let dBits := BitVec.ofNat 128 d
        match (toMiriSize tagW).truncate dBits with
        | .ok truncTag =>
          match refMiriTagToDiscrBits tagW tagS ety.discrWidth truncTag with
          | some recovered => recovered == dBits
          | none => false
        | .error _ => false)

/-- `core::cmp::Ordering` as a fieldless enum descriptor: a `#[repr(i8)]`
enum with the signed `i8` tag and discriminant bit patterns `255` (`Less`,
`-1_i8`), `0` (`Equal`), and `1` (`Greater`) (`library/core/src/cmp.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`). $M_{\text{ref}}$
lays out, validates, and reads the discriminant of `MirTy.ordering` through
this descriptor; `id` is never consulted. -/
noncomputable def refOrderingEnumTy : EnumTy := {
  id := 0
  discrWidth := .i8
  discrSigned := true
  tagRepr := .scalar .i8 true
  discriminants := [255, 0, 1]
}

/-- Project enum-like `MirTy` values (`.enum ety` and `core::cmp::Ordering`) to
the fieldless `EnumTy` descriptor governing their layout, projections,
discriminant reads, and shallow validation in $M_{\text{ref}}$. -/
noncomputable def refAsEnumTy? : MirTy → Option EnumTy
  | .enum ety => some ety
  | .ordering => some refOrderingEnumTy
  | _ => none

/-- Independent $M_{\text{ref}}$ check that every unprojected
`Assign(dst, Discriminant(src))` in `rbody` whose `src` has an admitted
enum-like type (`refAsEnumTy? srcTy = some ety`, covering `.enum ety` and
`core::cmp::Ordering`) and whose `dst` is in bounds has destination type
`.int ety.discrWidth ety.discrSigned` (`.int .i8 true` for `Ordering`),
matching `rustc`'s MIR well-typedness invariant for `Rvalue::Discriminant`. -/
noncomputable def refDiscriminantTypesValid (localTys : List MirTy)
    (rbody : RefBody) : Bool :=
  rbody.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .discriminant src =>
          if dst.projection.isEmpty && src.projection.isEmpty then
            match MirSemantics.getElem? localTys src.localId with
            | some srcTy =>
              match refAsEnumTy? srcTy with
              | some ety =>
                match MirSemantics.getElem? localTys dst.localId with
                | some dstTy =>
                  if refEnumAdmitted ety then
                    MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
                  else
                    true
                | none => true
              | none => true
            | none => true
          else
            true
        | _ => true
      | _ => true))

/-- Independent $M_{\text{ref}}$ check that every `.assert cond ...`
terminator in `rbody` whose condition is an unprojected in-bounds local or
constant literal has type `.bool`. -/
noncomputable def refAssertConditionTypesValid (types localTys : List MirTy)
    (rbody : RefBody) : Bool :=
  rbody.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .assert cond _ _ _ _ =>
      match cond with
      | .copy p | .move p =>
        if p.projection.isEmpty then
          match MirSemantics.getElem? localTys p.localId with
          | some condTy => MirTy.beq condTy .bool
          | none => true
        else
          true
      | .constant c =>
        match MirSemantics.getElem? types c.ty with
        | some condTy => MirTy.beq condTy .bool
        | none => false
    | _ => true)

/-- Independent $M_{\text{ref}}$ check that every unprojected
`Assign(dst, Cast(IntToInt, _, castTy))` in `rbody` whose `dst` is in bounds
has destination type `castTy` (`RefRvalue.cast` carries `castTy` as a `TyId`
into `types`; an out-of-bounds `castTy` fails the check), matching `rustc`'s
MIR well-typedness invariant that an assignment's place and rvalue have the
same type. -/
noncomputable def refCastTypesValid (types localTys : List MirTy)
    (rbody : RefBody) : Bool :=
  rbody.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .cast .intToInt _ castTyId =>
          if dst.projection.isEmpty then
            match MirSemantics.getElem? localTys dst.localId with
            | some dstTy =>
              match MirSemantics.getElem? types castTyId with
              | some castTy => MirTy.beq dstTy castTy
              | none => false
            | none => true
          else
            true
        | _ => true
      | _ => true))

/-- Independent $M_{\text{ref}}$ operand-type check for an unprojected in-bounds
local against `expected`. -/
noncomputable def refLocalOperandMatchesTy (localTys : List MirTy)
    (ropnd : RefOperand) (expected : MirTy) : Bool :=
  match ropnd with
  | .copy p | .move p =>
    if p.projection.isEmpty then
      match MirSemantics.getElem? localTys p.localId with
      | some srcTy => MirTy.beq srcTy expected
      | none => true
    else
      true
  | .constant _ => true

/-- Resolve the declared `MirTy` of a `RefOperand` when it is an unprojected
in-bounds local or a `RefProg.types`-indexed constant operand. -/
noncomputable def refOperandTy? (types localTys : List MirTy) :
    RefOperand → Option MirTy
  | .copy p | .move p =>
    if p.projection.isEmpty then MirSemantics.getElem? localTys p.localId
    else none
  | .constant rc => MirSemantics.getElem? types rc.ty

/-- Independent $M_{\text{ref}}$ left-homogeneity check for binary operators,
matching `Miri.MIR.BinOp.leftHomogeneous`. -/
noncomputable def refBinOpLeftHomogeneous : BinOp → Bool
  | .add | .addUnchecked | .sub | .subUnchecked | .mul | .mulUnchecked
  | .div | .rem | .bitXor | .bitAnd | .bitOr | .offset
  | .shl | .shlUnchecked | .shr | .shrUnchecked => true
  | .addWithOverflow | .subWithOverflow | .mulWithOverflow
  | .eq | .ne | .lt | .le | .gt | .ge | .cmp => false

/-- Independent $M_{\text{ref}}$ right-homogeneity check for binary operators,
matching `Miri.MIR.BinOp.rightHomogeneous`. -/
noncomputable def refBinOpRightHomogeneous : BinOp → Bool
  | .add | .addUnchecked | .addWithOverflow | .sub | .subUnchecked
  | .subWithOverflow | .mul | .mulUnchecked | .mulWithOverflow | .div | .rem
  | .bitXor | .bitAnd | .bitOr | .eq | .ne | .lt | .le | .gt | .ge
  | .cmp => true
  | .offset | .shl | .shlUnchecked | .shr | .shrUnchecked => false

/-- Independent $M_{\text{ref}}$ homogeneity check for unary operators,
matching `Miri.MIR.UnOp.homogeneous`. -/
noncomputable def refUnOpHomogeneous : UnOp → Bool
  | .not | .neg => true
  | .ptrMetadata => false

/-- Independent $M_{\text{ref}}$ check mirroring
`Trusted.MirSemantics.assignTypesValid`: every unprojected, in-bounds
`Assign(dst, rv)` operand whose layout hint `Miri` caches directly via
`known` (`Use`, `BinaryOp`, `UnaryOp`) agrees with the
declared local type. -/
noncomputable def refAssignTypesValid (types localTys : List MirTy)
    (rbody : RefBody) : Bool :=
  rbody.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        if dst.projection.isEmpty then
          match MirSemantics.getElem? localTys dst.localId with
          | none => true
          | some dstTy =>
            match rv with
            | .use ropnd => refLocalOperandMatchesTy localTys ropnd dstTy
            | .binaryOp op lhs rhs =>
              let lhsOk : Bool :=
                if refBinOpLeftHomogeneous op then
                  refLocalOperandMatchesTy localTys lhs dstTy
                else
                  true
              let rhsOk : Bool :=
                if refBinOpRightHomogeneous op then
                  match refOperandTy? types localTys lhs with
                  | none =>
                    match lhs with
                    | .constant _ =>
                      match rhs with
                      | .copy q | .move q =>
                        if q.projection.isEmpty then
                          match MirSemantics.getElem? localTys q.localId with
                          | some _ => false
                          | none => true
                        else true
                      | .constant _ => true
                    | _ => true
                  | some lTy => refLocalOperandMatchesTy localTys rhs lTy
                else
                  true
              lhsOk && rhsOk
            | .unaryOp op ropnd =>
              if refUnOpHomogeneous op then
                refLocalOperandMatchesTy localTys ropnd dstTy
              else
                true
            | _ => true
        else
          true
      | _ => true))

/-- Independent $M_{\text{ref}}$ 0-byte ZST enum check (`Variants.Single 0`). -/
noncomputable def refIsZstEnumTy (ety : EnumTy) : Bool :=
  match ety.tagRepr with
  | .zeroSized => refEnumAdmitted ety
  | .scalar _ _ => false

/-- Linear search from `idx` in $M_{\text{ref}}$ for the variant whose declared
discriminant equals `discrBits`. -/
noncomputable def refFindDiscrVariantAux (idx : Nat) (discrBits : BitVec 128) :
    List Nat → Option Nat
  | [] => none
  | d :: ds =>
    if BitVec.ofNat 128 d == discrBits then
      some idx
    else
      refFindDiscrVariantAux (idx + 1) discrBits ds

/-- Resolve `discrBits` to its variant index in `ds` for
`Miri.Interpreter.DiscriminantHooks.variantForDiscriminant`. -/
noncomputable def refFindDiscrVariant? (discrBits : BitVec 128)
    (ds : List Nat) : Option Nat :=
  refFindDiscrVariantAux 0 discrBits ds

/-- Independent $M_{\text{ref}}$ check for the `(T, bool)` result type
`.tuple [.int w s, .bool]` of `BinOp::{Add,Sub,Mul}WithOverflow`. -/
noncomputable def refIsOverflowPairTy : MirTy → Bool
  | .tuple [.int _ _, .bool] => true
  | _ => false

/-- Independent $M_{\text{ref}}$ supported local-type check. -/
noncomputable def refIsSupportedLocalTy : MirTy → Bool
  | .bool | .int _ _ | .char | .ordering | .unit | .never => true
  | .enum ety => refEnumAdmitted ety
  | .tuple fs => refIsOverflowPairTy (.tuple fs)
  | _ => false

/-- Independent $M_{\text{ref}}$ initial live slot for `ty` (inhabited for
0-byte ZSTs `.unit` and admitted `.zeroSized` 1-variant enums). -/
noncomputable def refLiveUninitSlot : MirTy → LocalSlot
  | .unit => .immediate (some .unit)
  | .enum ety =>
    if refIsZstEnumTy ety then .immediate (some (.enumVal ety 0))
    else .immediate none
  | _ => .immediate none

/-! ## Canonical Type-Table Resolution and `Miri.ABI.LayoutData` -/

/-- Auxiliary offset code for built-in scalar/unit types (`bool`, `unit`, and
the 12 integer types) when `ExecutionMachine` queries a compiler-known type
(such as `boolLayout` or an enum tag integer type) not interned in
`RefProg.types`. Indices `>= types.length` never collide with real `RefProg`
`TyId`s. -/
noncomputable def auxTyCode : MirTy → Option Nat
  | .bool => some 0
  | .unit => some 1
  | .int .i8 true => some 2
  | .int .i8 false => some 3
  | .int .i16 true => some 4
  | .int .i16 false => some 5
  | .int .i32 true => some 6
  | .int .i32 false => some 7
  | .int .i64 true => some 8
  | .int .i64 false => some 9
  | .int .i128 true => some 10
  | .int .i128 false => some 11
  | .int .isize true => some 12
  | .int .isize false => some 13
  | _ => none

/-- Inverse of `auxTyCode`. -/
noncomputable def auxTyOfCode : Nat → Option MirTy
  | 0 => some .bool
  | 1 => some .unit
  | 2 => some (.int .i8 true)
  | 3 => some (.int .i8 false)
  | 4 => some (.int .i16 true)
  | 5 => some (.int .i16 false)
  | 6 => some (.int .i32 true)
  | 7 => some (.int .i32 false)
  | 8 => some (.int .i64 true)
  | 9 => some (.int .i64 false)
  | 10 => some (.int .i128 true)
  | 11 => some (.int .i128 false)
  | 12 => some (.int .isize true)
  | 13 => some (.int .isize false)
  | _ => none

/-- Canonical `TyId` for `ty` against `types`: returns the first matching index
in `types` when present, or a collision-free auxiliary index `types.length +
code` for built-in scalar/unit types not interned in `types`. -/
noncomputable def tyIdFor (types : List MirTy) (ty : MirTy) : TyId :=
  match indexOfTy types ty with
  | some idx => idx
  | none =>
    match auxTyCode ty with
    | some code => types.length + code
    | none => types.length + 14

/-- Resolve a canonical `TyId` (either in `types` or an auxiliary index
`>= types.length`) back to its `MirTy`. -/
noncomputable def resolveTy (types : List MirTy) (tyId : TyId) :
    Option MirTy :=
  match MirSemantics.getElem? types tyId with
  | some ty => some ty
  | none =>
    if Nat.ble types.length tyId then
      auxTyOfCode (tyId - types.length)
    else
      none

/-- Normalize an in-bounds `RefProg` `TyId` to its first occurrence in `types`,
so duplicate entries in non-canonical `RefProg.types` tables map to identical
`Miri.MIR.TyId`s for `ScalarOps.assertSameType` and `Rvalue.assertRvalueLayout`
while out-of-bounds `TyId`s remain out of bounds (`>= types.length`). -/
noncomputable def canonicalTyId (types : List MirTy) (tyId : TyId) : TyId :=
  match MirSemantics.getElem? types tyId with
  | some ty => tyIdFor types ty
  | none => tyId

/-- Full unsigned `Miri.ABI.WrappingRange` for `sz : Miri.ABI.Size`. -/
noncomputable def refFullWrappingRangeSize (sz : Miri.ABI.Size) :
    Miri.ABI.WrappingRange :=
  match Miri.ABI.WrappingRange.full sz with
  | .ok r => r
  | .error _ => ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 0⟩

/-- Shared baseline `Miri.ABI.LayoutData` (`Align.ONE`, `Variants.Single 0`,
`.Primitive` fields) parameterized by `backendRepr` and byte `size`. -/
noncomputable def refBaseLayoutData (repr : Miri.ABI.BackendRepr)
    (sz : Miri.ABI.Size) : Miri.ABI.LayoutData := {
  fields := .Primitive
  variants := .Single 0
  backendRepr := repr
  largestNiche := none
  uninhabited := false
  align := Miri.ABI.AbiAlign.new Miri.ABI.Align.ONE
  size := sz
  maxReprAlign := none
  unadjustedAbiAlign := Miri.ABI.Align.ONE
  reprC := false
  randomizationSeed := 0
}

/-- Construct an initialized scalar `Miri.ABI.LayoutData` for `(w, signed)` so
`Miri.Interpreter.readImmediate` accepts primitive integer reads. -/
noncomputable def refScalarLayoutData (w : IntWidth) (s : Bool) :
    Miri.ABI.LayoutData :=
  let sz := toMiriSize w
  refBaseLayoutData
    (.Scalar (.Initialized (value := .Int (toMiriInteger w) s)
      (validRange := refFullWrappingRangeSize sz)))
    sz

/-- Construct the initialized 1-byte `Miri.ABI.LayoutData` for `bool`
(`validRange := [0, 1]`). -/
noncomputable def refBoolLayoutData : Miri.ABI.LayoutData :=
  refBaseLayoutData
    (.Scalar (.Initialized (value := .Int .I8 false)
      (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 1⟩)))
    (Miri.ABI.Size.ofBytes 1)

/-- Construct the initialized 4-byte `Miri.ABI.LayoutData` for `char`
(`validRange := [0, 0x10ffff]`, matching `rustc`'s `char` layout; the
surrogate gap is rejected by validation's `Scalar.toChar`, not by the range).
-/
noncomputable def refCharLayoutData : Miri.ABI.LayoutData :=
  refBaseLayoutData
    (.Scalar (.Initialized (value := .Int .I32 false)
      (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 0x10ffff⟩)))
    (Miri.ABI.Size.ofBytes 4)

/-- Construct the `Miri.ABI.LayoutData` of the overflow pair `(T, bool)` for an
integer `T` of `(w, signed)`: a `BackendRepr.ScalarPair` of the initialized
integer scalar and the initialized `bool` scalar at offset `toMiriSize w`
(`b_offset = a.size(dl).align_to(b_align)` with `bool`'s alignment 1, as in
`LayoutData::scalar_pair` in `compiler/rustc_abi/src/layout/simple.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`), fields
`.Arbitrary #[0, toMiriSize w] #[0, 1]`, and size `2 * w.byteSize` (the
natural-alignment size; every $M_{\text{ref}}$ layout keeps alignment
`Align.ONE`). -/
noncomputable def refOverflowPairLayoutData (w : IntWidth) (s : Bool) :
    Miri.ABI.LayoutData :=
  let sz := toMiriSize w
  {
    refBaseLayoutData
      (.ScalarPair
        (a := .Initialized (value := .Int (toMiriInteger w) s)
          (validRange := refFullWrappingRangeSize sz))
        (b := .Initialized (value := .Int .I8 false)
          (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 1⟩))
        (bOffset := sz))
      (Miri.ABI.Size.ofBytes (2 * sz.bytes)) with
    fields := .Arbitrary (Array.mk [Miri.ABI.Size.ZERO, sz]) (Array.mk [0, 1])
  }

/-- Construct the 0-byte fieldless aggregate `Miri.ABI.LayoutData` for `()` and
1-variant ZST enums (`FieldsShape.Arbitrary #[] #[]`, `Variants.Single 0`). -/
noncomputable def refUnitLayoutData : Miri.ABI.LayoutData := {
  refBaseLayoutData (.Memory (sized := true)) Miri.ABI.Size.ZERO with
  fields := .Arbitrary Array.empty Array.empty
  variants := .Single 0
}

/-- Construct the uninhabited 0-byte `Miri.ABI.LayoutData` for `!`
(`MirTy.never`, `uninhabited := true`, `Variants.Empty`). -/
noncomputable def refNeverLayoutData : Miri.ABI.LayoutData := {
  refBaseLayoutData (.Memory (sized := true)) Miri.ABI.Size.ZERO with
  fields := .Arbitrary Array.empty Array.empty
  variants := .Empty
  uninhabited := true
}

/-- Construct a `Miri.ABI.LayoutData` from a `Miri.ABI.Scalar` tag descriptor
for `Miri.Interpreter.DiscriminantHooks.tagLayout` (`BackendRepr.Scalar
(.Initialized ..)` so `PlaceMachine.readImmediate` reads the projected tag
field). -/
noncomputable def refTagScalarLayout? (tag : Miri.ABI.Scalar) :
    Option Miri.ABI.LayoutData :=
  match tag.primitive with
  | .Int integer signed =>
    some (refBaseLayoutData
      (.Scalar (.Initialized (value := .Int integer signed)
        (validRange := refFullWrappingRangeSize integer.size)))
      integer.size)
  | _ => none

/-- Inhabited 0-field `Miri.ABI.VariantLayout` entry for fieldless enum variants
in `Variants.Multiple`. -/
noncomputable def refInhabitedVariantLayout : Miri.ABI.VariantLayout := {
  size := Miri.ABI.Size.ZERO
  backendRepr := .Memory (sized := true)
  fieldOffsets := Array.empty
  fieldsInMemoryOrder := Array.empty
  largestNiche := none
  uninhabited := false
}

/-- `Miri.ABI.LayoutData` for a fieldless enum `ety : EnumTy`:
- `.zeroSized`: 0-byte fieldless aggregate (`Variants.Single 0`, `isZst = true`,
  `FieldsShape.Arbitrary #[] #[]`).
- `.scalar tagW tagS`: `BackendRepr.Scalar (.Union (.Int tagW tagS))` with
  `fields := .Arbitrary #[Size.ZERO] #[0]` and `variants := .Multiple tag
  .Direct 0 variants`. Using `.Union` on the outer enum makes
  `MemoryOperand.readImmediate` reject raw primitive reads on enum locals
  (`BinaryOp`/`UnaryOp`/`SwitchInt`), while field `0` projects to the
  initialized tag scalar (`refScalarLayoutData tagW tagS`) for both
  `Discriminant.readDiscriminant` and `ValidityVisitor.validatePlace` (whose
  field-0 visit marks `[0, tagSize)` as data bytes so `resetPadding` preserves
  the tag in memory on `Return`). -/
noncomputable def refEnumLayoutData (ety : EnumTy) : Miri.ABI.LayoutData :=
  match ety.tagRepr with
  | .zeroSized => refUnitLayoutData
  | .scalar tagW tagS =>
    let tag : Miri.ABI.Scalar :=
      .Union (value := .Int (toMiriInteger tagW) tagS)
    let variants :=
      Array.mk (ety.discriminants.map (fun _ => refInhabitedVariantLayout))
    {
      refBaseLayoutData (.Scalar tag) (toMiriSize tagW) with
      fields := .Arbitrary (Array.mk [Miri.ABI.Size.ZERO]) (Array.mk [0])
      variants := .Multiple tag .Direct 0 variants
    }

/-- Canonical `Miri.ABI.LayoutData` for any `MirTy` in $M_{\text{ref}}$. -/
noncomputable def refLayoutDataForTy : MirTy → Miri.ABI.LayoutData
  | .int w s => refScalarLayoutData w s
  | .bool => refBoolLayoutData
  | .char => refCharLayoutData
  | .unit => refUnitLayoutData
  | .never => refNeverLayoutData
  | .tuple [.int w s, .bool] => refOverflowPairLayoutData w s
  | ty =>
    match refAsEnumTy? ty with
    | some ety => refEnumLayoutData ety
    | none => refUnitLayoutData

/-- Canonical `Miri.Interpreter.LocalLayout` pairing `tyIdFor types ty` with
`refLayoutDataForTy ty`. -/
noncomputable def refLocalLayoutForTy (types : List MirTy) (ty : MirTy) :
    Miri.Interpreter.LocalLayout :=
  ⟨tyIdFor types ty, refLayoutDataForTy ty⟩

/-! ## Real `Miri.MIR` Syntax Lowering -/

/-- Map `Trusted.MirAst.UnOp` to `Miri.MIR.UnOp`. -/
noncomputable def toMiriUnOp : UnOp → Miri.MIR.UnOp
  | .not => .Not
  | .neg => .Neg
  | .ptrMetadata => .PtrMetadata

/-- Map `Trusted.MirAst.BinOp` to `Miri.MIR.BinOp`. -/
noncomputable def toMiriBinOp : BinOp → Miri.MIR.BinOp
  | .add => .Add
  | .addUnchecked => .AddUnchecked
  | .addWithOverflow => .AddWithOverflow
  | .sub => .Sub
  | .subUnchecked => .SubUnchecked
  | .subWithOverflow => .SubWithOverflow
  | .mul => .Mul
  | .mulUnchecked => .MulUnchecked
  | .mulWithOverflow => .MulWithOverflow
  | .div => .Div
  | .rem => .Rem
  | .bitXor => .BitXor
  | .bitAnd => .BitAnd
  | .bitOr => .BitOr
  | .shl => .Shl
  | .shlUnchecked => .ShlUnchecked
  | .shr => .Shr
  | .shrUnchecked => .ShrUnchecked
  | .eq => .Eq
  | .lt => .Lt
  | .le => .Le
  | .ne => .Ne
  | .ge => .Ge
  | .gt => .Gt
  | .cmp => .Cmp
  | .offset => .Offset

/-- Map `RefPlace` to `Miri.MIR.Place` (preserving `localId` and marking any
non-empty projection with `.Deref` so `OperandMachine.evalPlaceToOp` and
`PlaceDynamic.evalPlace` fail closed with `.unsupported` after checking local
bounds/liveness). -/
noncomputable def toMiriPlace (rp : RefPlace) : Miri.MIR.Place :=
  ⟨rp.localId,
    if rp.projection.isEmpty then Array.empty else Array.mk [.Deref]⟩

/-- Map `RefOperand` to `Miri.MIR.Operand`, carrying the canonicalized
`RefProg.types` index on `.Constant` operands (out-of-bounds indices remain
out of bounds so `constantAt` fails closed). -/
noncomputable def toMiriOperand (types : List MirTy) :
    RefOperand → Miri.MIR.Operand
  | .copy rp => .Copy (toMiriPlace rp)
  | .move rp => .Move (toMiriPlace rp)
  | .constant c =>
    let cv : Miri.MIR.ConstValue :=
      match c.lit with
      | .scalar bits => .Scalar (.Int bits.toNat 16)
      | .zeroSized => .ZeroSized
      | .rodataBytes _ | .rodataRef _ _ _ _ => .Indirect 0 0
    .Constant ⟨⟨0⟩, none, .Val cv (canonicalTyId types c.ty)⟩

/-- Map `RefRvalue` to `Miri.MIR.Rvalue`. `.cast .intToInt` maps to
`.Cast .IntToInt` with the canonicalized target `TyId`. Profile v1 unmodeled
rvalues (including Profile v2-only rvalues and pointer casts) map to the
fail-closed sentinel `.CopyForDeref ⟨0, Array.empty⟩` that
`evalRvalueIntoPlace` rejects immediately with `.invalidProgram` (`.blocked`),
without evaluating unmodeled operands or forcing stack allocations. -/
noncomputable def toMiriRvalue (types : List MirTy) :
    RefRvalue → Miri.MIR.Rvalue
  | .use op => .Use (toMiriOperand types op) .No
  | .binaryOp op lhs rhs =>
    .BinaryOp (toMiriBinOp op) (toMiriOperand types lhs)
      (toMiriOperand types rhs)
  | .unaryOp op opnd =>
    .UnaryOp (toMiriUnOp op) (toMiriOperand types opnd)
  | .cast .intToInt opnd ty =>
    .Cast .IntToInt (toMiriOperand types opnd) (canonicalTyId types ty)
  | .discriminant rp => .Discriminant (toMiriPlace rp)
  | .cast .ptrToPtr _ _ | .cast .intToPtr _ _ | .cast .unsize _ _
  | .cast .boxAsRef _ _
  | .cast .unsupported _ _
  | .useRetag _ | .ref _ _ | .addressOf _ _ | .fakeAddressOf _
  | .aggregateTuple _
  | .aggregateArray _ _ | .repeat_ _ _ _
  | .aggregateRangeTo _ _ | .aggregateRangeFrom _ _
  | .aggregateRange _ _ _ | .aggregateOption _ _ _ | .aggregateStruct _ _
  | .unsupported =>
    .CopyForDeref ⟨0, Array.empty⟩

/-- Map `RefStatementKind` to `Miri.MIR.Statement`. `.unsupported` lowers to
`.Assign ⟨0, #[]⟩ (.CopyForDeref ⟨0, #[]⟩)`, which `evalRvalueIntoPlace`
rejects fail-closed with `.invalidProgram` (or `.invalidLocal 0` on an empty
locals array), never triggering UB or mutating state. -/
noncomputable def toMiriStatement (types : List MirTy) :
    RefStatementKind → Miri.MIR.Statement
  | .nop => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Nop }
  | .storageLive localId =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .StorageLive localId }
  | .storageDead localId =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .StorageDead localId }
  | .assign dst rvalue =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assign (toMiriPlace dst) (toMiriRvalue types rvalue) }
  | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assign ⟨0, Array.empty⟩ (.CopyForDeref ⟨0, Array.empty⟩) }

/-- Map `SysrootNumKind` to its closed opcode `0..5`. -/
noncomputable def sysrootKindCode : SysrootNumKind → Nat
  | .uncheckedAdd => 0
  | .uncheckedSub => 1
  | .uncheckedMul => 2
  | .wrappingAdd => 3
  | .wrappingSub => 4
  | .wrappingMul => 5

/-- Decode opcode `0..5` back to `SysrootNumKind`. -/
noncomputable def sysrootKindOfCode : Nat → Option SysrootNumKind
  | 0 => some .uncheckedAdd
  | 1 => some .uncheckedSub
  | 2 => some .uncheckedMul
  | 3 => some .wrappingAdd
  | 4 => some .wrappingSub
  | 5 => some .wrappingMul
  | _ => none

/-- Map `IntWidth` to its closed code `0..5`. -/
noncomputable def intWidthCode : IntWidth → Nat
  | .i8 => 0
  | .i16 => 1
  | .i32 => 2
  | .i64 => 3
  | .i128 => 4
  | .isize => 5

/-- Decode code `0..5` back to `IntWidth`. -/
noncomputable def intWidthOfCode : Nat → Option IntWidth
  | 0 => some .i8
  | 1 => some .i16
  | 2 => some .i32
  | 3 => some .i64
  | 4 => some .i128
  | 5 => some .isize
  | _ => none

/-- Collision-free natural code `0..71` for a `SysrootNumOp`. -/
noncomputable def sysrootNumOpCode (op : SysrootNumOp) : Nat :=
  sysrootKindCode op.kind * 12 + intWidthCode op.width * 2 +
    (if op.signed then 1 else 0)

/-- Decode a natural code `0..71` back to `SysrootNumOp`. -/
noncomputable def sysrootNumOpOfCode (code : Nat) : Option SysrootNumOp :=
  if Nat.blt code 72 then
    match sysrootKindOfCode (Nat.div code 12),
        intWidthOfCode (Nat.div (Nat.mod code 12) 2) with
    | some k, some w =>
      some { kind := k, width := w, signed := Nat.mod code 2 == 1 }
    | _, _ => none
  else
    none

/-- Underlying `BinOp` for a `SysrootNumKind`. -/
noncomputable def refSysrootNumBinOp : SysrootNumKind → BinOp
  | .uncheckedAdd => .addUnchecked
  | .uncheckedSub => .subUnchecked
  | .uncheckedMul => .mulUnchecked
  | .wrappingAdd => .add
  | .wrappingSub => .sub
  | .wrappingMul => .mul

/-- Canonical `RefBody` for a pinned `core::num` sysroot call against type
table `types`. -/
noncomputable def sysrootNumRefBody (types : List MirTy) (op : SysrootNumOp) :
    RefBody :=
  let tyId := tyIdFor types (.int op.width op.signed)
  let isUnsafe : Bool :=
    match op.kind with
    | .uncheckedAdd | .uncheckedSub | .uncheckedMul => true
    | .wrappingAdd | .wrappingSub | .wrappingMul => false
  {
    identity := "core::num::sysroot"
    isUnsafe := isUnsafe
    argumentCount := 2
    locals := [tyId, tyId, tyId]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp (refSysrootNumBinOp op.kind)
          (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
      cleanup := false
    }]
  }

/-- Base `TyId` above ordinary `types` and `auxTyCode` (`types.length + 0..14`)
reserved for `FnDef` callee operands. -/
noncomputable def fnTyBase (types : List MirTy) : TyId :=
  types.length + 16

/-- Parity-tagged function-item identifier for an intra-crate body `defId`
(`even`). -/
noncomputable def fnTagForCrate (defId : DefId) : Nat :=
  2 * defId

/-- Parity-tagged function-item identifier for a pinned sysroot `core::num` op
(`odd`). -/
noncomputable def fnTagForSysroot (op : SysrootNumOp) : Nat :=
  2 * sysrootNumOpCode op + 1

/-- Map `Trusted.MirAst.UnwindAction` to `Miri.MIR.UnwindAction`. -/
noncomputable def toMiriUnwindAction : UnwindAction → Miri.MIR.UnwindAction
  | .continue_ => .Continue
  | .unreachable => .Unreachable
  | .terminate => .Terminate .InCleanup
  | .cleanup block => .Cleanup block

/-- Wrap a `RefOperand` as a `Miri.MIR.SpannedOperand` for call arguments. -/
noncomputable def toMiriSpannedOperand (types : List MirTy)
    (op : RefOperand) : Miri.MIR.SpannedOperand :=
  ⟨⟨0⟩, toMiriOperand types op⟩

/-- Zero `usize` constant operand used as diagnostic payload for
`Miri.MIR.AssertKind` variants whose inner operands are omitted from
`Trusted.MirAst.AssertKind`. -/
noncomputable def refAssertDummyOperand (types : List MirTy) :
    Miri.MIR.Operand :=
  .Constant ⟨⟨0⟩, none, .Val (.Scalar (.Int 0 8)) (tyIdFor types (.int .isize false))⟩

/-- Map `Trusted.MirAst.AssertKind` to `Miri.MIR.AssertKind`. `.unsupported`
maps to `.NullReferenceConstructed`, which `refPanicLangItem` rejects
fail-closed as `.unsupported`. -/
noncomputable def toMiriAssertKind (types : List MirTy) :
    AssertKind → Miri.MIR.AssertKind
  | .overflow op =>
    let z := refAssertDummyOperand types
    .Overflow (toMiriBinOp op) z z
  | .overflowNeg => .OverflowNeg (refAssertDummyOperand types)
  | .divByZero => .DivisionByZero (refAssertDummyOperand types)
  | .remByZero => .RemainderByZero (refAssertDummyOperand types)
  | .boundsCheck =>
    let z := refAssertDummyOperand types
    .BoundsCheck z z
  | .misalignedPtrDeref =>
    let z := refAssertDummyOperand types
    .MisalignedPointerDereference z z
  | .nullPtrDeref => .NullPointerDereference
  | .unsupported => .NullReferenceConstructed

/-- Map `RefTerminatorKind` to `Miri.MIR.Terminator`. `.assert` lowers to
`Miri.MIR.TerminatorKind.Assert` with `toMiriAssertKind` and
`toMiriUnwindAction`; `.call` and `.sysrootCall` lower to
`Miri.MIR.TerminatorKind.Call`; remaining Profile v1 unmodeled terminators
(`.unwindResume`, `.coreCall`, `.callNe`, `.drop`, and `.unsupported`) map to
`.CoroutineDrop`, which `ControlFlow.evalTerminator` rejects fail-closed with
`.invalidProgram` (`.blocked`). -/
noncomputable def toMiriTerminator (types : List MirTy) :
    RefTerminatorKind → Miri.MIR.Terminator
  | .goto target =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Goto target Array.empty }
  | .return_ =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
  | .unreachable =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Unreachable }
  | .switchInt discr targets =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .SwitchInt (toMiriOperand types discr)
        { cases := Array.mk
            (targets.branches.map (fun b => .Case b.1.toNat b.2))
          otherwise := targets.otherwise } }
  | .call callee args dst target unwind =>
    let funcOp : Miri.MIR.Operand :=
      .Constant ⟨⟨0⟩, none,
        .Val .ZeroSized (fnTyBase types + fnTagForCrate callee)⟩
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Call funcOp (Array.mk (args.map (toMiriSpannedOperand types)))
        (toMiriPlace dst) target (toMiriUnwindAction unwind) .Normal ⟨0⟩ }
  | .sysrootCall op args dst target unwind =>
    let funcOp : Miri.MIR.Operand :=
      .Constant ⟨⟨0⟩, none,
        .Val .ZeroSized (fnTyBase types + fnTagForSysroot op)⟩
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Call funcOp (Array.mk (args.map (toMiriSpannedOperand types)))
        (toMiriPlace dst) target (toMiriUnwindAction unwind) .Normal ⟨0⟩ }
  | .assert cond expected msg target unwind =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assert (toMiriOperand types cond) expected
        (toMiriAssertKind types msg) target (toMiriUnwindAction unwind) }
  | .unwindResume | .coreCall _ _ _ _ _ | .callNe _ _ _ _ _ | .drop _ _ _
  | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .CoroutineDrop }

/-- Lower a `RefBasicBlock` to a `Miri.MIR.BasicBlock`. -/
noncomputable def toMiriBasicBlock (types : List MirTy)
    (rbb : RefBasicBlock) : Miri.MIR.BasicBlock := {
  statements := Array.mk (rbb.statements.map (toMiriStatement types))
  terminator := toMiriTerminator types rbb.terminator
  cleanup := rbb.cleanup
}

/-- Lower a `RefBody` to a real `Miri.MIR.Body` (`Runtime(PostCleanup)` phase)
whose local type table uses canonical `TyId`s. -/
noncomputable def toMiriBody (types : List MirTy) (rbody : RefBody) :
    Miri.MIR.Body := {
  phase := .Runtime .PostCleanup
  argumentCount := rbody.argumentCount
  spreadArgument := none
  locals := Array.mk (rbody.locals.map (canonicalTyId types))
  basicBlocks := Array.mk (rbody.basicBlocks.map (toMiriBasicBlock types))
}

/-! ## Constant Decoding, Value Encoding, and Entry Initialization -/

/-- Construct the runtime `Val` for variant index `v` of an enum-like `MirTy`
(`.enum ety` or `core::cmp::Ordering`: `0` -> `Less`, `1` -> `Equal`, `2` ->
`Greater`). -/
noncomputable def refValOfEnumVariant? : MirTy → Nat → Option Val
  | .enum ety, v => some (.enumVal ety v)
  | .ordering, 0 => some (.ordering .less)
  | .ordering, 1 => some (.ordering .equal)
  | .ordering, 2 => some (.ordering .greater)
  | _, _ => none

/-- Extract the variant index of a runtime `Val` at an enum-like `MirTy`
(`.enum _` or `core::cmp::Ordering`). -/
noncomputable def refEnumVariantOfVal? : MirTy → Val → Option Nat
  | .enum _, .enumVal _ v => some v
  | .ordering, .ordering .less => some 0
  | .ordering, .ordering .equal => some 1
  | .ordering, .ordering .greater => some 2
  | _, _ => none

/-- Reference constant-literal decoder calling
`Miri.Memory.ScalarInt.tryFromUInt` and `Miri.Memory.ScalarInt.tryToBool`
(`vendor/lean-miri/Miri/Memory/ScalarInt.lean`) and `refMiriTagToDiscrBits` /
`refFindDiscrVariant?`, matching `ScalarInt::try_from_uint` and
`ScalarInt::try_to_bool` in `compiler/rustc_middle/src/ty/consts/int.rs` and
`read_discriminant` in `compiler/rustc_const_eval/src/interpret/discriminant.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def evalRefConstLit : MirTy → ConstLit → Except FaultKind Val
  | _, .rodataBytes _ | _, .rodataRef _ _ _ _ => .error .unsupported
  | .int w s, .scalar bits =>
    match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize w) with
    | .ok (some sc) => .ok (.scalar ⟨w, s, sc.data⟩)
    | _ => .error .unsupported
  | .bool, .scalar bits =>
    match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize .i8) with
    | .ok (some sc) =>
      match sc.tryToBool with
      | .ok b => .ok (.bool b)
      | .error (.invalidBool _) => .error .undefined
      | .error _ => .error .unsupported
    | _ => .error .unsupported
  | .unit, .zeroSized => .ok .unit
  | .char, .scalar bits =>
    match Miri.Memory.ScalarInt.tryFromUInt bits (Miri.ABI.Size.ofBytes 4) with
    | .ok (some sc) =>
      match sc.toChar with
      | .ok c => .ok (.char c)
      | .error (.invalidChar _) => .error .undefined
      | .error _ => .error .unsupported
    | _ => .error .unsupported
  | ty, .zeroSized =>
    match refAsEnumTy? ty, refValOfEnumVariant? ty 0 with
    | some ety, some val =>
      if refIsZstEnumTy ety then .ok val else .error .unsupported
    | _, _ => .error .unsupported
  | ty, .scalar bits =>
    match refAsEnumTy? ty with
    | some ety =>
      match ety.tagRepr with
      | .zeroSized => .error .unsupported
      | .scalar tagW tagS =>
        if !refEnumAdmitted ety then
          .error .unsupported
        else
          match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize tagW) with
          | .ok (some sc) =>
            match refMiriTagToDiscrBits tagW tagS ety.discrWidth sc.data with
            | some discrBits =>
              match refFindDiscrVariant? discrBits ety.discriminants with
              | some v =>
                match refValOfEnumVariant? ty v with
                | some val => .ok val
                | none => .error .unsupported
              | none => .error .undefined
            | none => .error .unsupported
          | _ => .error .unsupported
    | none => .error .unsupported

/-- Reference value validity and type check calling
`Miri.Memory.ScalarInt.tryFromUInt`, `Miri.Memory.ScalarInt.ofBool`, and
`Miri.Memory.ScalarInt.{ofChar,toChar}`. -/
noncomputable def checkRefVal (v : Val) (ty : MirTy) : Bool :=
  match v, ty with
  | .scalar sv, .int w s =>
    match Miri.Memory.ScalarInt.tryFromUInt sv.bits (toMiriSize sv.width) with
    | .ok (some _) => IntWidth.beq sv.width w && (sv.signed == s)
    | _ => false
  | .bool b, .bool =>
    match (Miri.Memory.ScalarInt.ofBool b).tryToBool with
    | .ok _ => true
    | .error _ => false
  | .char c, .char =>
    match (Miri.Memory.ScalarInt.ofChar c).toChar with
    | .ok _ => true
    | .error _ => false
  | .ordering _, .ordering => true
  | .unit, .unit => true
  | .enumVal ety v, .enum ety' =>
    (refEnumAdmitted ety && Nat.blt v ety.discriminants.length) &&
      EnumTy.beq ety ety'
  | .tuple [.scalar sv, .bool _], .tuple [.int w s, .bool] =>
    match Miri.Memory.ScalarInt.tryFromUInt sv.bits (toMiriSize sv.width) with
    | .ok (some _) => IntWidth.beq sv.width w && (sv.signed == s)
    | _ => false
  | _, _ => false

/-- Check that argument list `vs` matches parameter types `tys` under
`checkRefVal`. -/
noncomputable def checkRefArgsMatch : List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => checkRefVal v ty && checkRefArgsMatch vs tys
  | _, _ => false

/-- Encode a runtime `Val` at type `ty` into a real
`Miri.Interpreter.Immediate Miri.Memory.Provenance`:
- `.scalar sv` -> `.scalar (.fromScalarInt (miriScalar sv.width sv.bits))`
- `.bool b` -> `.scalar (.fromBool b)`
- `.char c` -> `.scalar (.fromChar c)`
- `.unit` and `.zeroSized` enum-like values -> `.uninit` (canonical ZST
  immediate)
- `.scalar tagW _` enum-like values (`.enumVal ety v` and `.ordering ord` via
  `refAsEnumTy?`) -> `.scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat
  128 disc)))` for `ety.discriminants[v]` (`255`, `0`, or `1` for `Ordering`,
  matching `ScalarOps.finish` on `BinOp::Cmp`)
- overflow pair `.tuple [.scalar sv, .bool b]` -> `.scalarPair (.fromScalarInt
  (miriScalar w sv.bits)) (.fromBool b)`, as `ScalarOps.finish` builds a
  `BinOp::*WithOverflow` result. -/
noncomputable def valToMiriImmediate :
    MirTy → Val → Miri.Interpreter.Immediate Miri.Memory.Provenance
  | .int w _, .scalar sv =>
    .scalar (.fromScalarInt (miriScalar w sv.bits))
  | .bool, .bool b =>
    .scalar (.fromBool b)
  | .char, .char c =>
    .scalar (.fromChar c)
  | .unit, .unit => .uninit
  | .tuple [.int w _, .bool], .tuple [.scalar sv, .bool b] =>
    .scalarPair (.fromScalarInt (miriScalar w sv.bits)) (.fromBool b)
  | ty, val =>
    match refAsEnumTy? ty, refEnumVariantOfVal? ty val with
    | some ety, some v =>
      match ety.tagRepr with
      | .zeroSized => .uninit
      | .scalar tagW _ =>
        match MirSemantics.getElem? ety.discriminants v with
        | some disc =>
          .scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc)))
        | none => .uninit
    | _, _ => .uninit

/-- Encode an $M_{\text{anneal}}$ `MemPlace` into the real
`Miri.Interpreter.MemPlace` of a sized local's stack allocation: a pointer at
byte offset `place.offset` whose provenance is allocation `place.allocId` with
the root tag `BorTag.one` (the tag `PlaceMachine.allocateStackRaw` gives every
stack allocation while borrow tracking is disabled, as in `mkRefMiriState`),
no unsized metadata, and no misalignment. An allocation id of `0`, which no
`MemoryState` produces, encodes as a pointer without provenance. -/
noncomputable def memPlaceToMiri (place : MemPlace) :
    Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  let prov : Option Miri.Memory.Provenance :=
    match Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat place.allocId) with
    | some id => some (.concrete id Miri.Memory.BorTag.one)
    | none => none
  ⟨⟨Miri.ABI.Size.ofBytes (UInt64.ofNat place.offset), prov⟩, .none, none⟩

/-- Encode a `LocalSlot` at type `ty` into a real
`Miri.Interpreter.LocalValue Miri.Memory.Provenance`, one constructor to one
constructor: `.dead` to `.dead`, `.immediate` to `.live (.immediate _)`, and
`.indirect` to `.live (.indirect _)`. -/
noncomputable def slotToMiriLocalValue (ty : MirTy) :
    LocalSlot → Miri.Interpreter.LocalValue Miri.Memory.Provenance
  | .dead => .dead
  | .immediate none => .live (.immediate .uninit)
  | .immediate (some v) => .live (.immediate (valToMiriImmediate ty v))
  | .indirect place => .live (.indirect (memPlaceToMiri place))
  | .partialTuple _ => .live (.immediate .uninit)

/-- Construct a pre-cached `Miri.Interpreter.LocalState Provenance LocalLayout`
for a `(ty, slot)` pair. -/
noncomputable def refLocalStateOfSlot (types : List MirTy) (ty : MirTy)
    (slot : LocalSlot) :
    Miri.Interpreter.LocalState Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout :=
  ⟨slotToMiriLocalValue ty slot, some (refLocalLayoutForTy types ty)⟩

/-- Allocate the caller-owned return buffer for `retTy` inside fresh
`Miri.Memory.MemoryState.empty`, matching `Miri.Interpreter.callMain`
(`vendor/lean-miri/Miri/Interpreter/MainThread.lean`). -/
noncomputable def refInitMemoryAndRetPlace (types : List MirTy)
    (retTy : MirTy) :
    Except FaultKind
      (Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit ×
       Miri.Interpreter.MPlaceTy Miri.Memory.Provenance) :=
  let retLayout := refLocalLayoutForTy types retTy
  let sz := retLayout.layout.size
  let align := retLayout.layout.align.abi
  match Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
      sz align .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) with
  | .error _ => .error .unsupported
  | .ok rawAlloc =>
    let (mem1, reserved) := Miri.Memory.MemoryState.empty.reserveAllocId
    match reserved with
    | .error _ => .error .unsupported
    | .ok allocId =>
      let tree := Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one sz
      let alloc := rawAlloc.withExtra tree
      let mem2 := { mem1 with
        live := mem1.live.push (allocId, ⟨.stack, alloc⟩) }
      let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
        ⟨Miri.ABI.Size.ZERO, some (.concrete allocId Miri.Memory.BorTag.one)⟩
      let mplace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
        ⟨⟨ptr, .none, none⟩, retLayout⟩
      .ok (mem2, mplace)

/-- Decode the entry function's returned `Val` out of the caller-owned return
allocation `retPlace` in `memory` after `Return` pops the root frame and
`ExecutionControl.hooks.copyReturn` writes and validates `_0` into `retPlace`.
An overflow pair reads the integer at offset `0` and the `bool` at offset
`toMiriSize w` (the `ScalarPair`'s `bOffset`), ignoring the padding. -/
noncomputable def refReadReturnVal
    (memory : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (retTy : MirTy)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance) :
    Except FaultKind Val :=
  match retTy with
  | .unit => .ok .unit
  | .int w s =>
    match retPlace.mplace.ptr.provenance with
    | some (.concrete allocId _) =>
      match memory.live.find? (fun entry => entry.1 == allocId) with
      | none => .error .unsupported
      | some (_, localAlloc) =>
        let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (toMiriSize w)
        match localAlloc.allocation.readScalar
            Miri.ABI.RuntimeTargetDataLayout.default.base range false with
        | .ok sc =>
          match sc.tryToScalarInt with
          | .ok (.integer sci) => .ok (.scalar ⟨w, s, sci.data⟩)
          | _ => .error .unsupported
        | .error (.invalidUninitBytes _) => .error .undefined
        | .error _ => .error .unsupported
    | _ => .error .unsupported
  | .bool =>
    match retPlace.mplace.ptr.provenance with
    | some (.concrete allocId _) =>
      match memory.live.find? (fun entry => entry.1 == allocId) with
      | none => .error .unsupported
      | some (_, localAlloc) =>
        let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 1)
        match localAlloc.allocation.readScalar
            Miri.ABI.RuntimeTargetDataLayout.default.base range false with
        | .ok sc =>
          match sc.tryToScalarInt with
          | .ok (.integer sci) =>
            match sci.tryToBool with
            | .ok b => .ok (.bool b)
            | .error (.invalidBool _) => .error .undefined
            | .error _ => .error .unsupported
          | _ => .error .unsupported
        | .error (.invalidUninitBytes _) => .error .undefined
        | .error _ => .error .unsupported
    | _ => .error .unsupported
  | .char =>
    match retPlace.mplace.ptr.provenance with
    | some (.concrete allocId _) =>
      match memory.live.find? (fun entry => entry.1 == allocId) with
      | none => .error .unsupported
      | some (_, localAlloc) =>
        let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 4)
        match localAlloc.allocation.readScalar
            Miri.ABI.RuntimeTargetDataLayout.default.base range false with
        | .ok sc =>
          match sc.tryToScalarInt with
          | .ok (.integer sci) =>
            match sci.toChar with
            | .ok c => .ok (.char c)
            | .error (.invalidChar _) => .error .undefined
            | .error _ => .error .unsupported
          | _ => .error .unsupported
        | .error (.invalidUninitBytes _) => .error .undefined
        | .error _ => .error .unsupported
    | _ => .error .unsupported
  | .tuple [.int w s, .bool] =>
    match retPlace.mplace.ptr.provenance with
    | some (.concrete allocId _) =>
      match memory.live.find? (fun entry => entry.1 == allocId) with
      | none => .error .unsupported
      | some (_, localAlloc) =>
        let intRange := Miri.Memory.allocRange Miri.ABI.Size.ZERO (toMiriSize w)
        let boolRange := Miri.Memory.allocRange (toMiriSize w)
          (Miri.ABI.Size.ofBytes 1)
        match localAlloc.allocation.readScalar
            Miri.ABI.RuntimeTargetDataLayout.default.base intRange false with
        | .ok intSc =>
          match intSc.tryToScalarInt with
          | .ok (.integer intSci) =>
            match localAlloc.allocation.readScalar
                Miri.ABI.RuntimeTargetDataLayout.default.base boolRange
                false with
            | .ok boolSc =>
              match boolSc.tryToScalarInt with
              | .ok (.integer boolSci) =>
                match boolSci.tryToBool with
                | .ok b => .ok (.tuple [.scalar ⟨w, s, intSci.data⟩, .bool b])
                | .error (.invalidBool _) => .error .undefined
                | .error _ => .error .unsupported
              | _ => .error .unsupported
            | .error (.invalidUninitBytes _) => .error .undefined
            | .error _ => .error .unsupported
          | _ => .error .unsupported
        | .error (.invalidUninitBytes _) => .error .undefined
        | .error _ => .error .unsupported
    | _ => .error .unsupported
  | ty =>
    match refAsEnumTy? ty with
    | some ety =>
      match ety.tagRepr with
      | .zeroSized =>
        if refIsZstEnumTy ety then
          match refValOfEnumVariant? ty 0 with
          | some val => .ok val
          | none => .error .unsupported
        else
          .error .unsupported
      | .scalar tagW tagS =>
        if !refEnumAdmitted ety then
          .error .unsupported
        else
          match retPlace.mplace.ptr.provenance with
          | some (.concrete allocId _) =>
            match memory.live.find? (fun entry => entry.1 == allocId) with
            | none => .error .unsupported
            | some (_, localAlloc) =>
              let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO
                (toMiriSize tagW)
              match localAlloc.allocation.readScalar
                  Miri.ABI.RuntimeTargetDataLayout.default.base range false with
              | .ok sc =>
                match sc.tryToScalarInt with
                | .ok (.integer sci) =>
                  match refMiriTagToDiscrBits tagW tagS ety.discrWidth
                      sci.data with
                  | some discrBits =>
                    match refFindDiscrVariant? discrBits ety.discriminants with
                    | some v =>
                      match refValOfEnumVariant? ty v with
                      | some val => .ok val
                      | none => .error .unsupported
                    | none => .error .undefined
                  | none => .error .unsupported
                | _ => .error .unsupported
              | .error (.invalidUninitBytes _) => .error .undefined
              | .error _ => .error .unsupported
          | _ => .error .unsupported
    | none => .error .unsupported

/-- Initialize real `Miri.Interpreter.LocalState` entries at function entry,
pre-populating `layout := some (refLocalLayoutForTy types ty)` on every local,
matching `Miri.Interpreter.CallMachine.pushDone` (`alwaysLiveVarsAndTemps`)
and `compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def initRefLocalsLoop (types : List MirTy) (rbody : RefBody)
    (args : List Val) :
    Nat → List MirTy →
      List (Miri.Interpreter.LocalState Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout)
  | _, [] => []
  | idx, ty :: rest =>
      let slot : LocalSlot :=
        if Nat.beq idx 0 then
          refLiveUninitSlot ty
        else if Nat.ble idx rbody.argumentCount then
          match MirSemantics.getElem? args (idx - 1) with
          | some v => .immediate (some v)
          | none => .dead
        else if refHasStorageAnnotation rbody idx then
          .dead
        else
          refLiveUninitSlot ty
      refLocalStateOfSlot types ty slot ::
        initRefLocalsLoop types rbody args (idx + 1) rest

/-- Construct a real `Miri.Interpreter.LocalState` with explicit layout cache
presence (`cached`). -/
noncomputable def refLocalStateOfSlotWithCache (types : List MirTy) (ty : MirTy)
    (slot : LocalSlot) (cached : Bool) :
    Miri.Interpreter.LocalState Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout := {
  value := slotToMiriLocalValue ty slot
  layout := if cached then some (refLocalLayoutForTy types ty) else none
}

/-- Construct a real `Miri.Interpreter.Frame` executing `defId`/`rbody` at
`(blockIdx, stmtIdx)` with `locals` and caller-owned return destination
`retPlace` (`returnContinuation := .stop false`). -/
noncomputable def mkRefMiriFrame (types : List MirTy) (defId : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (locals : List (Miri.Interpreter.LocalState Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout))
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance) :
    Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra := {
  body := toMiriBody types rbody
  bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex defId
  functionInstance := { kind := .Item defId, args := Array.empty }
  extra := {
    borrowTracker := none
    catchUnwind := none
    userRelevance := 255
    dataRace := none
  }
  returnContinuation := .stop false
  returnPlace := .memory retPlace
  localsIdentity := Miri.Interpreter.LocalsIdentity.ofAllocationToken 0
  locals := Array.mk locals
  vaList := Array.empty
  trackCallerArg := none
  location := .mir ⟨blockIdx, stmtIdx⟩
}

/-- Construct a non-root callee `Miri.Interpreter.Frame` with caller return
destination `callerIdx`/`dstLocalId` and continuation
`.goto retTarget? .Unreachable`. -/
noncomputable def mkRefMiriCallFrame (types : List MirTy) (fnTag : DefId)
    (rbody : RefBody) (blockIdx : BasicBlockId) (stmtIdx : Nat)
    (locals : List (Miri.Interpreter.LocalState Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout))
    (callerIdx : Nat) (dstLocalId : LocalId) (dstTy : MirTy)
    (retTarget? : Option BasicBlockId) :
    Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra := {
  body := toMiriBody types rbody
  bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex fnTag
  functionInstance := { kind := .Item fnTag, args := Array.empty }
  extra := {
    borrowTracker := none
    catchUnwind := none
    userRelevance := 255
    dataRace := none
  }
  returnContinuation := .goto retTarget? .Unreachable
  returnPlace := .frameLocal callerIdx dstLocalId none
    (refLocalLayoutForTy types dstTy)
    (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)
  localsIdentity := Miri.Interpreter.LocalsIdentity.ofAllocationToken 0
  locals := Array.mk locals
  vaList := Array.empty
  trackCallerArg := none
  location := .mir ⟨blockIdx, stmtIdx⟩
}

/-- Construct a `Miri.Interpreter.MachineHooks.State Unit RefUser` holding an
arbitrary bottom-to-top frame stack `frames` and cached
`topUserRelevantFrame`. -/
noncomputable def mkRefMiriStackState
    (frames : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra))
    (topRel? : Option Nat)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (callerMem : CallerMemory) :
    Miri.Interpreter.MachineHooks.State Unit RefUser :=
  let initThreads := Miri.Concurrency.ThreadManager.initial true
  {
    stack := ⟨frames⟩
    machine := {
      memory := mem
      borrowTracker := none
      dataRace := none
      threads := {
        initThreads with
        threads := initThreads.threads.mapIdx fun index thread =>
          if index == initThreads.activeThread.toNat then
            { thread with topUserRelevantFrame := topRel? }
          else
            thread
      }
      raceAllocations := Array.empty
      allocationSpans := Array.empty
      user := { control := ctrl, callerMem := callerMem }
      pendingMoveDeinit := false
    }
  }

/-- Construct a real `Miri.Interpreter.MachineHooks.State Unit RefUser` holding
a single active frame, return-place memory `mem`, terminator control `ctrl`,
and `callerMem`. -/
noncomputable def mkRefMiriState
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ctrl : Miri.Interpreter.TerminatorMachine.Control Unit)
    (callerMem : CallerMemory) :
    Miri.Interpreter.MachineHooks.State Unit RefUser :=
  mkRefMiriStackState (Array.mk [frame]) none mem ctrl callerMem

/-- Independent $M_{\text{ref}}$ membership check on `List Nat`. -/
noncomputable def refNatListContains (x : Nat) : List Nat → Bool
  | [] => false
  | y :: rest => Nat.beq x y || refNatListContains x rest

/-- Collect moved places from a `List RefOperand`. -/
noncomputable def refMovePlaceList : List RefOperand → List RefPlace
  | [] => []
  | .move p :: rest => p :: refMovePlaceList rest
  | _ :: rest => refMovePlaceList rest

/-- Independent $M_{\text{ref}}$ check that moved places and `dst` have empty
projections and distinct local IDs. -/
noncomputable def refPlacesDisjointAux (seen : List LocalId) :
    List RefPlace → Bool
  | [] => true
  | p :: rest =>
    if !p.projection.isEmpty || refNatListContains p.localId seen then
      false
    else
      refPlacesDisjointAux (p.localId :: seen) rest

/-- Independent $M_{\text{ref}}$ local-disjointness check for call move
arguments and return destination. -/
noncomputable def refMoveDefinitelyDisjoint (args : List RefOperand)
    (dst : RefPlace) : Bool :=
  refPlacesDisjointAux [] (refMovePlaceList args ++ [dst])

/-- Independent $M_{\text{ref}}$ type and constant-literal check for call
arguments against decoded callee parameter types. -/
noncomputable def refCallArgsMatchBody (types localTys : List MirTy) :
    List RefOperand → List MirTy → Bool
  | [], [] => true
  | opnd :: restArgs, paramTy :: restParams =>
    let argOk : Bool :=
      match opnd with
      | .copy place | .move place =>
        if !place.projection.isEmpty then
          false
        else
          match MirSemantics.getElem? localTys place.localId with
          | some argTy => MirTy.beq argTy paramTy
          | none => false
      | .constant c =>
        match MirSemantics.getElem? types c.ty with
        | none => false
        | some cTy =>
          MirTy.beq cTy paramTy &&
            match evalRefConstLit cTy c.lit with
            | .ok _ => true
            | .error _ => false
    argOk && refCallArgsMatchBody types localTys restArgs restParams
  | _, _ => false

/-- Independent $M_{\text{ref}}$ call-site admission check for one call site. -/
noncomputable def refCallTargetAdmitted (types localTys : List MirTy)
    (rbody : RefBody) (bb : RefBasicBlock) (calleeArgCount : Nat)
    (calleeLocalTys : List MirTy) (args : List RefOperand) (dst : RefPlace)
    (target : Option BasicBlockId) (unwind : UnwindAction) : Bool :=
  !bb.cleanup &&
    (match unwind with | .cleanup _ => false | _ => true) &&
    (match target with
     | none => true
     | some tgt => Nat.blt tgt rbody.basicBlocks.length) &&
    dst.projection.isEmpty &&
    refMoveDefinitelyDisjoint args dst &&
    Nat.beq args.length calleeArgCount &&
    Nat.blt calleeArgCount calleeLocalTys.length &&
    (match MirSemantics.getElem? localTys dst.localId,
        MirSemantics.getElem? calleeLocalTys 0 with
     | some dstTy, some retTy =>
       refIsSupportedLocalTy dstTy && MirTy.beq dstTy retTy
     | _, _ => false) &&
    refCallArgsMatchBody types localTys args
      ((calleeLocalTys.drop 1).take calleeArgCount)

/-- Independent $M_{\text{ref}}$ admission check for all call terminators in
`rbody`. Like `Trusted.MirSemantics.callsAdmitted`, it rejects `.call` targets
whose `isUnsafe` flag is set (`isUnsafe` is otherwise inert in
$M_{\text{ref}}$), so both models refuse the same programs at entry. -/
noncomputable def refCallsAdmitted (rp : RefProg) (localTys : List MirTy)
    (rbody : RefBody) : Bool :=
  rbody.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .call callee args dst target unwind =>
      match MirSemantics.getElem? rp.bodies callee with
      | none => false
      | some calleeRbody =>
        match decodeLocalTys rp.types calleeRbody.locals with
        | none => false
        | some calleeLocalTys =>
          !calleeRbody.isUnsafe &&
            refCallTargetAdmitted rp.types localTys rbody bb
              calleeRbody.argumentCount calleeLocalTys args dst target unwind
    | .sysrootCall op args dst target unwind =>
      let sysTy := .int op.width op.signed
      refCallTargetAdmitted rp.types localTys rbody bb 2 [sysTy, sysTy, sysTy]
        args dst target unwind
    | _ => true)

/-- Independent $M_{\text{ref}}$ check for whether `rbody` contains any call
terminator. -/
noncomputable def refBodyHasAnyCall (rbody : RefBody) : Bool :=
  rbody.basicBlocks.any (fun bb =>
    match bb.terminator with
    | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
    | _ => false)

/-- Independent $M_{\text{ref}}$ single-body static admission predicate. -/
noncomputable def refSingleBodyStaticAdmitted (rp : RefProg) (rbody : RefBody) :
    Bool :=
  match decodeLocalTys rp.types rbody.locals with
  | none => false
  | some localTys =>
    Nat.beq rp.pointerWidthBits 64 &&
      Nat.beq rp.mirProfileVersion 1 &&
      !rbody.identity.toByteArray.data.toList.isEmpty &&
      !rbody.basicBlocks.isEmpty &&
      Nat.blt rbody.argumentCount localTys.length &&
      refStorageAnnotationsInBounds rbody &&
      refDiscriminantTypesValid localTys rbody &&
      refCastTypesValid rp.types localTys rbody &&
      refAssertConditionTypesValid rp.types localTys rbody &&
      localTys.all refIsSupportedLocalTy &&
      refCallsAdmitted rp localTys rbody

/-- Independent $M_{\text{ref}}$ call-body static admission predicate. -/
noncomputable def refCallBodyStaticAdmitted (rp : RefProg) (rbody : RefBody) :
    Bool :=
  refSingleBodyStaticAdmitted rp rbody &&
    match decodeLocalTys rp.types rbody.locals with
    | none => false
    | some localTys => refAssignTypesValid rp.types localTys rbody

/-- Whenever `rbody` contains any call terminator, require `refAssignTypesValid`
on `rbody` and require every body in `rp.bodies` to satisfy
`refCallBodyStaticAdmitted rp`. -/
noncomputable def refAllCallBodiesStaticAdmitted (rp : RefProg)
    (rbody : RefBody) : Bool :=
  if refBodyHasAnyCall rbody then
    match decodeLocalTys rp.types rbody.locals with
    | none => false
    | some localTys =>
      refAssignTypesValid rp.types localTys rbody &&
        rp.bodies.all (refCallBodyStaticAdmitted rp)
  else
    true

/-- Entry initialization of $M_{\text{ref}}$ (`initRefState rp q maxSteps`):
validates 64-bit target layout, MIR profile version 1, empty `callerMem`,
entry body existence, non-empty basic blocks, `argumentCount < locals.length`,
in-bounds storage annotations, well-typed `Discriminant` and `Cast`
destinations, supported local types, admitted calls, and matching arguments;
allocates the caller-owned return buffer in `MemoryState.empty`; and initializes
a single-frame `Miri.Interpreter.MachineHooks.State` ready for
`ExecutionMachine.step`. -/
noncomputable def initRefState (rp : RefProg) (q : Query)
    (maxSteps : Nat) : Except FaultKind RefState :=
  if !Nat.beq rp.pointerWidthBits 64 || !Nat.beq rp.mirProfileVersion 1 then
    .error .unsupported
  else if !q.callerMem.allocations.isEmpty then
    .error .unsupported
  else
    match MirSemantics.getElem? rp.bodies rp.entryDefId with
    | none => .error .unsupported
    | some rbody =>
      match decodeLocalTys rp.types rbody.locals with
      | none => .error .unsupported
      | some localTys =>
        if rbody.basicBlocks.isEmpty then
          .error .unsupported
        else if !Nat.blt rbody.argumentCount localTys.length then
          .error .unsupported
        else if !refStorageAnnotationsInBounds rbody then
          .error .unsupported
        else if !refDiscriminantTypesValid localTys rbody then
          .error .unsupported
        else if !refCastTypesValid rp.types localTys rbody then
          .error .unsupported
        else if !refAssertConditionTypesValid rp.types localTys rbody then
          .error .unsupported
        else if !localTys.all refIsSupportedLocalTy then
          .error .unsupported
        else if !refCallsAdmitted rp localTys rbody then
          .error .unsupported
        else if !refAllCallBodiesStaticAdmitted rp rbody then
          .error .unsupported
        else
          let paramTys := (localTys.drop 1).take rbody.argumentCount
          if !checkRefArgsMatch q.args paramTys then
            .error .unsupported
          else
            match MirSemantics.getElem? localTys 0 with
            | none => .error .unsupported
            | some retTy =>
              match refInitMemoryAndRetPlace rp.types retTy with
              | .error k => .error k
              | .ok (mem, retPlace) =>
                let rlocals := initRefLocalsLoop rp.types rbody q.args 0 localTys
                let frame := mkRefMiriFrame rp.types rp.entryDefId rbody 0 0
                  rlocals retPlace
                .ok {
                  miri := mkRefMiriState frame mem refInitControl q.callerMem
                  retTy := retTy
                  retPlace := retPlace
                  stepsExecuted := 0
                  maxSteps := maxSteps
                }

end Trusted.Correspondence
