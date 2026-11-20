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
import Miri.Interpreter.LocalAccess
import Miri.Interpreter.Place
import Miri.Interpreter.Rvalue
import Miri.Interpreter.Discriminant
import Miri.Interpreter.Step
import Miri.Interpreter.ControlFlow
import Trusted.MirAst
import Trusted.MirModel
import Trusted.Correspondence.Codec

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Reference State, Operators, and Init (`Trusted.Correspondence.State`)

Defines `RefState`, `RefOutcome`, `Miri.Interpreter` scalar/enum adapters, and
entry initialization (`initRefState`). Imports only `Trusted.MirAst` and
`Trusted.MirModel`, never `Trusted.MirSemantics`.
-/

/-! ## Reference Machine State and Step Engine ($M_{\text{ref}}$) -/

/-- Reference local slot (`Miri.Interpreter.LocalState` in
`Miri/Interpreter/Operand.lean`, line 32), pairing the runtime
`slot : LocalSlot` with `cachedLayout : Option MirTy` pre-populated by
`initRefState`. -/
structure RefLocalState where
  slot : LocalSlot
  cachedLayout : Option MirTy

/-- Reference call-stack frame (`Miri.Interpreter.Frame` in
`Miri/Interpreter/Stack.lean`).

`isCallerSentinel` distinguishes the two kinds of frames that the reference
stack holds: `false` marks an active frame that executes `defId`'s body, and
`true` marks the suspended caller sentinel frame (`callerSentinelFrame`) beneath
the entry frame that owns its return destination slot `_0`. `evalRefStep`
executes only the top frame and requires `[sentinel, rframe]` with
`sentinel.isCallerSentinel = true` and `rframe.isCallerSentinel = false`. -/
structure RefFrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List RefLocalState
  isCallerSentinel : Bool := false

/-- Reference machine state for $M_{\text{ref}}$, which executes
`Miri.Interpreter.Step.step` over
`StepState (Option Val) LocalLayout Unit RefStepMachine` using Anneal-authored
hooks (`refStepHooksFor` and friends) rather than wrapping
`Miri.Interpreter.MachineHooks.State` (`Miri/Interpreter/MachineHooks.lean`) or
`Miri.Interpreter.ExecutionMachine.Limits`. Tracks `stepsExecuted : Nat` and
`maxSteps : Nat` explicitly so `RefWellFormed` and `RefBehavior` quantify over
the step budget; `Miri.Interpreter.ExecutionMachine.step` is wired separately
by `MiriMoveDeinitWiringClaim` (tying `ExecutionMachine.step` to
`ExecutionMachine.stepHooks`, not `refStepHooksFor`). -/
structure RefState where
  frames : List RefFrameState
  callerMem : CallerMemory
  stepsExecuted : Nat := 0
  maxSteps : Nat := 0

/-- Five-way adapter step outcome translating `Miri.Interpreter.Step.step`'s
`StepResult (StepState (Option Val) LocalLayout Unit RefStepMachine) Bool`
(i.e. `(StepState ..., Except StepError Bool)` in `Miri/Interpreter/Step.lean`,
under Anneal-authored hooks `refStepHooksFor` rather than
`Miri.Interpreter.ExecutionMachine.step`) together with explicit step-budget
exhaustion (`exhaustedStepLimit`). -/
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

/-- Convert the `StepResult` of executing the top frame's statement or
terminator into a `RefOutcome`.

Statement and terminator evaluators rebuild only the top frame
(`frames := [rframe']`). On `.step`, this function restores the caller
`sentinel` beneath that frame and increments `stepsExecuted`. -/
noncomputable def stepResultToRefOutcome (sentinel : RefFrameState)
    (stepsExecuted maxSteps : Nat) :
    StepResult RefState TerminalOut → RefOutcome
  | .step rs' =>
    .running {
      rs' with
      frames := sentinel :: rs'.frames
      stepsExecuted := stepsExecuted + 1
      maxSteps := maxSteps
    }
  | .done out => .returned out
  | .fault k => faultToRefOutcome k

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

/-- Independent $M_{\text{ref}}$ supported local-type check. -/
noncomputable def refIsSupportedLocalTy : MirTy → Bool
  | .bool | .int _ _ | .unit | .never => true
  | .enum ety => refEnumAdmitted ety
  | _ => false

/-- Independent $M_{\text{ref}}$ primitive-readable type check. -/
noncomputable def refIsPrimitiveReadableTy : MirTy → Bool
  | .bool | .int _ _ => true
  | _ => false

/-- Independent $M_{\text{ref}}$ initial live slot for `ty` (inhabited for
0-byte ZSTs `.unit` and admitted `.zeroSized` 1-variant enums). -/
noncomputable def refLiveUninitSlot : MirTy → LocalSlot
  | .unit => .live (some .unit)
  | .enum ety =>
    if refIsZstEnumTy ety then .live (some (.enumVal ety 0)) else .live none
  | _ => .live none

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

/-- Construct a scalar `Miri.ABI.LayoutData` for `(w, signed)`. -/
noncomputable def refScalarLayoutData (w : IntWidth) (s : Bool) :
    Miri.ABI.LayoutData :=
  refBaseLayoutData (.Scalar (.Union (value := .Int (toMiriInteger w) s)))
    (toMiriSize w)

/-- Construct a `Miri.ABI.LayoutData` from a `Miri.ABI.Scalar` tag descriptor
for `Miri.Interpreter.DiscriminantHooks.tagLayout`. -/
noncomputable def refTagScalarLayout? (tag : Miri.ABI.Scalar) :
    Option Miri.ABI.LayoutData :=
  match tag.primitive with
  | .Int integer _ => some (refBaseLayoutData (.Scalar tag) integer.size)
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
`Variants.Single 0` (`Size.ZERO`, `isZst = true`) for `.zeroSized`, and
`Variants.Multiple tag .Direct 0 variants` for `.scalar tagW tagS`.

For `.scalar tagW tagS`, `tag` uses `Miri.ABI.Scalar.Union` so
`Miri.ABI.Scalar.validRange` yields the full width range
(`WrappingRange.full`) without computing a wrapping-range hull over possibly
non-contiguous discriminants. Exact tag validity is still enforced by
`Miri.Interpreter.Discriminant.readDiscriminant` via `variantForDiscriminant`
(raising `InvalidTag(no declared discriminant)` UB for undeclared bit
patterns), and uninitialized enum slots are rejected earlier as UB by
`readImmediate` because `encodeRefEnumTagOp` maps `none` to `.uninit`. -/
noncomputable def refEnumLayoutData (ety : EnumTy) : Miri.ABI.LayoutData :=
  match ety.tagRepr with
  | .zeroSized =>
    refBaseLayoutData (.Memory (sized := true)) Miri.ABI.Size.ZERO
  | .scalar tagW tagS =>
    let tag : Miri.ABI.Scalar :=
      .Union (value := .Int (toMiriInteger tagW) tagS)
    let variants :=
      Array.mk (ety.discriminants.map (fun _ => refInhabitedVariantLayout))
    {
      refScalarLayoutData tagW tagS with
      variants := .Multiple tag .Direct 0 variants
    }

/-- Single `Miri.Interpreter.DiscriminantHooks` adapter for a fieldless enum
`ety : EnumTy` over state `S`, shared by both `evalRefConstLit` (`S = Unit`)
and `evalRefMiriRvalue` (`S = List RefLocalState`) to drive
`Miri.Interpreter.Discriminant.readDiscriminant` and
`Miri.Interpreter.Discriminant.discriminantForVariant`.

Note on `TyId`s `0` and `1`: this closed single-enum hook record never indexes
`RefProg.types`; `0` and `1` are private local sentinels identifying `ety` and
its discriminant integer type inside a single `Discriminant` call. `tagLayout`
and `projectRead` also stamp `0` on the tag scalar layout, which is harmless
because `Miri.Interpreter.Discriminant` never reads the tag layout's `TyId`. -/
noncomputable def refDiscriminantHooks (S : Type) (ety : EnumTy) :
    Miri.Interpreter.DiscriminantHooks Miri.Memory.Provenance S Unit Unit := {
  runtimeTarget := Miri.ABI.RuntimeTargetDataLayout.default
  discriminantLayout := fun _ ty s =>
    if Nat.beq ty 0 then
      .ok ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩ s
    else
      .error (.invalidProgram "unexpected enum TyId in discriminantLayout") s
  tagLayout := fun _ tag s =>
    match refTagScalarLayout? tag with
    | some l => .ok ⟨0, l⟩ s
    | none => .error (.invalidProgram "non-integer enum tag") s
  discriminantValue := fun _ ty variant s =>
    if Nat.beq ty 0 then
      match MirSemantics.getElem? ety.discriminants variant with
      | some disc => .ok (some (1, BitVec.ofNat 128 disc)) s
      | none => .error (.invalidProgram "enum variant out of bounds") s
    else
      .error (.invalidProgram "unexpected enum TyId in discriminantValue") s
  variantForDiscriminant := fun _ ty discrBits s =>
    if Nat.beq ty 0 then
      .ok (refFindDiscrVariant? discrBits ety.discriminants) s
    else
      .error (.invalidProgram
        "unexpected enum TyId in variantForDiscriminant") s
  adtVariantCount := fun _ _ s => .ok ety.discriminants.length s
  projectRead := fun _ op field s =>
    if Nat.beq field 0 then
      match op.layout.layout.variants with
      | .Multiple tag _ _ _ =>
        match refTagScalarLayout? tag with
        | some tl => .ok ⟨op.op, ⟨0, tl⟩⟩ s
        | none => .error (.invalidProgram "non-integer enum tag") s
      | _ => .error (.invalidProgram "projectRead on non-Multiple enum") s
    else
      .error (.invalidProgram "non-zero tag field on fieldless enum") s
  readImmediate := fun _ op s =>
    match op.op with
    | .immediate .uninit =>
      .error (.undefinedBehavior "InvalidUninitBytes(None)") s
    | .immediate imm => .ok ⟨imm, op.layout⟩ s
    | .indirect _ => .error (.unsupported "memory enum place unsupported") s
  destLayout := fun _ =>
    ⟨1, refScalarLayoutData ety.discrWidth ety.discrSigned⟩
  projectWrite := fun _ _ _ s =>
    .error (.unsupported "SetDiscriminant unsupported") s
  writeScalar := fun _ _ _ s =>
    .error (.unsupported "SetDiscriminant unsupported") s
  toOp := fun _ _ s =>
    .error (.unsupported "SetDiscriminant unsupported") s
  scalarMayBeNull := fun _ _ s => .ok true s
}

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
  | .offset => .Offset

/-- Reference constant-literal decoder calling
`Miri.Memory.ScalarInt.tryFromUInt` and `Miri.Memory.ScalarInt.tryToBool`
(`vendor/lean-miri/Miri/Memory/ScalarInt.lean`), matching
`ScalarInt::try_from_uint` and `ScalarInt::try_to_bool` in
`compiler/rustc_middle/src/ty/consts/int.rs` and `Scalar::to_bool` in
`compiler/rustc_middle/src/mir/interpret/value.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, overflow) = Self::truncate_from_uint(i, size);
>     if overflow { None } else { Some(r) }
> }"
>
> "pub fn try_to_bool(self) -> Result<bool, ()> {
>     match self.to_u8() {
>         0 => Ok(false),
>         1 => Ok(true),
>         _ => Err(()),
>     }
> }"
> (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "pub fn to_bool(self) -> InterpResult<'tcx, bool> {
>     let val = self.to_u8()?;
>     match val {
>         0 => interp_ok(false),
>         1 => interp_ok(true),
>         _ => throw_ub!(InvalidBool(val)),
>     }
> }"
> (`compiler/rustc_middle/src/mir/interpret/value.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefConstLit : MirTy → ConstLit → Except FaultKind Val
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
  | .enum ety, .zeroSized =>
    if refIsZstEnumTy ety then .ok (.enumVal ety 0) else .error .unsupported
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => .error .unsupported
    | .scalar tagW _ =>
      if !refEnumAdmitted ety then
        .error .unsupported
      else
        match Miri.Memory.ScalarInt.tryFromUInt bits (toMiriSize tagW) with
        | .ok (some sc) =>
          let op : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
            ⟨.immediate (.scalar (.fromScalarInt sc)),
              ⟨0, refEnumLayoutData ety⟩⟩
          match Miri.Interpreter.Discriminant.readDiscriminant
              (refDiscriminantHooks Unit ety) () op () with
          | .ok v _ => .ok (.enumVal ety v)
          | .error (.undefinedBehavior _) _ => .error .undefined
          | .error _ _ => .error .unsupported
        | _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Reference unary operator evaluator over `Miri.MIR.UnOp` calling
`Miri.Interpreter.IntegerOps.unary`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`), matching `unary_op` in
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn unary_op(
>     &self,
>     un_op: mir::UnOp,
>     val: &ImmTy<'tcx, M::Provenance>,
> ) -> InterpResult<'tcx, ImmTy<'tcx, M::Provenance>>"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefMiriUnOp (op : Miri.MIR.UnOp) (v : Val) :
    Except FaultKind Val :=
  match op, v with
  | .Not, .bool b => .ok (.bool (!b))
  | _, .scalar sv =>
    match Miri.Interpreter.IntegerOps.unary op (miriIntValue sv) with
    | .ok sc => .ok (.scalar ⟨sv.width, sv.signed, sc.data⟩)
    | .error (.undefinedBehavior _) => .error .undefined
    | .error _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Reference binary operator evaluator over `Miri.MIR.BinOp` calling
`Miri.Interpreter.IntegerOps.binary` and
`Miri.Interpreter.IntegerOps.binaryBool`
(`vendor/lean-miri/Miri/Interpreter/IntegerOps.lean`), matching `binary_op` in
`compiler/rustc_const_eval/src/interpret/operator.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn binary_op(
>     &self,
>     bin_op: mir::BinOp,
>     left: &ImmTy<'tcx, M::Provenance>,
>     right: &ImmTy<'tcx, M::Provenance>,
> ) -> InterpResult<'tcx, ImmTy<'tcx, M::Provenance>>"
> (`compiler/rustc_const_eval/src/interpret/operator.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefMiriBinOp (op : Miri.MIR.BinOp) (lhs rhs : Val) :
    Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    match op with
    | .AddWithOverflow | .SubWithOverflow | .MulWithOverflow | .Offset =>
      .error .unsupported
    | _ =>
      match Miri.Interpreter.IntegerOps.binary op
          (miriIntValue l) (miriIntValue r) with
      | .ok (.scalar sc) => .ok (.scalar ⟨l.width, l.signed, sc.data⟩)
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported
  | .bool l, .bool r =>
    match op with
    | .AddWithOverflow | .SubWithOverflow | .MulWithOverflow | .Offset =>
      .error .unsupported
    | _ =>
      match Miri.Interpreter.IntegerOps.binaryBool op l r with
      | .ok (.boolean b) => .ok (.bool b)
      | .ok _ => .error .unsupported
      | .error (.undefinedBehavior _) => .error .undefined
      | .error _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Reference scalar/boolean/unit/enum value validity and type check calling
`Miri.Memory.ScalarInt.tryFromUInt` and `Miri.Memory.ScalarInt.ofBool`. -/
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
  | .unit, .unit => true
  | .enumVal ety v, .enum ety' =>
    (refEnumAdmitted ety && Nat.blt v ety.discriminants.length) &&
      EnumTy.beq ety ety'
  | _, _ => false

/-- Check that argument list `vs` matches parameter types `tys` under
`checkRefVal`. -/
noncomputable def checkRefArgsMatch : List Val → List MirTy → Bool
  | [], [] => true
  | v :: vs, ty :: tys => checkRefVal v ty && checkRefArgsMatch vs tys
  | _, _ => false

/-- Caller sentinel frame beneath the entry function's frame.

$M_{\text{ref}}$ represents the caller of the entry function as an explicit
frame that owns the entry function's return place. In `lean-miri`,
`Miri.Interpreter.callMain`
(`vendor/lean-miri/Miri/Interpreter/MainThread.lean`) allocates the return
place `retPlace` before it calls the entry function, so that place outlives the
entry frame. The sentinel models this caller-owned place as a single live
destination slot (`_0`) of the entry function's return type `retTy`.

The sentinel never executes a statement and is marked with
`isCallerSentinel := true`. `initRefState` places it beneath the entry frame,
and `evalRefStep` requires it and preserves it on every running step, so the
reference stack has one fixed shape. Returning from the entry frame ends the
execution with `.returned` (`evalRefTerminator`) instead of resuming the
sentinel. Its `defId`, `blockIdx`, and `stmtIdx` are unused. -/
noncomputable def callerSentinelFrame (retTy : MirTy) : RefFrameState := {
  defId := 0
  blockIdx := 0
  stmtIdx := 0
  locals := [⟨refLiveUninitSlot retTy, some retTy⟩]
  isCallerSentinel := true
}

/-- Initialize `RefLocalState` slots at function entry, pre-populating
`cachedLayout := some ty` on every slot, matching
`Miri.Interpreter.CallMachine.pushDone` (`alwaysLiveVarsAndTemps`) and
`compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "self.storage_live(mir::RETURN_PLACE)?;
>
> let body = self.body();
> let always_live = always_storage_live_locals(body);
> for local in body.vars_and_temps_iter() {
>     if always_live.contains(local) {
>         self.storage_live(local)?;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def initRefLocalsLoop (rbody : RefBody) (args : List Val) :
    Nat → List MirTy → List RefLocalState
  | _, [] => []
  | idx, ty :: rest =>
      let slot : LocalSlot :=
        if Nat.beq idx 0 then
          refLiveUninitSlot ty
        else if Nat.ble idx rbody.argumentCount then
          match MirSemantics.getElem? args (idx - 1) with
          | some v => .live (some v)
          | none => .dead
        else if refHasStorageAnnotation rbody idx then
          .dead
        else
          refLiveUninitSlot ty
      ⟨slot, some ty⟩ :: initRefLocalsLoop rbody args (idx + 1) rest

/-- Entry initialization of $M_{\text{ref}}$ (`initRefState rp q maxSteps`):
resolves `rbody.locals` against `rp.types`, pre-populates `cachedLayout := some
ty` on every local, and initializes `stepsExecuted := 0` and
`maxSteps := maxSteps`.

Like `Trusted.MirSemantics.initState`, it first rejects programs captured for
a target whose pointer width is not 64 bits or whose `mirProfileVersion` is not
1. The initial stack is `[callerSentinelFrame retTy, rframe]`, where `retTy` is
the type of the entry function's return place `_0` and `rframe` executes the
entry body. -/
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
        else if !localTys.all refIsSupportedLocalTy then
          .error .unsupported
        else
          let paramTys := (localTys.drop 1).take rbody.argumentCount
          if !checkRefArgsMatch q.args paramTys then
            .error .unsupported
          else
            -- `argumentCount < localTys.length` makes `_0` present here; the
            -- `none` arm keeps the definition total and fails closed.
            match MirSemantics.getElem? localTys 0 with
            | none => .error .unsupported
            | some retTy =>
              let rlocals := initRefLocalsLoop rbody q.args 0 localTys
              let rframe : RefFrameState := {
                defId := rp.entryDefId
                blockIdx := 0
                stmtIdx := 0
                locals := rlocals
                isCallerSentinel := false
              }
              .ok {
                frames := [callerSentinelFrame retTy, rframe]
                callerMem := q.callerMem
                stepsExecuted := 0
                maxSteps := maxSteps
              }

end Trusted.Correspondence
