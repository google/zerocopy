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
import Init.Control.Except
import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.PlaceMachine
import Miri.Interpreter.ValidityMemory
import Miri.Interpreter.MemoryErrors
import Miri.Interpreter.OperandMachine
import Trusted.MirAst
import Trusted.MirModel
import Trusted.Correspondence.Codec
import Trusted.Correspondence.State

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Reference `ExecutionMachine.Config` Construction
(`Trusted.Correspondence.Config`)

Constructs the concrete `Miri.Interpreter.ExecutionMachine.Config Unit RefUser
Choice Unit Unit Unit` for a `RefProg`, wiring `deinitMovedPlace := true`,
64-bit target layouts, `ValidityMemory.bind` shallow validation,
`ExecutionScalar.Leaves`, `ExecutionLeaves.Discriminant`,
`ExecutionCast.Leaves` (integer-like `IntToInt` casts only),
`PlaceMachine.AccessConfig`, and `TerminatorMachine.Hooks` with fail-closed
Day-1 leaves for unmodeled features (calls, other casts, floats, pointers,
atomics, intrinsics, unwinding). Imports only `Init.*`, `Miri.*`,
`Trusted.MirAst`, `Trusted.MirModel`, and `Trusted.Correspondence.{Codec,State}`
— never `Trusted.MirSemantics`.
-/

/-- Resource budget passed to `Miri.Interpreter.ExecutionMachine.step`. Day-1
validity depth is at most 2 (scalar enum -> tag field / fieldless variant), so
budget `8` is never exhausted on any Day-1 type. -/
noncomputable def refLimits : Miri.Interpreter.ExecutionMachine.Limits := {
  callDispatch := 8
  casts := 8
  retag := 8
  validation := 8
}

/-- Pointer-arithmetic target for 64-bit `RefProg`s (`pointerSize = 8`). -/
noncomputable def refPointerArithmetic : Miri.Memory.PointerArithmetic :=
  ⟨Miri.ABI.Size.ofBytes 8⟩

/-- Maximum Rust object size on 64-bit targets (`i64::MAX`). -/
noncomputable def refMaxSizeOfVal : Miri.ABI.Size :=
  Miri.ABI.Size.ofBytes 9223372036854775807

/-- Resolve a concrete pointer `(allocId, offset, tag)` without integer-to-ptr
casts, matching Day-1 strict provenance on caller-owned return allocations. -/
noncomputable def refResolvePointerPure :
    Miri.Memory.PointerResolver Miri.Memory.Provenance
      Miri.Memory.ProvenanceExtra :=
  fun ptr _ =>
    match ptr.provenance with
    | some (.concrete allocId tag) =>
      .ok ⟨allocId, ptr.offset, .concrete tag⟩
    | _ => .error ptr.offset.bytes

/-- Lift `refResolvePointerPure` into `PlaceMachine.MachineM`. -/
noncomputable def refResolvePointer
    (_mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (sz : Int)
    (machine : Miri.Interpreter.MachineHooks.MachineState Unit RefUser) :
    EStateM.Result Miri.Interpreter.StepError
      (Miri.Interpreter.MachineHooks.MachineState Unit RefUser)
      (Except UInt64 (Miri.Memory.ResolvedPointer Miri.Memory.ProvenanceExtra)) :=
  .ok (refResolvePointerPure ptr sz) machine

/-- Global-allocation hooks for Day-1 programs (no globals materialized;
synchronizeMemory is identity). -/
noncomputable def refGlobalAllocationHooks :
    Miri.Memory.GlobalAllocationHooks Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser) := {
  synchronizeMemory := fun _ h => h
  evaluateStaticInitializer := fun mem h _ =>
    ⟨mem, h, .error "globals unsupported on Day 1"⟩
  beforeAccessGlobal := fun mem h _ _ _ _ =>
    ⟨mem, h, .error "globals unsupported on Day 1"⟩
  adjustGlobalAllocation := fun mem h _ _ =>
    ⟨mem, h, .error "globals unsupported on Day 1"⟩
}

/-- `PlaceMachine.AccessConfig` for `refExecutionConfig`, with
`deinitMovedPlace := true` and canonical `Miri.Interpreter.MemoryErrors.operand`
error mapping. -/
noncomputable def refAccessConfig :
    Miri.Interpreter.PlaceMachine.AccessConfig Unit RefUser := {
  runtime := Miri.ABI.RuntimeTargetDataLayout.default
  ghostMode := false
  globalKind := none
  globalHooks := refGlobalAllocationHooks
  dynamicLayout := fun mem h _ => ⟨mem, h, .ok none⟩
  resolvePointer := refResolvePointer
  beforeAllocationAccess := fun _ m => .ok () m
  diagnostic := fun _ _ _ m => .ok () m
  weakMemoryWrite := fun _ _ m => .ok () m
  syncAccess := fun _ _ _ m => .ok () m
  retainTouched := fun m _ => m
  memoryError := Miri.Interpreter.MemoryErrors.operand
  deinitMovedPlace := true
}

/-- `PlaceMachine.AllocationConfig` for `refExecutionConfig`. -/
noncomputable def refAllocationConfig :
    Miri.Interpreter.PlaceMachine.AllocationConfig Unit RefUser := {
  maximumObjectSize := refMaxSizeOfVal
  zeroedStorage := fun n _ => some (Array.replicate n.bytes.toNat 0)
  nativeStorage := none
  nativeDrop := none
  diagnostic := fun _ _ _ m => .ok () m
  allocationTail := fun _ _ _ m => .ok () m
  adjustRootAddress := fun allocId tag st =>
    .ok ⟨Miri.ABI.Size.ZERO, .concrete allocId tag⟩ st
}

/-- Resolve a `LocalLayout` by canonical `TyId` against `types`. -/
noncomputable def refLayoutOfTyId (types : List MirTy) (tyId : TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.LocalLayout :=
  match resolveTy types tyId with
  | some ty => .ok (refLocalLayoutForTy types ty)
  | none => .error (.invalidProgram "unknown TyId in layoutOf")

/-- Field-layout projection used by `ProjectionCx.field` and
`PlaceProjectionHooks.field`: projects field `0` of a scalar-tagged enum-like
type (`refAsEnumTy? ty = some ety`, covering `.enum ety` and
`core::cmp::Ordering`) to its initialized tag scalar layout
(`refLocalLayoutForTy types (.int tagW tagS)`), and fields `0` and `1` of an
overflow pair `.tuple [.int w s, .bool]` to the integer and `bool` layouts. -/
noncomputable def refProjectFieldLayout (types : List MirTy)
    (base : Miri.Interpreter.LocalLayout) (fieldIdx : Nat) :
    Except Miri.Interpreter.ProjectionError Miri.Interpreter.LocalLayout :=
  if Nat.beq fieldIdx 0 then
    match resolveTy types base.ty with
    | some (.tuple [.int w s, .bool]) =>
      .ok (refLocalLayoutForTy types (.int w s))
    | some ty =>
      match refAsEnumTy? ty with
      | some ety =>
        match ety.tagRepr with
        | .scalar tagW tagS => .ok (refLocalLayoutForTy types (.int tagW tagS))
        | .zeroSized => .error (.invariant "field projection on ZST enum")
      | none => .error (.obligation "field projection unsupported on Day 1")
    | none => .error (.obligation "field projection unsupported on Day 1")
  else if Nat.beq fieldIdx 1 then
    match resolveTy types base.ty with
    | some (.tuple [.int _ _, .bool]) => .ok (refLocalLayoutForTy types .bool)
    | _ => .error (.obligation "non-zero field projection unsupported on Day 1")
  else
    .error (.obligation "non-zero field projection unsupported on Day 1")

/-- Variant-layout projection used by `ProjectionCx.variant` and
`PlaceProjectionHooks.variant`: projects an enum-like (`refAsEnumTy?`) downcast
variant `v` to a 0-field `Variants.Single v` layout sharing `base.ty`. -/
noncomputable def refProjectVariantLayout (types : List MirTy)
    (base : Miri.Interpreter.LocalLayout) (variant : Nat) :
    Except Miri.Interpreter.ProjectionError Miri.Interpreter.LocalLayout :=
  match (resolveTy types base.ty).bind refAsEnumTy? with
  | some ety =>
    if Nat.blt variant ety.discriminants.length then
      .ok ⟨base.ty, { refUnitLayoutData with variants := .Single variant }⟩
    else
      .error (.invariant "enum variant index out of bounds")
  | none => .error (.obligation "variant projection unsupported on Day 1")

/-- Lift `ProjectionError` into `StepError` for `PlaceProjectionHooks`. -/
noncomputable def refProjErrToStepErr :
    Miri.Interpreter.ProjectionError → Miri.Interpreter.StepError
  | .machineError e => e
  | .obligation msg => .unsupported msg
  | _ => .invalidProgram "projection error"

/-- Pure `Miri.Interpreter.ProjectionCx` for immediate field/variant
projections (enum tag field `0` and downcast variants). -/
noncomputable def refProjectionCx (types : List MirTy) :
    Miri.Interpreter.ProjectionCx Miri.Memory.Provenance := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  maxSizeOfVal := refMaxSizeOfVal
  isSliceOrStr := fun _ => .ok false
  field := refProjectFieldLayout types
  variant := refProjectVariantLayout types
  dynamicAlign := fun _ _ => .ok none
  packedAlign := fun _ => .ok none
  immediateOffset := fun imm src off dst =>
    Miri.Interpreter.projectionImmediateOffset (fun _ _ => .ok ())
      imm src off dst false
  memoryOffset := fun _ _ _ _ =>
    .error (.obligation "pure memoryOffset unused")
  subsliceLayout := fun _ _ =>
    .error (.obligation "subslice unsupported on Day 1")
  layoutOf := fun tyId =>
    match resolveTy types tyId with
    | some ty => .ok (refLocalLayoutForTy types ty)
    | none => .error (.invariant "unknown TyId in ProjectionCx.layoutOf")
  deref := fun _ => .error (.obligation "deref unsupported on Day 1")
  localIndex := fun _ => .error (.obligation "index unsupported on Day 1")
}

/-- Base `PlaceMachine.CompilerHooks` used to construct `refValidityHooks`
before binding `validate` via `TypedMachineBindings.bindValidation`. -/
noncomputable def refBaseCompilerHooks (types : List MirTy) :
    Miri.Interpreter.PlaceMachine.CompilerHooks Unit RefUser Choice := {
  debugAssertions := false
  layout := fun _ localId st =>
    match st.stack.currentFrame? with
    | none => .error (.stack .emptyStack) st
    | some frame =>
      match frame.body.locals[localId]? with
      | none => .error (.stack (.missingLocalType localId)) st
      | some tyId =>
        match refLayoutOfTyId types tyId with
        | .ok l => .ok l st
        | .error e => .error e st
  validationInProgress := fun st => .ok false st
  projection := fun _ st => .ok (refProjectionCx types) st
  deref := fun _ _ _ st =>
    .error (.unsupported "projections unsupported on Day 1") st
  checkPlaceType := fun _ _ _ st => .ok () st
  memoryOffset := fun _ mplace off mode metaVal st =>
    Miri.Interpreter.placeMemoryOffset refPointerArithmetic
      refResolvePointerPure st.machine.memory.getAllocInfo
      mplace off mode metaVal st
  debugAbiCheck := fun _ _ st => .ok () st
  localSpan := fun _ _ st => .ok ⟨0⟩ st
  enforceValidity := fun _ _ st => .ok true st
  validate := fun _ _ st =>
    .error (.unsupported "validate bound by refValidatedCompilerHooks") st
  willValidateMemory := fun _ => true
}

/-- `DynamicLayoutHooks` for `refExecutionConfig` (all Day-1 types are sized,
so `DynamicLayout.sizeAndAlignFromMeta` hits its sized fast path). -/
noncomputable def refDynamicLayoutHooks (types : List MirTy) :
    Miri.Interpreter.DynamicLayoutHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  maxSizeOfVal := refMaxSizeOfVal
  classify := fun _ _ st =>
    .error (.unsupported "unsized dynamic layout unsupported on Day 1") st
  field := fun _ base idx st =>
    match refProjectFieldLayout types base idx with
    | .ok l => .ok l st
    | .error e => .error (refProjErrToStepErr e) st
  packedAlign := fun _ _ st => .ok none st
  vtableSizeAndAlign := fun _ _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
}

/-- Base `PlaceProjectionHooks` used inside `refValidityHooks` (whose read,
field, variant, and `toOp` paths never invoke `place.validate`). -/
noncomputable def refBasePlaceProjectionHooks (types : List MirTy) :
    Miri.Interpreter.PlaceProjectionHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      Miri.Interpreter.MachineHooks.FrameExtra := {
  place := Miri.Interpreter.PlaceMachine.placeHooks
    refAccessConfig refAllocationConfig (refBaseCompilerHooks types)
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  maxSizeOfVal := refMaxSizeOfVal
  dynamic := refDynamicLayoutHooks types
  dynamicFuel := 8
  isSliceOrStr := fun _ _ st => .ok false st
  field := fun _ base idx st =>
    match refProjectFieldLayout types base idx with
    | .ok l => .ok l st
    | .error e => .error (refProjErrToStepErr e) st
  variant := fun _ base v st =>
    match refProjectVariantLayout types base v with
    | .ok l => .ok l st
    | .error e => .error (refProjErrToStepErr e) st
  packedAlign := fun _ _ st => .ok none st
  subsliceLayout := fun _ _ _ st =>
    .error (.unsupported "subslice unsupported on Day 1") st
  layoutOf := fun _ tyId st =>
    match refLayoutOfTyId types tyId with
    | .ok l => .ok l st
    | .error e => .error e st
  localIndex := fun _ _ st =>
    .error (.unsupported "index unsupported on Day 1") st
}

/-- Decode a `Miri.MIR.ConstOperand` against `types` (strictly requiring an
in-bounds `RefProg.types` index) via `evalRefConstLit` and encode it into a
typed `Miri.Interpreter.OpTy Miri.Memory.Provenance`. -/
noncomputable def refEvalConstOperand (types : List MirTy)
    (c : Miri.MIR.ConstOperand)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    EStateM.Result Miri.Interpreter.StepError
      (Miri.Interpreter.MachineHooks.State Unit RefUser)
      (Miri.Interpreter.OpTy Miri.Memory.Provenance) :=
  match c with
  | ⟨_, _, .Val (.Scalar (.Int bitsNat _)) tyId⟩ =>
    match MirSemantics.getElem? types tyId with
    | none => .error (.unsupported "constant TyId out of bounds") st
    | some ty =>
      match evalRefConstLit ty (.scalar (BitVec.ofNat 128 bitsNat)) with
      | .ok v =>
        .ok ⟨.immediate (valToMiriImmediate ty v),
          refLocalLayoutForTy types ty⟩ st
      | .error .undefined =>
        .error (.undefinedBehavior "invalid constant scalar literal") st
      | .error .unsupported =>
        .error (.unsupported "unsupported constant scalar literal") st
  | ⟨_, _, .Val .ZeroSized tyId⟩ =>
    match MirSemantics.getElem? types tyId with
    | none => .error (.unsupported "constant TyId out of bounds") st
    | some ty =>
      match evalRefConstLit ty .zeroSized with
      | .ok v =>
        .ok ⟨.immediate (valToMiriImmediate ty v),
          refLocalLayoutForTy types ty⟩ st
      | .error .undefined =>
        .error (.undefinedBehavior "invalid zero-sized constant") st
      | .error .unsupported =>
        .error (.unsupported "unsupported zero-sized constant") st
  | _ => .error (.unsupported "unsupported ConstOperand") st

/-- `ExecutionLeaves.Operand` for `refExecutionConfig`. -/
noncomputable def refOperandLeaves (types : List MirTy) :
    Miri.Interpreter.ExecutionLeaves.Operand
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice := {
  checkPlaceType := fun _ _ _ st => .ok () st
  dereference := fun _ _ st =>
    .error (.unsupported "projections unsupported on Day 1") st
  runtimeChecks := fun _ _ st =>
    .error (.unsupported "RuntimeChecks unsupported on Day 1") st
  boolLayout := fun _ st => .ok (refLocalLayoutForTy types .bool) st
  -- `Miri.Interpreter.Panic.assertPanic` evaluates diagnostic operands inside
  -- `BoundsCheck` / `MisalignedPointerDereference` via `OperandPath.assertion`
  -- (`#[.field "kind", .field "message", .field field]`, plus `.constant`).
  -- `toMiriAssertKind` populates them with `refAssertDummyOperand` (a zero
  -- `usize` constant whose `TyId` may fall outside `RefProg.types`), so resolve
  -- that path to a synthetic zero `usize` immediate without requiring `types`.
  -- Function-item operands of `Call` terminators resolve to `fnTyBase`-tagged
  -- zero-sized immediates.
  constantAt := fun _ path c _ st =>
    match path.toList with
    | [.field "kind", .field "message", .field _, .field "constant"] =>
      .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar .isize 0))),
        refLocalLayoutForTy types (.int .isize false)⟩ st
    | _ =>
      match c with
      | ⟨_, _, .Val .ZeroSized fnTyId⟩ =>
        if path == (Miri.Interpreter.OperandPath.instruction "function").push
            (.field "constant") then
          if Nat.ble (fnTyBase types) fnTyId then
            .ok ⟨.immediate .uninit, ⟨fnTyId, refUnitLayoutData⟩⟩ st
          else
            .error (.unsupported "invalid function TyId") st
        else
          refEvalConstOperand types c st
      | _ => refEvalConstOperand types c st
}

/-- Padding decision of `copy_op_no_validate`, matching
`compiler/rustc_const_eval/src/interpret/place.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Input.CompilerCopy.hasPadding`:

> "// If the source has padding, we want to always do a mem-to-mem copy to
> // ensure consistent padding in the target independent of layout choices.
> let src_has_padding = match src.layout().backend_repr {
>     BackendRepr::Scalar(_) => false,
>     BackendRepr::ScalarPair { a: left, b: right, b_offset: _ }
>         if matches!(src.layout().ty.kind(), ty::Ref(..) | ty::RawPtr(..)) =>
>     {
>         // Wide pointers never have padding, so we can avoid calling `size()`.
>         debug_assert_eq!(left.size(self) + right.size(self),
>             src.layout().size);
>         false
>     }
>     BackendRepr::ScalarPair { a: left, b: right, b_offset: _ } => {
>         let left_size = left.size(self);
>         let right_size = right.size(self);
>         // We have padding if the sizes don't add up to the total.
>         ...
>         left_size + right_size != src.layout().size
>     }
>     // Everything else can only exist in memory anyway, so it doesn't matter.
>     BackendRepr::SimdVector { .. }
>     | BackendRepr::SimdScalableVector { .. }
>     | BackendRepr::Memory { .. } => true,
> };"

No reference or raw-pointer type has a $M_{\text{ref}}$ layout, so the
wide-pointer arm never applies. -/
noncomputable def refHasPadding (layout : Miri.Interpreter.LocalLayout) :
    Except Miri.Interpreter.StepError Bool :=
  match layout.layout.backendRepr with
  | .Scalar _ => .ok false
  | .ScalarPair (a := a) (b := b) (bOffset := _) =>
    match a.size refAccessConfig.runtime, b.size refAccessConfig.runtime with
    | .ok sizeA, .ok sizeB =>
      match sizeA.add sizeB with
      | .ok total => .ok (total != layout.layout.size)
      | .error _ => .error (.invalidProgram "scalar-pair size overflow")
    | _, _ => .error (.invalidProgram "scalar-pair scalar size unavailable")
  | _ => .ok true

/-- `PlaceCopyHooks` for `refExecutionConfig`: `refHasPadding` decides padding,
and canonical `TyId`s make layout compatibility exact `a.ty == b.ty`. -/
noncomputable def refPlaceCopyHooks :
    Miri.Interpreter.PlaceCopyHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice := {
  compatible := fun a b => .ok (a.ty == b.ty)
  hasPadding := refHasPadding
  readRaw := fun _ => Miri.Interpreter.PlaceMachine.readRaw refAccessConfig
  memoryCopy := fun _ _ _ st =>
    .error (.unsupported "memoryCopy unsupported on Day 1") st
  validateSource := fun _ _ _ st => .ok () st
}

/-- `ExecutionLeaves.Discriminant` for `refExecutionConfig`, routing all
enum-like types (`.enum ety` and `core::cmp::Ordering`) through
`refAsEnumTy?`. -/
noncomputable def refDiscriminantLeaves (types : List MirTy) :
    Miri.Interpreter.ExecutionLeaves.Discriminant
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice := {
  discriminantLayout := fun _ tyId st =>
    match (resolveTy types tyId).bind refAsEnumTy? with
    | some ety =>
      if refEnumAdmitted ety then
        .ok (refLocalLayoutForTy types (.int ety.discrWidth ety.discrSigned)) st
      else
        .error (.unsupported "unadmitted enum in discriminantLayout") st
    | none => .error (.unsupported "discriminant on non-enum type") st
  tagLayout := fun _ tag st =>
    match tag.primitive with
    | .Int integer signed =>
      let w := intWidthOfMiriInteger integer
      .ok (refLocalLayoutForTy types (.int w signed)) st
    | _ => .error (.invalidProgram "non-integer enum tag") st
  discriminantValue := fun _ tyId variant st =>
    match (resolveTy types tyId).bind refAsEnumTy? with
    | some ety =>
      match MirSemantics.getElem? ety.discriminants variant with
      | some disc =>
        .ok (some (tyIdFor types (.int ety.discrWidth ety.discrSigned),
          BitVec.ofNat 128 disc)) st
      | none => .error (.invalidProgram "enum variant out of bounds") st
    | none => .error (.unsupported "discriminantValue on non-enum type") st
  variantForDiscriminant := fun _ tyId discrBits st =>
    match (resolveTy types tyId).bind refAsEnumTy? with
    | some ety =>
      .ok (refFindDiscrVariant? discrBits ety.discriminants) st
    | none => .error (.unsupported "variantForDiscriminant on non-enum type") st
  adtVariantCount := fun _ tyId st =>
    match (resolveTy types tyId).bind refAsEnumTy? with
    | some ety => .ok ety.discriminants.length st
    | none => .error (.unsupported "adtVariantCount on non-enum type") st
  scalarMayBeNull := fun _ _ st =>
    .error (.unsupported "niche scalarMayBeNull unsupported on Day 1") st
}

/-- `OperandMachine.Hooks` used by `ValidityVisitor`'s `discriminant` hooks
(`projectRead`). -/
noncomputable def refValidityOperandHooks (types : List MirTy) :
    Miri.Interpreter.OperandMachine.Hooks Unit RefUser Choice := {
  compiler := refBaseCompilerHooks types
  projection := refBasePlaceProjectionHooks types
  layoutCompatible := refPlaceCopyHooks.compatible
  -- Invoked live by `OperandMachine.evalPlaceToOp`; Day-1 place/local types
  -- are validated statically at entry (`initRefState`).
  checkPlaceType := fun _ _ _ st => .ok () st
  dereference := (refOperandLeaves types).dereference
  runtimeChecks := (refOperandLeaves types).runtimeChecks
  boolLayout := (refOperandLeaves types).boolLayout
  constant := fun _ _ _ st =>
    .error (.unsupported "constant unused in validity") st
  constantAt := (refOperandLeaves types).constantAt
  deinitMovedPlace := true
}

/-- `DiscriminantHooks` supplied to `ValidityVisitor.Hooks` so enum validation
executes real `Miri.Interpreter.Discriminant.readDiscriminant`. -/
noncomputable def refValidityDiscriminantHooks (types : List MirTy) :
    Miri.Interpreter.DiscriminantHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      (Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) :=
  let leaves := refDiscriminantLeaves types
  let proj := refBasePlaceProjectionHooks types
  {
    runtimeTarget := refAccessConfig.runtime
    discriminantLayout := leaves.discriminantLayout
    tagLayout := leaves.tagLayout
    discriminantValue := leaves.discriminantValue
    variantForDiscriminant := leaves.variantForDiscriminant
    adtVariantCount := leaves.adtVariantCount
    projectRead :=
      Miri.Interpreter.OperandMachine.field (refValidityOperandHooks types)
    readImmediate := fun _ =>
      Miri.Interpreter.PlaceMachine.readImmediate
        { refAccessConfig with ghostMode := true, deinitMovedPlace := false }
    destLayout := Miri.Interpreter.RuntimePlace.layout
    projectWrite := Miri.Interpreter.PlaceDynamic.field proj
    writeScalar := fun c sc dest =>
      Miri.Interpreter.writePlaceImmediate proj.place c (.scalar sc) dest
    toOp := Miri.Interpreter.placeToOp proj.place
    scalarMayBeNull := leaves.scalarMayBeNull
  }

/-- `VTableHooks` fail-closed placeholder for Day-1 (unreachable without
trait objects). -/
noncomputable def refVTableHooks {F ABI : Type} :
    Miri.Interpreter.VTableHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice F ABI := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  isDynamic := fun _ _ st => .ok false st
  memoryOffset := fun _ _ _ _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
  resolvePointer := fun _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
  globalVTable := fun _ _ st => .ok none st
  globalFunction := fun _ _ st => .ok none st
  predicates := fun _ _ st => .ok Array.empty st
  normalizePredicate := fun _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
  layoutOf := fun _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
  eraseAndAnonymize := fun _ _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
  ensureMonomorphicType := fun _ _ st => .ok () st
  ensureMonomorphicDyn := fun _ _ st => .ok () st
  globalSalt := fun _ st => .ok 0 st
  reserveVTable := fun _ _ _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
  globalRootPointer := fun _ _ st =>
    .error (.unsupported "vtable unsupported on Day 1") st
  entries := fun _ _ _ st => .ok Array.empty st
  assertVirtualInstanceMatches := fun _ _ _ _ _ st => .ok () st
}

/-- `ValidityMemory.Environment` connecting `ValidityMemory.bind` directly to
`MachineHooks.State Unit RefUser`'s live `MemoryState`. -/
noncomputable def refValidityMemoryEnv :
    Miri.Interpreter.ValidityMemory.Environment
      Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit
      (Miri.Interpreter.PlaceMachine.AccessState Unit RefUser)
      Miri.Memory.ProvenanceExtra
      (Miri.Interpreter.MachineHooks.State Unit RefUser) := {
  context := {
    runtime := refAccessConfig.runtime
    ghostMode := true
    globalKind := none
    globalHooks := refAccessConfig.globalHooks
    accessHooks := Miri.Interpreter.PlaceMachine.accessHooks refAccessConfig
    dynamicLayout := refAccessConfig.dynamicLayout
  }
  memory := fun st => st.machine.memory
  hooks := fun st => ⟨st.machine, none⟩
  putMemoryHooks := fun st mem h =>
    { st with machine := { h.machine with memory := mem } }
  putTouched := fun st _ => st
  memoryError := fun h err =>
    h.pendingError.getD (Miri.Interpreter.MemoryErrors.operand err)
  pointerError := fun h err =>
    h.pendingError.getD (Miri.Interpreter.MemoryErrors.pointerAccess err)
  allocationError := Miri.Interpreter.MemoryErrors.allocation
}

/-- `ValidityVisitor.Hooks` bound to real `ValidityMemory.bind` for Day-1
integer, boolean, `char`, unit, never, fieldless-enum, `Ordering`, and
overflow-pair validation. -/
noncomputable def refValidityHooks (types : List MirTy) :
    Miri.Interpreter.ValidityVisitor.Hooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      Miri.Interpreter.MachineHooks.FrameExtra
      (Miri.Interpreter.FnVal Unit) (Miri.ABI.FnAbi TyId)
      Miri.Interpreter.ValidityMemory.PaddingHandle :=
  let proj := refBasePlaceProjectionHooks types
  let base : Miri.Interpreter.ValidityVisitor.Hooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      Miri.Interpreter.MachineHooks.FrameExtra
      (Miri.Interpreter.FnVal Unit) (Miri.ABI.FnAbi TyId)
      Miri.Interpreter.ValidityMemory.PaddingHandle := {
    target := Miri.ABI.RuntimeTargetDataLayout.default
    projection := proj
    vtable := refVTableHooks
    discriminant := refValidityDiscriminantHooks types
    debugAssertions := false
    classify := fun _ tyId st =>
      match resolveTy types tyId with
      | some .bool => .ok .boolean st
      | some (.int _ _) => .ok .integer st
      | some .char => .ok .character st
      | some .unit => .ok (.aggregate false false false) st
      | some .never => .ok .never st
      | some (.tuple [.int _ _, .bool]) => .ok (.aggregate false false false) st
      | some ty =>
        match refAsEnumTy? ty with
        | some _ => .ok (.aggregate false false true) st
        | none => .error (.invalidProgram "unsupported validity type") st
      | none => .error (.invalidProgram "unsupported validity type") st
    unitLayout := fun _ st => .ok (refLocalLayoutForTy types .unit) st
    typeName := fun _ _ st => .ok "" st
    opsemInhabited := fun _ tyId st =>
      match resolveTy types tyId with
      | some .never => .ok false st
      | some _ => .ok true st
      | none => .error (.invalidProgram "unknown TyId in opsemInhabited") st
    isFreeze := fun _ _ st =>
      .error (.unsupported "isFreeze unsupported on Day 1") st
    fieldPath := fun _ _ _ _ st => .ok .enumTag st
    variantPath := fun _ _ _ st => .ok (.variant "") st
    projectBox := fun _ _ st =>
      .error (.unsupported "box unsupported on Day 1") st
    toOp := Miri.Interpreter.placeToOp proj.place
    readImmediate := fun _ _ _ st =>
      .error (.unsupported "bound by ValidityMemory.bind") st
    clearProvenance := fun _ _ st =>
      .error (.unsupported "bound by ValidityMemory.bind") st
    writeNoValidate := fun _ _ _ st =>
      .error (.unsupported "bound by ValidityMemory.bind") st
    sizeAndAlign := fun _ mp st =>
      .ok (some (mp.layout.layout.size, mp.layout.layout.align.abi)) st
    ptrToPlace := fun _ _ st =>
      .error (.unsupported "ptrToPlace unsupported on Day 1") st
    metadataTail := fun _ _ st =>
      .error (.unsupported "metadataTail unsupported on Day 1") st
    checkPointerAccess := fun _ _ _ st =>
      .error (.unsupported "checkPointerAccess unsupported on Day 1") st
    checkPointerAlign := fun _ _ _ st =>
      .error (.unsupported "checkPointerAlign unsupported on Day 1") st
    checkPointerAlignResult := fun _ _ _ st =>
      .error (.unsupported "checkPointerAlignResult unsupported on Day 1") st
    scalarMayBeNull := fun _ _ st =>
      .error (.unsupported "pointer scalarMayBeNull unsupported on Day 1") st
    retagPointer := fun _ _ _ st =>
      .error (.unsupported "retagPointer unsupported on Day 1") st
    ctfePointerLookup := fun _ _ _ st =>
      .error (.unsupported "ctfePointerLookup unsupported on Day 1") st
    inMutableMemory := fun _ _ st =>
      .error (.unsupported "inMutableMemory unsupported on Day 1") st
    readBytes := fun _ _ _ _ st =>
      .error (.unsupported "bound by ValidityMemory.bind") st
    clearBytesProvenance := fun _ _ _ st =>
      .error (.unsupported "bound by ValidityMemory.bind") st
    beginPadding := fun _ _ _ st =>
      .error (.unsupported "bound by ValidityMemory.bind") st
    writePadding := fun _ _ _ st =>
      .error (.unsupported "bound by ValidityMemory.bind") st
    cachedUnionRanges := fun _ _ act => act
    withGhostValidation := fun act => act
  }
  Miri.Interpreter.ValidityMemory.bind base refValidityMemoryEnv
    (fun st => .ok false st) (fun _ _ st => .ok () st) (fun _ => true)

/-- `ExecutionScalar.Leaves` for `refExecutionConfig`. -/
noncomputable def refScalarLeaves (types : List MirTy) :
    Miri.Interpreter.ExecutionScalar.Leaves
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice := {
  classify := fun _ tyId st =>
    match resolveTy types tyId with
    | some .bool => .ok .boolean st
    | some (.int w s) => .ok (.integer (toMiriIntKind w s)) st
    | some .char => .ok .character st
    | _ => .error (.invalidProgram "non-scalar operand type") st
  boolLayout := fun _ st => .ok (refLocalLayoutForTy types .bool) st
  orderingLayout := fun _ st => .ok (refLocalLayoutForTy types .ordering) st
  overflowLayout := fun _ input st =>
    match resolveTy types input.ty with
    | some (.int w s) =>
      .ok (refLocalLayoutForTy types (.tuple [.int w s, .bool])) st
    | _ => .error (.invalidProgram "overflow layout on non-integer type") st
  metadataLayout := fun _ _ st =>
    .error (.unsupported "PtrMetadata unsupported on Day 1") st
  unitLayout := fun _ st => .ok (refLocalLayoutForTy types .unit) st
}

/-- `MachineHooks.StorageHooks` for `StorageLive` and `StorageDead`. -/
noncomputable def refStorageHooks (types : List MirTy) :
    Miri.Interpreter.MachineHooks.StorageHooks Unit RefUser := {
  veryTriviallySized := fun _ => .ok true
  layout := fun localId st =>
    match st.stack.currentFrame? with
    | none => .error (.stack .emptyStack) st
    | some frame =>
      match frame.body.locals[localId]? with
      | none => .error (.stack (.missingLocalType localId)) st
      | some tyId =>
        match refLayoutOfTyId types tyId with
        | .ok l => .ok l st
        | .error e => .error e st
  allocateDyn := fun _ _ st =>
    .error (.unsupported "unsized local unsupported on Day 1") st
  deallocateStack := fun _ st => .ok () st
}

/-- `CallMachine.Lifecycle` for `refExecutionConfig` (`Return` uses
`returnContinuation := .stop false`, so `CallMachine.cleanup` returns
`.noCleanup` directly without calling `afterPop`). -/
noncomputable def refLifecycle (types : List MirTy) :
    Miri.Interpreter.CallMachine.Lifecycle Unit RefUser Choice := {
  compiler := {
    requiresCallerLocation := fun _ st => .ok false st
    isLocalDefinition := fun _ st => .ok true st
    definitionCrate := fun _ st => .ok 0 st
    userRelevantCrate := fun _ st => .ok true st
    crateName := fun _ st => .ok "" st
    sourceScope := fun _ _ _ _ st => .ok ⟨none, none⟩ st
  }
  storage := refStorageHooks types
  freshLocalsIdentity := fun m =>
    (m, Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)
  preambleSpan := fun _ st => .ok ⟨0⟩ st
  requiredConstants := fun _ st => .ok () st
  afterPop := fun _ _ _ st => .ok .normal st
}

/-- `TypedRetag.Hooks` fail-closed placeholder (Tree Borrows is disabled on
Day 1, `borrowTracker = none`). -/
noncomputable def refRetagHooks :
    Miri.Interpreter.TypedRetag.Hooks Unit RefUser := {
  typeShape := fun _ st => .error (.unsupported "retag unsupported") st
  builtinDeref := fun _ st => .error (.unsupported "retag unsupported") st
  referencePointee := fun _ st => .error (.unsupported "retag unsupported") st
  isUnpin := fun _ st => .ok true st
  isUnsafeUnpin := fun _ st => .ok false st
  typeIsFreeze := fun _ st => .ok true st
  implicitWrites := fun st => .ok false st
  rustcNoWritable := fun _ st => .ok false st
  preciseInteriorMut := fun st => .ok false st
  immPtrToMPlace := fun _ st => .error (.unsupported "retag unsupported") st
  sizeAndAlign := fun mp st =>
    .ok (some (mp.layout.layout.size, mp.layout.layout.align.abi)) st
  checkPtrAccess := fun _ _ st => .error (.unsupported "retag unsupported") st
  resolveAllocation := fun _ st => .ok none st
  logCreation := fun _ _ _ _ _ st => .ok () st
  freeze := {
    target := refPointerArithmetic
    debugAssertions := false
    isUnsafeCell := fun _ st => .ok false st
    typeIsFreeze := fun _ st => .ok true st
    isDynamic := fun _ st => .ok false st
    isBox := fun _ st => .ok false st
    isTooGeneric := fun _ st => .ok false st
    sizeAndAlign := fun mp st =>
      .ok (some (mp.layout.layout.size, mp.layout.layout.align.abi)) st
    unpackDynTrait := fun _ st => .error (.unsupported "freeze unsupported") st
    projectBox := fun _ st => .error (.unsupported "freeze unsupported") st
    projectField := fun _ _ st => .error (.unsupported "freeze unsupported") st
    arrayLength := fun _ st => .error (.unsupported "freeze unsupported") st
    projectIndex := fun _ _ st => .error (.unsupported "freeze unsupported") st
  }
  ensureTreeExtra := fun _ st => .ok () st
  reconstruct := fun _ _ st => .error (.unsupported "retag unsupported") st
  writeUninit := fun _ st => .error (.unsupported "retag unsupported") st
}

/-- `PlaceMachine.CompilerHooks` with `validate` bound to real
`ValidityVisitor.validatePlace` via `TypedMachineBindings.bindValidation`. -/
noncomputable def refCompilerHooks (types : List MirTy) :
    Miri.Interpreter.PlaceMachine.CompilerHooks Unit RefUser Choice :=
  (Miri.Interpreter.TypedMachineBindings.bindValidation
    (refBaseCompilerHooks types) refPlaceCopyHooks (refValidityHooks types)
    refRetagHooks refLimits.retag refLimits.validation
    (fun _ _ st => .ok false st)).1

/-- `PlaceProjectionHooks` for `refExecutionConfig`, carrying `place.validate`
bound to `ValidityVisitor.validatePlace` so `ExecutionMachine.projectionHooks`,
`rvalueHooks`, and `ExecutionControl.hooks` run real shallow validation. -/
noncomputable def refPlaceProjectionHooks (types : List MirTy) :
    Miri.Interpreter.PlaceProjectionHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      Miri.Interpreter.MachineHooks.FrameExtra :=
  { refBasePlaceProjectionHooks types with
    place := Miri.Interpreter.PlaceMachine.placeHooks
      refAccessConfig refAllocationConfig (refCompilerHooks types) }

/-- Empty address-table placeholder for Day-1 `ExecutionMachine.Config`. -/
noncomputable def refEmptyAddressState :
    Miri.Memory.AllocAddresses.GlobalAddressState := {
  provenanceMode := .strict
  addressMode := .managed
  generation := none
}

/-- `TerminatorMachine.Hooks` wired to `RefUser.control`. Because
`gcInterval = 0` and `threads.fixedScheduling = true`,
`beforeTerminatorWithChoice` updates `basicBlockCount`, `sinceGc`, and
`monotonic` without GC or preemption. -/
noncomputable def refTerminatorMachineHooks :
    Miri.Interpreter.TerminatorMachine.Hooks Unit RefUser Unit := {
  getControl := fun u => u.control
  setControl := fun ctrl u => { u with control := ctrl }
  provenance := {
    visitUser := fun _ roots => .ok roots
    addresses := fun _ => refEmptyAddressState
    setAddresses := fun _ u => u
    symbolicAlignment := fun _ => Array.empty
    setSymbolicAlignment := fun _ u => u
  }
  blockingIoGc := fun st => .ok () st
}

/-- Fail-closed `FloatOpsHooks` placeholder for Day-1. -/
noncomputable def refFloatOpsHooks (types : List MirTy) :
    Miri.Interpreter.FloatOpsHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice := {
  integerKindOf := fun _ _ st => .error (.unsupported "floats unsupported") st
  formatOf := fun _ _ st => .error (.unsupported "floats unsupported") st
  boolLayout := fun _ st => .ok (refLocalLayoutForTy types .bool) st
  floatNondeterministic := false
  chooseNaN := fun _ _ st => .ok 0 st
}

/-- `ExecutionCast.Leaves` for `refExecutionConfig`. `typeInfo` classifies
integers, `bool`, and `char` (the integer-like types of `CastKind::IntToInt`)
and fails closed with `.unsupported` on every other type, so
`Miri.Interpreter.Cast.cast` rejects any other cast source or target; every
pointer, function, and vtable leaf fails closed. -/
noncomputable def refCastLeaves (types : List MirTy) :
    Miri.Interpreter.ExecutionCast.Leaves
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice := {
  typeInfo := fun _ tyId st =>
    match resolveTy types tyId with
    | some (.int w s) => .ok (.integer (toMiriIntKind w s)) st
    | some .bool => .ok .boolean st
    | some .char => .ok .character st
    | _ => .error (.unsupported "cast type unsupported") st
  layoutOf := fun _ tyId st =>
    match refLayoutOfTyId types tyId with
    | .ok l => .ok l st
    | .error e => .error e st
  exposeProvenance := fun _ _ st =>
    .error (.unsupported "casts unsupported") st
  pointerFromExposedAddress := fun _ _ st =>
    .error (.unsupported "casts unsupported") st
  usizeLayout := fun _ st =>
    .ok (refLocalLayoutForTy types (.int .isize false)) st
  ensureMonomorphic := fun _ _ st => .ok () st
  requireNoBoundVars := fun _ _ st => .ok () st
  resolveFunction := fun _ _ _ st => .ok none st
  resolveClosureFnOnce := fun _ _ _ st =>
    .error (.unsupported "casts unsupported") st
  builtinDeref := fun _ _ _ st => .ok none st
  boxLayout := fun _ _ st => .error (.unsupported "casts unsupported") st
  validateImmediateABI := fun _ _ => .ok ()
  fieldLayout := fun _ _ _ st => .error (.unsupported "casts unsupported") st
  lockstepTails := fun _ _ _ st => .error (.unsupported "casts unsupported") st
  vtableType := fun _ _ _ st => .error (.unsupported "casts unsupported") st
  vtablePointer := fun _ _ _ st => .error (.unsupported "casts unsupported") st
  principal := fun _ _ st => .ok none st
  vtableEntries := fun _ _ _ st => .ok Array.empty st
  supertraitSlot := fun _ _ _ st => .ok none st
  eraseSelfTraitRef := fun _ n st => .ok n st
  normalizePrincipal := fun _ _ st => .ok none st
}

/-- Fail-closed `AtomicAccessHooks` placeholder for Day-1. -/
noncomputable def refAtomicAccessHooks (types : List MirTy) :
    Miri.Interpreter.AtomicAccessHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      (Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) := {
  target := Miri.ABI.RuntimeTargetDataLayout.default.base
  getGlobal := fun st => st.machine.dataRace
  setGlobal := fun st g =>
    { st with machine := { st.machine with dataRace := some g } }
  threads := fun st => st.machine.threads
  getAtomic := fun _ _ => .error (.unsupported "atomics unsupported")
  setAtomic := fun _ _ st => .error (.unsupported "atomics unsupported") st
  placeLayout := Miri.Interpreter.RuntimePlace.layout
  placePointer := fun _ => .error (.unsupported "atomics unsupported")
  physicalRead := fun _ _ st => .error (.unsupported "atomics unsupported") st
  physicalWrite := fun _ _ _ st =>
    .error (.unsupported "atomics unsupported") st
  ghostRead := fun _ _ st => .ok none st
  checkPointerAlign := fun _ _ _ st =>
    .error (.unsupported "atomics unsupported") st
  resolveAllocation := fun _ _ st =>
    .error (.unsupported "atomics unsupported") st
  mutability := fun _ _ st => .error (.unsupported "atomics unsupported") st
  scalarOps := {
    classify := (refScalarLeaves types).classify
    boolLayout := (refScalarLeaves types).boolLayout
    orderingLayout := (refScalarLeaves types).orderingLayout
    overflowLayout := (refScalarLeaves types).overflowLayout
    metadataLayout := (refScalarLeaves types).metadataLayout
    unitLayout := (refScalarLeaves types).unitLayout
    floatBinary := fun _ _ _ _ st =>
      .error (.unsupported "floats unsupported") st
    pointerBinary := fun _ _ _ _ st =>
      .error (.unsupported "pointerBinary unsupported") st
    floatUnary := fun _ _ _ st =>
      .error (.unsupported "floats unsupported") st
    derefValidity := fun _ _ st =>
      .error (.unsupported "derefValidity unsupported") st
  }
  loadChoiceRank := fun _ _ st => .ok 0 st
  weakPolicy := .neverFail
  weakSuccessChoice := fun _ st => .ok true st
  diagnostic := fun _ _ st => .ok () st
  classifyDispatchError := fun _ => .unsupported "atomics unsupported"
  classifyGlobalError := fun _ => .unsupported "atomics unsupported"
}

/-- Fail-closed `IntrinsicVarArgsHooks` placeholder for Day-1. -/
noncomputable def refVarArgsHooks :
    Miri.Interpreter.IntrinsicVarArgsHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      (Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) := {
  getLists := fun _ => Array.empty
  setLists := fun st _ => st
  markDead := fun st _ _ _ => st
  reserveAllocId := fun _ st => .error (.unsupported "varargs unsupported") st
  globalRootPointer := fun _ _ st =>
    .error (.unsupported "varargs unsupported") st
  resolvePointer := fun _ _ st =>
    .error (.unsupported "varargs unsupported") st
  destLayout := Miri.Interpreter.RuntimePlace.layout
  layoutOf := fun _ _ st => .error (.unsupported "varargs unsupported") st
  typeInfo := fun _ _ st => .ok .other st
  identicalCTypes := fun _ _ _ st => .ok false st
  isCVoid := fun _ _ st => .ok false st
  vaListFields := fun _ _ st => .ok Array.empty st
  isRawPointer := fun _ _ st => .ok false st
  projectField := fun _ _ _ st =>
    .error (.unsupported "varargs unsupported") st
  derefPointer := fun _ _ st => .error (.unsupported "varargs unsupported") st
  placePointer := fun _ => .error (.unsupported "varargs unsupported")
  readPointer := fun _ _ st => .error (.unsupported "varargs unsupported") st
  readScalar := fun _ _ st => .error (.unsupported "varargs unsupported") st
  writePointer := fun _ _ _ st =>
    .error (.unsupported "varargs unsupported") st
  forceAllocation := fun _ _ st =>
    .error (.unsupported "varargs unsupported") st
  writeBytesPointer := fun _ _ _ _ st =>
    .error (.unsupported "varargs unsupported") st
  copyAllowTransmute := fun _ _ _ st =>
    .error (.unsupported "varargs unsupported") st
}

/-- Fail-closed `IntrinsicHooks` placeholder for Day-1 (unreachable since
`TerminatorKind.call` lowers to `.CoroutineDrop`). -/
noncomputable def refIntrinsicHooks (types : List MirTy) :
    Miri.Interpreter.IntrinsicHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      (Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) :=
  let atomics := refAtomicAccessHooks types
  let scalarOps := atomics.scalarOps
  let floats := refFloatOpsHooks types
  let simd : Miri.Interpreter.IntrinsicSimdHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit RefUser) Choice
      (Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) := {
    target := Miri.ABI.RuntimeTargetDataLayout.default.base
    boolTy := tyIdFor types .bool
    u8Ty := tyIdFor types (.int .i8 false)
    isSimd := fun _ _ st => .ok false st
    simdSizeAndType := fun _ _ st =>
      .error (.unsupported "simd unsupported") st
    forceAllocation := fun _ _ st =>
      .error (.unsupported "simd unsupported") st
    placeLayout := Miri.Interpreter.RuntimePlace.layout
    placePointer := fun _ => .error (.unsupported "simd unsupported")
    fieldRead := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    fieldWrite := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    fieldLayout := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    indexRead := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    indexWrite := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    readImmediate := fun _ _ st => .error (.unsupported "simd unsupported") st
    writeImmediate := fun _ _ _ st =>
      .error (.unsupported "simd unsupported") st
    copyOp := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    derefImmediate := fun _ _ st => .error (.unsupported "simd unsupported") st
    readPlaceImmediate := fun _ _ st =>
      .error (.unsupported "simd unsupported") st
    unalignedPlace := fun _ _ _ st =>
      .error (.unsupported "simd unsupported") st
    checkAlign := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    readBytes := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    writeBytes := fun _ _ _ st => .error (.unsupported "simd unsupported") st
    shuffleConst := fun _ _ st => .error (.unsupported "simd unsupported") st
    alignmentConst := fun _ _ st => .error (.unsupported "simd unsupported") st
    scalarOps := scalarOps
    floatOps := floats
    castHooks := Miri.Interpreter.ExecutionCast.hooks
      (refCastLeaves types) refAccessConfig refAllocationConfig
      (refCompilerHooks types) (refPlaceProjectionHooks types)
      refPlaceCopyHooks refRetagHooks (refValidityHooks types)
      {
        registry := fun _ => Miri.Interpreter.FunctionPointers.Registry.empty
        putRegistry := fun u _ => u
        crossCrateInlineAlways := false
        inlineNever := fun _ st => .ok false st
        chooseSalt := fun st => .error (.unsupported "fnPtr unsupported") st
        ptrGetAlloc := fun _ st => .ok none st
        adjustRootPointer := fun allocId tag st =>
          .ok ⟨Miri.ABI.Size.ZERO, .concrete allocId tag⟩ st
        importedFunction := fun _ st => .ok none st
      }
      floats (refOperandLeaves types).dereference
      (Miri.Interpreter.OperandMachine.field (refValidityOperandHooks types))
      (fun _ _ st => .ok false st) 8 8 none
    chooseEqualFloatRight := fun _ _ _ st => .ok false st
    fuseMulAdd := fun _ st => .ok false st
    mathLane := fun _ _ _ _ st => .error (.unsupported "simd unsupported") st
    returnToBlock := fun _ _ st => .error (.unsupported "simd unsupported") st
  }
  {
    simdHooks := simd
    atomicHooks := {
      toAtomicAccessHooks := atomics
      orderingConst := fun _ _ st =>
        .error (.unsupported "atomics unsupported") st
      volatileConst := fun _ _ st =>
        .error (.unsupported "atomics unsupported") st
      derefPointer := fun _ _ st =>
        .error (.unsupported "atomics unsupported") st
      readImmediate := fun _ _ st =>
        .error (.unsupported "atomics unsupported") st
      writeImmediate := fun _ _ _ st =>
        .error (.unsupported "atomics unsupported") st
      returnToBlock := fun _ _ st =>
        .error (.unsupported "atomics unsupported") st
    }
    typeIdHooks := {
      target := Miri.ABI.RuntimeTargetDataLayout.default.base
      hasErasableRegions := fun _ _ st => .ok false st
      typeHash := fun _ _ st => .ok (BitVec.ofNat 128 0) st
      u128Layout := fun _ st =>
        .ok (refLocalLayoutForTy types (.int .i128 false)) st
      unitLayout := fun _ st => .ok (refLocalLayoutForTy types .unit) st
      reserveTypeId := fun _ _ st =>
        .error (.unsupported "typeId unsupported") st
      globalRootPointer := fun _ _ _ st =>
        .error (.unsupported "typeId unsupported") st
      resolvePointer := fun _ _ st =>
        .error (.unsupported "typeId unsupported") st
      globalTypeId := fun _ _ st => .ok none st
      placeLayout := Miri.Interpreter.RuntimePlace.layout
      copyAllowTransmute := fun _ _ _ st =>
        .error (.unsupported "typeId unsupported") st
      projectFieldRead := fun _ _ _ st =>
        .error (.unsupported "typeId unsupported") st
      projectFieldWrite := fun _ _ _ st =>
        .error (.unsupported "typeId unsupported") st
      elementLayout := fun _ _ st =>
        .error (.unsupported "typeId unsupported") st
      offsetRead := fun _ _ _ _ _ st =>
        .error (.unsupported "typeId unsupported") st
      offsetWrite := fun _ _ _ _ _ st =>
        .error (.unsupported "typeId unsupported") st
      readImmediate := fun _ _ st =>
        .error (.unsupported "typeId unsupported") st
      readPlaceScalar := fun _ _ st =>
        .error (.unsupported "typeId unsupported") st
      writeScalar := fun _ _ _ st =>
        .error (.unsupported "typeId unsupported") st
    }
    varArgsHooks := refVarArgsHooks
    varArgsFuel := 8
    target := Miri.ABI.RuntimeTargetDataLayout.default.base
    pointerOffset := Miri.ABI.Size.ofBytes 8
    maxSizeOfVal := refMaxSizeOfVal
    destLayout := Miri.Interpreter.RuntimePlace.layout
    layoutOf := fun _ tyId st =>
      match refLayoutOfTyId types tyId with
      | .ok l => .ok l st
      | .error e => .error e st
    pointeeType := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    integerKind := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    usizeLayout := fun _ st =>
      .ok (refLocalLayoutForTy types (.int .isize false)) st
    isizeLayout := fun _ st =>
      .ok (refLocalLayoutForTy types (.int .isize true)) st
    readImmediate := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    evalOperand := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    writeImmediate := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    writePointer := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    copyOp := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    placeToOp := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    placePointer := fun _ => .error (.unsupported "intrinsics unsupported")
    derefPointer := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    immPointerToPlace := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    dynamicSizeAlign := fun _ _ st => .ok none st
    scalarOps := scalarOps
    floatOps := floats
    applyFloatNondeterminism := fun _ v st => .ok v st
    chooseEqualFloatRight := fun _ _ _ st => .ok false st
    fuseMulAdd := fun _ st => .ok false st
    floatFastError := fun _ v _ st => .ok v st
    checkAlign := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    memCopy := fun _ _ _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    writeBytes := fun _ _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    readBytesStripProvenance := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    allocateStack := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    deallocateStack := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    enforceValidity := fun _ _ st => .ok true st
    enforceValidityRecursively := fun _ _ st => .ok false st
    validatePlace := fun _ _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    tryAllocId := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    checkSignedAccess := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    vtableSizeAlign := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    readDiscriminant := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    discriminantForVariant := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    variantLayout := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    ensureMonomorphic := fun _ _ st => .ok () st
    typeNameConstant := fun _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    needsDrop := fun _ _ st => .ok false st
    variantCount := fun _ _ st => .ok 0 st
    callerLocationConstant := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    chooseStaticKnown := fun _ st => .ok false st
    catchUnwind := fun _ _ _ _ _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    returnToBlock := fun _ _ st =>
      .error (.unsupported "intrinsics unsupported") st
    mathHooks := none
  }

/-- Resolve a parity-tagged function item (`fnTag = 2 * defId` for crate bodies,
`2 * opCode + 1` for pinned `core::num` sysroot ops) to its
`(RefBody, localTys)`. -/
noncomputable def refResolveCalleeBody (rp : RefProg) (fnTag : Nat) :
    Option (RefBody × List MirTy) :=
  if Nat.mod fnTag 2 == 0 then
    match MirSemantics.getElem? rp.bodies (Nat.div fnTag 2) with
    | none => none
    | some rbody =>
      match decodeLocalTys rp.types rbody.locals with
      | none => none
      | some localTys => some (rbody, localTys)
  else
    match sysrootNumOpOfCode (Nat.div fnTag 2) with
    | none => none
    | some op =>
      let rbody := sysrootNumRefBody rp.types op
      let ty := .int op.width op.signed
      some (rbody, [ty, ty, ty])

/-- Construct the canonical `Miri.ABI.FnAbi TyId` for `(rbody, localTys)`. -/
noncomputable def refFnAbiOfBody (types : List MirTy) (rbody : RefBody)
    (localTys : List MirTy) :
    Except Miri.Interpreter.StepError (Miri.ABI.FnAbi Miri.MIR.TyId) :=
  let paramTys := (localTys.drop 1).take rbody.argumentCount
  if paramTys.length != rbody.argumentCount then
    .error (.unsupported "callee missing parameter types")
  else
    match MirSemantics.getElem? localTys 0 with
    | none => .error (.unsupported "callee missing return type")
    | some retTy =>
      let argAbis :=
        (paramTys.map (fun ty =>
          ({ layout := refLocalLayoutForTy types ty
             mode := .Direct Miri.ABI.ArgAttributes.new } :
            Miri.ABI.ArgAbi Miri.MIR.TyId))).toArray
      let retAbi : Miri.ABI.ArgAbi Miri.MIR.TyId := {
        layout := refLocalLayoutForTy types retTy
        mode := .Direct Miri.ABI.ArgAttributes.new
      }
      .ok {
        args := argAbis
        ret := retAbi
        cVariadic := false
        fixedCount := 0
        conv := .Rust
        canUnwind := false
      }

/-- Panic lang-item handler for `refExecutionConfig`:
- `.PanicMisalignedPointerDereference` and `.PanicNullPointerDereference`
  trigger `.undefinedBehavior` (`.ub`);
- the 5 non-optional safe panic lang items (`.PanicBoundsCheck`,
  `.PanicDivOverflow`, `.PanicRemOverflow`, `.PanicDivZero`, `.PanicRemZero`)
  cleanly terminate execution via `.termination (.abort "panic abort")` iff
  `rp.hasLocalPanicHandler = false`, `rp.panicStrategy = .abort`, and the
  active `Assert` terminator has a non-cleanup unwind action (failing closed
  with `.unsupported` otherwise);
- all other lang items (including optional overflow checks
  `Panic{Add,Sub,Mul,Neg,Shr,Shl}Overflow`) fail closed with `.unsupported`. -/
noncomputable def refPanicLangItem (rp : RefProg) (_c : Choice)
    (item : Miri.Interpreter.Panic.LangItem)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser) :
    EStateM.Result Miri.Interpreter.StepError
      (Miri.Interpreter.MachineHooks.State Unit RefUser)
      (Option Miri.MIR.DefId) :=
  match item with
  | .PanicMisalignedPointerDereference | .PanicNullPointerDereference =>
    .error (.undefinedBehavior "panic on misaligned or null pointer dereference") st
  | .PanicBoundsCheck | .PanicDivOverflow | .PanicRemOverflow
  | .PanicDivZero | .PanicRemZero =>
    if rp.hasLocalPanicHandler then
      .error (.unsupported "crate-local panic_handler unsupported") st
    else
      match rp.panicStrategy with
      | .unwind => .error (.unsupported "panic unwind unsupported") st
      | .abort =>
        match st.stack.currentFrame? with
        | some frame =>
          match frame.location with
          | .mir loc =>
            match frame.body.basicBlocks[loc.block]? with
            | some bb =>
              match bb.terminator.kind with
              | .Assert _ _ _ _ (.Cleanup _) =>
                .error (.unsupported "panic assert cleanup unsupported") st
              | .Assert _ _ _ _ _ =>
                .error (.termination (.abort "panic abort")) st
              | _ => .error (.unsupported "unexpected non-assert terminator") st
            | none => .error (.invalidBlock loc.block) st
          | .unwinding _ => .error (.unsupported "panic during unwind unsupported") st
        | none => .error (.stack .emptyStack) st
  | _ => .error (.unsupported "unsupported panic language item") st

/-- Canonical `Miri.Interpreter.ExecutionMachine.Config` for `rp : RefProg`,
with `deinitMovedPlace := true` and real `ValidityMemory.bind` shallow
validation. -/
noncomputable def refExecutionConfig (rp : RefProg) :
    Miri.Interpreter.ExecutionMachine.Config Unit RefUser Choice Unit Unit
      Unit :=
  let types := rp.types
  {
    access := refAccessConfig
    allocation := refAllocationConfig
    compiler := refCompilerHooks types
    projection := refPlaceProjectionHooks types
    operands := refOperandLeaves types
    copy := refPlaceCopyHooks
    retag := refRetagHooks
    validity := refValidityHooks types
    validationRecursive := fun _ _ st => .ok false st
    lifecycle := refLifecycle types
    functions := {
      registry := fun _ => Miri.Interpreter.FunctionPointers.Registry.empty
      putRegistry := fun u _ => u
      crossCrateInlineAlways := false
      inlineNever := fun _ st => .ok false st
      chooseSalt := fun st => .error (.unsupported "fnPtr unsupported") st
      ptrGetAlloc := fun _ st => .ok none st
      adjustRootPointer := fun allocId tag st =>
        .ok ⟨Miri.ABI.Size.ZERO, .concrete allocId tag⟩ st
      importedFunction := fun _ st => .ok none st
    }
    calls := {
      compiler := {
        functionSignature := fun _ layout st =>
          if Nat.blt layout.ty (fnTyBase types) then
            .error (.unsupported "invalid callee TyId") st
          else
            let fnTag := layout.ty - fnTyBase types
            match refResolveCalleeBody rp fnTag with
            | none => .error (.unsupported "missing callee signature") st
            | some (rbody, _) => .ok (rbody.argumentCount, ()) st
        functionKind := fun tyId st =>
          if Nat.blt tyId (fnTyBase types) then
            .error (.unsupported "invalid callee TyId") st
          else
            .ok (.FnDef (tyId - fnTyBase types) Array.empty) st
        resolve := fun _ defId _ st =>
          .ok { kind := .Item defId, args := Array.empty } st
        fnAbiOfFnPtr := fun _ _ _ st =>
          .error (.unsupported "fnPtr calls unsupported on Day 1") st
        fnAbiOfInstance := fun _ fnInstance extra st =>
          if !extra.isEmpty then
            .error (.unsupported "variadic calls unsupported") st
          else
            match fnInstance.kind with
            | .Item fnTag =>
              match refResolveCalleeBody rp fnTag with
              | none => .error (.unsupported "missing callee ABI") st
              | some (rbody, localTys) =>
                match refFnAbiOfBody types rbody localTys with
                | .ok abi => .ok abi st
                | .error e => .error e st
            | _ => .error (.unsupported "non-Item call unsupported") st
        isRustCall := fun _ => false
        rustAbi := ()
        checkArgumentCompat := fun _ callerAbi calleeAbi st =>
          .ok (decide (callerAbi == calleeAbi)) st
        targetFeatures := {
          required := fun _ st => .ok Array.empty st
          available := fun _ st => .ok true st
          isLikeWasm := fun st => .ok false st
        }
        tupleFields := fun _ st => .ok Array.empty st
        isClosureLike := fun _ st => .ok false st
        closureUpvarCount := fun _ st => .ok none st
        llvmLinkName := fun _ st => .ok "" st
      }
      dispatch := {
        foreign := none
        returnToBlock := fun _ st =>
          .error (.unsupported "foreign/intrinsic returnToBlock unsupported") st
        isForeignItem := fun _ st => .ok false st
        symbolName := fun _ st => .ok "" st
        loadMir := fun _ fnInstance st =>
          match fnInstance.kind with
          | .Item fnTag =>
            match refResolveCalleeBody rp fnTag with
            | none => .error (.unsupported "missing callee MIR") st
            | some (rbody, _) =>
              .ok {
                identity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex fnTag
                body := toMiriBody types rbody
              } st
          | _ => .error (.unsupported "non-Item loadMir unsupported") st
        backend := { selection := fun _ => .ok .none }
        dynSymName := fun _ => ""
        foreignScope := fun act => act
      }
      llvm := fun _ st =>
        .error (.unsupported "llvm intrinsics unsupported on Day 1") st
    }
    virtual := {
      compiler := {
        classifyReceiver := fun _ st => .ok .other st
        fieldLayout := fun _ _ st =>
          .error (.unsupported "virtual calls unsupported on Day 1") st
        structTailForCodegen := fun _ st =>
          .error (.unsupported "virtual calls unsupported on Day 1") st
        dynamicData := fun _ st => .ok none st
        mutPointerType := fun _ st =>
          .error (.unsupported "virtual calls unsupported on Day 1") st
        mutReferenceType := fun _ st =>
          .error (.unsupported "virtual calls unsupported on Day 1") st
        builtinDeref := fun _ st => .ok none st
        layoutOf := fun tyId st =>
          match refLayoutOfTyId types tyId with
          | .ok l => .ok l st
          | .error e => .error e st
        parentTrait := fun _ st =>
          .error (.unsupported "virtual calls unsupported on Day 1") st
        rebaseVirtualArgs := fun _ _ _ st =>
          .error (.unsupported "virtual calls unsupported on Day 1") st
        expectResolveForVTable := fun _ _ _ st =>
          .error (.unsupported "virtual calls unsupported on Day 1") st
        resolveDropGlue := fun _ st =>
          .error (.unsupported "drop glue unsupported on Day 1") st
        requiresCallerLocation := fun _ st => .ok false st
        sourceScope := fun _ _ _ _ st => .ok ⟨none, none⟩ st
        unitLayout := fun st => .ok (refLocalLayoutForTy types .unit) st
      }
      vtable := refVTableHooks
      alignment := {
        policy := fun _ => .None
        promises := fun _ => Array.empty
      }
    }
    helpers := {
      loadMir := fun _ _ st =>
        .error (.unsupported "calls unsupported on Day 1") st
      unitLayout := refLocalLayoutForTy types .unit
      fnAbiOfSignature := fun _ _ st =>
        .error (.unsupported "calls unsupported on Day 1") st
      callerLocationType := fun st =>
        .error (.unsupported "callerLocation unsupported on Day 1") st
      dummySpan := ⟨0⟩
    }
    control := { bodySpan := fun _ => .ok ⟨0⟩ }
    panic := {
      driver := {
        payloads := fun _ => Miri.Interpreter.Unwind.PayloadStore.empty
        setPayloads := fun _ u => u
        -- `Miri.Interpreter.Panic.assertPanic` reads diagnostic immediate
        -- operands on `BoundsCheck` / `MisalignedPointerDereference` before
        -- calling the panic lang item; `callFunction` and `readPointer` stay
        -- fail-closed as `.unsupported`.
        readImmediate := fun _ op st =>
          Miri.Interpreter.PlaceMachine.readImmediate refAccessConfig op st
        readPointer := fun _ _ st =>
          .error (.unsupported "panic unsupported on Day 1") st
        forceAllocation := fun _ _ st =>
          .error (.unsupported "panic unsupported on Day 1") st
        getPtrFn := fun _ _ st =>
          .error (.unsupported "panic unsupported on Day 1") st
        callFunction := fun _ _ _ _ st =>
          .error (.unsupported "panic unsupported on Day 1") st
        writeNull := fun _ _ st =>
          .error (.unsupported "panic unsupported on Day 1") st
        writeScalar := fun _ _ _ st =>
          .error (.unsupported "panic unsupported on Day 1") st
        panicUnwinds := false
      }
      allocateStringDedup := fun _ _ st =>
        .error (.unsupported "panic unsupported on Day 1") st
      toImmediatePointer := fun _ _ st =>
        .error (.unsupported "panic unsupported on Day 1") st
      langItem := refPanicLangItem rp
      genericParameters := fun _ _ st => .ok Array.empty st
      evalOperand := fun _ _ st =>
        .error (.unsupported "panic unsupported on Day 1") st
    }
    unwindTerminateFunction := fun _ _ st =>
      .error (.unsupported "unwindTerminate unsupported on Day 1") st
    -- `ignoreOptionalOverflowChecks = false` keeps optional overflow checks
    -- at `.unsupported` in both models rather than skipping to `target`.
    ignoreOptionalOverflowChecks := false
    rvalues := {
      threadLocalPointer := fun _ _ st =>
        .error (.unsupported "ThreadLocalRef unsupported on Day 1") st
      normalize := fun _ ty st => .ok ty st
    }
    discriminant := refDiscriminantLeaves types
    scalar := refScalarLeaves types
    floats := refFloatOpsHooks types
    casts := refCastLeaves types
    backend := { selection := fun _ => .ok .none }
    atomics := refAtomicAccessHooks types
    varArgs := refVarArgsHooks
    intrinsics := fun _ => refIntrinsicHooks types
    intrinsicName := fun _ st => .ok "" st
    intrinsicMustOverride := fun _ st => .ok true st
    intrinsicFallbackIsSpec := fun _ st => .ok false st
    addresses := fun _ => refEmptyAddressState
    arithmetic := refPointerArithmetic
    isRawPointer := fun _ _ st => .ok false st
    usizeLayout := fun _ st =>
      .ok (refLocalLayoutForTy types (.int .isize false)) st
    pointeeLayout := fun _ _ st =>
      .error (.unsupported "pointeeLayout unsupported on Day 1") st
    terminators := refTerminatorMachineHooks
    preemptionChoice := fun _ st => .ok false st
    deinitMovedPlace := true
  }

end Trusted.Correspondence
