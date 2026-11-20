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
import Trusted.Correspondence.State

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Reference Step Engine and Trace Predicates (`Trusted.Correspondence.Eval`)

Defines `evalRefStep`, `Miri.Interpreter` hook adapters, and reference
reachability/behavior predicates (`RefStep`, `RefReaches`, `RefReachesOutcome`,
`RefWellFormed`, `RefBehavior`, `RefDiverges`). Imports only `Trusted.MirAst`
and `Trusted.MirModel`, never `Trusted.MirSemantics`.
-/

/-! ### `Miri.Interpreter` Evaluator Wiring Adapters -/

/-- Canonical 8-byte sized `Miri.Interpreter.LocalLayout` (`isZst = false`) used
as a fixed placeholder at adapter sites that do not branch on per-type size.

Authoritative call-site list: `mkSingleLocalMiriFrame` (which feeds
`mkRefStepStateWith`, `refTerminatorHooksFor.popFrame`, `writeRefPlace`, and
`refStepHooksFor.storageLive`), `mkTwoLocalMiriFrame` (which feeds
`refStepHooksFor.storageDead`), `writeRefPlace`, `refLocalAccessHooks.layout`,
`refLocalStorageHooks.layout`,
`refRvalueHooks.{placeLayout,evalOperand,readImmediate,binaryOp,unaryOp}`, and
the non-ZST fallback of `refLocalLayoutForTy`. Its `ty := 0` field is an unused
placeholder inside single-local adapter frames and never indexes
`RefProg.types`. -/
noncomputable def refSizedLocalLayout : Miri.Interpreter.LocalLayout := {
  ty := 0
  layout :=
    refBaseLayoutData (.Memory (sized := true)) (Miri.ABI.Size.ofBytes 8)
}

/-- Canonical 0-byte ZST `Miri.Interpreter.LocalLayout` (`Size.ZERO`,
`isZst = true`) used for `MirTy.unit` and 1-variant ZST enum local slots. Its
`ty := 0` field is an unused placeholder inside single-local adapter frames and
never indexes `RefProg.types`. -/
noncomputable def refLocalLayoutZst : Miri.Interpreter.LocalLayout := {
  ty := 0
  layout := refBaseLayoutData (.Memory (sized := true)) Miri.ABI.Size.ZERO
}

/-- `Miri.Interpreter.LocalLayout` used by `evalRefPlaceOperand` (the sole call
site, building `mkSingleLocalMiriFrameWithLayout` for
`Miri.Interpreter.evalOperand`): 0-byte ZST (`refLocalLayoutZst`,
`isZst = true`) for `MirTy.unit` and admitted 1-variant ZST fieldless enums
(`refIsZstEnumTy`), and `refSizedLocalLayout` (`isZst = false`) for every other
local type—including non-ZST types and uninhabited `!` (`MirTy.never`). Note
that although `rustc` treats `!` as a 0-byte ZST, using `refSizedLocalLayout`
(`isZst = false`) for `.never` makes moving a `!` local take Miri's non-ZST
deinitialization path (`.live none`), and the difference is unobservable
because `!` is uninhabited and can never be initialized, read, or written.
`StorageLive` (`refStepHooksFor.storageLive`) does not call
`refLocalLayoutForTy`: it runs `Miri.Interpreter.Frame.storageLive` on a dummy
dead local `0` (where `refLocalStorageHooks.veryTriviallySized` returns
`.ok true` so `refLocalStorageHooks.layout` is skipped and the call always
returns `.ok ()`), discards the resulting Miri frame, and writes
`refLiveUninitSlot localTy` directly (whose catch-all arm initializes `!` to
`.live none`). -/
noncomputable def refLocalLayoutForTy : MirTy → Miri.Interpreter.LocalLayout
  | .unit => refLocalLayoutZst
  | .enum ety =>
    if refIsZstEnumTy ety then refLocalLayoutZst else refSizedLocalLayout
  | _ => refSizedLocalLayout

/-- Embed a typed payload `x : α` into `Miri.Interpreter.Immediate α` via
`Miri.Memory.Scalar.fromPointer` without pattern-matching on `x` so projection
back via `miriImmediateToPayload?` reduces by `rfl` even when `x` is a free
variable. -/
noncomputable def payloadToMiriImmediate {α : Type} (x : α) :
    Miri.Interpreter.Immediate α :=
  .scalar (Miri.Memory.Scalar.fromPointer ⟨.big, .w64⟩
    ⟨Miri.ABI.Size.ZERO, x⟩)

/-- Project a typed payload `α` back out of
`Miri.Interpreter.Immediate α`. -/
noncomputable def miriImmediateToPayload? {α : Type} :
    Miri.Interpreter.Immediate α → Option α
  | .scalar s =>
    match s.toBitsOrPtrInternal (Miri.ABI.Size.ofBytes 8) with
    | .ok (.pointer ptr) => some ptr.provenance
    | _ => none
  | _ => none

/-- Lift a `LocalSlot` into `Miri.Interpreter.LocalValue (Option Val)`.

Uninitialized live adapter locals (`.live none`) are stored in Miri frames as
an initialized pointer immediate carrying `none` provenance rather than
`Immediate.uninit`, so Miri's own `.uninit` check never fires on adapter frames
and uninitialized-read UB is enforced explicitly by the adapter hooks
(`readRefPrimitiveSlot`, `refRvalueHooks.copyOp`,
`refTerminatorHooksFor.copyReturn`, and `encodeRefEnumTagOp` ->
`Miri.Interpreter.Discriminant.readDiscriminant`). -/
noncomputable def slotToMiriLocalValue :
    LocalSlot → Miri.Interpreter.LocalValue (Option Val)
  | .dead => .dead
  | .live optVal => .live (.immediate (payloadToMiriImmediate optVal))

/-- Minimal `Miri.MIR.BasicBlock` with configurable `cleanup : Bool` for
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`. -/
noncomputable def refDummyMirBlock (cleanup : Bool) : Miri.MIR.BasicBlock := {
  statements := Array.empty
  terminator := { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
  cleanup := cleanup
}

/-- Minimal `Miri.MIR.Body` with two local declarations (`_0` and `_1`) and one
basic block for `Miri.Interpreter.Frame`. -/
noncomputable def refDummyMirBody (cleanup : Bool) : Miri.MIR.Body := {
  phase := .Runtime .PostCleanup
  argumentCount := 0
  spreadArgument := none
  locals := Array.mk [0, 0]
  basicBlocks := Array.mk [refDummyMirBlock cleanup]
}

/-- Construct a single-local `Miri.Interpreter.Frame` holding `lv` at local `0`
with pre-cached `layout`. -/
noncomputable def mkSingleLocalMiriFrameWithLayout
    (lv : Miri.Interpreter.LocalValue (Option Val))
    (layout : Miri.Interpreter.LocalLayout) (cleanup : Bool) :
    Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit := {
  body := refDummyMirBody cleanup
  bodyIdentity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex 0
  functionInstance := { kind := .Item 0, args := Array.empty }
  extra := ()
  returnContinuation := .stop false
  returnPlace := .frameLocal 0 0 none layout
    (Miri.Interpreter.LocalsIdentity.ofAllocationToken 0)
  localsIdentity := Miri.Interpreter.LocalsIdentity.ofAllocationToken 0
  locals := Array.mk [⟨lv, some layout⟩]
  vaList := Array.empty
  trackCallerArg := none
  location := .mir ⟨0, 0⟩
}

/-- Construct a single-local `Miri.Interpreter.Frame` holding `lv` at local `0`
with pre-cached `refSizedLocalLayout`. -/
noncomputable def mkSingleLocalMiriFrame
    (lv : Miri.Interpreter.LocalValue (Option Val)) (cleanup : Bool) :
    Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit :=
  mkSingleLocalMiriFrameWithLayout lv refSizedLocalLayout cleanup

/-- Construct a two-local `Miri.Interpreter.Frame` holding `lv₀` at `_0` and
`lv₁` at `_1` for `Miri.Interpreter.Frame.storageDead` (which forbids
`StorageDead` on return place `_0` and deallocates `_1`). -/
noncomputable def mkTwoLocalMiriFrame
    (lv₀ lv₁ : Miri.Interpreter.LocalValue (Option Val)) :
    Miri.Interpreter.Frame (Option Val) Miri.Interpreter.LocalLayout Unit := {
  mkSingleLocalMiriFrame lv₀ false with
  locals := Array.mk [⟨lv₀, some refSizedLocalLayout⟩,
                      ⟨lv₁, some refSizedLocalLayout⟩]
}

/-- Write `val` into destination local `dstLocalId` in `rlocals` via
`Miri.Interpreter.placeWriteLocalImmediate`
(`vendor/lean-miri/Miri/Interpreter/Place.lean`), preserving its cached layout
`some ty`. -/
noncomputable def writeRefPlace (rlocals : List RefLocalState)
    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List RefLocalState) :=
  if !checkRefVal val dstTy then
    .error .unsupported
  else
    match MirSemantics.getElem? rlocals dstLocalId with
    | some ⟨slot, some ty⟩ =>
      let frame₀ := mkSingleLocalMiriFrame (slotToMiriLocalValue slot) false
      match Miri.Interpreter.placeWriteLocalImmediate
          EStateM.get EStateM.set (pure true)
          (fun _ _ => pure ()) (fun _ _ => pure ())
          0 refSizedLocalLayout (payloadToMiriImmediate (some val)) frame₀ with
      | .ok () frame₁ =>
        match frame₁.getLocal 0,
            MirSemantics.setElem? rlocals dstLocalId
              ⟨.live (some val), some ty⟩ with
        | .ok ⟨.live (.immediate _), _⟩, some rlocals' => .ok rlocals'
        | .ok ⟨.live (.immediate _), _⟩, none => .error .unsupported
        | _, _ => .error .undefined
      | .error _ _ => .error .undefined
    | _ => .error .unsupported

/-- `Miri.Interpreter.LocalAccessHooks` with `deinitMovedPlace` configured for
`Miri.Interpreter.evalOperand`. -/
noncomputable def refLocalAccessHooks (deinitMovedPlace : Bool) :
    Miri.Interpreter.LocalAccessHooks (Option Val) Unit Unit := {
  layout := fun frame state _ _ => ⟨frame, state, .ok refSizedLocalLayout⟩
  validationInProgress := fun _ => true
  afterLocalRead := fun frame state _ => ⟨frame, state, .ok ()⟩
  project := fun frame state _ _ =>
    ⟨frame, state, .error (.resolver "projections unsupported on Day 1")⟩
  checkPlaceType := fun frame state _ _ => ⟨frame, state, .ok ()⟩
  runtimeChecks := fun frame state _ =>
    ⟨frame, state, .error (.resolver "runtimeChecks unsupported")⟩
  constant := fun frame state _ _ =>
    ⟨frame, state, .error (.resolver "constant handled via evalRefConstLit")⟩
  deinitMovedPlace := deinitMovedPlace
}

/-- Evaluate an unprojected `.Copy` or `.Move` local operand via
`Miri.Interpreter.evalOperand` (`deinitMovedPlace = true`), projecting both the
read `Option Val` and (when `isMove = true`) the post-move `LocalSlot` from the
updated `Miri.Interpreter.Frame`: non-ZST moves derive `.live none` from Miri's
`.immediate .uninit`, while `outLayout.layout.isZst` (`MirTy.unit` and admitted
1-variant ZST enums) uses `refLiveUninitSlot`. -/
noncomputable def evalRefPlaceOperand (rlocals : List RefLocalState)
    (localId : LocalId) (projEmpty : Bool) (isMove : Bool) :
    Except FaultKind (MirTy × Option Val × List RefLocalState) :=
  if !projEmpty then
    .error .unsupported
  else
    match MirSemantics.getElem? rlocals localId with
    | some ⟨slot, some ty⟩ =>
      let layout := refLocalLayoutForTy ty
      let frame₀ :=
        mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue slot) layout
          false
      let mirOp : Miri.MIR.Operand :=
        if isMove then .Move ⟨0, Array.empty⟩ else .Copy ⟨0, Array.empty⟩
      match Miri.Interpreter.evalOperand (refLocalAccessHooks true) frame₀ ()
          mirOp (some layout) with
      | ⟨frame₁, _, .ok ⟨.immediate imm, outLayout⟩⟩ =>
        let optVal : Option Val :=
          match miriImmediateToPayload? imm with
          | some v => v
          | none => none
        if !isMove then
          .ok (ty, optVal, rlocals)
        else
          let postSlot? : Option LocalSlot :=
            match frame₁.getLocal 0 with
            | .ok ⟨.live (.immediate .uninit), _⟩ => some (.live none)
            | .ok ⟨.live (.immediate _), _⟩ =>
              if outLayout.layout.isZst then some (refLiveUninitSlot ty)
              else none
            | _ => none
          match postSlot? with
          | some postSlot =>
            match MirSemantics.setElem? rlocals localId ⟨postSlot, some ty⟩ with
            | some rlocals' => .ok (ty, optVal, rlocals')
            | none => .error .unsupported
          | none => .error .undefined
      | _ => .error .undefined
    | _ => .error .unsupported

/-- Map `RefPlace` to `Miri.MIR.Place` (preserving `localId` and marking any
non-empty projection so unprojected local checks reject projected accesses
fail-closed). -/
noncomputable def toMiriPlace (rp : RefPlace) : Miri.MIR.Place :=
  ⟨rp.localId,
    if rp.projection.isEmpty then Array.empty else Array.mk [.Deref]⟩

/-- Map `RefOperand` to `Miri.MIR.Operand` so
`Miri.Interpreter.evalRvalueIntoPlace` and
`Miri.Interpreter.ControlFlow.evalTerminator` receive real operands.

For scalar constants, `.Scalar (.Int bits.toNat 16)` uses `sizeBytes := 16` as
a uniform 128-bit `BitVec` carrier (`bits.toNat` round-trips losslessly through
`BitVec.ofNat 128` in `evalRefMiriOperandToSlot`), and `c.ty` is the real
`RefProg.types` index resolved by `evalRefMiriOperandToSlot` (unlike the
private sentinel `TyId`s `0`/`1` inside `refSizedLocalLayout`,
`refLocalLayoutZst`, and `refDiscriminantHooks`, which never index
`RefProg.types`). -/
noncomputable def toMiriOperand : RefOperand → Miri.MIR.Operand
  | .copy rp => .Copy (toMiriPlace rp)
  | .move rp => .Move (toMiriPlace rp)
  | .constant c =>
    let cv : Miri.MIR.ConstValue :=
      match c.lit with
      | .scalar bits => .Scalar (.Int bits.toNat 16)
      | .zeroSized => .ZeroSized
    .Constant ⟨⟨0⟩, none, .Val cv c.ty⟩

/-- Map `RefRvalue` to `Miri.MIR.Rvalue` for
`Miri.Interpreter.Step.evalStatement` and
`Miri.Interpreter.evalRvalueIntoPlace`.

Day-1 supported rvalues (`.use`, `.binaryOp`, `.unaryOp`, `.discriminant`) and
Day-1 unmodeled AST rvalues (`.ref`, `.addressOf`, `.aggregateTuple`) translate
to their real `Miri.MIR.Rvalue` constructors so `evalRvalueIntoPlace` routes
them through its real dispatch arms (`forceAllocation` for `.ref`/`.addressOf`
and `writeAggregate` for `.aggregateTuple`). `.unsupported` uses
`.CopyForDeref ⟨0, Array.empty⟩` as a fail-closed sentinel that
`evalRvalueIntoPlace` rejects directly with `.invalidProgram` (`.fault
.unsupported`). -/
noncomputable def toMiriRvalue : RefRvalue → Miri.MIR.Rvalue
  | .use op => .Use (toMiriOperand op) .No
  | .binaryOp op lhs rhs =>
    .BinaryOp (toMiriBinOp op) (toMiriOperand lhs) (toMiriOperand rhs)
  | .unaryOp op opnd =>
    .UnaryOp (toMiriUnOp op) (toMiriOperand opnd)
  | .discriminant rp => .Discriminant (toMiriPlace rp)
  | .ref .shared rp => .Ref .Erased .Shared (toMiriPlace rp)
  | .ref .mut rp => .Ref .Erased (.Mut .Default) (toMiriPlace rp)
  | .addressOf .shared rp => .RawPtr .Const (toMiriPlace rp)
  | .addressOf .mut rp => .RawPtr .Mut (toMiriPlace rp)
  | .aggregateTuple ops =>
    .Aggregate .Tuple (Array.mk (ops.map toMiriOperand))
  | .unsupported => .CopyForDeref ⟨0, Array.empty⟩

/-- Stage 1 of reference operand evaluation over `Miri.MIR.Operand` (shared by
`refRvalueHooks.evalOperand` and `refTerminatorHooksFor.evalDiscriminant`),
calling `Miri.Interpreter.evalOperand`
(`vendor/lean-miri/Miri/Interpreter/LocalAccess.lean`) with
`deinitMovedPlace = true`.

Upstream `eval_operand` evaluates `Move` exactly like `Copy` and leaves move
invalidation unimplemented:

> "let op = match mir_op {
>     // FIXME: do some more logic on `move` to invalidate the old location
>     &Copy(place) | &Move(place) => self.eval_place_to_op(place, layout)?,
>     ...
>     Constant(constant) => {
>         ... self.eval_mir_constant(&c, constant.span, layout)?
>     }
> };"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

`deinitMovedPlace = true` is therefore not `rustc@8144389c` behavior: it is
Anneal's deliberately stricter move-deinitialization rule, implemented by
Anneal's own opt-in `vendor/lean-miri` patch on top of `lean-miri@c92d1d97`
and mirrored by `Trusted.MirSemantics.evalOperandToSlot` in
$M_{\text{anneal}}$. Moving a non-ZST local leaves it uninitialized, so a later
read of that local faults with UB. This over-approximates upstream UB, which is
sound because deinitializing a local can only add faults on later reads.
Canaries `D6`–`D9` (`CanaryD6UseAfterMoveUbClaim` through
`CanaryD9MoveUnitZstOkClaim`) are self-consistency canaries of this stricter
rule: they check that $M_{\text{anneal}}$ and $M_{\text{ref}}$ agree on it,
not that either model matches upstream Miri or MiniRust.

Delegates `.Copy` and `.Move` on unprojected live locals to
`evalRefPlaceOperand` (`Miri.Interpreter.evalOperand` with
`refLocalLayoutForTy ty`), and decodes `.Constant` via `types[tyId]?` and
`evalRefConstLit` (ignoring the carrier `sizeBytes` field). -/
noncomputable def evalRefMiriOperandToSlot (types : List MirTy)
    (rlocals : List RefLocalState) :
    Miri.MIR.Operand →
      Except FaultKind (MirTy × Option Val × List RefLocalState)
  | .Copy place =>
    evalRefPlaceOperand rlocals place.localId place.projection.isEmpty false
  | .Move place =>
    evalRefPlaceOperand rlocals place.localId place.projection.isEmpty true
  | .Constant ⟨_, _, .Val (.Scalar (.Int bitsNat _)) tyId⟩ =>
    match MirSemantics.getElem? types tyId with
    | none => .error .unsupported
    | some ty =>
      match evalRefConstLit ty (.scalar (BitVec.ofNat 128 bitsNat)) with
      | .ok v => .ok (ty, some v, rlocals)
      | .error k => .error k
  | .Constant ⟨_, _, .Val .ZeroSized tyId⟩ =>
    match MirSemantics.getElem? types tyId with
    | none => .error .unsupported
    | some ty =>
      match evalRefConstLit ty .zeroSized with
      | .ok v => .ok (ty, some v, rlocals)
      | .error k => .error k
  | _ => .error .unsupported

/-- Stage 2A of reference operand evaluation (shared by
`refRvalueHooks.readImmediate` and `refTerminatorHooksFor.evalDiscriminant`):
checks `refIsPrimitiveReadableTy ty` before inspecting `optVal` for uninit UB,
matching `Miri.Interpreter.readImmediate`
(`vendor/lean-miri/Miri/Interpreter/MemoryOperand.lean`) and `read_immediate`
in `compiler/rustc_const_eval/src/interpret/operand.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`), which reports reading an
uninitialized immediate as UB:

> "let imm = self.read_immediate_raw(op)?.right().unwrap();
> if matches!(*imm, Immediate::Uninit) {
>     throw_ub!(InvalidUninitBytes(None));
> }"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Adapter frames never store `Immediate.uninit` (see `slotToMiriLocalValue`), so
Miri's own check never fires on them and this Anneal-written rule enforces the
UB directly: `optVal = none` faults with `.undefined`. -/
noncomputable def readRefPrimitiveSlot (ty : MirTy) (optVal : Option Val) :
    Except FaultKind Val :=
  if !refIsPrimitiveReadableTy ty then
    .error .unsupported
  else
    match optVal with
    | some v => .ok v
    | none => .error .undefined

/-- Lift `FaultKind` into `Miri.Interpreter.StepError` inside `RvalueM`. -/
noncomputable def faultToStepError : FaultKind → Miri.Interpreter.StepError
  | .undefined => .undefinedBehavior "reference UB"
  | .unsupported => .unsupported "reference unsupported"

/-- Re-encode a fieldless enum's `(ety, optVal)` slot payload into a
`Miri.Interpreter.OpTy Miri.Memory.Provenance` (`.uninit` for `.zeroSized` or
uninitialized scalar tags, and `Miri.Memory.ScalarInt.truncateFromUInt` for
initialized scalar tags) for `Miri.Interpreter.Discriminant.readDiscriminant`.
-/
noncomputable def encodeRefEnumTagOp (ety : EnumTy) (optVal : Option Val) :
    Except Miri.Interpreter.StepError
      (Miri.Interpreter.OpTy Miri.Memory.Provenance) :=
  let layout : Miri.Interpreter.LocalLayout := ⟨0, refEnumLayoutData ety⟩
  match ety.tagRepr, optVal with
  | .zeroSized, none => .ok ⟨.immediate .uninit, layout⟩
  | .zeroSized, some (.enumVal ety' v) =>
    if EnumTy.beq ety ety' && Nat.beq v 0 then
      .ok ⟨.immediate .uninit, layout⟩
    else
      .error (.unsupported "mismatched ZST enum variant in slot")
  | .zeroSized, some _ =>
    .error (.unsupported "non-enum value in ZST enum slot")
  | .scalar _ _, none => .ok ⟨.immediate .uninit, layout⟩
  | .scalar tagW _, some (.enumVal ety' v) =>
    if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
      match MirSemantics.getElem? ety.discriminants v with
      | some disc =>
        match Miri.Memory.ScalarInt.truncateFromUInt
            (BitVec.ofNat 128 disc) (toMiriSize tagW) with
        | .ok (tagSc, _) =>
          .ok ⟨.immediate (.scalar (.fromScalarInt tagSc)), layout⟩
        | .error _ => .error (.invalidProgram "enum tag truncate failure")
      | none => .error (.invalidProgram "missing enum discriminant")
    else
      .error (.unsupported "mismatched scalar enum variant in slot")
  | .scalar _ _, some _ =>
    .error (.unsupported "non-enum value in scalar enum slot")

/-- Evaluate an unprojected enum local `src` to
`Miri.Interpreter.OpTy (MirTy × Option Val)` via
`Miri.Interpreter.evalPlaceToOp` (`Miri.Interpreter.localToOp`) for
`RvalueHooks.evalPlaceToOp` (`.Discriminant src`), returning layout
`⟨enumTyId, refEnumLayoutData ety⟩` where `enumTyId` is the real
`RefProg.types` index of `.enum ety` (forwarded by Miri as `op.layout.ty` to
`discriminantForVariant`). -/
noncomputable def evalRefEnumPlaceToOp (types : List MirTy)
    (src : Miri.MIR.Place) (rlocals : List RefLocalState) :
    EStateM.Result Miri.Interpreter.StepError (List RefLocalState)
      (Miri.Interpreter.OpTy (MirTy × Option Val)) :=
  if !src.projection.isEmpty then
    .error (.unsupported "projected Discriminant unsupported") rlocals
  else
    match MirSemantics.getElem? rlocals src.localId with
    | some ⟨slot, some (.enum ety)⟩ =>
      if !refEnumAdmitted ety then
        .error (.unsupported "unadmitted enum in Discriminant") rlocals
      else
        match indexOfTy types (.enum ety) with
        | none =>
          .error (.unsupported "enum type missing from type table") rlocals
        | some enumTyId =>
          let layout : Miri.Interpreter.LocalLayout :=
            ⟨enumTyId, refEnumLayoutData ety⟩
          let frame₀ :=
            mkSingleLocalMiriFrameWithLayout (slotToMiriLocalValue slot) layout
              false
          match (Miri.Interpreter.evalPlaceToOp (refLocalAccessHooks false)
              frame₀ () ⟨0, Array.empty⟩ (some layout)).outcome with
          | .error (.stack stackErr) => .error (.stack stackErr) rlocals
          | .error _ => .error (.unsupported "evalPlaceToOp failed") rlocals
          | .ok ⟨.indirect _, _⟩ =>
            .error (.unsupported "indirect enum local unsupported") rlocals
          | .ok ⟨.immediate imm, _⟩ =>
            let optVal : Option Val :=
              match miriImmediateToPayload? imm with
              | some v => v
              | none => none
            .ok ⟨.immediate (payloadToMiriImmediate (.enum ety, optVal)),
              layout⟩ rlocals
    | _ => .error (.unsupported "Discriminant on non-enum local") rlocals

/-- `Miri.Interpreter.RvalueHooks` closing over only `types : List MirTy`,
instantiated with provenance carrier `MirTy × Option Val`, state
`List RefLocalState`, and place value `LocalId × MirTy` to drive real
`Miri.MIR.Rvalue`, `Miri.MIR.Operand`, and `Miri.MIR.Place` terms through
`Miri.Interpreter.evalRvalueIntoPlace` and `Miri.Interpreter.Discriminant`
(`vendor/lean-miri/Miri/Interpreter/{Rvalue,Discriminant}.lean`).

Value and type transport: `evalOperand` and `evalPlaceToOp` embed
`(MirTy, Option Val)` directly into Miri's `Immediate (MirTy × Option Val)`
carrier via `payloadToMiriImmediate`; `readImmediate`, `copyOp`, `binaryOp`,
`unaryOp`, `readDiscriminant`, and `writeImmediate` decode the `Immediate` /
`OpTy` arguments Miri passes them via `miriImmediateToPayload?`; `copyOp`
checks `MirTy.beq` and commits to `dest : LocalId × MirTy` via `writeRefPlace`;
and `writeImmediate` discards the `MirTy` tag carried in the `Immediate`
payload (so the result `MirTy` tags attached by `binaryOp`, `unaryOp`, and
`discriminantForVariant` are unconsumed, and `assertRvalueLayout` over constant
`refSizedLocalLayout` is vacuous) and relies on `writeRefPlace` (`checkRefVal`)
as the effective result-type check against `dest.2`. For `.Discriminant`,
`evalPlaceToOp` carries the enum's real `RefProg.types` index in `op.layout.ty`,
`readDiscriminant` re-encodes the decoded enum payload at
`Miri.Memory.Provenance` via `encodeRefEnumTagOp`, and `discriminantForVariant`
resolves `types[ty]?` from Miri's forwarded `ty` parameter before calling
`Miri.Interpreter.Discriminant.discriminantForVariant` at the closed hook's
private `TyId 0`—so the rvalue state is plain `List RefLocalState` with no
call-order side-channel fields.

Day-1 hook coverage: `.use`, `.binaryOp`, `.unaryOp`, and `.discriminant`
exercise `evalPlace`, `placeLayout`, `evalOperand`, `evalPlaceToOp`,
`readImmediate`, `copyOp`, `binaryOp`, `unaryOp`, `readDiscriminant`,
`discriminantForVariant`, `writeImmediate`, and `withRetagMode`. `.ref` and
`.addressOf` fail closed in `forceAllocation` (after `placeBaseRaw` and
`evalPlace`), and `.aggregateTuple` fails closed in `writeAggregate`. The
remaining `RvalueHooks` fields (`writePointer`, `threadLocalPointer`,
`copyOpAllowTransmute`, `writeRepeat`, `toRef`, `enforceValidity`,
`retagPtrValue`, `normalize`, `cast`) are required by the `RvalueHooks` record
but unreachable under the Day-1 `RefRvalue` fragment (`toRef`,
`enforceValidity`, and `retagPtrValue` are gated behind `forceAllocation`).

Uninitialized-read UB in `copyOp`: adapter frames never store
`Immediate.uninit` (see `slotToMiriLocalValue`), so `copyOp` itself rejects an
uninitialized `.use` operand (`optVal = none` faults with `.undefined`). This
Anneal-written rule matches `Rvalue::Use` in `rustc`, which copies the operand
with `copy_op`:

> "Use(ref operand, with_retag) => {
>     ...
>     let op = self.eval_operand(operand, Some(dest.layout))?;
>     ...
>     M::with_retag_mode(self, mode, |ecx| ecx.copy_op(&op, &dest))?;
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

`copy_op` validates the copied value whenever the machine enforces validity.
Miri does so by default: `MiriConfig::default()` sets
`validation: ValidationMode::Shallow` (`src/eval.rs`), and Miri's
`enforce_validity` returns `ecx.machine.validation != ValidationMode::No`
(`src/machine.rs`, `rust-lang/miri`
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):

> "self.copy_op_no_validate(src, dest, allow_transmute)?;
>
> if M::enforce_validity(self, dest.layout()) {
>     ...
>     self.validate_place(
>         &dest,
>         M::enforce_validity_recursively(self, dest.layout()),
>         /*reset_provenance_and_padding*/ true,
>     )?;
> }"
> (`compiler/rustc_const_eval/src/interpret/place.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Validation reads each `bool` and integer value through `read_immediate`
(quoted at `readRefPrimitiveSlot`) and reports its `InvalidUninitBytes` UB as
an `Uninit` validation failure, which is itself UB:

> "interp_ok(try_validation!(
>     self.ecx.read_immediate(val),
>     self.path,
>     Ub(InvalidUninitBytes(_)) =>
>         Uninit { expected },
>     ...
> ))"
> (`compiler/rustc_const_eval/src/interpret/validity.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def refRvalueHooks (types : List MirTy) :
    Miri.Interpreter.RvalueHooks (MirTy × Option Val) (List RefLocalState) Unit
      (LocalId × MirTy) := {
  placeLayout := fun _ => refSizedLocalLayout
  evalPlace := fun _ place _ s =>
    if !place.projection.isEmpty then
      .error (.unsupported "projected place unsupported") s
    else
      match MirSemantics.getElem? s place.localId with
      | some ⟨_, some ty⟩ => .ok (place.localId, ty) s
      | _ => .error (.unsupported "missing destination local") s
  evalOperand := fun _ mirOp _ s =>
    match evalRefMiriOperandToSlot types s mirOp with
    | .error k => .error (faultToStepError k) s
    | .ok (ty, optVal, locals') =>
      .ok ⟨.immediate (payloadToMiriImmediate (ty, optVal)),
          refSizedLocalLayout⟩
        locals'
  evalPlaceToOp := fun _ src _ s =>
    evalRefEnumPlaceToOp types src s
  readImmediate := fun _ op s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (ty, optVal) =>
        match readRefPrimitiveSlot ty optVal with
        | .error k => .error (faultToStepError k) s
        | .ok v =>
          .ok ⟨payloadToMiriImmediate (ty, some v), refSizedLocalLayout⟩ s
      | none => .error (.invalidProgram "missing operand payload") s
    | .indirect _ => .error (.unsupported "indirect operand unsupported") s
  writeImmediate := fun _ imm dest s =>
    match miriImmediateToPayload? imm with
    | some (_, some v) =>
      match writeRefPlace s dest.1 dest.2 v with
      | .error k => .error (faultToStepError k) s
      | .ok locals' => .ok () locals'
    | _ => .error (.invalidProgram "missing rvalue result payload") s
  writePointer := fun _ _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  threadLocalPointer := fun _ _ s =>
    .error (.unsupported "ThreadLocalRef unsupported") s
  withRetagMode := fun _ _ act => act
  copyOp := fun _ op dest s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (srcTy, optVal) =>
        if !(MirTy.beq srcTy dest.2) then
          .error (.unsupported "Use type mismatch") s
        else
          -- Uninitialized `.use` operands are UB (`copy_op` validation in
          -- `rustc@8144389c`; see the docstring above).
          match optVal with
          | none => .error (.undefinedBehavior "uninit Use operand") s
          | some v =>
            match writeRefPlace s dest.1 dest.2 v with
            | .error k => .error (faultToStepError k) s
            | .ok locals' => .ok () locals'
      | none => .error (.invalidProgram "missing Use operand payload") s
    | .indirect _ => .error (.unsupported "indirect Use operand") s
  copyOpAllowTransmute := fun _ _ _ s =>
    .error (.unsupported "transmute copy unsupported") s
  binaryOp := fun _ miriOp lhs rhs s =>
    match miriImmediateToPayload? lhs.imm, miriImmediateToPayload? rhs.imm with
    | some (lTy, some lVal), some (_, some rVal) =>
      match evalRefMiriBinOp miriOp lVal rVal with
      | .error k => .error (faultToStepError k) s
      | .ok v =>
        let resTy : MirTy :=
          match miriOp with
          | .Eq | .Lt | .Le | .Ne | .Ge | .Gt => .bool
          | _ => lTy
        .ok ⟨payloadToMiriImmediate (resTy, some v), refSizedLocalLayout⟩ s
    | _, _ => .error (.invalidProgram "missing BinaryOp operands") s
  unaryOp := fun _ miriOp val s =>
    match miriImmediateToPayload? val.imm with
    | some (ty, some v) =>
      match evalRefMiriUnOp miriOp v with
      | .error k => .error (faultToStepError k) s
      | .ok u =>
        .ok ⟨payloadToMiriImmediate (ty, some u), refSizedLocalLayout⟩ s
    | _ => .error (.invalidProgram "missing UnaryOp operand") s
  writeAggregate := fun _ _ _ _ s =>
    .error (.unsupported "Aggregate unsupported on Day 1") s
  writeRepeat := fun _ _ _ s =>
    .error (.unsupported "Repeat unsupported") s
  forceAllocation := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported on Day 1") s
  toRef := fun _ _ s =>
    .error (.unsupported "Ref/RawPtr unsupported on Day 1") s
  enforceValidity := fun _ _ s => .ok false s
  retagPtrValue := fun _ _ _ s => .ok none s
  placeBaseRaw := fun _ _ s => .ok false s
  normalize := fun _ ty s => .ok ty s
  cast := fun _ _ _ _ _ s =>
    .error (.unsupported "Cast unsupported") s
  readDiscriminant := fun c op s =>
    match op.op with
    | .immediate imm =>
      match miriImmediateToPayload? imm with
      | some (.enum ety, optVal) =>
        match encodeRefEnumTagOp ety optVal with
        | .error err => .error err s
        | .ok miriOp =>
          Miri.Interpreter.Discriminant.readDiscriminant
            (refDiscriminantHooks (List RefLocalState) ety) c miriOp s
      | _ => .error (.invalidProgram "non-enum Discriminant operand") s
    | .indirect _ => .error (.unsupported "indirect enum local unsupported") s
  discriminantForVariant := fun c ty variant s =>
    match MirSemantics.getElem? types ty with
    | some (.enum ety) =>
      match Miri.Interpreter.Discriminant.discriminantForVariant
          (refDiscriminantHooks (List RefLocalState) ety) c 0 variant s with
      | .error err s' => .error err s'
      | .ok discr s' =>
        match discr.imm with
        | .scalar msc =>
          match msc.tryToScalarInt with
          | .ok (.integer sc) =>
            let v : Val :=
              .scalar ⟨ety.discrWidth, ety.discrSigned, sc.data⟩
            .ok ⟨payloadToMiriImmediate
                  (.int ety.discrWidth ety.discrSigned, some v),
                discr.layout⟩ s'
          | _ => .error (.invalidProgram "non-integer discriminant scalar") s'
        | _ => .error (.invalidProgram "non-scalar discriminant immediate") s'
    | _ =>
      .error (.invalidProgram "non-enum TyId in discriminantForVariant") s
}

/-- Reference rvalue evaluator over `Miri.MIR.Rvalue` and `Miri.MIR.Place`,
delegating destination place resolution, outer dispatch, left-to-right operand
sequencing, operator dispatch, discriminant reading, and destination writes to
`Miri.Interpreter.evalRvalueIntoPlace`,
`Miri.Interpreter.Discriminant.{readDiscriminant, discriminantForVariant}`,
`Miri.Interpreter.placeWriteLocalImmediate`, and `Miri.Interpreter.runRvalue`
(`vendor/lean-miri/Miri/Interpreter/{Rvalue,Discriminant,Place}.lean`),
matching `eval_rvalue_into_place` in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn eval_rvalue_into_place(
>     &mut self,
>     rvalue: &mir::Rvalue<'tcx>,
>     place: mir::Place<'tcx>,
> ) -> InterpResult<'tcx>"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefMiriRvalue (types : List MirTy)
    (rlocals : List RefLocalState) (dst : Miri.MIR.Place)
    (mirRv : Miri.MIR.Rvalue) :
    Except FaultKind (List RefLocalState) :=
  match Miri.Interpreter.runRvalue
      (Miri.Interpreter.evalRvalueIntoPlace
        (refRvalueHooks types) () mirRv dst) rlocals with
  | (rlocals', .ok ()) => .ok rlocals'
  | (_, .error (.undefinedBehavior _))
  | (_, .error (.stack (.localExpectedLive _))) => .error .undefined
  | _ => .error .unsupported

/-- `Miri.Interpreter.LocalStorageHooks` for
`Miri.Interpreter.Frame.storageLive` and
`Miri.Interpreter.Frame.storageDead`. -/
noncomputable def refLocalStorageHooks :
    Miri.Interpreter.LocalStorageHooks
      (Option Val) Miri.Interpreter.LocalLayout Unit Unit := {
  veryTriviallySized := fun _ => .ok true
  layout := fun s _ _ => ⟨s, .ok refSizedLocalLayout⟩
  isSized := fun _ => true
  afterLocalWrite := fun s _ _ => ⟨s, .ok ()⟩
  allocateDyn := fun s _ _ =>
    ⟨s, .error (.allocationFailure "unsized local unsupported")⟩
  deallocateStack := fun s _ => ⟨s, .ok ()⟩
}

/-- Machine state threaded through `Miri.Interpreter.Step.step`: holds the
active frame's `locals` (updated in place by `.Assign`, `.StorageLive`,
`.StorageDead`, and `.SwitchInt` discriminant moves) and an optional `terminal`
outcome (set by `TerminatorHooks.copyReturn`). -/
structure RefStepMachine where
  locals : List RefLocalState
  terminal : Option (StepResult RefState TerminalOut) := none

/-- Construct a single-frame `Miri.Interpreter.StepState` over `bbs` at
location `.mir ⟨blockIdx, 0⟩` with frame `cleanup` flag and initial
`locals := rlocals`. -/
noncomputable def mkRefStepStateWith (rlocals : List RefLocalState)
    (bbs : Array Miri.MIR.BasicBlock) (blockIdx : BasicBlockId)
    (cleanup : Bool) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      RefStepMachine := {
  stack := ⟨Array.mk [{
    mkSingleLocalMiriFrame .dead cleanup with
    body := { refDummyMirBody cleanup with basicBlocks := bbs }
    location := .mir ⟨blockIdx, 0⟩
  }]⟩
  machine := { locals := rlocals }
}

/-- Minimal `Miri.Interpreter.StepState` with a single statement `stmt` at
location `.mir ⟨0, 0⟩` so `Miri.Interpreter.Step.step` executes its statement
dispatch and statement-index increment path. -/
noncomputable def mkRefStmtStepState (rlocals : List RefLocalState)
    (stmt : Miri.MIR.Statement) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  mkRefStepStateWith rlocals
    (Array.mk [{ refDummyMirBlock false with statements := Array.mk [stmt] }])
    0 false

/-- Minimal `Miri.Interpreter.StepState` at terminator position
(`statements := Array.empty`, `location := .mir ⟨0, 0⟩`) so
`Miri.Interpreter.Step.step` executes its `beforeTerminator` + `terminator`
(`Miri.Interpreter.ControlFlow.evalTerminator`) path. -/
noncomputable def mkRefTermStepState (rlocals : List RefLocalState)
    (term : Miri.MIR.Terminator) (cleanup : Bool) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  mkRefStepStateWith rlocals
    (Array.mk [{ refDummyMirBlock cleanup with terminator := term }])
    0 cleanup

/-- Minimal `Miri.Interpreter.StepState` with `basicBlocks := Array.empty` at
location `.mir ⟨blockIdx, 0⟩`. Because `basicBlocks` is empty,
`Miri.Interpreter.Step.step` always takes its out-of-bounds `.invalidBlock`
error path here (making the fallback `_ => .ub` arm in `evalRefStep`
unreachable). -/
noncomputable def mkRefInvalidBlockStepState (rlocals : List RefLocalState)
    (blockIdx : BasicBlockId) :
    Miri.Interpreter.StepState (Option Val) Miri.Interpreter.LocalLayout Unit
      RefStepMachine :=
  mkRefStepStateWith rlocals Array.empty blockIdx false

/-- Extract the active `.mir loc` from the top frame of `st`, returning `none`
on an empty stack or `.unwinding` frame. -/
noncomputable def extractMirLocation? {M : Type}
    (st : Miri.Interpreter.StepState (Option Val)
      Miri.Interpreter.LocalLayout Unit M) :
    Option Miri.MIR.Location :=
  match st.stack.currentFrame? with
  | some f =>
    match f.location with
    | .mir loc => some loc
    | .unwinding _ => none
  | none => none

/-- Map `RefStatementKind` to its `Miri.MIR.Statement` constructor for
`Miri.Interpreter.Step.step` and `Miri.Interpreter.Step.evalStatement`.

`.unsupported` translates to the fail-closed sentinel
`.Intrinsic (.Assume (.Copy ⟨0, Array.empty⟩))` so `Step.evalStatement` routes
it to `refStepHooksFor.intrinsic` (`.fault .unsupported`). -/
noncomputable def toMiriStatementForDispatch :
    RefStatementKind → Miri.MIR.Statement
  | .nop => { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Nop }
  | .storageLive localId =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .StorageLive localId }
  | .storageDead localId =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .StorageDead localId }
  | .assign dst rvalue =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Assign (toMiriPlace dst) (toMiriRvalue rvalue) }
  | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .Intrinsic (.Assume (.Copy ⟨0, Array.empty⟩)) }

/-- Map `RefTerminatorKind` to its `Miri.MIR.Terminator` constructor for
`Miri.Interpreter.Step.step` and
`Miri.Interpreter.ControlFlow.evalTerminator`.

- `.goto`, `.return_`, `.unreachable`, and `.switchInt` translate to their
  corresponding `Miri.MIR.TerminatorKind` constructors: for `.switchInt`, each
  `BitVec 128` case literal is encoded losslessly as `caseBits.toNat` in
  `Miri.MIR.SwitchTarget.Case`, driving `evalDiscriminant`,
  `compareSwitchCase`, and `ControlFlow.goToBlock`.
- All Day-1 unmodeled terminators (`.unwindResume`, `.assert`, `.call`, and
  `.unsupported`) route to the fail-closed sentinel `.UnwindTerminate .Abi`
  (firing `unwindTerminate` -> `.fault .unsupported`). Routing `.assert` or
  `.call` directly would only construct unused placeholder message/callee
  fields before `readAssertCondition`/`call` fail closed, and routing
  `.unwindResume` to `Miri.MIR.TerminatorKind.UnwindResume` would invoke
  `ControlFlow.returnFromCurrentFrame ... true` on Day 1's single-frame
  `StepState`, reporting `.undefinedBehavior` rather than Day 1's fail-closed
  `.unsupported` classification. -/
noncomputable def toMiriTerminatorForDispatch :
    RefTerminatorKind → Miri.MIR.Terminator
  | .goto target =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Goto target Array.empty }
  | .return_ =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return }
  | .unreachable =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Unreachable }
  | .switchInt discr targets =>
    { sourceInfo := ⟨⟨0⟩, 0⟩
      kind := .SwitchInt (toMiriOperand discr)
        { cases := Array.mk
            (targets.branches.map (fun b => .Case b.1.toNat b.2))
          otherwise := targets.otherwise } }
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>
    { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .UnwindTerminate .Abi }

/-- `Miri.Interpreter.TerminatorHooks` for
`Miri.Interpreter.ControlFlow.evalTerminator` and
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`.

`evalDiscriminant` evaluates Miri's passed `op : Miri.MIR.Operand` via
`evalRefMiriOperandToSlot` and `readRefPrimitiveSlot`, threading post-move
locals through `RefStepMachine.locals`. `compareSwitchCase` decodes each case
literal at the discriminant's type via `evalRefConstLit`
(`Miri.Memory.ScalarInt.tryFromUInt` and `tryToBool`) and compares it via
`evalRefMiriBinOp .Eq` (`Miri.Interpreter.IntegerOps.binary` / `binaryBool`),
matching `compareSwitchCase` in `Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`),
`ScalarInt::try_from_uint` in `compiler/rustc_middle/src/ty/consts/int.rs`, and
`SwitchInt` in `compiler/rustc_const_eval/src/interpret/step.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "for (const_int, target) in targets.iter() {
>     ...
>     let res = self.binary_op(
>         mir::BinOp::Eq,
>         &discr,
>         &ImmTy::from_uint(const_int, discr.layout),
>     )?;
>     if res.to_scalar().to_bool()? {
>         target_block = target;
>         break;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, overflow) = Self::truncate_from_uint(i, size);
>     if overflow { None } else { Some(r) }
> }"
> (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Day-1 hook coverage: `.return_` exercises `bodySpan`, `returnOperand`,
`popFrame`, `copyReturn`, and `cleanupFrame`; `.switchInt` exercises
`evalDiscriminant` and `compareSwitchCase`; and `.unwindResume`, `.assert`,
`.call`, and `.unsupported` all route through `.UnwindTerminate .Abi` and fail
closed in `unwindTerminate`. The remaining `TerminatorHooks` fields (`call`,
`tailCall`, `drop`, `ignoreOptionalOverflowChecks`, `readAssertCondition`, and
`assertPanic`) are required by the record, fail closed (or return `false`), and
are unreachable under Day 1.

Uninitialized-read UB in `copyReturn`: adapter frames never store
`Immediate.uninit` (see `slotToMiriLocalValue`), so `copyReturn` itself
rejects an uninitialized return place `_0` (`.live none` faults with
`.undefined`; so does a dead `_0`, matching
`Trusted.MirSemantics.evalTerminator`). This Anneal-written rule matches
`return_from_current_stack_frame`, which copies `_0` into the caller's return
place with `copy_op_allow_transmute`:

> "// Copy the return value and remember the return continuation.
> if !unwinding {
>     self.copy_op_allow_transmute(&return_op, frame.return_place())?;
>     ...
> }"
> (`compiler/rustc_const_eval/src/interpret/call.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Like `copy_op`, `copy_op_allow_transmute` delegates to `copy_op_inner`, whose
validation reports an uninitialized `bool` or integer value as UB (both quoted
at `refRvalueHooks`). -/
noncomputable def refTerminatorHooksFor (types : List MirTy)
    (callerMem : CallerMemory) :
    Miri.Interpreter.TerminatorHooks (Option Val) Miri.Interpreter.LocalLayout
      Unit RefStepMachine Unit Unit Val := {
  bodySpan := fun _ => .ok ⟨0⟩
  returnOperand := fun _ st => (st, .ok ())
  popFrame := fun _ st =>
    ( { st with stack := Miri.Interpreter.Stack.empty },
      .ok (mkSingleLocalMiriFrame .dead false) )
  copyReturn := fun _ _ _ st =>
    -- An uninitialized `_0` is UB (`copy_op_allow_transmute` validation in
    -- `rustc@8144389c`; see the docstring above).
    match MirSemantics.getElem? st.machine.locals 0 with
    | some ⟨.live (some retVal), some _⟩ =>
      ({ st with machine := { st.machine with
          terminal := some (.done (.returned ⟨retVal, callerMem⟩)) } }, .ok ())
    | some ⟨.live none, some _⟩ | some ⟨.dead, some _⟩ =>
      (st, .error (.undefinedBehavior "uninit or dead return place"))
    | _ => (st, .error (.unsupported "missing return place"))
  cleanupFrame := fun _ _ _ st => (st, .ok .normal)
  unwindTerminate := fun _ _ st =>
    (st, .error (.unsupported "UnwindTerminate unsupported"))
  evalDiscriminant := fun _ op st =>
    match evalRefMiriOperandToSlot types st.machine.locals op with
    | .error k => (st, .error (faultToStepError k))
    | .ok (ty, optVal, rlocalsAfterDiscr) =>
      match readRefPrimitiveSlot ty optVal with
      | .error k => (st, .error (faultToStepError k))
      | .ok discrVal =>
        match discrVal with
        | .scalar _ | .bool _ =>
          ({ st with machine :=
              { st.machine with locals := rlocalsAfterDiscr } },
            .ok discrVal)
        | _ => (st, .error (.unsupported "non-scalar SwitchInt discriminant"))
  compareSwitchCase := fun _ discrVal caseBitsNat st =>
    let caseBits := BitVec.ofNat 128 caseBitsNat
    let caseTy? : Option MirTy :=
      match discrVal with
      | .scalar sv => some (.int sv.width sv.signed)
      | .bool _ => some .bool
      | _ => none
    (st,
      match caseTy? with
      | none => .error (.unsupported "non-scalar SwitchInt discriminant")
      | some caseTy =>
        match evalRefConstLit caseTy (.scalar caseBits) with
        | .error k => .error (faultToStepError k)
        | .ok caseVal =>
          match evalRefMiriBinOp .Eq discrVal caseVal with
          | .ok (.bool eq) => .ok eq
          | .error k => .error (faultToStepError k)
          | .ok _ => .error (.unsupported "non-bool SwitchInt Eq result"))
  call := fun _ _ st => (st, .error (.unsupported "Call unsupported on Day 1"))
  tailCall := fun _ _ st => (st, .error (.unsupported "TailCall unsupported"))
  drop := fun _ _ _ _ st => (st, .error (.unsupported "Drop unsupported"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ _ st =>
    (st, .error (.unsupported "Assert unsupported on Day 1"))
  assertPanic := fun _ _ _ st =>
    (st, .error (.unsupported "Assert unsupported on Day 1"))
}

/-- `Miri.Interpreter.StepHooks` routing `.Assign`, `.StorageLive`,
`.StorageDead`, and terminators through `Miri.Interpreter.Step.step`,
`Miri.Interpreter.Step.evalStatement`,
`Miri.Interpreter.Frame.storageLive`,
`Miri.Interpreter.Frame.storageDead`, and
`Miri.Interpreter.ControlFlow.evalTerminator`.

Closes over only `types` and `callerMem`: all statement places/rvalues and
terminator operands/switch targets arrive through `Miri.Interpreter.Step.step`
and frame locals thread through `RefStepMachine.locals`. Note on `storageLive`:
it invokes `Miri.Interpreter.Frame.storageLive` on a dummy dead local `0`
(where `refLocalStorageHooks.veryTriviallySized` returns `.ok true`, so
`refLocalStorageHooks.layout` is skipped and the call always returns `.ok ()`),
discards the resulting Miri frame, and writes `refLiveUninitSlot localTy`
directly into `RefStepMachine.locals`.

Day-1 hook coverage: `.assign`, `.storageLive`, `.storageDead`, `.unsupported`
(via `.Intrinsic (.Assume ...)`), and terminators exercise `assign`,
`storageLive`, `storageDead`, `intrinsic`, `beforeTerminator`, and `terminator`.
The remaining `StepHooks` fields (`evalPlace`, `writeDiscriminant`,
`incrementConstEvalCounter`, and `returnFromCurrentFrame`) are required by the
record but unreachable under Day 1 (`evalPlace` and `writeDiscriminant` fail
closed; `returnFromCurrentFrame` returns `.ok ()`, which is harmless only
because `mkRefStepStateWith` always constructs `.mir` locations, never
`.unwinding`). -/
noncomputable def refStepHooksFor (types : List MirTy)
    (callerMem : CallerMemory) :
    Miri.Interpreter.StepHooks (Option Val) Miri.Interpreter.LocalLayout Unit
      RefStepMachine Unit Unit := {
  assign := fun _ dst rvalue st =>
    match evalRefMiriRvalue types st.machine.locals dst rvalue with
    | .error k => (st, .error (faultToStepError k))
    | .ok rlocalsAfterWrite =>
      ({ st with machine :=
          { st.machine with locals := rlocalsAfterWrite } }, .ok ())
  evalPlace := fun _ _ _ st => (st, .error (.unsupported "SetDiscriminant"))
  writeDiscriminant := fun _ _ _ st =>
    (st, .error (.unsupported "SetDiscriminant"))
  storageLive := fun _ localId st =>
    let res := Miri.Interpreter.Frame.storageLive
      (mkSingleLocalMiriFrame .dead false) () refLocalStorageHooks 0
    match res.outcome with
    | .error e => (st, .error (.stack e))
    | .ok () =>
      match MirSemantics.getElem? st.machine.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? st.machine.locals localId
            ⟨refLiveUninitSlot localTy, some localTy⟩ with
        | some rlocals' =>
          ({ st with machine := { st.machine with locals := rlocals' } },
            .ok ())
        | none => (st, .error (.unsupported "storageLive local out of bounds"))
      | _ => (st, .error (.unsupported "storageLive missing cached layout"))
  storageDead := fun _ localId st =>
    let res := Miri.Interpreter.Frame.storageDead
      (mkTwoLocalMiriFrame .dead .dead) () refLocalStorageHooks
      (if Nat.beq localId 0 then 0 else 1)
    match res.outcome with
    | .error e => (st, .error (.stack e))
    | .ok () =>
      match MirSemantics.getElem? st.machine.locals localId with
      | some ⟨_, some localTy⟩ =>
        match MirSemantics.setElem? st.machine.locals localId
            ⟨.dead, some localTy⟩ with
        | some rlocals' =>
          ({ st with machine := { st.machine with locals := rlocals' } },
            .ok ())
        | none => (st, .error (.unsupported "storageDead local out of bounds"))
      | _ => (st, .error (.unsupported "storageDead missing cached layout"))
  intrinsic := fun _ _ st => (st, .error (.unsupported "Intrinsic"))
  incrementConstEvalCounter := fun _ st => (st, .ok ())
  returnFromCurrentFrame := fun _ _ st => (st, .ok ())
  beforeTerminator := fun _ st => (st, .ok ())
  terminator :=
    Miri.Interpreter.ControlFlow.evalTerminator
      (refTerminatorHooksFor types callerMem)
}

/-- Reference statement evaluator delegating outer step and statement dispatch
to `Miri.Interpreter.Step.step` and `Miri.Interpreter.Step.evalStatement`,
`_0` `StorageDead` rejection to `Miri.Interpreter.Frame.storageDead`, and
exercising `Miri.Interpreter.Frame.storageLive` (whose dummy-frame call always
returns `.ok ()`; see `refStepHooksFor`)
(`vendor/lean-miri/Miri/Interpreter/{Step,Stack}.lean`), matching
`eval_statement` in `compiler/rustc_const_eval/src/interpret/step.rs` and
`storage_live` / `storage_dead` in
`compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn eval_statement(&mut self, stmt: &mir::Statement<'tcx>)
> -> InterpResult<'tcx> {
>   ...
>   match &stmt.kind {
>     Assign((place, rvalue)) =>
>       self.eval_rvalue_into_place(rvalue, *place)?,
>     ...
>     // Mark locals as alive
>     StorageLive(local) => {
>       self.storage_live(*local)?;
>     }
>     // Mark locals as dead
>     StorageDead(local) => {
>       self.storage_dead(*local)?;
>     }
>     ...
>   }
>   interp_ok(())
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "assert!(local != mir::RETURN_PLACE, "Cannot make return place dead");"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefStatement (types : List MirTy) (rframe : RefFrameState)
    (callerMem : CallerMemory) (stmt : RefStatementKind) :
    StepResult RefState TerminalOut :=
  match Miri.Interpreter.Step.step
      (refStepHooksFor types callerMem) ()
      (mkRefStmtStepState rframe.locals
        (toMiriStatementForDispatch stmt)) with
  | (st', .ok true) =>
    match extractMirLocation? st' with
    | some loc =>
      .step {
        frames := [{
          rframe with
          stmtIdx := rframe.stmtIdx + loc.statementIndex
          locals := st'.machine.locals
        }]
        callerMem
      }
    | none => .fault .unsupported
  | (_, .error (.undefinedBehavior _)) => .fault .undefined
  | (_, _) => .fault .unsupported

/-- Reference terminator evaluator delegating outer step, terminator dispatch,
`SwitchInt` branch selection, and `goToBlock` jumps to
`Miri.Interpreter.Step.step`, `Miri.Interpreter.ControlFlow.evalTerminator`,
`Miri.Interpreter.ControlFlow.goToBlock`, and
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`
(`vendor/lean-miri/Miri/Interpreter/{Step,ControlFlow}.lean`), matching
`eval_terminator` in `compiler/rustc_const_eval/src/interpret/step.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "fn eval_terminator(&mut self, terminator: &mir::Terminator<'tcx>) ->
> InterpResult<'tcx> {
>     ...
>     match terminator.kind {
>         Return => {
>             self.return_from_current_stack_frame(/* unwinding */ false)?
>         }
>         Goto { target, loop_hint_attrs: _ } => self.go_to_block(target),
>         SwitchInt { ref discr, ref targets } => { ... }
>         ...
>         Unreachable => throw_ub!(Unreachable),
>         ...
>     }
>     interp_ok(())
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalRefTerminator (types : List MirTy) (rbb : RefBasicBlock)
    (rframe : RefFrameState) (callerMem : CallerMemory) :
    StepResult RefState TerminalOut :=
  match Miri.Interpreter.Step.step
      (refStepHooksFor types callerMem) ()
      (mkRefTermStepState rframe.locals
        (toMiriTerminatorForDispatch rbb.terminator) rbb.cleanup) with
  | (st', .ok true) =>
    match st'.machine.terminal with
    | some res => res
    | none =>
      match extractMirLocation? st' with
      | some loc =>
        .step {
          frames := [{
            rframe with
            blockIdx := loc.block
            stmtIdx := loc.statementIndex
            locals := st'.machine.locals
          }]
          callerMem
        }
      | none => .fault .unsupported
  | (_, .error (.undefinedBehavior _)) => .fault .undefined
  | (_, _) => .fault .unsupported

/-- Single-step evaluator of $M_{\text{ref}}$:
checks `rs.stepsExecuted < rs.maxSteps` first, returning `.exhaustedStepLimit`
when the step budget is reached, and otherwise resolves the active `RefBody`
and `RefBasicBlock` and delegates statement, terminator, and out-of-bounds
block transitions to `Miri.Interpreter.Step.step` (`evalRefStatement`,
`evalRefTerminator`, and `mkRefInvalidBlockStepState`), incrementing
`stepsExecuted := rs.stepsExecuted + 1` on each running step.

The stack must have the shape established by `initRefState`: a suspended
caller sentinel (`isCallerSentinel = true`) beneath an executing frame
(`isCallerSentinel = false`). Any other shape is `.blocked`. Each running
step preserves the sentinel and replaces only the top frame.

Adapter-owned boundary rules: (1) on an out-of-bounds `blockIdx`,
`mkRefInvalidBlockStepState` runs `Step.step` over `basicBlocks := Array.empty`,
so `.invalidBlock` is always returned and the `_ => .ub` branch is unreachable;
(2) `stmtIdx > rbb.statements.length` returns `.blocked` directly to match
`Trusted.MirSemantics.evalStep` (unreachable from `initRefState`; Miri's
`Step.step` instead dispatches the terminator for any `statementIndex ≥
statements.size`). -/
noncomputable def evalRefStep (rp : RefProg) (_c : Choice)
    (rs : RefState) : RefOutcome :=
  if !Nat.blt rs.stepsExecuted rs.maxSteps then
    .exhaustedStepLimit
  else
    match rs.frames with
    | [sentinel, rframe] =>
      if !sentinel.isCallerSentinel || rframe.isCallerSentinel then
        .blocked
      else
        match MirSemantics.getElem? rp.bodies rframe.defId with
        | none => .blocked
        | some rbody =>
          match MirSemantics.getElem? rbody.basicBlocks rframe.blockIdx with
          | none =>
            match Miri.Interpreter.Step.step
                (refStepHooksFor rp.types rs.callerMem) ()
                (mkRefInvalidBlockStepState rframe.locals rframe.blockIdx) with
            | (_, .error (.invalidBlock _)) => .blocked
            | _ => .ub
          | some rbb =>
            match MirSemantics.getElem? rbb.statements rframe.stmtIdx with
            | some rstmt =>
              stepResultToRefOutcome sentinel rs.stepsExecuted rs.maxSteps
                (evalRefStatement rp.types rframe rs.callerMem rstmt)
            | none =>
              if Nat.beq rframe.stmtIdx rbb.statements.length then
                stepResultToRefOutcome sentinel rs.stepsExecuted rs.maxSteps
                  (evalRefTerminator rp.types rbb rframe rs.callerMem)
              else
                .blocked
    | _ => .blocked

/-- Relational small-step transition of $M_{\text{ref}}$. -/
def RefStep (rp : RefProg) (rs : RefState)
    (out : RefOutcome) : Prop :=
  ∃ c : Choice, ValidRefChoice rp rs c ∧ evalRefStep rp c rs = out

/-- Unbounded finite-step reachability in $M_{\text{ref}}$, chaining `rs₃` from
`RefStep rp rs₂ (.running rs₃)` unmodified. -/
inductive RefReaches (rp : RefProg) : RefState → RefState → Prop where
  | refl (rs : RefState) : RefReaches rp rs rs
  | tail {rs₁ rs₂ rs₃ : RefState} :
      RefReaches rp rs₁ rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReaches rp rs₁ rs₃

/-- Outcome `out` is reached from `(rp, q)` under step budget `maxSteps`. -/
def RefReachesOutcome (rp : RefProg) (q : Query)
    (maxSteps : Nat) (out : RefOutcome) : Prop :=
  match initRefState rp q maxSteps with
  | .error k => out = faultToRefOutcome k
  | .ok rs₀ => ∃ rs : RefState, RefReaches rp rs₀ rs ∧ RefStep rp rs out

/-- All-prefix well-formedness in $M_{\text{ref}}$: quantifies universally over
all step budgets `maxSteps : Nat`. -/
def RefWellFormed (rp : RefProg) (q : Query) : Prop :=
  ∀ maxSteps : Nat,
    (∃ rs₀ : RefState, initRefState rp q maxSteps = .ok rs₀ ∧
      ∀ rs : RefState, RefReaches rp rs₀ rs →
        ∃ c : Choice, ValidRefChoice rp rs c) ∧
    ¬ RefReachesOutcome rp q maxSteps .ub ∧
    ¬ RefReachesOutcome rp q maxSteps .blocked

/-- Observable terminal behavior in $M_{\text{ref}}$: quantifies existentially
over a sufficient step budget `maxSteps : Nat`. -/
def RefBehavior (rp : RefProg) (q : Query)
    (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat, RefReachesOutcome rp q maxSteps (.returned out)

/-- Divergence in $M_{\text{ref}}$: initialization succeeds at step budget `0`
with `rs₀`, and there exists an infinite reference execution trace
`trace : Nat → RefState` starting at `trace 0 = rs₀` such that at every step
`n`, executing `trace n` with `stepsExecuted := n` and step budget
`maxSteps := n + 1` transitions via `RefStep` to
`.running { trace (n + 1) with stepsExecuted := n + 1, maxSteps := n + 1 }`. -/
def RefDiverges (rp : RefProg) (q : Query) : Prop :=
  ∃ rs₀ : RefState,
    initRefState rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        RefStep rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (.running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 })

end Trusted.Correspondence
