-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.State
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Memory
public import Trusted.MirSemantics.Bytes

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Small-Step Execution Rules (`Trusted.MirSemantics.Step`)

Constant, operand, rvalue, place-write, statement, terminator, and single-step
transition rules (`evalStep`) for $M_{\text{anneal}}$.
-/

/-- Stage 1 of operand evaluation (`eval_operand` and `eval_place_to_op` in
`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`, and
`Miri.Interpreter.OperandMachine.evalOperand` in
`vendor/lean-miri/Miri/Interpreter/OperandMachine.lean` with opt-in
`deinitMovedPlace = true`):

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
>
> "let mut op = self.local_to_op(
>     place.local,
>     if place.projection.is_empty() { layout } else { None },
> )?;
> for elem in place.projection.iter() {
>     op = self.project(&op, elem)?
> }"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Matching `eval_place_to_op`, local bounds and liveness (`.dead` -> UB) are
checked before inspecting `place.projection` (`.unsupported` on non-empty
projections). Note that upstream `eval_operand` currently leaves move
invalidation unimplemented (as recorded in the `FIXME` above). As a
deliberate, conservative over-approximation (sound because deinitializing can
only introduce faults on subsequent reads), `evalOperandToSlot` resolves an
`Operand` to `(ty : MirTy, optVal : Option Val, locals' : List LocalSlot,
mem' : MemoryState)` without yet requiring `optVal` to be initialized
(`some v`), and deinitializes moved non-ZST locals.

An `.indirect place` local is read from memory with `loadIndirect`
(`local_to_op` returns `Operand::Indirect`, and the caller's read checks the
bytes). The caller's static type check `tyOk` runs before that read and before
any move deinitialization, so an ill-typed use of an `.indirect` local faults
with `.unsupported` even when its memory is dead, out of bounds, or holds
invalid bytes. This matches `lean-miri`, where `OperandMachine.evalOperand`
resolves an indirect place without touching memory, and the consumer checks
the type (`MemoryOperand.readImmediate`'s primitive-readability check, or
`Place.copyRuntimePlaceNoValidate`'s layout-compatibility check) before
reading the bytes and deinitializing a moved place. Resolving an `.immediate`
local or a constant reads no memory, so for those operands the caller checks
the type after resolution with the same result.
- `.copy place`: reads `(ty, optVal)` without mutating `locals` or `mem`.
- `.move place` on an `.immediate` local: reads `(ty, optVal)` and
  conservatively transitions `locals[place.localId]` to `liveUninitSlot ty`
  (preserving `.immediate (some .unit)` on `MirTy.unit` and
  `.immediate (some (.enumVal ety 0))` on admitted 1-variant `.zeroSized`
  `MirTy.enum`, and setting all other local types to `.immediate none`,
  matching `OperandMachine.evalOperand` with opt-in `deinitMovedPlace = true`).
- `.move place` on an `.indirect mplace` local: reads `(ty, optVal)` and marks
  the value's bytes at `mplace` uninitialized (`deinitIndirect`; zero-sized
  types have no bytes, so their unique value survives as in the immediate
  case).
- `.constant c`: decodes constant literal without mutating `locals` or `mem`.
-/
noncomputable def evalOperandToSlot (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (tyOk : MirTy → Bool) :
    Operand →
      Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState)
  | .copy place =>
    match getElem? bodyLocals place.localId,
        getElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some ty, some (.immediate optVal) =>
      if !place.projection.isEmpty then
        .error .unsupported
      else
        .ok (ty, optVal, locals, mem)
    | some ty, some (.indirect mplace) =>
      if !place.projection.isEmpty then
        .error .unsupported
      else if !tyOk ty then
        .error .unsupported
      else
        match loadIndirect mem ty mplace with
        | .ok optVal => .ok (ty, optVal, locals, mem)
        | .error k => .error k
    | _, _ => .error .unsupported
  | .move place =>
    match getElem? bodyLocals place.localId,
        getElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some ty, some (.immediate optVal) =>
      if !place.projection.isEmpty then
        .error .unsupported
      else
        match setElem? locals place.localId (liveUninitSlot ty) with
        | some locals' => .ok (ty, optVal, locals', mem)
        | none => .error .unsupported
    | some ty, some (.indirect mplace) =>
      if !place.projection.isEmpty then
        .error .unsupported
      else if !tyOk ty then
        .error .unsupported
      else
        match loadIndirect mem ty mplace with
        | .error k => .error k
        | .ok optVal =>
          match deinitIndirect mem ty mplace with
          | .ok mem' => .ok (ty, optVal, locals, mem')
          | .error k => .error k
    | _, _ => .error .unsupported
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok v => .ok (c.ty, some v, locals, mem)
    | .error k => .error k

/-- Stage 2 of operand evaluation (`evalOperandToSlot` followed by
`read_immediate` in
`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`, and
`Miri.Interpreter.MemoryOperand.readImmediate` in
`vendor/lean-miri/Miri/Interpreter/MemoryOperand.lean`):

> "if !matches!(
>     op.layout().backend_repr,
>     BackendRepr::Scalar(abi::Scalar::Initialized { .. })
>         | BackendRepr::ScalarPair { ... }
> ) {
>     span_bug!(
>         self.cur_span(),
>         \"primitive read not possible for type: {}\",
>         op.layout().ty
>     );
> }
> let imm = self.read_immediate_raw(op)?.right().unwrap();
> if matches!(*imm, Immediate::Uninit) {
>     throw_ub!(InvalidUninitBytes(None));
> }"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Used by `.binaryOp`, `.unaryOp`, and `.switchInt`. Checks
`isPrimitiveReadableTy ty` on the static type first (`.unsupported` on
non-primitives such as `.unit`; `evalOperandToSlot` performs this check before
reading an `.indirect` local's memory), and then checks initialization (`optVal
= some v`, faulting with `.undefined` on uninitialized storage). -/
noncomputable def evalPrimitiveOperand (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match evalOperandToSlot bodyLocals locals mem isPrimitiveReadableTy opnd with
  | .error k => .error k
  | .ok (ty, optVal, locals', mem') =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match optVal with
      | some v => .ok (v, locals', mem')
      | none => .error .undefined

/-- Result of `Rvalue.discriminant` on a local of admitted fieldless enum type
`ety` whose value is `optVal`: the variant's declared discriminant as a scalar
of `(ety.discrWidth, ety.discrSigned)`, with `locals` and `mem` unchanged.
Matches `read_discriminant` and `discriminant_for_variant` in
`compiler/rustc_const_eval/src/interpret/discriminant.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `Miri.Interpreter.Discriminant`:

> "let discr_layout = self.layout_of(ty.discriminant_ty(*self.tcx))?;
> let discr_value = match ty.discriminant_for_variant(*self.tcx, variant) {
>     Some(discr) => {
>         ...
>         assert_eq!(discr.ty, discr_layout.ty);
>         Scalar::from_uint(discr.val, discr_layout.size)
>     }
>     ...
> };
> interp_ok(ImmTy::from_scalar(discr_value, discr_layout))"

An uninitialized (`none`) scalar-tagged enum value faults with `.error
.undefined`, whereas an inhabited 1-variant ZST enum (`ety.tagRepr =
.zeroSized`, `Variants::Single { index: 0 }`) returns `ety.discriminants[0]`
without reading tag bytes. -/
noncomputable def evalDiscriminantOfVal (ety : EnumTy) (optVal : Option Val)
    (locals : List LocalSlot) (mem : MemoryState) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  if !enumAdmitted ety then
    .error .unsupported
  else
    -- For 1-variant `.zeroSized` enums, `Miri`'s `readDiscriminant`
    -- (`Variants::Single { index: 0 }`) returns variant `0` without reading
    -- tag bytes even if a slot holds `.immediate none` (`Uninit`), preserving
    -- universal 1-step lockstep over arbitrary `FrameState`s.
    match ety.tagRepr, optVal with
    | .zeroSized, none =>
      match getElem? ety.discriminants 0 with
      | some disc =>
        .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
          truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals, mem)
      | none => .error .unsupported
    | .zeroSized, some (.enumVal ety' v) =>
      if EnumTy.beq ety ety' && Nat.beq v 0 then
        match getElem? ety.discriminants 0 with
        | some disc =>
          .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
            truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals, mem)
        | none => .error .unsupported
      else
        .error .unsupported
    | .zeroSized, some _ => .error .unsupported
    | .scalar _ _, none => .error .undefined
    | .scalar _ _, some (.enumVal ety' v) =>
      if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
        match getElem? ety.discriminants v with
        | some disc =>
          .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
            truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals, mem)
        | none => .error .unsupported
      else
        .error .unsupported
    | .scalar _ _, some _ => .error .unsupported

/-- Result of `Rvalue.discriminant` on a local of type `core::cmp::Ordering`
whose value is `optVal`: the `i8` discriminant (`orderingTagBits`: `-1_i8`,
`0_i8`, or `1_i8`) as a scalar of `(.i8, true)`, with `locals` and `mem`
unchanged. `Ordering` is a `#[repr(i8)]` fieldless enum whose tag is its
discriminant, so this matches `read_discriminant` and
`discriminant_for_variant` as `evalDiscriminantOfVal` does for scalar-tagged
enums; an uninitialized (`none`) value faults with `.error .undefined`. -/
noncomputable def evalOrderingDiscriminantOfVal (optVal : Option Val)
    (locals : List LocalSlot) (mem : MemoryState) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match optVal with
  | none => .error .undefined
  | some (.ordering ord) =>
    .ok (.scalar ⟨.i8, true, BitVec.ofNat 128 (orderingTagBits ord)⟩, locals,
      mem)
  | some _ => .error .unsupported

/-- Evaluate an `Rvalue` for a destination of type `dstTy`, following the RHS
cases of `eval_rvalue_into_place`
(`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.Rvalue.evalRvalueIntoPlace` (`Miri/Interpreter/Rvalue.lean`),
together with Anneal's conservative `Operand.move` deinitialization
(`evalOperandToSlot`). `evalStatement` evaluates this RHS before checking
destination liveness and writing `dst` in `writePlace`, matching `rustc` and
`lean-miri` for unprojected sized locals (where `local_to_place` does not check
liveness and `DeadLocal` fires at write time; an unmodeled RHS can return
`.unsupported` before write-time `DeadLocal`, and `.use` checks uninitialized
input before writing while `rustc`'s `copy_op` validates after writing, with
both producing `.undefined`):
- `.use opnd`: resolves `(srcTy, optVal, locals₁, mem₁) ← evalOperandToSlot`,
  checks `srcTy = dstTy` (`copyRuntimePlaceNoValidate`; for an `.indirect`
  local, `evalOperandToSlot` checks it before reading memory), then checks
  `optVal = some v` (validity check in `copy_op` / `copyRuntimePlace`).
- `.binaryOp op lhs rhs`: evaluates `lhs` and then `rhs` left-to-right via
  `evalPrimitiveOperand` (threading `locals₁` and `mem₁` from `lhs` into
  `rhs`), then applies `evalBinOp`.
- `.unaryOp op opnd`: evaluates `opnd` via `evalPrimitiveOperand`, then applies
  `evalUnOp`.
- `.cast .intToInt opnd castTy`: resolves `(srcTy, optVal, locals₁, mem₁) ←
  evalOperandToSlot`, checks that `srcTy` is integer-like (`isIntLikeTy`,
  matching `Miri.Interpreter.Cast.cast`'s source-type validity check, which
  precedes `read_immediate`), then checks `optVal = some v` (`read_immediate`'s
  uninitialized check), and applies `evalIntToIntCast v castTy`, which rejects
  targets other than integers and `char`. (`castTypesValid` guarantees
  `castTy = dstTy`.)
- `.discriminant place`: reads an unprojected local of admitted fieldless enum
  type `.enum ety` or of type `.ordering` (from its `.immediate` value or, for
  an `.indirect` local, with `loadIndirect`) and returns
  `evalDiscriminantOfVal ety` or `evalOrderingDiscriminantOfVal`. Reading
  `.discriminant` from a `.dead` local faults with `.error .undefined`. -/
noncomputable def evalRvalue (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (dstTy : MirTy) :
    Rvalue → Except FaultKind (Val × List LocalSlot × MemoryState)
  | .use opnd =>
    match evalOperandToSlot bodyLocals locals mem
        (fun srcTy => MirTy.beq srcTy dstTy) opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals₁, mem₁) =>
      if !(MirTy.beq srcTy dstTy) then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals₁, mem₁)
        | none => .error .undefined
  | .binaryOp op lhs rhs =>
    match evalPrimitiveOperand bodyLocals locals mem lhs with
    | .error k => .error k
    | .ok (lVal, locals₁, mem₁) =>
      match evalPrimitiveOperand bodyLocals locals₁ mem₁ rhs with
      | .error k => .error k
      | .ok (rVal, locals₂, mem₂) =>
        match evalBinOp op lVal rVal with
        | .error k => .error k
        | .ok res => .ok (res, locals₂, mem₂)
  | .unaryOp op opnd =>
    match evalPrimitiveOperand bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (v, locals₁, mem₁) =>
      match evalUnOp op v with
      | .error k => .error k
      | .ok res => .ok (res, locals₁, mem₁)
  | .cast .intToInt opnd castTy =>
    match evalOperandToSlot bodyLocals locals mem isIntLikeTy opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals₁, mem₁) =>
      if !isIntLikeTy srcTy then
        .error .unsupported
      else
        match optVal with
        | none => .error .undefined
        | some v =>
          match evalIntToIntCast v castTy with
          | .error k => .error k
          | .ok res => .ok (res, locals₁, mem₁)
  | .discriminant place =>
    match getElem? bodyLocals place.localId,
        getElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some srcTy, some (.immediate optVal) =>
      if !place.projection.isEmpty then
        .error .unsupported
      else
        match srcTy with
        | .enum ety => evalDiscriminantOfVal ety optVal locals mem
        | .ordering => evalOrderingDiscriminantOfVal optVal locals mem
        | _ => .error .unsupported
    | some srcTy, some (.indirect mplace) =>
      if !place.projection.isEmpty then
        .error .unsupported
      else
        match srcTy with
        | .enum ety =>
          match loadIndirect mem srcTy mplace with
          | .error k => .error k
          | .ok optVal => evalDiscriminantOfVal ety optVal locals mem
        | .ordering =>
          match loadIndirect mem srcTy mplace with
          | .error k => .error k
          | .ok optVal => evalOrderingDiscriminantOfVal optVal locals mem
        | _ => .error .unsupported
    | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Write `val` into an unprojected `dst : Place` of known `dstTy : MirTy` in
`locals`: checks `checkVal val dstTy` first (matching
`Rvalue.assertRvalueLayout`), then checks `dst` liveness (matching
`Place.writePlaceImmediate`). An `.immediate` local takes `val` directly; an
`.indirect mplace` local stores `val`'s bytes at `mplace` (`storeIndirect`,
matching `write_immediate_no_validate`'s `Left(mplace)` case in
`compiler/rustc_const_eval/src/interpret/place.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
noncomputable def writePlace (locals : List LocalSlot) (mem : MemoryState)
    (dstLocalId : LocalId) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlot × MemoryState) :=
  if !checkVal val dstTy then
    .error .unsupported
  else
    match getElem? locals dstLocalId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.immediate _) =>
      match setElem? locals dstLocalId (.immediate (some val)) with
      | some locals' => .ok (locals', mem)
      | none => .error .unsupported
    | some (.indirect mplace) =>
      match storeIndirect mem dstTy mplace val with
      | .ok mem' => .ok (locals, mem')
      | .error k => .error k
    | some (.partialTuple _) => .error .unsupported

/-- Release the storage of the replaced local value `old`, matching
`deallocate_local` in `compiler/rustc_const_eval/src/interpret/stack.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "fn deallocate_local(&mut self, local: LocalValue<M::Provenance>) ->
> InterpResult<'tcx> {
>     if let LocalValue::Live(Operand::Indirect(MemPlace { ptr, .. })) = local
>     {
>         ...
>         self.deallocate_ptr(ptr, None, MemoryKind::Stack)?;
>     };
>     interp_ok(())
> }" -/
noncomputable def deallocateLocal (mem : MemoryState) :
    LocalSlot → Except FaultKind MemoryState
  | .indirect mplace => deallocateStack mem mplace
  | _ => .ok mem

/-- Evaluate a single `StatementKind` in `frame`, matching `eval_statement` in
`compiler/rustc_const_eval/src/interpret/step.rs` and `storage_live` /
`storage_dead` in `compiler/rustc_const_eval/src/interpret/stack.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn eval_statement(&mut self, stmt: &mir::Statement<'tcx>) ->
> InterpResult<'tcx> {
>     ...
>     match &stmt.kind {
>         Assign((place, rvalue)) => self.eval_rvalue_into_place(rvalue,
>             *place)?,
>         ...
>         StorageLive(local) => { self.storage_live(*local)?; }
>         StorageDead(local) => { self.storage_dead(*local)?; }
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)
>
> "// If the local is already live, deallocate its old memory.
> let old = mem::replace(&mut self.frame_mut().locals[local].value,
>     local_val);
> self.deallocate_local(old)?;"
> (`storage_live_dyn`, `compiler/rustc_const_eval/src/interpret/stack.rs`)
>
> "assert!(local != mir::RETURN_PLACE, \"Cannot make return place dead\");
> ...
> // If the local is already dead, this is a NOP.
> let old = mem::replace(&mut self.frame_mut().locals[local].value,
>     LocalValue::Dead);
> self.deallocate_local(old)?;"
> (`storage_dead`, `compiler/rustc_const_eval/src/interpret/stack.rs`,
> `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- `.storageLive localId` sets `locals[localId] := liveUninitSlot localTy` for
  any in-bounds `localId < frame.locals.length` (and faults with `.unsupported`
  on out-of-bounds `localId`), then deallocates the old value's storage
  (`deallocateLocal`).
- `.storageDead 0` or out-of-bounds `.storageDead localId` faults with
  `.unsupported` (`StackError.cannotMakeReturnPlaceDead` /
  `StackError.invalidLocal`); otherwise `.storageDead localId` sets
  `locals[localId] := .dead` and deallocates the old value's storage.
- `.assign dst rvalue` resolves `dst`'s local bounds and `dstTy` first, then
  evaluates `rvalue` (yielding `(val, localsAfterRval, memAfterRval)`), then
  checks `checkVal` and `dst` liveness in `writePlace`, matching `rustc` and
  `lean-miri` for unprojected sized locals (where `local_to_place` does not
  check liveness and `DeadLocal` fires at write time; an unmodeled RHS can
  fault `.unsupported` before write-time `DeadLocal`, and `.use` checks
  uninitialized input before writing while `rustc`'s `copy_op` validates after
  writing, both producing `.undefined`). -/
noncomputable def evalStatement (body : Body) (frame : FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (stmt : StatementKind) :
    StepResult State TerminalOut :=
  match stmt with
  | .nop =>
    .step {
      frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }]
      callerMem
      mem
    }
  | .storageLive localId =>
    match getElem? body.locals localId with
    | none => .fault .unsupported
    | some localTy =>
      match getElem? frame.locals localId with
      | none => .fault .unsupported
      | some old =>
        match setElem? frame.locals localId (liveUninitSlot localTy) with
        | none => .fault .unsupported
        | some locals' =>
          match deallocateLocal mem old with
          | .error k => .fault k
          | .ok mem' =>
            .step {
              frames := [{
                frame with
                stmtIdx := frame.stmtIdx + 1
                locals := locals'
              }]
              callerMem
              mem := mem'
            }
  | .storageDead localId =>
    if Nat.beq localId 0 then
      .fault .unsupported
    else
      match getElem? frame.locals localId with
      | none => .fault .unsupported
      | some old =>
        match setElem? frame.locals localId .dead with
        | none => .fault .unsupported
        | some locals' =>
          match deallocateLocal mem old with
          | .error k => .fault k
          | .ok mem' =>
            .step {
              frames := [{
                frame with
                stmtIdx := frame.stmtIdx + 1
                locals := locals'
              }]
              callerMem
              mem := mem'
            }
  | .assign dst rvalue =>
    if !dst.projection.isEmpty then
      .fault .unsupported
    else
      match getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match evalRvalue body.locals frame.locals mem dstTy rvalue with
        | .error k => .fault k
        | .ok (val, localsAfterRval, memAfterRval) =>
          match writePlace localsAfterRval memAfterRval dst.localId dstTy
              val with
          | .error k => .fault k
          | .ok (localsAfterWrite, memAfterWrite) =>
            .step {
              frames := [{
                frame with
                stmtIdx := frame.stmtIdx + 1
                locals := localsAfterWrite
              }]
              callerMem
              mem := memAfterWrite
            }
  | .unsupported => .fault .unsupported

/-- Evaluate a `SwitchTargets` branch list against discriminant bits `discrBits`
at width `w`, matching `SwitchInt` in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`), `ScalarInt::try_from_uint` in
`compiler/rustc_middle/src/ty/consts/int.rs`, and `compareSwitchCase`
(`Scalar.fromUInt` -> `ScalarInt.tryFromUInt`) in
`Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`):

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

If `caseBits` overflows width `w` (`truncateBits w caseBits != caseBits`),
`Scalar.fromUInt` throws `.scalarInt (.integerConversionOverflow _)`, which
`ScalarOps.scalarError` maps to `.invalidProgram` (`.error .unsupported`);
otherwise `evalSwitchBranches` compares `truncateBits w discrBits ==
truncateBits w caseBits` up to the first matching branch, returning `.ok
otherwise` when no branch matches. -/
noncomputable def evalSwitchBranches (w : IntWidth) (discrBits : BitVec 128)
    (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Except FaultKind BasicBlockId
  | [] => .ok otherwise
  | (caseBits, target) :: rest =>
    if truncateBits w caseBits != caseBits then
      .error .unsupported
    else if truncateBits w discrBits == truncateBits w caseBits then
      .ok target
    else
      evalSwitchBranches w discrBits otherwise rest

/-- Evaluate a `SwitchTargets` branch list against a boolean discriminant
`discr`, matching `compareSwitchCase` in
`Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`), where each case
value is checked at 1-byte layout via `Scalar.fromUInt`
(`ScalarInt.tryFromUInt`) and compared via `ScalarOps.binary .Eq`
(`Scalar.toBool` on both operands):
- `caseBits` overflowing 1 byte (`truncateBits .i8 caseBits != caseBits`) fails
  `Scalar.fromUInt` with `.invalidProgram` (`.error .unsupported`);
- `0` (`false`) and `1` (`true`) match `!discr` and `discr`;
- `2..255` trigger `ScalarIntError.invalidBool` and fault with `.error
  .undefined`. -/
noncomputable def evalBoolSwitchBranches (discr : Bool)
    (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Except FaultKind BasicBlockId
  | [] => .ok otherwise
  | (caseBits, target) :: rest =>
    match evalConstLit .bool (.scalar caseBits) with
    | .ok (.bool false) =>
      if !discr then .ok target else evalBoolSwitchBranches discr otherwise rest
    | .ok (.bool true) =>
      if discr then .ok target else evalBoolSwitchBranches discr otherwise rest
    | .error k =>
      .error k
    | .ok _ =>
      .error .unsupported

/-- Evaluate a `SwitchTargets` branch list against a `char` discriminant
`discr`, matching `compareSwitchCase` in
`Miri.Interpreter.ExecutionMachine.stepHooks`
(`vendor/lean-miri/Miri/Interpreter/ExecutionMachine.lean`), where each case
value is checked at the 4-byte `char` layout via `Scalar.fromUInt`
(`ScalarInt.tryFromUInt`) and compared via `ScalarOps.binary .Eq`
(`Scalar.toChar` on both operands, then `IntegerOps.binaryChar`):
- `caseBits` overflowing 4 bytes fails `Scalar.fromUInt` with
  `.invalidProgram` (`.error .unsupported`);
- a `caseBits` that is not a Unicode scalar value triggers
  `ScalarIntError.invalidChar` and faults with `.error .undefined`;
- otherwise the case matches when it equals `discr`. These are exactly the
  outcomes of `evalConstLit .char (.scalar caseBits)`. -/
noncomputable def evalCharSwitchBranches (discr : Char)
    (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Except FaultKind BasicBlockId
  | [] => .ok otherwise
  | (caseBits, target) :: rest =>
    match evalConstLit .char (.scalar caseBits) with
    | .ok (.char c) =>
      if Nat.beq discr.toNat c.toNat then
        .ok target
      else
        evalCharSwitchBranches discr otherwise rest
    | .error k =>
      .error k
    | .ok _ =>
      .error .unsupported

/-- Assign the frame location to `(target, 0)`, matching
`Miri.Interpreter.ControlFlow.goToBlock` (`Miri/Interpreter/ControlFlow.lean`:
target block existence is checked at the start of the next step in `evalStep` /
`Step.step`). -/
noncomputable def jumpToBlock (frame : FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) (target : BasicBlockId) :
    StepResult State TerminalOut :=
  .step {
    frames := [{ frame with blockIdx := target, stmtIdx := 0 }]
    callerMem
    mem
  }

/-- Outcome of a failing `TerminatorKind.assert` under `panicStrategy` and
`unwind`, matching `rustc`'s `TerminatorKind::Assert` and `UnwindAction`
(`compiler/rustc_middle/src/mir/syntax.rs`, lines 853-863, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`),
`AssertKind::is_optional_overflow_check`
(`compiler/rustc_middle/src/mir/terminator.rs`, lines 164-168), codegen
elision (`compiler/rustc_codegen_ssa/src/mir/block.rs`, lines 714-716), and
`assert_panic` (`compiler/rustc_const_eval/src/interpret/step.rs`, lines
622-631):

> "Evaluates the operand, which must have type `bool`. If it is not equal to
> `expected`, initiates a panic. Initiating a panic corresponds to a `Call`
> terminator with some unspecified constant as the function to call, all the
> operands stored in the `AssertMessage` as parameters, and `None` for the
> destination. Keep in mind that the `cleanup` path is not necessarily executed
> even in the case of a panic, for example in `-C panic=abort`. If the
> assertion does not fail, execution continues at the specified basic block.
>
> When overflow checking is disabled and this is run-time MIR (as opposed to
> compile-time MIR that is used for CTFE), the following variants of this
> terminator behave as `goto target`:
> - `OverflowNeg(..)`,
> - `Overflow(op, ..)` if op is add, sub, mul, shl, shr, but NOT div or rem."
> (`compiler/rustc_middle/src/mir/syntax.rs`)
>
> "pub fn is_optional_overflow_check(&self) -> bool {
>     use AssertKind::*;
>     use BinOp::*;
>     matches!(
>         self,
>         OverflowNeg(..) | Overflow(Add | Sub | Mul | Shl | Shr, ..)
>     )
> }"
> (`compiler/rustc_middle/src/mir/terminator.rs`)
>
> "if !bx.sess().overflow_checks() && msg.is_optional_overflow_check() {
>     const_cond = Some(expected);
> }"
> (`compiler/rustc_codegen_ssa/src/mir/block.rs`)
>
> "Assert { ref cond, expected, ref msg, target, unwind } => {
>     let ignored =
>         M::ignore_optional_overflow_checks(self)
>             && msg.is_optional_overflow_check();
>     let cond_val =
>         self.read_scalar(&self.eval_operand(cond, None)?)?.to_bool()?;
>     if ignored || expected == cond_val {
>         self.go_to_block(target);
>     } else {
>         M::assert_panic(self, msg, unwind)?;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`)

Memory/alignment UB panics (`misalignedPtrDeref`, `nullPtrDeref`) always fault
`.undefined`. Non-optional safe panics (`boundsCheck`, `overflow .div`,
`overflow .rem`, `divByZero`, `remByZero`) terminate cleanly with
`.aborted callerMem` iff `hasLocalPanicHandler = false`,
`panicStrategy = .abort`, and `unwind ≠ .cleanup _`. When a crate defines a
crate-local `#[panic_handler]` (`hasLocalPanicHandler = true`), failing safe
asserts stay `.fault .unsupported` because the unverified handler can execute
arbitrary code or diverge. Optional overflow checks
(`overflow .add|.sub|.mul|.shl|.shr`, `overflowNeg`) abort under the same
conditions only when `overflowChecks = true`, that is, when the program was
captured under `-Coverflow-checks=yes`, where codegen keeps them as runtime
panics. With `overflowChecks = false` they stay `.fault .unsupported`: codegen
then elides inherited optional overflow asserts
(`#[rustc_inherit_overflow_checks]`) as `goto target` rather than aborting.
Under `--panic unwind` or `.cleanup _`, all failed safe asserts fail closed as
`.fault .unsupported`. -/
noncomputable def evalAssertFailure (msg : AssertKind)
    (panicStrategy : PanicStrategy) (unwind : UnwindAction)
    (callerMem : CallerMemory) (hasLocalPanicHandler : Bool := true)
    (overflowChecks : Bool := false) :
    StepResult State TerminalOut :=
  match msg with
  | .misalignedPtrDeref | .nullPtrDeref => .fault .undefined
  | .boundsCheck | .overflow .div | .overflow .rem
  | .divByZero | .remByZero =>
    if hasLocalPanicHandler then
      .fault .unsupported
    else
      match panicStrategy, unwind with
      | .abort, .continue_ | .abort, .unreachable | .abort, .terminate =>
        .done (.aborted callerMem)
      | _, _ => .fault .unsupported
  | .overflow .add | .overflow .sub | .overflow .mul | .overflow .shl
  | .overflow .shr | .overflowNeg =>
    if !overflowChecks || hasLocalPanicHandler then
      .fault .unsupported
    else
      match panicStrategy, unwind with
      | .abort, .continue_ | .abort, .unreachable | .abort, .terminate =>
        .done (.aborted callerMem)
      | _, _ => .fault .unsupported
  | .overflow _ | .unsupported => .fault .unsupported

/-- Evaluate a basic block's `TerminatorKind` when
`frame.stmtIdx == bb.statements.length`, matching `eval_terminator` in
`compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

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
>         Assert { ref cond, expected, ref msg, target, unwind } => {
>             ...
>         }
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`; `Assert` also matches
> `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`)

`Return` reads `_0`'s value (from memory with `loadIndirect` if `_0` is
`.indirect`); an uninitialized or dead `_0` faults with `.undefined`.
`Assert` evaluates `cond` to `.bool`; if equal to `expected` it jumps to
`target`, otherwise it delegates to `evalAssertFailure`. -/
noncomputable def evalTerminator (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory)
    (panicStrategy : PanicStrategy := .unwind)
    (hasLocalPanicHandler : Bool := true) :
    StepResult State TerminalOut :=
  match bb.terminator with
  | .goto target => jumpToBlock frame mem callerMem target
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match getElem? frame.locals 0 with
      | some (.immediate (some retVal)) =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some (.immediate none) | some .dead => .fault .undefined
      -- Profile v1 never creates partially moved tuples.
      | some (.partialTuple _) => .fault .unsupported
      | some (.indirect mplace) =>
        match getElem? body.locals 0 with
        | none => .fault .unsupported
        | some retTy =>
          match loadIndirect mem retTy mplace with
          | .ok (some retVal) => .done (.returned ⟨retVal, callerMem⟩)
          | .ok none => .fault .undefined
          | .error k => .fault k
      | none => .fault .unsupported
  | .unreachable =>
    .fault .undefined
  | .switchInt discr targets =>
    match evalPrimitiveOperand body.locals frame.locals mem discr with
    | .error k => .fault k
    | .ok (discrVal, localsAfterDiscr, memAfterDiscr) =>
      let targetRes : Except FaultKind BasicBlockId :=
        match discrVal with
        | .scalar sv =>
          evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches
        | .bool b =>
          evalBoolSwitchBranches b targets.otherwise targets.branches
        | .char c =>
          evalCharSwitchBranches c targets.otherwise targets.branches
        | _ =>
          -- An overflow pair is primitive-readable, but `compareSwitchCase`'s
          -- `ScalarOps.binary .Eq` rejects it, so only an empty branch list
          -- (which compares nothing) jumps to `otherwise`.
          match targets.branches with
          | [] => .ok targets.otherwise
          | _ :: _ => .error .unsupported
      match targetRes with
      | .error k => .fault k
      | .ok target =>
        jumpToBlock { frame with locals := localsAfterDiscr } memAfterDiscr
          callerMem target
  | .assert cond expected msg target unwind =>
    match evalPrimitiveOperand body.locals frame.locals mem cond with
    | .error k => .fault k
    | .ok (condVal, locals1, mem1) =>
      match condVal with
      | .bool b =>
        if b == expected then
          jumpToBlock { frame with locals := locals1 } mem1 callerMem target
        else
          evalAssertFailure msg panicStrategy unwind callerMem
            hasLocalPanicHandler
      | _ => .fault .unsupported
  | .unwindResume | .call _ _ _ _ _ | .coreCall _ _ _ _ _
  | .sysrootCall _ _ _ _ _ | .unsupported =>
    .fault .unsupported

/-!
## Profile v2 Memory, Reference, Raw-Pointer, and Core-Primitive Evaluation
-/

/-- Signed `BinOp.offset` in Profile v2: handles both non-negative and negative
`isize` element offsets inside a live allocation (failing `.undefined` on
out-of-bounds or overflow past `isize::MAX`).

`BinOp::Offset` has `ptr::offset` semantics
(`compiler/rustc_middle/src/mir/syntax.rs:1410-1411`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "* `Offset` has the same semantics as [`offset`](pointer::offset), except
>   that the second parameter may be a `usize` as well."

The interpreter computes `count * size` with an overflow check, then requires
the signed byte range to be in bounds of a live allocation
(`compiler/rustc_const_eval/src/interpret/intrinsics.rs:1034-1041`, same
pin):

> "// The offset must be in bounds starting from `ptr`.
> self.check_ptr_access_signed(
>     ptr,
>     offset_bytes,
>     CheckInAllocMsg::InboundsPointerArithmetic,
> )?;
> // This also implies that there is no overflow, so we are done.
> interp_ok(ptr.wrapping_signed_offset(offset_bytes, self))"

In `check_and_deref_ptr` (`memory.rs:531-534,546-552`), size 0 is always
accepted. Otherwise the range is `[offset, offset + size)` for `size >= 0`, or
`[offset - |size|, offset)` for `size < 0`, and it must lie within the
allocation. The non-negative case reuses `ptrAddInMem`. The negative case
checks `delta < 2^63`, provenance, liveness, `offset <= len`, and
`delta <= offset`. Both `isize` and `usize` counts (`IntWidth.isize`) are
accepted. Conservative divergences: a zero offset still requires a live
allocation, and a negative count with a zero-sized pointee and no provenance
is `.undefined`. -/
noncomputable def evalPtrOffsetV2 (mem : MemoryState) (elemSize : Nat)
    (p : PtrVal) (countVal : Val) : Except FaultKind Val :=
  match countVal with
  | .scalar sv =>
    if !IntWidth.beq sv.width .isize then
      .error .unsupported
    else
      match decodeScalar sv with
      | .ofNat n =>
        match ptrAddInMem mem elemSize p n with
        | .ok p' => .ok (.ptr p')
        | .error k => .error k
      | .negSucc k =>
        let absCount := k + 1
        let delta := absCount * elemSize
        if !Nat.blt delta isizeMaxBytes then
          .error .undefined
        else
          match p.allocId with
          | none => .error .undefined
          | some aid =>
            match findAllocation aid mem.allocations with
            | none => .error .undefined
            | some a =>
              if !a.live || !Nat.ble p.offsetBytes.toNat a.bytes.length ||
                  !Nat.ble delta p.offsetBytes.toNat then
                .error .undefined
              else
                .ok (.ptr { p with
                  offsetBytes := UInt64.ofNat (p.offsetBytes.toNat - delta) })
  | _ => .error .unsupported

/-- Promote local `localId` from `.immediate` to a stack `.indirect`
allocation in `mem` when its address is taken (`Rvalue.ref` /
`Rvalue.addressOf`), initializing stack bytes if the local holds an immediate
value.

This mirrors the interpreter's `force_allocation`, which `Rvalue::Ref` and
`Rvalue::RawPtr` both call
(`compiler/rustc_const_eval/src/interpret/place.rs:983-986,1004-1015`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "/// Ensures that a place is in memory, and returns where it is. If the place
> /// currently refers to a local that doesn't yet have a matching allocation,
> /// create such an allocation. This is essentially `force_to_memplace`.
> ...
> let mplace = self.allocate(local_layout, MemoryKind::Stack)?;
> // Preserve old value. (As an optimization, we can skip this if it
> // was uninit.)
> if !matches!(local_val, Immediate::Uninit) {
>     // We don't have to validate as we can assume the local was
>     // already valid for its type. We must not use any part of
>     // `place` here, that could be a projection to a part of the
>     // local!
>     self.write_immediate_to_mplace_no_validate(
>         local_val,
>         local_layout,
>         mplace.mplace,
>     )?;
> }"

A `.dead` local (after `StorageDead`) faults with `.undefined`. Unsized local
types fail closed. -/
noncomputable def promoteLocalToMemory (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (localId : LocalId) :
    Except FaultKind (MirTy × MemPlace × List LocalSlot × MemoryState) :=
  match getElem? bodyLocals localId, getElem? locals localId with
  | some _, some .dead => .error .undefined
  | some localTy, some (.indirect mplace) =>
    if isUnsizedTy localTy then
      .error .unsupported
    else
      .ok (localTy, mplace, locals, mem)
  | some localTy, some (.immediate optVal) =>
    match layoutOfTyV2 localTy with
    | none => .error .unsupported
    | some lay =>
      let (mem1, mplace) := allocateStack mem lay
      match optVal with
      | none =>
        match setElem? locals localId (.indirect mplace) with
        | some locals1 => .ok (localTy, mplace, locals1, mem1)
        | none => .error .unsupported
      | some v =>
        match storeIndirectV2 mem1 localTy mplace v with
        | .error k => .error k
        | .ok mem2 =>
          match setElem? locals localId (.indirect mplace) with
          | some locals1 => .ok (localTy, mplace, locals1, mem2)
          | none => .error .unsupported
  | _, _ => .error .unsupported

/-- Compute the zero-based element index for `ProjectionElem.constantIndex`
(`ConstantIndex { offset, min_length, from_end }` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "The thing being indexed must be at least this long -- otherwise, the
> projection is UB.
>
> For arrays this is always the exact length."
> "If `true`, `offset` is a 1-based offset from the end of the slice.
> Always false when indexing an array."

Returns `.error .undefined` when `len < minLength` or `offset` is out of
range. -/
noncomputable def constantIndexOffset (len off minLen : Nat)
    (fromEnd : Bool) : Except FaultKind Nat :=
  if !Nat.ble minLen len then
    .error .undefined
  else if fromEnd then
    if Nat.beq off 0 || !Nat.ble off len then
      .error .undefined
    else
      .ok (len - off)
  else
    if !Nat.blt off len then
      .error .undefined
    else
      .ok off

/-- Project one tuple, range, or fixed-size array element through an immediate
`Val` in Profile v2, factored out so `projectValFieldV2`'s equation lemma
stays free of `Quot.sound`. -/
noncomputable def projectOneElemV2 (ty : MirTy) (v : Val)
    (proj : ProjectionElem) : Except FaultKind (MirTy × Val) :=
  match proj with
  | .field idx fTy =>
    match ty with
    | .tuple ts =>
      match v with
      | .tuple vs =>
        match getElem? ts idx, getElem? vs idx with
        | some elemTy, some elemVal =>
          if !MirTy.beq elemTy fTy then
            .error .unsupported
          else
            .ok (elemTy, elemVal)
        | _, _ => .error .unsupported
      | _ => .error .unsupported
    | .rangeTo (.int .isize false) =>
      match v with
      | .rangeTo e =>
        if !Nat.beq idx 0 || !MirTy.beq fTy (.int .isize false) then
          .error .unsupported
        else
          .ok (.int .isize false,
            .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 e.toNat)⟩)
      | _ => .error .unsupported
    | .rangeFrom (.int .isize false) =>
      match v with
      | .rangeFrom s =>
        if !Nat.beq idx 0 || !MirTy.beq fTy (.int .isize false) then
          .error .unsupported
        else
          .ok (.int .isize false,
            .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 s.toNat)⟩)
      | _ => .error .unsupported
    | _ => .error .unsupported
  | .constantIndex off minLen fromEnd =>
    match ty with
    | .array elem len =>
      match v with
      | .array vs =>
        if !Nat.beq vs.length len then
          .error .unsupported
        else
          match constantIndexOffset len off minLen fromEnd with
          | .error k => .error k
          | .ok idx =>
            match getElem? vs idx with
            | some elemVal => .ok (elem, elemVal)
            | none => .error .undefined
      | _ => .error .unsupported
    | _ => .error .unsupported
  | .deref => .error .unsupported
  | .unsupported => .error .unsupported

/-- Project tuple, range, or fixed-size array elements through an immediate
`Val` in Profile v2. -/
noncomputable def projectValFieldV2 (ty : MirTy) (v : Val) :
    List ProjectionElem → Except FaultKind (MirTy × Val)
  | [] => .ok (ty, v)
  | proj :: rest =>
    match projectOneElemV2 ty v proj with
    | .error k => .error k
    | .ok (elemTy, elemVal) => projectValFieldV2 elemTy elemVal rest

/-- Project a memory-backed `MirTy` along `.constantIndex` / fixed-layout
`.field` projections (`overflowPair` and `RangeTo`/`RangeFrom`), returning the
leaf `MirTy` and cumulative byte offset from the base allocation offset. -/
noncomputable def projectMemoryLayoutV2 :
    MirTy → List ProjectionElem → Except FaultKind (MirTy × Nat)
  | ty, [] => .ok (ty, 0)
  | .array elem len, .constantIndex off minLen fromEnd :: rest =>
    match layoutOfTyV2 elem with
    | none => .error .unsupported
    | some elemLay =>
      match constantIndexOffset len off minLen fromEnd with
      | .error k => .error k
      | .ok idx =>
        match projectMemoryLayoutV2 elem rest with
        | .error k => .error k
        | .ok (leafTy, subOff) => .ok (leafTy, idx * elemLay.size + subOff)
  | .tuple [.int w s, .bool], .field 0 fTy :: rest =>
    if !MirTy.beq (.int w s) fTy then
      .error .unsupported
    else
      projectMemoryLayoutV2 (.int w s) rest
  | .tuple [.int w _, .bool], .field 1 fTy :: rest =>
    if !MirTy.beq .bool fTy then
      .error .unsupported
    else
      match projectMemoryLayoutV2 .bool rest with
      | .error k => .error k
      | .ok (leafTy, subOff) => .ok (leafTy, (intLayout w).size + subOff)
  | .rangeTo (.int .isize false), .field 0 fTy :: rest
  | .rangeFrom (.int .isize false), .field 0 fTy :: rest =>
    if !MirTy.beq (.int .isize false) fTy then
      .error .unsupported
    else
      projectMemoryLayoutV2 (.int .isize false) rest
  | _, _ => .error .unsupported

/-- Step a static `MirTy` along a tail of field and `ConstantIndex`
projections. -/
noncomputable def stepProjectedTyV2 : MirTy → List ProjectionElem → Option MirTy
  | ty, [] => some ty
  | .tuple fs, .field idx fTy :: rest =>
    match getElem? fs idx with
    | some t => if MirTy.beq t fTy then stepProjectedTyV2 t rest else none
    | none => none
  | .rangeTo (.int .isize false), .field 0 fTy :: rest
  | .rangeFrom (.int .isize false), .field 0 fTy :: rest =>
    if MirTy.beq (.int .isize false) fTy then stepProjectedTyV2 fTy rest else none
  | .array elem _, .constantIndex _ _ _ :: rest => stepProjectedTyV2 elem rest
  | _, _ => none

/-- Resolve the static `MirTy` of a `Place` in Profile v2, supporting single-
step leading `.deref`, `.field`, and `.constantIndex` projections. -/
noncomputable def placeProjectedTyV2 (bodyLocals : List MirTy)
    (place : Place) : Option MirTy :=
  match getElem? bodyLocals place.localId with
  | none => none
  | some baseTy =>
    match place.projection with
    | .deref :: rest =>
      match baseTy with
      | .ref _ pt | .rawPtr _ pt =>
        if isUnsizedTy pt then none else stepProjectedTyV2 pt rest
      | _ => none
    | projs => stepProjectedTyV2 baseTy projs

/-- Read a dereferenced projected place (`*p` followed by `.constantIndex` /
`.field` projections) in Profile v2. Both references (`isRef = true`) and raw
pointers (`isRef = false`) require base-pointer alignment to `pt`; references
additionally require the whole enclosing pointee `pt` to be live and in bounds,
while raw pointers check liveness/bounds on the projected leaf access. -/
noncomputable def readDerefProjectedV2 (locals : List LocalSlot)
    (mem : MemoryState) (isRef : Bool) (pt : MirTy) (slot : LocalSlot)
    (rest : List ProjectionElem) :
    Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState) :=
  if isUnsizedTy pt then
    .error .unsupported
  else
    match layoutOfTyV2 pt with
    | none => .error .unsupported
    | some ptLay =>
      let ptrRes : Except FaultKind (Option Val) :=
        match slot with
        | .dead | .partialTuple _ => .error .undefined
        | .immediate optVal => .ok optVal
        | .indirect mplace => loadIndirectV2 mem (.rawPtr .shared pt) mplace
      match ptrRes with
      | .error k => .error k
      | .ok none => .error .undefined
      | .ok (some (.ptr pv)) =>
        match projectMemoryLayoutV2 pt rest with
        | .error k => .error k
        | .ok (leafTy, subOff) =>
          match layoutOfTyV2 leafTy with
          | none => .error .unsupported
          | some leafLay =>
            match pv.allocId with
            | none =>
              let addr := pv.offsetBytes.toNat + subOff
              -- Base alignment to `ptLay.alignLog2` also guarantees leaf
              -- alignment for every non-packed `projectMemoryLayoutV2` offset.
              let badBaseAlign :=
                !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 ptLay.alignLog2)) 0
              let badRefBase :=
                isRef && (Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 ptLay.size)
              let badLeaf :=
                !Nat.blt addr (Nat.pow 2 64) || Nat.beq addr 0 || Nat.blt 0 leafLay.size
              if badBaseAlign || badRefBase || badLeaf then
                .error .undefined
              else
                match decodeValV2 profileV2TargetEndian leafTy [] with
                | .error k => .error k
                | .ok optVal => .ok (leafTy, optVal, locals, mem)
            | some aid =>
              match findAllocation aid mem.allocations with
              | none => .error .undefined
              | some a =>
                if !isAligned a pv.offsetBytes.toNat ptLay.alignLog2 ||
                    (isRef && (!a.live || !isInBounds a pv.offsetBytes.toNat ptLay.size)) ||
                    (!isRef && Nat.blt 0 leafLay.size && !a.live) ||
                    !Nat.blt (pv.offsetBytes.toNat + subOff) (Nat.pow 2 64) then
                  .error .undefined
                else
                  match loadIndirectV2 mem leafTy ⟨aid, pv.offsetBytes.toNat + subOff⟩ with
                  | .error k => .error k
                  | .ok optVal => .ok (leafTy, optVal, locals, mem)
      | .ok (some _) => .error .unsupported

/-- Per-field initialization of a tuple held directly in a local slot:
`some (vs.map some)` for an initialized immediate tuple `vs`, `some fs` for a
partially moved tuple, and `none` otherwise. -/
noncomputable def tupleSlotFields? : LocalSlot → Option (List (Option Val))
  | .immediate (some (.tuple vs)) => some (vs.map some)
  | .partialTuple fs => some fs
  | _ => none

/-- Read a projected `Place` in Profile v2, supporting unprojected locals,
immediate tuple/range/array `.field`/`.constantIndex` projections, and `.deref`
(optionally followed by sub-projections) on sized references and raw pointers.
`isMove` additionally deinitializes unprojected locals (and memory slots for
indirect stack moves). A `move` of a `.deref` place fails closed with
`.unsupported`.

A `move` of a single-level `.field` of a tuple held directly in a local
deinitializes only that field, leaving the local as a
`LocalSlot.partialTuple`. Rustc emits this shape under `-Coverflow-checks=yes`:
`assert(!move (_t.1: bool))` followed by `_r = move (_t.0: T)` on an
overflow pair `_t`. The moved field takes its `liveUninitSlot` value, as a
moved unprojected local does, so reading it again faults with `.undefined`
unless it is zero-sized. Reading a partially moved tuple as a whole also
faults with `.undefined`. Once every field is uninitialized the slot is
`.immediate none` again, the state a whole-tuple move leaves. MIR leaves open
whether a move deinitializes its place (see below), but the tuple is a local
rather than caller memory, so a body that never reads the moved field again,
as every verified body must, behaves the same under either reading. Field
moves out of `.indirect` locals and nested field moves fail closed with
`.unsupported`.

The deref case follows the Reference
(`src/behavior-considered-undefined.md:26-28`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`):

> "* Accessing (loading from or storing to) a place that is [dangling] or
>   [based on a misaligned pointer]."

The interpreter turns `*p` into a place aligned for the pointee type
(`deref_pointer`), and `get_place_alloc` checks bounds and liveness before
alignment (`compiler/rustc_const_eval/src/interpret/place.rs:490-497`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "let (size, _align) = self
>     .size_and_align_of_val(mplace)?
>     .unwrap_or((mplace.layout.size, mplace.layout.align.abi));
> // We check alignment separately, and *after* checking everything else.
> // If an access is both OOB and misaligned, we want to see the bounds error.
> let a = self.get_ptr_alloc(mplace.ptr(), size)?;
> self.check_misalign(mplace.mplace.misaligned, CheckAlignMsg::BasedOn)?;"

`get_ptr_alloc` skips the bounds and liveness checks for size 0
(`check_and_deref_ptr`). `loadIndirectV2` reuses `readBytes`, which has
exactly that split.

`move` of a `.deref` place is rejected because MIR leaves its effect
unspecified (`compiler/rustc_middle/src/mir/syntax.rs:1310-1319`, same
`rust-lang/rust` pin):

> "Creates a value by performing loading the place, just like the `Copy`
> operand.
>
> This *may* additionally overwrite the place with `uninit` bytes, depending
> on how we decide in [UCG#188]. You should not emit MIR that may attempt a
> subsequent second load of this place without first re-initializing it.
>
> **Needs clarification:** The operational impact of `Move` is unclear.
> Currently (both in Miri and codegen) it has no effect at all unless it
> appears in an argument to `Call`; for `Call` it allows the argument to be
> passed to the callee "in-place", i.e. the callee might just get a reference
> to this place instead of a full copy."

Deinitializing the pointee could expose `uninit` caller bytes on return
(`extractCallerMemory`) where the real program leaves the old bytes, and
treating the move as a copy would pick the other resolution. Failing closed
avoids committing to either. -/
noncomputable def readPlaceV2 (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (isMove : Bool) (place : Place) :
    Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState) :=
  match getElem? bodyLocals place.localId, getElem? locals place.localId with
  | some _, some .dead => .error .undefined
  | some baseTy, some slot =>
    match place.projection with
    | [] =>
      if !isSupportedV2LocalTy baseTy then
        .error .unsupported
      else
        match slot with
        | .dead => .error .undefined
        | .partialTuple _ => .error .undefined
        | .immediate optVal =>
          if isMove then
            match setElem? locals place.localId (liveUninitSlot baseTy) with
            | some locals1 => .ok (baseTy, optVal, locals1, mem)
            | none => .error .unsupported
          else
            .ok (baseTy, optVal, locals, mem)
        | .indirect mplace =>
          match loadIndirectV2 mem baseTy mplace with
          | .error k => .error k
          | .ok optVal =>
            if isMove then
              match deinitIndirectV2 mem baseTy mplace with
              | .ok mem1 => .ok (baseTy, optVal, locals, mem1)
              | .error k => .error k
            else
              .ok (baseTy, optVal, locals, mem)
    | .deref :: rest =>
      if isMove then
        .error .unsupported
      else if !rest.isEmpty then
        match baseTy with
        | .ref _ pt =>
          readDerefProjectedV2 locals mem true pt slot rest
        | .rawPtr _ pt =>
          readDerefProjectedV2 locals mem false pt slot rest
        | _ => .error .unsupported
      else
        match baseTy with
        | .ref _ pt | .rawPtr _ pt =>
          if isUnsizedTy pt then
            .error .unsupported
          else
            match layoutOfTyV2 pt with
            | none => .error .unsupported
            | some lay =>
              let ptrRes : Except FaultKind (Option Val) :=
                match slot with
                | .dead | .partialTuple _ => .error .undefined
                | .immediate optVal => .ok optVal
                | .indirect mplace => loadIndirectV2 mem baseTy mplace
              match ptrRes with
              | .error k => .error k
              | .ok none => .error .undefined
              | .ok (some (.ptr pv)) =>
                match pv.allocId with
                -- No provenance: only a zero-sized access at a non-null
                -- aligned address is accepted (`without_provenance` permits
                -- zero-sized accesses "if suitably aligned"; see
                -- `library/core/src/ptr/mod.rs:887-890` at `rust-lang/rust`
                -- `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). Null is
                -- rejected even for ZSTs. That matches `core::ptr` ("*every*
                -- non-null pointer", `ptr/mod.rs:19`) and is stricter than
                -- the Reference ("even if it is a null pointer",
                -- `behavior-considered-undefined.md:142-143` at
                -- `ad35aca481751a06afeb23820a672b0f3b11a476`) and rustc's
                -- `check_null.rs:69`. The two sources conflict for
                -- integer-derived pointers: the Reference
                -- (`types/pointer.md:73`) says an integer-*transmuted* pointer
                -- "may not be dereferenced (not even if `T` has [size zero])",
                -- whereas `core::ptr` permits the zero-sized access. This arm
                -- follows `core::ptr`, the library contract unsafe code is
                -- written against.
                | none =>
                  if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 lay.size ||
                      !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then
                    .error .undefined
                  else
                    match decodeValV2 profileV2TargetEndian pt [] with
                    | .error k => .error k
                    | .ok optVal => .ok (pt, optVal, locals, mem)
                | some aid =>
                  match loadIndirectV2 mem pt ⟨aid, pv.offsetBytes.toNat⟩ with
                  | .error k => .error k
                  | .ok optVal => .ok (pt, optVal, locals, mem)
              | .ok (some _) => .error .unsupported
        | _ => .error .unsupported
    | .field idx fTy :: rest =>
      if isMove then
        if !rest.isEmpty then
          .error .unsupported
        else
          match slot with
          | .dead | .immediate none => .error .undefined
          | _ =>
            match baseTy, tupleSlotFields? slot with
            | .tuple ts, some fs =>
              match getElem? ts idx, getElem? fs idx with
              | some elemTy, some (some elemVal) =>
                if !MirTy.beq elemTy fTy then
                  .error .unsupported
                else
                  let movedVal : Option Val :=
                    match liveUninitSlot elemTy with
                    | .immediate v => v
                    | _ => none
                  match setElem? fs idx movedVal with
                  | some fs' =>
                    let slot' : LocalSlot :=
                      if fs'.all Option.isNone then .immediate none
                      else .partialTuple fs'
                    match setElem? locals place.localId slot' with
                    | some locals1 => .ok (elemTy, some elemVal, locals1, mem)
                    | none => .error .unsupported
                  | none => .error .unsupported
              | some _, some none => .error .undefined
              | _, _ => .error .unsupported
            | _, _ => .error .unsupported
      else
        match slot with
        | .dead | .immediate none => .error .undefined
        | .immediate (some v) =>
          match projectValFieldV2 baseTy v (.field idx fTy :: rest) with
          | .error k => .error k
          | .ok (fty, fv) => .ok (fty, some fv, locals, mem)
        | .indirect mplace =>
          match projectMemoryLayoutV2 baseTy (.field idx fTy :: rest) with
          | .error k => .error k
          | .ok (leafTy, subOff) =>
            match loadIndirectV2 mem leafTy
                ⟨mplace.allocId, mplace.offset + subOff⟩ with
            | .error k => .error k
            | .ok optVal => .ok (leafTy, optVal, locals, mem)
        | .partialTuple fs =>
          if !rest.isEmpty then
            .error .unsupported
          else
            match baseTy with
            | .tuple ts =>
              match getElem? ts idx, getElem? fs idx with
              | some elemTy, some (some elemVal) =>
                if !MirTy.beq elemTy fTy then .error .unsupported
                else .ok (elemTy, some elemVal, locals, mem)
              | some _, some none => .error .undefined
              | _, _ => .error .unsupported
            | _ => .error .unsupported
    | .constantIndex _ _ _ :: _ =>
      if isMove then
        .error .unsupported
      else
        match slot with
        | .dead | .immediate none => .error .undefined
        | .partialTuple _ => .error .unsupported
        | .immediate (some v) =>
          match projectValFieldV2 baseTy v place.projection with
          | .error k => .error k
          | .ok (fty, fv) => .ok (fty, some fv, locals, mem)
        | .indirect mplace =>
          match projectMemoryLayoutV2 baseTy place.projection with
          | .error k => .error k
          | .ok (leafTy, subOff) =>
            match loadIndirectV2 mem leafTy
                ⟨mplace.allocId, mplace.offset + subOff⟩ with
            | .error k => .error k
            | .ok optVal => .ok (leafTy, optVal, locals, mem)
    | .unsupported :: _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Evaluate an immutable `.rodata` constant reference/slice by allocating a
read-only provenance-free `Allocation` in `mem` and checking `refValidInMem`
for reference types. Mutable `&mut`/`*mut` constants into read-only memory and
out-of-range sizes, alignments, offsets, or lengths fail closed with
`.unsupported`. -/
noncomputable def evalRodataRefConstV2 (ty : MirTy) (bytes : List RodataByte)
    (alignLog2 offsetBytes : Nat) (sliceLen : Option Nat)
    (locals : List LocalSlot) (mem : MemoryState) :
    Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState) :=
  if !Nat.blt bytes.length isizeMaxBytes || !Nat.ble alignLog2 29 ||
      !Nat.blt offsetBytes (Nat.pow 2 64) then
    .error .unsupported
  else
    let allocBytes := bytes.map rodataByteToAllocByte
    let (mem1, aid) := allocRodataMemory mem allocBytes alignLog2
    let ptr : PtrVal := ⟨some aid, UInt64.ofNat offsetBytes, .isize⟩
    match ty, sliceLen with
    | .ref reqMut (.slice elem), some len =>
      if !Nat.blt len (Nat.pow 2 64) then
        .error .unsupported
      else if Mutability.beq reqMut .mut then
        .error .unsupported
      else
        let v : Val := .slicePtr ptr (UInt64.ofNat len)
        match refValidInMem mem1 .shared (.slice elem) v with
        | .error k => .error k
        | .ok () => .ok (ty, some v, locals, mem1)
    | .rawPtr reqMut (.slice _), some len =>
      if !Nat.blt len (Nat.pow 2 64) then
        .error .unsupported
      else if Mutability.beq reqMut .mut then
        .error .unsupported
      else
        .ok (ty, some (.slicePtr ptr (UInt64.ofNat len)), locals, mem1)
    | .ref reqMut pt, none =>
      if isUnsizedTy pt then
        .error .unsupported
      else if Mutability.beq reqMut .mut then
        .error .unsupported
      else
        let v : Val := .ptr ptr
        match refValidInMem mem1 .shared pt v with
        | .error k => .error k
        | .ok () => .ok (ty, some v, locals, mem1)
    | .rawPtr reqMut pt, none =>
      if isUnsizedTy pt then
        .error .unsupported
      else if Mutability.beq reqMut .mut then
        .error .unsupported
      else
        .ok (ty, some (.ptr ptr), locals, mem1)
    | _, _ => .error .unsupported

/-- Stage 1 of Profile v2 operand evaluation. -/
noncomputable def evalOperandToSlotV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) :
    Operand → Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState)
  | .copy place => readPlaceV2 bodyLocals locals mem false place
  | .move place => readPlaceV2 bodyLocals locals mem true place
  | .constant c =>
    match c.lit with
    | .scalar _ | .zeroSized =>
      match evalConstLit c.ty c.lit with
      | .ok v => .ok (c.ty, some v, locals, mem)
      | .error k => .error k
    | .rodataBytes bytes =>
      if !isSupportedV2DataTy c.ty then
        .error .unsupported
      else
        let allocBytes := bytes.map rodataByteToAllocByte
        match decodeValV2 profileV2TargetEndian c.ty allocBytes with
        | .ok (some v) => .ok (c.ty, some v, locals, mem)
        | .ok none => .error .undefined
        | .error k => .error k
    | .rodataRef bytes alignLog2 offsetBytes sliceLen =>
      evalRodataRefConstV2 c.ty bytes alignLog2 offsetBytes sliceLen locals mem

/-- Stage 2 of Profile v2 operand evaluation for primitive values. -/
noncomputable def evalPrimitiveOperandV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match evalOperandToSlotV2 bodyLocals locals mem opnd with
  | .error k => .error k
  | .ok (ty, optVal, locals1, mem1) =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match optVal with
      | some v => .ok (v, locals1, mem1)
      | none => .error .undefined

/-- Evaluate a list of operands left-to-right in Profile v2, requiring each
operand to be initialized. -/
noncomputable def evalArgOperandsV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) :
    List Operand → Except FaultKind (List (MirTy × Val) × List LocalSlot × MemoryState)
  | [] => .ok ([], locals, mem)
  | opnd :: rest =>
    match evalOperandToSlotV2 bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (_, none, _, _) => .error .undefined
    | .ok (ty, some v, locals1, mem1) =>
      match evalArgOperandsV2 bodyLocals locals1 mem1 rest with
      | .error k => .error k
      | .ok (vs, locals2, mem2) => .ok ((ty, v) :: vs, locals2, mem2)

/-- Extract values only from an argument list when tuple-constructing. -/
noncomputable def argValues : List (MirTy × Val) → List Val
  | [] => []
  | (_, v) :: rest => v :: argValues rest

/-- Return `true` when `ty` is a `*const T` raw pointer type. -/
noncomputable def isConstRawPtrTy : MirTy → Bool
  | .rawPtr .shared _ => true
  | _ => false

/-- Check pointer-to-pointer cast compatibility in Profile v2 (preserving
provenance while disallowing forging references or mismatched slice elements).

`CastKind::PtrToPtr` is the identity on the pointer value whenever source and
target have the same size
(`compiler/rustc_const_eval/src/interpret/cast.rs:197-200`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "// Handle casting any ptr to raw ptr (might be a wide ptr).
> if cast_to.size == src.layout.size {
>     // Thin or wide pointer that just has the ptr kind of target type
>     // changed.
>     return interp_ok(ImmTy::from_immediate(**src, cast_to));"

Profile v2 supports thin-to-thin casts, and wide `[E]`-to-`[E]` casts with
the same element type. Both preserve the address, provenance, and length.
Dropping the metadata (wide to thin, `cast.rs:201-207`) fails closed with
`.unsupported`. Only raw-pointer sources are accepted, because MIR never
expresses a reference-to-raw conversion as a cast (see `CastKind.ptrToPtr`).

A `*const T` to `*mut T` cast also fails closed with `.unsupported`. Profile
v2 models no aliasing rules, and `allocateStack` makes every local's
allocation writable. In MIR that `rustc` accepts, the cast is the only way a
v2 body can obtain a writable pointer into a local it may not mutate
(`&raw const x as *mut T` with `x` not `mut`). The Rust Reference makes
writing through such a pointer undefined behavior
(`src/behavior-considered-undefined.md:50-57`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`):

> "* Mutating immutable bytes.
>   ...
>   The bytes owned by an immutable binding or immutable `static` are
>   immutable, unless those bytes are part of an [`UnsafeCell<U>`]."

The borrow checker rejects `&raw mut x` unless `x` is `mut`, and `&raw mut *p`
for `p : *const T`; Profile v2 has no `UnsafeCell`; and `writePlaceV2`
refuses stores through `*const T`. Refusing this cast removes that route. -/
noncomputable def evalPtrToPtrCastV2 (srcTy : MirTy) (srcVal : Val)
    (castTy : MirTy) : Except FaultKind Val :=
  match castTy with
  | .rawPtr castMut castPt =>
    if isConstRawPtrTy srcTy && Mutability.beq castMut .mut then
      .error .unsupported
    else
      match srcTy, srcVal with
      | .rawPtr _ srcPt, .ptr p =>
        if isUnsizedTy srcPt || isUnsizedTy castPt then
          .error .unsupported
        else
          .ok (.ptr p)
      | .rawPtr _ (.slice srcElem), .slicePtr p len =>
        match castPt with
        | .slice castElem =>
          if MirTy.beq srcElem castElem then
            .ok (.slicePtr p len)
          else
            .error .unsupported
        | _ => .error .unsupported
      | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Evaluate `Rvalue.ref` in Profile v2 (`&local`, or the reborrow `&*r` of a
reference local `r`).

`Rvalue::Ref` forces the place into memory and yields a pointer to it
(`compiler/rustc_const_eval/src/interpret/step.rs:208-211`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "Ref(_, borrow_kind, place) => {
>     let src = self.eval_place(place)?;
>     let place = self.force_allocation(&src)?;
>     let mut val = ImmTy::from_immediate(place.to_ref(self), dest.layout);"

The value produced must be a valid reference, so `refValidInMem` checks it.
Retagging is not modeled; see `BodyVerifiedV2`. A `&mut *r` through a shared
`r : &T` returns `.undefined`, an arm that MIR type checking makes
unreachable. `&*p` for a raw pointer `p` is `.unsupported`. A body containing
it would mix reference and raw-pointer locals, which `BodyStaticAdmittedV2`
rejects anyway. -/
noncomputable def evalRefRvalueV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (dstTy : MirTy)
    (reqMut : Mutability) (place : Place) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match place.projection with
  | [] =>
    match promoteLocalToMemory bodyLocals locals mem place.localId with
    | .error k => .error k
    | .ok (localTy, mplace, locals1, mem1) =>
      if !MirTy.beq dstTy (.ref reqMut localTy) then
        .error .unsupported
      else
        let rv : Val := .ptr ⟨some mplace.allocId, UInt64.ofNat mplace.offset, .isize⟩
        match refValidInMem mem1 reqMut localTy rv with
        | .error k => .error k
        | .ok () => .ok (rv, locals1, mem1)
  | [.deref] =>
    match getElem? bodyLocals place.localId, getElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some baseTy, some slot =>
      match baseTy with
      | .ref srcMut pt =>
        if Mutability.beq srcMut .shared && Mutability.beq reqMut .mut then
          .error .undefined
        else if !MirTy.beq dstTy (.ref reqMut pt) then
          .error .unsupported
        else
          let ptrRes : Except FaultKind (Option Val) :=
            match slot with
            | .dead | .partialTuple _ => .error .undefined
            | .immediate optVal => .ok optVal
            | .indirect mplace => loadIndirectV2 mem baseTy mplace
          match ptrRes with
          | .error k => .error k
          | .ok none => .error .undefined
          | .ok (some v) =>
            match refValidInMem mem reqMut pt v with
            | .error k => .error k
            | .ok () => .ok (v, locals, mem)
      | _ => .error .unsupported
    | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Evaluate `Rvalue.addressOf` in Profile v2 (`&raw const/mut local`, or
`&raw const/mut *p` of a raw-pointer local `p`).

`Rvalue::RawPtr` also forces the place into memory (`promoteLocalToMemory`)
and produces a pointer without any validity check. The Reference permits a raw
borrow even of a place based on a misaligned pointer
(`src/behavior-considered-undefined.md:118-124`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`):

> "`&raw const`/`&raw mut` on such a place is allowed.
>
> `&`/`&mut` on a place requires the alignment of the field type (or else the
> program would be "producing an invalid value"), which generally is a less
> restrictive requirement than being based on an aligned pointer."

`&raw *r` for a reference `r` is `.unsupported`. A body containing it would
mix reference and raw-pointer locals, which `BodyStaticAdmittedV2` rejects
anyway. `&raw mut *p` through a `*const T` returns `.undefined`, like
`&mut *r` through a shared `r` in `evalRefRvalueV2`. MIR borrow checking makes
that arm unreachable, and refusing it keeps a `*const T` from yielding a
`*mut T` here, as `evalPtrToPtrCastV2` does for casts. -/
noncomputable def evalAddressOfRvalueV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (dstTy : MirTy)
    (reqMut : Mutability) (place : Place) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  match place.projection with
  | [] =>
    match promoteLocalToMemory bodyLocals locals mem place.localId with
    | .error k => .error k
    | .ok (localTy, mplace, locals1, mem1) =>
      if !MirTy.beq dstTy (.rawPtr reqMut localTy) then
        .error .unsupported
      else
        .ok (.ptr ⟨some mplace.allocId, UInt64.ofNat mplace.offset, .isize⟩, locals1, mem1)
  | [.deref] =>
    match getElem? bodyLocals place.localId, getElem? locals place.localId with
    | some _, some .dead => .error .undefined
    | some baseTy, some slot =>
      match baseTy with
      | .rawPtr srcMut pt =>
        if Mutability.beq srcMut .shared && Mutability.beq reqMut .mut then
          .error .undefined
        else if !MirTy.beq dstTy (.rawPtr reqMut pt) then
          .error .unsupported
        else
          let ptrRes : Except FaultKind (Option Val) :=
            match slot with
            | .dead | .partialTuple _ => .error .undefined
            | .immediate optVal => .ok optVal
            | .indirect mplace => loadIndirectV2 mem baseTy mplace
          match ptrRes with
          | .error k => .error k
          | .ok none => .error .undefined
          | .ok (some v) => .ok (v, locals, mem)
      | _ => .error .unsupported
    | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Evaluate an `Rvalue` in Profile v2.

The Profile v2 arms correspond to rustc as follows (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`).

- `.useRetag` is `Use(op, WithRetag::Yes)`
  (`compiler/rustc_middle/src/mir/syntax.rs:1364-1365`):

  > "/// Yields the operand unchanged, except for a potential retag.
  > Use(Operand<'tcx>, WithRetag),"

  Profile v2 does not model Stacked or Tree Borrows tags. Instead it
  re-validates every contained reference (`refsValidInMem`). A copied
  reference is produced and considered live
  (`src/behavior-considered-undefined.md:44-45`):

  > "  * Each time a reference or box is dereferenced or reborrowed, it is
  >     considered live.
  >   * Each time a reference or box is passed to or returned from a function,
  >     it is considered live."

  This under-approximates aliasing UB (see `BodyVerifiedV2`) and
  over-approximates validity UB by requiring initialized pointees.
- `.binaryOp .offset` is `BinOp::Offset` on a raw pointer whose result type
  equals the left operand type (see `evalPtrOffsetV2`).
- `.unaryOp .ptrMetadata` is `UnOp::PtrMetadata`
  (`compiler/rustc_middle/src/mir/syntax.rs:1608-1611`):

  > "Gets the metadata `M` from a `*const`/`*mut`/`&`/`&mut` to `impl
  > Pointee<Metadata = M>`.
  >
  > For example, this will give a `()` from `*const i32`, a `usize` from `&mut
  > [u8]`, or a `ptr::DynMetadata<dyn Foo>` (internally a pointer) from a `*mut
  > dyn Foo`."

  The interpreter returns the slice metadata, or `ImmTy::uninit` of `()` for
  thin pointers
  (`compiler/rustc_const_eval/src/interpret/operator.rs:487-500`). Lean
  returns `.unit` for thin pointers, which is equivalent for a ZST. For
  reference operands Lean also re-checks `refValidInMem`, which is
  conservative.
- `.cast .ptrToPtr` is `CastKind::PtrToPtr` (see `evalPtrToPtrCastV2`).
- `.cast .intToPtr` is `CastKind::PointerWithExposedProvenance` from `usize`.
  The result has no provenance, exactly as in the CTFE machine
  (`compiler/rustc_const_eval/src/interpret/machine.rs:743-746`):

  > "// Allow these casts, but make the pointer not dereferenceable.
  > // (I.e., they behave like transmutation.)
  > // This is correct because no pointers can ever be exposed in
  > // compile-time evaluation.
  > interp_ok(Pointer::without_provenance(addr))"

  At runtime the cast is "An address-to-pointer cast that picks up an exposed
  provenance" (`compiler/rustc_middle/src/mir/syntax.rs:1496`). Dropping
  provenance is therefore conservative: the pointer can be used only for
  zero-sized accesses.
- `.ref` and `.addressOf` are `Rvalue::Ref` and `Rvalue::RawPtr` (see
  `evalRefRvalueV2` and `evalAddressOfRvalueV2`).
- `.aggregateRangeTo` and `.aggregateRangeFrom` construct the one-field
  `core::ops::RangeTo { end }` and `RangeFrom { start }` with `Idx = usize`
  (field layout quoted at `MirTy.rangeTo`). -/
noncomputable def evalRvalueV2 (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (dstTy : MirTy) :
    Rvalue → Except FaultKind (Val × List LocalSlot × MemoryState)
  | .use opnd =>
    match evalOperandToSlotV2 bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals1, mem1) =>
      if !MirTy.beq srcTy dstTy then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals1, mem1)
        | none => .error .undefined
  | .useRetag opnd =>
    match evalOperandToSlotV2 bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals1, mem1) =>
      if !MirTy.beq srcTy dstTy then
        .error .unsupported
      else
        match optVal with
        | none => .error .undefined
        | some v =>
          if !refsValidInMem mem1 srcTy v then
            .error .undefined
          else
            .ok (v, locals1, mem1)
  | .binaryOp .offset lhs rhs =>
    match evalOperandToSlotV2 bodyLocals locals mem lhs with
    | .error k => .error k
    | .ok (lhsTy, optLhsVal, locals1, mem1) =>
      match optLhsVal with
      | none => .error .undefined
      | some (.ptr p) =>
        match lhsTy with
        | .rawPtr _ pt =>
          if isUnsizedTy pt || !MirTy.beq dstTy lhsTy then
            .error .unsupported
          else
            match layoutOfTyV2 pt with
            | none => .error .unsupported
            | some lay =>
              match evalOperandToSlotV2 bodyLocals locals1 mem1 rhs with
              | .error k => .error k
              | .ok (_, none, _, _) => .error .undefined
              | .ok (_, some rVal, locals2, mem2) =>
                match evalPtrOffsetV2 mem2 lay.size p rVal with
                | .error k => .error k
                | .ok res => .ok (res, locals2, mem2)
        | _ => .error .unsupported
      | some _ => .error .unsupported
  | .binaryOp op lhs rhs =>
    match evalPrimitiveOperandV2 bodyLocals locals mem lhs with
    | .error k => .error k
    | .ok (lVal, locals1, mem1) =>
      match evalPrimitiveOperandV2 bodyLocals locals1 mem1 rhs with
      | .error k => .error k
      | .ok (rVal, locals2, mem2) =>
        match evalBinOp op lVal rVal with
        | .error k => .error k
        | .ok res => .ok (res, locals2, mem2)
  | .unaryOp .ptrMetadata opnd =>
    match evalOperandToSlotV2 bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (_, none, _, _) => .error .undefined
    | .ok (srcTy, some val, locals1, mem1) =>
      match srcTy, val with
      | .ref srcMut (.slice elem), .slicePtr p len =>
        if !MirTy.beq dstTy (.int .isize false) then
          .error .unsupported
        else
          match refValidInMem mem1 srcMut (.slice elem) (.slicePtr p len) with
          | .error k => .error k
          | .ok () =>
            .ok (.scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 len.toNat)⟩,
              locals1, mem1)
      | .rawPtr _ (.slice _), .slicePtr _ len =>
        if !MirTy.beq dstTy (.int .isize false) then
          .error .unsupported
        else
          .ok (.scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 len.toNat)⟩,
            locals1, mem1)
      | .ref srcMut pt, .ptr p =>
        if isUnsizedTy pt || !MirTy.beq dstTy .unit then
          .error .unsupported
        else
          match refValidInMem mem1 srcMut pt (.ptr p) with
          | .error k => .error k
          | .ok () => .ok (.unit, locals1, mem1)
      | .rawPtr _ pt, .ptr _ =>
        if isUnsizedTy pt || !MirTy.beq dstTy .unit then
          .error .unsupported
        else
          .ok (.unit, locals1, mem1)
      | _, _ => .error .unsupported
  | .unaryOp op opnd =>
    match evalPrimitiveOperandV2 bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (v, locals1, mem1) =>
      match evalUnOp op v with
      | .error k => .error k
      | .ok res => .ok (res, locals1, mem1)
  | .cast .intToInt opnd castTy =>
    match evalOperandToSlotV2 bodyLocals locals mem opnd with
    | .error k => .error k
    | .ok (srcTy, optCastVal, locals1, mem1) =>
      if !isIntLikeTy srcTy || !MirTy.beq dstTy castTy then
        .error .unsupported
      else
        match optCastVal with
        | some castV =>
          match evalIntToIntCast castV castTy with
          | .error k => .error k
          | .ok res => .ok (res, locals1, mem1)
        | none => .error .undefined
  | .cast .ptrToPtr opnd castTy =>
    if !MirTy.beq dstTy castTy then
      .error .unsupported
    else
      match evalOperandToSlotV2 bodyLocals locals mem opnd with
      | .error k => .error k
      | .ok (_, none, _, _) => .error .undefined
      | .ok (srcTy, some v, locals1, mem1) =>
        match evalPtrToPtrCastV2 srcTy v castTy with
        | .error k => .error k
        | .ok res => .ok (res, locals1, mem1)
  | .cast .intToPtr opnd castTy =>
    if !MirTy.beq dstTy castTy then
      .error .unsupported
    else
      match castTy with
      | .rawPtr _ pt =>
        if isUnsizedTy pt then
          .error .unsupported
        else
          match evalOperandToSlotV2 bodyLocals locals mem opnd with
          | .error k => .error k
          | .ok (.int .isize false, some (.scalar sv), locals1, mem1) =>
            .ok (.ptr ⟨none, UInt64.ofNat sv.bits.toNat, .isize⟩, locals1, mem1)
          | .ok (_, none, _, _) => .error .undefined
          | .ok (_, _, _, _) => .error .unsupported
      | _ => .error .unsupported
  | .cast .unsize opnd castTy =>
    if !MirTy.beq dstTy castTy then
      .error .unsupported
    else
      match evalOperandToSlotV2 bodyLocals locals mem opnd with
      | .error k => .error k
      | .ok (_, none, _, _) => .error .undefined
      | .ok (srcTy, some v, locals1, mem1) =>
        match srcTy, castTy, v with
        | .ref srcMut (.array srcElem len), .ref dstMut (.slice dstElem), .ptr p =>
          if !MirTy.beq srcElem dstElem || !Nat.blt len (Nat.pow 2 64) then
            .error .unsupported
          else if Mutability.beq srcMut .shared &&
              Mutability.beq dstMut .mut then
            .error .undefined
          else
            match refValidInMem mem1 srcMut (.array srcElem len) (.ptr p) with
            | .error k => .error k
            | .ok () =>
              let sv : Val := .slicePtr p (UInt64.ofNat len)
              match refValidInMem mem1 dstMut (.slice dstElem) sv with
              | .error k => .error k
              | .ok () => .ok (sv, locals1, mem1)
        | .rawPtr srcMut (.array srcElem len),
          .rawPtr dstMut (.slice dstElem), .ptr p =>
          if !MirTy.beq srcElem dstElem || !Nat.blt len (Nat.pow 2 64) then
            .error .unsupported
          else if Mutability.beq srcMut .shared &&
              Mutability.beq dstMut .mut then
            .error .undefined
          else
            .ok (.slicePtr p (UInt64.ofNat len), locals1, mem1)
        | _, _, _ => .error .unsupported
  | .discriminant place =>
    if !place.projection.isEmpty then
      match readPlaceV2 bodyLocals locals mem false place with
      | .error k => .error k
      | .ok (srcTy, optVal, locals1, mem1) =>
        match srcTy with
        | .enum ety =>
          if !MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned) then
            .error .unsupported
          else
            evalDiscriminantOfVal ety optVal locals1 mem1
        | .ordering =>
          if !MirTy.beq dstTy (.int .i8 true) then
            .error .unsupported
          else
            evalOrderingDiscriminantOfVal optVal locals1 mem1
        | _ => .error .unsupported
    else
      match getElem? bodyLocals place.localId, getElem? locals place.localId with
      | some _, some .dead => .error .undefined
      | some srcTy, some (.immediate optVal) =>
        match srcTy with
        | .enum ety =>
          if !MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned) then
            .error .unsupported
          else
            evalDiscriminantOfVal ety optVal locals mem
        | .ordering =>
          if !MirTy.beq dstTy (.int .i8 true) then
            .error .unsupported
          else
            evalOrderingDiscriminantOfVal optVal locals mem
        | _ => .error .unsupported
      | some srcTy, some (.indirect mplace) =>
        match srcTy with
        | .enum ety =>
          if !MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned) then
            .error .unsupported
          else
            match loadIndirectV2 mem srcTy mplace with
            | .error k => .error k
            | .ok optVal => evalDiscriminantOfVal ety optVal locals mem
        | .ordering =>
          if !MirTy.beq dstTy (.int .i8 true) then
            .error .unsupported
          else
            match loadIndirectV2 mem srcTy mplace with
            | .error k => .error k
            | .ok optVal => evalOrderingDiscriminantOfVal optVal locals mem
        | _ => .error .unsupported
      | _, _ => .error .unsupported
  | .ref reqMut place => evalRefRvalueV2 bodyLocals locals mem dstTy reqMut place
  | .addressOf reqMut place => evalAddressOfRvalueV2 bodyLocals locals mem dstTy reqMut place
  | .aggregateTuple fields =>
    match dstTy with
    | .tuple fieldTys =>
      match evalArgOperandsV2 bodyLocals locals mem fields with
      | .error k => .error k
      | .ok (typedVals, locals1, mem1) =>
        let vs := argValues typedVals
        if !checkValV2List vs fieldTys then
          .error .unsupported
        else
          .ok (.tuple vs, locals1, mem1)
    | _ => .error .unsupported
  | .aggregateArray elemTy elems =>
    match dstTy with
    | .array dstElem dstLen =>
      if !MirTy.beq elemTy dstElem || !Nat.beq elems.length dstLen then
        .error .unsupported
      else
        match evalArgOperandsV2 bodyLocals locals mem elems with
        | .error k => .error k
        | .ok (typedVals, locals1, mem1) =>
          let vs := argValues typedVals
          if !checkValUniformV2 (fun v => checkValV2 v dstElem) vs then
            .error .unsupported
          else
            .ok (.array vs, locals1, mem1)
    | _ => .error .unsupported
  | .repeat_ op elemTy count =>
    match dstTy with
    | .array dstElem dstLen =>
      if !MirTy.beq elemTy dstElem || !Nat.beq count dstLen then
        .error .unsupported
      else
        match evalOperandToSlotV2 bodyLocals locals mem op with
        | .error k => .error k
        | .ok (opTy, optVal, locals1, mem1) =>
          if !MirTy.beq opTy elemTy then
            .error .unsupported
          else
            match optVal with
            | none => .error .undefined
            | some v =>
              if !checkValV2 v elemTy then
                .error .unsupported
              else
                .ok (.array (List.replicate count v), locals1, mem1)
    | _ => .error .unsupported
  | .aggregateRangeTo elemTy endOp =>
    match elemTy with
    | .int .isize false =>
      if !MirTy.beq dstTy (.rangeTo (.int .isize false)) then
        .error .unsupported
      else
        match evalOperandToSlotV2 bodyLocals locals mem endOp with
        | .error k => .error k
        | .ok (.int .isize false, some (.scalar sv), locals1, mem1) =>
          .ok (.rangeTo (UInt64.ofNat sv.bits.toNat), locals1, mem1)
        | .ok (_, none, _, _) => .error .undefined
        | .ok (_, _, _, _) => .error .unsupported
    | _ => .error .unsupported
  | .aggregateRangeFrom elemTy startOp =>
    match elemTy with
    | .int .isize false =>
      if !MirTy.beq dstTy (.rangeFrom (.int .isize false)) then
        .error .unsupported
      else
        match evalOperandToSlotV2 bodyLocals locals mem startOp with
        | .error k => .error k
        | .ok (.int .isize false, some (.scalar sv), locals1, mem1) =>
          .ok (.rangeFrom (UInt64.ofNat sv.bits.toNat), locals1, mem1)
        | .ok (_, none, _, _) => .error .undefined
        | .ok (_, _, _, _) => .error .unsupported
    | _ => .error .unsupported
  | .cast .unsupported _ _ | .unsupported => .error .unsupported

/-- Update an immediate `Val` along a non-empty `.field` / `.constantIndex`
projection path in Profile v2. -/
noncomputable def updateValAtProjV2 :
    MirTy → Val → List ProjectionElem → Val → Except FaultKind Val
  | ty, _, [], newVal =>
    if checkValV2 newVal ty then .ok newVal else .error .unsupported
  | .array elem len, .array vs, .constantIndex off minLen fromEnd :: rest, newVal =>
    if !Nat.beq vs.length len then
      .error .unsupported
    else
      match constantIndexOffset len off minLen fromEnd with
      | .error k => .error k
      | .ok idx =>
        match getElem? vs idx with
        | none => .error .undefined
        | some oldElem =>
          match updateValAtProjV2 elem oldElem rest newVal with
          | .error k => .error k
          | .ok elem' =>
            match setElem? vs idx elem' with
            | some vs' => .ok (.array vs')
            | none => .error .unsupported
  | .tuple fs, .tuple vs, .field idx fTy :: rest, newVal =>
    match getElem? fs idx, getElem? vs idx with
    | some elemTy, some oldElem =>
      if !MirTy.beq elemTy fTy then
        .error .unsupported
      else
        match updateValAtProjV2 elemTy oldElem rest newVal with
        | .error k => .error k
        | .ok elem' =>
          match setElem? vs idx elem' with
          | some vs' => .ok (.tuple vs')
          | none => .error .unsupported
    | _, _ => .error .unsupported
  | .rangeTo (.int .isize false), .rangeTo oldEnd, .field 0 fTy :: rest,
    newVal =>
    if !MirTy.beq (.int .isize false) fTy then
      .error .unsupported
    else
      match updateValAtProjV2 (.int .isize false)
          (.scalar ⟨.isize, false, BitVec.ofNat 128 oldEnd.toNat⟩)
          rest newVal with
      | .error k => .error k
      | .ok (.scalar sv) => .ok (.rangeTo (UInt64.ofNat sv.bits.toNat))
      | .ok _ => .error .unsupported
  | .rangeFrom (.int .isize false), .rangeFrom oldStart, .field 0 fTy :: rest,
    newVal =>
    if !MirTy.beq (.int .isize false) fTy then
      .error .unsupported
    else
      match updateValAtProjV2 (.int .isize false)
          (.scalar ⟨.isize, false, BitVec.ofNat 128 oldStart.toNat⟩)
          rest newVal with
      | .error k => .error k
      | .ok (.scalar sv) => .ok (.rangeFrom (UInt64.ofNat sv.bits.toNat))
      | .ok _ => .error .unsupported
  | _, _, _, _ => .error .unsupported

/-- Validate a non-deref `.field` / `.constantIndex` projection tail against
`baseTy` before rvalue evaluation (`eval_rvalue_into_place` destination-first
order), returning `.error .undefined` for out-of-bounds `ConstantIndex`,
`.error .unsupported` for ill-typed or unmodeled projections, or `.ok leafTy`.
-/
noncomputable def validatePlaceProjV2 :
    MirTy → List ProjectionElem → Except FaultKind MirTy
  | ty, [] => .ok ty
  | .array elem len, .constantIndex off minLen fromEnd :: rest =>
    match constantIndexOffset len off minLen fromEnd with
    | .error k => .error k
    | .ok _ => validatePlaceProjV2 elem rest
  | .tuple fs, .field idx fTy :: rest =>
    match getElem? fs idx with
    | some t =>
      if MirTy.beq t fTy then validatePlaceProjV2 t rest
      else .error .unsupported
    | none => .error .unsupported
  | .rangeTo (.int .isize false), .field 0 fTy :: rest
  | .rangeFrom (.int .isize false), .field 0 fTy :: rest =>
    if MirTy.beq (.int .isize false) fTy then
      validatePlaceProjV2 (.int .isize false) rest
    else .error .unsupported
  | _, _ => .error .unsupported

/-- Destination of a Profile v2 store, resolved by `resolvePlaceDestV2`
before the value to store is computed: an unprojected local `localId`, a
projected local `localId`, a resolved indirect-local sub-place, the pointee
type `pointee` (with layout `lay`) of a dereferenced pointer local, or a
dereferenced projected sub-place. -/
inductive PlaceDestV2 where
  | local (localId : LocalId)
  | localProj (localId : LocalId) (baseTy : MirTy)
      (projs : List ProjectionElem)
  | indirectProj (leafTy : MirTy) (mplace : MemPlace) (subOff : Nat)
  | deref (pointee : MirTy) (lay : LayoutData) (pv : PtrVal)
  | derefProjected (pointee : MirTy) (ptLay : LayoutData)
      (leafTy : MirTy) (subOff : Nat) (pv : PtrVal)

/-- Resolve the destination `dst : Place` of a Profile v2 store against
`locals` and `mem`, without accessing the destination itself.

This is the place evaluation that `rustc` performs before it evaluates an
assignment's rvalue (`compiler/rustc_const_eval/src/interpret/step.rs:157-162`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub fn eval_rvalue_into_place(
> ...
>     let dest = self.eval_place(place)?;"

and `lean-miri` matches (`Miri/Interpreter/Rvalue.lean:49-53`: "Destination
evaluation is always first"). For `(*ptr)` (optionally followed by sub-
projections) it reads the pointer value out of `ptr`'s slot and checks the
pointer's static type, but checks nothing about the pointed-to allocation.
Those access checks belong to the store itself (`writePlaceDestV2`). An
unprojected local resolves to the local itself; whether it is stored in place
or in its stack allocation is decided at the store, as `rustc` does for
`Place::Local`.

Stores through `*const T` or `&T` return `.undefined`. MIR type checking
makes that arm unreachable. -/
noncomputable def resolvePlaceDestV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (dst : Place)
    (dstTy : MirTy) : Except FaultKind PlaceDestV2 :=
  match dst.projection with
  | [] => .ok (.local dst.localId)
  | [.deref] =>
    match getElem? bodyLocals dst.localId, getElem? locals dst.localId with
    | some _, some .dead => .error .undefined
    | some ptrTy, some slot =>
      match ptrTy with
      | .ref ptrMut pt | .rawPtr ptrMut pt =>
        if isUnsizedTy pt || !MirTy.beq pt dstTy then
          .error .unsupported
        else if !Mutability.beq ptrMut .mut then
          .error .undefined
        else
          match layoutOfTyV2 pt with
          | none => .error .unsupported
          | some lay =>
            let ptrRes : Except FaultKind (Option Val) :=
              match slot with
              | .dead | .partialTuple _ => .error .undefined
              | .immediate optVal => .ok optVal
              | .indirect mplace => loadIndirectV2 mem ptrTy mplace
            match ptrRes with
            | .error k => .error k
            | .ok none => .error .undefined
            | .ok (some (.ptr pv)) => .ok (.deref pt lay pv)
            | .ok (some _) => .error .unsupported
      | _ => .error .unsupported
    | _, _ => .error .unsupported
  | .deref :: rest =>
    match getElem? bodyLocals dst.localId, getElem? locals dst.localId with
    | some _, some .dead => .error .undefined
    | some ptrTy, some slot =>
      match ptrTy with
      | .ref ptrMut pt | .rawPtr ptrMut pt =>
        if isUnsizedTy pt then
          .error .unsupported
        else if !Mutability.beq ptrMut .mut then
          .error .undefined
        else
          match layoutOfTyV2 pt, projectMemoryLayoutV2 pt rest with
          | none, _ => .error .unsupported
          | _, .error k => .error k
          | some ptLay, .ok (leafTy, subOff) =>
            if !MirTy.beq leafTy dstTy then
              .error .unsupported
            else
              let ptrRes : Except FaultKind (Option Val) :=
                match slot with
                | .dead | .partialTuple _ => .error .undefined
                | .immediate optVal => .ok optVal
                | .indirect mplace => loadIndirectV2 mem ptrTy mplace
              match ptrRes with
              | .error k => .error k
              | .ok none => .error .undefined
              | .ok (some (.ptr pv)) =>
                .ok (.derefProjected pt ptLay leafTy subOff pv)
              | .ok (some _) => .error .unsupported
      | _ => .error .unsupported
    | _, _ => .error .unsupported
  | projs =>
    match getElem? bodyLocals dst.localId, getElem? locals dst.localId with
    | some _, some .dead => .error .undefined
    | some baseTy, some (.immediate _) =>
      match validatePlaceProjV2 baseTy projs with
      | .error k => .error k
      | .ok leafTy =>
        if !MirTy.beq leafTy dstTy then
          .error .unsupported
        else
          .ok (.localProj dst.localId baseTy projs)
    | some baseTy, some (.indirect mplace) =>
      match projectMemoryLayoutV2 baseTy projs with
      | .error k => .error k
      | .ok (leafTy, subOff) =>
        if !MirTy.beq leafTy dstTy then
          .error .unsupported
        else
          .ok (.indirectProj leafTy mplace subOff)
    | _, _ => .error .unsupported

/-- Store `val` of type `dstTy` at the destination `dest` resolved by
`resolvePlaceDestV2`, against the current `locals` and `mem`. Supports
unprojected locals, dereference stores `(*ptr) = val`, and projected
field/`ConstantIndex` places (requiring mutable provenance-backed live aligned
in-bounds storage).

A deref store uses the same access rules as `readPlaceV2`, implemented by
`storeIndirectV2` → `writeBytes`. Non-empty writes also require a `.mut`
allocation (`WriteToReadOnly`). A zero-sized write performs no mutation
(`src/behavior-considered-undefined.md:57`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`):

> "A mutation is any write of more than 0 bytes which overlaps with any of the
> relevant bytes (even if that write does not change the memory contents)." -/
noncomputable def writePlaceDestV2 (locals : List LocalSlot)
    (mem : MemoryState) (dest : PlaceDestV2) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlot × MemoryState) :=
  if !checkValV2 val dstTy then
    .error .unsupported
  else
    match dest with
    | .local localId =>
      match getElem? locals localId with
      | none => .error .unsupported
      | some .dead => .error .undefined
      | some (.immediate _) | some (.partialTuple _) =>
        match setElem? locals localId (.immediate (some val)) with
        | some locals1 => .ok (locals1, mem)
        | none => .error .unsupported
      | some (.indirect mplace) =>
        match storeIndirectV2 mem dstTy mplace val with
        | .ok mem1 => .ok (locals, mem1)
        | .error k => .error k
    | .deref pt lay pv =>
      match pv.allocId with
      -- No provenance: only a zero-sized write at a non-null
      -- aligned address is accepted. Null is rejected even for
      -- ZSTs (conservative). See the matching arm of `readPlaceV2`.
      | none =>
        if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 lay.size ||
            !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then
          .error .undefined
        else
          match encodeValV2 profileV2TargetEndian pt val with
          | .error k => .error k
          | .ok [] => .ok (locals, mem)
          | .ok (_ :: _) => .error .unsupported
      | some aid =>
        match findAllocation aid mem.allocations with
        | none => .error .undefined
        | some a =>
          if Nat.blt 0 lay.size &&
              (!a.live || !Mutability.beq a.mutability .mut) then
            .error .undefined
          else
            match storeIndirectV2 mem pt ⟨aid, pv.offsetBytes.toNat⟩ val with
            | .ok mem1 => .ok (locals, mem1)
            | .error k => .error k
    | .localProj localId baseTy projs =>
      match getElem? locals localId with
      | none => .error .unsupported
      | some .dead => .error .undefined
      | some (.immediate (some oldVal)) =>
        match updateValAtProjV2 baseTy oldVal projs val with
        | .error k => .error k
        | .ok updated =>
          match setElem? locals localId (.immediate (some updated)) with
          | some locals1 => .ok (locals1, mem)
          | none => .error .unsupported
      | some (.immediate none) | some (.partialTuple _) => .error .unsupported
      | some (.indirect mplace) =>
        match projectMemoryLayoutV2 baseTy projs with
        | .error k => .error k
        | .ok (leafTy, subOff) =>
          if !MirTy.beq leafTy dstTy then
            .error .unsupported
          else
            match storeIndirectV2 mem leafTy ⟨mplace.allocId, mplace.offset + subOff⟩ val with
            | .ok mem1 => .ok (locals, mem1)
            | .error k => .error k
    | .indirectProj leafTy mplace subOff =>
      match storeIndirectV2 mem leafTy ⟨mplace.allocId, mplace.offset + subOff⟩ val with
      | .ok mem1 => .ok (locals, mem1)
      | .error k => .error k
    | .derefProjected _pt ptLay leafTy subOff pv =>
      match pv.allocId with
      | none =>
        if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 ptLay.size ||
            !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 ptLay.alignLog2)) 0 then
          .error .undefined
        else
          match encodeValV2 profileV2TargetEndian leafTy val with
          | .error k => .error k
          | .ok [] => .ok (locals, mem)
          | .ok (_ :: _) => .error .unsupported
      | some aid =>
        match findAllocation aid mem.allocations with
        | none => .error .undefined
        | some a =>
          if !a.live || !Mutability.beq a.mutability .mut ||
              !isInBounds a pv.offsetBytes.toNat ptLay.size ||
              !isAligned a pv.offsetBytes.toNat ptLay.alignLog2 then
            .error .undefined
          else
            match storeIndirectV2 mem leafTy ⟨aid, pv.offsetBytes.toNat + subOff⟩ val with
            | .ok mem1 => .ok (locals, mem1)
            | .error k => .error k

/-- Write `val` into `dst : Place` in Profile v2, resolving `dst` and storing
to it against the same `locals` and `mem` (`resolvePlaceDestV2`, then
`writePlaceDestV2`). Assignments resolve their destination before evaluating
their rvalue instead (see `evalStatementV2`). -/
noncomputable def writePlaceV2 (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (dst : Place) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlot × MemoryState) :=
  match resolvePlaceDestV2 bodyLocals locals mem dst dstTy with
  | .error k => .error k
  | .ok dest => writePlaceDestV2 locals mem dest dstTy val

/-- Determine the static pointee/destination type of `dst : Place` in
Profile v2. Fast-paths `[]` and `[.deref]` inline so proofs unfolding only
`placeStaticTyV2` do not need to unfold `placeProjectedTyV2`. -/
noncomputable def placeStaticTyV2 (bodyLocals : List MirTy) (dst : Place) :
    Option MirTy :=
  match getElem? bodyLocals dst.localId, dst.projection with
  | some ty, [] => some ty
  | some (.ref _ pt), [.deref] | some (.rawPtr _ pt), [.deref] =>
    if isUnsizedTy pt then none else some pt
  | _, [] | _, [.deref] => none
  | _, _ => placeProjectedTyV2 bodyLocals dst

/-- Representation class governing whether `StatementKind.assign` copies a
sized Profile v2 value as zero bytes (`zst`), as a padding-free immediate
(`scalar` / `scalarPair`), or via `copy_nonoverlapping` memory copy
(`memoryCopy`).

In MIR (`compiler/rustc_middle/src/mir/syntax.rs:328-335`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "We currently require that the LHS place not overlap with any place read as
> part of computation of the RHS for some rvalues. This requirement is under
> discussion in [#68364]. Specifically, overlap is permitted only for
> assignments of a type with `BackendRepr::Scalar | BackendRepr::ScalarPair`
> where all the scalar fields are
> [`Scalar::Initialized`][rustc_abi::Scalar::Initialized]."

In `rustc_const_eval`'s `copy_op_no_validate`
(`compiler/rustc_const_eval/src/interpret/place.rs:901-922, 970-977`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "If the source has padding, we want to always do a mem-to-mem copy to ensure
> consistent padding in the target independent of layout choices."
> "left_size + right_size != src.layout().size"
> "BackendRepr::Memory { .. } => true,"
> "Setting `nonoverlapping` here only has an effect when we don't hit the
> fast-path above, but that should at least match what LLVM does where `memcpy`
> is also only used when the type does not have Scalar/ScalarPair layout."
> "self.mem_copy(src.ptr(), dest.ptr(), dest_size, /*nonoverlapping*/ true)?;"

Vendored `lean-miri` (`anneal/vendor/lean-miri/Miri/Interpreter/Place.lean`,
lines 339-381, commit `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`,
`copyRuntimePlaceNoValidate`) mirrors this directly:

> "`copy.memoryCopy` enforces `nonoverlapping = true` (per `PlaceCopyHooks` and
> `Allocation.copyRepeatedly`), so any overlapping copy with initialized bytes
> fails with `.copyRangesOverlap` UB before reaching deinitialization"

Thus `Rvalue::Use` and per-field `Aggregate` writes take the non-overlapping
memory-copy path whenever `size > 0` and either the type has
`BackendRepr::Memory` (arrays `[T; N]` with `N > 0` and non-ZST `T`, tuples
with `>= 3` scalars, or alignment-inflated tuples such as `([u64; 0], u32, u32)`
and `([u32; 0], u8)` where aggregate alignment exceeds scalar alignment per
`rustc_abi::LayoutCalculator::univariant`) or has padding bytes
(`src_has_padding = true`, e.g. `(u32, bool)` or `(u32, u8)`). -/
inductive CopyReprV2 where
  | zst (alignLog2 : Nat)
  | scalar (alignLog2 : Nat)
  | scalarPair (elemAlignLog2 : Nat)
  | memoryCopy

/-- Accumulator for flattening tuple fields when classifying `CopyReprV2`. -/
inductive TupleCopyPayloadV2 where
  | none
  | oneScalar (alignLog2 : Nat)
  | twoScalars (elemAlignLog2 : Nat)
  | memory

mutual
  /-- Classify `ty` into its `CopyReprV2` representation class. -/
  noncomputable def copyReprOfTyV2 : MirTy → CopyReprV2
    | .unit | .never => .zst 0
    | .bool | .ordering => .scalar 0
    | .int w _ => .scalar (intLayout w).alignLog2
    | .char => .scalar 2
    | .enum ety =>
      if !enumAdmitted ety then
        .memoryCopy
      else
        match ety.tagRepr with
        | .zeroSized => .zst 0
        | .scalar tagW _ => .scalar (intLayout tagW).alignLog2
    | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false) => .scalar 3
    | .ref _ pt | .rawPtr _ pt =>
      if isUnsizedTy pt then .scalarPair 3 else .scalar 3
    | .array elem len =>
      match copyReprOfTyV2 elem with
      | .zst a => .zst a
      | .scalar a | .scalarPair a =>
        if Nat.beq len 0 then .zst a else .memoryCopy
      | .memoryCopy =>
        if Nat.beq len 0 then
          match layoutOfArrayV2 elem with
          | some l => .zst l.alignLog2
          | none => .memoryCopy
        else
          .memoryCopy
    | .tuple fs =>
      let (maxA, payload) := copyReprOfTupleFieldsV2 fs
      match payload with
      | .none => .zst maxA
      | .oneScalar a => if Nat.ble maxA a then .scalar a else .memoryCopy
      | .twoScalars a => if Nat.ble maxA a then .scalarPair a else .memoryCopy
      | .memory => .memoryCopy
    | .slice _ | .rangeTo _ | .rangeFrom _ | .unsupported => .memoryCopy

  noncomputable def copyReprOfTupleFieldsV2 :
      List MirTy → Nat × TupleCopyPayloadV2
    | [] => (0, .none)
    | f :: fs =>
      let (restMaxA, restPayload) := copyReprOfTupleFieldsV2 fs
      match copyReprOfTyV2 f with
      | .zst fa => (Nat.max fa restMaxA, restPayload)
      | .scalar fa =>
        let nextPayload :=
          match restPayload with
          | .none => .oneScalar fa
          | .oneScalar a1 =>
            if Nat.beq fa a1 then .twoScalars fa else .memory
          | .twoScalars _ | .memory => .memory
        (Nat.max fa restMaxA, nextPayload)
      | .scalarPair fa =>
        let nextPayload :=
          match restPayload with
          | .none => .twoScalars fa
          | _ => .memory
        (Nat.max fa restMaxA, nextPayload)
      | .memoryCopy => (restMaxA, .memory)
end

/-- Return `true` iff `ty` copies through `copy_nonoverlapping` (`size > 0`
with `BackendRepr::Memory` or layout padding). -/
noncomputable def isMemoryCopyReprTyV2 (ty : MirTy) : Bool :=
  match copyReprOfTyV2 ty with
  | .memoryCopy => true
  | _ => false

/-- Normalized projection step inside an unpromoted immediate local slot. -/
inductive ImmProjStepV2 where
  | field (idx : Nat)
  | index (idx : Nat)

/-- Storage span of a place for `Assign` overlap / in-place aliasing checks. -/
inductive CopyPlaceSpanV2 where
  | memRange (allocId : AllocId) (offset size : Nat)
  | immPath (localId : LocalId) (steps : List ImmProjStepV2)

/-- Symmetric prefix relation on immediate-local projection paths: two paths in
the same immediate local overlap iff one is a prefix of the other. -/
noncomputable def immProjPrefixSymV2 :
    List ImmProjStepV2 → List ImmProjStepV2 → Bool
  | [], _ => true
  | _, [] => true
  | .field i :: r1, .field j :: r2 => Nat.beq i j && immProjPrefixSymV2 r1 r2
  | .index i :: r1, .index j :: r2 => Nat.beq i j && immProjPrefixSymV2 r1 r2
  | _, _ => false

/-- Return `true` when two `CopyPlaceSpanV2` storage spans overlap on `> 0`
bytes (or share an immediate-local sub-place prefix). -/
noncomputable def copySpansOverlapV2 : CopyPlaceSpanV2 → CopyPlaceSpanV2 → Bool
  | .memRange a1 off1 sz1, .memRange a2 off2 sz2 =>
    Nat.beq a1 a2 && Nat.blt 0 sz1 && Nat.blt 0 sz2 &&
      Nat.blt off1 (off2 + sz2) && Nat.blt off2 (off1 + sz1)
  | .immPath l1 p1, .immPath l2 p2 =>
    Nat.beq l1 l2 && immProjPrefixSymV2 p1 p2
  | _, _ => false

/-- Normalize a non-deref projection path on an immediate local of `baseTy`. -/
noncomputable def normalizeImmProjPathV2 :
    MirTy → List ProjectionElem → Option (List ImmProjStepV2)
  | _, [] => some []
  | .tuple fs, .field idx fTy :: rest =>
    match getElem? fs idx with
    | some elemTy =>
      if !MirTy.beq elemTy fTy then none
      else (normalizeImmProjPathV2 elemTy rest).map (.field idx :: ·)
    | none => none
  | .rangeTo (.int .isize false), .field 0 fTy :: rest
  | .rangeFrom (.int .isize false), .field 0 fTy :: rest =>
    if !MirTy.beq (.int .isize false) fTy then none
    else (normalizeImmProjPathV2 (.int .isize false) rest).map (.field 0 :: ·)
  | .array elem len, .constantIndex off minLen fromEnd :: rest =>
    match constantIndexOffset len off minLen fromEnd with
    | .ok idx => (normalizeImmProjPathV2 elem rest).map (.index idx :: ·)
    | .error _ => none
  | _, _ => none

/-- Compute the `CopyPlaceSpanV2` of a resolved assignment destination `dest`
of type `dstTy` against pre-rvalue `locals`. -/
noncomputable def destCopySpanV2 (locals : List LocalSlot) (dest : PlaceDestV2)
    (dstTy : MirTy) : Option CopyPlaceSpanV2 :=
  match dest with
  | .local lid =>
    match getElem? locals lid with
    | some (.indirect mplace) =>
      (layoutOfTyV2 dstTy).map (fun lay => .memRange mplace.allocId mplace.offset lay.size)
    | some (.immediate _) | some (.partialTuple _) => some (.immPath lid [])
    | _ => none
  | .localProj lid baseTy projs =>
    match getElem? locals lid with
    | some (.indirect mplace) =>
      match projectMemoryLayoutV2 baseTy projs, layoutOfTyV2 dstTy with
      | .ok (_, subOff), some lay =>
        some (.memRange mplace.allocId (mplace.offset + subOff) lay.size)
      | _, _ => none
    | some (.immediate _) | some (.partialTuple _) =>
      (normalizeImmProjPathV2 baseTy projs).map (.immPath lid ·)
    | _ => none
  | .indirectProj leafTy mplace subOff =>
    (layoutOfTyV2 leafTy).map (fun lay =>
      .memRange mplace.allocId (mplace.offset + subOff) lay.size)
  | .deref _ lay pv =>
    pv.allocId.map (fun aid => .memRange aid pv.offsetBytes.toNat lay.size)
  | .derefProjected _ _ leafTy subOff pv =>
    match pv.allocId, layoutOfTyV2 leafTy with
    | some aid, some lay =>
      some (.memRange aid (pv.offsetBytes.toNat + subOff) lay.size)
    | _, _ => none

/-- Sub-destination span for field/element `idx` of an `AggregateTuple`
(`isArray = false`) or `AggregateArray` (`isArray = true`) written into `base`
of aggregate type `aggTy`. -/
noncomputable def destAggregateSubSpanV2 (base : CopyPlaceSpanV2)
    (aggTy elemTy : MirTy) (isArray : Bool) (idx : Nat) :
    Option CopyPlaceSpanV2 :=
  match base with
  | .immPath lid steps =>
    let step := if isArray then ImmProjStepV2.index idx else .field idx
    some (.immPath lid (steps ++ [step]))
  | .memRange aid baseOff _ =>
    if isArray then
      (layoutOfTyV2 elemTy).map (fun lay =>
        .memRange aid (baseOff + idx * lay.size) lay.size)
    else
      match aggTy with
      | .tuple [.int w _, .bool] =>
        if Nat.beq idx 0 then
          some (.memRange aid baseOff (intLayout w).size)
        else if Nat.beq idx 1 then
          some (.memRange aid (baseOff + (intLayout w).size) 1)
        else
          none
      | _ => none

/-- Compute the `CopyPlaceSpanV2` of a source `Place` against pre-rvalue
`locals` and `mem`. -/
noncomputable def srcPlaceCopySpanV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (place : Place) :
    Option CopyPlaceSpanV2 :=
  match getElem? bodyLocals place.localId, getElem? locals place.localId with
  | some baseTy, some slot =>
    match place.projection with
    | [] =>
      match slot with
      | .indirect mplace =>
        (layoutOfTyV2 baseTy).map (fun lay =>
          .memRange mplace.allocId mplace.offset lay.size)
      | .immediate _ | .partialTuple _ => some (.immPath place.localId [])
      | .dead => none
    | .deref :: rest =>
      match baseTy with
      | .ref _ pt | .rawPtr _ pt =>
        let ptrOpt : Option Val :=
          match slot with
          | .immediate optVal => optVal
          | .indirect mplace =>
            match loadIndirectV2 mem baseTy mplace with
            | .ok optVal => optVal
            | .error _ => none
          | .dead | .partialTuple _ => none
        match ptrOpt with
        | some (.ptr pv) =>
          match pv.allocId with
          | none => none
          | some aid =>
            if rest.isEmpty then
              (layoutOfTyV2 pt).map (fun lay =>
                .memRange aid pv.offsetBytes.toNat lay.size)
            else
              match projectMemoryLayoutV2 pt rest with
              | .ok (leafTy, subOff) =>
                (layoutOfTyV2 leafTy).map (fun lay =>
                  .memRange aid (pv.offsetBytes.toNat + subOff) lay.size)
              | .error _ => none
        | _ => none
      | _ => none
    | projs =>
      match slot with
      | .indirect mplace =>
        match projectMemoryLayoutV2 baseTy projs with
        | .ok (leafTy, subOff) =>
          (layoutOfTyV2 leafTy).map (fun lay =>
            .memRange mplace.allocId (mplace.offset + subOff) lay.size)
        | .error _ => none
      | .immediate _ | .partialTuple _ =>
        (normalizeImmProjPathV2 baseTy projs).map (.immPath place.localId ·)
      | .dead => none
  | _, _ => none

/-- Compute the `CopyPlaceSpanV2` of an `Operand` (`none` for `.constant`). -/
noncomputable def operandCopySpanV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) :
    Operand → Option CopyPlaceSpanV2
  | .copy p | .move p => srcPlaceCopySpanV2 bodyLocals locals mem p
  | .constant _ => none

/-- Compute the storage span of the pointer local read when evaluating a
`.deref` projection in an `Aggregate` operand (`none` for `.constant` or
operands without `.deref`; `some none` when a `.deref` operand's base pointer
local has an unresolved storage span). -/
noncomputable def operandDerefBaseSpanV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) :
    Operand → Option (Option CopyPlaceSpanV2)
  | .copy p | .move p =>
    let hasDeref :=
      p.projection.any (fun e => match e with | .deref => true | _ => false)
    if hasDeref then
      some (srcPlaceCopySpanV2 bodyLocals locals mem
        { localId := p.localId, projection := [] })
    else
      none
  | .constant _ => none

/-- Walk aggregate operands left-to-right matching `rustc`'s `write_aggregate`
(`compiler/rustc_const_eval/src/interpret/step.rs:334-340`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "for (field_index, operand) in operands.iter_enumerated() {"
> "    let field_dest = self.project_field(&variant_dest, field_index)?;"
> "    let op = self.eval_operand(operand, Some(field_dest.layout))?;"
> "    self.copy_op_no_validate(&op, &field_dest, /*allow_transmute*/ false)?;"
> "}"

and vendored `lean-miri`'s `Miri.Interpreter.writeAggregate`
(`anneal/vendor/lean-miri/Miri/Interpreter/Aggregate.lean:42-74`, commit
`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), which loops over
`[:operands.size]` and executes `h.copyOpNoValidate choice operand field false`.
If an earlier field write `writtenSpans` overlaps either a later operand's
source span or the pointer local read by a later `.deref` operand, fail closed
with `.error .unsupported`; if operand `idx` overlaps its own destination field
span and `isMemoryCopyReprTyV2 fieldTy`, fault `.error .undefined`
(`copy_nonoverlapping` UB). -/
noncomputable def checkAggregateCopyHazardLoopV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (baseSpan : CopyPlaceSpanV2)
    (aggTy : MirTy) (isArray : Bool) (idx : Nat)
    (writtenSpans : List CopyPlaceSpanV2) :
    List MirTy → List Operand → Except FaultKind Unit
  | [], [] => .ok ()
  | fieldTy :: restTys, op :: restOps =>
    let opSpanOpt := operandCopySpanV2 bodyLocals locals mem op
    let clobberedByEarlier :=
      match opSpanOpt with
      | none => false
      | some opSpan => writtenSpans.any (fun w => copySpansOverlapV2 w opSpan)
    let ptrClobberedByEarlier :=
      match operandDerefBaseSpanV2 bodyLocals locals mem op with
      | none => false
      | some none => !writtenSpans.isEmpty
      | some (some ptrSpan) =>
        writtenSpans.any (fun w => copySpansOverlapV2 w ptrSpan)
    if clobberedByEarlier then
      .error .unsupported
    else if ptrClobberedByEarlier then
      .error .unsupported
    else
      match destAggregateSubSpanV2 baseSpan aggTy fieldTy isArray idx with
      | none =>
        let wholeOverlap :=
          match opSpanOpt with
          | none => false
          | some opSpan => copySpansOverlapV2 baseSpan opSpan
        if wholeOverlap then
          .error .unsupported
        else
          checkAggregateCopyHazardLoopV2 bodyLocals locals mem baseSpan aggTy
            isArray (idx + 1) (baseSpan :: writtenSpans) restTys restOps
      | some subSpan =>
        let selfOverlap :=
          match opSpanOpt with
          | none => false
          | some opSpan => copySpansOverlapV2 subSpan opSpan
        if selfOverlap && isMemoryCopyReprTyV2 fieldTy then
          .error .undefined
        else
          checkAggregateCopyHazardLoopV2 bodyLocals locals mem baseSpan aggTy
            isArray (idx + 1) (subSpan :: writtenSpans) restTys restOps
  | _, _ => .error .unsupported

/-- Post-store non-overlap and in-place aggregate hazard check for Profile v2
`StatementKind.assign`. Fast-paths non-copy rvalues and immediate/ZST `.use`
assignments definitionally so proof obligations on scalar, pointer, slice, and
zero-sized copies reduce by `rfl`.

For `Rvalue.repeat_`, this matches `rustc`'s `write_repeat`
(`compiler/rustc_const_eval/src/interpret/step.rs:366-388`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "let first = self.project_index(&dest, 0)?;"
> "self.copy_op(&src, &first)?;"
> "self.mem_copy_repeatedly("
> "    first_ptr,"
> "    rest_ptr,"
> "    elem_size,"
> "    length - 1,"
> "    /*nonoverlapping:*/ true,"
> ")?;"

and vendored `lean-miri`'s `Miri.Interpreter.writeRepeat`
(`anneal/vendor/lean-miri/Miri/Interpreter/Aggregate.lean:76-95`, commit
`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):

> "Positive lengths copy once and replicate the resulting bytes; the source can
> alias the destination, so evaluating/copying every element would be
> incorrect."

Accordingly, when `count > 0` and `isMemoryCopyReprTyV2 elemTy`, only overlap
between `op` and element `0` (`first`) faults `.undefined`; overlap with
elements `1..count` is well-defined because `copy_op` copies `src` into element
`0` once before `mem_copy_repeatedly` replicates element `0` into the remaining
elements. -/
noncomputable def checkAssignCopyHazardV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (dest : PlaceDestV2)
    (dstTy : MirTy) : Rvalue → Except FaultKind Unit
  | .use (.copy src) | .use (.move src)
  | .useRetag (.copy src) | .useRetag (.move src) =>
    if !isMemoryCopyReprTyV2 dstTy then
      .ok ()
    else
      match destCopySpanV2 locals dest dstTy,
          srcPlaceCopySpanV2 bodyLocals locals mem src with
      | some dSpan, some sSpan =>
        if copySpansOverlapV2 dSpan sSpan then
          .error .undefined
        else
          .ok ()
      | _, _ => .error .unsupported
  | .aggregateTuple fields =>
    match copyReprOfTyV2 dstTy with
    | .zst _ => .ok ()
    | _ =>
      match dstTy, destCopySpanV2 locals dest dstTy with
      | .tuple fieldTys, some baseSpan =>
        checkAggregateCopyHazardLoopV2 bodyLocals locals mem baseSpan dstTy false
          0 [] fieldTys fields
      | _, _ => .error .unsupported
  | .aggregateArray elemTy elems =>
    match copyReprOfTyV2 dstTy with
    | .zst _ => .ok ()
    | _ =>
      match destCopySpanV2 locals dest dstTy with
      | some baseSpan =>
        checkAggregateCopyHazardLoopV2 bodyLocals locals mem baseSpan dstTy true
          0 [] (List.replicate elems.length elemTy) elems
      | none => .error .unsupported
  | .repeat_ op elemTy count =>
    if Nat.beq count 0 || !isMemoryCopyReprTyV2 elemTy then
      .ok ()
    else
      match op with
      | .constant _ => .ok ()
      | .copy src | .move src =>
        match destCopySpanV2 locals dest dstTy,
            srcPlaceCopySpanV2 bodyLocals locals mem src with
        | some baseSpan, some opSpan =>
          match destAggregateSubSpanV2 baseSpan dstTy elemTy true 0 with
          | some firstSpan =>
            if copySpansOverlapV2 firstSpan opSpan then
              .error .undefined
            else
              .ok ()
          | none =>
            if copySpansOverlapV2 baseSpan opSpan then
              .error .unsupported
            else
              .ok ()
        | _, _ => .error .unsupported
  | .use (.constant _) | .useRetag (.constant _)
  | .binaryOp _ _ _ | .unaryOp _ _ | .cast _ _ _ | .discriminant _
  | .ref _ _ | .addressOf _ _ | .aggregateRangeTo _ _
  | .aggregateRangeFrom _ _ | .unsupported => .ok ()

/-- Evaluate one `StatementKind` in Profile v2.

`.assign dst rvalue` resolves `dst` against the state before the rvalue runs
(`resolvePlaceDestV2`, following `eval_rvalue_into_place`), then evaluates
`rvalue`, then stores into the resolved destination against the state the
rvalue left (`writePlaceDestV2`). So `*_1 = PtrMetadata(move _1)` reads the
pointer in `_1` before the rvalue moves out of `_1`. -/
noncomputable def evalStatementV2 (body : Body) (frame : FrameState)
    (mem : MemoryState) (callerMem : CallerMemory) (stmt : StatementKind) :
    StepResult State TerminalOut :=
  match stmt with
  | .nop =>
    .step {
      frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }]
      callerMem
      mem
    }
  | .storageLive localId =>
    match getElem? body.locals localId, getElem? frame.locals localId with
    | some localTy, some old =>
      match setElem? frame.locals localId (liveUninitSlot localTy) with
      | none => .fault .unsupported
      | some locals1 =>
        match deallocateLocal mem old with
        | .error k => .fault k
        | .ok mem1 =>
          .step {
            frames := [{
              frame with
              stmtIdx := frame.stmtIdx + 1
              locals := locals1
            }]
            callerMem
            mem := mem1
          }
    | _, _ => .fault .unsupported
  | .storageDead localId =>
    if Nat.beq localId 0 then
      .fault .unsupported
    else
      match getElem? frame.locals localId with
      | none => .fault .unsupported
      | some old =>
        match setElem? frame.locals localId .dead with
        | none => .fault .unsupported
        | some locals1 =>
          match deallocateLocal mem old with
          | .error k => .fault k
          | .ok mem1 =>
            .step {
              frames := [{
                frame with
                stmtIdx := frame.stmtIdx + 1
                locals := locals1
              }]
              callerMem
              mem := mem1
            }
  | .assign dst rvalue =>
    match placeStaticTyV2 body.locals dst with
    | none => .fault .unsupported
    | some dstTy =>
      match resolvePlaceDestV2 body.locals frame.locals mem dst dstTy with
      | .error k => .fault k
      | .ok dest =>
        match evalRvalueV2 body.locals frame.locals mem dstTy rvalue with
        | .error k => .fault k
        | .ok (val, locals1, mem1) =>
          match writePlaceDestV2 locals1 mem1 dest dstTy val with
          | .error k => .fault k
          | .ok (locals2, mem2) =>
            match checkAssignCopyHazardV2 body.locals frame.locals mem dest
                dstTy rvalue with
            | .error k => .fault k
            | .ok () =>
              .step {
                frames := [{
                  frame with
                  stmtIdx := frame.stmtIdx + 1
                  locals := locals2
                }]
                callerMem
                mem := mem2
              }
  | .unsupported => .fault .unsupported

/-- Element-wise equality helper over two value lists using a fixed element
comparator (factored out for structural recursion in `arrayValEqV2`). -/
noncomputable def valEqListWith
    (f : Val → Val → Except FaultKind Bool) :
    List Val → List Val → Except FaultKind Bool
  | [], [] => .ok true
  | x :: xs, y :: ys =>
    match f x y with
    | .ok true => valEqListWith f xs ys
    | .ok false => .ok false
    | .error k => .error k
  | _, _ => .error .unsupported

/-- Structural value equality for `CoreCallOp.arrayEq` on Profile v2 scalar,
unit, ordering, and nested fixed-size array elements. -/
noncomputable def arrayValEqV2 : MirTy → Val → Val → Except FaultKind Bool
  | .int _ _, x, y
  | .bool, x, y
  | .char, x, y =>
    match evalBinOp .eq x y with
    | .ok (.bool b) => .ok b
    | .ok _ => .error .unsupported
    | .error k => .error k
  | .unit, .unit, .unit => .ok true
  | .ordering, .ordering .less, .ordering .less
  | .ordering, .ordering .equal, .ordering .equal
  | .ordering, .ordering .greater, .ordering .greater => .ok true
  | .ordering, .ordering _, .ordering _ => .ok false
  | .array elem _, .array xs, .array ys =>
    valEqListWith (arrayValEqV2 elem) xs ys
  | _, _, _ => .error .unsupported

/-- Execute a closed-world `CoreCallOp` primitive in Profile v2 against memory
`m`. Every argument and result is checked against the callee's `core`
signature, and any mismatch is `.unsupported`.

- `.sliceLen`: `<[T]>::len(&self)` is `ptr::metadata(self)`
  (`library/core/src/slice/mod.rs:116-118`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). Lean also re-validates the
  `&[uN]` argument, which is conservative: a reference passed to a function
  is considered live.
- `.sliceGetUncheckedRangeTo`/`RangeFrom`: see `sliceGetUncheckedCheck`.
  The input slice reference is validated at its own mutability `inMut`.
  Capture produces these only for `get_unchecked(&self)` on `[u8]`, as
  `&[u8] -> &[u8]`, so the `&[u8] -> &mut [u8]` arm (`.undefined`) is
  unreachable.
- `.ptrAdd`: see `ptrAddInMem`.
- `.usizeUncheckedSub`: UB exactly when `rhs > lhs`, which is the
  precondition of `usize::unchecked_sub`
  (`library/core/src/num/uint_macros.rs:1139-1146`, same pin):

  > "assert_unsafe_precondition!(
  >     check_language_ub,
  >     concat!(stringify!($SelfT), "::unchecked_sub cannot overflow"),
  >     (
  >         lhs: $SelfT = self,
  >         rhs: $SelfT = rhs,
  >     ) => !lhs.overflowing_sub(rhs).1,
  > );"

A failed `core` precondition faults with `.undefined` instead of panicking,
so no call unwinds (see `UnwindAction`). -/
noncomputable def execCoreCallOp (m : MemoryState) (op : CoreCallOp)
    (args : List (MirTy × Val)) (dstTy : MirTy) : Except FaultKind Val :=
  match op, args with
  | .sliceLen, [(.ref reqMut (.slice (.int w s)), .slicePtr p len)] =>
    if !MirTy.beq dstTy (.int .isize false) then
      .error .unsupported
    else
      match refValidInMem m reqMut (.slice (.int w s)) (.slicePtr p len) with
      | .error k => .error k
      | .ok () =>
        .ok (.scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 len.toNat)⟩)
  | .sliceGetUncheckedRangeTo,
      [(.ref inMut (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeTo (.int .isize false), .rangeTo endOff)] =>
    match dstTy with
    | .ref outMut (.slice (.int .i8 false)) =>
      if Mutability.beq inMut .shared && Mutability.beq outMut .mut then
        .error .undefined
      else
        match refValidInMem m inMut (.slice (.int .i8 false)) (.slicePtr p len) with
        | .error k => .error k
        | .ok () => sliceGetUncheckedCheck m p len.toNat 0 endOff.toNat
    | _ => .error .unsupported
  | .sliceGetUncheckedRangeFrom,
      [(.ref inMut (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeFrom (.int .isize false), .rangeFrom startOff)] =>
    match dstTy with
    | .ref outMut (.slice (.int .i8 false)) =>
      if Mutability.beq inMut .shared && Mutability.beq outMut .mut then
        .error .undefined
      else
        match refValidInMem m inMut (.slice (.int .i8 false)) (.slicePtr p len) with
        | .error k => .error k
        | .ok () => sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat
    | _ => .error .unsupported
  | .ptrAdd reqMut pointee,
      [(.rawPtr argMut argPt, .ptr p), (.int .isize false, .scalar countSv)] =>
    if !Mutability.beq reqMut argMut || !MirTy.beq pointee argPt ||
        !MirTy.beq dstTy (.rawPtr reqMut pointee) || isUnsizedTy pointee then
      .error .unsupported
    else
      match layoutOfTyV2 pointee with
      | none => .error .unsupported
      | some lay =>
        match ptrAddInMem m lay.size p countSv.bits.toNat with
        | .error k => .error k
        | .ok p' => .ok (.ptr p')
  | .usizeUncheckedSub,
      [(.int .isize false, .scalar lSv), (.int .isize false, .scalar rSv)] =>
    if !MirTy.beq dstTy (.int .isize false) then
      .error .unsupported
    else if !Nat.ble rSv.bits.toNat lSv.bits.toNat then
      .error .undefined
    else
      let diff := lSv.bits.toNat - rSv.bits.toNat
      .ok (.scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 diff)⟩)
  | .intToLeBytes w s, [(.int argW argS, .scalar sv)] =>
    if !IntWidth.beq w argW || !IntWidth.beq sv.width w ||
        s != argS || sv.signed != s ||
        !MirTy.beq dstTy (.array (.int .i8 false) w.byteSize) || !sv.wf then
      .error .unsupported
    else
      let bytes := leBytesOfNat w.byteSize sv.bits.toNat
      .ok (.array (bytes.map (fun b => .scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)))
  | .arrayEq elem len,
      [(.ref m1 (.array e1 n1), .ptr p1), (.ref m2 (.array e2 n2), .ptr p2)] =>
    if !MirTy.beq dstTy .bool || !MirTy.beq elem e1 || !MirTy.beq elem e2 ||
        !Nat.beq len n1 || !Nat.beq len n2 || !isArrayEqElemSupported elem then
      .error .unsupported
    else
      match refValidInMem m m1 (.array elem len) (.ptr p1),
          refValidInMem m m2 (.array elem len) (.ptr p2) with
      | .error k, _ => .error k
      | _, .error k => .error k
      | .ok (), .ok () =>
        let loadArr (p : PtrVal) : Except FaultKind (List Val) :=
          match p.allocId with
          | none =>
            match decodeValV2 profileV2TargetEndian (.array elem len) [] with
            | .ok (some (.array vs)) => .ok vs
            | .ok _ => .error .unsupported
            | .error k => .error k
          | some aid =>
            match loadIndirectV2 m (.array elem len) ⟨aid, p.offsetBytes.toNat⟩ with
            | .ok (some (.array vs)) => .ok vs
            | .ok none => .error .undefined
            | .ok (some _) => .error .unsupported
            | .error k => .error k
        match loadArr p1, loadArr p2 with
        | .error k, _ => .error k
        | _, .error k => .error k
        | .ok vs1, .ok vs2 =>
          match valEqListWith (arrayValEqV2 elem) vs1 vs2 with
          | .ok b => .ok (.bool b)
          | .error k => .error k
  | _, _ => .error .unsupported

/-- Evaluate a basic block's `TerminatorKind` in Profile v2.

`.return_` faults with `.undefined` unless every returned reference is
valid, belongs to caller memory, and has `&mut` spans disjoint from the other
returned spans. A returned value is "produced", so it must be valid
(`src/behavior-considered-undefined.md:69-73`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`):

> "* Producing an [invalid value][invalid-values]. "Producing" a value happens
>   any time a value is assigned to or read from a place, passed to a
>   function/primitive operation or returned from a function/primitive
>   operation."

Returned references are also considered live for the aliasing rules (lines
44-45 there). Popping the frame deallocates the callee's locals
(`compiler/rustc_const_eval/src/interpret/stack.rs:442-453`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), so a reference into callee stack
memory would dangle (`refsStayInCallerMem`). Conservative divergence: a
reference to a zero-sized callee local never dangles in Rust, but Lean rejects
it.

`.assert` continues when the condition matches `expected`. Otherwise the
terminator "initiates a panic"
(`compiler/rustc_middle/src/mir/syntax.rs:853-854`). The
`MisalignedPointerDereference` and `NullPointerDereference` asserts are
inserted only by the `-Zub-checks` passes
(`compiler/rustc_mir_transform/src/check_pointers.rs:24-42`) in front of
raw-pointer accesses that would otherwise be UB under
`src/behavior-considered-undefined.md:26-28`. A failure of either assert
therefore faults with `.undefined`, which is conservative: with checks enabled,
rustc's behavior is a defined, non-unwinding panic. Every other failed assert
delegates to `evalAssertFailure`: under `--panic abort` without a crate-local
`#[panic_handler]` and with a non-cleanup unwind action, non-optional safe
panics return `.done (.aborted (extractCallerMemory callerMem mem1))`, and so
do optional overflow checks when `overflowChecks = true`; optional overflow
checks without `overflowChecks`, crates with a crate-local `#[panic_handler]`,
cleanup unwinds, and `--panic unwind` stay `.fault .unsupported`. -/
noncomputable def evalTerminatorV2 (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory)
    (panicStrategy : PanicStrategy := .unwind)
    (hasLocalPanicHandler : Bool := true)
    (overflowChecks : Bool := false) :
    StepResult State TerminalOut :=
  match bb.terminator with
  | .goto target => jumpToBlock frame mem callerMem target
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match getElem? body.locals 0 with
      | none => .fault .unsupported
      | some retTy =>
        let retRes : Except FaultKind Val :=
          match getElem? frame.locals 0 with
          | some (.immediate (some v)) => .ok v
          | some (.immediate none) | some .dead | some (.partialTuple _) => .error .undefined
          | some (.indirect mplace) =>
            match loadIndirectV2 mem retTy mplace with
            | .ok (some v) => .ok v
            | .ok none => .error .undefined
            | .error k => .error k
          | none => .error .unsupported
        match retRes with
        | .error k => .fault k
        | .ok retVal =>
          if hasEscapingRodataPtr callerMem mem retTy retVal then
            .fault .unsupported
          else if !refsStayInCallerMem callerMem retTy retVal ||
              !refsValidInMem mem retTy retVal ||
              !spansPairwiseDisjoint (refAccessSpans retTy retVal) then
            .fault .undefined
          else
            .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩)
  | .unreachable => .fault .undefined
  | .switchInt discr targets =>
    match evalPrimitiveOperandV2 body.locals frame.locals mem discr with
    | .error k => .fault k
    | .ok (discrVal, localsAfterDiscr, memAfterDiscr) =>
      let targetRes : Except FaultKind BasicBlockId :=
        match discrVal with
        | .scalar sv =>
          evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches
        | .bool b =>
          evalBoolSwitchBranches b targets.otherwise targets.branches
        | .char c =>
          evalCharSwitchBranches c targets.otherwise targets.branches
        | _ =>
          match targets.branches with
          | [] => .ok targets.otherwise
          | _ :: _ => .error .unsupported
      match targetRes with
      | .error k => .fault k
      | .ok target =>
        jumpToBlock { frame with locals := localsAfterDiscr } memAfterDiscr
          callerMem target
  | .assert cond expected msg target unwind =>
    match evalPrimitiveOperandV2 body.locals frame.locals mem cond with
    | .error k => .fault k
    | .ok (condVal, locals1, mem1) =>
      match condVal with
      | .bool b =>
        if b == expected then
          jumpToBlock { frame with locals := locals1 } mem1 callerMem target
        else
          evalAssertFailure msg panicStrategy unwind
            (extractCallerMemory callerMem mem1) hasLocalPanicHandler
            overflowChecks
      | _ => .fault .unsupported
  | .coreCall op args dst (some target) _ =>
    if !dst.projection.isEmpty then
      .fault .unsupported
    else
      match getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match evalArgOperandsV2 body.locals frame.locals mem args with
        | .error k => .fault k
        | .ok (typedArgs, locals1, mem1) =>
          match execCoreCallOp mem1 op typedArgs dstTy with
          | .error k => .fault k
          | .ok resVal =>
            match writePlaceV2 body.locals locals1 mem1 dst dstTy resVal with
            | .error k => .fault k
            | .ok (locals2, mem2) =>
              jumpToBlock { frame with locals := locals2 } mem2 callerMem target
  | .coreCall _ _ _ none _ | .unwindResume | .call _ _ _ _ _
  | .sysrootCall _ _ _ _ _ | .unsupported =>
    .fault .unsupported

/-- Single small-step transition in Profile v2. -/
noncomputable def evalStepV2 (p : Program) (s : State) :
    StepResult State TerminalOut :=
  match s.frames with
  | [frame] =>
    match getElem? p.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match getElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatementV2 body frame s.mem s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminatorV2 body bb frame s.mem s.callerMem p.panicStrategy
              p.hasLocalPanicHandler p.overflowChecks
          else
            .fault .unsupported
  | _ => .fault .unsupported

/-- Choice-indexed wrapper for Profile v2 deterministic small-step
evaluation. -/
noncomputable def evalStepV2Choice (p : Program) (_c : Choice) (s : State) :
    StepResult State TerminalOut :=
  evalStepV2 p s
/-- Lift a single-frame `StepResult` onto an ambient `callers` tail stack.
When `callers = []`, return `res` directly so single-frame steps reduce
definitionally to the underlying statement or terminator transition. -/
noncomputable def attachCallers (callers : List FrameState)
    (res : StepResult State TerminalOut) : StepResult State TerminalOut :=
  match callers with
  | [] => res
  | _ :: _ =>
    match res with
    | .step s' => .step { s' with frames := s'.frames ++ callers }
    | .done out => .done out
    | .fault k => .fault k

/-- Evaluate a single call argument against its declared callee parameter type
`paramTy`, returning the passed value and updated `(locals, mem)`. Matches
`evalFnCallArgumentAt` (`deinitMovedPlace = true`) and `passArgument`
(`copyRuntimePlace`'s validity check) in `Miri.Interpreter.Call`, which model
`eval_fn_call_argument` in `compiler/rustc_const_eval/src/interpret/step.rs`
and `pass_argument` in `compiler/rustc_const_eval/src/interpret/call.rs`
(`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> /// Evaluate the arguments of a function call
> ...
> mir::Operand::Move(place) => {
>     let place = self.eval_place(*place)?;
>     if move_definitely_disjoint {

> /// Initialize a single callee argument, checking the types for compatibility.

`rustc` passes a moved argument in place (`FnArg::InPlace`) when it already
lives in memory. Profile version 1 has no in-memory argument passing, so an
`.indirect` moved slot (or an `.indirect` copied slot when the call also moves
an argument) fails closed with `.unsupported`. -/
noncomputable def evalCallArg (callerLocalsTys : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (hasMove : Bool)
    (opnd : Operand) (paramTy : MirTy) :
    Except FaultKind (Val × List LocalSlot × MemoryState) :=
  let indirectBlocked : Bool :=
    match opnd with
    | .copy place =>
      hasMove &&
        match getElem? locals place.localId with
        | some (.indirect _) => true
        | _ => false
    | .move place =>
      match getElem? locals place.localId with
      | some (.indirect _) => true
      | _ => false
    | _ => false
  if indirectBlocked then
    .error .unsupported
  else
    match evalOperandToSlot callerLocalsTys locals mem
        (fun srcTy => MirTy.beq srcTy paramTy) opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals', mem') =>
      if !MirTy.beq srcTy paramTy then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals', mem')
        | none => .error .undefined

/-- Evaluate a call's argument operands left-to-right against `paramTys`,
accumulating argument values and threading moved-place deinitialization through
the caller's `locals` and `mem`. -/
noncomputable def evalCallArgs (callerLocalsTys : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) (hasMove : Bool) :
    List Operand → List MirTy →
      Except FaultKind (List Val × List LocalSlot × MemoryState)
  | [], [] => .ok ([], locals, mem)
  | opnd :: restArgs, paramTy :: restParams =>
    match evalCallArg callerLocalsTys locals mem hasMove opnd paramTy with
    | .error k => .error k
    | .ok (v, locals₁, mem₁) =>
      match evalCallArgs callerLocalsTys locals₁ mem₁ hasMove restArgs
          restParams with
      | .error k => .error k
      | .ok (vs, locals₂, mem₂) => .ok (v :: vs, locals₂, mem₂)
  | _, _ => .error .unsupported

/-- Execute a direct `.call` or `.sysrootCall` terminator: validate call-site
preconditions (`callTargetAdmitted` and static callee validity), evaluate
arguments left-to-right (deinitializing moved non-ZST caller slots), check that
the caller's destination slot is live (`.dead` -> `.undefined`), initialize the
callee's frame (`initLocalsLoop`), and push it onto `callers`. This follows
`eval_callee_and_args` (`compiler/rustc_const_eval/src/interpret/step.rs`)
and `init_stack_frame` (`compiler/rustc_const_eval/src/interpret/call.rs`) in
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`:

> // The first order of business is to figure out the callee signature.

The callee frame records the return place `dst` and continuation `target`
(`retDst?`/`retTarget?`), which `evalNonRootReturn` consumes. -/
noncomputable def evalCallTerminator (callerBody : Body) (bb : BasicBlock)
    (caller : FrameState) (callers : List FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) (calleeDefId : DefId)
    (sysrootOp? : Option SysrootNumOp) (calleeBody : Body)
    (args : List Operand) (dst : Place) (target : Option BasicBlockId)
    (unwind : UnwindAction) : StepResult State TerminalOut :=
  if !callTargetAdmitted callerBody bb calleeBody args dst target unwind ||
      calleeBody.basicBlocks.isEmpty ||
      !storageAnnotationsInBounds calleeBody ||
      !discriminantTypesValid calleeBody ||
      !castTypesValid calleeBody ||
      !assignTypesValid calleeBody ||
      !calleeBody.locals.all isSupportedScalarOrUnitTy then
    .fault .unsupported
  else
    let hasMove : Bool :=
      args.any (fun a => match a with | .move _ => true | _ => false)
    let paramTys := (calleeBody.locals.drop 1).take calleeBody.argumentCount
    match evalCallArgs callerBody.locals caller.locals mem hasMove args
        paramTys with
    | .error k => .fault k
    | .ok (argVals, callerLocals', mem') =>
      match getElem? callerLocals' dst.localId with
      | none => .fault .unsupported
      | some .dead => .fault .undefined
      | some (.indirect _) => .fault .unsupported
      -- Profile v1 never creates partially moved tuples.
      | some (.partialTuple _) => .fault .unsupported
      | some (.immediate _) =>
        let calleeLocals :=
          initLocalsLoop calleeBody argVals 0 calleeBody.locals
        let calleeFrame : FrameState := {
          defId := calleeDefId
          blockIdx := 0
          stmtIdx := 0
          locals := calleeLocals
          sysrootOp? := sysrootOp?
          retDst? := some dst
          retTarget? := target
        }
        let caller' : FrameState := { caller with locals := callerLocals' }
        .step {
          frames := calleeFrame :: caller' :: callers
          callerMem := callerMem
          mem := mem'
        }

/-- Whether any slot in `locals` is an `.indirect` stack allocation. -/
noncomputable def localsHaveIndirect (locals : List LocalSlot) : Bool :=
  locals.any (fun slot => match slot with | .indirect _ => true | _ => false)

/-- Execute a non-root `TerminatorKind.return_`: read callee `_0` (`.dead` or
uninitialized -> `.undefined`), write it into `caller`'s return destination
`dst`, pop the callee frame, and transfer control in `caller` to
`blockIdx := tgt, stmtIdx := 0` (or fault with `.undefined` when
`retTarget? = none`, matching
`Miri.Interpreter.ControlFlow.returnToBlock none`). This follows
`return_from_current_stack_frame` and `return_to_block` in
`compiler/rustc_const_eval/src/interpret/{call,eval_context}.rs`
(`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> // Remove the frame from the stack.
> let frame = self.pop_stack_frame_raw()?;
> // Copy the return value and remember the return continuation.
> if !unwinding {
>     self.copy_op_allow_transmute(&return_op, frame.return_place())?;

> if let Some(target) = target {
>     self.go_to_block(target);
>     interp_ok(())
> } else {
>     throw_ub!(Unreachable)
> }

Popping a frame also deallocates its in-memory locals (`cleanup_stack_frame`
in `compiler/rustc_const_eval/src/interpret/stack.rs`):

> // Cleanup: deallocate locals.
> ...
> if cleanup {
>     for local in &frame.locals {
>         self.deallocate_local(local.value)?;
>     }

$M_{\text{anneal}}$ does not model that deallocation, so a callee frame with
any `.indirect` local (`localsHaveIndirect`) fails closed with `.unsupported`
instead of leaking a live stack allocation. Profile version 1 never creates
such a callee local. -/
noncomputable def evalNonRootReturn (p : Program) (calleeBody : Body)
    (bb : BasicBlock) (callee : FrameState) (caller : FrameState)
    (restCallers : List FrameState) (mem : MemoryState)
    (callerMem : CallerMemory) : StepResult State TerminalOut :=
  if bb.cleanup || localsHaveIndirect callee.locals then
    .fault .unsupported
  else
    let retRead : Except FaultKind Val :=
      match getElem? callee.locals 0 with
      | some (.immediate (some retVal)) => .ok retVal
      | some (.immediate none) | some .dead => .error .undefined
      -- Profile v1 never creates partially moved tuples.
      | some (.partialTuple _) => .error .unsupported
      | some (.indirect mplace) =>
        match getElem? calleeBody.locals 0 with
        | none => .error .unsupported
        | some retTy =>
          match loadIndirect mem retTy mplace with
          | .ok (some retVal) => .ok retVal
          | .ok none => .error .undefined
          | .error k => .error k
      | none => .error .unsupported
    match retRead with
    | .error k => .fault k
    | .ok retVal =>
      match callee.retDst? with
      | none => .fault .unsupported
      | some dst =>
        if !dst.projection.isEmpty then
          .fault .unsupported
        else
          match activeFrameBody p caller with
          | none => .fault .unsupported
          | some callerBody =>
            match getElem? callerBody.locals dst.localId with
            | none => .fault .unsupported
            | some dstTy =>
              match writePlace caller.locals mem dst.localId dstTy retVal with
              | .error k => .fault k
              | .ok (callerLocals', mem') =>
                match callee.retTarget? with
                | none => .fault .undefined
                | some tgt =>
                  .step {
                    frames := {
                      caller with
                      blockIdx := tgt
                      stmtIdx := 0
                      locals := callerLocals'
                    } :: restCallers
                    callerMem := callerMem
                    mem := mem'
                  }

/-- Total single-step evaluator of $M_{\text{anneal}}$ over running `State`s,
matching `InterpCx::step` in `compiler/rustc_const_eval/src/interpret/step.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub fn step(&mut self) -> InterpResult<'tcx, bool> {
>     if self.stack().is_empty() {
>         return interp_ok(false);
>     }
>     ...
>     let basic_block = &self.body().basic_blocks[loc.block];
>     if let Some(stmt) = basic_block.statements.get(loc.statement_index) {
>         ...
>         self.eval_statement(stmt)?;
>         ...
>         self.frame_mut().loc.as_mut().left().unwrap().statement_index += 1;
>         return interp_ok(true);
>     }
>     ...
>     let terminator = basic_block.terminator();
>     self.eval_terminator(terminator)?;
>     ...
>     interp_ok(true)
> }"

Out-of-bounds `frame.blockIdx` faults with `.fault .unsupported` (matching
`Miri.Interpreter.Step.step` `StepError.invalidBlock`). -/
noncomputable def evalStep (p : Program) (_c : Choice) (s : State) :
    StepResult State TerminalOut :=
  match s.frames with
  | frame :: callers =>
    match activeFrameBody p frame with
    | none => .fault .unsupported
    | some body =>
      match getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match getElem? bb.statements frame.stmtIdx with
        | some stmt =>
          attachCallers callers
            (evalStatement body frame s.mem s.callerMem stmt)
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            match bb.terminator with
            | .call callee args dst target unwind =>
              match getElem? p.bodies callee with
              | none => .fault .unsupported
              | some calleeBody =>
                evalCallTerminator body bb frame callers s.mem s.callerMem
                  callee none calleeBody args dst target unwind
            | .sysrootCall op args dst target unwind =>
              evalCallTerminator body bb frame callers s.mem s.callerMem
                0 (some op) (sysrootNumBody op) args dst target unwind
            | .return_ =>
              match callers with
              | [] =>
                evalTerminator body bb frame s.mem s.callerMem p.panicStrategy
                  p.hasLocalPanicHandler
              | caller :: rest =>
                evalNonRootReturn p body bb frame caller rest s.mem s.callerMem
            | _ =>
              attachCallers callers
                (evalTerminator body bb frame s.mem s.callerMem p.panicStrategy
                  p.hasLocalPanicHandler)
          else
            .fault .unsupported
  | [] => .fault .unsupported

/-- Move the immediate local `localId` of the single active frame into a fresh
stack allocation, returning the new state and the local's memory place.
Matches `force_allocation` in
`compiler/rustc_const_eval/src/interpret/place.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`Miri.Interpreter.forceAllocation`
(`vendor/lean-miri/Miri/Interpreter/Place.lean`):

> "let whole_local = match self.frame_mut().locals[local].access_mut()? {
>     &mut Operand::Immediate(local_val) => {
>         // We need to make an allocation.
>         ...
>         let local_layout = self.layout_of_local(&self.frame(), local, None)?;
>         assert!(local_layout.is_sized(), \"unsized locals cannot be
>             immediate\");
>         let mplace = self.allocate(local_layout, MemoryKind::Stack)?;
>         // Preserve old value. (As an optimization, we can skip this if it
>         // was uninit.)
>         if !matches!(local_val, Immediate::Uninit) {
>             // We don't have to validate as we can assume the local was
>             // already valid for its type. ...
>             self.write_immediate_to_mplace_no_validate(
>                 local_val,
>                 local_layout,
>                 mplace.mplace,
>             )?;
>         }
>         M::after_local_moved_to_memory(self, local, &mplace)?;
>         ...
>         *self.frame_mut().locals[local].access_mut().unwrap() =
>             Operand::Indirect(mplace.mplace);
>         mplace.mplace
>     }
>     &mut Operand::Indirect(mplace) => mplace, // this already was an indirect
>                                                // local
> };"

- A `.dead` local faults with `.undefined` (`access_mut` raises `DeadLocal`).
- An `.indirect place` local is already in memory and is returned unchanged.
- An `.immediate optVal` local of type `ty` gets a fresh stack allocation of
  layout `layoutOfTy ty` (`allocateStack`). An initialized value is stored
  without validation (`storeIndirect`); an uninitialized value leaves the
  allocation's bytes uninitialized. The slot becomes `.indirect place`.

`rustc` forces an allocation when a place expression needs the local's
address: a projection, a reference or raw pointer to the local, or an argument
or return place passed in memory. Profile version 1 rejects all of these
(`.unsupported`), so no profile-version-1 `evalStep` calls `forceAllocation`;
`CanaryMemoryLifecycleAnnealClaim` applies it between steps to exercise
`.indirect` locals. -/
noncomputable def forceAllocation (p : Program) (s : State)
    (localId : LocalId) : Except FaultKind (State × MemPlace) :=
  match s.frames with
  | [frame] =>
    match getElem? p.bodies frame.defId with
    | none => .error .unsupported
    | some body =>
      match getElem? body.locals localId, getElem? frame.locals localId with
      | some _, some .dead => .error .undefined
      | some _, some (.indirect place) => .ok (s, place)
      | some ty, some (.immediate optVal) =>
        match layoutOfTy ty with
        | none => .error .unsupported
        | some layout =>
          let (mem₁, place) := allocateStack s.mem layout
          let stored : Except FaultKind MemoryState :=
            match optVal with
            | none => .ok mem₁
            | some v => storeIndirect mem₁ ty place v
          match stored with
          | .error k => .error k
          | .ok mem₂ =>
            match setElem? frame.locals localId (.indirect place) with
            | none => .error .unsupported
            | some locals' =>
              .ok ({ s with
                frames := [{ frame with locals := locals' }]
                mem := mem₂ }, place)
      | _, _ => .error .unsupported
  | _ => .error .unsupported

end Trusted.MirSemantics

end
