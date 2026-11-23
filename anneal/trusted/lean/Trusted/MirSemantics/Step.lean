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
>         ...
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

`Return` reads `_0`'s value (from memory with `loadIndirect` if `_0` is
`.indirect`); an uninitialized or dead `_0` faults with `.undefined`. -/
noncomputable def evalTerminator (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory) :
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
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .coreCall _ _ _ _ _ | .unsupported =>
    .fault .unsupported

/-!
## Profile v2 Memory, Reference, Raw-Pointer, and Core-Primitive Evaluation
-/

/-- Signed `BinOp.offset` in Profile v2: handles both non-negative and negative
`isize` element offsets inside a live allocation (failing `.undefined` on out-of-bounds
or overflow past `isize::MAX`). -/
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
allocation in `mem` when its address is taken (`Rvalue.ref` / `Rvalue.addressOf`),
initializing stack bytes if the local holds an immediate value. -/
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

/-- Project tuple / range fields through an immediate `Val` in Profile v2. -/
noncomputable def projectValFieldV2 :
    MirTy → Val → List ProjectionElem → Except FaultKind (MirTy × Val)
  | ty, v, [] => .ok (ty, v)
  | .tuple ts, .tuple vs, .field idx fTy :: rest =>
    match getElem? ts idx, getElem? vs idx with
    | some elemTy, some elemVal =>
      if !MirTy.beq elemTy fTy then
        .error .unsupported
      else
        projectValFieldV2 elemTy elemVal rest
    | _, _ => .error .unsupported
  | .rangeTo (.int .isize false), .rangeTo e, .field 0 fTy :: rest =>
    if !MirTy.beq fTy (.int .isize false) then
      .error .unsupported
    else
      let sv : Val := .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 e.toNat)⟩
      projectValFieldV2 (.int .isize false) sv rest
  | .rangeFrom (.int .isize false), .rangeFrom s, .field 0 fTy :: rest =>
    if !MirTy.beq fTy (.int .isize false) then
      .error .unsupported
    else
      let sv : Val := .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 s.toNat)⟩
      projectValFieldV2 (.int .isize false) sv rest
  | _, _, _ => .error .unsupported

/-- Read a projected `Place` in Profile v2, supporting unprojected locals,
immediate tuple/range `.field` projections, and single-step `.deref` on
sized references and raw pointers (`*p`). `isMove` additionally deinitializes
unprojected locals (and memory slots for indirect stack moves). -/
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
      if !rest.isEmpty then
        .error .unsupported
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
                | .dead => .error .undefined
                | .immediate optVal => .ok optVal
                | .indirect mplace => loadIndirectV2 mem baseTy mplace
              match ptrRes with
              | .error k => .error k
              | .ok none => .error .undefined
              | .ok (some (.ptr pv)) =>
                match pv.allocId with
                | none =>
                  if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 lay.size ||
                      !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then
                    .error .undefined
                  else if MirTy.beq pt .unit then
                    .ok (pt, some .unit, locals, mem)
                  else
                    .error .unsupported
                | some aid =>
                  if isMove then
                    match findAllocation aid mem.allocations with
                    | none => .error .undefined
                    | some a =>
                      if !Mutability.beq a.mutability .mut then
                        .error .undefined
                      else
                        match loadIndirectV2 mem pt ⟨aid, pv.offsetBytes.toNat⟩ with
                        | .error k => .error k
                        | .ok optVal =>
                          match deinitIndirectV2 mem pt ⟨aid, pv.offsetBytes.toNat⟩ with
                          | .ok mem1 => .ok (pt, optVal, locals, mem1)
                          | .error k => .error k
                  else
                    match loadIndirectV2 mem pt ⟨aid, pv.offsetBytes.toNat⟩ with
                    | .error k => .error k
                    | .ok optVal => .ok (pt, optVal, locals, mem)
              | .ok (some _) => .error .unsupported
        | _ => .error .unsupported
    | .field _ _ :: _ =>
      if isMove then
        .error .unsupported
      else
        let baseValRes : Except FaultKind (Option Val) :=
          match slot with
          | .dead => .error .undefined
          | .immediate optVal => .ok optVal
          | .indirect mplace => loadIndirectV2 mem baseTy mplace
        match baseValRes with
        | .error k => .error k
        | .ok none => .error .undefined
        | .ok (some v) =>
          match projectValFieldV2 baseTy v place.projection with
          | .error k => .error k
          | .ok (fty, fv) => .ok (fty, some fv, locals, mem)
    | .unsupported :: _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Stage 1 of Profile v2 operand evaluation. -/
noncomputable def evalOperandToSlotV2 (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mem : MemoryState) :
    Operand → Except FaultKind (MirTy × Option Val × List LocalSlot × MemoryState)
  | .copy place => readPlaceV2 bodyLocals locals mem false place
  | .move place => readPlaceV2 bodyLocals locals mem true place
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok v => .ok (c.ty, some v, locals, mem)
    | .error k => .error k

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

/-- Check pointer-to-pointer cast compatibility in Profile v2 (preserving
provenance while disallowing forging references or mismatched slice elements). -/
noncomputable def evalPtrToPtrCastV2 (srcTy : MirTy) (srcVal : Val)
    (castTy : MirTy) : Except FaultKind Val :=
  match castTy with
  | .rawPtr _ castPt =>
    match srcTy, srcVal with
    | .rawPtr _ srcPt, .ptr p | .ref _ srcPt, .ptr p =>
      if isUnsizedTy srcPt || isUnsizedTy castPt then
        .error .unsupported
      else
        .ok (.ptr p)
    | .rawPtr _ (.slice srcElem), .slicePtr p len
    | .ref _ (.slice srcElem), .slicePtr p len =>
      match castPt with
      | .slice castElem =>
        if MirTy.beq srcElem castElem then
          .ok (.slicePtr p len)
        else
          .error .unsupported
      | _ => .error .unsupported
    | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Evaluate `Rvalue.ref` in Profile v2 (`&local` or `&(*ptr)` reborrow). -/
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
            | .dead => .error .undefined
            | .immediate optVal => .ok optVal
            | .indirect mplace => loadIndirectV2 mem baseTy mplace
          match ptrRes with
          | .error k => .error k
          | .ok none => .error .undefined
          | .ok (some v) =>
            match refValidInMem mem reqMut pt v with
            | .error k => .error k
            | .ok () => .ok (v, locals, mem)
      | .rawPtr _ pt =>
        if !MirTy.beq dstTy (.ref reqMut pt) then
          .error .unsupported
        else
          let ptrRes : Except FaultKind (Option Val) :=
            match slot with
            | .dead => .error .undefined
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

/-- Evaluate `Rvalue.addressOf` in Profile v2 (`&raw const/mut local` or
`&raw const/mut (*ptr)`). -/
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
      | .ref srcMut pt =>
        if Mutability.beq srcMut .shared && Mutability.beq reqMut .mut then
          .error .undefined
        else if !MirTy.beq dstTy (.rawPtr reqMut pt) then
          .error .unsupported
        else
          let ptrRes : Except FaultKind (Option Val) :=
            match slot with
            | .dead => .error .undefined
            | .immediate optVal => .ok optVal
            | .indirect mplace => loadIndirectV2 mem baseTy mplace
          match ptrRes with
          | .error k => .error k
          | .ok none => .error .undefined
          | .ok (some v) => .ok (v, locals, mem)
      | .rawPtr _ pt =>
        if !MirTy.beq dstTy (.rawPtr reqMut pt) then
          .error .unsupported
        else
          let ptrRes : Except FaultKind (Option Val) :=
            match slot with
            | .dead => .error .undefined
            | .immediate optVal => .ok optVal
            | .indirect mplace => loadIndirectV2 mem baseTy mplace
          match ptrRes with
          | .error k => .error k
          | .ok none => .error .undefined
          | .ok (some v) => .ok (v, locals, mem)
      | _ => .error .unsupported
    | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Evaluate an `Rvalue` in Profile v2. -/
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
          if isUnsizedTy pt then
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
  | .discriminant place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match getElem? bodyLocals place.localId, getElem? locals place.localId with
      | some _, some .dead => .error .undefined
      | some srcTy, some (.immediate optVal) =>
        match srcTy with
        | .enum ety => evalDiscriminantOfVal ety optVal locals mem
        | .ordering => evalOrderingDiscriminantOfVal optVal locals mem
        | _ => .error .unsupported
      | some srcTy, some (.indirect mplace) =>
        match srcTy with
        | .enum ety =>
          match loadIndirectV2 mem srcTy mplace with
          | .error k => .error k
          | .ok optVal => evalDiscriminantOfVal ety optVal locals mem
        | .ordering =>
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

/-- Write `val` into `dst : Place` in Profile v2, supporting both unprojected
locals and dereference stores `(*ptr) = val` (requiring mutable provenance-backed
live aligned in-bounds storage). -/
noncomputable def writePlaceV2 (bodyLocals : List MirTy) (locals : List LocalSlot)
    (mem : MemoryState) (dst : Place) (dstTy : MirTy) (val : Val) :
    Except FaultKind (List LocalSlot × MemoryState) :=
  if !checkValV2 val dstTy then
    .error .unsupported
  else
    match dst.projection with
    | [] =>
      match getElem? locals dst.localId with
      | none => .error .unsupported
      | some .dead => .error .undefined
      | some (.immediate _) =>
        match setElem? locals dst.localId (.immediate (some val)) with
        | some locals1 => .ok (locals1, mem)
        | none => .error .unsupported
      | some (.indirect mplace) =>
        match storeIndirectV2 mem dstTy mplace val with
        | .ok mem1 => .ok (locals, mem1)
        | .error k => .error k
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
                | .dead => .error .undefined
                | .immediate optVal => .ok optVal
                | .indirect mplace => loadIndirectV2 mem ptrTy mplace
              match ptrRes with
              | .error k => .error k
              | .ok none => .error .undefined
              | .ok (some (.ptr pv)) =>
                match pv.allocId with
                | none =>
                  if Nat.beq pv.offsetBytes.toNat 0 || Nat.blt 0 lay.size ||
                      !Nat.beq (Nat.mod pv.offsetBytes.toNat (Nat.pow 2 lay.alignLog2)) 0 then
                    .error .undefined
                  else if MirTy.beq pt .unit then
                    .ok (locals, mem)
                  else
                    .error .unsupported
                | some aid =>
                  match findAllocation aid mem.allocations with
                  | none => .error .undefined
                  | some a =>
                    if !a.live || !Mutability.beq a.mutability .mut then
                      .error .undefined
                    else
                      match storeIndirectV2 mem pt ⟨aid, pv.offsetBytes.toNat⟩ val with
                      | .ok mem1 => .ok (locals, mem1)
                      | .error k => .error k
              | .ok (some _) => .error .unsupported
        | _ => .error .unsupported
      | _, _ => .error .unsupported
    | _ => .error .unsupported

/-- Determine the static pointee/destination type of `dst : Place` in
Profile v2. -/
noncomputable def placeStaticTyV2 (bodyLocals : List MirTy) (dst : Place) :
    Option MirTy :=
  match getElem? bodyLocals dst.localId, dst.projection with
  | some ty, [] => some ty
  | some (.ref _ pt), [.deref] | some (.rawPtr _ pt), [.deref] =>
    if isUnsizedTy pt then none else some pt
  | _, _ => none

/-- Evaluate one `StatementKind` in Profile v2. -/
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
      match evalRvalueV2 body.locals frame.locals mem dstTy rvalue with
      | .error k => .fault k
      | .ok (val, locals1, mem1) =>
        match writePlaceV2 body.locals locals1 mem1 dst dstTy val with
        | .error k => .fault k
        | .ok (locals2, mem2) =>
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

/-- Execute a closed-world `CoreCallOp` primitive in Profile v2 against memory
`m`. Note that `sliceFromRawParts` / `sliceFromRawPartsMut` admit integer
element types (`u8`, `u16`, `u32`, `u64`, `usize`, etc.) whose bit patterns are
all valid when initialized. -/
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
  | .sliceAsPtr, [(.ref reqMut (.slice elem), .slicePtr p len)] =>
    if !MirTy.beq dstTy (.rawPtr .shared elem) then
      .error .unsupported
    else
      match refValidInMem m reqMut (.slice elem) (.slicePtr p len) with
      | .error k => .error k
      | .ok () => .ok (.ptr p)
  | .sliceAsMutPtr, [(.ref .mut (.slice elem), .slicePtr p len)] =>
    if !MirTy.beq dstTy (.rawPtr .mut elem) then
      .error .unsupported
    else
      match refValidInMem m .mut (.slice elem) (.slicePtr p len) with
      | .error k => .error k
      | .ok () => .ok (.ptr p)
  | .sliceFromRawParts, [(.rawPtr _ (.int w s), .ptr p), (.int .isize false, .scalar lenSv)] =>
    let elem := MirTy.int w s
    if !MirTy.beq dstTy (.ref .shared (.slice elem)) then
      .error .unsupported
    else
      let lay := intLayout w
      sliceFromRawPartsCheck m false lay.size lay.alignLog2 p
        (UInt64.ofNat lenSv.bits.toNat)
  | .sliceFromRawPartsMut, [(.rawPtr .mut (.int w s), .ptr p), (.int .isize false, .scalar lenSv)] =>
    let elem := MirTy.int w s
    if !MirTy.beq dstTy (.ref .mut (.slice elem)) then
      .error .unsupported
    else
      let lay := intLayout w
      sliceFromRawPartsCheck m true lay.size lay.alignLog2 p
        (UInt64.ofNat lenSv.bits.toNat)
  | .sliceGetUncheckedRangeTo,
      [(.ref inMut (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeTo (.int .isize false), .rangeTo endOff)] =>
    match dstTy with
    | .ref outMut (.slice (.int .i8 false)) =>
      if Mutability.beq inMut .shared && Mutability.beq outMut .mut then
        .error .undefined
      else
        match refValidInMem m outMut (.slice (.int .i8 false)) (.slicePtr p len) with
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
        match refValidInMem m outMut (.slice (.int .i8 false)) (.slicePtr p len) with
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
  | _, _ => .error .unsupported

/-- Evaluate a basic block's `TerminatorKind` in Profile v2. -/
noncomputable def evalTerminatorV2 (body : Body) (bb : BasicBlock)
    (frame : FrameState) (mem : MemoryState) (callerMem : CallerMemory) :
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
          | some (.immediate none) | some .dead => .error .undefined
          | some (.indirect mplace) =>
            match loadIndirectV2 mem retTy mplace with
            | .ok (some v) => .ok v
            | .ok none => .error .undefined
            | .error k => .error k
          | none => .error .unsupported
        match retRes with
        | .error k => .fault k
        | .ok retVal =>
          if !refsStayInCallerMem callerMem retTy retVal ||
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
  | .assert cond expected msg target _ =>
    match evalPrimitiveOperandV2 body.locals frame.locals mem cond with
    | .error k => .fault k
    | .ok (condVal, locals1, mem1) =>
      match condVal with
      | .bool b =>
        if b == expected then
          jumpToBlock { frame with locals := locals1 } mem1 callerMem target
        else
          match msg with
          | .misalignedPtrDeref | .nullPtrDeref => .fault .undefined
          | _ => .fault .unsupported
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
  | .coreCall _ _ _ none _ | .unwindResume | .call _ _ _ _ _ | .unsupported =>
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
            evalTerminatorV2 body bb frame s.mem s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

/-- Choice-indexed wrapper for Profile v2 deterministic small-step
evaluation. -/
noncomputable def evalStepV2Choice (p : Program) (_c : Choice) (s : State) :
    StepResult State TerminalOut :=
  evalStepV2 p s

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
  | [frame] =>
    match getElem? p.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match getElem? body.basicBlocks frame.blockIdx with
      | none => .fault .unsupported
      | some bb =>
        match getElem? bb.statements frame.stmtIdx with
        | some stmt => evalStatement body frame s.mem s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminator body bb frame s.mem s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

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
