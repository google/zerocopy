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
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Ops
import Trusted.MirSemantics.Enum
import Trusted.MirSemantics.State

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Small-Step Execution Rules (`Trusted.MirSemantics.Step`)

Constant, operand, rvalue, place-write, statement, terminator, and single-step
transition rules (`evalStep`) for $M_{\text{anneal}}$.
-/

/-- Decode a typed constant literal `ConstLit` into a runtime `Val`, matching
`ScalarInt::try_from_uint` and `ScalarInt::try_to_bool` in
`compiler/rustc_middle/src/ty/consts/int.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and `Miri.Memory.ScalarInt`
(`vendor/lean-miri/Miri/Memory/ScalarInt.lean`):

> "pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
>     let (r, overflow) = Self::truncate_from_uint(i, size);
>     if overflow { None } else { Some(r) }
> }"
> "pub fn try_to_bool(self) -> Result<bool, ()> {
>     match self.to_u8() {
>         0 => Ok(false),
>         1 => Ok(true),
>         _ => Err(()),
>     }
> }"
> (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

A 1-byte `.bool` scalar whose value is neither `0` nor `1` triggers
`ScalarIntError.invalidBool`, which `Miri.Interpreter.ScalarOps.scalarError`
maps to `.undefinedBehavior`, so `evalConstLit` returns `.error .undefined`.

For fieldless enums (`.enum ety`), constant decoding matches `op_to_const`
(`compiler/rustc_const_eval/src/const_eval/eval_queries.rs:258`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
`read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs`,
`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "let discr_val = self.int_to_int_or_float(&tag_val, discr_layout).unwrap();
> let discr_bits = discr_val.to_scalar().to_bits(discr_layout.size)?;
> ...
> adt.discriminants(*self.tcx).find(|(_, var)| var.val == discr_bits)
> ...
> .ok_or_else(|| err_ub!(InvalidTag(Scalar::from_uint(tag_bits,
>     tag_layout.size))))?;"

- Admitted 1-variant ZST enums (`ety.tagRepr = .zeroSized`) decode
  `ConstLit.zeroSized` to `.ok (.enumVal ety 0)`.
- Admitted direct-tagged enums (`ety.tagRepr = .scalar tagW tagS`) validate
  that `bits` fits in `tagW`, extend/truncate `bits` to `ety.discrWidth` via
  `tagBitsToDiscrBits`, and resolve the matching declaration index via
  `findDiscrVariant?` (returning `.error .undefined` on an invalid tag bit
  pattern not matching any declared discriminant). -/
noncomputable def evalConstLit : MirTy → ConstLit → Except FaultKind Val
  | .int w s, .scalar bits =>
    if truncateBits w bits != bits then
      .error .unsupported
    else
      .ok (.scalar ⟨w, s, truncateBits w bits⟩)
  | .bool, .scalar bits =>
    if truncateBits .i8 bits != bits then
      .error .unsupported
    else
      let v := UInt8.ofNat (truncateBits .i8 bits).toNat
      if v == 0 then
        .ok (.bool false)
      else if v == 1 then
        .ok (.bool true)
      else
        .error .undefined
  | .unit, .zeroSized => .ok .unit
  | .enum ety, .zeroSized =>
    if isZstEnumTy ety then .ok (.enumVal ety 0) else .error .unsupported
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => .error .unsupported
    | .scalar tagW tagS =>
      if !enumAdmitted ety || truncateBits tagW bits != bits then
        .error .unsupported
      else
        let discrBits := tagBitsToDiscrBits tagW tagS ety.discrWidth bits
        match findDiscrVariant? discrBits ety.discriminants with
        | some v => .ok (.enumVal ety v)
        | none => .error .undefined
  | _, _ => .error .unsupported

/-- Stage 1 of operand evaluation (`eval_operand` in
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

Note that upstream `eval_operand` currently leaves move invalidation
unimplemented (as recorded in the `FIXME` above). As a deliberate, conservative
over-approximation (sound because deinitializing can only introduce faults on
subsequent reads), `evalOperandToSlot` resolves an `Operand` to
`(ty : MirTy, optVal : Option Val, locals' : List LocalSlot)` without yet
requiring `optVal` to be initialized (`some v`), and deinitializes moved
non-ZST locals:
- `.copy place`: reads `(ty, optVal)` without mutating `locals`.
- `.move place`: reads `(ty, optVal)` and conservatively transitions
  `locals[place.localId]` to `liveUninitSlot ty` (preserving
  `.live (some .unit)` on `MirTy.unit` and `.live (some (.enumVal ety 0))` on
  admitted 1-variant `.zeroSized` `MirTy.enum`, and setting all other local
  types to `.live none`, matching `OperandMachine.evalOperand` with opt-in
  `deinitMovedPlace = true`).
- `.constant c`: decodes constant literal without mutating `locals`. -/
noncomputable def evalOperandToSlot (bodyLocals : List MirTy)
    (locals : List LocalSlot) :
    Operand → Except FaultKind (MirTy × Option Val × List LocalSlot)
  | .copy place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match getElem? bodyLocals place.localId,
          getElem? locals place.localId with
      | some ty, some (.live optVal) => .ok (ty, optVal, locals)
      | some _, some .dead => .error .undefined
      | _, _ => .error .unsupported
  | .move place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match getElem? bodyLocals place.localId,
          getElem? locals place.localId with
      | some ty, some (.live optVal) =>
        match setElem? locals place.localId (liveUninitSlot ty) with
        | some locals' => .ok (ty, optVal, locals')
        | none => .error .unsupported
      | some _, some .dead => .error .undefined
      | _, _ => .error .unsupported
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok v => .ok (c.ty, some v, locals)
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
non-primitives such as `.unit`), and then checks initialization (`optVal = some
v`, faulting with `.undefined` on uninitialized storage). -/
noncomputable def evalPrimitiveOperand (bodyLocals : List MirTy)
    (locals : List LocalSlot) (opnd : Operand) :
    Except FaultKind (Val × List LocalSlot) :=
  match evalOperandToSlot bodyLocals locals opnd with
  | .error k => .error k
  | .ok (ty, optVal, locals') =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match optVal with
      | some v => .ok (v, locals')
      | none => .error .undefined

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
- `.use opnd`: resolves `(srcTy, optVal, locals₁) ← evalOperandToSlot`, checks
  `srcTy = dstTy` (`copyRuntimePlaceNoValidate`), then checks `optVal = some v`
  (validity check in `copy_op` / `copyRuntimePlace`).
- `.binaryOp op lhs rhs`: evaluates `lhs` and then `rhs` left-to-right via
  `evalPrimitiveOperand` (threading `locals₁` from `lhs` into `rhs`), then
  applies `evalBinOp`.
- `.unaryOp op opnd`: evaluates `opnd` via `evalPrimitiveOperand`, then applies
  `evalUnOp`.
- `.discriminant place`: reads the active variant of an unprojected local of
  admitted fieldless enum type `.enum ety` and returns its declared
  discriminant as a scalar of `(ety.discrWidth, ety.discrSigned)`, matching
  `read_discriminant` and `discriminant_for_variant` in
  `compiler/rustc_const_eval/src/interpret/discriminant.rs` (`rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
  `Miri.Interpreter.Discriminant`:

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

  Reading `.discriminant` from a `.dead` local or from an uninitialized
  (`.live none`) scalar-tagged enum local faults with `.error .undefined`,
  whereas an inhabited 1-variant ZST enum (`ety.tagRepr = .zeroSized`,
  `Variants::Single { index: 0 }`) returns `ety.discriminants[0]` without
  reading tag bytes. -/
noncomputable def evalRvalue (bodyLocals : List MirTy) (locals : List LocalSlot)
    (dstTy : MirTy) : Rvalue → Except FaultKind (Val × List LocalSlot)
  | .use opnd =>
    match evalOperandToSlot bodyLocals locals opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, locals₁) =>
      if !(MirTy.beq srcTy dstTy) then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, locals₁)
        | none => .error .undefined
  | .binaryOp op lhs rhs =>
    match evalPrimitiveOperand bodyLocals locals lhs with
    | .error k => .error k
    | .ok (lVal, locals₁) =>
      match evalPrimitiveOperand bodyLocals locals₁ rhs with
      | .error k => .error k
      | .ok (rVal, locals₂) =>
        match evalBinOp op lVal rVal with
        | .error k => .error k
        | .ok res => .ok (res, locals₂)
  | .unaryOp op opnd =>
    match evalPrimitiveOperand bodyLocals locals opnd with
    | .error k => .error k
    | .ok (v, locals₁) =>
      match evalUnOp op v with
      | .error k => .error k
      | .ok res => .ok (res, locals₁)
  | .discriminant place =>
    if !place.projection.isEmpty then
      .error .unsupported
    else
      match getElem? bodyLocals place.localId,
          getElem? locals place.localId with
      | some (.enum ety), some slot =>
        if !enumAdmitted ety then
          .error .unsupported
        else
          -- For 1-variant `.zeroSized` enums, `Miri`'s `readDiscriminant`
          -- (`Variants::Single { index: 0 }`) returns variant `0` without
          -- reading tag bytes even if a slot holds `.live none` (`Uninit`),
          -- preserving universal 1-step lockstep over arbitrary `FrameState`s.
          match ety.tagRepr, slot with
          | _, .dead => .error .undefined
          | .zeroSized, .live none =>
            match getElem? ety.discriminants 0 with
            | some disc =>
              .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
            | none => .error .unsupported
          | .zeroSized, .live (some (.enumVal ety' v)) =>
            if EnumTy.beq ety ety' && Nat.beq v 0 then
              match getElem? ety.discriminants 0 with
              | some disc =>
                .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
              | none => .error .unsupported
            else
              .error .unsupported
          | .zeroSized, .live (some _) => .error .unsupported
          | .scalar _ _, .live none => .error .undefined
          | .scalar _ _, .live (some (.enumVal ety' v)) =>
            if EnumTy.beq ety ety' && Nat.blt v ety.discriminants.length then
              match getElem? ety.discriminants v with
              | some disc =>
                .ok (.scalar ⟨ety.discrWidth, ety.discrSigned,
                  truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩, locals)
              | none => .error .unsupported
            else
              .error .unsupported
          | .scalar _ _, .live (some _) => .error .unsupported
      | _, _ => .error .unsupported
  | _ => .error .unsupported

/-- Write `val` into an unprojected `dst : Place` of known `dstTy : MirTy` in
`locals`: checks `checkVal val dstTy` first (matching
`Rvalue.assertRvalueLayout`), then checks `dst` liveness (matching
`Place.writePlaceImmediate`). -/
noncomputable def writePlace (locals : List LocalSlot) (dstLocalId : LocalId)
    (dstTy : MirTy) (val : Val) : Except FaultKind (List LocalSlot) :=
  if !checkVal val dstTy then
    .error .unsupported
  else
    match getElem? locals dstLocalId with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.live _) =>
      match setElem? locals dstLocalId (.live (some val)) with
      | some locals' => .ok locals'
      | none => .error .unsupported

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
> "assert!(local != mir::RETURN_PLACE, \"Cannot make return place dead\");"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- `.storageLive localId` sets `locals[localId] := liveUninitSlot localTy` for
  any in-bounds `localId < frame.locals.length` (and faults with `.unsupported`
  on out-of-bounds `localId`).
- `.storageDead 0` or out-of-bounds `.storageDead localId` faults with
  `.unsupported` (`StackError.cannotMakeReturnPlaceDead` /
  `StackError.invalidLocal`).
- `.assign dst rvalue` resolves `dst`'s local bounds and `dstTy` first, then
  evaluates `rvalue` (yielding `(val, localsAfterRval)`), then checks
  `checkVal` and `dst` liveness in `writePlace`, matching `rustc` and
  `lean-miri` for unprojected sized locals (where `local_to_place` does not
  check liveness and `DeadLocal` fires at write time; an unmodeled RHS can
  fault `.unsupported` before write-time `DeadLocal`, and `.use` checks
  uninitialized input before writing while `rustc`'s `copy_op` validates after
  writing, both producing `.undefined`). -/
noncomputable def evalStatement (body : Body) (frame : FrameState)
    (callerMem : CallerMemory) (stmt : StatementKind) :
    StepResult State TerminalOut :=
  match stmt with
  | .nop =>
    .step { frames := [{ frame with stmtIdx := frame.stmtIdx + 1 }], callerMem }
  | .storageLive localId =>
    match getElem? body.locals localId with
    | none => .fault .unsupported
    | some localTy =>
      match setElem? frame.locals localId (liveUninitSlot localTy) with
      | some locals' =>
        .step {
          frames := [{
            frame with
            stmtIdx := frame.stmtIdx + 1
            locals := locals'
          }]
          callerMem
        }
      | none => .fault .unsupported
  | .storageDead localId =>
    if Nat.beq localId 0 then
      .fault .unsupported
    else
      match setElem? frame.locals localId .dead with
      | some locals' =>
        .step {
          frames := [{
            frame with
            stmtIdx := frame.stmtIdx + 1
            locals := locals'
          }]
          callerMem
        }
      | none => .fault .unsupported
  | .assign dst rvalue =>
    if !dst.projection.isEmpty then
      .fault .unsupported
    else
      match getElem? body.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match evalRvalue body.locals frame.locals dstTy rvalue with
        | .error k => .fault k
        | .ok (val, localsAfterRval) =>
          match writePlace localsAfterRval dst.localId dstTy val with
          | .error k => .fault k
          | .ok localsAfterWrite =>
            .step {
              frames := [{
                frame with
                stmtIdx := frame.stmtIdx + 1
                locals := localsAfterWrite
              }]
              callerMem
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

/-- Assign the frame location to `(target, 0)`, matching
`Miri.Interpreter.ControlFlow.goToBlock` (`Miri/Interpreter/ControlFlow.lean`:
target block existence is checked at the start of the next step in `evalStep` /
`Step.step`). -/
noncomputable def jumpToBlock (frame : FrameState) (callerMem : CallerMemory)
    (target : BasicBlockId) : StepResult State TerminalOut :=
  .step {
    frames := [{ frame with blockIdx := target, stmtIdx := 0 }]
    callerMem
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
> `8144389c895da997dbdecaa635e41d6a50be6ffd`) -/
noncomputable def evalTerminator (body : Body) (bb : BasicBlock)
    (frame : FrameState) (callerMem : CallerMemory) :
    StepResult State TerminalOut :=
  match bb.terminator with
  | .goto target => jumpToBlock frame callerMem target
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match getElem? frame.locals 0 with
      | some (.live (some retVal)) =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some (.live none) | some .dead => .fault .undefined
      | none => .fault .unsupported
  | .unreachable =>
    .fault .undefined
  | .switchInt discr targets =>
    match evalPrimitiveOperand body.locals frame.locals discr with
    | .error k => .fault k
    | .ok (discrVal, localsAfterDiscr) =>
      let targetRes : Except FaultKind BasicBlockId :=
        match discrVal with
        | .scalar sv =>
          evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches
        | .bool b =>
          evalBoolSwitchBranches b targets.otherwise targets.branches
        | _ => .error .unsupported
      match targetRes with
      | .error k => .fault k
      | .ok target =>
        jumpToBlock { frame with locals := localsAfterDiscr } callerMem target
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>
    .fault .unsupported

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
        | some stmt => evalStatement body frame s.callerMem stmt
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            evalTerminator body bb frame s.callerMem
          else
            .fault .unsupported
  | _ => .fault .unsupported

end Trusted.MirSemantics
