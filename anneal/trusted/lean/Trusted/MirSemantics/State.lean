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
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Enum
import Trusted.MirSemantics.Memory

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Machine State and Entry Initialization (`Trusted.MirSemantics.State`)

Execution frame and machine state types (`FrameState`, `State`), choice
admissibility (`ValidChoice`), storage-marker bounds checks, and entry
initialization (`initState`) for $M_{\text{anneal}}$.
-/

/-- Active execution frame of $M_{\text{anneal}}$, corresponding to
`rustc_const_eval::interpret::Frame`
(`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
structure FrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlot

/-- Running machine state of $M_{\text{anneal}}$: the active execution
frames, caller-visible memory, and the byte-level memory holding the stack
allocations of locals that have been moved into memory (`LocalSlot.indirect`).
`initState` builds the entry state, so `State` has no synthetic pre-entry
variant. -/
structure State where
  frames : List FrameState
  callerMem : CallerMemory := ⟨[]⟩
  mem : MemoryState

/-- Admissible demonic choice predicate at state `s`. -/
noncomputable def ValidChoice (_p : Program) (_s : State) (c : Choice) : Prop :=
  c = 0

/-- Whether statement `stmt` is a `StorageLive` or `StorageDead` marker for
`localId`. -/
noncomputable def stmtHasStorageMarker (localId : LocalId) :
    StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.beq id localId
  | _ => false

/-- Whether any basic block in `body` contains a `StorageLive` or `StorageDead`
annotation for `localId`.

Corresponds to `always_storage_live_locals` in
`compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Some locals have no `StorageLive` or `StorageDead` statements within the
> entire MIR body. These locals are implicitly allocated for the full duration
> of the function."
> (`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

and `Miri.Interpreter.CallMachine.alwaysLiveVarsAndTemps`: locals without any
`StorageLive`/`StorageDead` annotation in the body are live for the entire
function activation, whereas annotated non-argument locals start `.dead`. -/
noncomputable def hasStorageAnnotation (body : Body) (localId : LocalId) :
    Bool :=
  body.basicBlocks.any (fun bb =>
    bb.statements.any (stmtHasStorageMarker localId))

/-- Check that every `StorageLive` and `StorageDead` local index in `body` is
strictly less than `body.locals.length`, matching the entry check in
`Miri.Interpreter.CallMachine.alwaysLiveVarsAndTemps`. -/
noncomputable def storageAnnotationsInBounds (body : Body) : Bool :=
  let numLocals := body.locals.length
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id numLocals
      | _ => true))

/-- Check that every unprojected `Assign(dst, Discriminant(src))` in `body`
whose `src` has an admitted fieldless enum type `.enum ety` (or the type
`core::cmp::Ordering`) and whose `dst` is in bounds has destination type
`.int ety.discrWidth ety.discrSigned` (`.int .i8 true` for `Ordering`, whose
discriminant type is its `#[repr(i8)]`),
matching `rustc`'s MIR well-typedness invariant for `Rvalue::Discriminant`
(`compiler/rustc_const_eval/src/interpret/step.rs` and
`compiler/rustc_const_eval/src/interpret/discriminant.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Discriminant(place) => {
>     let op = self.eval_place_to_op(*place, None)?;
>     let variant = self.read_discriminant(&op)?;
>     let discr = self.discriminant_for_variant(op.layout.ty, variant)?;
>     self.write_immediate(*discr, &dest)?;
> }"
> (`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Because `write_immediate` does not re-check the destination local's `MirTy`
signedness against `op.layout.ty.discriminant_ty(tcx)` (relying on `rustc`'s
MIR typechecker), rejecting ill-typed `Discriminant` destinations statically
at entry keeps both $M_{\text{anneal}}$ and $M_{\text{ref}}$ fail-closed. -/
noncomputable def discriminantTypesValid (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .discriminant src =>
          if dst.projection.isEmpty && src.projection.isEmpty then
            match getElem? body.locals src.localId with
            | some srcTy =>
              match srcTy with
              | .enum ety =>
                match getElem? body.locals dst.localId with
                | some dstTy =>
                  if enumAdmitted ety then
                    MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
                  else
                    true
                | none => true
              | .ordering =>
                match getElem? body.locals dst.localId with
                | some dstTy => MirTy.beq dstTy (.int .i8 true)
                | none => true
              | _ => true
            | none => true
          else
            true
        | _ => true
      | _ => true))

/-- Check that every unprojected `Assign(dst, Cast(IntToInt, _, castTy))` in
`body` whose `dst` is in bounds has destination type `castTy`, matching
`rustc`'s MIR well-typedness invariant that an assignment's place and rvalue
have the same type (`StatementKind::Assign` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "Assignments in which the types of the place and rvalue differ are not
> well-formed."

`Miri.Interpreter.Cast.cast` resolves the cast target layout from `castTy`
only when it differs from the destination type, and `write_immediate` does
not re-check the destination type, so rejecting ill-typed casts statically at
entry keeps both $M_{\text{anneal}}$ and $M_{\text{ref}}$ fail-closed. -/
noncomputable def castTypesValid (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .cast .intToInt _ castTy =>
          if dst.projection.isEmpty then
            match getElem? body.locals dst.localId with
            | some dstTy => MirTy.beq dstTy castTy
            | none => true
          else
            true
        | _ => true
      | _ => true))

/-- Initialize the local slots of `body` at function entry (`idx = 0 ..
body.locals.length - 1`), matching `Miri.Interpreter.CallMachine` (`pushRaw`,
`alwaysLiveVarsAndTemps`, `pushDone`) and
`compiler/rustc_const_eval/src/interpret/stack.rs` (`rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "self.storage_live(mir::RETURN_PLACE)?;
> let body = self.body();
> let always_live = always_storage_live_locals(body);
> for local in body.vars_and_temps_iter() {
>     if always_live.contains(local) {
>         self.storage_live(local)?;
>     }
> }"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

- `_0` (return place): `liveUninitSlot ty`.
- `_1 .. _argumentCount` (parameters): `.immediate (some arg)`.
- `> argumentCount`: `.dead` if `hasStorageAnnotation body idx`, else
  `liveUninitSlot ty`. -/
noncomputable def initLocalsLoop (body : Body) (args : List Val) :
    Nat → List MirTy → List LocalSlot
  | _, [] => []
  | idx, ty :: rest =>
      let slot : LocalSlot :=
        if Nat.beq idx 0 then
          liveUninitSlot ty
        else if Nat.ble idx body.argumentCount then
          match getElem? args (idx - 1) with
          | some v => .immediate (some v)
          | none => .dead
        else if hasStorageAnnotation body idx then
          .dead
        else
          liveUninitSlot ty
      slot :: initLocalsLoop body args (idx + 1) rest

/-- Entry initialization (`initState p q`):
Validates the 64-bit target layout (`p.pointerWidthBits = 64`), the MIR
semantic profile version (`p.mirProfileVersion = 1`; see
`Trusted.MirAst.Program`), entry body existence, non-empty basic blocks,
in-bounds storage annotations, well-typed `Discriminant` and `Cast`
destinations, supported local types, empty `callerMem`, and
well-typed `q.args`. Returns `.error .unsupported` if any static/entry
precondition fails. The entry state's memory is `entryMemory`. -/
noncomputable def initState (p : Program) (q : Query) :
    Except FaultKind State :=
  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1 then
    .error .unsupported
  else if !q.callerMem.allocations.isEmpty then
    .error .unsupported
  else
    match getElem? p.bodies p.entryDefId with
    | none => .error .unsupported
    | some body =>
      if body.basicBlocks.isEmpty then
        .error .unsupported
      else if !Nat.blt body.argumentCount body.locals.length then
        .error .unsupported
      else if !storageAnnotationsInBounds body then
        .error .unsupported
      else if !discriminantTypesValid body then
        .error .unsupported
      else if !castTypesValid body then
        .error .unsupported
      else if !body.locals.all isSupportedScalarOrUnitTy then
        .error .unsupported
      else
        let paramTys := (body.locals.drop 1).take body.argumentCount
        if !checkArgsMatch q.args paramTys then
          .error .unsupported
        else
          let locals := initLocalsLoop body q.args 0 body.locals
          let frame : FrameState := {
            defId := p.entryDefId
            blockIdx := 0
            stmtIdx := 0
            locals := locals
          }
          .ok {
            frames := [frame]
            callerMem := q.callerMem
            mem := entryMemory
          }

end Trusted.MirSemantics
