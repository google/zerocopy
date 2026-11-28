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
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Memory
public import Trusted.MirSemantics.Bytes

@[expose] public section

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
`8144389c895da997dbdecaa635e41d6a50be6ffd`).

- `defId`: index into `Program.bodies` when `sysrootOp? = none`.
- `sysrootOp?`: when `some op`, this frame executes the pinned `core::num`
  sysroot primitive `sysrootNumBody op` rather than a body in `Program.bodies`.
- `retDst?` / `retTarget?`: caller return destination and continuation block for
  non-root callee frames (`none` on the root entry frame). -/
structure FrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlot
  sysrootOp? : Option SysrootNumOp := none
  retDst? : Option Place := none
  retTarget? : Option BasicBlockId := none

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

/-- Check that every `.assert cond ...` terminator in `body` whose condition
is an unprojected in-bounds local or constant literal has type `.bool`,
matching `rustc`'s MIR validator check for `TerminatorKind::Assert` in
`compiler/rustc_mir_transform/src/validate.rs` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "TerminatorKind::Assert { cond, .. } => {
>     let cond_ty = cond.ty(&self.body.local_decls, self.tcx);
>     if cond_ty != self.tcx.types.bool {
>         self.fail(
>             location,
>             format!(
>                 \"encountered non-boolean condition of type {cond_ty} in
>                 `Assert` terminator\"
>             ),
>         );
>     }
> }" -/
noncomputable def assertConditionTypesValid (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .assert cond _ _ _ _ =>
      match cond with
      | .copy p | .move p =>
        if p.projection.isEmpty then
          match getElem? body.locals p.localId with
          | some condTy => MirTy.beq condTy .bool
          | none => true
        else
          true
      | .constant c => MirTy.beq c.ty .bool
    | _ => true)

/-- Profile v2 extension of `discriminantTypesValid`, additionally checking
that `Rvalue.discriminant` on `.option _` writes to `.int .isize true`. -/
noncomputable def discriminantTypesValidV2 (body : Body) : Bool :=
  discriminantTypesValid body &&
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst (.discriminant src) =>
        if dst.projection.isEmpty && src.projection.isEmpty then
          match getElem? body.locals src.localId with
          | some (.option _) =>
            match getElem? body.locals dst.localId with
            | some dstTy => MirTy.beq dstTy (.int .isize true)
            | none => true
          | _ => true
        else
          true
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

/-- Pinned left-homogeneity of `Trusted.MirAst.BinOp`, matching
`Miri.MIR.BinOp.leftHomogeneous` and `binop_left_homogeneous` in
`compiler/rustc_const_eval/src/util/mod.rs` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> /// Classify whether an operator is "left-homogeneous", i.e., the LHS has the
> /// same type as the result.

The arms below list the same `true`/`false` partition of operators as that
function's `match`. -/
noncomputable def binOpLeftHomogeneous : BinOp → Bool
  | .add | .addUnchecked | .sub | .subUnchecked | .mul | .mulUnchecked
  | .div | .rem | .bitXor | .bitAnd | .bitOr | .offset
  | .shl | .shlUnchecked | .shr | .shrUnchecked => true
  | .addWithOverflow | .subWithOverflow | .mulWithOverflow
  | .eq | .ne | .lt | .le | .gt | .ge | .cmp => false

/-- Pinned right-homogeneity of `Trusted.MirAst.BinOp`, matching
`Miri.MIR.BinOp.rightHomogeneous` and `binop_right_homogeneous` in
`compiler/rustc_const_eval/src/util/mod.rs` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> /// Classify whether an operator is "right-homogeneous", i.e., the RHS has the
> /// same type as the LHS.

The arms below list the same `true`/`false` partition of operators as that
function's `match`. -/
noncomputable def binOpRightHomogeneous : BinOp → Bool
  | .add | .addUnchecked | .addWithOverflow | .sub | .subUnchecked
  | .subWithOverflow | .mul | .mulUnchecked | .mulWithOverflow | .div | .rem
  | .bitXor | .bitAnd | .bitOr | .eq | .ne | .lt | .le | .gt | .ge
  | .cmp => true
  | .offset | .shl | .shlUnchecked | .shr | .shrUnchecked => false

/-- Pinned homogeneity of `Trusted.MirAst.UnOp` (operand and result share a
type), matching `Miri.MIR.UnOp.homogeneous`. `rustc` has no `util` helper
for unary operators; the rule is `UnOp::ty` in
`compiler/rustc_middle/src/mir/statement.rs` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> UnOp::Not | UnOp::Neg => arg_ty,
> UnOp::PtrMetadata => arg_ty.pointee_metadata_ty_or_projection(tcx), -/
noncomputable def unOpHomogeneous : UnOp → Bool
  | .not | .neg => true
  | .ptrMetadata => false

/-- Check whether an unprojected, in-bounds local operand agrees structurally
with `expected` (leaving constants and projected/out-of-bounds operands
unconstrained). -/
noncomputable def localOperandMatchesTy (locals : List MirTy)
    (opnd : Operand) (expected : MirTy) : Bool :=
  match opnd with
  | .copy p | .move p =>
    if p.projection.isEmpty then
      match getElem? locals p.localId with
      | some srcTy => MirTy.beq srcTy expected
      | none => true
    else
      true
  | .constant _ => true

/-- Resolve the declared `MirTy` of `opnd` when it is an unprojected in-bounds
local or a constant operand. -/
noncomputable def operandTy? (locals : List MirTy) : Operand → Option MirTy
  | .copy p | .move p =>
    if p.projection.isEmpty then getElem? locals p.localId else none
  | .constant c => some c.ty

/-- Check that every unprojected, in-bounds `Assign(dst, rv)` operand whose
layout hint `Miri` caches directly via `known` (`Use`, `BinaryOp`, `UnaryOp` in
`Miri.Interpreter.Rvalue.evalRvalueIntoPlace`) agrees with the declared local
type, matching `rustc`'s MIR well-typedness invariant
(`StatementKind::Assign` in `compiler/rustc_middle/src/mir/syntax.rs`). -/
noncomputable def assignTypesValid (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        if dst.projection.isEmpty then
          match getElem? body.locals dst.localId with
          | none => true
          | some dstTy =>
            match rv with
            | .use opnd => localOperandMatchesTy body.locals opnd dstTy
            | .binaryOp op lhs rhs =>
              let lhsOk : Bool :=
                if binOpLeftHomogeneous op then
                  localOperandMatchesTy body.locals lhs dstTy
                else
                  true
              let rhsOk : Bool :=
                if binOpRightHomogeneous op then
                  match operandTy? body.locals lhs with
                  | none => true
                  | some lTy => localOperandMatchesTy body.locals rhs lTy
                else
                  true
              lhsOk && rhsOk
            | .unaryOp op opnd =>
              if unOpHomogeneous op then
                localOperandMatchesTy body.locals opnd dstTy
              else
                true
            | _ => true
        else
          true
      | _ => true))

/-- Underlying MIR binary operator implemented by each `SysrootNumKind`. -/
noncomputable def sysrootNumBinOp : SysrootNumKind → BinOp
  | .uncheckedAdd => .addUnchecked
  | .uncheckedSub => .subUnchecked
  | .uncheckedMul => .mulUnchecked
  | .wrappingAdd => .add
  | .wrappingSub => .sub
  | .wrappingMul => .mul

/-- Pinned synthetic MIR `Body` for a verified `core::num` sysroot call
(`_0 = binOp(copy _1, copy _2); return`). Matched 1:1 against `core`'s
`tcx.instance_mir` by `anneal-rustc-capture` and loaded into both
$M_{\text{anneal}}$ and $M_{\text{ref}}$ (`dispatch.loadMir`). The source is
`library/core/src/num/uint_macros.rs` (`int_macros.rs` for signed types) in
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, e.g.:

> pub const unsafe fn unchecked_add(self, rhs: Self) -> Self {
>     assert_unsafe_precondition!(
>         check_language_ub,
>         concat!(stringify!($SelfT), "::unchecked_add cannot overflow"),
> ...
>     // SAFETY: this is guaranteed to be safe by the caller.
>     unsafe {
>         intrinsics::unchecked_add(self, rhs)
>     }
> }

> pub const fn wrapping_add(self, rhs: Self) -> Self {
>     intrinsics::wrapping_add(self, rhs)
> }

The `assert_unsafe_precondition!` branch is dead under capture's flags (UB
checks off; see `verify_sysroot_num_call` in `anneal-rustc-capture`), so the
body reduces to the intrinsic. `unchecked_*` keeps its UB contract through
`.addUnchecked`/`.subUnchecked`/`.mulUnchecked`, which fault `.undefined` on
overflow, and is marked `isUnsafe`. -/
noncomputable def sysrootNumBody (op : SysrootNumOp) : Body :=
  let ty : MirTy := .int op.width op.signed
  let isUnsafe : Bool :=
    match op.kind with
    | .uncheckedAdd | .uncheckedSub | .uncheckedMul => true
    | .wrappingAdd | .wrappingSub | .wrappingMul => false
  {
    identity := "core::num::sysroot"
    isUnsafe := isUnsafe
    argumentCount := 2
    locals := [ty, ty, ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp (sysrootNumBinOp op.kind)
          (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .return_
      cleanup := false
    }]
  }

/-- Resolve the `Body` currently executing in `frame` (`sysrootNumBody op` when
`frame.sysrootOp? = some op`, otherwise `p.bodies[frame.defId]`). -/
noncomputable def activeFrameBody (p : Program) (frame : FrameState) :
    Option Body :=
  match frame.sysrootOp? with
  | some op => some (sysrootNumBody op)
  | none => getElem? p.bodies frame.defId

/-- Membership test on a `List Nat` without emitting `._unsafe_rec`. -/
noncomputable def natListContains (x : Nat) : List Nat → Bool
  | [] => false
  | y :: rest => Nat.beq x y || natListContains x rest

/-- Collect the caller places moved by a call's argument list. -/
noncomputable def movePlaceList : List Operand → List Place
  | [] => []
  | .move p :: rest => p :: movePlaceList rest
  | _ :: rest => movePlaceList rest

/-- Pairwise disjointness and empty-projection check across moved argument
places and the call destination place, matching `moveDefinitelyDisjoint` in
`Miri.Interpreter.Call`. -/
noncomputable def placesDisjointAux (seen : List LocalId) : List Place → Bool
  | [] => true
  | p :: rest =>
    if !p.projection.isEmpty || natListContains p.localId seen then
      false
    else
      placesDisjointAux (p.localId :: seen) rest

/-- Pairwise local-disjointness of `.move` call arguments and `dst`, matching
`move_definitely_disjoint` in `eval_callee_and_args`
(`compiler/rustc_const_eval/src/interpret/step.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> // We only have to care about `Move` arguments.
> ...
> if place.is_indirect_first_projection() {
>     // An indirect in-place argument could alias with anything else...
>     break 'move_definitely_disjoint false;
> }
> if !previous_locals.insert(place.local) {
>     // This local is the base for two arguments! They might overlap.
>     break 'move_definitely_disjoint false;
> }

`rustc` then forces possibly-aliasing moved arguments into memory. Profile
version 1 has no in-memory argument passing, so `callTargetAdmitted` requires
this check to succeed and also rejects every projected moved place or
destination. -/
noncomputable def moveDefinitelyDisjoint (args : List Operand) (dst : Place) :
    Bool :=
  placesDisjointAux [] (movePlaceList args ++ [dst])

/-- Static type and constant admissibility of call arguments `args` against
callee parameter types `paramTys`. -/
noncomputable def callArgsMatchBody (bodyLocals : List MirTy) :
    List Operand → List MirTy → Bool
  | [], [] => true
  | opnd :: restArgs, paramTy :: restParams =>
    let argOk : Bool :=
      match opnd with
      | .copy place | .move place =>
        if !place.projection.isEmpty then
          false
        else
          match getElem? bodyLocals place.localId with
          | some argTy => MirTy.beq argTy paramTy
          | none => false
      | .constant c =>
        MirTy.beq c.ty paramTy &&
          match evalConstLit c.ty c.lit with
          | .ok _ => true
          | .error _ => false
    argOk && callArgsMatchBody bodyLocals restArgs restParams
  | _, _ => false

/-- Static admissibility of a single call site inside `body` against resolved
`calleeBody`. It statically over-approximates the dynamic checks that `rustc`
performs when it builds the callee frame (`init_stack_frame` and
`pass_argument` in `compiler/rustc_const_eval/src/interpret/call.rs`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> /// Initialize a single callee argument, checking the types for compatibility.

Here argument, parameter, destination and return types must be identical
supported scalar or unit types, not merely ABI-compatible, and the argument
count must equal the callee's `argumentCount`. -/
noncomputable def callTargetAdmitted (body : Body) (bb : BasicBlock)
    (calleeBody : Body) (args : List Operand) (dst : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) : Bool :=
  !bb.cleanup &&
    (match unwind with | .cleanup _ => false | _ => true) &&
    (match target with
     | none => true
     | some tgt => Nat.blt tgt body.basicBlocks.length) &&
    dst.projection.isEmpty &&
    moveDefinitelyDisjoint args dst &&
    Nat.beq args.length calleeBody.argumentCount &&
    Nat.blt calleeBody.argumentCount calleeBody.locals.length &&
    (match getElem? body.locals dst.localId, getElem? calleeBody.locals 0 with
     | some dstTy, some retTy =>
       isSupportedScalarOrUnitTy dstTy && MirTy.beq dstTy retTy
     | _, _ => false) &&
    callArgsMatchBody body.locals args
      ((calleeBody.locals.drop 1).take calleeBody.argumentCount)

/-- Check that every `.call` and `.sysrootCall` terminator in `body` resolves
to a valid target body with matching signature, disjoint moved places and
destination, valid return block, and non-cleanup unwind action.

A `.call` target must also be a safe function (`isUnsafe = false`). Calling an
`unsafe fn` is sound only if the caller establishes the callee's safety
contract, and $M_{\text{anneal}}$ executes the callee's MIR without checking
the callee's `Specs.safety` at the call site, so a caller could otherwise be
verified while violating a contract that the callee's MIR does not enforce.
Such programs fail closed at `initState`. The pinned `core::num` bodies behind
`.sysrootCall` are exempt: their only safety contract (no overflow for
`unchecked_*`) is enforced by `.addUnchecked`/`.subUnchecked`/`.mulUnchecked`
faulting `.undefined`. -/
noncomputable def callsAdmitted (p : Program) (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    match bb.terminator with
    | .call callee args dst target unwind =>
      match getElem? p.bodies callee with
      | none => false
      | some calleeBody =>
        !calleeBody.isUnsafe &&
          callTargetAdmitted body bb calleeBody args dst target unwind
    | .sysrootCall op args dst target unwind =>
      callTargetAdmitted body bb (sysrootNumBody op) args dst target unwind
    | _ => true)

/-- Whether `body` contains any `.call` or `.sysrootCall` terminator. -/
noncomputable def bodyHasAnyCall (body : Body) : Bool :=
  body.basicBlocks.any (fun bb =>
    match bb.terminator with
    | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
    | _ => false)

/-- Single-body static admission predicate for `(p, body)`. -/
noncomputable def singleBodyStaticAdmitted (p : Program) (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !stringIsEmpty body.identity &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    discriminantTypesValid body &&
    castTypesValid body &&
    assertConditionTypesValid body &&
    body.locals.all isSupportedScalarOrUnitTy &&
    callsAdmitted p body

/-- Static admission predicate for bodies participating in a calling program
(`singleBodyStaticAdmitted` plus `assignTypesValid`). -/
noncomputable def callBodyStaticAdmitted (p : Program) (body : Body) : Bool :=
  singleBodyStaticAdmitted p body && assignTypesValid body

/-- Whenever `body` contains any call terminator, require `assignTypesValid` on
`body` and require every body in `p.bodies` to satisfy
`callBodyStaticAdmitted p` so caller and transitive callees are all admitted at
entry. -/
noncomputable def allCallBodiesStaticAdmitted (p : Program) (body : Body) :
    Bool :=
  if bodyHasAnyCall body then
    assignTypesValid body && p.bodies.all (callBodyStaticAdmitted p)
  else
    true

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
      else if !assertConditionTypesValid body then
        .error .unsupported
      else if !body.locals.all isSupportedScalarOrUnitTy then
        .error .unsupported
      else if !callsAdmitted p body then
        .error .unsupported
      else if !allCallBodiesStaticAdmitted p body then
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

/-- Profile v2 entry initialization (`initStateV2 p q`):
Validates `p.pointerWidthBits = 64`, `p.mirProfileVersion = 2`, caller memory
allocation invariants (`validCallerMemory q.callerMem`), Profile v2 local
types (`isSupportedV2LocalTy`), well-typed arguments (`checkArgsMatchV2`), and
reference validity + mutable-borrow disjointness (`refsValidInMemList`,
`spansPairwiseDisjoint`).

`initStateV2` does not re-check that the body keeps reference and raw-pointer
locals apart (`bodyMixesRefsAndRawPtrsV2`, defined in `Boundary.lean`, which
imports this module). `BodyVerifiedV2` requires `BodyStaticAdmittedV2`, which
includes that check, before it says anything about executions. -/
noncomputable def initStateV2 (p : Program) (q : Query) :
    Except FaultKind State :=
  if !Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 2 then
    .error .unsupported
  else if !validCallerMemory q.callerMem then
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
      else if !discriminantTypesValidV2 body then
        .error .unsupported
      else if !castTypesValid body then
        .error .unsupported
      else if !assertConditionTypesValid body then
        .error .unsupported
      else if !body.locals.all isSupportedV2LocalTy then
        .error .unsupported
      else
        let paramTys := (body.locals.drop 1).take body.argumentCount
        if !checkArgsMatchV2 q.args paramTys then
          .error .unsupported
        else
          let entryMem := entryMemoryForArgsV2 q.callerMem paramTys q.args
          if !refsValidInMemList entryMem paramTys q.args ||
              !spansPairwiseDisjoint (refAccessSpansList paramTys q.args) then
            .error .undefined
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
              mem := entryMem
            }

mutual
  /-- Return `true` when `ty` is a reference or a `Box` (which the aliasing
  models treat like a unique reference), or an option, range, tuple, struct,
  fixed-size array, or `Vec` containing one. Profile v2 pointees never
  contain references or pointers (`isSupportedV2LocalTy`), so only
  algebraic, container, and fixed-array nesting need inspection. Kept
  exhaustive over `MirTy` so adding new aggregate/container constructors
  forces updating reference tracking. -/
  noncomputable def tyHasRefV2 : MirTy → Bool
    | .ref _ _ => true
    | .array elem _ => tyHasRefV2 elem
    | .option e | .rangeTo e | .rangeFrom e | .range e => tyHasRefV2 e
    | .box _ => true
    | .tuple fs => tyListHasRefV2 fs
    | .struct_ _ fs => tyListHasRefV2 fs
    | .vec elem => tyHasRefV2 elem
    | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
    | .rawPtr _ _ | .slice _ | .str | .unsupported => false

  noncomputable def tyListHasRefV2 : List MirTy → Bool
    | [] => false
    | t :: ts => tyHasRefV2 t || tyListHasRefV2 ts
end

/-- Return `true` when projection element `e` reads local `lid` (an `.index`
projection's index local). -/
noncomputable def projElemMentionsLocalV2 (lid : LocalId) :
    ProjectionElem → Bool
  | .index i => Nat.beq i lid
  | .deref | .field _ _ | .constantIndex _ _ _ | .downcast _ | .unsupported =>
    false

/-- Return `true` when `p` accesses local `lid`, as its base local or as the
index local of an `.index` projection. -/
noncomputable def placeMentionsLocalV2 (lid : LocalId) (p : Place) : Bool :=
  Nat.beq p.localId lid || p.projection.any (projElemMentionsLocalV2 lid)

/-- Return `true` when `opnd` reads or moves from local `lid`. -/
noncomputable def operandMentionsLocalV2 (lid : LocalId) : Operand → Bool
  | .copy p | .move p => placeMentionsLocalV2 lid p
  | .constant _ => false

/-- Return `true` when any operand in `ops` mentions local `lid`. -/
noncomputable def operandListMentionsLocalV2 (lid : LocalId) :
    List Operand → Bool
  | [] => false
  | op :: ops =>
    operandMentionsLocalV2 lid op || operandListMentionsLocalV2 lid ops

/-- Return `true` when `rv` mentions local `lid` in any operand or place. -/
noncomputable def rvalueMentionsLocalV2 (lid : LocalId) : Rvalue → Bool
  | .use op | .useRetag op | .unaryOp _ op | .cast _ op _
  | .repeat_ op _ _ | .aggregateRangeTo _ op | .aggregateRangeFrom _ op =>
    operandMentionsLocalV2 lid op
  | .binaryOp _ lhs rhs =>
    operandMentionsLocalV2 lid lhs || operandMentionsLocalV2 lid rhs
  | .discriminant p | .ref _ p | .addressOf _ p | .fakeAddressOf p =>
    placeMentionsLocalV2 lid p
  | .aggregateRange _ startOp endOp =>
    operandMentionsLocalV2 lid startOp || operandMentionsLocalV2 lid endOp
  | .aggregateOption _ _ (some op) => operandMentionsLocalV2 lid op
  | .aggregateOption _ _ none => false
  | .aggregateTuple ops | .aggregateArray _ ops | .aggregateStruct _ ops =>
    operandListMentionsLocalV2 lid ops
  | .unsupported => false

/-- Return `true` when `term` mentions local `lid` in any operand or
destination place. -/
noncomputable def terminatorMentionsLocalV2 (lid : LocalId) :
    TerminatorKind → Bool
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => false
  | .switchInt discr _ => operandMentionsLocalV2 lid discr
  | .assert cond _ _ _ _ => operandMentionsLocalV2 lid cond
  | .call _ args dst _ _ | .coreCall _ args dst _ _
  | .sysrootCall _ args dst _ _ | .callNe _ args dst _ _ =>
    operandListMentionsLocalV2 lid args || placeMentionsLocalV2 lid dst
  | .drop place _ _ => placeMentionsLocalV2 lid place

/-- Check static well-typedness of `.fakeAddressOf src` into unprojected local
`dstId`: `src` must be `⟨baseId, [.deref]⟩` with `baseId != dstId`,
`locals[baseId]?` must be `.ref _ pt` or `.rawPtr _ pt` with
`!isOverflowPairTy pt`, and `locals[dstId]?` must be `.rawPtr .shared pt`. -/
noncomputable def fakeAddressOfTypesMatchV2 (locals : List MirTy)
    (dstId : LocalId) (src : Place) : Bool :=
  !Nat.beq src.localId dstId &&
    match src.projection with
    | [.deref] =>
      match getElem? locals src.localId, getElem? locals dstId with
      | some (.ref _ pt), some dstTy
      | some (.rawPtr _ pt), some dstTy =>
        !isOverflowPairTy pt && MirTy.beq dstTy (.rawPtr .shared pt)
      | _, _ => false
    | _ => false

/-- Return `true` when `stmt` is an unprojected `.fakeAddressOf` assignment to
local `lid`. -/
noncomputable def stmtAssignsFakeAddressOfToV2 (lid : LocalId) :
    StatementKind → Bool
  | .assign dst rv =>
    match rv with
    | .fakeAddressOf _ => Nat.beq dst.localId lid && dst.projection.isEmpty
    | _ => false
  | _ => false

/-- Check that `stmt` uses candidate fake-metadata local `lid` exclusively as
a well-typed unprojected `.fakeAddressOf (*base)` destination (`base != lid`)
or as an unprojected `.unaryOp .ptrMetadata` operand (into a destination other
than `lid`), plus `StorageLive`/`StorageDead` markers. -/
noncomputable def stmtRespectsFakePtrMetadataLocalV2 (locals : List MirTy)
    (lid : LocalId) : StatementKind → Bool
  | .assign dst rv =>
    if placeMentionsLocalV2 lid dst then
      dst.projection.isEmpty &&
        match rv with
        | .fakeAddressOf src => fakeAddressOfTypesMatchV2 locals lid src
        | _ => false
    else if rvalueMentionsLocalV2 lid rv then
      match rv with
      | .unaryOp .ptrMetadata opnd =>
        match opnd with
        | .copy p | .move p => Nat.beq p.localId lid && p.projection.isEmpty
        | .constant _ => false
      | _ => false
    else
      true
  | .storageLive _ | .storageDead _ | .nop | .unsupported => true

/-- Return `true` when local `lid` of `body` is a compiler-synthesized
`RawPtrKind::FakeForPtrMetadata` temporary:
1. `lid > body.argumentCount` (neither `_0` nor a caller parameter);
2. `body.locals[lid]? = some (.rawPtr .shared pt)` (top-level `*const` local);
3. at least one statement in `body` assigns `.fakeAddressOf` to `⟨lid, []⟩`;
4. every statement and terminator in `body` uses `lid` exclusively as an
   unprojected `.fakeAddressOf (*base)` destination (`base != lid`) or as an
   unprojected `.unaryOp .ptrMetadata` operand (never dereferenced, reborrowed,
   cast, offset, copied elsewhere, passed to calls, or returned). -/
noncomputable def isFakePtrMetadataLocalV2 (body : Body)
    (lid : LocalId) : Bool :=
  Nat.blt body.argumentCount lid &&
    match getElem? body.locals lid with
    | some (.rawPtr .shared _) =>
      body.basicBlocks.any (fun bb =>
        bb.statements.any (stmtAssignsFakeAddressOfToV2 lid)) &&
        body.basicBlocks.all (fun bb =>
          bb.statements.all
            (stmtRespectsFakePtrMetadataLocalV2 body.locals lid) &&
            !terminatorMentionsLocalV2 lid bb.terminator)
    | _ => false

/-- Check that every `.fakeAddressOf` rvalue in `body` assigns into an
unprojected local satisfying `isFakePtrMetadataLocalV2 body dst.localId` (even
in bodies without reference locals). -/
noncomputable def bodyFakeAddressOfValidV2 (body : Body) : Bool :=
  body.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .assign dst rv =>
        match rv with
        | .fakeAddressOf _ =>
          dst.projection.isEmpty && isFakePtrMetadataLocalV2 body dst.localId
        | _ => true
      | _ => true))

/-- Loop over `locals` starting at index `idx`, returning `true` if any local
contains a raw pointer (`tyHasRawPtrV2`) and is not a metadata-only
`FakeForPtrMetadata` temporary (`isFakePtrMetadataLocalV2`). -/
noncomputable def bodyHasRawPtrLocalLoopV2 (body : Body) :
    Nat → List MirTy → Bool
  | _, [] => false
  | idx, ty :: rest =>
    (tyHasRawPtrV2 ty && !isFakePtrMetadataLocalV2 body idx) ||
      bodyHasRawPtrLocalLoopV2 body (idx + 1) rest

/-- Return `true` when `body` declares any non-`FakeForPtrMetadata` raw-pointer
local (including raw pointers nested inside tuples or arrays). -/
noncomputable def bodyHasRawPtrLocalV2 (body : Body) : Bool :=
  bodyHasRawPtrLocalLoopV2 body 0 body.locals

/-- Return `true` when `body` has both reference-typed and non-fake
raw-pointer-typed locals.

Profile v2 does not model Rust's pointer aliasing rules. The Rust Reference
(`src/behavior-considered-undefined.md:36-39`, `rust-lang/reference`
`ad35aca481751a06afeb23820a672b0f3b11a476`) lists as undefined behavior:

> "* Breaking the pointer aliasing rules. The exact aliasing rules are not
>   determined yet, but here is an outline of the general principles: `&T`
>   must point to memory that is not mutated while they are live (except for
>   data inside an [`UnsafeCell<U>`]), and `&mut T` must point to memory that
>   is not read or written by any pointer not derived from the reference and
>   that no other reference points to while they are live."

Rather than approximate these rules, Profile v2 admits only bodies that
cannot create or use conflicting references themselves. Every value a body
creates lives in a local of its type, so a body without real raw-pointer locals
creates references only from other references. The borrow checker then rules
out conflicting uses, since Profile v2 has no `UnsafeCell`. A `*const` local
used exclusively for `RawPtrKind::FakeForPtrMetadata` + `UnOp::PtrMetadata`
(`isFakePtrMetadataLocalV2`) never incurs a retag in Miri and can never be
dereferenced, reborrowed, cast, offset, or escaped, so exempting it cannot
derive references from raw pointers or access referenced memory through raw
pointers. A body without reference locals creates no references at all. Mixing
references with any other raw-pointer local would let a body derive overlapping
references from raw pointers, or access referenced memory through raw pointers,
so `BodyStaticAdmittedV2` rejects such bodies.

A `Box<P>` local counts as a reference (`tyHasRefV2`). The aliasing models
retag a `Box` like a unique reference, so a body that also had raw-pointer
locals could derive a raw pointer from the box and use it after the box is
moved or through a cast to `*mut P`, which is undefined behavior that
Profile v2 would not detect. The only `Box` dereference cast is therefore
`boxAsRef`, which yields a validated `&P`. A `Vec<T>` local counts as neither
a reference nor a raw pointer, although it owns a heap buffer: a body reaches
that buffer only through the contracts in `AllocContracts`, which check the
buffer on every use and return references rather than raw pointers. Raw
pointers to `Vec` or `Box` handles are not admitted local types
(`isSupportedV2LocalTy`), so no body can derive an alias of a heap buffer
from raw pointers.

This does not cover the aliasing permission of raw-pointer arguments: a
raw-pointer-only body that writes through a `*mut` argument the caller derived
from a live `&T` is undefined behavior that Profile v2 does not detect. Callers
must pass raw pointers whose provenance permits the accesses the body makes,
which receipts record as an assumption. -/
noncomputable def bodyMixesRefsAndRawPtrsV2 (body : Body) : Bool :=
  tyListHasRefV2 body.locals && bodyHasRawPtrLocalV2 body

end Trusted.MirSemantics

end
